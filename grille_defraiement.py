#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
GRILLE DE DÉFRAIEMENT TRAIN PAR DÉPARTEMENT
===========================================

Règle appliquée
  Pour chaque département, on prend les 3 communes les plus peuplées.
  Pour chacune, on cherche les trains vers la ville de l'événement le vendredi
  (à partir de l'heure choisie) et les trains retour le dimanche (à partir de
  l'heure choisie). On calcule le prix aller + retour, et le département reçoit
  le montant de la commune la plus chère.

Sources (officielles, gratuites, pas de blocage anti-robot)
  - Communes et populations : API Découpage administratif (geo.api.gouv.fr)
  - Horaires et itinéraires : API SNCF (api.sncf.com, clé gratuite)
  - Prix : open data SNCF (ressources.data.sncf.com) — fourchettes officielles
    « plein tarif » par origine-destination ; on retient le prix MAXIMUM en 2nde.
    Les tronçons dont le tarif est introuvable sont estimés au kilomètre et
    signalés « à vérifier » dans le résultat.

Utilisation
  Double-cliquer sur LANCER.bat (Windows) ou LANCER.command (Mac),
  ou dans un terminal :  python grille_defraiement.py
  (mode sans fenêtre :   python grille_defraiement.py --aide)
"""

import base64
import csv
import datetime as dt
import hashlib
import json
import math
import os
import queue
import re
import shutil
import socket
import ssl
import subprocess
import sys
import threading
import time
import traceback
import unicodedata
import urllib.error
import urllib.parse
import urllib.request

VERSION = "1.0"

if getattr(sys, "frozen", False):
    BASE_DIR = os.path.dirname(sys.executable)
else:
    BASE_DIR = os.path.dirname(os.path.abspath(__file__))

CACHE_DIR = os.path.join(BASE_DIR, "cache")
RESULT_DIR = os.path.join(BASE_DIR, "resultats")
CONFIG_PATH = os.path.join(BASE_DIR, "config.json")
CORRECTIONS_PATH = os.path.join(BASE_DIR, "corrections_gares.csv")

NAVITIA_BASE = "https://api.sncf.com/v1/coverage/sncf"
GEO_BASE = "https://geo.api.gouv.fr"
ODS_BASE = "https://ressources.data.sncf.com"
API_KEY_URL = "https://www.digital.sncf.com/startup/api/token-developpeur"
USER_AGENT = "GrilleDefraiement/%s (python-urllib)" % VERSION

# Jeux de données tarifaires SNCF (open data)
TARIFF_DATASETS = {
    "TGV": ("tarifs-tgv-inoui-ouigo", "TGV INOUI / OUIGO"),
    "IC": ("tarifs-intercites", "Intercités"),
    "TER": ("tarifs-ter-par-od", "TER"),
}

IDF_DEPS = {"75", "77", "78", "91", "92", "93", "94", "95"}
PARIS_INSEE = "75056"
PARIS_GARES = ["Paris Gare de Lyon", "Paris Montparnasse", "Paris Gare du Nord",
               "Paris Est", "Paris Austerlitz", "Paris Saint-Lazare", "Paris Bercy"]

ARRONDIS = {"aucun": 0, "à l'euro supérieur": 1, "aux 5 € supérieurs": 5, "aux 10 € supérieurs": 10}
JOURS = ["lundi", "mardi", "mercredi", "jeudi", "vendredi", "samedi", "dimanche"]
MOIS = ["janvier", "février", "mars", "avril", "mai", "juin", "juillet", "août",
        "septembre", "octobre", "novembre", "décembre"]

FAMILY_LABEL = {"TGV": "TGV", "OUIGO": "OUIGO", "IC": "Intercités", "TER": "TER", "IDF": "Transilien/RER"}

DEFAULT_CONFIG = {
    "ville": "",
    "gare": "",
    "date_aller": "",
    "heure_aller": "16:00",
    "date_retour": "",
    "heure_retour": "16:00",
    "heure_limite": "23:59",
    "arrondi": "à l'euro supérieur",
    "cle_api": "",
    "departements": "",
    "avance": {
        "delai_entre_requetes_secondes": 0.6,
        "villes_par_departement": 3,
        "distance_max_gare_km": 25,
        "gares_candidates_par_ville": 5,
        "correspondances_max": 3,
        "inclure_outre_mer": False,
        "tarif_ile_de_france_euros": 2.50,
        "estimation_euros_par_km": {"TGV": 0.25, "OUIGO": 0.16, "IC": 0.20, "TER": 0.20},
        "duree_cache_horaires_jours": 3,
        "duree_cache_tarifs_jours": 7,
    },
}

try:  # certificats à jour si le module certifi est présent (utile sur Mac)
    import certifi
    SSL_CONTEXT = ssl.create_default_context(cafile=certifi.where())
except Exception:
    SSL_CONTEXT = None


class UserError(Exception):
    """Erreur expliquée à l'utilisateur (message affiché tel quel)."""


class Cancelled(Exception):
    """Arrêt demandé par l'utilisateur."""


# --------------------------------------------------------------------------
# Petits outils
# --------------------------------------------------------------------------

def strip_accents(s):
    return "".join(c for c in unicodedata.normalize("NFKD", str(s or "")) if not unicodedata.combining(c))


def norm_key(s):
    return re.sub(r"[^a-z0-9]+", "_", strip_accents(s).lower()).strip("_")


def norm_name(s):
    """Normalise un nom de gare pour comparer « Marseille Saint-Charles » et « MARSEILLE ST CHARLES »."""
    s = strip_accents(s).upper()
    s = re.sub(r"\(.*?\)", " ", s)
    s = re.sub(r"[^A-Z0-9]+", " ", s)
    words = []
    for w in s.split():
        w = {"SAINT": "ST", "SAINTE": "STE", "SNCF": ""}.get(w, w)
        if w:
            words.append(w)
    return " ".join(words)


def uic7(value):
    """Code UIC réduit à 7 chiffres (sans la clé de contrôle), ou None."""
    if value is None:
        return None
    s = re.sub(r"\.0+$", "", str(value).strip())
    d = re.sub(r"\D", "", s).lstrip("0")
    return d[:7] if len(d) >= 7 else None


def uic_from_navitia_id(sa_id):
    nums = re.findall(r"\d{7,}", sa_id or "")
    return uic7(nums[-1]) if nums else None


def parse_price(v):
    if v is None:
        return None
    if isinstance(v, (int, float)):
        return float(v)
    s = str(v).strip()
    for ch in ("\u202f", "\xa0", " ", "€", "EUR"):
        s = s.replace(ch, "")
    if not s:
        return None
    if "," in s and "." in s:
        s = s.replace(".", "").replace(",", ".")
    else:
        s = s.replace(",", ".")
    try:
        return float(s)
    except ValueError:
        return None


def haversine_km(lon1, lat1, lon2, lat2):
    lon1, lat1, lon2, lat2 = map(math.radians, (float(lon1), float(lat1), float(lon2), float(lat2)))
    a = math.sin((lat2 - lat1) / 2) ** 2 + math.cos(lat1) * math.cos(lat2) * math.sin((lon2 - lon1) / 2) ** 2
    return 6371.0 * 2 * math.asin(math.sqrt(a))


def parse_date(s):
    s = (s or "").strip()
    for fmt in ("%d/%m/%Y", "%d/%m/%y", "%Y-%m-%d", "%d-%m-%Y", "%d.%m.%Y"):
        try:
            return dt.datetime.strptime(s, fmt).date()
        except ValueError:
            pass
    raise ValueError(s)


def parse_time(s):
    s = (s or "").strip().lower().replace(" ", "")
    m = re.fullmatch(r"(\d{1,2})(?:[h:](\d{0,2}))?", s)
    if not m:
        raise ValueError(s)
    h, mi = int(m.group(1)), int(m.group(2) or 0)
    if not (0 <= h <= 23 and 0 <= mi <= 59):
        raise ValueError(s)
    return dt.time(h, mi)


def date_fr(d):
    return "%s %d %s %d" % (JOURS[d.weekday()], d.day, MOIS[d.month - 1], d.year)


def heure_fr(t):
    return "%dh%02d" % (t.hour, t.minute)


def eur(x):
    if x is None:
        return "—"
    return ("%.2f €" % x).replace(".", ",")


def fmt_int(n):
    return "{:,}".format(int(n or 0)).replace(",", " ")


def navitia_dt(s):
    return dt.datetime.strptime(s, "%Y%m%dT%H%M%S")


def slug(s):
    return re.sub(r"[^A-Za-z0-9]+", "-", strip_accents(s)).strip("-") or "evenement"


def round_up(x, step):
    if x is None:
        return None
    if not step:
        return round(x, 2)
    return math.ceil(round(x, 2) / step - 1e-9) * step


def dep_sort_key(d):
    code = d["code"]
    if code in ("2A", "2B"):
        return (20, code)
    try:
        return (int(code), "")
    except ValueError:
        return (999, code)


def commune_of(sa):
    """Nom de la commune d'un arrêt Navitia."""
    admins = sa.get("administrative_regions") or []
    for ad in admins:
        if ad.get("level") == 8 and ad.get("name"):
            return ad["name"]
    if admins and admins[0].get("name"):
        return admins[0]["name"]
    m = re.search(r"\(([^()]+)\)\s*$", sa.get("label") or "")
    return m.group(1) if m else None


def in_commune(sa, commune):
    for ad in sa.get("administrative_regions") or []:
        if str(ad.get("insee") or "") == commune["code"]:
            return True
    c = commune_of(sa)
    return bool(c) and norm_name(c) == norm_name(commune["nom"])


def same_station(a, b):
    if a.get("id") and a.get("id") == b.get("id"):
        return True
    ua, ub = uic_from_navitia_id(a.get("id")), uic_from_navitia_id(b.get("id"))
    return bool(ua) and ua == ub


def load_config():
    cfg = json.loads(json.dumps(DEFAULT_CONFIG))
    if os.path.exists(CONFIG_PATH):
        try:
            with open(CONFIG_PATH, encoding="utf-8") as f:
                user = json.load(f)
            for k, v in user.items():
                if k == "avance" and isinstance(v, dict):
                    for k2, v2 in v.items():
                        if isinstance(v2, dict) and isinstance(cfg["avance"].get(k2), dict):
                            cfg["avance"][k2].update(v2)
                        else:
                            cfg["avance"][k2] = v2
                else:
                    cfg[k] = v
        except Exception:
            pass
    return cfg


def save_config(cfg):
    try:
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
    except Exception:
        pass


def load_corrections():
    """Fichier corrections_gares.csv : code_insee;gare (lignes # ignorées)."""
    if not os.path.exists(CORRECTIONS_PATH):
        try:
            with open(CORRECTIONS_PATH, "w", encoding="utf-8-sig") as f:
                f.write("# Corrections de gares (facultatif)\n"
                        "# Si une ville est associee a une mauvaise gare dans l'onglet 'Detail villes',\n"
                        "# ajoutez une ligne :  code INSEE de la ville;nom de la gare a utiliser\n"
                        "# Le code INSEE figure dans l'onglet 'Detail villes'. Exemple :\n"
                        "# 92012;Paris Montparnasse\n"
                        "code_insee;gare\n")
        except Exception:
            pass
        return {}
    out = {}
    for enc in ("utf-8-sig", "cp1252"):
        try:
            with open(CORRECTIONS_PATH, encoding=enc) as f:
                lines = f.read().splitlines()
            break
        except UnicodeDecodeError:
            continue
    else:
        return {}
    for line in lines:
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = re.split(r"[;,\t]", line, maxsplit=1)
        if len(parts) == 2 and parts[0].strip().lower() != "code_insee" and parts[1].strip():
            out[parts[0].strip().zfill(5)] = parts[1].strip()
    return out


# --------------------------------------------------------------------------
# Accès réseau : pauses entre requêtes, nouvelles tentatives, cache disque
# --------------------------------------------------------------------------

class Http:
    def __init__(self, delay, log, stop_event=None):
        self.delay = delay
        self.log = log
        self.stop = stop_event
        self._last = 0.0
        os.makedirs(CACHE_DIR, exist_ok=True)

    def _check_stop(self):
        if self.stop is not None and self.stop.is_set():
            raise Cancelled()

    def _sleep(self, seconds):
        end = time.time() + seconds
        while time.time() < end:
            self._check_stop()
            time.sleep(min(0.2, max(0.0, end - time.time())))

    @staticmethod
    def cache_path(url, ext=".json"):
        return os.path.join(CACHE_DIR, hashlib.sha1(url.encode("utf-8")).hexdigest() + ext)

    def get(self, url, headers=None, max_age_days=None, cache_status=(200,)):
        """Renvoie (code HTTP, texte). Met en cache les réponses dont le code est dans cache_status."""
        path = self.cache_path(url)
        if max_age_days and os.path.exists(path) and time.time() - os.path.getmtime(path) < max_age_days * 86400:
            try:
                with open(path, encoding="utf-8") as f:
                    c = json.load(f)
                return c["status"], c["body"]
            except Exception:
                pass
        status, raw = self._request(url, headers or {})
        body = raw.decode("utf-8-sig", errors="replace")
        if max_age_days and status in cache_status:
            tmp = path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump({"url": url, "status": status, "body": body}, f, ensure_ascii=False)
            os.replace(tmp, path)
        return status, body

    def download(self, url, max_age_days):
        """Télécharge un (gros) fichier dans le cache ; renvoie (code, chemin)."""
        path = self.cache_path(url, ".csv")
        if os.path.exists(path) and os.path.getsize(path) > 0 and \
                time.time() - os.path.getmtime(path) < max_age_days * 86400:
            return 200, path
        status, _ = self._request(url, {}, dest=path)
        return status, (path if status == 200 else None)

    def _request(self, url, headers, dest=None):
        h = {"User-Agent": USER_AGENT, "Accept": "*/*"}
        h.update(headers)
        last_err = None
        for attempt in range(7):
            self._check_stop()
            wait = self.delay - (time.time() - self._last)
            if wait > 0:
                self._sleep(wait)
            try:
                req = urllib.request.Request(url, headers=h)
                with urllib.request.urlopen(req, timeout=120, context=SSL_CONTEXT) as r:
                    status = r.status
                    if dest:
                        tmp = dest + ".tmp"
                        with open(tmp, "wb") as f:
                            shutil.copyfileobj(r, f, 1 << 20)
                        os.replace(tmp, dest)
                        raw = b""
                    else:
                        raw = r.read()
            except urllib.error.HTTPError as e:
                status = e.code
                try:
                    raw = e.read()
                except Exception:
                    raw = b""
            except (urllib.error.URLError, socket.timeout, TimeoutError, ConnectionError, OSError) as e:
                self._last = time.time()
                reason = getattr(e, "reason", e)
                if "CERTIFICATE_VERIFY_FAILED" in str(reason):
                    raise UserError(
                        "Erreur de certificat de sécurité (fréquent sur Mac).\n\n"
                        "Ouvrez le dossier Applications > Python 3.x et double-cliquez sur "
                        "« Install Certificates.command », puis relancez.")
                last_err = reason
                pause = min(120, 5 * 2 ** attempt)
                self.log("   (connexion impossible : %s — nouvel essai dans %d s)" % (reason, pause))
                self._sleep(pause)
                continue
            self._last = time.time()
            if status == 429 or status >= 500:
                last_err = "code HTTP %d" % status
                pause = min(300, 10 * 2 ** attempt)
                self.log("   (serveur occupé, code %d — pause de %d s puis nouvel essai)" % (status, pause))
                self._sleep(pause)
                continue
            return status, raw
        host = urllib.parse.urlsplit(url).netloc
        if last_err == "code HTTP 429" and "sncf" in host:
            raise UserError("Le quota de requêtes de l'API SNCF semble atteint.\n\n"
                            "Relancez plus tard (ou demain) : tout ce qui a déjà été calculé est "
                            "gardé en mémoire et ne sera pas refait.")
        raise UserError("Impossible de joindre %s après plusieurs essais (%s).\n\n"
                        "Vérifiez la connexion Internet puis relancez : le travail déjà fait "
                        "est conservé." % (host, last_err))


# --------------------------------------------------------------------------
# Communes et populations (geo.api.gouv.fr)
# --------------------------------------------------------------------------

class Geo:
    def __init__(self, http):
        self.http = http

    def _json(self, path, params=None):
        url = GEO_BASE + path + ("?" + urllib.parse.urlencode(params) if params else "")
        status, body = self.http.get(url, max_age_days=30)
        if status != 200:
            raise UserError("Le service geo.api.gouv.fr a répondu avec le code %s (%s)." % (status, path))
        return json.loads(body)

    def departements(self):
        return self._json("/departements", {"fields": "nom,code"})

    def communes(self, code_dep):
        return self._json("/departements/%s/communes" % code_dep, {"fields": "nom,code,population,centre"})

    def find_commune(self, text):
        text = text.strip()
        fields = "nom,code,population,centre,codeDepartement"
        if re.fullmatch(r"\d{5}", text):
            res = self._json("/communes", {"codePostal": text, "fields": fields})
        else:
            res = self._json("/communes", {"nom": text, "fields": fields, "boost": "population", "limit": 15})
        if not res:
            raise UserError("Ville introuvable : « %s ». Vérifiez l'orthographe." % text)
        exact = [c for c in res if norm_name(c.get("nom")) == norm_name(text)]
        if exact:
            return max(exact, key=lambda c: c.get("population") or 0)
        if re.fullmatch(r"\d{5}", text):
            return max(res, key=lambda c: c.get("population") or 0)
        return res[0]


# --------------------------------------------------------------------------
# Horaires et itinéraires (API SNCF / Navitia)
# --------------------------------------------------------------------------

NAVITIA_ERRORS = {
    "no_solution": "aucune solution",
    "no_origin": "départ non desservi",
    "no_destination": "arrivée non desservie",
    "no_origin_nor_destination": "départ et arrivée non desservis",
    "unknown_object": "gare inconnue",
}


class Navitia:
    def __init__(self, http, key, cache_days, log):
        self.http = http
        self.cache_days = cache_days
        self.log = log
        self.simple_mode = False
        key = (key or "").strip()
        self.headers = {"Authorization": "Basic " + base64.b64encode((key + ":").encode()).decode()}

    def get(self, path, params=None, cache=True):
        url = NAVITIA_BASE + path
        if params:
            url += "?" + urllib.parse.urlencode(params, doseq=True)
        status, body = self.http.get(url, headers=self.headers,
                                     max_age_days=self.cache_days if cache else None,
                                     cache_status=(200, 404))
        if status in (401, 403):
            raise UserError("La clé API SNCF est refusée.\n\nVérifiez qu'elle est copiée en entier, "
                            "sans espace. Pour obtenir une clé gratuite :\n" + API_KEY_URL)
        try:
            data = json.loads(body) if body else {}
        except ValueError:
            data = {}
        if not isinstance(data, dict):
            data = {}
        if status not in (200, 404) and "error" not in data:
            data["error"] = {"id": "http_%d" % status, "message": data.get("message") or body[:200]}
        return data

    def production_period(self):
        data = self.get("", cache=False)
        regions = data.get("regions") or []
        if not regions:
            return None
        try:
            r = regions[0]
            return (dt.datetime.strptime(r["start_production_date"][:8], "%Y%m%d").date(),
                    dt.datetime.strptime(r["end_production_date"][:8], "%Y%m%d").date())
        except Exception:
            return None

    def search_stop_areas(self, q, count=15):
        data = self.get("/places", {"q": q, "type[]": "stop_area", "count": count})
        return [p["stop_area"] for p in (data.get("places") or [])
                if p.get("embedded_type") == "stop_area" and p.get("stop_area")]

    def nearby_stop_areas(self, lon, lat, distance_m, count=10):
        data = self.get("/coords/%.6f;%.6f/places_nearby" % (float(lon), float(lat)),
                        {"type[]": "stop_area", "distance": int(distance_m), "count": count})
        out = []
        for p in data.get("places_nearby") or []:
            if p.get("embedded_type") == "stop_area" and p.get("stop_area"):
                sa = dict(p["stop_area"])
                try:
                    sa["_distance_km"] = float(p.get("distance") or 0) / 1000.0
                except ValueError:
                    sa["_distance_km"] = None
                out.append(sa)
        return out

    def stop_area(self, sa_id):
        data = self.get("/stop_areas/" + urllib.parse.quote(sa_id, safe=":"))
        sas = data.get("stop_areas") or []
        return sas[0] if sas else None

    def journeys(self, from_id, to_id, day, hmin, hmax, max_transfers):
        """Trajets partant le jour `day` entre hmin et hmax. Renvoie (liste, message d'erreur)."""
        start = dt.datetime.combine(day, hmin)
        end = dt.datetime.combine(day, hmax)
        if self.simple_mode:
            params = {"from": from_id, "to": to_id, "datetime": start.strftime("%Y%m%dT%H%M%S"),
                      "datetime_represents": "departure", "count": 10}
        else:
            params = {"from": from_id, "to": to_id, "datetime": start.strftime("%Y%m%dT%H%M%S"),
                      "datetime_represents": "departure",
                      "timeframe_duration": max(3600, int((end - start).total_seconds())),
                      "max_nb_journeys": 20, "max_nb_transfers": max_transfers,
                      "data_freshness": "base_schedule"}
        data = self.get("/journeys", params)
        err = data.get("error") or {}
        msg = (err.get("message") or data.get("message") or "")
        if not self.simple_mode and not data.get("journeys") and "param" in msg.lower():
            self.simple_mode = True
            self.log("   (l'API refuse certains paramètres avancés — passage en mode simple)")
            return self.journeys(from_id, to_id, day, hmin, hmax, max_transfers)
        if err:
            eid = err.get("id") or ""
            if eid == "date_out_of_bounds":
                raise UserError("Les horaires SNCF ne sont pas encore disponibles pour le %s." % date_fr(day))
            return [], NAVITIA_ERRORS.get(eid, msg or eid)
        out, seen = [], set()
        for j in data.get("journeys") or []:
            try:
                dep = navitia_dt(j["departure_date_time"])
            except Exception:
                continue
            if not (start <= dep <= end):
                continue
            pts = [s for s in j.get("sections") or [] if s.get("type") == "public_transport"]
            if not pts:
                continue
            sig = (j.get("departure_date_time"), j.get("arrival_date_time"),
                   tuple((s.get("display_informations") or {}).get("headsign") or "" for s in pts))
            if sig in seen:
                continue
            seen.add(sig)
            out.append(j)
        return out, (None if out else "aucun train dans la plage horaire")


# --------------------------------------------------------------------------
# Tarifs officiels SNCF (open data)
# --------------------------------------------------------------------------

def _is_numeric_col(h, sample):
    vals = [r.get(h) for r in sample if (r.get(h) or "").strip()]
    if not vals:
        return False
    return sum(1 for v in vals if parse_price(v) is not None) >= 0.8 * len(vals)


def _looks_like_class(v):
    s = strip_accents(v).lower().strip()
    if re.fullmatch(r"(classe\s*)?[12]\s*(e|er|ere|re|nde|de|eme)?(\s*classe)?", s):
        return True
    return len(s) <= 20 and ("premi" in s or "second" in s)


def detect_columns(headers, sample):
    K = {h: norm_key(h) for h in headers}
    numeric = {h: _is_numeric_col(h, sample) for h in headers}

    def is_code(k):
        return "uic" in k or k.startswith("code") or "_code" in k or k.endswith("_id")

    def first(lst):
        return lst[0] if lst else None

    o = [h for h in headers if "origine" in K[h] or K[h].startswith("depart") or "gare_depart" in K[h]]
    d = [h for h in headers if "destination" in K[h] or "arrivee" in K[h]]
    cols = {
        "o_uic": first([h for h in o if is_code(K[h])]),
        "o_name": first([h for h in o if not is_code(K[h]) and not numeric[h]]),
        "d_uic": first([h for h in d if is_code(K[h])]),
        "d_name": first([h for h in d if not is_code(K[h]) and not numeric[h]]),
        "carrier": first([h for h in headers if not numeric[h] and
                          any(w in K[h] for w in ("transporteur", "marque", "produit", "entite"))]),
    }
    used = set(o) | set(d) | {cols["carrier"]}
    price_cands = [h for h in headers if h not in used and numeric[h] and
                   any(w in K[h] for w in ("prix", "tarif", "montant", "plein"))]
    maxc = [h for h in price_cands if "max" in K[h]]
    if maxc:
        cols["price"] = [maxc[0]]
    else:
        filt = [h for h in price_cands if not any(
            w in K[h] for w in ("min", "abonnement", "mensuel", "annuel", "reduit", "jeune"))]
        cols["price"] = filt or price_cands
    used |= set(cols["price"])
    def class_like(h):
        vals = [r.get(h) for r in sample if (r.get(h) or "").strip()]
        return bool(vals) and sum(1 for v in vals if _looks_like_class(v)) >= 0.9 * len(vals)

    classe = first([h for h in headers if h not in used and "classe" in K[h] and class_like(h)])
    others = [h for h in headers if h not in used and not numeric[h]]
    if not classe:
        classe = first([h for h in others if class_like(h)])
    cols["classe"] = classe
    others = [h for h in others if h != classe]
    cols["profil"] = first([h for h in others if "profil" in K[h]]) or \
        first([h for h in others if any(w in K[h] for w in ("tarif", "libelle", "classe", "type"))])
    return cols


class TariffTable:
    COMPOUND = {"DU", "DE", "DES", "LA", "LE", "LES", "SUR", "SOUS", "EN", "D", "L", "AUX", "AU", "ET"}

    def __init__(self, key, label, path):
        self.key, self.label = key, label
        self.ok = False
        self.by_uic, self.by_name, self.names = {}, {}, set()
        self._city_cache = {}
        with open(path, encoding="utf-8-sig", errors="replace", newline="") as f:
            first_line = f.readline()
            f.seek(0)
            delim = max([";", ",", "\t"], key=first_line.count)
            reader = csv.DictReader(f, delimiter=delim)
            headers = reader.fieldnames or []
            sample = []
            for row in reader:
                sample.append(row)
                if len(sample) >= 400:
                    break
            self.cols = detect_columns(headers, sample)
            c = self.cols
            if not (c["price"] and (c["o_uic"] or c["o_name"]) and (c["d_uic"] or c["d_name"])):
                self.info = "colonnes non reconnues (%s)" % ", ".join(headers)
                return
            n = 0
            for rows in (sample, reader):
                for r in rows:
                    n += self._add(r)
        self.ok = n > 0
        desc = ", ".join("%s=%s" % (k, v) for k, v in c.items() if v)
        self.info = "%d tarifs chargés [%s]" % (n, desc)

    def _add(self, r):
        c = self.cols
        prices = [parse_price(r.get(h)) for h in c["price"]]
        prices = [p for p in prices if p is not None and p > 0]
        if not prices:
            return 0
        entry = (strip_accents(r.get(c["carrier"]) or "").upper() if c["carrier"] else "",
                 strip_accents(r.get(c["classe"]) or "").lower() if c["classe"] else "",
                 strip_accents(r.get(c["profil"]) or "").lower() if c["profil"] else "",
                 max(prices))
        ou = uic7(r.get(c["o_uic"])) if c["o_uic"] else None
        du = uic7(r.get(c["d_uic"])) if c["d_uic"] else None
        if ou and du:
            self.by_uic.setdefault((ou, du), []).append(entry)
        on = norm_name(r.get(c["o_name"])) if c["o_name"] else ""
        dn = norm_name(r.get(c["d_name"])) if c["d_name"] else ""
        if on and dn:
            self.by_name.setdefault((on, dn), []).append(entry)
            self.names.add(on)
            self.names.add(dn)
        return 1

    @staticmethod
    def _select(entries, family):
        e = entries
        if family == "OUIGO":
            e = [x for x in e if "OUIGO" in x[0]] or e
        elif family == "TGV":
            e = [x for x in e if "OUIGO" not in x[0]] or e
        e = [x for x in e if not any(w in x[2] for w in ("abonnement", "mensuel", "annuel", "hebdo"))] or e
        e = [x for x in e if "normal" in x[2] or "plein" in x[2]] or e
        by_class = {}
        for x in e:
            by_class[x[1]] = max(by_class.get(x[1], 0.0), x[3])
        second = [p for cl, p in by_class.items() if cl == "" or "2" in cl or "second" in cl]
        return max(second) if second else min(by_class.values())

    def _prefix_names(self, n):
        """Noms du jeu de données qui sont un début du nom Navitia (« PARIS GARE DE LYON » pour
        « Paris Gare de Lyon - Hall 1 & 2 »), ou l'inverse."""
        if not n:
            return []
        key = "§" + n
        if key not in self._city_cache:
            out = [m for m in self.names if m == n or n.startswith(m + " ") or m.startswith(n + " ")]
            out = [m for m in out if len(m.split()) >= 2 or m == n]
            self._city_cache[key] = out
        return self._city_cache[key]

    def _names_for_city(self, sa):
        city = commune_of(sa)
        if not city:
            return []
        c = norm_name(city)
        if c not in self._city_cache:
            out = []
            for n in self.names:
                if n == c:
                    out.append(n)
                elif n.startswith(c + " ") and n[len(c) + 1:].split(" ")[0] not in self.COMPOUND:
                    out.append(n)
            self._city_cache[c] = out
        return self._city_cache[c]

    def lookup(self, a, b, family):
        """Prix maximum 2nde entre deux gares Navitia. Renvoie (prix, méthode) ou (None, None)."""
        if not self.ok:
            return None, None
        ua, ub = uic_from_navitia_id(a.get("id")), uic_from_navitia_id(b.get("id"))
        for x, y in ((ua, ub), (ub, ua)):
            if x and y and (x, y) in self.by_uic:
                return self._select(self.by_uic[(x, y)], family), "tarif officiel"
        na, nb = norm_name(a.get("name")), norm_name(b.get("name"))
        for x, y in ((na, nb), (nb, na)):
            if (x, y) in self.by_name:
                return self._select(self.by_name[(x, y)], family), "tarif officiel"
        pa, pb = self._prefix_names(na), self._prefix_names(nb)
        entries = []
        for x in pa:
            for y in pb:
                entries += self.by_name.get((x, y), []) + self.by_name.get((y, x), [])
        if entries:
            return self._select(entries, family), "tarif officiel"
        entries = []
        for x in self._names_for_city(a):
            for y in self._names_for_city(b):
                entries += self.by_name.get((x, y), []) + self.by_name.get((y, x), [])
        if entries:
            return self._select(entries, family), "tarif officiel, gares de la même ville (approché)"
        return None, None


class Tariffs:
    def __init__(self, http, log, cache_days):
        self.tables = {}
        for key, (ds, label) in TARIFF_DATASETS.items():
            urls = ["%s/api/explore/v2.1/catalog/datasets/%s/exports/csv?delimiter=%%3B&use_labels=false" % (ODS_BASE, ds),
                    "%s/explore/dataset/%s/download/?format=csv&csv_separator=%%3B&use_labels_for_header=false" % (ODS_BASE, ds)]
            try:
                path, last = None, None
                for u in urls:
                    status, path = http.download(u, cache_days)
                    if status == 200 and path:
                        break
                    last = status
                if not path:
                    raise RuntimeError("téléchargement impossible (code %s)" % last)
                t = TariffTable(key, label, path)
                self.tables[key] = t
                log("   Tarifs %s : %s" % (label, t.info))
            except Cancelled:
                raise
            except Exception as e:
                log("   ⚠ Tarifs %s indisponibles (%s) : ces tronçons seront estimés au km." % (label, e))

    def table(self, key):
        t = self.tables.get(key)
        return t if (t and t.ok) else None

    def lookup(self, fam, a, b):
        order = {"TGV": ["TGV"], "OUIGO": ["TGV"], "IC": ["IC", "TER"], "TER": ["TER", "IC"]}.get(fam, ["TER"])
        for k in order:
            t = self.table(k)
            if t:
                p, how = t.lookup(a, b, fam)
                if p is not None:
                    return p, how
        return None, None


# --------------------------------------------------------------------------
# Calcul du prix d'un trajet
# --------------------------------------------------------------------------

def classify(section):
    di = section.get("display_informations") or {}
    cm = strip_accents(di.get("commercial_mode") or "").upper()
    net = strip_accents(di.get("network") or "").upper()
    pm = strip_accents(di.get("physical_mode") or "").upper()
    txt = " ".join((cm, net, pm))
    if "OUIGO" in txt:
        return "OUIGO"
    if re.search(r"\b(TGV|INOUI|LYRIA|EUROSTAR|ICE|FRECCIAROSSA|AVE|RENFE|TRENITALIA)\b", cm) \
            or "GRANDE VITESSE" in pm:
        return "TGV"
    if "INTERCIT" in cm or "INTERCIT" in net:
        return "IC"
    if re.search(r"\b(TRANSILIEN|RER)\b", txt):
        return "IDF"
    return "TER"


def section_endpoint(place):
    sp = place.get("stop_point") or {}
    sa = dict(sp.get("stop_area") or {})
    if not sa:
        sa = {"id": place.get("id"), "name": place.get("name")}
    if not sa.get("administrative_regions"):
        sa["administrative_regions"] = sp.get("administrative_regions") or place.get("administrative_regions") or []
    if not sa.get("coord"):
        sa["coord"] = sp.get("coord") or {}
    if not sa.get("label"):
        sa["label"] = sp.get("label") or place.get("name") or ""
    return sa


def section_km(section, a, b):
    gj = section.get("geojson") or {}
    props = gj.get("properties")
    for p in (props if isinstance(props, list) else [props]):
        if isinstance(p, dict) and p.get("length"):
            try:
                return float(p["length"]) / 1000.0
            except ValueError:
                pass
    coords = gj.get("coordinates") or []
    if len(coords) >= 2:
        try:
            return sum(haversine_km(coords[i][0], coords[i][1], coords[i + 1][0], coords[i + 1][1])
                       for i in range(len(coords) - 1))
        except Exception:
            pass
    try:
        return haversine_km(a["coord"]["lon"], a["coord"]["lat"], b["coord"]["lon"], b["coord"]["lat"]) * 1.25
    except Exception:
        return 0.0


class Pricer:
    def __init__(self, tariffs, adv):
        self.t = tariffs
        self.rates = adv["estimation_euros_par_km"]
        self.idf = float(adv["tarif_ile_de_france_euros"])

    def price(self, journey):
        legs = []
        for s in journey.get("sections") or []:
            if s.get("type") != "public_transport":
                continue
            a, b = section_endpoint(s.get("from") or {}), section_endpoint(s.get("to") or {})
            legs.append({"fam": classify(s), "a": a, "b": b, "km": section_km(s, a, b)})
        if not legs:
            return None
        groups = []
        for leg in legs:
            if groups and groups[-1][0]["fam"] == leg["fam"]:
                groups[-1].append(leg)
            else:
                groups.append([leg])
        total, lines, estimated, approx = 0.0, [], False, False

        def line(fam, a, b, p, how):
            return "%s %s → %s : %s (%s)" % (FAMILY_LABEL[fam], a.get("name"), b.get("name"), eur(p), how)

        for g in groups:
            fam, a, b = g[0]["fam"], g[0]["a"], g[-1]["b"]
            if fam == "IDF":
                total += self.idf
                lines.append(line(fam, a, b, self.idf, "ticket Île-de-France"))
                continue
            p, how = self.t.lookup(fam, a, b)
            if p is not None:
                total += p
                approx = approx or "approché" in how
                lines.append(line(fam, a, b, p, how))
                continue
            for leg in g:
                p, how = (self.t.lookup(fam, leg["a"], leg["b"]) if len(g) > 1 else (None, None))
                if p is None:
                    rate = float(self.rates.get(fam, self.rates.get("TER", 0.20)))
                    p = round(leg["km"] * rate, 2)
                    how = "ESTIMATION : %.0f km × %.2f €/km" % (leg["km"], rate)
                    estimated = True
                else:
                    approx = approx or "approché" in how
                total += p
                lines.append(line(fam, leg["a"], leg["b"], p, how))
        summary = []
        for s in journey.get("sections") or []:
            if s.get("type") == "public_transport":
                try:
                    h = navitia_dt(s["departure_date_time"]).strftime("%H:%M")
                except Exception:
                    h = "?"
                summary.append("%s %s %s → %s" % (h, FAMILY_LABEL[classify(s)],
                                                   (s.get("from") or {}).get("name", "?"),
                                                   (s.get("to") or {}).get("name", "?")))
        return {"price": round(total, 2), "estimated": estimated, "approx": approx,
                "details": lines, "summary": " | ".join(summary)}


# --------------------------------------------------------------------------
# Moteur principal
# --------------------------------------------------------------------------

def build_params(raw):
    """Vérifie les saisies. Renvoie (params, avertissements). Lève UserError si une saisie est invalide."""
    errors, warnings = [], []
    p = {"ville": (raw.get("ville") or "").strip(), "gare": (raw.get("gare") or "").strip(),
         "cle": (raw.get("cle_api") or "").strip()}
    if not p["ville"]:
        errors.append("Indiquez la ville de l'événement.")
    if not p["cle"]:
        errors.append("Indiquez la clé API SNCF (gratuite, voir le bouton « Obtenir une clé »).")
    for k, label in (("date_aller", "date aller"), ("date_retour", "date retour")):
        try:
            p[k] = parse_date(raw.get(k))
        except ValueError:
            errors.append("La %s n'est pas valide (format attendu : JJ/MM/AAAA)." % label)
    for k, label in (("heure_aller", "heure aller"), ("heure_retour", "heure retour"),
                     ("heure_limite", "heure limite")):
        try:
            p[k] = parse_time(raw.get(k))
        except ValueError:
            errors.append("L'%s n'est pas valide (format attendu : 16:00)." % label)
    if errors:
        raise UserError("\n".join(errors))
    if p["date_retour"] < p["date_aller"]:
        raise UserError("La date retour est avant la date aller.")
    for k in ("heure_aller", "heure_retour"):
        if p["heure_limite"] <= p[k]:
            raise UserError("L'heure limite (%s) doit être après l'heure de départ (%s)."
                            % (heure_fr(p["heure_limite"]), heure_fr(p[k])))
    if p["date_aller"].weekday() != 4:
        warnings.append("La date aller (%s) n'est pas un vendredi." % date_fr(p["date_aller"]))
    if p["date_retour"].weekday() != 6:
        warnings.append("La date retour (%s) n'est pas un dimanche." % date_fr(p["date_retour"]))
    p["arrondi_label"] = raw.get("arrondi") if raw.get("arrondi") in ARRONDIS else "aucun"
    p["arrondi"] = ARRONDIS[p["arrondi_label"]]
    deps = []
    for tok in re.split(r"[\s,;]+", raw.get("departements") or ""):
        tok = tok.strip().upper()
        if tok:
            deps.append(tok.zfill(2) if tok.isdigit() and len(tok) == 1 else tok)
    p["deps"] = deps
    return p, warnings


class Engine:
    def __init__(self, params, adv, log, progress, stop_event=None, result_dir=None):
        self.p, self.adv = params, adv
        self.result_dir = result_dir or RESULT_DIR
        self._log, self.progress, self.stop = log, progress, stop_event
        self.log_file = None
        self.grid, self.cities, self.trips = [], [], []

    def log(self, msg):
        self._log(msg)
        if self.log_file:
            try:
                self.log_file.write(msg + "\n")
                self.log_file.flush()
            except Exception:
                pass

    def check_stop(self):
        if self.stop is not None and self.stop.is_set():
            raise Cancelled()

    def run(self):
        os.makedirs(self.result_dir, exist_ok=True)
        try:
            self.log_file = open(os.path.join(self.result_dir, "dernier_journal.txt"), "w", encoding="utf-8")
        except Exception:
            self.log_file = None
        try:
            return self._run()
        except Exception:
            if self.log_file:
                self.log_file.write("\n" + traceback.format_exc())
            raise
        finally:
            if self.log_file:
                self.log_file.close()
                self.log_file = None

    def _run(self):
        p, adv = self.p, self.adv
        self.http = Http(float(adv["delai_entre_requetes_secondes"]), self.log, self.stop)
        self.geo = Geo(self.http)
        self.nav = Navitia(self.http, p["cle"], float(adv["duree_cache_horaires_jours"]), self.log)
        self.K = max(1, int(adv["gares_candidates_par_ville"]))
        self.dmax = float(adv["distance_max_gare_km"])
        self.maxtr = int(adv["correspondances_max"])
        self.idf_ticket = float(adv["tarif_ile_de_france_euros"])
        self.corrections = load_corrections()
        self._paris = None

        self.log("Étape 1/4 — Vérification de la clé API SNCF…")
        period = self.nav.production_period()
        if period:
            start, end = period
            self.log("   Clé valide. Horaires SNCF disponibles du %s au %s." % (start.strftime("%d/%m/%Y"),
                                                                              end.strftime("%d/%m/%Y")))
            for label, d in (("aller", p["date_aller"]), ("retour", p["date_retour"])):
                if not (start <= d <= end):
                    raise UserError(
                        "Les horaires SNCF du %s (%s) ne sont pas disponibles : l'API couvre actuellement "
                        "du %s au %s.\n\nAstuce : les prix utilisés sont les tarifs plafonds officiels, "
                        "qui ne dépendent pas de la date. Vous pouvez lancer le calcul avec un vendredi et "
                        "un dimanche couverts par l'API : le résultat sera en pratique le même (seuls les "
                        "horaires exacts changent)." % (date_fr(d), label, start.strftime("%d/%m/%Y"),
                                                         end.strftime("%d/%m/%Y")))
        else:
            self.log("   Clé acceptée (période des horaires non communiquée).")

        self.log("\nÉtape 2/4 — Ville de l'événement…")
        self.ev = self.geo.find_commune(p["ville"])
        self.ev_dep = self.ev.get("codeDepartement") or ""
        self.log("   %s (%s), %s habitants." % (self.ev["nom"], self.ev_dep, fmt_int(self.ev.get("population"))))
        self.ev_cands = self.event_candidates()
        if len(self.ev_cands) > 1:
            self.log("   Plusieurs gares possibles : %s.\n   Pour chaque ville de départ, la gare donnant le "
                     "trajet le plus rapide sera retenue.\n   Pour imposer une gare, remplissez « Gare "
                     "d'arrivée »." % ", ".join(sa.get("name", "?") for sa in self.ev_cands))
        else:
            self.log("   Gare d'arrivée : %s" % self.ev_cands[0].get("name"))

        self.log("\nÉtape 3/4 — Grilles tarifaires officielles SNCF…")
        self.tariffs = Tariffs(self.http, self.log, float(adv["duree_cache_tarifs_jours"]))
        if not self.tariffs.tables:
            self.log("   ⚠ Aucune grille tarifaire n'a pu être chargée : tous les prix seront estimés au km.")
        self.pricer = Pricer(self.tariffs, adv)

        self.log("\nÉtape 4/4 — Calcul par département…")
        deps = self.geo.departements()
        if not adv.get("inclure_outre_mer"):
            deps = [d for d in deps if not d["code"].startswith("97")]
        if p["deps"]:
            wanted = set(p["deps"])
            unknown = wanted - {d["code"] for d in deps}
            if unknown:
                self.log("   ⚠ Départements inconnus ignorés : %s" % ", ".join(sorted(unknown)))
            deps = [d for d in deps if d["code"] in wanted]
            if not deps:
                raise UserError("Aucun des départements demandés n'a été reconnu.")
        deps.sort(key=dep_sort_key)
        nvilles = int(adv["villes_par_departement"])
        for i, dep in enumerate(deps):
            self.check_stop()
            self.progress(i, len(deps), "%s – %s" % (dep["code"], dep["nom"]))
            self.log("\n[%d/%d] %s – %s" % (i + 1, len(deps), dep["code"], dep["nom"]))
            communes = sorted(self.geo.communes(dep["code"]), key=lambda c: c.get("population") or 0, reverse=True)
            res = []
            for c in communes[:nvilles]:
                self.check_stop()
                try:
                    r = self.process_city(c, dep)
                except (Cancelled, UserError):
                    raise
                except Exception as e:
                    r = self.empty_city(c, dep)
                    r["remarques"].append("erreur inattendue : %s" % e)
                    if self.log_file:
                        self.log_file.write(traceback.format_exc())
                res.append(r)
                self.cities.append(r)
                self.log("   • %s → %s : aller %s, retour %s%s" % (
                    c["nom"], r["gare"] or "—", eur(r["aller"]), eur(r["retour"]),
                    (" (%s)" % "; ".join(r["remarques"])) if r["remarques"] else ""))
            self.grid.append(self.summarize(dep, res))
        self.progress(len(deps), len(deps), "Écriture du fichier…")
        return write_output(self)

    # -- gares ----------------------------------------------------------------

    def paris_stations(self):
        if self._paris is None:
            out = []
            for name in PARIS_GARES:
                for sa in self.nav.search_stop_areas(name, count=5):
                    if (commune_of(sa) or "").lower().startswith("paris") or sa.get("name", "").lower().startswith("paris"):
                        if all(not same_station(sa, x) for x in out):
                            out.append(sa)
                        break
            self._paris = out
        return self._paris

    def commune_stations(self, commune):
        if commune["code"] == PARIS_INSEE:
            return self.paris_stations(), "gares de la ville"
        found = [sa for sa in self.nav.search_stop_areas(commune["nom"]) if in_commune(sa, commune)]
        if found:
            return found[:self.K], "gare(s) de la ville"
        centre = (commune.get("centre") or {}).get("coordinates")
        if centre:
            near = self.nav.nearby_stop_areas(centre[0], centre[1], self.dmax * 1000, count=3)
            if near:
                return near[:3], "gare la plus proche"
        return [], ""

    def event_candidates(self):
        if self.p["gare"]:
            sas = self.nav.search_stop_areas(self.p["gare"], count=5)
            if not sas:
                raise UserError("Gare d'arrivée introuvable : « %s ». Essayez son nom exact "
                                "(ex. « Marseille Saint-Charles »)." % self.p["gare"])
            return [sas[0]]
        sas, _ = self.commune_stations(self.ev)
        if not sas:
            raise UserError("Aucune gare SNCF trouvée pour %s. Indiquez une gare dans « Gare d'arrivée »."
                            % self.ev["nom"])
        return sas if self.ev["code"] == PARIS_INSEE else sas[:3]

    def origin_candidates(self, c, dep):
        out = []
        if c["code"] in self.corrections:
            name = self.corrections[c["code"]]
            sa = self.nav.stop_area(name) if name.startswith("stop_area:") else \
                (self.nav.search_stop_areas(name, count=5) or [None])[0]
            if sa:
                return [{"sa": sa, "mode": "gare corrigée (corrections_gares.csv)", "extra": 0.0, "note": ""}]
            self.log("   ⚠ Correction ignorée pour %s : gare « %s » introuvable" % (c["nom"], name))
        sas, mode = self.commune_stations(c)
        for sa in sas:
            out.append({"sa": sa, "mode": mode, "extra": 0.0, "note": ""})
        if dep["code"] in IDF_DEPS and self.ev_dep not in IDF_DEPS and c["code"] != PARIS_INSEE:
            for sa in self.paris_stations():
                out.append({"sa": sa, "mode": "via Paris", "extra": self.idf_ticket,
                            "note": "départ d'une gare parisienne (+ ticket Île-de-France)"})
        return out

    # -- villes ---------------------------------------------------------------

    def empty_city(self, c, dep):
        return {"dep_code": dep["code"], "dep_nom": dep["nom"], "ville": c["nom"], "insee": c["code"],
                "population": c.get("population") or 0, "gare": "", "mode": "", "dist_km": None,
                "gare_evt": "", "aller": None, "retour": None, "aller_info": "", "retour_info": "",
                "remarques": [], "estimated": False, "approx": False}

    def process_city(self, c, dep):
        p = self.p
        r = self.empty_city(c, dep)
        if c["code"] == self.ev["code"]:
            r.update(aller=0.0, retour=0.0, gare="(ville de l'événement)")
            r["remarques"].append("ville de l'événement")
            return r
        if dep["code"] in IDF_DEPS and self.ev_dep in IDF_DEPS:
            r.update(aller=self.idf_ticket, retour=self.idf_ticket, gare="(transports franciliens)")
            r["remarques"].append("trajet intra Île-de-France : ticket Île-de-France")
            return r
        origins = self.origin_candidates(c, dep)
        if not origins:
            r["remarques"].append("aucune gare SNCF à moins de %.0f km" % self.dmax)
            return r
        found = self.best_pair(origins)
        if found and found[0] == "same":
            o = found[1]
            r.update(aller=o["extra"], retour=o["extra"], gare=o["sa"].get("name"), mode=o["mode"])
            r["remarques"].append("même gare que l'événement")
            return r
        if found and found[0] == "ok":
            _, o, e, js_a = found
        else:
            o, e, js_a = origins[0], self.ev_cands[0], []
            r["remarques"].append("aucun train aller trouvé le %s entre %s et %s (%s)" % (
                date_fr(p["date_aller"]), heure_fr(p["heure_aller"]), heure_fr(p["heure_limite"]),
                (found[1] if found else None) or "aucune solution"))
        r["gare"] = o["sa"].get("name", "")
        r["mode"] = o["mode"]
        r["dist_km"] = o["sa"].get("_distance_km")
        r["gare_evt"] = e.get("name", "")
        if o["note"]:
            r["remarques"].append(o["note"])
        js_r, err_r = self.nav.journeys(e["id"], o["sa"]["id"], p["date_retour"], p["heure_retour"],
                                        p["heure_limite"], self.maxtr)
        if not js_r:
            r["remarques"].append("aucun train retour trouvé le %s entre %s et %s (%s)" % (
                date_fr(p["date_retour"]), heure_fr(p["heure_retour"]), heure_fr(p["heure_limite"]), err_r))
        r["aller"], r["aller_info"] = self.choose(js_a, r, "Aller", o["extra"])
        r["retour"], r["retour_info"] = self.choose(js_r, r, "Retour", o["extra"])
        est = r.pop("_est", [])
        if est:
            r["remarques"].append("prix en partie estimé au km (%s)" % " et ".join(est))
        if r["approx"]:
            r["remarques"].append("tarif approché (gares de la même ville)")
        return r

    def best_pair(self, origins):
        """Choisit la gare de départ puis la gare d'arrivée donnant le trajet aller le moins cher
        (à prix égal : le plus rapide).
        Renvoie ("same", o, e) / ("ok", o, e, trajets) / ("none", message)."""
        p = self.p
        cache = {}

        def attempt(o, e):
            key = (o["sa"].get("id"), e.get("id"))
            if key not in cache:
                js, err = self.nav.journeys(o["sa"]["id"], e["id"], p["date_aller"], p["heure_aller"],
                                            p["heure_limite"], self.maxtr)
                score = None
                for j in js:
                    pr = self.pricer.price(j)
                    if pr is not None:
                        s = (round(pr["price"] + o["extra"], 2), int(j.get("duration") or 10 ** 9))
                        score = s if score is None or s < score else score
                if score is None:
                    js = []
                cache[key] = (js, err, score)
            return cache[key]

        for o in origins:
            for e in self.ev_cands:
                if same_station(o["sa"], e):
                    return ("same", o, e)
        best, last_err = None, None
        e0 = self.ev_cands[0]
        for o in origins:                      # 1) meilleure gare de départ
            js, err, sc = attempt(o, e0)
            if js and (best is None or sc < best[3]):
                best = (o, e0, js, sc)
            last_err = last_err or err
        if best:                               # 2) meilleure gare d'arrivée pour cette gare de départ
            for e in self.ev_cands[1:]:
                js, err, sc = attempt(best[0], e)
                if js and sc < best[3]:
                    best = (best[0], e, js, sc)
        else:                                  # 3) rien trouvé : on essaie les autres combinaisons
            for o in origins[:4]:
                for e in self.ev_cands[1:4]:
                    js, err, sc = attempt(o, e)
                    if js and (best is None or sc < best[3]):
                        best = (o, e, js, sc)
                    last_err = last_err or err
        if best:
            return ("ok", best[0], best[1], best[2])
        return ("none", last_err)

    def choose(self, js, r, sens, extra):
        priced = []
        for j in js:
            pr = self.pricer.price(j)
            if pr is None:
                continue
            if extra:
                pr["price"] = round(pr["price"] + extra, 2)
                pr["details"].append("+ %s de transports franciliens jusqu'à la gare parisienne" % eur(extra))
            priced.append((j, pr))
        if not priced:
            return None, ""
        # Règle : le trajet le moins cher (2nde classe) ; à prix égal, le plus rapide
        pick = min(priced, key=lambda x: (x[1]["price"], int(x[0].get("duration") or 10 ** 9)))
        for j, pr in priced:
            try:
                dep_t, arr_t = navitia_dt(j["departure_date_time"]), navitia_dt(j["arrival_date_time"])
            except Exception:
                dep_t = arr_t = None
            self.trips.append({
                "dep_code": r["dep_code"], "ville": r["ville"], "sens": sens,
                "depart": dep_t.strftime("%d/%m %H:%M") if dep_t else "",
                "arrivee": arr_t.strftime("%d/%m %H:%M") if arr_t else "",
                "duree": "%dh%02d" % divmod(int(j.get("duration") or 0) // 60, 60),
                "corresp": j.get("nb_transfers", ""), "itineraire": pr["summary"], "prix": pr["price"],
                "estime": "OUI" if pr["estimated"] else "", "detail": "\n".join(pr["details"]),
                "retenu": "OUI" if j is pick[0] else ""})
        pr = pick[1]
        if pr["estimated"]:
            r["estimated"] = True
            r.setdefault("_est", []).append(sens.lower())
        if pr["approx"]:
            r["approx"] = True
        return pr["price"], pr["summary"]

    def summarize(self, dep, res):
        def tot(r):
            return (r["aller"] or 0.0) + (r["retour"] or 0.0)
        complete = [r for r in res if r["aller"] is not None and r["retour"] is not None]
        partial = [r for r in res if (r["aller"] is None) != (r["retour"] is None)]
        best = max(complete, key=tot) if complete else (max(partial, key=tot) if partial else None)
        notes, check = [], False
        for r in res:
            if r["aller"] is None or r["retour"] is None:
                check = True
                notes.append("%s : non calculé (%s)" % (r["ville"], "; ".join(r["remarques"]) or "aucun trajet"))
        if best is None:
            notes.insert(0, "aucun trajet trouvé pour ce département : montant à fixer à la main")
            check = True
        else:
            if best["estimated"] or best["approx"]:
                check = True
            if best["remarques"]:
                notes.insert(0, "%s : %s" % (best["ville"], "; ".join(best["remarques"])))
        total = tot(best) if best else None
        return {"dep_code": dep["code"], "dep_nom": dep["nom"], "ville": best["ville"] if best else "",
                "gare": best["gare"] if best else "", "aller": best["aller"] if best else None,
                "retour": best["retour"] if best else None, "total": total,
                "montant": round_up(total, self.p["arrondi"]), "a_verifier": "OUI" if check else "",
                "remarques": " | ".join(notes)}


# --------------------------------------------------------------------------
# Écriture du résultat (Excel, ou CSV si Excel indisponible)
# --------------------------------------------------------------------------

def ensure_openpyxl(log):
    try:
        import openpyxl  # noqa: F401
        return True
    except ImportError:
        pass
    if getattr(sys, "frozen", False):
        return False
    log("   Installation du module Excel (openpyxl), une seule fois…")
    for extra in ([], ["--user"]):
        try:
            subprocess.run([sys.executable, "-m", "pip", "install", "--quiet", "--disable-pip-version-check"]
                           + extra + ["openpyxl"], check=True, timeout=300,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            import importlib
            importlib.invalidate_caches()
            import openpyxl  # noqa: F401
            return True
        except Exception:
            continue
    return False


GRID_COLS = [("Code", "dep_code", 7), ("Département", "dep_nom", 24), ("Ville retenue", "ville", 24),
             ("Gare de départ", "gare", 28), ("Aller (€)", "aller", 11), ("Retour (€)", "retour", 11),
             ("Total A/R (€)", "total", 13), ("Montant grille (€)", "montant", 17),
             ("À vérifier", "a_verifier", 10), ("Remarques", "remarques", 90)]
CITY_COLS = [("Code", "dep_code", 7), ("Département", "dep_nom", 22), ("Ville", "ville", 24),
             ("Code INSEE", "insee", 11), ("Population", "population", 12), ("Gare de départ", "gare", 28),
             ("Choix de la gare", "mode", 22), ("Distance gare (km)", "dist_km", 12),
             ("Gare de l'événement", "gare_evt", 26), ("Aller (€)", "aller", 11),
             ("Train aller retenu", "aller_info", 60), ("Retour (€)", "retour", 11),
             ("Train retour retenu", "retour_info", 60), ("Total A/R (€)", "total", 13),
             ("Remarques", "remarques", 70)]
TRIP_COLS = [("Code", "dep_code", 7), ("Ville", "ville", 22), ("Sens", "sens", 8), ("Départ", "depart", 13),
             ("Arrivée", "arrivee", 13), ("Durée", "duree", 8), ("Corresp.", "corresp", 9),
             ("Itinéraire", "itineraire", 80), ("Prix (€)", "prix", 10), ("Estimé ?", "estime", 9),
             ("Détail du calcul", "detail", 100), ("Retenu", "retenu", 8)]
MONEY = {"aller", "retour", "total", "montant", "prix"}


def meta_rows(eng):
    p = eng.p
    rows = [("Ville de l'événement", "%s (%s)" % (eng.ev["nom"], eng.ev_dep)),
            ("Gare(s) d'arrivée", ", ".join(sa.get("name", "?") for sa in eng.ev_cands)),
            ("Aller", "%s, trains partant entre %s et %s" % (date_fr(p["date_aller"]), heure_fr(p["heure_aller"]),
                                                            heure_fr(p["heure_limite"]))),
            ("Retour", "%s, trains partant entre %s et %s" % (date_fr(p["date_retour"]), heure_fr(p["heure_retour"]),
                                                             heure_fr(p["heure_limite"]))),
            ("Règle de calcul", "Pour chaque ville : le trajet le moins cher en 2nde classe (aller et retour). "
                                "Pour le département : la ville la plus chère des trois (total aller + retour)."),
            ("Arrondi du montant", p["arrondi_label"]),
            ("Villes par département", str(eng.adv["villes_par_departement"])),
            ("Généré le", dt.datetime.now().strftime("%d/%m/%Y à %H:%M")),
            ("", ""),
            ("MÉTHODE", ""),
            ("Horaires", "API SNCF (api.sncf.com) : trains réellement programmés aux dates et heures demandées."),
            ("Prix", "Open data SNCF : prix MAXIMUM officiel en 2nde classe (plein tarif) pour chaque "
                     "origine-destination. C'est un plafond : le prix payé réellement est égal ou inférieur."),
            ("Correspondances", "Tronçons d'une même famille (TGV, TER…) tarifés de bout en bout si le tarif "
                                "existe, sinon tronçon par tronçon."),
            ("Estimations", "Si un tarif est introuvable, le tronçon est estimé au km (%s) : ligne marquée "
                            "« À vérifier »." % ", ".join("%s %.2f €/km" % (k, v) for k, v in
                                                          eng.adv["estimation_euros_par_km"].items())),
            ("Île-de-France", "Trajets franciliens : %s par trajet. Villes d'IDF sans grande gare : départ "
                              "d'une gare parisienne + ce ticket." % eur(eng.idf_ticket)),
            ("Corriger une gare", "Fichier corrections_gares.csv (dans le dossier du programme), puis relancer."),
            ("Corriger un montant", "Modifiez Aller ou Retour dans l'onglet Grille : Total et Montant se "
                                    "recalculent automatiquement."),
            ("", ""), ("GRILLES TARIFAIRES CHARGÉES", "")]
    for k, (ds, label) in TARIFF_DATASETS.items():
        t = eng.tariffs.tables.get(k)
        rows.append((label, ("%s — jeu « %s »" % (t.info, ds)) if t else "non chargée (estimations au km)"))
    return rows


def write_output(eng):
    os.makedirs(eng.result_dir, exist_ok=True)
    base = "grille_defraiement_%s_%s" % (slug(eng.ev["nom"]), eng.p["date_aller"].strftime("%Y-%m-%d"))
    for r in eng.cities:
        r["total"] = None if (r["aller"] is None or r["retour"] is None) else round(r["aller"] + r["retour"], 2)
        if isinstance(r.get("remarques"), list):
            r["remarques"] = "; ".join(r["remarques"])
        if r.get("dist_km") is not None:
            r["dist_km"] = round(r["dist_km"], 1)
    if ensure_openpyxl(eng.log):
        path = os.path.join(eng.result_dir, base + ".xlsx")
        try:
            _write_xlsx(path, eng)
        except PermissionError:
            path = os.path.join(eng.result_dir, base + "_%s.xlsx" % dt.datetime.now().strftime("%H%M%S"))
            _write_xlsx(path, eng)
        eng.log("\nTerminé ! Fichier : %s" % path)
        return path
    eng.log("   ⚠ Excel indisponible : résultats enregistrés en CSV (lisibles avec Excel).")
    path = os.path.join(eng.result_dir, base + "_grille.csv")
    for suffix, cols, rows in (("_grille.csv", GRID_COLS, eng.grid), ("_villes.csv", CITY_COLS, eng.cities),
                               ("_trajets.csv", TRIP_COLS, eng.trips)):
        with open(os.path.join(eng.result_dir, base + suffix), "w", encoding="utf-8-sig", newline="") as f:
            w = csv.writer(f, delimiter=";")
            w.writerow([c[0] for c in cols])
            for r in rows:
                w.writerow([("%.2f" % r[k]).replace(".", ",") if (k in MONEY and r.get(k) is not None)
                            else ("" if r.get(k) is None else r.get(k)) for _, k, _ in cols])
    eng.log("\nTerminé ! Fichiers dans : %s" % eng.result_dir)
    return path


def _write_xlsx(path, eng):
    from openpyxl import Workbook
    from openpyxl.styles import Alignment, Font, PatternFill
    from openpyxl.utils import get_column_letter

    font = Font(name="Arial", size=10)
    bold = Font(name="Arial", size=10, bold=True)
    head_font = Font(name="Arial", size=10, bold=True, color="FFFFFF")
    head_fill = PatternFill("solid", fgColor="1F4E78")
    warn_fill = PatternFill("solid", fgColor="FCE4D6")
    money_fmt = '#,##0.00 "€"'

    wb = Workbook()

    def sheet(ws, cols, rows, flag_key=None, formulas=None):
        for ci, (title, _, width) in enumerate(cols, 1):
            cell = ws.cell(row=1, column=ci, value=title)
            cell.font, cell.fill = head_font, head_fill
            cell.alignment = Alignment(vertical="center", wrap_text=True)
            ws.column_dimensions[get_column_letter(ci)].width = width
        ws.row_dimensions[1].height = 30
        idx = {k: i for i, (_, k, _) in enumerate(cols, 1)}
        for ri, r in enumerate(rows, 2):
            flagged = bool(flag_key and r.get(flag_key))
            for ci, (_, k, _) in enumerate(cols, 1):
                v = r.get(k)
                if formulas and k in formulas:
                    v = formulas[k](ri, idx, r)
                cell = ws.cell(row=ri, column=ci, value=v)
                cell.font = font
                cell.alignment = Alignment(vertical="top", wrap_text=k in ("remarques", "detail", "itineraire"))
                if k in MONEY:
                    cell.number_format = money_fmt
                if flagged:
                    cell.fill = warn_fill
        ws.freeze_panes = "A2"
        if rows:
            ws.auto_filter.ref = "A1:%s%d" % (get_column_letter(len(cols)), len(rows) + 1)

    step = eng.p["arrondi"]

    def f_total(ri, idx, r):
        if r.get("aller") is None and r.get("retour") is None:
            return None
        return "=%s%d+%s%d" % (get_column_letter(idx["aller"]), ri, get_column_letter(idx["retour"]), ri)

    def f_montant(ri, idx, r):
        if r.get("total") is None:
            return None
        t = "%s%d" % (get_column_letter(idx["total"]), ri)
        return ("=CEILING(ROUND(%s,2),%d)" % (t, step)) if step else ("=ROUND(%s,2)" % t)

    ws = wb.active
    ws.title = "Grille"
    sheet(ws, GRID_COLS, eng.grid, "a_verifier", {"total": f_total, "montant": f_montant})
    for ri in range(2, len(eng.grid) + 2):
        ws.cell(row=ri, column=8).font = bold
    n = len(eng.grid) + 3
    ws.cell(row=n, column=1, value="Lignes en orange : à vérifier (prix estimé, tarif approché ou ville "
                                   "sans trajet). Vous pouvez corriger Aller/Retour : Total et Montant "
                                   "se recalculent.").font = Font(name="Arial", size=9, italic=True)

    def f_total_city(ri, idx, r):
        if r.get("total") is None:
            return None
        return "=%s%d+%s%d" % (get_column_letter(idx["aller"]), ri, get_column_letter(idx["retour"]), ri)

    flagged_cities = []
    for r in eng.cities:
        rr = dict(r)
        rr["_flag"] = "x" if (r["aller"] is None or r["retour"] is None or r["estimated"] or r["approx"]) else ""
        flagged_cities.append(rr)
    sheet(wb.create_sheet("Détail villes"), CITY_COLS, flagged_cities, "_flag", {"total": f_total_city})
    sheet(wb.create_sheet("Détail trajets"), TRIP_COLS, eng.trips, "estime")

    ws = wb.create_sheet("Paramètres et méthode")
    ws.column_dimensions["A"].width = 30
    ws.column_dimensions["B"].width = 120
    for ri, (k, v) in enumerate(meta_rows(eng), 1):
        a, b = ws.cell(row=ri, column=1, value=k), ws.cell(row=ri, column=2, value=v)
        a.font, b.font = bold, font
        b.alignment = Alignment(wrap_text=True, vertical="top")
    wb.save(path)


# --------------------------------------------------------------------------
# Interface graphique
# --------------------------------------------------------------------------

def open_path(path):
    try:
        if sys.platform.startswith("win"):
            os.startfile(path)  # noqa
        elif sys.platform == "darwin":
            subprocess.Popen(["open", path])
        else:
            subprocess.Popen(["xdg-open", path])
    except Exception:
        pass


def run_gui():
    try:
        import tkinter as tk
        from tkinter import messagebox, ttk
        from tkinter.scrolledtext import ScrolledText
    except ImportError:
        print("L'interface graphique (tkinter) n'est pas disponible sur cet ordinateur.\n"
              "Installez Python depuis https://www.python.org/downloads/ (il inclut tkinter),\n"
              "ou utilisez le mode texte :  python grille_defraiement.py --aide")
        sys.exit(1)
    import webbrowser

    cfg = load_config()
    root = tk.Tk()
    root.title("Grille de défraiement train — v%s" % VERSION)
    root.minsize(700, 680)
    root.geometry("820x780")

    msgs = queue.Queue()
    state = {"thread": None, "stop": None, "result": None, "auto_retour": True}

    main = ttk.Frame(root, padding=12)
    main.pack(fill="both", expand=True)

    def section(title):
        f = ttk.LabelFrame(main, text=title, padding=(10, 6))
        f.pack(fill="x", pady=4)
        f.columnconfigure(2, weight=1)
        return f

    V = {k: tk.StringVar(value=str(cfg.get(k, ""))) for k in
         ("ville", "gare", "date_aller", "heure_aller", "date_retour", "heure_retour", "heure_limite",
          "arrondi", "cle_api", "departements")}
    hints = {k: tk.StringVar() for k in ("date_aller", "date_retour")}
    inputs = []

    def add_row(frame, r, label, var, width=None, hint=None, combo=None, show=None):
        ttk.Label(frame, text=label).grid(row=r, column=0, sticky="w", padx=(0, 10), pady=3)
        if combo:
            w = ttk.Combobox(frame, textvariable=var, values=combo, state="readonly", width=24)
        else:
            w = ttk.Entry(frame, textvariable=var, width=width or 36, show=show or "")
        w.grid(row=r, column=1, sticky="w", pady=3)
        inputs.append(w)
        if isinstance(hint, tk.StringVar):
            ttk.Label(frame, textvariable=hint, foreground="#555").grid(row=r, column=2, sticky="w", padx=(10, 0))
        elif hint:
            ttk.Label(frame, text=hint, foreground="#555").grid(row=r, column=2, sticky="w", padx=(10, 0))
        return w

    f1 = section("1. L'événement")
    add_row(f1, 0, "Ville de l'événement", V["ville"])
    add_row(f1, 1, "Gare d'arrivée (facultatif)", V["gare"],
            hint="si plusieurs gares (ex. Paris Gare de Lyon)")

    f2 = section("2. Dates et horaires")
    add_row(f2, 0, "Aller : date du vendredi", V["date_aller"], width=14, hint=hints["date_aller"])
    add_row(f2, 1, "Aller : trains à partir de", V["heure_aller"], width=8)
    e_retour = add_row(f2, 2, "Retour : date du dimanche", V["date_retour"], width=14, hint=hints["date_retour"])
    add_row(f2, 3, "Retour : trains à partir de", V["heure_retour"], width=8)
    add_row(f2, 4, "Trains jusqu'à (aller et retour)", V["heure_limite"], width=8)

    f3 = section("3. Règles de calcul")
    ttk.Label(f3, text="Chaque ville : trajet le moins cher en 2nde classe. Département : la plus chère "
                       "des 3 villes.", foreground="#555").grid(row=0, column=0, columnspan=3, sticky="w", pady=(0, 4))
    add_row(f3, 1, "Arrondir le montant", V["arrondi"], combo=list(ARRONDIS))
    add_row(f3, 2, "Départements (facultatif)", V["departements"], width=24,
            hint="vide = toute la métropole · essai : 13, 69")

    f4 = section("4. Clé API SNCF (gratuite, à saisir une seule fois)")
    e_key = add_row(f4, 0, "Clé", V["cle_api"], show="•")
    kb = ttk.Frame(f4)
    kb.grid(row=1, column=1, sticky="w")
    ttk.Button(kb, text="Obtenir une clé gratuite", command=lambda: webbrowser.open(API_KEY_URL)).pack(side="left")
    show_var = tk.BooleanVar(value=False)
    ttk.Checkbutton(kb, text="afficher la clé", variable=show_var,
                    command=lambda: e_key.configure(show="" if show_var.get() else "•")).pack(side="left", padx=10)

    def refresh_hints(*_):
        for k, wanted in (("date_aller", 4), ("date_retour", 6)):
            txt = V[k].get().strip()
            if not txt:
                hints[k].set("format JJ/MM/AAAA")
                continue
            try:
                d = parse_date(txt)
                hints[k].set("→ " + date_fr(d) + ("" if d.weekday() == wanted else
                                                  "   ⚠ pas un %s" % JOURS[wanted]))
            except ValueError:
                hints[k].set("⚠ date non reconnue (JJ/MM/AAAA)")

    def on_aller_change(*_):
        try:
            d = parse_date(V["date_aller"].get())
        except ValueError:
            refresh_hints()
            return
        if state["auto_retour"] or not V["date_retour"].get().strip():
            state["auto_retour"] = True
            V["date_retour"].set((d + dt.timedelta(days=2)).strftime("%d/%m/%Y"))
        refresh_hints()

    V["date_aller"].trace_add("write", on_aller_change)
    e_retour.bind("<Key>", lambda _e: state.__setitem__("auto_retour", False))
    V["date_retour"].trace_add("write", refresh_hints)
    if V["date_retour"].get().strip():
        state["auto_retour"] = False
        refresh_hints()
    else:
        on_aller_change()

    bar = ttk.Frame(main)
    bar.pack(fill="x", pady=(8, 4))
    b_run = ttk.Button(bar, text="▶  Lancer le calcul")
    b_run.pack(side="left")
    b_stop = ttk.Button(bar, text="■  Arrêter", state="disabled")
    b_stop.pack(side="left", padx=8)
    b_open = ttk.Button(bar, text="Ouvrir le dossier des résultats",
                        command=lambda: (os.makedirs(RESULT_DIR, exist_ok=True), open_path(RESULT_DIR)))
    b_open.pack(side="right")

    prog = ttk.Progressbar(main, mode="determinate", maximum=100)
    prog.pack(fill="x", pady=(4, 0))
    status = tk.StringVar(value="Prêt.")
    ttk.Label(main, textvariable=status).pack(anchor="w")
    logbox = ScrolledText(main, height=14, wrap="word", state="disabled", font=("Consolas", 9)
                          if sys.platform.startswith("win") else None)
    logbox.pack(fill="both", expand=True, pady=(4, 0))

    def log(msg):
        logbox.configure(state="normal")
        logbox.insert("end", msg + "\n")
        logbox.see("end")
        logbox.configure(state="disabled")

    def set_running(running):
        b_run.configure(state="disabled" if running else "normal")
        b_stop.configure(state="normal" if running else "disabled")
        for w in inputs:
            try:
                w.configure(state="disabled" if running else ("readonly" if isinstance(w, ttk.Combobox) else "normal"))
            except Exception:
                pass

    def current_values():
        return {k: v.get() for k, v in V.items()}

    def start():
        raw = current_values()
        try:
            params, warnings = build_params(raw)
        except UserError as e:
            messagebox.showerror("Saisie à corriger", str(e))
            return
        if warnings and not messagebox.askyesno("Vérification", "\n".join(warnings) + "\n\nContinuer quand même ?"):
            return
        cfg.update(raw)
        save_config(cfg)
        logbox.configure(state="normal")
        logbox.delete("1.0", "end")
        logbox.configure(state="disabled")
        prog["value"] = 0
        stop = threading.Event()
        state["stop"] = stop

        def worker():
            try:
                eng = Engine(params, cfg["avance"], log=lambda m: msgs.put(("log", m)),
                             progress=lambda d, t, l: msgs.put(("progress", (d, t, l))), stop_event=stop)
                msgs.put(("done", eng.run()))
            except Cancelled:
                msgs.put(("cancelled", None))
            except UserError as e:
                msgs.put(("error", str(e)))
            except Exception:
                tb = traceback.format_exc()
                try:
                    os.makedirs(RESULT_DIR, exist_ok=True)
                    with open(os.path.join(RESULT_DIR, "erreur.txt"), "w", encoding="utf-8") as f:
                        f.write(tb)
                except Exception:
                    pass
                msgs.put(("crash", tb))

        set_running(True)
        status.set("Démarrage…")
        t = threading.Thread(target=worker, daemon=True)
        state["thread"] = t
        t.start()

    def stop_run():
        if state["stop"]:
            state["stop"].set()
            status.set("Arrêt en cours… (le travail déjà fait est conservé)")

    b_run.configure(command=start)
    b_stop.configure(command=stop_run)

    def poll():
        try:
            while True:
                kind, val = msgs.get_nowait()
                if kind == "log":
                    log(val)
                elif kind == "progress":
                    d, t, label = val
                    prog["value"] = 100.0 * d / max(1, t)
                    status.set("Département %d/%d : %s" % (min(d + 1, t), t, label) if d < t else label)
                elif kind == "done":
                    set_running(False)
                    prog["value"] = 100
                    status.set("Terminé.")
                    if messagebox.askyesno("Terminé", "La grille est prête :\n%s\n\nL'ouvrir maintenant ?" % val):
                        open_path(val)
                elif kind == "cancelled":
                    set_running(False)
                    status.set("Arrêté. Relancez quand vous voulez : le travail déjà fait ne sera pas refait.")
                    log("\nArrêté par l'utilisateur.")
                elif kind == "error":
                    set_running(False)
                    status.set("Interrompu.")
                    log("\n⚠ " + val)
                    messagebox.showerror("Problème", val)
                elif kind == "crash":
                    set_running(False)
                    status.set("Erreur inattendue.")
                    log("\n" + val)
                    messagebox.showerror("Erreur inattendue",
                                         "Une erreur inattendue s'est produite. Le détail est enregistré dans\n"
                                         + os.path.join(RESULT_DIR, "erreur.txt"))
        except queue.Empty:
            pass
        root.after(150, poll)

    def on_close():
        if state["stop"]:
            state["stop"].set()
        cfg.update(current_values())
        save_config(cfg)
        root.destroy()

    root.protocol("WM_DELETE_WINDOW", on_close)
    log("Bienvenue ! Remplissez les champs puis cliquez sur « Lancer le calcul ».\n"
        "Conseil : faites d'abord un essai sur 2 départements (ex. « 13, 69 ») pour vérifier que tout "
        "fonctionne.\nUn calcul complet (France métropolitaine) prend environ 30 à 60 minutes ; vous pouvez "
        "l'arrêter et le reprendre, rien n'est refait.")
    poll()
    root.mainloop()


# --------------------------------------------------------------------------
# Mode texte (sans fenêtre)
# --------------------------------------------------------------------------

def run_cli(argv):
    import argparse
    ap = argparse.ArgumentParser(description="Grille de défraiement train (mode texte)")
    ap.add_argument("--ville", required=True)
    ap.add_argument("--gare", default="")
    ap.add_argument("--aller", required=True, help="date du vendredi, JJ/MM/AAAA")
    ap.add_argument("--retour", default="", help="date du dimanche (par défaut : aller + 2 jours)")
    ap.add_argument("--heure-aller", default="16:00")
    ap.add_argument("--heure-retour", default="16:00")
    ap.add_argument("--heure-limite", default="23:59")
    ap.add_argument("--arrondi", default="à l'euro supérieur", choices=list(ARRONDIS))
    ap.add_argument("--deps", default="", help="ex. 13,69 (vide = toute la métropole)")
    ap.add_argument("--cle", default="", help="clé API SNCF (sinon celle de config.json)")
    a = ap.parse_args(argv)
    cfg = load_config()
    retour = a.retour
    if not retour:
        try:
            retour = (parse_date(a.aller) + dt.timedelta(days=2)).strftime("%d/%m/%Y")
        except ValueError:
            retour = ""
    raw = {"ville": a.ville, "gare": a.gare, "date_aller": a.aller, "date_retour": retour,
           "heure_aller": a.heure_aller, "heure_retour": a.heure_retour, "heure_limite": a.heure_limite,
           "arrondi": a.arrondi, "departements": a.deps,
           "cle_api": a.cle or cfg.get("cle_api", "")}
    try:
        params, warnings = build_params(raw)
        for w in warnings:
            print("⚠ " + w)

        def progress(d, t, label):
            pass
        path = Engine(params, cfg["avance"], log=print, progress=progress).run()
        print(path)
        return 0
    except UserError as e:
        print("\n⚠ " + str(e))
        return 1
    except KeyboardInterrupt:
        print("\nArrêté.")
        return 1


if __name__ == "__main__":
    args = sys.argv[1:]
    if args and args[0] in ("--aide", "--help", "-h"):
        run_cli(["--help"])
    elif args:
        sys.exit(run_cli(args))
    else:
        run_gui()

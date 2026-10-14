# -*- coding: utf-8 -*-
"""
Site web : grille de défraiement train par département.

Le calcul lui-même est dans grille_defraiement.py (le même moteur que la version
ordinateur). Ce fichier ne fait que l'interface web :
  - un formulaire (ville, dates, heures, arrondi) ;
  - une file d'attente : un seul calcul à la fois, pour ménager la clé API SNCF ;
  - une page de suivi par calcul (on peut la fermer et revenir avec la même adresse) ;
  - le téléchargement du fichier Excel.

Réglages (dans les « Secrets » de l'hébergeur, jamais dans les fichiers) :
  SNCF_API_KEY = "votre clé API SNCF"        (obligatoire)
  APP_PASSWORD = "un mot de passe"           (facultatif : protège l'accès au site)
"""

import collections
import datetime as dt
import hashlib
import json
import os
import queue
import threading
import time
import traceback
import uuid

import streamlit as st

import grille_defraiement as G

st.set_page_config(page_title="Grille de défraiement train", page_icon="🚆", layout="centered")

WEB_RESULTS = os.path.join(G.BASE_DIR, "resultats_web")
FIELDS = ("ville", "gare", "date_aller", "heure_aller", "date_retour", "heure_retour",
          "heure_limite", "arrondi", "departements")


def secret(name):
    try:
        value = st.secrets.get(name)
    except Exception:
        value = None
    return str(value or os.environ.get(name) or "").strip()


# --------------------------------------------------------------------------
# Calculs en arrière-plan (partagés entre tous les visiteurs du site)
# --------------------------------------------------------------------------

def job_key(raw):
    data = {k: str(raw.get(k, "")).strip().lower() for k in FIELDS}
    return hashlib.sha1(json.dumps(data, sort_keys=True).encode()).hexdigest()[:16]


class Job:
    def __init__(self, raw, params=None, jid=None):
        self.id = jid or uuid.uuid4().hex[:10]
        self.raw = {k: raw.get(k, "") for k in FIELDS}
        self.key = job_key(raw)
        self.params = params
        self.created = time.time()
        self.finished = None
        self.status = "queued"            # queued, running, done, error, cancelled
        self.progress = (0, 0, "")
        self.logs = collections.deque(maxlen=600)
        self.result = None
        self.error = None
        self.trace = None
        self.grid = None
        self.stop = threading.Event()
        self.dir = os.path.join(WEB_RESULTS, self.id)

    @property
    def title(self):
        try:
            a = G.date_fr(G.parse_date(self.raw["date_aller"]))
            r = G.date_fr(G.parse_date(self.raw["date_retour"]))
        except ValueError:
            a, r = self.raw["date_aller"], self.raw["date_retour"]
        return "%s — %s → %s" % (self.raw["ville"], a, r)

    def save(self):
        os.makedirs(self.dir, exist_ok=True)
        meta = {"id": self.id, "raw": self.raw, "created": self.created, "finished": self.finished,
                "status": self.status, "result": self.result, "error": self.error, "grid": self.grid}
        with open(os.path.join(self.dir, "job.json"), "w", encoding="utf-8") as f:
            json.dump(meta, f, ensure_ascii=False)


class Manager:
    def __init__(self):
        self.jobs = collections.OrderedDict()
        self.q = queue.Queue()
        self.lock = threading.Lock()
        self.current = None
        self._load()
        threading.Thread(target=self._worker, daemon=True).start()

    def _load(self):
        """Retrouve les calculs terminés (si le site n'a pas redémarré entre-temps)."""
        if not os.path.isdir(WEB_RESULTS):
            return
        metas = []
        for d in os.listdir(WEB_RESULTS):
            try:
                with open(os.path.join(WEB_RESULTS, d, "job.json"), encoding="utf-8") as f:
                    metas.append(json.load(f))
            except Exception:
                continue
        for m in sorted(metas, key=lambda m: m.get("created") or 0):
            if m.get("status") not in ("done", "error", "cancelled"):
                continue
            j = Job(m["raw"], jid=m["id"])
            j.created, j.finished, j.status = m.get("created"), m.get("finished"), m["status"]
            j.result, j.error, j.grid = m.get("result"), m.get("error"), m.get("grid")
            self.jobs[j.id] = j

    def submit(self, raw, params, force=False):
        key = job_key(raw)
        with self.lock:
            if not force:
                for j in reversed(self.jobs.values()):
                    if j.key != key:
                        continue
                    if j.status in ("queued", "running"):
                        return j
                    if j.status == "done" and j.result and os.path.exists(j.result):
                        return j
            job = Job(raw, params)
            self.jobs[job.id] = job
        self.q.put(job.id)
        return job

    def cancel(self, job):
        job.stop.set()
        if job.status == "queued":
            job.status = "cancelled"
            job.finished = time.time()

    def position(self, job):
        """Nombre de calculs à passer avant celui-ci."""
        ahead = 0
        for j in self.jobs.values():
            if j is job:
                break
            if j.status in ("queued", "running"):
                ahead += 1
        return ahead

    def recent(self, n=8):
        return list(reversed(self.jobs.values()))[:n]

    def _worker(self):
        while True:
            jid = self.q.get()
            job = self.jobs.get(jid)
            if job is None or job.status != "queued":
                continue
            job.status = "running"
            self.current = job

            def progress(d, t, label, job=job):
                job.progress = (d, t, label)
            try:
                cfg = G.load_config()
                eng = G.Engine(job.params, cfg["avance"], log=job.logs.append, progress=progress,
                               stop_event=job.stop, result_dir=job.dir)
                job.result = eng.run()
                job.grid = [{k: g.get(k) for k in ("dep_code", "dep_nom", "ville", "aller", "retour",
                                                    "total", "montant", "a_verifier", "remarques")}
                            for g in eng.grid]
                job.status = "done"
            except G.Cancelled:
                job.status = "cancelled"
            except G.UserError as e:
                job.status, job.error = "error", str(e)
            except Exception:
                job.status, job.error = "error", "Erreur inattendue pendant le calcul."
                job.trace = traceback.format_exc()
            finally:
                job.finished = time.time()
                self.current = None
                try:
                    job.save()
                except Exception:
                    pass


@st.cache_resource
def get_manager():
    return Manager()


# --------------------------------------------------------------------------
# Pages
# --------------------------------------------------------------------------

STATUS_LABEL = {"queued": "⏳ en attente", "running": "⚙️ en cours", "done": "✅ terminé",
                "error": "⚠️ erreur", "cancelled": "✖️ annulé"}


def go(job_id=None):
    st.query_params.clear()
    if job_id:
        st.query_params["job"] = job_id
    st.rerun()


def check_password():
    pw = secret("APP_PASSWORD")
    if not pw or st.session_state.get("auth"):
        return True
    with st.form("login"):
        typed = st.text_input("Mot de passe", type="password")
        ok = st.form_submit_button("Entrer")
    if ok:
        if typed == pw:
            st.session_state["auth"] = True
            st.rerun()
        st.error("Mot de passe incorrect.")
    return False


def next_friday():
    d = dt.date.today() + dt.timedelta(days=1)
    while d.weekday() != 4:
        d += dt.timedelta(days=1)
    return d


def page_form(mgr, api_key):
    st.write("Pour chaque département : les 3 villes les plus peuplées, le trajet **le moins cher en "
             "2nde classe** pour chacune, et on retient **la plus chère des trois**.")

    if "aller" not in st.session_state:
        st.session_state["aller"] = next_friday()
        st.session_state["retour"] = st.session_state["aller"] + dt.timedelta(days=2)

    def aller_changed():
        st.session_state["retour"] = st.session_state["aller"] + dt.timedelta(days=2)

    ville = st.text_input("Ville de l'événement", placeholder="ex. Marseille")
    gare = st.text_input("Gare d'arrivée (facultatif)", placeholder="ex. Paris Gare de Lyon",
                         help="Seulement si la ville a plusieurs gares et que vous voulez en imposer une. "
                              "Sinon, pour chaque ville de départ, la gare la moins chère est choisie.")
    c1, c2 = st.columns(2)
    c1.date_input("Aller : le vendredi", key="aller", format="DD/MM/YYYY", on_change=aller_changed)
    c2.date_input("Retour : le dimanche", key="retour", format="DD/MM/YYYY")
    h1, h2, h3 = st.columns(3)
    ha = h1.time_input("Trains aller à partir de", value=dt.time(16, 0), step=900)
    hr = h2.time_input("Trains retour à partir de", value=dt.time(16, 0), step=900)
    hl = h3.time_input("Trains jusqu'à", value=dt.time(23, 59), step=60)
    arrondi = st.selectbox("Arrondir le montant", list(G.ARRONDIS), index=1)
    with st.expander("Option : limiter à quelques départements (pour un essai rapide)"):
        deps = st.text_input("Départements", placeholder="ex. 13, 69 — laisser vide pour toute la France "
                                                          "métropolitaine")

    aller, retour = st.session_state["aller"], st.session_state["retour"]
    if aller.weekday() != 4:
        st.warning("La date aller (%s) n'est pas un vendredi." % G.date_fr(aller))
    if retour.weekday() != 6:
        st.warning("La date retour (%s) n'est pas un dimanche." % G.date_fr(retour))

    if st.button("Lancer le calcul", type="primary", width="stretch"):
        raw = {"ville": ville, "gare": gare, "date_aller": aller.strftime("%d/%m/%Y"),
               "date_retour": retour.strftime("%d/%m/%Y"), "heure_aller": ha.strftime("%H:%M"),
               "heure_retour": hr.strftime("%H:%M"), "heure_limite": hl.strftime("%H:%M"),
               "arrondi": arrondi, "departements": deps, "cle_api": api_key}
        try:
            params, _ = G.build_params(raw)
        except G.UserError as e:
            st.error(str(e))
            return
        job = mgr.submit(raw, params)
        go(job.id)

    recent = mgr.recent()
    if recent:
        st.divider()
        st.caption("Calculs récents")
        for j in recent:
            if st.button("%s · %s" % (STATUS_LABEL.get(j.status, j.status), j.title), key="r_" + j.id):
                go(j.id)


def show_grid(job):
    rows = []
    for g in job.grid or []:
        rows.append({"Code": g["dep_code"], "Département": g["dep_nom"], "Ville retenue": g["ville"],
                     "Aller": G.eur(g["aller"]), "Retour": G.eur(g["retour"]),
                     "Montant": G.eur(g["montant"]), "À vérifier": g["a_verifier"] or ""})
    if rows:
        n = sum(1 for r in rows if r["À vérifier"])
        if n:
            st.caption("%d département(s) à vérifier : le détail est dans le fichier Excel (lignes en orange)." % n)
        st.dataframe(rows, hide_index=True)


@st.fragment(run_every=3)
def live_status(mgr, job):
    """Partie de la page rafraîchie toutes les 3 secondes pendant le calcul."""
    if job.status not in ("queued", "running"):
        st.rerun()
    if job.status == "queued":
        ahead = mgr.position(job)
        st.info("En attente : %d calcul(s) passe(nt) avant le vôtre. Un seul calcul tourne à la fois." % ahead
                if ahead else "Démarrage…")
    else:
        d, t, label = job.progress
        if not t:
            st.progress(0.0, text="Préparation : vérification de la clé et chargement des tarifs SNCF…")
        else:
            st.progress(min(1.0, d / t), text=("Département %d/%d : %s" % (d + 1, t, label))
                        if d < t else (label or "Écriture du fichier…"))
    st.info("Comptez 30 à 60 minutes pour toute la France. **Vous pouvez fermer cette page** : gardez "
            "son adresse (favori ou copier-coller) pour revenir chercher le résultat.")
    if job.logs:
        with st.expander("Journal détaillé", expanded=False):
            st.code("\n".join(list(job.logs)[-300:]), language=None)


def page_job(mgr, jid):
    job = mgr.jobs.get(jid)
    if job is None:
        st.warning("Ce calcul est introuvable : le site a sans doute redémarré entre-temps. Relancez-le.")
        if st.button("Nouveau calcul", type="primary"):
            go()
        return

    st.subheader(job.title)
    r = job.raw
    st.caption("Trains aller dès %s, retour dès %s, jusqu'à %s · arrondi : %s%s" % (
        r["heure_aller"], r["heure_retour"], r["heure_limite"], r["arrondi"],
        (" · départements : %s" % r["departements"]) if r["departements"].strip() else ""))

    running = job.status in ("queued", "running")
    if running:
        live_status(mgr, job)
    if job.status == "done":
        st.success("C'est prêt !")
        if job.result and os.path.exists(job.result):
            with open(job.result, "rb") as f:
                data = f.read()
            xlsx = job.result.endswith(".xlsx")
            st.download_button("⬇️ Télécharger le fichier Excel" if xlsx else "⬇️ Télécharger le résultat",
                               data=data, file_name=os.path.basename(job.result), type="primary",
                               mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"
                               if xlsx else "text/csv", width="stretch")
        else:
            st.warning("Le fichier n'est plus disponible (le site a redémarré). Cliquez sur « Recalculer ».")
        show_grid(job)
    elif job.status == "error":
        st.error(job.error or "Erreur.")
        if job.trace:
            with st.expander("Détail technique"):
                st.code(job.trace)
    elif job.status == "cancelled":
        st.warning("Calcul annulé.")

    if job.logs and not running:
        with st.expander("Journal détaillé", expanded=False):
            st.code("\n".join(list(job.logs)[-300:]), language=None)

    c1, c2 = st.columns(2)
    if running:
        if c1.button("Annuler ce calcul"):
            mgr.cancel(job)
            st.rerun()
    elif c1.button("Recalculer", help="Relance le calcul avec les mêmes paramètres"):
        api_key = secret("SNCF_API_KEY")
        raw = dict(job.raw, cle_api=api_key)
        try:
            params, _ = G.build_params(raw)
            go(mgr.submit(raw, params, force=True).id)
        except G.UserError as e:
            st.error(str(e))
    if c2.button("Nouveau calcul"):
        go()



def main():
    st.title("🚆 Grille de défraiement train")
    if not check_password():
        st.stop()
    api_key = secret("SNCF_API_KEY")
    if not api_key:
        st.error("Le site n'est pas encore configuré : la clé API SNCF manque. Ajoutez-la dans les "
                 "« Secrets » de l'application sous la forme :  SNCF_API_KEY = \"votre-clé\"")
        st.stop()
    mgr = get_manager()
    jid = st.query_params.get("job")
    if jid:
        page_job(mgr, jid)
    else:
        page_form(mgr, api_key)


main()

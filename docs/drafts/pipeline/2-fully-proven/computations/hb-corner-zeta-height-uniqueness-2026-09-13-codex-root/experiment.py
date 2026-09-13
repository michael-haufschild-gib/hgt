import concurrent.futures as cf
import json
import os
import time

import mpmath as mp

from kernel import diagnostic


SLICE = os.environ["ZERO_SLICE"]
OUT = "results-" + SLICE + ".jsonl"
SCALES = ["5.436563656918090470720574942705324995514494187399919149933935255448153260707095", "6", "10", "30"]


def find_roots(height, L, intervals, tol):
    grid = [mp.mpf(i) / (2 * intervals) for i in range(intervals + 1)]
    vals = [(s, diagnostic(s, height, L)[0]) for s in grid]
    roots = []
    for (a, fa), (b, fb) in zip(vals, vals[1:]):
        if fa == 0 or fa * fb < 0:
            try:
                r = mp.findroot(lambda x: diagnostic(x, height, L)[0], (a, b), tol=tol, maxsteps=60)
            except Exception:
                continue
            if mp.mpf("1e-25") < r < mp.mpf(".5") - mp.mpf("1e-25") and not any(abs(r-x) < mp.mpf("1e-30") for x in roots):
                roots.append(r)
    return roots


def scan(job):
    n, height_text, L_text = job
    mp.mp.dps = 80
    h, L = mp.mpf(height_text), mp.mpf(L_text)
    out = {"kind":"scan", "slice":SLICE, "n":n, "height":height_text, "L":L_text}
    try:
        coarse = find_roots(h, L, 96, mp.mpf("1e-55"))
        fine = find_roots(h, L, 192, mp.mpf("1e-55"))
        out["coarse_roots"] = [mp.nstr(x,65) for x in coarse]
        out["fine_roots"] = [mp.nstr(x,65) for x in fine]
        out["grid_agree"] = len(coarse)==len(fine) and all(abs(a-b)<mp.mpf("1e-35") for a,b in zip(coarse,fine))
    except Exception as exc:
        out["error"] = str(exc)[:300]
    return out


def validate(job):
    n, height_text, L_text, root_text = job
    out = {"kind":"validation", "slice":SLICE, "n":n, "height":height_text, "L":L_text,
           "reported_sigma":root_text, "precision":[]}
    for dps in (120, 180):
        mp.mp.dps = dps
        h, L, guess = mp.mpf(height_text), mp.mpf(L_text), mp.mpf(root_text)
        try:
            eps = mp.mpf("1e-10")
            r = mp.findroot(lambda x: diagnostic(x,h,L)[0], (guess-eps,guess+eps),
                            tol=mp.power(10,-dps+18), maxsteps=80)
            score, nr, nd, rim = diagnostic(r,h,L)
            reflected = diagnostic(1-r,h,L)[0]
            out["precision"].append({"dps":dps,"sigma":mp.nstr(r,dps),"score":mp.nstr(score,dps),
                "W_R_abs":mp.nstr(nr,dps),"W_Delta_abs":mp.nstr(nd,dps),"ratio_imag":mp.nstr(rim,dps),
                "reflection_odd_defect":mp.nstr(reflected+score,dps)})
        except Exception as exc:
            out["error"] = str(exc)[:300]
    return out


def emit(row):
    with open(OUT,"a") as f:
        f.write(json.dumps(row)+"\n")
    if row["kind"] != "validation" or row.get("error"):
        print(json.dumps(row),flush=True)


def main():
    started=time.monotonic()
    zeros=json.load(open("zeros.json"))
    if SLICE=="low":
        selected=[z for z in zeros if 1<=z["n"]<=128]
    elif SLICE=="distant":
        selected=[z for z in zeros if 257<=z["n"]<=320 or 1<=z["n"]<=8]
    else:
        raise ValueError(SLICE)
    jobs=[(z["n"],z["rho"][1],L) for z in selected for L in SCALES]
    with cf.ProcessPoolExecutor(max_workers=14) as pool:
        rows=list(pool.map(scan,jobs,chunksize=1))
        for row in rows:
            emit(row)
        candidates=[(r["n"],r["height"],r["L"],x) for r in rows if r.get("grid_agree") for x in r.get("fine_roots",[])]
        for row in pool.map(validate,candidates,chunksize=1):
            emit(row)
    summary=[]
    for L in SCALES:
        rr=[r for r in rows if r["L"]==L]
        summary.append({"L":L,"cases":len(rr),"unstable":sum(not r.get("grid_agree",False) for r in rr),
            "offcritical_cases":sum(bool(r.get("fine_roots")) for r in rr),
            "offcritical_roots":sum(len(r.get("fine_roots",[])) for r in rr)})
    emit({"kind":"gate","slice":SLICE,"summary":summary,
          "all_cases_processed":len(rows)==4*len(selected),"validation_count":len(candidates)})
    emit({"kind":"complete","slice":SLICE,"seconds":time.monotonic()-started})


if __name__=="__main__":
    main()

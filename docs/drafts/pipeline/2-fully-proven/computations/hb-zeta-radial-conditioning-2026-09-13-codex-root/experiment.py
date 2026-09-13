import concurrent.futures as cf
import json
import math
import os
import time

import mpmath as mp

DEADLINE = float(os.environ["CAMPAIGN_DEADLINE"])


def budget():
    if time.monotonic() > DEADLINE - 4:
        raise TimeoutError("family deadline")


def cstr(z, digits=50):
    return [mp.nstr(mp.re(z), digits), mp.nstr(mp.im(z), digits)]


def pars(rho, branch, side):
    s = rho - 2 if branch else -rho - 1
    w = -1 - rho / 2 if side else -2 + rho / 2
    c0 = (5 * s * s + 15 * s + 4) / 4
    c1 = s * (s - 1) * ((s + 2) * (2 * s + 3) - (w + 1) * (w + 2) / 2) / 4
    return w, s, c0, c1


def entry_hyper(rho, branch, side):
    budget()
    w, s, c0, c1 = pars(rho, branch, side)
    return c0 * mp.hyp2f1(-2 * s, 3, w + 4, -1) + 12 * c1 / ((w + 4) * (w + 5)) * mp.hyp2f1(-2 * s, 5, w + 6, -1)


def metrics(rho, evaluator=entry_hyper):
    A = mp.matrix([[evaluator(rho, False, False), evaluator(rho, False, True)],
                   [evaluator(rho, True, False), evaluator(rho, True, True)]])
    det = mp.det(A)
    frob2 = sum(abs(A[i, j]) ** 2 for i in range(2) for j in range(2))
    delta = abs(det) / frob2
    disc = mp.sqrt(max(mp.mpf(0), frob2 * frob2 - 4 * abs(det) ** 2))
    small2 = max(mp.mpf(0), (frob2 - disc) / 2)
    large2 = max(mp.mpf(0), (frob2 + disc) / 2)
    ratio = mp.sqrt(small2 / large2) if large2 else mp.mpf(0)
    return A, det, delta, ratio


def sample(item):
    mp.mp.dps = 60
    n = item["n"]
    t = mp.mpf(item["rho"][1])
    gap = mp.mpf(item["gap"])
    out = {"kind": "sample", "n": n, "gamma": str(t), "gap": str(gap), "points": {}}
    try:
        for label, height in (("minus", t - gap / 4), ("zero", t), ("plus", t + gap / 4)):
            A, det, delta, ratio = metrics(mp.mpc(".5", height))
            out["points"][label] = {
                "height": mp.nstr(height, 60),
                "matrix": [[cstr(A[i, j], 45) for j in range(2)] for i in range(2)],
                "det": cstr(det, 45),
                "delta": mp.nstr(delta, 45),
                "singular_ratio": mp.nstr(ratio, 45),
            }
        out["contrast"] = mp.nstr(mp.log(mp.mpf(out["points"]["zero"]["delta"])) -
            (mp.log(mp.mpf(out["points"]["minus"]["delta"])) + mp.log(mp.mpf(out["points"]["plus"]["delta"]))) / 2, 45)
    except Exception as exc:
        out["error"] = str(exc)[:300]
    return out


def jseries(n, w, s):
    term = mp.mpc(1)
    total = mp.mpc(0)
    quiet = 0
    for k in range(8000):
        rational = sum((-1) ** j * mp.binomial(n, j) / (w + k + j + 1) for j in range(n + 1))
        add = term * rational
        total += add
        quiet = quiet + 1 if abs(add) < mp.eps * max(1, abs(total)) / 100 else 0
        if quiet >= 12:
            return mp.power(2, 2 * s) * total
        term *= -(2 * s - k) / (2 * (k + 1))
    raise ArithmeticError("series did not converge")


def entry_series(rho, branch, side):
    w, s, c0, c1 = pars(rho, branch, side)
    return (c0 * jseries(2, w, s) + c1 * jseries(4, w, s)) / mp.beta(3, w + 1)


def validate(job):
    n, label, height = job
    out = {"kind": "validation", "n": n, "label": label, "height": height, "precision": []}
    try:
        last = None
        for dps in (100, 160):
            mp.mp.dps = dps
            A, det, delta, ratio = metrics(mp.mpc(".5", height))
            out["precision"].append({"dps": dps, "det": cstr(det, dps), "delta": mp.nstr(delta, dps), "singular_ratio": mp.nstr(ratio, dps)})
            last = A
        mp.mp.dps = 190
        independent, det_i, delta_i, ratio_i = metrics(mp.mpc(".5", height), entry_series)
        out.update({
            "independent_det": cstr(det_i, 180),
            "independent_delta": mp.nstr(delta_i, 180),
            "independent_ratio": mp.nstr(ratio_i, 180),
            "matrix_discrepancy": mp.nstr(mp.norm(last - independent), 150),
        })
    except Exception as exc:
        out["error"] = str(exc)[:350]
    return out


def median(xs):
    ys = sorted(xs)
    n = len(ys)
    return ys[n // 2] if n % 2 else (ys[n // 2 - 1] + ys[n // 2]) / 2


def emit(row):
    with open("results.jsonl", "a") as f:
        f.write(json.dumps(row) + "\n")
    print(json.dumps({k: v for k, v in row.items() if k not in ("points", "precision")}), flush=True)


def main():
    started = time.monotonic()
    data = json.load(open("zeros.json"))
    if [len([x for x in data if a <= x["n"] <= b]) for a, b in ((1, 64), (65, 128), (257, 320))] != [64, 64, 64]:
        raise ValueError("input cohort mismatch")
    with cf.ProcessPoolExecutor(max_workers=14) as pool:
        rows = list(pool.map(sample, data, chunksize=1))
        for row in rows:
            emit(row)
        summaries = []
        for name, lo, hi in (("discovery", 1, 64), ("holdout", 65, 128), ("distant", 257, 320)):
            group = [r for r in rows if lo <= r["n"] <= hi and "error" not in r]
            contrasts = [mp.mpf(r["contrast"]) for r in group]
            ordered = sorted(group, key=lambda r: mp.mpf(r["points"]["zero"]["delta"]))
            summary = {
                "kind": "cohort", "cohort": name, "count": len(group),
                "mean_contrast": mp.nstr(sum(contrasts) / len(contrasts), 30),
                "median_contrast": mp.nstr(median(contrasts), 30),
                "positive_count": sum(x > 0 for x in contrasts),
                "minimum_zero": {"n": ordered[0]["n"], "delta": ordered[0]["points"]["zero"]["delta"]},
                "maximum_zero": {"n": ordered[-1]["n"], "delta": ordered[-1]["points"]["zero"]["delta"]},
            }
            emit(summary)
            summaries.append(summary)
        jobs = []
        chosen = set()
        for lo, hi in ((1, 64), (65, 128), (257, 320)):
            group = [r for r in rows if lo <= r["n"] <= hi and "error" not in r]
            for row in (min(group, key=lambda r: mp.mpf(r["points"]["zero"]["delta"])),
                        max(group, key=lambda r: mp.mpf(r["points"]["zero"]["delta"])),
                        max(group, key=lambda r: abs(mp.mpf(r["contrast"])))):
                key = (row["n"], "zero")
                if key not in chosen:
                    chosen.add(key)
                    jobs.append((row["n"], "zero", row["points"]["zero"]["height"]))
        for row in pool.map(validate, jobs, chunksize=1):
            emit(row)
    gate = all(mp.mpf(s["mean_contrast"]) > 0 and mp.mpf(s["median_contrast"]) > 0 for s in summaries)
    emit({"kind": "gate", "passed": gate})
    emit({"kind": "complete", "seconds": time.monotonic() - started})


if __name__ == "__main__":
    main()

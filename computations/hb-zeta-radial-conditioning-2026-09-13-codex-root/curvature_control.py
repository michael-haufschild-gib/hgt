import concurrent.futures as cf
import json
import os
import time

import mpmath as mp

DEADLINE = float(os.environ["CAMPAIGN_DEADLINE"])


def budget():
    if time.monotonic() > DEADLINE - 4:
        raise TimeoutError("family deadline")


def pars(rho, branch, side):
    s = rho - 2 if branch else -rho - 1
    w = -1 - rho / 2 if side else -2 + rho / 2
    c0 = (5 * s * s + 15 * s + 4) / 4
    c1 = s * (s - 1) * ((s + 2) * (2 * s + 3) - (w + 1) * (w + 2) / 2) / 4
    return w, s, c0, c1


def entry(rho, branch, side):
    budget()
    w, s, c0, c1 = pars(rho, branch, side)
    return c0 * mp.hyp2f1(-2 * s, 3, w + 4, -1) + 12 * c1 / ((w + 4) * (w + 5)) * mp.hyp2f1(-2 * s, 5, w + 6, -1)


def log_delta(height):
    rho = mp.mpc(".5", height)
    A = [[entry(rho, b, s) for s in (False, True)] for b in (False, True)]
    det = A[0][0] * A[1][1] - A[0][1] * A[1][0]
    frob2 = sum(abs(x) ** 2 for row in A for x in row)
    return mp.log(abs(det) / frob2)


def curvature(center, halfwidth):
    return log_delta(center) - (log_delta(center - halfwidth) + log_delta(center + halfwidth)) / 2


def sample(item):
    mp.mp.dps = 60
    t = mp.mpf(item["rho"][1])
    gap = mp.mpf(item["gap"])
    out = {"kind": "sample", "n": item["n"]}
    try:
        zero = curvature(t, gap / 4)
        midpoint = curvature(t + gap / 2, gap / 4)
        out.update({"zero_contrast": mp.nstr(zero, 45), "midpoint_contrast": mp.nstr(midpoint, 45),
                    "specific_difference": mp.nstr(zero - midpoint, 45)})
    except Exception as exc:
        out["error"] = str(exc)[:300]
    return out


def median(xs):
    ys = sorted(xs)
    n = len(ys)
    return ys[n // 2] if n % 2 else (ys[n // 2 - 1] + ys[n // 2]) / 2


def emit(row):
    with open("curvature-control.jsonl", "a") as f:
        f.write(json.dumps(row) + "\n")
    print(json.dumps(row), flush=True)


def main():
    started = time.monotonic()
    data = json.load(open("zeros.json"))
    with cf.ProcessPoolExecutor(max_workers=14) as pool:
        rows = list(pool.map(sample, data, chunksize=1))
    for row in rows:
        emit(row)
    falsified = False
    for name, lo, hi in (("discovery", 1, 64), ("holdout", 65, 128), ("distant", 257, 320)):
        group = [r for r in rows if lo <= r["n"] <= hi and "error" not in r]
        mids = [mp.mpf(r["midpoint_contrast"]) for r in group]
        diffs = [mp.mpf(r["specific_difference"]) for r in group]
        all_positive = all(x > 0 for x in mids)
        falsified = falsified or all_positive
        emit({"kind": "cohort", "cohort": name, "count": len(group),
              "midpoint_positive_count": sum(x > 0 for x in mids), "midpoint_all_positive": all_positive,
              "median_midpoint_contrast": mp.nstr(median(mids), 30),
              "median_specific_difference": mp.nstr(median(diffs), 30)})
    emit({"kind": "specificity_gate", "arithmetic_specificity_falsified": falsified})
    emit({"kind": "complete", "seconds": time.monotonic() - started})


if __name__ == "__main__":
    main()

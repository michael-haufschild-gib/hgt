import concurrent.futures as cf
import json
import os
import time

import mpmath as mp

from experiment import observable


OUT = os.environ.get("ROOT_EXIT_OUT", "root-exit-discovery.jsonl")
MODE = os.environ.get("ROOT_EXIT_MODE", "discover")
HEIGHTS = ["20", "30", "50", "75", "100", "150", "200"]


def cross_data(sigma, height, L):
    W, ratio = observable(mp.mpc(sigma, height), L, True)
    numerator = -mp.im(W[0] * mp.conj(W[1]))
    return numerator, abs(W[1]), mp.im(ratio)


def roots_half(height, L):
    # Cross-numerator scan includes the true strip boundary and cannot confuse a
    # ratio pole with a zero. The central symmetry root is excluded.
    grid = [mp.mpf(i) / 240 for i in range(121)]
    vals = [(s, cross_data(s, height, L)[0]) for s in grid]
    roots = []
    for (a, fa), (b, fb) in zip(vals, vals[1:]):
        if fa == 0:
            r = a
        elif fa * fb < 0:
            try:
                r = mp.findroot(lambda x: cross_data(x, height, L)[0], (a, b),
                                tol=mp.mpf("1e-65"), maxsteps=60)
            except Exception:
                continue
        else:
            continue
        if -mp.mpf("1e-40") <= r < mp.mpf(".499999999999") and not any(abs(r-x) < mp.mpf("1e-35") for x in roots):
            roots.append(r)
    return roots


def scan_height(height_text):
    mp.mp.dps = 90
    h = mp.mpf(height_text)
    L0, L1 = 2 * mp.e, mp.mpf(6)
    Lgrid = [L0 + (L1-L0) * i / 64 for i in range(65)]
    boundary = [(L, cross_data(mp.mpf(0), h, L)[0]) for L in Lgrid]
    cutoff = [(L, cross_data(mp.mpf(".02"), h, L)[0]) for L in Lgrid]

    def refine_boundary(data, sigma):
        ans = []
        for (a, fa), (b, fb) in zip(data, data[1:]):
            if fa == 0 or fa * fb < 0:
                try:
                    r = mp.findroot(lambda x: cross_data(sigma, h, x)[0], (a, b),
                                    tol=mp.mpf("1e-65"), maxsteps=80)
                    if L0 <= r <= L1 and not any(abs(r-x) < mp.mpf("1e-35") for x in ans):
                        ans.append(r)
                except Exception:
                    pass
        return ans

    boundary_events = refine_boundary(boundary, mp.mpf(0))
    cutoff_events = refine_boundary(cutoff, mp.mpf(".02"))
    coarse = []
    for i in range(17):
        L = L0 + (L1-L0) * i / 16
        roots = roots_half(h, L)
        coarse.append({"L": mp.nstr(L, 55), "roots": [mp.nstr(x, 55) for x in roots]})

    events = []
    for L in boundary_events:
        eps = mp.mpf("1e-8") * max(mp.mpf(1), abs(L))
        n, den, rim = cross_data(mp.mpf(0), h, L)
        lo = roots_half(h, L-eps)
        hi = roots_half(h, L+eps)
        upper_n, _, _ = cross_data(mp.mpf(1), h, L)
        events.append({
            "kind": "boundary", "L": mp.nstr(L, 80),
            "N": mp.nstr(n, 70), "N_sigma1": mp.nstr(upper_n, 70),
            "denominator_abs": mp.nstr(den, 70), "ratio_imag": mp.nstr(rim, 70),
            "roots_below": [mp.nstr(x, 55) for x in lo],
            "roots_above": [mp.nstr(x, 55) for x in hi],
        })

    # Look for an interior tangency only if the direct half-strip root count
    # changes without a boundary event in the same L interval.
    interior = []
    for left, right in zip(coarse, coarse[1:]):
        if len(left["roots"]) == len(right["roots"]):
            continue
        a, b = mp.mpf(left["L"]), mp.mpf(right["L"])
        if any(a <= x <= b for x in boundary_events):
            continue
        seed_s = mp.mpf(".25")
        candidates = []
        for j in range(1, 40):
            s = mp.mpf(j) / 80
            Lm = (a+b)/2
            candidates.append((abs(cross_data(s, h, Lm)[0]), s))
        seed_s = min(candidates)[1]
        try:
            s, L = mp.findroot(
                lambda x, y: (cross_data(x, h, y)[0], mp.diff(lambda q: cross_data(q, h, y)[0], x)),
                (seed_s, (a+b)/2), tol=mp.mpf("1e-55"), maxsteps=80,
            )
            if 0 < s < mp.mpf(".5") and L0 <= L <= L1:
                interior.append({"sigma": mp.nstr(s, 70), "L": mp.nstr(L, 70),
                                 "N": mp.nstr(cross_data(s,h,L)[0], 60),
                                 "N_sigma": mp.nstr(mp.diff(lambda q: cross_data(q,h,L)[0],s),60),
                                 "denominator_abs": mp.nstr(cross_data(s,h,L)[1],60)})
        except Exception:
            pass
    return {"kind": "height", "mode": MODE, "height": height_text,
            "boundary_events": events,
            "cutoff_events": [mp.nstr(x, 70) for x in cutoff_events],
            "interior_events": interior, "coarse_roots": coarse}


def validate_event(job):
    height_text, L_text = job
    out = {"kind": "validation", "mode": MODE, "height": height_text,
           "reported_L": L_text, "precision": []}
    for dps in (130, 190):
        mp.mp.dps = dps
        h, guess = mp.mpf(height_text), mp.mpf(L_text)
        try:
            root = mp.findroot(lambda L: cross_data(mp.mpf(0), h, L)[0],
                               (guess*(1-mp.mpf("1e-12")), guess*(1+mp.mpf("1e-12"))),
                               tol=mp.power(10, -dps+20), maxsteps=100)
            n, den, rim = cross_data(mp.mpf(0), h, root)
            eps = mp.power(10, -30)
            below, above = roots_half(h, root-eps), roots_half(h, root+eps)
            out["precision"].append({"dps": dps, "L": mp.nstr(root, dps),
                "N": mp.nstr(n, dps), "denominator_abs": mp.nstr(den, dps),
                "ratio_imag": mp.nstr(rim, dps),
                "roots_below": [mp.nstr(x,dps//2) for x in below],
                "roots_above": [mp.nstr(x,dps//2) for x in above]})
        except Exception as exc:
            out["error"] = str(exc)[:300]
    return out


def emit(row):
    with open(OUT, "a") as f:
        f.write(json.dumps(row) + "\n")
    slim = {k:v for k,v in row.items() if k not in ("coarse_roots","precision")}
    print(json.dumps(slim), flush=True)


def main():
    started = time.monotonic()
    workers = min(14, len(HEIGHTS))
    with cf.ProcessPoolExecutor(max_workers=workers) as pool:
        rows = list(pool.map(scan_height, HEIGHTS, chunksize=1))
        for row in rows:
            emit(row)
        jobs = [(r["height"], e["L"]) for r in rows for e in r["boundary_events"]]
        for row in pool.map(validate_event, jobs, chunksize=1):
            emit(row)
    count_b = sum(len(r["boundary_events"]) for r in rows)
    count_i = sum(len(r["interior_events"]) for r in rows)
    emit({"kind":"gate", "mode":MODE, "boundary_exit_classified": count_b==len(HEIGHTS) and count_i==0,
          "boundary_event_count":count_b, "interior_event_count":count_i})
    emit({"kind":"complete", "mode":MODE, "seconds":time.monotonic()-started})


if __name__ == "__main__":
    main()

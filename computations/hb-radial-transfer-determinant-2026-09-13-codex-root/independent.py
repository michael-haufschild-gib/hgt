import concurrent.futures as cf
import json
import os
import time

import mpmath as mp

DEADLINE = float(os.environ["CAMPAIGN_DEADLINE"])
OUT = "independent.jsonl"


def budget():
    if time.monotonic() > DEADLINE - 4:
        raise TimeoutError("family deadline")


def cstr(z, digits=60):
    return [mp.nstr(mp.re(z), digits), mp.nstr(mp.im(z), digits)]


def pars(rho, branch, side):
    s = rho - 2 if branch else -rho - 1
    w = -1 - rho / 2 if side else -2 + rho / 2
    c0 = (5 * s * s + 15 * s + 4) / 4
    c1 = s * (s - 1) * ((s + 2) * (2 * s + 3) - (w + 1) * (w + 2) / 2) / 4
    return w, s, c0, c1


def jseries(n, w, s):
    term = mp.mpc(1)
    total = mp.mpc(0)
    quiet = 0
    for k in range(7000):
        budget()
        rational = sum((-1) ** j * mp.binomial(n, j) / (w + k + j + 1) for j in range(n + 1))
        add = term * rational
        total += add
        quiet = quiet + 1 if abs(add) < mp.eps * max(1, abs(total)) / 100 else 0
        if quiet >= 12:
            return mp.power(2, 2 * s) * total
        term *= -(2 * s - k) / (2 * (k + 1))
    raise ArithmeticError("series did not converge")


def entry(rho, branch, side):
    w, s, c0, c1 = pars(rho, branch, side)
    return (c0 * jseries(2, w, s) + c1 * jseries(4, w, s)) / mp.beta(3, w + 1)


def det_value(rho):
    a = [[entry(rho, b, s) for s in (False, True)] for b in (False, True)]
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def perimeter(r0, r1, t0, t1, n):
    corners = [mp.mpc(r0, t0), mp.mpc(r1, t0), mp.mpc(r1, t1), mp.mpc(r0, t1)]
    return [corners[j] + (corners[(j + 1) % 4] - corners[j]) * k / n for j in range(4) for k in range(n)]


def scan(job):
    mp.mp.dps = 70
    r0, r1, t0, t1 = map(mp.mpf, job)
    out = {"kind": "tile", "job": job, "contours": []}
    started = time.monotonic()
    try:
        for n in (16, 32):
            points = perimeter(r0, r1, t0, t1, n)
            vals = [det_value(z) for z in points]
            inc = [mp.arg(vals[(i + 1) % len(vals)] / vals[i]) for i in range(len(vals))]
            out["contours"].append({
                "n": n,
                "winding": mp.nstr(sum(inc) / (2 * mp.pi), 40),
                "max_phase_step": mp.nstr(max(map(abs, inc)), 30),
                "minimum": mp.nstr(min(map(abs, vals)), 30),
            })
    except Exception as exc:
        out["error"] = str(exc)[:250]
    out["seconds"] = time.monotonic() - started
    return out


def emit(row):
    with open(OUT, "a") as f:
        f.write(json.dumps(row) + "\n")
    print(json.dumps({k: v for k, v in row.items() if k != "contours"}), flush=True)


def main():
    started = time.monotonic()
    mp.mp.dps = 70
    emit({"kind": "control", "rho": [".5", "10"], "det": cstr(det_value(mp.mpc(".5", "10")))})
    rs = [(mp.mpf(".01") + i * mp.mpf(".98") / 4, mp.mpf(".01") + (i + 1) * mp.mpf(".98") / 4) for i in range(4)]
    ts = [(mp.mpf(".1") + 2 * i, mp.mpf(".1") + 2 * (i + 1)) for i in range(8)]
    jobs = [[str(a), str(b), str(c), str(d)] for a, b in rs for c, d in ts]
    rows = []
    with cf.ProcessPoolExecutor(max_workers=14) as pool:
        for row in pool.map(scan, jobs, chunksize=1):
            emit(row)
            rows.append(row)
    emit({"kind": "shared_count", "sum_winding_32": mp.nstr(sum(mp.mpf(r["contours"][-1]["winding"]) for r in rows if "error" not in r), 30)})
    emit({"kind": "complete", "seconds": time.monotonic() - started})


if __name__ == "__main__":
    main()

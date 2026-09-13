import concurrent.futures as cf
import json
import os
import time

import mpmath as mp

DEADLINE = float(os.environ["CAMPAIGN_DEADLINE"])
OUT = "discovery.jsonl"


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


def entry(rho, branch, side):
    budget()
    w, s, c0, c1 = pars(rho, branch, side)
    return c0 * mp.hyp2f1(-2 * s, 3, w + 4, -1) + 12 * c1 / ((w + 4) * (w + 5)) * mp.hyp2f1(-2 * s, 5, w + 6, -1)


def matrix(rho):
    return mp.matrix([[entry(rho, False, False), entry(rho, False, True)],
                      [entry(rho, True, False), entry(rho, True, True)]])


def det_value(rho):
    a = matrix(rho)
    return a[0, 0] * a[1, 1] - a[0, 1] * a[1, 0]


def perimeter(r0, r1, t0, t1, n):
    corners = [mp.mpc(r0, t0), mp.mpc(r1, t0), mp.mpc(r1, t1), mp.mpc(r0, t1)]
    return [corners[j] + (corners[(j + 1) % 4] - corners[j]) * k / n for j in range(4) for k in range(n)]


def contour(r0, r1, t0, t1, n):
    points = perimeter(r0, r1, t0, t1, n)
    vals = [det_value(z) for z in points]
    inc = [mp.arg(vals[(i + 1) % len(vals)] / vals[i]) for i in range(len(vals))]
    imin = min(range(len(vals)), key=lambda i: abs(vals[i]))
    return {
        "n": n,
        "winding": mp.nstr(sum(inc) / (2 * mp.pi), 30),
        "max_phase_step": mp.nstr(max(map(abs, inc)), 30),
        "minimum": mp.nstr(abs(vals[imin]), 30),
        "minimum_rho": cstr(points[imin], 30),
    }


def scan(job):
    mp.mp.dps = 60
    r0, r1, t0, t1 = map(mp.mpf, job)
    out = {"kind": "tile", "job": job, "contours": [], "roots": [], "failures": []}
    started = time.monotonic()
    try:
        for n in (32, 64):
            out["contours"].append(contour(r0, r1, t0, t1, n))
        winding = int(mp.nint(mp.mpf(out["contours"][-1]["winding"])))
        if winding != 0:
            seeds = [mp.mpc((r0 + r1) / 2, (t0 + t1) / 2), mp.mpc(*out["contours"][-1]["minimum_rho"])]
            for seed in seeds:
                try:
                    root = mp.findroot(det_value, (seed, seed + mp.mpc(".0003", ".0002")), tol=mp.mpf("1e-48"), maxsteps=60)
                    if r0 < root.real < r1 and t0 < root.imag < t1 and abs(det_value(root)) < mp.mpf("1e-40"):
                        if not any(abs(root - mp.mpc(*x["rho"])) < mp.mpf("1e-24") for x in out["roots"]):
                            out["roots"].append({"rho": cstr(root, 60), "residual": mp.nstr(abs(det_value(root)), 40)})
                except Exception as exc:
                    out["failures"].append(str(exc)[:180])
    except Exception as exc:
        out["error"] = str(exc)[:250]
    out["seconds"] = time.monotonic() - started
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
            return mp.power(2, 2 * s) * total, k + 1
        term *= -(2 * s - k) / (2 * (k + 1))
    raise ArithmeticError("endpoint series did not converge")


def decomposition(rho, branch, side):
    w, s, c0, c1 = pars(rho, branch, side)
    j0, terms = jseries(0, w, s)
    d = 2 * s - w
    e = w + 2 * s + 2
    E = e * (e + 1) * (e + 2) * (e + 3)
    P = c0 * (e + d * d) * (e + 2) * (e + 3) + c1 * (d ** 4 + (6 * e + 8) * d * d + 3 * e * (e + 2))
    Q = d * (c0 * (e + 2) * (e + 3) + c1 * (d * d + 5 * e + 8))
    scale = E * mp.beta(3, w + 1)
    return P * j0 / scale, Q / scale, terms


def validate(seed):
    started = time.monotonic()
    out = {"kind": "validation", "seed": seed, "precision": []}
    try:
        for dps in (60, 100, 160):
            mp.mp.dps = dps
            z = mp.mpc(*seed)
            root = mp.findroot(det_value, (z, z + mp.mpc("1e-8", "2e-8")), tol=mp.power(10, -dps + 12), maxsteps=70)
            out["precision"].append({"dps": dps, "rho": cstr(root, dps), "residual": mp.nstr(abs(det_value(root)), dps)})
            seed = cstr(root, dps)
        mp.mp.dps = 190
        root = mp.mpc(*seed)
        A = matrix(root)
        dec = [[decomposition(root, b, s) for s in (False, True)] for b in (False, True)]
        base = mp.matrix([[dec[i][j][0] for j in range(2)] for i in range(2)])
        boundary = mp.matrix([[dec[i][j][1] for j in range(2)] for i in range(2)])
        rebuilt = base + boundary
        det_base = mp.det(base)
        det_boundary = mp.det(boundary)
        # Explicit right-null vector avoids relying on SVD conventions.
        v = mp.matrix([A[0, 1], -A[0, 0]])
        nv = mp.sqrt(abs(v[0]) ** 2 + abs(v[1]) ** 2)
        v = v / nv
        residual = A * v
        gram = A.transpose_conj() * A
        tr = mp.re(gram[0, 0] + gram[1, 1])
        disc = mp.sqrt(max(mp.mpf(0), tr * tr - 4 * abs(mp.det(A)) ** 2))
        singular = [mp.sqrt(max(mp.mpf(0), (tr - disc) / 2)), mp.sqrt(max(mp.mpf(0), (tr + disc) / 2))]
        circle = [root + mp.mpf("1e-7") * mp.exp(2j * mp.pi * k / 64) for k in range(64)]
        vals = [det_value(z) for z in circle]
        winding = sum(mp.arg(vals[(k + 1) % 64] / vals[k]) for k in range(64)) / (2 * mp.pi)
        anchor = root + mp.mpc(".001", ".0007")
        out.update({
            "matrix": [[cstr(A[i, j], 80) for j in range(2)] for i in range(2)],
            "entry_magnitudes": [[mp.nstr(abs(A[i, j]), 50) for j in range(2)] for i in range(2)],
            "series_terms": [[dec[i][j][2] for j in range(2)] for i in range(2)],
            "reconstruction_error": mp.nstr(mp.norm(A - rebuilt), 80),
            "det_base_period_only": cstr(det_base, 80),
            "det_boundary_only": cstr(det_boundary, 80),
            "det_complete": cstr(mp.det(A), 80),
            "right_null_mixture": [cstr(v[i], 80) for i in range(2)],
            "reader_residuals": [cstr(residual[i], 80) for i in range(2)],
            "singular_values": [mp.nstr(x, 80) for x in singular],
            "local_winding": mp.nstr(winding, 50),
            "derivative": cstr(mp.diff(det_value, root), 80),
            "anchor": {"rho": cstr(anchor, 50), "det": cstr(det_value(anchor), 80)},
        })
    except Exception as exc:
        out["error"] = str(exc)[:350]
    out["seconds"] = time.monotonic() - started
    return out


def emit(row):
    with open(OUT, "a") as f:
        f.write(json.dumps(row) + "\n")
    short = {k: v for k, v in row.items() if k not in ("contours", "matrix", "precision")}
    print(json.dumps(short), flush=True)


def main():
    started = time.monotonic()
    mp.mp.dps = 60
    emit({"kind": "control", "rho": [".5", "10"], "det": cstr(det_value(mp.mpc(".5", "10")), 50)})
    rs = [(mp.mpf(".01") + i * mp.mpf(".98") / 8, mp.mpf(".01") + (i + 1) * mp.mpf(".98") / 8) for i in range(8)]
    ts = [(mp.mpf(".1") + 4 * i, min(mp.mpf("80"), mp.mpf(".1") + 4 * (i + 1))) for i in range(20)]
    jobs = [[str(a), str(b), str(c), str(d)] for a, b in rs for c, d in ts]
    rows = []
    with cf.ProcessPoolExecutor(max_workers=14) as pool:
        for row in pool.map(scan, jobs, chunksize=1):
            emit(row)
            rows.append(row)
        roots = []
        for row in rows:
            for candidate in row.get("roots", []):
                z = mp.mpc(*candidate["rho"])
                if not any(abs(z - mp.mpc(*old)) < mp.mpf("1e-18") for old in roots):
                    roots.append(candidate["rho"])
        emit({"kind": "candidate_count", "count": len(roots), "roots": roots})
        for row in pool.map(validate, roots, chunksize=1):
            emit(row)
    emit({"kind": "complete", "seconds": time.monotonic() - started})


if __name__ == "__main__":
    main()

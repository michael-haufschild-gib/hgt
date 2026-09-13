import concurrent.futures as cf
import json
import os
import time

import mpmath as mp

DEADLINE = float(os.environ["CAMPAIGN_DEADLINE"])


def budget():
    if time.monotonic() > DEADLINE - 4:
        raise TimeoutError("family deadline")


def cstr(z, digits=60):
    return [mp.nstr(mp.re(z), digits), mp.nstr(mp.im(z), digits)]


def primitive_power(k, q0, q1):
    return mp.log(q1 / q0) if k == 5 else (mp.power(q1, k - 5) - mp.power(q0, k - 5)) / (k - 5)


def hmn(m, n, L, z):
    # Analytic z<-1 cell. q endpoints are d-1,d+1 with d=L-z.
    d = L - z
    q0, q1 = d - 1, d + 1
    total = mp.mpc(0)
    for i in range(m + 1):
        for j in range(n + 1):
            coef = mp.binomial(m, i) * mp.binomial(n, j) * mp.power(-L, m - i) * mp.power(-d, n - j)
            total += coef * primitive_power(i + j, q0, q1)
    return total


def fmn(m, n, delta, L, z):
    exponent = delta if (m, n) in ((1, 1), (1, 3)) else delta - 2
    return mp.power(L, exponent) * hmn(m, n, L, z)


def dstar_f33(delta, L, z):
    budget()
    dLL = mp.diff(lambda x: x * x * fmn(3, 3, delta, x, z), L, 2)
    dzz = mp.diff(lambda y: L * L * fmn(3, 3, delta, L, y), z, 2)
    return dLL - dzz


def coefficients(s, t):
    lam = (s + 1) * (s + 2)
    A0 = (5 * lam - 6) / 4
    ks, kt = s * (s - 1) / 4, t * (t - 1) / 4
    alphas, alphat = ks * (s + 2) * (2 * s + 3), kt * (t + 2) * (2 * t + 3)
    betas, betat = -ks / 2, -kt / 2
    return A0, alphas, alphat, betas, betat


def corner(s, t, delta, L, derivative=True):
    z = 1 - L
    A0, alphas, alphat, betas, betat = coefficients(s, t)
    f13 = fmn(1, 3, delta, L, z)
    f31 = fmn(3, 1, delta, L, z)
    f33 = fmn(3, 3, delta, L, z)
    deriv = dstar_f33(delta, L, z) if derivative else 0
    cR = L * L * (A0 * betas * f13 + A0 * betat * f31 +
                    (alphas * betat + betas * alphat) * f33 + betas * betat * deriv)
    cD = L * L * betas * betat * f33
    return cR, cD


def observable(rho, L, derivative=True):
    s, t, delta = rho - 2, -rho - 1, 2 * rho - 1
    a = corner(s, t, delta, L, derivative)
    b = corner(t, s, -delta, L, derivative)
    W = (a[0] - b[0], a[1] - b[1])
    ratio = -W[0] / W[1]
    return W, ratio


def sample(job):
    mp.mp.dps = 80
    height, L, sigma = map(mp.mpf, job)
    rho = mp.mpc(sigma, height)
    out = {"kind": "sample", "height": str(height), "L": str(L), "sigma": str(sigma)}
    try:
        W, ratio = observable(rho, L, True)
        W0, ratio0 = observable(rho, L, False)
        reflected = mp.mpc(1 - sigma, height)
        Wr, ratior = observable(reflected, L, True)
        out.update({"W": [cstr(x, 70) for x in W], "ratio": cstr(ratio, 70),
                    "ablated_ratio": cstr(ratio0, 70), "reflection_ratio": cstr(ratior, 70),
                    "reflection_conjugacy_defect": cstr(ratior - mp.conj(ratio), 60),
                    "denominator_abs": mp.nstr(abs(W[1]), 60), "ablated_denominator_abs": mp.nstr(abs(W0[1]), 60)})
    except Exception as exc:
        out["error"] = str(exc)[:300]
    return out


def scan(job):
    mp.mp.dps = 80
    height, L = map(mp.mpf, job)
    sigmas = [mp.mpf(".02") + i * mp.mpf(".96") / 48 for i in range(49)]
    out = {"kind": "scan", "height": str(height), "L": str(L), "roots": [], "ablated_roots": [], "samples": []}
    try:
        for derivative, key in ((True, "roots"), (False, "ablated_roots")):
            vals = []
            for sigma in sigmas:
                W, ratio = observable(mp.mpc(sigma, height), L, derivative)
                vals.append((sigma, mp.im(ratio), abs(W[1])))
                if derivative:
                    out["samples"].append([mp.nstr(sigma, 20), mp.nstr(mp.im(ratio), 45), mp.nstr(abs(W[1]), 30)])
            for (a, fa, da), (b, fb, db) in zip(vals, vals[1:]):
                if min(da, db) < mp.mpf("1e-50"):
                    continue
                if fa == 0 or fa * fb < 0:
                    try:
                        root = mp.findroot(lambda x: mp.im(observable(mp.mpc(x, height), L, derivative)[1]), (a, b), tol=mp.mpf("1e-60"), maxsteps=50)
                        if mp.mpf(".02") < root < mp.mpf(".98") and not any(abs(root - mp.mpf(x)) < mp.mpf("1e-35") for x in out[key]):
                            out[key].append(mp.nstr(root, 70))
                    except Exception:
                        pass
    except Exception as exc:
        out["error"] = str(exc)[:300]
    return out


def controls():
    mp.mp.dps = 100
    L, z = mp.mpf("10"), mp.mpf("-9")
    rows = []
    for m, n in ((1, 1), (1, 3), (3, 1), (3, 3)):
        direct = mp.quad(lambda y: y ** m * (y + z) ** n / (L + y) ** 6, [-1 - z, 1 - z])
        exact = hmn(m, n, L, z)
        rows.append({"m": m, "n": n, "quadrature_error": mp.nstr(abs(exact - direct), 80)})
    delta = mp.mpc(".3", "2.1")
    exact_d = dstar_f33(delta, L, z)
    fd = []
    for eps in (mp.mpf("1e-4"), mp.mpf("1e-6"), mp.mpf("1e-8")):
        g = lambda x, y: x * x * fmn(3, 3, delta, x, y)
        dll = (g(L + eps, z) - 2 * g(L, z) + g(L - eps, z)) / eps ** 2
        dzz = (g(L, z + eps) - 2 * g(L, z) + g(L, z - eps)) / eps ** 2
        fd.append({"eps": str(eps), "error": mp.nstr(abs((dll - dzz) - exact_d), 60)})
    return {"kind": "controls", "moments": rows, "dstar_finite_difference": fd}


def validate(job):
    height, L, sigma = job
    out = {"kind": "validation", "height": height, "L": L, "sigma": sigma, "precision": []}
    try:
        for dps in (120, 180):
            mp.mp.dps = dps
            W, ratio = observable(mp.mpc(sigma, height), mp.mpf(L), True)
            out["precision"].append({"dps": dps, "ratio": cstr(ratio, dps), "W": [cstr(x, dps) for x in W]})
    except Exception as exc:
        out["error"] = str(exc)[:300]
    return out


def emit(row):
    with open("results.jsonl", "a") as f:
        f.write(json.dumps(row) + "\n")
    print(json.dumps({k: v for k, v in row.items() if k not in ("samples", "precision")}), flush=True)


def main():
    started = time.monotonic()
    emit(controls())
    heights = ["14.134725141734693790457251983562470270784257115699", "50", "100"]
    scales = [mp.nstr(2 * mp.e, 50), "10", "30"]
    sigmas = [".2", ".35", ".5", ".65", ".8"]
    with cf.ProcessPoolExecutor(max_workers=14) as pool:
        for row in pool.map(sample, [[h, L, s] for h in heights for L in scales for s in sigmas], chunksize=1):
            emit(row)
        scans = list(pool.map(scan, [[h, L] for h in heights for L in scales], chunksize=1))
        for row in scans:
            emit(row)
        candidates = []
        for row in scans:
            for root in row.get("roots", []):
                candidates.append([row["height"], row["L"], root])
        for row in pool.map(validate, candidates, chunksize=1):
            emit(row)
    complete_detector = all(row.get("roots") == ["0.5"] for row in scans)
    emit({"kind": "gate", "complete_detector": complete_detector,
          "root_sets": [{"height": r["height"], "L": r["L"], "roots": r.get("roots"), "ablated_roots": r.get("ablated_roots")} for r in scans]})
    emit({"kind": "complete", "seconds": time.monotonic() - started})


if __name__ == "__main__":
    main()

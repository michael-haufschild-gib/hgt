import concurrent.futures as cf
import json
import os
import time

import mpmath as mp

DEADLINE = float(os.environ["CAMPAIGN_DEADLINE"])
OUT = "challenge-stable.jsonl"
SEED = (
    "0.880795460232595309035783338060080245984264806920089923751085",
    "0.634145625801657837777746285670772699883161431185172620706643",
)


def seed_value():
    return mp.mpc(*SEED)


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


def stable_difference(z, s, w, c0, c1):
    root = mp.sqrt(1 - z)
    d = 2 * s - w
    C = c0 + c1
    L = mp.log(root) + d * mp.log((1 + root) / 2)
    return mp.power(2, d) * (C * mp.expm1(L) - c1 * z * mp.exp(L))


def entry_direct(rho, branch, side):
    budget()
    w, s, c0, c1 = pars(rho, branch, side)
    f0 = mp.power(2, 2 * s - w) * (c0 + c1)

    def transformed(u):
        if u == 0:
            return mp.mpc(0)
        z = u ** 4
        return 4 * u ** 3 * mp.power(z, w) * stable_difference(z, s, w, c0, c1)

    integral = mp.quad(transformed, [0, mp.mpf(".08"), mp.mpf(".25"), mp.mpf(".55"), mp.mpf(".8"), 1])
    return (f0 / (w + 1) + integral) / (2 * mp.beta(3, w + 1))


def matrix_direct(rho):
    return mp.matrix([[entry_direct(rho, False, False), entry_direct(rho, False, True)],
                      [entry_direct(rho, True, False), entry_direct(rho, True, True)]])


def determinant(rho):
    return mp.det(matrix_direct(rho))


def controls():
    mp.mp.dps = 100
    rho = seed_value()
    rows = []
    for branch in (False, True):
        for side in (False, True):
            w, s, c0, c1 = pars(rho, branch, side)
            z = mp.mpf(".2")
            root = mp.sqrt(1 - z)
            naive = root * mp.power(1 + root, 2 * s - w) * (c0 + c1 * (1 - z)) - mp.power(2, 2 * s - w) * (c0 + c1)
            stable = stable_difference(z, s, w, c0, c1)
            tiny = mp.mpf("1e-40")
            rows.append({
                "branch": branch, "side": side,
                "moderate_difference_error": mp.nstr(abs(naive - stable), 80),
                "tiny_scaled_difference": cstr(stable_difference(tiny, s, w, c0, c1) / tiny, 80),
            })
    return {"kind": "controls", "rows": rows}


def refine(dps):
    mp.mp.dps = dps
    started = time.monotonic()
    z = seed_value()
    out = {"kind": "refinement", "dps": dps}
    try:
        root = mp.findroot(determinant, (z, z + mp.mpc("3e-7", "2e-7")), tol=mp.power(10, -dps + 10), maxsteps=35)
        A = matrix_direct(root)
        v = mp.matrix([A[0, 1], -A[0, 0]])
        v /= mp.sqrt(abs(v[0]) ** 2 + abs(v[1]) ** 2)
        residual = A * v
        out.update({
            "rho": cstr(root, dps), "determinant": cstr(mp.det(A), dps),
            "matrix": [[cstr(A[i, j], dps) for j in range(2)] for i in range(2)],
            "right_null_mixture": [cstr(v[i], dps) for i in range(2)],
            "reader_residuals": [cstr(residual[i], dps) for i in range(2)],
        })
    except Exception as exc:
        out["error"] = str(exc)[:350]
    out["seconds"] = time.monotonic() - started
    return out


def circle_value(k):
    mp.mp.dps = 80
    z = seed_value() + mp.mpf("1e-6") * mp.exp(2j * mp.pi * k / 48)
    return k, cstr(z, 80), cstr(determinant(z), 80)


def emit(row):
    with open(OUT, "a") as f:
        f.write(json.dumps(row) + "\n")
    print(json.dumps({k: v for k, v in row.items() if k not in ("matrix", "samples")}), flush=True)


def main():
    started = time.monotonic()
    emit(controls())
    with cf.ProcessPoolExecutor(max_workers=14) as pool:
        for row in pool.map(refine, (70, 110, 150)):
            emit(row)
        samples = list(pool.map(circle_value, range(48), chunksize=1))
    samples.sort()
    vals = [mp.mpc(*v) for _, _, v in samples]
    winding = sum(mp.arg(vals[(k + 1) % 48] / vals[k]) for k in range(48)) / (2 * mp.pi)
    emit({"kind": "local_contour", "winding": mp.nstr(winding, 40), "samples": [{"rho": z, "det": v} for _, z, v in samples]})
    mp.mp.dps = 100
    anchor = seed_value() + mp.mpc(".001", ".0007")
    emit({"kind": "anchor", "rho": cstr(anchor, 70), "determinant": cstr(determinant(anchor), 90)})
    emit({"kind": "complete", "seconds": time.monotonic() - started})


if __name__ == "__main__":
    main()

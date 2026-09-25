"""Exploratory floating-point deletion areas. Run mathematics on designated Runpod only.

No output is a proof or a certificate. The parent directory is the repository's
required computation store; it does not label this conjecture fully proved.
"""

import os

for variable in ("OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "OMP_NUM_THREADS",
                 "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[variable] = "1"

import argparse
import concurrent.futures
import datetime
import json
import platform
import time

import mpmath as mp
import numpy as np

LABELS = [2, 3, 5, 7]
CHECKPOINTS = [210 * 2 ** k for k in (6, 8, 10, 12)]
BLOCK_SIZE = 16384


def packed(z):
    return {"re": float(z.real), "im": float(z.imag)}


def matrix_packed(a):
    return [[packed(z) for z in row] for row in a]


def measurement(prefix, cross, n):
    area = (cross - cross.T) / 2  # transpose, deliberately NOT conjugate transpose
    terms = [area[0, 1] * area[2, 3], -area[0, 2] * area[1, 3],
             area[0, 3] * area[1, 2]]
    pf = sum(terms)
    scale = sum(abs(z) for z in terms)
    return {"N": n, "endpoints": [packed(z) for z in prefix],
            "area": matrix_packed(area), "pfaffian_terms": [packed(z) for z in terms],
            "pfaffian": packed(pf), "pfaffian_abs": float(abs(pf)),
            "pfaffian_product_scale": float(scale),
            "normalized_pfaffian_abs": float(abs(pf) / scale) if scale else None}


def vector_areas(s, checkpoints, extended=False):
    real_type = np.longdouble if extended else np.float64
    complex_type = np.clongdouble if extended else np.complex128
    s = complex_type(s)
    prefix = np.zeros(4, dtype=complex_type)
    cross = np.zeros((4, 4), dtype=complex_type)
    result = []
    start = 1
    for stop in checkpoints:
        while start <= stop:
            end = min(start + BLOCK_SIZE - 1, stop)
            n = np.arange(start, end + 1, dtype=np.int64)
            weights = np.exp(-s * np.log(n.astype(real_type)))
            coeff = np.column_stack([1 - p * (n % p == 0) for p in LABELS])
            jump = coeff * weights[:, None]
            within = np.cumsum(jump, axis=0)
            before = prefix + within - jump
            cross += before.T @ jump
            prefix += within[-1]
            start = end + 1
        result.append(measurement(prefix, cross, stop))
    return result


def direct_area(s, nmax):
    prefix = [0j] * 4
    cross = [[0j] * 4 for _ in LABELS]
    for n in range(1, nmax + 1):
        w = n ** (-s)
        jump = [(1 - p * (n % p == 0)) * w for p in LABELS]
        for i in range(4):
            for j in range(4):
                cross[i][j] += prefix[i] * jump[j]
        prefix = [a + b for a, b in zip(prefix, jump)]
    return measurement(np.array(prefix), np.array(cross), nmax)


def mp_direct_area(s, nmax):
    mp.mp.dps = 70
    prefix = [mp.mpc(0) for _ in LABELS]
    cross = [[mp.mpc(0) for _ in LABELS] for _ in LABELS]
    for n in range(1, nmax + 1):
        jump = [(1 - p * (n % p == 0)) * mp.power(n, -s) for p in LABELS]
        for i in range(4):
            for j in range(4):
                cross[i][j] += prefix[i] * jump[j]
        prefix = [a + b for a, b in zip(prefix, jump)]
    return measurement(np.array(prefix, dtype=object), np.array(cross, dtype=object), nmax)


def unpack(z):
    return complex(z["re"], z["im"])


def compare(a, b):
    return {"area_max_abs_difference": max(abs(unpack(a["area"][i][j]) -
                    unpack(b["area"][i][j])) for i in range(4) for j in range(4)),
            "endpoint_max_abs_difference": max(abs(unpack(x) - unpack(y))
                    for x, y in zip(a["endpoints"], b["endpoints"])),
            "pfaffian_abs_difference": abs(unpack(a["pfaffian"]) - unpack(b["pfaffian"]))}


def run_case(case):
    start = time.monotonic()
    s = complex(float(case["s_re"]), float(case["s_im"]))
    result = vector_areas(s, CHECKPOINTS, extended=case.get("extended", False))
    return {**case, "checkpoints": result, "elapsed_seconds": time.monotonic() - start}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=6)
    args = parser.parse_args()
    started = time.monotonic()
    mp.mp.dps = 70
    zeros = {k: mp.zetazero(k) for k in (1, 2, 5)}
    cases = []
    for k, root in zeros.items():
        for shift in (mp.mpf(0), mp.mpf("0.1")):
            s = root + shift
            cases.append({"name": "zero_%d_shift_%s" % (k, shift),
                          "s_re": mp.nstr(s.real, 70), "s_im": mp.nstr(s.imag, 70),
                          "approximate_zero": not bool(shift),
                          "zeta_abs_at_mp_parameter": mp.nstr(abs(mp.zeta(s)), 15),
                          "endpoint_targets": [packed((1-mp.power(p, 1-s))*mp.zeta(s))
                                               for p in LABELS]})
    for s in (mp.mpc("1.25", 0), mp.mpc(2, 0), mp.mpc(1, 3)):
        cases.append({"name": "control_%s_%s" % (s.real, s.imag),
                      "s_re": mp.nstr(s.real, 70), "s_im": mp.nstr(s.imag, 70),
                      "approximate_zero": False,
                      "zeta_abs_at_mp_parameter": mp.nstr(abs(mp.zeta(s)), 15),
                      "endpoint_targets": [packed((1-mp.power(p, 1-s))*mp.zeta(s))
                                           for p in LABELS]})
    cases.append({**cases[0], "name": "zero_1_extended_precision", "extended": True})
    s0 = complex(float(zeros[1].real), float(zeros[1].imag))
    fast = vector_areas(s0, [4200])[0]
    direct = direct_area(s0, 4200)
    mp_fast = vector_areas(s0, [2100])[0]
    mp_direct = mp_direct_area(zeros[1], 2100)
    validation = {"scalar_vs_vector_N4200": compare(fast, direct),
                  "mp70_vs_vector_N2100": compare(mp_fast, mp_direct)}
    if max(v["area_max_abs_difference"] for v in validation.values()) > 1e-9:
        raise RuntimeError("independent area implementation mismatch")
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        results = list(pool.map(run_case, cases))
    output = {"purpose": "falsification guidance only; no rigorous root or tail certificate",
              "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "python": platform.python_version(), "numpy": np.__version__,
              "mpmath": mp.__version__, "cpu_count": os.cpu_count(),
              "workers": args.workers, "threads_per_worker": 1,
              "longdouble_decimal_precision": int(np.finfo(np.longdouble).precision),
              "labels": LABELS, "block_size": BLOCK_SIZE, "validation": validation,
              "cases": results, "elapsed_seconds": time.monotonic() - started}
    print(json.dumps(output, indent=2, allow_nan=False))


if __name__ == "__main__":
    main()

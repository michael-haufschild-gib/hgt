"""Frozen fixed-core reserve diagnostic; execute only on the supplied RunPod."""
import os
for option in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[option] = "1"
import json
import math
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

S = [2, 3, 5, 7, 11, 13]
CUTOFFS = [2 ** k for k in range(9, 19)]
THRESHOLD = 1e-8


def source_float(nmax):
    import numpy as np
    from scipy.special import gammaln
    tau = np.zeros(nmax + 1, dtype=np.int64)
    for d in range(1, nmax + 1):
        tau[d::d] += 1
    prime = np.ones(nmax + 1, dtype=bool)
    prime[:2] = False
    for p in range(2, math.isqrt(nmax) + 1):
        if prime[p]:
            prime[p * p::p] = False
    mu = np.ones(nmax + 1, dtype=np.int8)
    mu[0] = 0
    for p in np.flatnonzero(prime):
        mu[p::p] *= -1
        if p * p <= nmax:
            mu[p * p::p * p] = 0
    nums = np.arange(nmax + 1, dtype=np.float64)
    defect = gammaln(nums + 1) - np.cumsum(tau) + 2 * np.euler_gamma * nums
    roots = np.sqrt(nums)
    unit = np.zeros(nmax + 1)
    unit[1:] = np.cumsum(defect[:-1] / (roots[1:] + roots[:-1]))
    indices = np.flatnonzero(mu).astype(np.int64)
    quotient = nmax // indices
    unsigned = roots[indices] * unit[quotient] + (roots[nmax] - roots[indices * quotient]) * defect[quotient]
    return indices, mu[indices] * unsigned


def cutoff_job(nmax):
    import numpy as np
    indices, coeff = source_float(nmax)
    residuals = [None] * (1 << len(S))
    residuals[0] = indices
    divisibility = [indices % p == 0 for p in S]
    energies, heads = [], []
    total = float(np.sum(coeff))
    conservation_error = 0.0
    for mask in range(1 << len(S)):
        if mask:
            bit = (mask & -mask).bit_length() - 1
            previous = residuals[mask ^ (1 << bit)]
            residuals[mask] = np.where(divisibility[bit], previous // S[bit], previous)
        field = np.bincount(residuals[mask], weights=coeff, minlength=nmax + 1)
        energies.append(float(np.dot(field, field)))
        heads.append(float(field[1]))
        conservation_error = max(conservation_error, abs(float(np.sum(field)) - total))
    budget = energies[0]
    edges = []
    for mask in range(1 << len(S)):
        for bit, p in enumerate(S):
            if mask & (1 << bit):
                continue
            target = mask | (1 << bit)
            release = (energies[mask] - energies[target]) / nmax ** 2
            head_release = (heads[mask] ** 2 - heads[target] ** 2) / nmax ** 2
            edges.append({"mask": mask, "p": p, "release": release,
                          "head_release": head_release,
                          "nonempty_release": release - head_release,
                          "parent_below_budget": energies[mask] <= budget,
                          "parent_budget_ratio": energies[mask] / budget})
    return {"M": nmax, "budget": budget, "energies": energies, "heads": heads,
            "edges": edges, "conservation_error": conservation_error}


def audit(nmax, mask, p):
    import mpmath as mp
    mp.mp.dps = 80
    spf = list(range(nmax + 1))
    for prime in range(2, math.isqrt(nmax) + 1):
        if spf[prime] == prime:
            for n in range(prime * prime, nmax + 1, prime):
                if spf[n] == n:
                    spf[n] = prime
    tau, exponent, mu = [0] * (nmax + 1), [0] * (nmax + 1), [0] * (nmax + 1)
    tau[1], mu[1] = 1, 1
    for n in range(2, nmax + 1):
        prime, m = spf[n], n // spf[n]
        if m % prime == 0:
            exponent[n] = exponent[m] + 1
            tau[n] = tau[m] // (exponent[m] + 1) * (exponent[n] + 1)
            mu[n] = 0
        else:
            exponent[n], tau[n], mu[n] = 1, 2 * tau[m], -mu[m]
    roots = [mp.sqrt(n) for n in range(nmax + 1)]
    defect, unit = [mp.mpf(0)] * (nmax + 1), [mp.mpf(0)] * (nmax + 1)
    logfactorial, divisor_total = mp.mpf(0), 0
    for n in range(1, nmax + 1):
        logfactorial += mp.log(n)
        divisor_total += tau[n]
        defect[n] = logfactorial - divisor_total + 2 * mp.euler * n
        unit[n] = unit[n - 1] + defect[n - 1] / (roots[n] + roots[n - 1])
    processed = [q for bit, q in enumerate(S) if mask & (1 << bit)]
    fields = [{}, {}]
    for n in range(1, nmax + 1):
        if not mu[n]:
            continue
        q = nmax // n
        coeff = mu[n] * (roots[n] * unit[q] + (roots[nmax] - roots[n * q]) * defect[q])
        r = n
        for prime in processed:
            if r % prime == 0:
                r //= prime
        rnext = r // p if r % p == 0 else r
        for field, label in zip(fields, (r, rnext)):
            field[label] = field.get(label, mp.mpf(0)) + coeff
    energies = [mp.fsum(x * x for x in field.values()) for field in fields]
    heads = [field.get(1, mp.mpf(0)) for field in fields]
    release = (energies[0] - energies[1]) / nmax ** 2
    hrelease = (heads[0] ** 2 - heads[1] ** 2) / nmax ** 2
    return {"M": nmax, "mask": mask, "processed": processed, "p": p, "digits": 80,
            "energies": [mp.nstr(x, 82) for x in energies],
            "heads": [mp.nstr(x, 82) for x in heads],
            "normalized_release": mp.nstr(release, 82),
            "normalized_nonempty_release": mp.nstr(release - hrelease, 82),
            "negative": bool(release < -mp.mpf(str(THRESHOLD)))}


def main():
    started = time.monotonic()
    os.chdir(Path(__file__).resolve().parent)
    with ProcessPoolExecutor(max_workers=8) as pool:
        runs = sorted(pool.map(cutoff_job, CUTOFFS), key=lambda row: row["M"])
    tail = [{(e["mask"], e["p"]): e for e in row["edges"]} for row in runs[-3:]]
    persistent = []
    for key, edge in tail[-1].items():
        if all(part[key]["release"] < -THRESHOLD for part in tail):
            persistent.append({"mask": key[0], "processed": [p for bit, p in enumerate(S) if key[0] & (1 << bit)],
                               "p": key[1], "tail": [part[key] for part in tail],
                               "parents_below_budget": all(part[key]["parent_below_budget"] for part in tail)})
    blocked_pool = []
    for mask in range((1 << len(S)) - 1):
        if all(all(edge["release"] < -THRESHOLD and edge["parent_below_budget"]
                   for key, edge in part.items() if key[0] == mask) for part in tail):
            blocked_pool.append(mask)
    out = {"primes": S, "cutoffs": CUTOFFS, "threshold": THRESHOLD,
           "runs": runs, "persistent_negative_edges": persistent,
           "fixed_pool_all_negative_release_masks": blocked_pool,
           "screen_seconds": time.monotonic() - started, "audit": None}
    eligible = [e for e in persistent if e["parents_below_budget"]] or persistent
    selected = min(eligible, key=lambda e: e["tail"][-1]["release"]) if eligible else None
    out["audit_status"] = "pending" if selected else "not_triggered"
    Path("summary.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({"screen_seconds": out["screen_seconds"], "persistent_negative_edges": len(persistent),
                      "below_budget": sum(e["parents_below_budget"] for e in persistent),
                      "fixed_pool_all_negative": blocked_pool, "audit_selected": selected}), flush=True)
    if selected:
        out["audit"] = audit(CUTOFFS[-1], selected["mask"], selected["p"])
        out["audit_status"] = "complete"
        final = runs[-1]
        target = selected["mask"] | (1 << S.index(selected["p"]))
        discrepancies = [abs(float(value) - final["energies"][mask]) / CUTOFFS[-1] ** 2
                         for value, mask in zip(out["audit"]["energies"], (selected["mask"], target))]
        out["audit"]["float_normalized_energy_discrepancies"] = discrepancies
        if max(discrepancies) > THRESHOLD:
            raise RuntimeError("independent energy discrepancy exceeds the frozen diagnostic threshold")
        print(json.dumps({"audit": out["audit"]}), flush=True)
    out["total_seconds"] = time.monotonic() - started
    Path("summary.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({"total_seconds": out["total_seconds"], "status": "complete"}), flush=True)


if __name__ == "__main__":
    main()

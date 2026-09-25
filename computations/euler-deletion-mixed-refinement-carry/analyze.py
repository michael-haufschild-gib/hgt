"""Run on the same Runpod; inspect scalar-repair conjecture and finite identity."""
import os
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["OMP_NUM_THREADS"] = "1"
import json
import mpmath as mp
import numpy as np


def z(v):
    return complex(*v)


with open("results.json", encoding="utf-8") as stream:
    payload = json.load(stream)

summary = []
for row in payload["results"]:
    repairs = []
    for p in payload["bases"]:
        qs = [q for q in payload["bases"] if q != p]
        t = np.array([z(row["T"][str(q)][-1]) for q in qs])
        j = np.array([z(row["J"][str(p) + "," + str(q)][-1]) for q in qs])
        kappa = np.vdot(t, j) / np.vdot(t, t)
        residual = float(np.linalg.norm(j - kappa * t) / np.linalg.norm(j))
        repairs.append({"p": p, "kappa": [kappa.real, kappa.imag],
                        "relative_residual": residual})
    item = {
        "label": row["spec"]["label"],
        "s": row["s"],
        "J_2_3": row["J"]["2,3"],
        "J_3_2": row["J"]["3,2"],
        "scalar_repairs": repairs,
        "max_insertion_limit_error": [
            max(v[i] for v in row["insertion_limit_error"].values())
            for i in range(len(payload["cutoffs"]))
        ],
    }
    summary.append(item)
    print(item["label"], "J23", item["J_2_3"][-1],
          "scalar residuals", [round(x["relative_residual"], 6) for x in repairs],
          "limit errors", item["max_insertion_limit_error"], flush=True)

# Independent 50-decimal scalar summation, retaining exact matched finite cutoffs.
mp.mp.dps = 50
s = mp.zetazero(1)
p, q, N = 2, 3, 4096
Z = mp.zeta(s)
S = [mp.mpc(0)]
for n in range(1, p * N + 1):
    S.append(S[-1] + mp.power(n, -s))


def tail(d, k):
    c = mp.power(d, 1 - s)
    return S[k] - c * S[k // d] - (1 - c) * Z


def primitive(d, stop):
    return mp.fsum(tail(d, k) * mp.power(k + 1, -mp.conj(s)) for k in range(stop))


J = mp.power(p, 1 - s) * mp.fsum(
    tail(q, k) * (
        mp.fsum(mp.power(p * k + r, -mp.conj(s)) for r in range(1, p + 1))
        - p * mp.power(p * k + p, -mp.conj(s))
    ) for k in range(N)
)
lhs = primitive(p * q, p * N) - primitive(p, p * N)
rhs = mp.power(p, 2 - 2 * mp.re(s)) * primitive(q, N) + J
check = {"digits": 50, "p": p, "q": q, "N": N,
         "J": [str(mp.re(J)), str(mp.im(J))],
         "matched_finite_identity_error": str(abs(lhs - rhs))}
print("high precision finite check", check, flush=True)
with open("analysis.json", "w", encoding="utf-8") as stream:
    json.dump({"summary": summary, "independent_check": check}, stream, indent=2)

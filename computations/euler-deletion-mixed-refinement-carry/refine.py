"""Runpod: test residue-cell cutoff prediction and specified two-coordinate repairs."""
import os
os.environ["OPENBLAS_NUM_THREADS"] = "1"
import json
import numpy as np

with open("results.json", encoding="utf-8") as stream:
    data = json.load(stream)
records = []
for row in data["results"]:
    s = complex(*row["s"])
    alpha = 2 * s.real
    T = {
        int(q): [complex(*v) - (int(q) ** 2 - 1) / (12 * N ** alpha)
                 for v, N in zip(values, data["cutoffs"])]
        for q, values in row["T"].items()
    }
    errors = [0.0] * len(data["cutoffs"])
    repairs = []
    for p in data["bases"]:
        qs = np.array([q for q in data["bases"] if q != p])
        t = np.array([T[q][-1] for q in qs])
        j = np.array([complex(*row["J"][str(p) + "," + str(q)][-1]) for q in qs])
        channels = {
            "scalar": [],
            "plus_mean": [qs - 1],
            "plus_cell_variance": [qs ** 2 - 1],
            "plus_euler_amplitude": [qs.astype(float) ** (1 - s) - 1],
        }
        fits = {}
        for model, extras in channels.items():
            basis = np.column_stack([t] + extras)
            coeff, _, rank, singular = np.linalg.lstsq(basis, j, rcond=None)
            fits[model] = {
                "relative_residual": float(np.linalg.norm(j - basis @ coeff) / np.linalg.norm(j)),
                "rank": int(rank),
                "condition": float(singular[0] / singular[-1]),
            }
        repairs.append({"p": p, "fits": fits})
        for q in qs:
            for i, N in enumerate(data["cutoffs"]):
                actual = T[p*q][i] - T[p][i] - p ** (2-alpha) * T[q][i]
                direct = complex(*row["J"][str(p) + "," + str(q)][i])
                errors[i] = max(errors[i], abs(actual - direct))
    result = {"label": row["spec"]["label"],
              "cell_corrected_insertion_errors": errors,
              "repairs": repairs}
    records.append(result)
    print(result["label"], "corrected errors", errors,
          "p=2 fits", repairs[0]["fits"], flush=True)
with open("refinement.json", "w", encoding="utf-8") as stream:
    json.dump({"prediction": "T_p(N)-T_p(infinity) ~ (p^2-1)/(12*N^(2*Re(s))) at complete cells",
               "status": "asymptotic prediction tested numerically, not a Lean theorem",
               "records": records}, stream, indent=2)

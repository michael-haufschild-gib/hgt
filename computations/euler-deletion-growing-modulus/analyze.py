"""Runpod-only analysis of the growing-modulus scan."""
import json
import numpy as np

def z(v):
    return complex(*v)

def packed(v):
    return [float(v.real), float(v.imag)]

with open("results.json") as source:
    data = json.load(source)
output = []
for result in data["results"]:
    s = z(result["s"])
    rows = result["rows"]
    p = np.array([r["p"] for r in rows], dtype=float)
    remainder = np.array([z(r["observations"][-1]["after_leading"]) for r in rows])
    repaired = np.array([z(r["observations"][-1]["after_leading_and_G1"]) for r in rows])
    drift = max(abs(z(r["observations"][-1]["estimate"]) -
                    z(r["observations"][-2]["estimate"])) for r in rows)
    delta = np.diff(repaired) / np.diff(np.log(p))
    # Test the proposed coefficient using the final six moduli and retain fit error.
    design = np.column_stack((p ** (1 - s), np.ones(len(p)), np.log(p)))
    coeff, *_ = np.linalg.lstsq(design[-6:], remainder[-6:], rcond=None)
    fit_error = max(abs(design[-6:] @ coeff - remainder[-6:]))
    row = {"label": result["spec"]["label"], "zeta_norm_squared": abs(z(result["zeta"])) ** 2,
           "cutoff_drift_after_tail_model": drift,
           "moduli_last_four": p[-4:].tolist(),
           "after_G1_last_four": [packed(v) for v in repaired[-4:]],
           "log_slopes_last_three": [packed(v) for v in delta[-3:]],
           "fit_coefficients_amplitude_constant_log": [packed(v) for v in coeff],
           "fit_max_error": float(fit_error),
           "normalized_leading_error_at_largest_modulus": rows[-1]["observations"][-1]["leading_normalized_error"]}
    output.append(row)
    print(json.dumps(row), flush=True)
with open("analysis.json", "w") as out:
    json.dump(output, out, indent=2)

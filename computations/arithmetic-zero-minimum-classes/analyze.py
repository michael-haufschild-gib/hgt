"""Runpod-only analysis of the pre-specified minimum and divisor-dominance tests."""
import json
from collections import Counter

with open("results.json") as src:
    data = json.load(src)
zeros = [r for r in data["results"] if r["sigma"] == 0.5]
worst = {"ratio": 0}
for row in zeros:
    values = {v[0]: complex(v[2],v[3]) for v in row["rows"]}
    for p in range(1, data["max_p"]+1):
        for q in range(2, data["max_p"]//p+1):
            if abs(values[p]) == 0:
                continue
            ratio = abs(values[p*q])/abs(values[p])
            if ratio > worst["ratio"]:
                worst = {"ratio": ratio,"zero_index":row["zero_index"],"p":p,"q":q,
                         "W_p":[values[p].real,values[p].imag],
                         "W_pq":[values[p*q].real,values[p*q].imag]}
zero_lookup = {r["zero_index"]:r for r in zeros}
controls = [r for r in data["results"] if r["sigma"] != 0.5]
output = {"zero_tests":len(zeros),"controls":len(controls),
          "below_paper_tail_boundary":sum(r["min_X_minus_wall_boundary"] < 0 for r in zeros),
          "observed_minimum_index_counts":dict(Counter(r["min_X_index"] for r in zeros)),
          "observed_minimum_mobius_counts":dict(Counter(r["rows"][r["min_X_index"]-1][1] for r in zeros)),
          "max_head_order_W_drift":max(r["head_order_max_W_drift"] for r in data["results"]),
          "max_head_order_X_drift":max(r["head_order_max_X_drift"] for r in data["results"]),
          "controls_with_same_observed_min_index":sum(r["min_X_index"] == zero_lookup[r["zero_index"]]["min_X_index"] for r in controls),
          "divisor_dominance_worst":worst,"scan_seconds":data["seconds"],
          "scope":"Finite-grid diagnostics; shifted points are nonzero controls, not counterexamples to RH."}
with open("analysis.json","w") as out:
    json.dump(output,out,indent=2)
print(json.dumps(output,indent=2),flush=True)

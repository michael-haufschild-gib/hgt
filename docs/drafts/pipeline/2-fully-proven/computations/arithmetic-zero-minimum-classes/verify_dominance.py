"""Runpod-only independent check of the frozen divisor-dominance conjecture."""
import json
import mpmath as mp
from verify import w_value

mp.mp.dps = 80
with open("analysis.json") as src:
    witness = json.load(src)["divisor_dominance_worst"]
s = mp.zetazero(witness["zero_index"])
rows = []
for p in [witness["p"],witness["p"]*witness["q"]]:
    head = max(32,int(mp.ceil(4*mp.im(s)/p)))
    wa = w_value(s,p,head,12)
    wb = w_value(s,p,head+32,18)
    rows.append({"p":p,"W":[str(mp.re(wb)),str(mp.im(wb))],
                 "norm":str(abs(wb)),"head_order_drift":str(abs(wb-wa)),
                 "heads":[head,head+32]})
ratio = mp.mpf(rows[1]["norm"])/mp.mpf(rows[0]["norm"])
result = {"digits":80,"orders":[12,18],"zero_index":witness["zero_index"],
          "height":str(mp.im(s)),"p":witness["p"],"q":witness["q"],
          "ratio":str(ratio),"zeta_residual":str(abs(mp.zeta(s))),"values":rows,
          "note":"High-precision diagnostics, not a rigorous interval certificate or Lean proof."}
with open("dominance-verification.json","w") as out:
    json.dump(result,out,indent=2)
print(json.dumps(result,indent=2),flush=True)

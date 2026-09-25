"""Re-verify reported TP5+ violations at dps 150 (rules out roundoff)."""
import json, sys
sys.path.insert(0, "/root/precert")
import mpmath as mp
import theta_common as tc

S = json.load(open("/root/precert/tp2_summary.json"))
print("counts:", json.dumps({"neg": S["neg"], "resolved_neg": S["resolved_neg"], "tot": S["tot"]}))
mp.mp.dps = 150
for rec in S["examples"][:6]:
    xs, ys = rec["xs"], rec["ys"]
    n = len(xs)
    M = mp.matrix([[tc.phi_derivs(mp.mpf(repr(x)) - mp.mpf(repr(y)), order=0)[0] for y in ys] for x in xs])
    d = mp.det(M)
    norm = mp.mpf(1)
    for i in range(n):
        norm *= max(abs(M[i, j]) for j in range(n))
    rel = d / norm
    print(f"order {rec['order']} width {rec['width']}: reported rel_log10={rec['rel_log10']:.2f} "
          f"sign {rec['sign']} -> dps150 rel={mp.nstr(rel, 8)} sign {int(mp.sign(rel))}")

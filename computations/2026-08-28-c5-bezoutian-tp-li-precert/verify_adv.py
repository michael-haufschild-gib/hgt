import json, sys
sys.path.insert(0, "/root/precert")
import mpmath as mp
import theta_common as tc

S = json.load(open("/root/precert/bez_summary.json"))
print("== worst_by_rank (random draws) ==")
for r in sorted(S["worst_by_rank"], key=int):
    rec = S["worst_by_rank"][r]
    print(f"rank {r}: rel_log10={rec['rel_log10']:.2f} regime={rec['regime']}")
print("== adversarial finals ==")
for rec in sorted(S["adversarial"], key=lambda x: x["rank"]):
    print(f"rank {rec['rank']}: final rel_log10={rec['final_rel_log10']}, sign={rec['final_sign']}")

# re-verify every adversarial endpoint at dps 300, with correlation normalization
print("== re-verification at dps 300 ==")
for rec in sorted(S["adversarial"], key=lambda x: x["rank"]):
    mp.mp.dps = 300
    nodes = [mp.mpc(a, b) for a, b in rec["nodes"]]
    M = tc.bezoutian_matrix(nodes)
    n = len(nodes)
    # correlation normalization
    Dg = [mp.sqrt(mp.re(M[i, i])) for i in range(n)]
    C = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            C[i, j] = M[i, j] / (Dg[i] * Dg[j])
    lo, hi, _ = tc.hermitian_min_max_eig(M)
    loc, hic, _ = tc.hermitian_min_max_eig(C)
    print(f"rank {rec['rank']}: raw rel={mp.nstr(lo/hi, 6)} corr_min={mp.nstr(loc, 6)} "
          f"(log10 corr_min={tc.log10_or_none(loc)})", flush=True)

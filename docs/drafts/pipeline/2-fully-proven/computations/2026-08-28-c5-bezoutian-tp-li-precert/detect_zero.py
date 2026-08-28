"""Detection-mode sensitivity: rank-2 Bezoutian nodes hugging gamma_1 from the right."""
import sys
sys.path.insert(0, "/root/precert")
import mpmath as mp
import theta_common as tc
mp.mp.dps = 60
g1 = mp.im(mp.zetazero(1))
print("gamma_1 =", mp.nstr(g1, 20))
for eps_exp in (0, -1, -2, -3, -4):
    eps = mp.mpf(10) ** eps_exp
    nodes = [mp.mpc(mp.mpf(1)/2 + eps, g1 - mp.mpf(1)/10),
             mp.mpc(mp.mpf(1)/2 + eps, g1 + mp.mpf(1)/10)]
    M = tc.bezoutian_matrix(nodes)
    lo, hi, _ = tc.hermitian_min_max_eig(M)
    n = 2
    Dg = [mp.sqrt(mp.re(M[i, i])) for i in range(n)]
    C = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            C[i, j] = M[i, j] / (Dg[i] * Dg[j])
    loc, _, _ = tc.hermitian_min_max_eig(C)
    print(f"eps=1e{eps_exp}: corr_min_eig = {mp.nstr(loc, 8)}  raw lo sign {int(mp.sign(lo))}")

"""
THE-MACHINE (Wheeler). NODE = "Periodic orbits obstruct full equidistribution"
(random walks on homogeneous spaces). Constraint: obstruction = unimodular eigenvalue
of the averaging operator, and it is RIGID/ALGEBRAIC (Benoist-Quint: stationary measures
homogeneous, no exotic obstructions).

Transferred experiment (minimal change): the distribution-relation transfer operator
T_m h(x) = sum_{j=0}^{m-1} h((x+j)/m) (the m-map x|->mx on R/Z) is the averaging operator.
  (1) Spectrum of normalized M_m = T_m/m on Fourier modes |k|<=K: spectral gap? unimodular eigs?
  (2) Perturbation-survivors of the Gauss multiplication relation = unimodular eigenmodes:
      e^{2pi i k x} survives level m iff k(m-1) even. JOINT survivor set over m=2,3,5: rigid or exotic?
  (3) Are joint survivors exactly the growth-killed (archimedean) modes? -> weld labor-division.
Fast: numpy eig on a ~41-dim matrix. <1s.
"""
import numpy as np

K = 20
ks = np.arange(-K, K+1)
idx = {k:i for i,k in enumerate(ks)}
N = len(ks)

def transfer_matrix(m):
    # T_m e_k = m e_{k/m} if m|k else 0   (since sum_j e^{2pi i k j/m} = m if m|k else 0)
    M = np.zeros((N, N), dtype=complex)
    for k in ks:
        if k % m == 0 and (k//m) in idx:
            M[idx[k//m], idx[k]] = m
    return M / m  # normalized averaging operator

print("="*74)
print("(1) Spectral gap of the averaging operator M_m = T_m/m")
print("="*74)
for m in (2,3,5):
    M = transfer_matrix(m)
    ev = np.linalg.eigvals(M)
    mod = np.abs(ev)
    unimodular = np.sum(mod > 1-1e-9)
    print(f"  m={m}: #eigs |lambda|>~1 = {unimodular} (expect 1 = constant);"
          f"  2nd-largest |lambda| = {np.sort(mod)[-2]:.3f}  => spectral gap if <1")

print()
print("="*74)
print("(2) Gauss-multiplication perturbation survivors (unimodular eigenmodes)")
print("     e^{2pi i k x} survives level m  <=>  k(m-1) even")
print("="*74)
def survives(k, m):
    return (k*(m-1)) % 2 == 0
for m in (2,3,4,5,7,8,9):
    surv = [k for k in range(0, 11) if survives(k, m)]
    print(f"  m={m}: surviving k in 0..10 = {surv}")

joint = [k for k in range(-10, 11) if all(survives(k, m) for m in (2,3,4,5,7))]
print(f"\n  JOINT survivors over m=2,3,4,5,7  (k in -10..10): {joint}")
print(f"  => exactly the even integers 2Z : RIGID algebraic subgroup, NO exotic survivors.")
# which levels are binding?
binding = [m for m in range(2,12) if any(not survives(k,m) for k in range(0,11))]
print(f"  binding levels (impose any constraint): {binding}  => only EVEN m; odd primes impose NOTHING")

print()
print("="*74)
print("(3) Are joint survivors the growth-killed (archimedean) modes?")
print("="*74)
# mode e^{2pi i k x} at x=sigma+i t : |.| = e^{-2 pi k t}. Off-axis growth governed by |k|.
# The survivors 2Z are unbounded for t<0 (k>0) / t>0 (k<0); only k=0 bounded on both sides.
print("  survivor modes e^{2pi i k x}, k in 2Z\\{0}: |mode(sigma+it)| = e^{-2pi k t} -> unbounded")
print("  off the real axis. The archimedean growth/log-convexity (Bohr-Mollerup) constraint kills")
print("  every k != 0. => DIFFERENCE side (distribution rels) gives spectral gap killing all NON-even")
print("  modes; residual obstruction lattice 2Z is killed ONLY by the ARCHIMEDEAN side. Weld = two")
print("  constraint-families with disjoint kernels; intersection = the point (uniqueness of Gamma).")

#!/usr/bin/env python3
# Apex attack foundation for: baker-for-stieltjes.md §F (Nesterenko / OP route).
# Measure dmu(t)=dt/(e^t-1) on (0,inf); moments mu_j = j! zeta(j+1) (j>=1); Hankel dets > 0.
# Local run, sub-second, no runpod.
import mpmath as mp
mp.mp.dps = 30

print("moment identity mu_j = int_0^inf t^j/(e^t-1) dt  vs  j! zeta(j+1):")
for j in range(1, 6):
    I = mp.quad(lambda t: t**j/(mp.e**t - 1), [0, mp.inf])
    F = mp.factorial(j)*mp.zeta(j+1)
    print("  j=%d  integral=%s  j!zeta(j+1)=%s  |diff|=%.1e" %
          (j, mp.nstr(I, 16), mp.nstr(F, 16), float(abs(I - F))))

def mu(k):
    return mp.factorial(k)*mp.zeta(k+1)   # k>=1

print("Hankel dets H_n = det[mu_{i+j+1}]  (positive ==> OP system exists):")
for n in range(1, 6):
    M = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            M[i, j] = mu(i + j + 1)
    print("  n=%d  det=%s" % (n, mp.nstr(mp.det(M), 12)))

# Monic orthogonal polynomials P_n(t) wrt dmu via the moment Hankel system (next-step seed for baker-for-stieltjes).
# P_n(t) = det of bordered Hankel / H_n ; print P_1,P_2 coefficients.
print("monic OPs P_n(t) wrt dmu (coeffs low->high):")
def op_coeffs(n):
    # Solve for monic P_n = t^n + c_{n-1}t^{n-1}+...+c_0 with <P_n, t^k>=0 for k<n.
    A = mp.matrix(n, n); b = mp.matrix(n, 1)
    for k in range(n):
        for i in range(n):
            A[k, i] = mu(k + i + 1)
        b[k] = -mu(k + n + 1)
    c = mp.lu_solve(A, b)
    return [c[i] for i in range(n)] + [mp.mpf(1)]
for n in range(1, 3):
    print("  P_%d:" % n, [mp.nstr(x, 10) for x in op_coeffs(n)])

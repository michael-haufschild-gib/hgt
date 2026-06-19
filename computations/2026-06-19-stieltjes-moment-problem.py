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

# --- baker-for-stieltjes §G: the concrete difference auxiliary ---
# R_P(s) = int_0^inf P(t) t^{s-1}/(e^t-1) dt = sum_j a_j Gamma(s+j) zeta(s+j),  P(t)=sum_j a_j t^j.
print()
print("=== difference auxiliary R_P(s)=sum_j a_j Gamma(s+j)zeta(s+j) ===")
def R_lhs(coeffs, s):
    P = lambda t: sum(coeffs[j]*t**j for j in range(len(coeffs)))
    return mp.quad(lambda t: P(t)*t**(s-1)/(mp.e**t-1), [0, mp.inf])
def R_rhs(coeffs, s):
    return sum(coeffs[j]*mp.gamma(s+j)*mp.zeta(s+j) for j in range(len(coeffs)))
for coeffs, s in [([3,-5,1], mp.mpf('1.5')), ([3,-5,1], mp.mpf('2.3')), ([0,2,0,1], mp.mpf('1.7'))]:
    L = R_lhs(coeffs, s); Rr = R_rhs(coeffs, s)
    print("  P=%s s=%s |diff|=%.1e" % (coeffs, mp.nstr(s,3), float(abs(L-Rr))))

# --- baker-for-stieltjes §H: the family is the sigma-orbit of Gamma*zeta ---
# sigma:s->s+1, f_j(s)=Gamma(s+j)zeta(s+j). Claim sigma f_j = f_{j+1}; f_0 has no finite sigma-recurrence.
print()
print("=== sigma-orbit: sigma f_j = f_{j+1}, and sigma f_0/f_0 = s*zeta(s+1)/zeta(s) (not rational) ===")
def f(j, s): return mp.gamma(s+j)*mp.zeta(s+j)
s = mp.mpf('1.3')
for j in range(0, 3):
    print("  sigma f_%d = f_%d : |diff|=%.1e" % (j, j+1, float(abs(f(j, s+1)-f(j+1, s)))))
for s in [mp.mpf('1.3'), mp.mpf('2.1')]:
    print("  s=%s  sigma f_0/f_0=%s  s*zeta(s+1)/zeta(s)=%s" %
          (mp.nstr(s,3), mp.nstr(f(0,s+1)/f(0,s),10), mp.nstr(s*mp.zeta(s+1)/mp.zeta(s),10)))

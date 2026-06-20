# DEAD-END (2026-06-19, DeWitt) — the archimedean/prime split of the secular moments sigma_k FAILS.
# sigma_k^arch := -k[w^k] log Gamma_R(s(w)), s(w)=1/2-sqrt(1/4-w), grows like 4^k from a SPURIOUS
# branch point at w=1/4 (the critical line) injected by the sqrt parametrization into each factor;
# it cancels only in the symmetric xi. Physical sigma_k=sum(1/4+gamma^2)^{-k} ~ (1/200)^k DECREASES.
# Validation FAILED: sigma_1^arch(taylor)=1.86 vs trivial-pole sum -0.31 (4^k branch term dominates).
# Lesson: the secular MOMENTS do not linearly decompose into archimedean+prime as smooth+fluctuation
# (both pieces 4^k-large, cancel). The clean archimedean object is the smooth DENSITY (1/2pi)log(t/2pi),
# not a moment split. Recorded so it is not re-tried. See chat id=420.
#
import mpmath as mp
mp.mp.dps = 60
def s_of_w(w): return (1 - mp.sqrt(1-4*w))/2
def sw_ratio(w): return 2/(1+mp.sqrt(1-4*w))   # = s(w)/w, regular at 0 (=1)
def f(w):
    s = s_of_w(w)
    return -(s/2)*mp.log(mp.pi) + mp.loggamma(s/2+1) - mp.log(sw_ratio(w))
N=12
coeffs = mp.taylor(f, 0, N, method='quad', radius=0.15)  # quadrature-based Taylor, robust
print(" k   sigma_k^arch  (archimedean part of secular moment sigma_k = sum_rho (1/4+gamma^2)^{-k})")
for k in range(1, N+1):
    print(f"{k:3d}   {mp.nstr(-k*coeffs[k], 14)}")
# Validate sigma_1^arch: archimedean trivial-zero w-poles are w_n = (-2n)(1+2n) = -2n(2n+1), n>=1 (Gamma_R poles s=-2n)
direct = mp.nsum(lambda n: mp.mpf(1)/(-2*n*(2*n+1)), [1, mp.inf])
print("\n VALIDATION sigma_1^arch:")
print("   taylor    :", mp.nstr(-1*coeffs[1], 14))
print("   direct sum 1/(-2n(2n+1)), n>=1:", mp.nstr(direct, 14))
print("   (closed form sum_{n>=1} 1/(-2n(2n+1)) = -(2-2log2) = 2log2 - 2 =", mp.nstr(2*mp.log(2)-2,14), ")")

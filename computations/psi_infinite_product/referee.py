# The infinite-order archimedean trivialization psi(s) = prod_{k>=0} zeta(s+k) (foundations 37).
# Checks: (1) difference equation psi(s)=zeta(s)psi(s+1); (2) psi vanishes at the zeta zeros;
#         (3) growth/order probe (finite-order, one-sided: grows as Re s -> -inf).
# psi assembled from local q-Pochhammers prod_k (1-p^{-(s+k)})^{-1}, summed over primes.
# Run: runpod 157.157.221.29:39437, python3.13 + mpmath 1.4.1. 2026-06-19.
import mpmath as mp
mp.mp.dps = 25

def psi(s, K=60):
    p = mp.mpf(1)
    for k in range(K+1):
        p *= mp.zeta(s + k)
    return p

print("=== psi(s)=prod_{k>=0} zeta(s+k): construction check (foundations 37) ===")
for s in [mp.mpf(2), mp.mpf('2.5'), mp.mpf(3)+1j]:
    lhs = psi(s); rhs = mp.zeta(s)*psi(s+1)
    print("s=%s : psi(s)=%s ; |psi(s)-zeta(s)psi(s+1)|=%.2e" % (mp.nstr(s,4), mp.nstr(lhs,8), float(abs(lhs-rhs))))

g1 = mp.im(mp.zetazero(1))
rho = mp.mpf(1)/2 + 1j*g1
print()
print("first zeta zero gamma_1 = %.6f" % float(g1))
print("|psi(rho)| = %.3e   (should ~0: psi vanishes at zeta zeros)" % float(abs(psi(rho))))
print("|psi(1/2+i*10)| = %.4f  (off-zero reference)" % float(abs(psi(mp.mpf(1)/2+10j))))

print()
print("log|psi(sigma+30i)| vs sigma (growth/order probe):")
for sig in [mp.mpf('1.5'), mp.mpf(1), mp.mpf('0.5'), mp.mpf(0), mp.mpf('-1'), mp.mpf('-2')]:
    v = psi(sig + 30j)
    print("  sigma=%+.1f : log|psi|=%+.4f" % (float(sig), float(mp.log(abs(v)))))

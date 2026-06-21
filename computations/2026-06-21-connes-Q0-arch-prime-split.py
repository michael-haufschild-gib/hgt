"""
gpt/24 §H — arch/prime decomposition of the source-aware Q_0 (the "write-the-fake-proof" test).

Fake proof to interrogate: Q_0[p] = Q_arch[p] + Q_prime[p] has a manifestly-positive structure after
the s=1 pole cancellation.  Genuinely undecidable: does it, or is it only massive cancellation
(S_k^A, S_k^P ~ 2^{2k} cancelling to S_k ~ gamma_1^{-2k})?  No expectation baked in — measure it.

Split via the log-derivative (no branch cuts):
   (log Xi)'(w) = xi'/xi(1/2+w) = A(w) + P(w),
   A(w) = 1/(1/2+w) + 1/(w-1/2) - (1/2)log pi + (1/2) psi((1/2+w)/2)   [archimedean + the s,s-1 poles]
   P(w) = zeta'/zeta(1/2+w)                                            [prime]
   S_k = sum_rho (rho-1/2)^{-2k} = -1/2 * [w^{2k-1}] (A+P),  so  S_k^A = -1/2[w^{2k-1}]A, S_k^P = -1/2[w^{2k-1}]P.
Cross-check: S_k should equal (-1)^k * 2 * sum_{gamma>0} gamma^{-2k}  (from the actual zeros).

Chunk args: KMAX dps Nzeros.  Run small first.
"""
import sys, mpmath as mp
KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 4
mp.mp.dps = int(sys.argv[2]) if len(sys.argv) > 2 else 60
NZ   = int(sys.argv[3]) if len(sys.argv) > 3 else 40
ORD = 2*KMAX

def A(w): return 1/(mp.mpf(1)/2+w) + 1/(w-mp.mpf(1)/2) - mp.log(mp.pi)/2 + mp.digamma((mp.mpf(1)/2+w)/2)/2
def P(w): return mp.zeta(mp.mpf(1)/2+w, 1, 1) / mp.zeta(mp.mpf(1)/2+w)

ca = mp.taylor(A, 0, ORD)
cp = mp.taylor(P, 0, ORD)
SA = {k: -ca[2*k-1] for k in range(1, KMAX+1)}   # S_k = -[w^{2k-1}](A+P)  (all-rho sum, no 1/2)
SP = {k: -cp[2*k-1] for k in range(1, KMAX+1)}

# cross-check against the zeros
gam = [mp.zetazero(n).imag for n in range(1, NZ+1)]
TN = gam[-1]
def tail(k):
    p = 2*k-1; return (1/mp.pi)*TN**(-p)/p*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/p)
Szero = {k: (-1)**k * (2*mp.fsum(g**(-2*k) for g in gam) + tail(k)) for k in range(1, KMAX+1)}

print(f"# arch/prime split of S_k (dps={mp.mp.dps}); cancellation depth |S_k^A|/|S_k|")
print(f"# {'k':>2} {'S_k^A':>16} {'S_k^P':>16} {'S_k^A+S_k^P':>16} {'S_k(zeros)':>16} {'split_err':>10} {'|SA|/|S|':>10}")
for k in range(1, KMAX+1):
    s = SA[k]+SP[k]
    err = abs(s - Szero[k])
    canc = abs(SA[k])/abs(s) if s != 0 else mp.inf
    print(f"  {k:>2} {mp.nstr(SA[k],8):>16} {mp.nstr(SP[k],8):>16} {mp.nstr(s,8):>16} {mp.nstr(Szero[k],8):>16} {mp.nstr(err,3):>10} {mp.nstr(canc,5):>10}")

# §H form-level test: inertia of the separate arch / prime / total Hankel forms H_d=[T_{i+j+1}], T_k=(-1)^k S_k
def inertia(Sdict, d):
    H = mp.matrix(d+1, d+1)
    for i in range(d+1):
        for j in range(d+1): H[i,j] = (-1)**(i+j+1) * Sdict[i+j+1]
    ev = mp.eigsy(H, eigvals_only=True)
    npos = sum(1 for e in ev if e > 0); nneg = sum(1 for e in ev if e < 0)
    return npos, nneg, ev[0], ev[-1]
DM = (KMAX-1)//2
print(f"\n# form inertia (npos,nneg) of H_d=[T_{{i+j+1}}] for arch / prime / total (Q_0):")
print(f"# {'d':>2}  {'arch(np,nn)':>12} {'prime(np,nn)':>12} {'Q_0(np,nn)':>12}  {'lmin(Q_0)':>12}")
for d in range(1, DM+1):
    pa = inertia(SA, d); pp = inertia(SP, d); pt = inertia({k: SA[k]+SP[k] for k in SA}, d)
    print(f"  {d:>2}  {str(pa[:2]):>12} {str(pp[:2]):>12} {str(pt[:2]):>12}  {mp.nstr(pt[2],5):>12}")

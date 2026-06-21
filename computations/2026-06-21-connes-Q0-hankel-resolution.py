"""
gpt/24 §C — resolution profile of the source-aware Q_0 Hankel: does the on-line bulk MASK an
off-line quartet until high d, or is it caught at d=1?  (The Hankel analog of the Phi_2 blind-spot.)

Setup: T_k = T_k^bulk + T_k^quartet, where
  T_k^bulk    = 2 sum_{gamma>0} gamma^{-2k}  (first N on-line zeros + density tail),
  T_k^quartet = 2 * Re( y0^k ),  y0 = -1/w0^2,  w0 = a + i*gamma0  (folded FE quartet, weight 2).
Build H_d^(0)=[T_{i+j+1}]_{i,j=0}^d and find the SMALLEST d with lambda_min(H_d^(0)) < 0
(the order at which the quartet is detected). Vary (a, gamma0).

Question (not predictable): is d*=1 for all (a,gamma0) — i.e. the reciprocal-Hankel is faithful at
fixed low order regardless of height/distance, UNLIKE Phi_2 which needed n*~2pi*gamma and missed
far-off-line high zeros?  Or does the bulk push d* up for far/high quartets?

Chunked: args N DMAX dps. Small chunk first (~seconds).
"""
import sys, mpmath as mp
N    = int(sys.argv[1]) if len(sys.argv) > 1 else 80
DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 8
mp.mp.dps = int(sys.argv[3]) if len(sys.argv) > 3 else 60
KMAX = 2*DMAX + 1

gam = [mp.zetazero(n).imag for n in range(1, N+1)]
TN = gam[-1]
def tail(k):
    p = 2*k - 1
    return (1/mp.pi) * TN**(-p)/p * (mp.log(TN/(2*mp.pi)) + mp.mpf(1)/p)
Tb = {k: 2*mp.fsum(g**(-2*k) for g in gam) + tail(k) for k in range(1, KMAX+1)}

def quartetT(a, g0, k):
    w0 = mp.mpc(a, g0)
    y0 = -1/w0**2
    return 2*mp.re(y0**k)            # folded pair {w0,-w0} conj-closed -> 2 Re(y0^k)

def first_indef_d(a, g0):
    Tq = {k: quartetT(a, g0, k) for k in range(1, KMAX+1)}
    for d in range(0, DMAX+1):
        H = mp.matrix(d+1, d+1)
        for i in range(d+1):
            for j in range(d+1):
                H[i,j] = Tb[i+j+1] + Tq[i+j+1]
        ev = mp.eigsy(H, eigvals_only=True)
        if ev[0] < 0:
            return d, ev[0]
    return None, None

print(f"# Q_0 Hankel resolution: smallest d with lambda_min(H_d^(0)) < 0 when an off-line quartet")
print(f"# {{+-a +- i*g0}} is added to {N} on-line zeros.  (bulk-only is PD: d*=None)")
print(f"# {'a':>6} {'gamma0':>8}  {'d*':>4}  {'lambda_min(H_d*)':>18}")
for (a, g0) in [(0.1,14.13),(0.25,14.13),(0.4,14.13),(0.25,30.0),(0.25,80.0),
                (0.4,80.0),(0.05,200.0),(0.4,200.0),(0.45,400.0)]:
    d, lm = first_indef_d(mp.mpf(a), mp.mpf(g0))
    ds = str(d) if d is not None else ">DMAX"
    lms = mp.nstr(lm,5) if lm is not None else "  (PD)"
    print(f"  {a:>6} {g0:>8}  {ds:>4}  {lms:>18}")

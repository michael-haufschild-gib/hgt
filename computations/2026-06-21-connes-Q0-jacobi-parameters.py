"""
gpt/24 §B — Jacobi / continued-fraction parameters of the source-aware Q_0 moment sequence.

Chunked: parameters N (zeros), DMAX (Hankel order), DPS at top. Run the small chunk first (~1 min),
read beta_n, then decide whether a bigger chunk (more zeros / higher d / precision) is worth it.

Q_0 = [T_{i+j+1}] is the moment matrix of m_l = T_{l+1}. Recurrence p_{n+1}=(x-a_n)p_n - b_n p_{n-1};
b_n>0 iff positive-definite. Question (informative, not predictable): are b_n cleanly positive and
stable (-> Jacobi/Krein/continued-fraction proof of Q_0>=0 plausible) or fragile? what is their
structure (measure dominated by atom y_1=1/gamma_1^2 plus hard edge at 0)?

For RH zeros: T_k = (-1)^k S_k = 2 sum_{gamma>0} gamma^{-2k}, from N zero ordinates + density tail
2*int_{TN}^inf (1/2pi)log(t/2pi) t^{-2k} dt (matters only for k=1,2).
"""
import sys, mpmath as mp
N    = int(sys.argv[1]) if len(sys.argv) > 1 else 60
DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 4
mp.mp.dps = int(sys.argv[3]) if len(sys.argv) > 3 else 40
KMAX = 2*DMAX + 1

gam = []
for n in range(1, N+1):
    gam.append(mp.zetazero(n).imag)
TN = gam[-1]
def tail(k):                 # 2 * (1/2pi) * int_{TN}^inf log(t/2pi) t^{-2k} dt  (closed form)
    p = 2*k - 1
    return (1/mp.pi) * TN**(-p)/p * (mp.log(TN/(2*mp.pi)) + mp.mpf(1)/p)
T = {k: 2*mp.fsum(g**(-2*k) for g in gam) + tail(k) for k in range(1, KMAX+1)}
m = [T[l+1] for l in range(0, 2*DMAX+1)]

def jacobi_from_moments(mom, d):
    sig = [[mp.mpf(0)]*(2*d+1) for _ in range(d+1)]
    a = [mp.mpf(0)]*(d+1); b = [mp.mpf(0)]*(d+1)
    for l in range(2*d+1): sig[0][l] = mom[l]
    a[0] = mom[1]/mom[0]; b[0] = mom[0]
    for n in range(1, d+1):
        for l in range(n, 2*d-n+1):
            prev2 = sig[n-2][l] if n >= 2 else mp.mpf(0)
            sig[n][l] = sig[n-1][l+1] - a[n-1]*sig[n-1][l] - b[n-1]*prev2
        a[n] = sig[n][n+1]/sig[n][n] - sig[n-1][n]/sig[n-1][n-1]
        b[n] = sig[n][n]/sig[n-1][n-1]
    return a, b

a, b = jacobi_from_moments(m, DMAX)
print(f"# chunk N={N} DMAX={DMAX} dps={mp.mp.dps}; gamma_1={float(gam[0]):.6f} y_1=1/g1^2={1/float(gam[0])**2:.6e}")
print(f"# T_1={mp.nstr(T[1],8)}  T_2={mp.nstr(T[2],8)}  T_{KMAX}={mp.nstr(T[KMAX],6)}  (T_k -> 2*y_1^k)")
print(f"# Jacobi a_n,b_n of m_l=T_{{l+1}}:")
print(f"   {'n':>2}  {'alpha_n':>15}  {'beta_n':>15}  {'b_n>0':>6}  {'b_n/y_1^2':>12}")
y1sq = (1/float(gam[0])**2)**2
ok = True
for n in range(DMAX+1):
    pos = b[n] > 0
    if n >= 1: ok = ok and pos
    print(f"   {n:>2}  {mp.nstr(a[n],8):>15}  {mp.nstr(b[n],8):>15}  {str(pos):>6}  {mp.nstr(b[n]/y1sq,6):>12}")
print(f"# all beta_n>0 (n>=1): {ok}")

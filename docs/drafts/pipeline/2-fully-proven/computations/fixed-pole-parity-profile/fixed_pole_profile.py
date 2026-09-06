# Fixed-pole Weil criterion (corpus: riemannHypothesis_iff_primeGammaPoleInequality), exact entries.
#   kappa = -gamma - log(2 pi);  L(t) = -log(1-exp(-t))
#   B0(a) = int_0^{2a} L(t) dt
#   B1(a) = e^a/2 * int_0^{2a} e^{-t} L(2t) dt + e^{-a} * int_0^{2a} e^{t} (L(t) - L(2t)/2) dt
#   EM(t) = sum_{2<=n<=e^t} Lambda(n)/n - t ;  psi(X) = sum_{n<=X} Lambda(n)
#   T(a)  = sum_{2<=n<=floor(e^{2a})} Lambda(n)(1+1/n)(2a - log n)
#   A(a)  = kappa*2 sinh a - e^a + (1-2a)e^{-a} + B1 - 2 e^a EM(2a) + 2 e^{-a} psi(e^{2a})
#   C(a)  = kappa*2a + 2a^2 + (2 sinh a)^2 + B0 - T(a)
#   RH <=> |C(a)| <= A(a) for all a>0.  even = A + C, odd = A - C.  Guidance only.
import numpy as np, math, sys
from mpmath import mp, quad, log, exp, euler, pi, mpf
mp.dps = 30
XMAX = int(math.exp(2*8.0)) + 2   # a <= 8
# sieve Lambda(n)
N = XMAX
lam = np.zeros(N+1)
spf = np.zeros(N+1, dtype=np.int64)
for i in range(2, N+1):
    if spf[i] == 0:
        for j in range(i, N+1, i):
            if spf[j] == 0: spf[j] = i
for n in range(2, N+1):
    p = spf[n]; m = n
    while m % p == 0: m //= p
    if m == 1: lam[n] = math.log(p)
ns = np.arange(N+1, dtype=np.float64)
logn = np.zeros(N+1); logn[1:] = np.log(ns[1:])
psi_c = np.cumsum(lam)                    # psi(x) = psi_c[floor x]
M1_c = np.cumsum(np.where(ns>0, lam/np.maximum(ns,1), 0.0))
w = lam*(1+1/np.maximum(ns,1)); S1 = np.cumsum(w); S2 = np.cumsum(w*logn)   # T = 2a*S1 - S2
kappa = float(-euler - log(2*pi))
def L(t): return -log(1-exp(-t))
def B0(a): return float(quad(L, [0, 2*a]))
def B1(a):
    a = mpf(a)
    i1 = quad(lambda t: exp(-t)*L(2*t), [0, 2*a])
    i2 = quad(lambda t: exp(t)*(L(t)-L(2*t)/2), [0, 2*a])
    return float(exp(a)/2*i1 + exp(-a)*i2)
def entries(a):
    X = math.exp(2*a); k = int(math.floor(X))
    if k > N: raise ValueError
    psi = psi_c[k]; EM = M1_c[k] - 2*a; T = 2*a*S1[k] - S2[k]
    b0 = B0(a); b1 = B1(a)
    A = kappa*2*math.sinh(a) - math.exp(a) + (1-2*a)*math.exp(-a) + b1 - 2*math.exp(a)*EM + 2*math.exp(-a)*psi
    C = kappa*2*a + 2*a*a + (2*math.sinh(a))**2 + b0 - T
    return A, C, b0, b1, EM, psi, T
grid = list(np.round(np.arange(0.01, 0.5, 0.01), 4)) + list(np.round(np.arange(0.5, 8.0001, 0.02), 4))
rows = []
for a in grid:
    A, C, b0, b1, EM, psi, T = entries(float(a))
    rows.append((a, A, C, A+C, A-C, b0, b1, EM, psi, T))
    print(f"a={a:6.3f} A={A: .6e} C={C: .6e} even={A+C: .6e} odd={A-C: .6e} |C|/A={abs(C)/A if A!=0 else float('nan'): .4f} B0={b0:.5f} B1={b1:.5f} EM={EM: .4f} psi={psi:.3f}")
    sys.stdout.flush()
rows = np.array(rows)
A = rows[:,1]; C = rows[:,2]
ok = A > 0
print("\nmin over grid of A - |C| :", (A-np.abs(C)).min(), "at a =", rows[np.argmin(A-np.abs(C)),0])
print("min over grid of (A-|C|)/A:", ((A-np.abs(C))/A)[ok].min(), "at a =", rows[ok][np.argmin(((A-np.abs(C))/A)[ok]),0])
print("min even/e^a:", (rows[:,3]/np.exp(rows[:,0])).min(), "at a=", rows[np.argmin(rows[:,3]/np.exp(rows[:,0])),0])
print("min odd/e^a :", (rows[:,4]/np.exp(rows[:,0])).min(), "at a=", rows[np.argmin(rows[:,4]/np.exp(rows[:,0])),0])
neg = rows[(rows[:,3] < 0) | (rows[:,4] < 0)]
print("grid points with a negative parity energy:", len(neg))
for r in neg[:40]: print("  NEG a=%.3f even=%.4e odd=%.4e" % (r[0], r[3], r[4]))
np.save("fixed_pole_profile.npy", rows)

"""comp73 [P3] / gpt/43 #3 — source-side s_d from prime truncations: is a finite prime
sum a FAITHFUL source for the derivatives (zeta'/zeta)^{(2k-1)}(1/2) that feed T_k^P?

The reciprocal moments split T_k = T_k^A (archimedean: Gamma/pole/trivial, closed) + T_k^P
(prime part).  comp64: T_k^P is built from g_k := (zeta'/zeta)^{(2k-1)}(1/2).  The Dirichlet
series (zeta'/zeta)(s) = -sum_n Lambda(n) n^{-s} converges only for Re s>1; at s=1/2 the partial
sum is dominated by the s=1 POLE (~2 sqrt X) with O(sqrt X) ZERO-driven oscillation.  So:
  g_k via mpmath (a genuine SOURCE method, Euler-Maclaurin -- NOT zero-feeding) = the target.
  S_k(X) = -sum_{n<=X} Lambda(n)(-log n)^{2k-1} n^{-1/2}             (sharp prime truncation)
  P_k(X) = same with a smooth Riesz cutoff phi(n/X)=(1-(n/X))^2  (tames the cutoff edge).
Question (gpt/43): does S_k/P_k -> g_k as X grows?  If it diverges/oscillates, finite primes
are NOT a faithful source for the residual sign -> the no-zero-feeding extraction genuinely
needs the full distributional explicit formula (pole subtraction + zero sum), not a truncation."""
import numpy as np, mpmath as mp
mp.mp.dps = 40
N = 2_000_000
KS = (1,2,3)

# ---- target g_k = (zeta'/zeta)^{(2k-1)}(1/2)  (source: mpmath, no zeros)
def zlz(s): return mp.zeta(s,derivative=1)/mp.zeta(s)
half = mp.mpf('0.5')
g = {k: mp.diff(zlz, half, 2*k-1) for k in KS}
print("target g_k = (zeta'/zeta)^{(2k-1)}(1/2)  [source via mpmath]:")
for k in KS: print(f"   k={k} (order {2*k-1}):  {mp.nstr(g[k],12)}")

# ---- von Mangoldt Lambda(n) via sieve of smallest-prime-factor
print(f"\nsieving Lambda(n), n<= {N} ...")
spf = np.zeros(N+1, dtype=np.int64)
for i in range(2, int(N**0.5)+1):
    if spf[i]==0:
        spf[i*i::i] = np.where(spf[i*i::i]==0, i, spf[i*i::i])
Lam = np.zeros(N+1)
n = np.arange(N+1)
for i in range(2, N+1):
    p = spf[i] if spf[i] else i           # i prime if spf==0
    m = i
    while m % p == 0: m //= p
    if m == 1: Lam[i] = np.log(p)          # prime power p^a -> log p
# vectorize the prime-power test cheaply: redo with logs
Lam = np.zeros(N+1)
isp = spf==0; isp[:2]=False
prime_idx = np.nonzero(isp)[0]
Lam[prime_idx] = np.log(prime_idx.astype(float))
# prime powers p^a<=N, a>=2
for p in prime_idx:
    if p*p>N: break
    q=p*p
    while q<=N:
        Lam[q]=np.log(p); q*=p

logn = np.zeros(N+1); logn[2:] = np.log(n[2:].astype(float))
inv_sqrt = np.zeros(N+1); inv_sqrt[2:] = n[2:].astype(float)**(-0.5)

checkpoints = [int(x) for x in (1e3,1e4,1e5,3e5,1e6,2e6)]
print("\n=== sharp truncation S_k(X) vs target g_k (does it converge?) ===")
print(f"{'X':>10} | "+" | ".join(f"k={k}: S_k(X)        gap=S-g" for k in KS))
for X in checkpoints:
    mask = np.zeros(N+1,dtype=bool); mask[2:X+1]=True
    row=[]
    for k in KS:
        term = -Lam*((-logn)**(2*k-1))*inv_sqrt
        Sk = float(np.sum(term[mask]))
        row.append(f"{Sk:14.4f} {Sk-float(g[k]):12.3f}")
    print(f"{X:>10} | "+" | ".join(row))

print("\n=== smooth Riesz cutoff P_k(X)=-sum Lambda (-log n)^{2k-1} n^{-1/2}(1-n/X)^2 ===")
print(f"{'X':>10} | "+" | ".join(f"k={k}: P_k(X)        gap=P-g" for k in KS))
for X in checkpoints:
    u = np.zeros(N+1); u[2:X+1] = 1.0 - n[2:X+1].astype(float)/X
    w = u*u
    row=[]
    for k in KS:
        term = -Lam*((-logn)**(2*k-1))*inv_sqrt*w
        Pk = float(np.sum(term))
        row.append(f"{Pk:14.4f} {Pk-float(g[k]):12.3f}")
    print(f"{X:>10} | "+" | ".join(row))

# oscillation scale: std of S_1(X) over a window of X near the top decade
print("\n=== fluctuation scale of S_1(X) over X in [1e6, 2e6] (sampled) vs sqrt(X) ~", f"{(2e6)**0.5:.0f} ===")
xs = np.linspace(1_000_000, 2_000_000, 40, dtype=int)
term1 = -Lam*((-logn)**1)*inv_sqrt
csum = np.cumsum(term1)
vals = csum[xs]
print(f"   S_1 range over window: [{vals.min():.2f}, {vals.max():.2f}], spread={vals.max()-vals.min():.2f}; target g_1={float(g[1]):.4f}")
print("\nDONE")

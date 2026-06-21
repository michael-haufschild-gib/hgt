"""
gpt/27 Comp 4 (= gpt/25 recommendation) — deflated Q_0 tables.

Tests the conjectured proof shape: the Q_0 measure is "dominant atom y_1 + tail", so deflating the
first r known on-line atoms should improve conditioning and expose a stable residual — OR instability
just migrates to y_{r+1} (the y_n=1/gamma_n^2 are close: ratios ~0.45). Genuinely undecidable which.

Deflate: T_k^(r) = T_k - 2 sum_{n=1}^r y_n^k,  y_n = 1/gamma_n^2  (removes the first r on-line atoms).
Residual T_k^(r) = 2 sum_{n>r} y_n^k. Build H_{d,r} = [T_{i+j+1}^(r)], report lambda_min, condition number.

Chunk args: N DMAX dps. Small first.
"""
import sys, mpmath as mp
N    = int(sys.argv[1]) if len(sys.argv) > 1 else 120
DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
mp.mp.dps = int(sys.argv[3]) if len(sys.argv) > 3 else 80
KMAX = 2*DMAX + 1

gam = [mp.zetazero(n).imag for n in range(1, N+1)]
y = [1/g**2 for g in gam]
TN = gam[-1]
def tail(k):
    p = 2*k-1; return (1/mp.pi)*TN**(-p)/p*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/p)
T = {k: 2*mp.fsum(g**(-2*k) for g in gam) + tail(k) for k in range(1, KMAX+1)}

def Tdef(k, r):                       # deflate first r atoms
    return T[k] - 2*mp.fsum(y[n]**k for n in range(r))

def block(r, d):
    H = mp.matrix(d+1, d+1)
    for i in range(d+1):
        for j in range(d+1): H[i,j] = Tdef(i+j+1, r)
    ev = mp.eigsy(H, eigvals_only=True)
    nneg = sum(1 for e in ev if e < 0)
    return ev[0], ev[-1], nneg

def christoffel(r, d):                # Hankel of measure prod_{l<r}(y-y_l)^2 * y * sum delta_{y_n}
    H = mp.matrix(d+1, d+1)
    w = [mp.fprod((y[n]-y[l])**2 for l in range(r)) for n in range(N)]  # kills n<r
    for i in range(d+1):
        for j in range(d+1):
            H[i,j] = 2*mp.fsum(w[n]*y[n]**(i+j+1) for n in range(N))
    ev = mp.eigsy(H, eigvals_only=True)
    return ev[0], ev[-1], sum(1 for e in ev if e < 0)

print(f"# deflated Q_0: N={N} dps={mp.mp.dps}; y_1={float(y[0]):.4e} y_2={float(y[1]):.4e} (ratio {float(y[1]/y[0]):.3f})")
print(f"# A) NAIVE moment-subtraction  H_{{d,r}}=[T_{{i+j+1}}-2 sum_{{n<r}} y_n^{{i+j+1}}], d={DMAX}:")
print(f"#   {'r':>3} {'lambda_min':>14} {'cond':>12} {'nneg':>5}")
for r in [0,1,2,5,10]:
    lmin, lmax, nneg = block(r, DMAX); cond = lmax/lmin if lmin != 0 else mp.inf
    print(f"    {r:>3} {mp.nstr(lmin,6):>14} {mp.nstr(cond,5):>12} {nneg:>5}")
print(f"# B) CHRISTOFFEL multiplicative  test p=prod_{{l<r}}(y-y_l)*q, d_q={DMAX}:")
print(f"#   {'r':>3} {'lambda_min':>14} {'cond':>12} {'nneg':>5}")
for r in [0,1,2,5]:
    lmin, lmax, nneg = christoffel(r, DMAX); cond = lmax/lmin if lmin != 0 else mp.inf
    print(f"    {r:>3} {mp.nstr(lmin,6):>14} {mp.nstr(cond,5):>12} {nneg:>5}")

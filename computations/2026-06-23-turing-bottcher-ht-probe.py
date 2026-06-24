import mpmath as mp
# Bottcher coordinate phi for f(z)=z^2+c: phi(z^2+c)=phi(z)^2, phi(z)~z near infinity.
# phi(z) = z * prod_{k>=0} (1 + c/z_k^2)^(1/2^(k+1)), z_0=z, z_{k+1}=z_k^2+c.
# Precision-plateau HT-probe: does best algebraic-ODE residual FREEZE under precision (HT) or TRACK it (DA)?

def bottcher(z, c, terms=10):
    # fixed term count (no break) -> smooth function for reliable mp.diff; |z|>=5 converges by ~k=5
    zk = mp.mpc(z); acc = mp.mpc(1)
    for k in range(terms):
        acc *= (1 + c/zk**2)**(mp.mpf(1)/mp.mpf(2)**(k+1))
        zk = zk*zk + c
    return z*acc

def jets(c, z, n):
    f = lambda w: bottcher(w, c)
    out = [f(z)]
    for q in range(1, n+1):
        out.append(mp.diff(f, z, q))
    return out

def monos(n, d, A):
    def es(n, d):
        if n == 0:
            for e in range(d+1): yield (e,)
        else:
            for e in range(d+1):
                for r in es(n-1, d-e): yield (e,)+r
    return [(a, e) for a in range(A+1) for e in es(n, d)]

PTS = [mp.mpc(re, im) for re in ('5.0','6.0','7.0','8.0','9.0','10.0')
                       for im in ('0.5','-1.3','2.1','-2.7','1.0','-0.4','3.0')]  # 42 pts, |z|>=5

def sigma_min(c, n, d, A, dps):
    mp.mp.dps = dps
    mons = monos(n, d, A); ncol = len(mons)
    rows = []
    for z in PTS:
        j = jets(c, z, n)
        rows.append([(z**a)*mp.fprod([j[t]**e[t] for t in range(n+1)]) for (a, e) in mons])
    M = mp.matrix(rows)
    nu = [mp.sqrt(sum(abs(M[r,cc])**2 for r in range(M.rows))) for cc in range(ncol)]
    nu = [x if x != 0 else mp.mpf(1) for x in nu]   # guard zero-norm columns
    Mn = mp.matrix([[M[r,cc]/nu[cc] for cc in range(ncol)] for r in range(M.rows)])
    S = mp.svd(Mn, compute_uv=False)
    k = min(M.rows, ncol)
    return ncol, S[k-1]

for label, c in (('c=0 (DA control, phi=z)', mp.mpf(0)), ('c=i (generic)', mp.mpc(0,1))):
    print(f"=== {label} ===")
    for (n, d, A) in [(1,2,2),(1,3,2),(2,2,1)]:
        nc, s40 = sigma_min(c, n, d, A, 40)
        _,  s70 = sigma_min(c, n, d, A, 70)
        frozen = abs(s70/s40 - 1) < mp.mpf(10)**(-2) if s40 != 0 else False
        print(f"  n={n} d={d} A={A} ncol={nc}: sigma_min dps40={mp.nstr(s40,4)} dps70={mp.nstr(s70,4)}  FROZEN={frozen}")
print("FROZEN (dps40==dps70) => no exact relation, residual is a real positive floor = HT-suggestive (like Gamma).")
print("TRACKS (drops ~10^-30) => exact algebraic ODE exists = DA.")

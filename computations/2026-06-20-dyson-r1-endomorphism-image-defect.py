# THE MACHINE R1 (dyson). NODE=Endomorphism operator (difference algebra).
# Experiment transferred: iterate the natural self-map (shift sigma: f(s)->f(s+1)),
# measure whether {f,sigma f,...} closes into a low-order relation over C(s)
# (image-defect plateaus = endomorphism catches) or never closes (defect grows = resist).
import mpmath as mp
mp.mp.dps = 60

def gram_min_ratio(rows):
    n = len(rows[0]); m = len(rows)
    G = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            G[i,j] = mp.fsum(mp.conj(rows[k][i])*rows[k][j] for k in range(m))
    E = mp.eigsy(G, eigvals_only=True)
    ev = sorted(abs(x) for x in E)
    return ev[0]/ev[-1]

def fit_order1_affine(f, pts, sdeg=3):
    rows = []
    for s in pts:
        f0 = f(s); f1 = f(s+1)
        row = [s**k * f1 for k in range(sdeg+1)] + [s**k * f0 for k in range(sdeg+1)] + [s**k for k in range(sdeg+1)]
        rows.append(row)
    return gram_min_ratio(rows)

pts = [mp.mpf('1.3')+mp.mpf('0.37')*k for k in range(16)]
print("Gamma (DA order1, Gamma(s+1)=s Gamma(s)) :", mp.nstr(fit_order1_affine(mp.gamma, pts), 6))
ptz = [mp.mpf('2.2')+mp.mpf('0.41')*k for k in range(16)]
print("zeta  (diff-transcendental [conj])       :", mp.nstr(fit_order1_affine(mp.zeta, ptz), 6))
g = lambda s: mp.e**(2j*mp.pi*s)
print("control 1-periodic exp(2pi i s) (Fix sig):", mp.nstr(fit_order1_affine(g, pts), 6))
# dps stability check on zeta verdict
mp.mp.dps = 90
print("zeta @dps90 (stability)                  :", mp.nstr(fit_order1_affine(mp.zeta, ptz), 6))

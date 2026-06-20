# THE MACHINE R2 (dyson). NODE=Wilson loops (gauge-inv parallel transport).
# Transfer A: closed-contour content W(C)=#zeros-#poles inside; scaling vs contour geometry.
# Transfer B: weld "curvature" = infinitesimal-plaquette holonomy [d_s, M_p] (M_p f = p^-s f).
import mpmath as mp
mp.mp.dps = 30
PI = float(mp.pi)

print("=== A. Wilson content scaling: (#zeros-#poles in contour C) vs contour size ===")
print("Gamma (disk radius R, content=#poles 0..R):")
for R in [5,10,20,40,80]:
    nP = R+1
    print(f"  R={R:3d}  perim~2piR={2*PI*R:8.1f}  area~piR^2={PI*R*R:10.1f}  N={nP:4d}  N/R={nP/R:.3f}")
print("zeta (box height T in strip, content=#nontrivial zeros 0<Im<=T, Riemann-Siegel count):")
for T in [10,30,50,100,200]:
    N = int(mp.nzeros(T))
    NTlogT = N/(T*float(mp.log(T)))
    print(f"  T={T:4d}  perim~4T={4*T:6d}  area~2T={2*T:5d}  N={N:5d}  N/T={N/T:.3f}  N/(TlogT)={NTlogT:.4f}")

print()
print("=== B. weld curvature [d_s,M_p] on test objects (predict = -log p, object-independent) ===")
for (name,f) in [("Gamma",mp.gamma),("zeta",mp.zeta),("p^-s control",lambda s: mp.mpf(2)**(-s))]:
    p = 3; s0 = mp.mpf('2.7')
    Mp = lambda s: mp.mpf(p)**(-s) * f(s)
    lhs = mp.diff(Mp, s0) - mp.mpf(p)**(-s0)*mp.diff(f, s0)
    ratio = lhs / (mp.mpf(p)**(-s0)*f(s0))
    print(f"  {name:14s}: [d_s,M_p]f/(M_p f) = {mp.nstr(ratio,8)}   (-log {p} = {mp.nstr(-mp.log(p),8)})")

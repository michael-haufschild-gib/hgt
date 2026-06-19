#!/usr/bin/env python3.13
"""
arakelov_w_coordinate.py -- Critic 2026-06-19.  B7 (height/Arakelov theory of zeros).
Multiplicative coordinate w_rho = 1 - 1/rho.  CLAIM (derived):
   |w_rho| = 1  <=>  Re(rho) = 1/2   exactly;   and
   |w_rho|^2 - 1 = A(1-2*beta)/A^2  with A=beta^2+gamma^2  =>  Re>1/2 INSIDE (|w|<1), Re<1/2 OUTSIDE (|w|>1).
Canonical height h(rho)=|log|w_rho||  >=0, =0 iff on the critical line (Kronecker-type).
Verify on the first N genuine zeros (on line) and on off-line test points (dichotomy).
Archive: publications/galois-for-l-functions/computations/arakelov_w_coordinate/.
"""
import mpmath as mp
mp.mp.dps = 30
N = 50
print(f" dps={mp.mp.dps}; first {N} zeta zeros (on the line, should give |w|=1, h=0):")
maxdev = mp.mpf(0)
for n in range(1, N+1):
    rho = mp.mpc(mp.mpf(1)/2, mp.im(mp.zetazero(n)))
    w = 1 - 1/rho
    dev = abs(abs(w) - 1)
    maxdev = max(maxdev, dev)
    if n <= 5 or n == N:
        print(f"   gamma_{n}={float(mp.im(rho)):.5f}:  |w|={mp.nstr(abs(w),20)}  h=|log|w||={mp.nstr(abs(mp.log(abs(w))),6)}")
print(f"   => max ||w|-1| over first {N} zeros = {mp.nstr(maxdev,6)}   (should be ~1e-(dps))")

print("\n off-line test points rho=beta+i*gamma (gamma=14.1347, first ordinate); dichotomy check:")
g0 = mp.im(mp.zetazero(1))
for beta in [mp.mpf('0.30'), mp.mpf('0.40'), mp.mpf('0.50'), mp.mpf('0.60'), mp.mpf('0.70')]:
    rho = mp.mpc(beta, g0); w = 1 - 1/rho
    side = "ON  line" if abs(abs(w)-1)<mp.mpf(10)**(-20) else ("INSIDE (|w|<1)" if abs(w)<1 else "OUTSIDE (|w|>1)")
    A = beta**2 + g0**2
    pred = A*(1-2*beta)   # sign of |w|^2-1
    print(f"   beta={float(beta):.2f}: |w|={mp.nstr(abs(w),18)}  h={mp.nstr(abs(mp.log(abs(w))),6)}  [{side}]  sign(|w|^2-1)=sign(A(1-2b))={'+' if pred>0 else '-' if pred<0 else '0'}")

print("\n FE pairing rho<->1-rho (on line, gamma=14.1347): |w_rho|*|w_{1-rho}| (product-formula balance?):")
rho = mp.mpc(mp.mpf(1)/2, g0); rhobar = 1-rho
wr, wb = 1-1/rho, 1-1/rhobar
print(f"   |w_rho|={mp.nstr(abs(wr),18)}  |w_(1-rho)|={mp.nstr(abs(wb),18)}  product={mp.nstr(abs(wr)*abs(wb),18)}")
beta=mp.mpf('0.7'); rho=mp.mpc(beta,g0); rhoFE=mp.mpc(1-beta,g0)  # FE partner shares gamma under reflection
wr,wf = 1-1/rho, 1-1/rhoFE
print(f"   off-line beta=0.7: |w_rho|={mp.nstr(abs(wr),12)} |w_(1-beta)|={mp.nstr(abs(wf),12)} product={mp.nstr(abs(wr)*abs(wf),12)}")
print("\n VERDICT: |w|=1 exactly on the critical line; inside/outside off it; h=0 iff on line (Kronecker height).")

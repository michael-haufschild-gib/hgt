#!/usr/bin/env python3
# THE MACHINE (procedural workflow). Round: NODE = Anvil-shaped cloud tops (codex list -> rng 19 ->
# Thunderstorms -> codex list -> rng 2 -> Anvil tops). Seeds: 887799326869491222.
# NODE RULES (codex, Step 5): convective column grows -> hits TROPOPAUSE (stable LID) -> can't rise ->
# spreads HORIZONTALLY -> wind shear stretches downwind -> rare OVERSHOOTING tops punch above briefly.
# ABSTRACT CONSTRAINT: capped vertical growth, redirected sideways at a max-principle lid, rare overshoot.
#
# STEP 6 experiments (on the constraint) -> STEP 7 SAME experiments on Gamma & zeta (& completed Lambda):
#   "vertical" = growth of |f(sigma+it)| as t grows;  "horizontal" = sigma.
#   E1 vertical rate: exponential slope d log|f|/dt  AND polynomial exponent mu(sigma)=dlog|f|/dlog t.
#   E2 lid/convexity: is mu(sigma) convex & decreasing across the strip (Phragmen-Lindelof "stable lid")?
#   E3 overshoot: max|f|/median|f| over a t-window (rare spikes above the anvil level).
#   E4 shear/asymmetry: mu(sigma) vs mu(1-sigma); is the COMPLETED Lambda anvil symmetric about 1/2?
import mpmath as mp
mp.mp.dps=25

SIG=[-0.5, 0.0, 0.25, 0.5, 0.75, 1.0, 1.5]
def winstats(f, sigma, T, n=160):
    ts=[mp.mpf(T)+ (mp.mpf(T))*mp.mpf(i)/mp.mpf(n-1) for i in range(n)]   # t in [T,2T]
    mags=[abs(f(mp.mpc(sigma, t))) for t in ts]
    logs=[mp.log(m) if m>0 else mp.mpf('-1e30') for m in mags]
    # exponential slope d log|f|/dt via least squares
    tb=mp.fsum(ts)/n; lb=mp.fsum(logs)/n
    num=mp.fsum((ts[i]-tb)*(logs[i]-lb) for i in range(n))
    den=mp.fsum((ts[i]-tb)**2 for i in range(n))
    slope=num/den
    mx=max(mags); md=sorted(mags)[n//2]
    return slope, mx, md, logs, ts

def mu_poly(f, sigma, T1=80, T2=400):
    # polynomial growth exponent mu = [log max|f|@T2win - log max|f|@T1win]/[log(1.5 T2)-log(1.5 T1)]
    _,mx1,_,_,_=winstats(f,sigma,T1); _,mx2,_,_,_=winstats(f,sigma,T2)
    return float((mp.log(mx2)-mp.log(mx1))/(mp.log(mp.mpf('1.5')*T2)-mp.log(mp.mpf('1.5')*T1)))

def zeta(s): return mp.zeta(s)
def gamma(s): return mp.gamma(s)
def Lambda(s): return mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)   # completed xi (no s(s-1) factor)

print("== E1 vertical rate: exponential slope d log|f|/dt  (t in [400,800]) ==")
print(f"{'sigma':>6} | {'zeta slope':>12} | {'Gamma slope':>12} | {'Lambda slope':>13}")
for sg in SIG:
    sz,_,_,_,_=winstats(zeta,sg,400); sgm,_,_,_,_=winstats(gamma,sg,400); sl,_,_,_,_=winstats(Lambda,sg,400)
    print(f"{sg:6.2f} | {float(sz):12.5f} | {float(sgm):12.5f} | {float(sl):13.5f}")
print(f"  [Gamma ref -pi/2={float(-mp.pi/2):.5f}; Lambda~Gamma(s/2) ref -pi/4={float(-mp.pi/4):.5f}; zeta poly => ~0]")

print("\n== E2 lid/convexity: polynomial exponent mu(sigma) (zeta) — convex & decreasing? ==")
print(f"{'sigma':>6} | {'mu_zeta':>9} | {'convexity bound (1-s)/2 on [0,1]':>32}")
muz={}
for sg in SIG:
    m=mu_poly(zeta,sg); muz[sg]=m
    cb=(1-sg)/2 if 0<=sg<=1 else float('nan')
    print(f"{sg:6.2f} | {m:9.4f} | {cb:32.4f}")
# discrete convexity check on interior nodes
xs=[0.0,0.25,0.5,0.75,1.0]
print("  discrete 2nd differences of mu_zeta (>=0 => convex lid):")
for i in range(1,len(xs)-1):
    d2=muz[xs[i-1]]-2*muz[xs[i]]+muz[xs[i+1]]
    print(f"    mu''~ at sigma={xs[i]:.2f}: {d2:+.4f}")

print("\n== E3 overshoot: max|f|/median|f| over t in [400,800] (rare spikes above anvil) ==")
print(f"{'sigma':>6} | {'zeta':>10} | {'Gamma':>10} | {'Lambda':>10}")
for sg in SIG:
    _,zx,zd,_,_=winstats(zeta,sg,400); _,gx,gd,_,_=winstats(gamma,sg,400); _,lx,ld,_,_=winstats(Lambda,sg,400)
    print(f"{sg:6.2f} | {float(zx/zd):10.3f} | {float(gx/gd):10.3f} | {float(lx/ld):10.3f}")

print("\n== E4 shear/asymmetry: is the COMPLETED Lambda anvil symmetric about sigma=1/2? ==")
print(f"{'sigma':>6} | {'mu_Lambda(s)':>12} | {'mu_Lambda(1-s)':>14} | {'|diff|':>9}")
for sg in [0.0,0.25,0.5]:
    a=mu_poly(Lambda,sg); b=mu_poly(Lambda,1-sg)
    print(f"{sg:6.2f} | {a:12.4f} | {b:14.4f} | {abs(a-b):9.4f}")
print("\nREAD: zeta = storm (poly vertical growth, anvil mu(sigma)); Gamma = downdraft (exp DECAY slope ~ -pi/2,")
print("      NO anvil); convexity of mu = the Phragmen-Lindelof 'stable lid'; overshoot = large values/pole;")
print("      E4 tests whether the completed Lambda's anvil is reflection-symmetric (functional equation).")

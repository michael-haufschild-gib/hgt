#!/usr/bin/env python3
# THE MACHINE (walk). start->codex related->rng10->Functional equations->codex parts->rng6->
# NODE = d'Alembert eqn f(x+y)+f(x-y)=2 f(x) f(y) (cosine addition law). Seed walk.
# DEEP RULE (codex Step 5): WITH regularity, solutions are RIGIDLY cos(ax)/cosh(ax)/const — a finite-
# parameter family; the single equation + regularity PINS the function. RIGIDITY is the constraint's force.
#
# STEP 6 experiment: how RIGID is a defining functional equation? does a perturbation preserve it?
#   rigid  = no nontrivial perturbation keeps the residual ~0 (the FE alone pins the object).
#   loose  = an infinite-dim family of perturbations keeps residual ~0 (FE under-determines the object).
# STEP 7: run the SAME rigidity test on Gamma's shift-FE and zeta/Lambda's reflection-FE.
import mpmath as mp
mp.mp.dps=30

def dalembert_res(f, xs):
    r=mp.mpf(0)
    for x in xs:
        for y in xs:
            r=max(r, abs(f(x+y)+f(x-y)-2*f(x)*f(y)))
    return r

print("== NODE check: d'Alembert RIGIDITY (cosine addition law) ==")
xs=[mp.mpf('0.3'),mp.mpf('0.7'),mp.mpf('1.1'),mp.mpf('1.9')]
cos=lambda t: mp.cos(t)
print(f"  f=cos(x)            residual = {float(dalembert_res(cos,xs)):.2e}   (solves it)")
for eps in (mp.mpf('0.1'), mp.mpf('0.3')):
    g=lambda t,e=eps: (1+e)*mp.cos(t)
    print(f"  f=(1+{float(eps)})*cos(x)   residual = {float(dalembert_res(g,xs)):.2e}   (rescale BREAKS it)")
P=lambda t: 1+mp.mpf('0.3')*mp.cos(2*mp.pi*t)
gP=lambda t: mp.cos(t)*P(t)
print(f"  f=cos(x)*P(x)       residual = {float(dalembert_res(gP,xs)):.2e}   (period factor BREAKS it)")
print("  => D'Alembert is RIGID: NO nontrivial perturbation preserves it. (cos is DA/elementary.)")

print("\n== STEP 7a: GAMMA shift-FE  f(s+1) = s f(s)  — rigid or loose? ==")
ss=[mp.mpf('1.4'),mp.mpf('2.3'),mp.mpf('3.6'),mp.mpc('1.2','0.8')]
def shift_res(f): return max(abs(f(s+1)-s*f(s)) for s in ss)
Pper=lambda s: 1+mp.mpf('0.3')*mp.cos(2*mp.pi*s)            # period-1 factor (P(s+1)=P(s))
print(f"  f=Gamma             residual = {float(shift_res(mp.gamma)):.2e}   (solves it)")
print(f"  f=Gamma*P (P per-1) residual = {float(shift_res(lambda s: mp.gamma(s)*Pper(s))):.2e}   (STILL solves it -> LOOSE)")
print(f"  sanity Gamma*(1+0.3 cos 2pi s) != Gamma:  |P(1.4)-1| = {float(abs(Pper(mp.mpf('1.4'))-1)):.3f}  (genuine perturbation)")
print("  => Gamma's shift-FE is LOOSE: any period-1 factor preserves it (infinite-dim family). Needs")
print("     Bohr-Mollerup log-convexity to pin Gamma uniquely.")

print("\n== STEP 7b: zeta/LAMBDA reflection-FE  Lambda(s) = Lambda(1-s)  — rigid or loose? ==")
Lam=lambda s: mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)
tt=[mp.mpc('0.3','1.0'),mp.mpc('0.8','2.0'),mp.mpc('0.4','0.5'),mp.mpc('0.2','1.5')]
def refl_res(f): return max(abs(f(s)-f(1-s)) for s in tt)
Qsym=lambda s: 1+mp.mpf('0.3')/((s-mp.mpf('0.5'))**2+1)          # BOUNDED, Q(s)=Q(1-s)
print(f"  f=Lambda            residual = {float(refl_res(Lam)):.2e}   (solves it, by functional equation)")
print(f"  f=Lambda*Q (Q symm) residual = {float(refl_res(lambda s: Lam(s)*Qsym(s))):.2e}   (STILL solves it -> LOOSE)")
print(f"  sanity Q!=1: |Q(0.3+1i)-1| = {float(abs(Qsym(mp.mpc('0.3','1.0'))-1)):.3f}  (genuine perturbation)")
print("  => Lambda's reflection-FE is LOOSE: any reflection-symmetric factor preserves it (infinite-dim).")
print("     Needs Euler product + growth order to pin zeta.")

print("\nREAD: D'Alembert (cos, DA/elementary) = RIGID single-FE (pins a finite-param family). Gamma-shift &")
print("      Lambda-reflection (HT) = LOOSE single-FE (infinite-dim perturbation family; under-determine the")
print("      object; need supplementary constraints to pin). CONJECTURE: HT <=> the natural FE is non-rigid.")

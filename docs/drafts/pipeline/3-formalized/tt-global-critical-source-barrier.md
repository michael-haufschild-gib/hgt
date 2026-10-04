# Global critical barrier for the actual modular source

- **ID:** tt-global-critical-source-barrier (C70)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** TT, actual transported fourth Schur gap / third-minor slope.
- **Statement:** For every actual source point x>0,
  q(x)>1/12−7/(72k(x)), where q=(u−3J)/(uk(9−u²)).

## Frontier contribution

This is a global constraint on the actual trajectory, without a free
source-sign or RH premise. In compact variables h=1/k, r=k²(9−u²),
t=k(1−3J/u), it gives r−12t<(7/6)hr. The old coarse cone admitted a
negative third-slope expanding mode. This removes that leading mode;
it does not prove global third-slope positivity. The full source
quadratic, transported fourth gap, join and all-rank closure remain open.

## Dependency-closed paper proof [PROVED HERE]

Write V=u², T=9−V, b=1/12−7h/72, δ=q−b. Define

    D=4h²/27+31h/72−5/12+V(1+h/3)b/18,
    A=36−5T+(2/9)Vh(3−h)
      +(2/3)V(1+h/3)T(q+b)+(7/108)Vh(1+h/3)T.

The exact source ODE gives δ′=(k/u)(Aδ+TD). Its rescaled field
H=6uh d/dx has Hh=−(4/3)h(3+h)V(h−Tq), HV=12VT. On the
actual ray 0<h<4/5, 0<V<9 and k/u≥1/3.

First, D<0 for 0≤h≤2/3. For 2/3≤h≤4/5, q≤b implies HD<0:
D_h>1/2, b≤1/54, Tb≤1/6 and h−Tb≥1/2. At q=b the exact identity is

    HD=−(2/9)V(3+h)[6h(h−Tb)D_h−Tb]<0.

Decreasing q decreases HD. Consequently, whenever δ≤0 and D=0,
D′<0. Whenever δ=0, δ′=(k/u)TD, with positive coefficient of D.

Near x=0, clear δ's positive denominator with
B=u(1+7T/72−kT/12)−3J. Then B(0)=0 and
B′(0)=12+(279/8)k(0)−(135/4)k(0)²>0 from the established actual
seam range 5/4<k(0)<19/15. Thus δ>0 near the seam.

On the tail, h→0 and V→9 give D<0 and A≥30. If δ≤0 there,
δ′<10δ. The existing bounded-escape lemma and the established bound
on δ rule out a negative tail value. At a zero, δ′<0 would produce
such a value immediately. Hence δ>0 eventually.

For any point x>0 choose positive-δ endpoints a<x≤c. A negative
component of δ inside [a,c] has first and last zero endpoints. At its
left endpoint δ′≤0, hence D≤0. The strict downward crossing law for
D at D=0, while δ≤0, forces D<0 up to the right endpoint. There
δ′<0 contradicts the nonnegative left derivative needed to reach zero
from below. Thus δ≥0 globally. The formal compact-interval lemma
`HTGeometry.TwoFunctionTrap.nonneg_between` supplies this argument.

Finally suppose δ(x)=0. Global nonnegativity makes x a local minimum,
so δ′(x)=0 and hence D(x)=0. Differentiate
δ′=rate·δ+weight·D, weight=(k/u)T>0. At this point
δ″=weight·D′<0, contradicting the second-derivative minimum theorem
already formalized in `DeBruijnLaguerreEvolution`. Therefore δ>0.

The expanding-mode inequality follows from the exact identity

    (7/6)kT−[k²T−12k(1−3J/u)]=12k²Tδ>0.

## Lean certificate

Production leaves under `formal/GaloisForLFunctions/RHTower/`:
`ThetaCuspRatioCriticalFirstJet`, `ThetaCuspRatioCriticalBarrierAlgebra`,
`ThetaCuspRatioCriticalBarrierDynamics`, `ThetaCuspRatioBoundaryTrap`,
`ThetaCuspRatioCriticalBarrierSeamTail`, `ThetaCuspRatioCriticalBarrierGlobal`,
`ThetaCuspRatioCriticalBarrierStrict`.

Actual capstones in `RHTower.ThetaCuspModularRatio`:
`criticalError_pos`, `boundaryRatio_gt_critical_barrier`,
`expandingMode_critical_upper`. Every production leaf passed direct
`lake env lean` audit; no full or umbrella build, no raised heartbeat.
Imported type/axiom audit of fifteen results passed: only `propext`,
`Classical.choice`, `Quot.sound`. Logs: `/tmp/tt_c70_prod_*.log` and
`/tmp/tt_c70_production_axioms.log`. All seven leaves are wired into
`RHTower.lean`; index exit 0. Lint exit 1: twelve unrelated missing umbrella imports; no C70 finding.
Full lint log: `/tmp/tt_c70_lint.log`.

The first-jet precursor proves
P_h(0,r,r/12)=(7/6)Cr for C=6²⁴·1990656·1679616. It identifies
the affine correction directly from the exact third-minor polynomial.

## Log

- 2026-10-04 — Strict actual barrier proved; seven production leaf audits
  passed. Full third-slope sign remains the next hard open problem.

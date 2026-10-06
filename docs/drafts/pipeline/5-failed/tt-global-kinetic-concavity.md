# TT C86 — Global kinetic concavity

- Stage: 5-failed candidate; Route TT remains active.
- Parent: `../1-in-progress/tt-kinetic-contraction-source.md`.
- Lean: complete scratch proofs passed; 41 production leaves staged and wired,
  serial direct production audits running. Imported production audit pending.

The candidate required the entire reduced kinetic source to be concave in
its kinetic coordinate throughout the nonlinear cone. Its exact zero-clock
principal is concave, but this does not extend to finite clock.

All eighteen higher source rows and all nine curvature drift columns give
the exact terminal identity

    -reducedKineticCurvatureCore(h,9,1/3) = h^4*q(h).

The complete degree20 polynomial q retains all21 monomials. For0<=h<=1,
grouping positive higher powers against negative lower powers proves

    q(h) <= 13688314407775983685466978280013824*(1-14*h)
            -100761203279462102129131923450101760*h^2.

Consequently the entire source has strictly positive second derivative at
v=9,z=1/3 for0<h<=1 and1<=14*h. This is an interval proof, with no sampled
test or external coefficient arithmetic.

The strongest positive survivor is an interior family. For every
1/14<=h<=4/5 there exists delta>0 such that every0<s<delta satisfies, with
b=1/12-7*h/72,

    r=s*(1-h^2*b*s), V=9-r*h^2,
    Z0=(1-h*b*s)/3, z=(1-s)*Z0,
    0<r<361/25, V>0, 0<z<Z0<1/3,
    d²/dz² reducedKineticValue(h,V,z)>0.

Complex nonlinear-boundary incidence is proved. Continuity of the complete
polynomial tensor propagates strict terminal curvature into this interior
family. Antitonicity of the derivative of a concave function then proves
`nonconcave_inside_nonlinear_cone`: the complete source is not concave on
[0,Z0] for all these states. This is a failure inside the admissible cone,
not merely on its r=0 closure. It does not identify these states with the
actual source trajectory or refute source positivity.

Paper proof is dependency-closed. Scratch capstones and exact dominance law
passed `lake --old env lean` with only propext, Classical.choice, Quot.sound.
Production leaves: `ThetaCuspRatioKineticCurvature`,
`ThetaCuspRatioKineticCurvatureControl`,
`ThetaCuspRatioKineticTerminalCurvature`,
`ThetaCuspRatioKineticAxisCurvature`,
`ThetaCuspRatioKineticInteriorCurvature`, and their36 complete source leaves.
Audit manifest: `/tmp/tt_c86_curvature_production_manifest.json`.

Next candidate: direct full-source controls or the exact source-minus-boundary
quotient can retain positivity despite changing curvature. The already-proved
first two source controls remain valid. Full source sign, full source quadratic,
fourth Schur gap, compact join, all-rank closure and RH remain open.

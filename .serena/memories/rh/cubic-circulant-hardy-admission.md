# Literal arithmetic source to cubic Xi index — Lean-closed

2026-09-05. RH goal ACTIVE. No independent arithmetic zero-charge/conservation law proved. Card: docs/drafts/pipeline/1-in-progress/cubic-flat-current-normalization.md. Parent finite algebra/RunPod discriminator: `mem:rh/cubic-circulant-source-normalization`.

Verified/wired leaves (namespace RHTower):
- CubicFiniteChannelHardySource: arbitrary finite PiLp matrix blocks; ordinary matrix CCM cocycle i/(2*pi) integral tr(M N'); genuine rounded cubic with i/(4*pi) current trace.
- CubicCirculantHardyAdmission: literal E(norm z) tensor three-column circulant projections; smooth compact-deviation source admission, flat aggregate/current, exact pointwise recovery before compression.
- CubicCirculantWindingIntegral: actual graph/tensor jets, exact primitives with equal tails, integral tr(S K')=integral f'/f. `exists_faithful_circulant_winding_cubic`: fixed t,b chosen before any f, t²+b²=1,6(tb)²=1,tb≠0; doubled/reversed (labels 0,2,1) genuine projections, nuclear corrections, ordinary cubic trace (2*pi*i)^-1 integral f'/f.
- NEW CubicArithmeticRectangleSource (~420 lines): four smooth stationary ramps traverse bottom/right/top/left positively; exact whole-line-to-rectIntegral substitution. Literal source is `cubicArithmeticRectangleSource z1 z2 x := XiC(cubicSmoothRectangle z1 z2 x)`. No zeros/count/index in this definition.

NEW principal statements:
`cubicSmoothRectangle_integral`: edgewise continuity implies exact rectangle contour transport.
`cubicArithmeticRectangleSource_integral`: existing edge XiExplicitAdmissible hypotheses imply integral f'/f = rectIntegral continuedPrimeArchSourceRelativeTrace; literal fixed prime--Gamma coefficients unchanged.
`cubicArithmeticRectangleSource_winding`: /(2*pi*i) equals cardinality xiZeroCopyClosedRectangle, retaining analytic multiplicity copies.
`exists_faithful_arithmetic_rectangle_cubic`: constants precede all rectangles; genuine 12-channel orthogonal P,Q,R modulo nuclear corrections to doubled Hardy compressions of this same source; exact precompression Xi-value recovery AND nuclear combined cubic C=(R-P)^3-(R-Q)^3-(Q-P)^3 with Tr C=card xiZeroCopyClosedRectangle. No index/trace/budget/RH premise. Recovery is nonlinear pointwise, not bounded inverse or linear prime-label transport after compression.

Verification: full scratch and published arithmetic leaf checks passed, no warnings; 5 axiom audits only propext/Classical.choice/Quot.sound; scoped diff checks passed. No umbrella/full build. All own Lean/lint jobs ended. Latest GLOBAL lint failed solely on concurrent unwired HTGeometry.DispersivePDE.BrizardElasticaFrenetConservation; not changed. No claim global lint clean. Prior winding-leaf lint had passed.

NEXT HARD MATHEMATICS: independent arithmetic property forcing this literal cubic charge to vanish on admissible contours isolating off-critical zeros. Universality of smooth-source admission/recovery/normalization does not supply it. Actual Xi operator/divisor identification is NO LONGER OPEN. Do not re-formalize contour parametrization or polish normalization. This is a standard analytic BRIDGE, not claimed new arithmetic SOTA or RH proof.

Lean pitfalls: explicit Matrix values avoid Pi pointwise multiplication. Complex group-instance diamonds: `convert ... using 1; congr` or `simpa only [...] using!`. Real derivative casts require ((deriv realFunction x : R):C). Real.smoothTransition.contDiff parameter n:NatInfinity differs ambient ContDiff order; use a typed `have hs : ContDiff R infinity ...`. Derivative of transition zero at endpoints via global min/max. ContinuousAt.comp must explicitly specify inner `(f := fun w:R => ...)` or unification picks wrong partial addition. Integral_add hypotheses involving Pi.add need simp only [Pi.add_apply] in intermediate equality before rw. integral_symm a b rewrites integral b..a. Do not simultaneously simp source definition and normalized integral theorem: unfolding denominator prevents matching; rewrite normalization first.

RunPod experiment/report complete; no additional numerical computation needed for this bridge. hgtl7 SKILL.md was renamed during session; existing SKILL.md.bkp.md read completely and workflow retained.
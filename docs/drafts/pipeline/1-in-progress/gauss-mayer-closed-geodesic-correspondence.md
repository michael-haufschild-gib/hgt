# Primitive Mayer cycles and closed modular geodesics

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Parent:** [PM tasks](route-pm-mayer-scattering-and-escape.md), Mayer 1.
- **Inputs:** [integral coding](../3-formalized/gauss-mayer-modular-primitive-coding.md), [translation lengths](../3-formalized/gauss-mayer-hyperbolic-translation-length.md), [inverse orientation](../3-formalized/gauss-mayer-inverse-orientation-multiplicities.md).

## Target

Use the actual modular frame quotient `SL₂(ℤ)\SL₂(ℝ)`, with flow
`[C]↦[C diag(exp(t/2),exp(−t/2))]`. Its primitive periodic flow orbits
should be in bijection with the certified primitive pair cycles. The least
positive period must equal the actual translation length `2 log λ_c`.
Reversing flow orientation must correspond to the certified inverse-cycle
involution, including self-inverse classes.

The geometric lift at frame `C` is `t↦C·(i exp(t))`. Its Poincaré distance
between parameters must be `|t−u|`; thus the flow parameter is geometric
arc length, independent of the symbolic coding.

## Proof obligations

1. Construct the integral left quotient and its right diagonal flow.
2. Identify positive return times with actual integral positive-trace
   hyperbolic matrices conjugate to the real diagonal flow element.
3. Prove the return-time subgroup is discrete. Integrality forces every
   nonzero return matrix to have trace at least three; the trace of the
   diagonal element tends to two at time zero. A nontrivial discrete real
   subgroup has a least positive generator.
4. Identify that generator with an integral primitive root. Existing
   whole-pair root classification then gives least period `2 log λ_c`.
5. Prove phase equivalence of periodic frames exactly matches integral
   conjugacy of primitive return matrices. A real matrix commuting with a
   nontrivial diagonal flow element is diagonal; its two possible signs
   differ by the integral central matrix `−I`.
6. Transfer the existing determinant product along this bijection, retaining
   the exact inverse-orientation multiplicities.

No periodic-flow classification or least-period theorem is assumed. The
independent scattering comparison remains a separate obligation.

For surjectivity, a positive integral return is conjugate to an actual
nonempty pair word. Extract its primitive whole-word root `v` and repetition
`n`. The root's canonical frame returns under the same powered matrix at
time `nL_v`. Positive diagonal return time is determined by trace, since
`x+x⁻¹=y+y⁻¹` with `x,y>1` gives `(x−y)(xy−1)=0`. Equal-return phase
uniqueness then identifies the original geometric orbit with the root's
orbit. This avoids a separate classification of shortest integral returns.

For reversal, use `J=[[0,−1],[1,0]]`. The relation `Ja_t=a_(−t)J`
reverses diagonal time, and a return `γ` becomes `γ⁻¹` at the same positive
time. Since `J²=−I`, reversal squares to the identity on the integral
quotient. The proved inverse-conjugacy criterion and equal-return phase
uniqueness identify this geometric operation with the inverse-cycle map.

## Certified return-time law

`RenormalizedIntersectionTheory/GaussMayerGeodesicFlow.lean` constructs the
actual integral frame quotient and diagonal flow. `isometry_axis` and
`axis_eq_flow_basepoint` identify its unit-speed Poincaré lifts.
`periods_eq_bot_or_positive_lattice` proves, for every frame class `x`,
that its return-time subgroup is either trivial or `Tℤ` for some `T>0`.

For a positive return time `t`, the integral return matrix has trace
`exp(t/2)+exp(−t/2)`. If `0<t<2 log 2`, this trace lies strictly between
two and three, contradicting integrality. Hence the period subgroup is
not dense. The real subgroup dichotomy gives the cyclic lattice, whose
generator can be chosen positive. The direct Lean check and all nine
transitive axiom audits passed with only the standard three axioms.

`GaussMayerGeodesicCentralizer.common_return_phase` proves that two real
frames with the same nonzero integral return lie on the same modular flow
orbit. Their relative frame centralizes a nontrivial diagonal element,
so is a diagonal time or its negative; the integral central element `−I`
removes the sign. The centralizer module passed its direct check and seven
standard-axiom audits.

`GaussMayerPrimitiveGeodesicReturns.cycleFrame_periods` proves that every
primitive cycle has an actual modular eigenframe whose return group is
exactly `L_cℤ`; `cycleFrame_least_period` identifies `L_c` as its least
positive return. The explicit determinant-one eigenbasis supplies the
return at `L_c=2 log λ_c`. If the positive period generator were `T` with
`L_c=nT` and `n>1`, its integral return matrix would be an `n`th root of
the actual cycle matrix, contradicting the proved whole-pair root
classification. The direct check and seven standard-axiom audits passed.

Integral conjugacy of flow orbits, surjectivity onto all periodic orbits,
geometric orientation reversal, and the geodesic-indexed determinant
product remain to be formalized.

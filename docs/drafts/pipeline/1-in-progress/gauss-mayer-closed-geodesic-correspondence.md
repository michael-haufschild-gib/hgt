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

Primitive-return classification, integral conjugacy of flow orbits, the cycle
bijection, and the geodesic-indexed determinant product remain to be formalized.

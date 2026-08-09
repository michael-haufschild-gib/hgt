# Formalization progress — noncommuting-exactification-geometry

Tracking file for the 2 -> 3 gate of the six cards in this folder.  Lean modules live in
`formal/GaloisForLFunctions/HTGeometry/` unless noted.

## Card 3 — constraint-laplacian-uncertainty-and-capacity-horizon

| Card item | Lean module | Status |
|---|---|---|
| infrastructure: Hilbert closed-range theorem | `HilbertClosedRange.lean` | built |
| §2 constraint Laplacian, §3 Thm 3.1 (1)(2)(3) | `ConstraintLaplacian.lean` | built |
| §4 Thm 4.1 (4.2)(4.3)(4.4) | `FriedrichsAngle.lean` | built |
| §4 Thm 4.1 (4.5) closed sum | `FriedrichsClosedSum.lean` | built |
| §5 Prop 5.1, Prop 5.2 | `ExchangeCurvature.lean` | built |
| §6 (exposition, no numbered theorem) | — | not required by the gate |
| §7 Thm 7.1, Example 7.2 | `NestedConvexCapacity.lean` | built |

## Card 5 — source-observer-hodge-curvature-and-subunit-annihilation-law

| Card item | Lean module | Status |
|---|---|---|
| §2 Thm 2.1, §3 Cor 3.1-3.4, sharpness, §4 Thm 4.1 | `SourceObserverHodgeCurvature.lean` | built |

## Card 1 — observer-horizon-stability-under-bounded-and-compact-repair

| Card item | Lean module | Status |
|---|---|---|
| §2 Thm 2.1 graph shear + horizon invariance | `ObserverHorizonStability.lean` | built |
| §3 Thm 3.1 bounded positive form correction | `ObserverHorizonStability.lean` | built |
| §4 Thm 4.1 compact stability of a weakly-null singular sequence | `ObserverHorizonStability.lean` | built |
## Card 2 — affine-observer-holonomy-and-global-section-law — TODO
## Card 4 — finite-jet-indistinguishability-and-clock-covariance — TODO

Corpus assets found: `hypertranscendental_gamma` (Hölder), `hypertranscendental_gamma_add_const`,
`differentiallyAlgebraic_add_polynomial(_iff)`, `differentiallyAlgebraic_add/sub/mul/pow`,
`hypertranscendentalOver_inv_iff`, `differentiallyAlgebraicOfOrder_zero_of_polynomial`,
`DifferentiallyAlgebraicNear`/`HypertranscendentalNear`.
## Card 6 — two-prime-kummer-precision-horizon-and-compact-repair-no-go — IN PROGRESS

Plan: `HTGeometry/FiniteDiagonalOperator.lean` (general finite diagonal multiplier: smallest
singular value, normal operator, inverse norm, approximate-inverse bound) then
`RHTower/TwoPrimeKummerPrecisionHorizon.lean` (arithmetic clock separation `d_N`, the elementary
window `3^{-N} ≤ d_N ≤ log 2 / ⌊N/2⌋`, spectrum, and the compact-repair no-go via
`ObserverHorizonStability.not_injective_and_isClosed_range_of_weaklyNull`).

## Rules in force
- foreground `lake env lean <file>` only, one process at a time; `lake build <module>` to
  produce oleans for downstream modules.
- background lean runs get killed and report false "clean" results — never trust them.
- umbrella wiring (`HTGeometry.lean`) must be updated before the final audit.

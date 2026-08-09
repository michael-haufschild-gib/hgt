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
## Card 2 — affine-observer-holonomy-and-global-section-law

| Card item | Lean module | Status |
|---|---|---|
| §2 tree gauge, §3 Thm 3.1 | `AffineObserverHolonomy.lean` | built |
| §4 Thm 4.1, §5 Cor 5.1, §6 Prop 6.1, §8 Thm 8.1 + Cor 8.2 | `ObserverFieldEquation.lean` | built |
| §7 Prop 7.1 (1) and (3) | `HolonomyGeneratingSet.lean` | built |

§7(2) (conjugacy of based holonomy groups under change of root) is the gauge covariance
`gaugeHolonomy`/`exact_gauge_iff` of `ObserverFieldEquation.lean` applied to the root transport.
## Card 4 — finite-jet-indistinguishability-and-clock-covariance — IN PROGRESS

| Card item | Lean module | Status |
|---|---|---|
| invertible triangular variable substitution | `TriangularSubstitution.lean` | built |
| §3 Thm 3.1 (3.1), (3.2) and the clock invariance of hypertranscendence | `ClockChangeTriangular.lean` | built |
| §3 Cor 3.2 differential-birational generator covariance | — | TODO |
| §4 Thm 4.1, Cor 4.2, Cor 4.3 | — | TODO |
| §5 Prop 5.1 source-dependent trivialization | — | TODO |

Corpus assets found: `hypertranscendental_gamma` (Hölder), `hypertranscendental_gamma_add_const`,
`differentiallyAlgebraic_add_polynomial(_iff)`, `differentiallyAlgebraic_add/sub/mul/pow`,
`hypertranscendentalOver_inv_iff`, `differentiallyAlgebraicOfOrder_zero_of_polynomial`,
`DifferentiallyAlgebraicNear`/`HypertranscendentalNear`.
## Card 6 — two-prime-kummer-precision-horizon-and-compact-repair-no-go

| Card item | Lean module | Status |
|---|---|---|
| general finite diagonal multiplier | `HTGeometry/FiniteDiagonalOperator.lean` | built |
| arithmetic clock separation, elementary window, injective mode families | `RHTower/TwoPrimeKummerClockSeparation.lean` | built |
| §2 Thm 2.1, §3 Thm 3.1, §4 Thm 4.1 | `RHTower/TwoPrimeKummerPrecisionHorizon.lean` | built |
| general `ℓ²` multiplier spectrum and Weyl sequences | `RHTower/DiagonalMultiplierSpectrum.lean` | built |
| §5 Thm 5.1, §6 Thm 6.1 | `RHTower/TwoPrimeKummerEssentialSpectrum.lean` | built |

## Rules in force
- foreground `lake env lean <file>` only, one process at a time; `lake build <module>` to
  produce oleans for downstream modules.
- background lean runs get killed and report false "clean" results — never trust them.
- umbrella wiring (`HTGeometry.lean`) must be updated before the final audit.

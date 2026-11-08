# Whole-space critical threshold versus the onset aperture

- **ID:** cact-whole-space-threshold-onset
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Obstacles summary §3](../../../reports/review-0611/obstacles-summary.md), “The one question”.
- **Statement:** `criticalPositivityThreshold = criticalNonnegativityThreshold = polarPaymentCriticalThreshold`; for universal `c₁,c₂>0` and every finite `0≤a≤onsetAperture zetaZeroConfig`, `c₁ exp(c₂a) ≤ criticalPositivityThreshold`.

## Exact conclusions

Fix `φ=tiltedUnitSpline` and put `a* = onsetAperture zetaZeroConfig`. Let `R_c`, `R_c^{nn}`, `R_c^{polar}`, `R_c^⊥`,
and `R_c^{high}` denote the whole-space
positivity, nonnegativity, polar-payment, primitive, and high-conductor thresholds. Then

```
0 < R_c = R_c^{nn} = R_c^{polar}
        ≤ R_c^⊥ = R_c^{high} = inf_{A≥0} windowThreshold A.
```

For universal `c₀,c₁,c₂>0` and every finite `0≤a≤a*`,
`R_c≥c₁ exp(c₂a)` and `R_c^⊥≥c₀ exp(6a)`.
If the corresponding threshold is finite, its logarithm is at least
`log c₁+c₂a` or `log c₀+6a`, respectively.
All five thresholds are infinite iff `a*=∞` iff RH.
The whole-space exponent is the proved polar-payment constant `c₂`; no specific value is asserted.

## Proof

1. Split a nonpositive direction into its low conductor packet and three complement bands.
   Nonpolar dual-seventh cancellation and adjustable Schur payment absorb every discarded
   cross term with arbitrarily small relative packet loss. The comparison retains the
   **actual** pole diagonal and signed polar collar pairing.
2. Put `J=‖U‖₂²+b₁²/log N`. Collar Gårding makes `J>0`; division by `√J` gives a collar
   and pole coordinate with `‖U‖₂²+β²=1`, bounded eighth exponential mass, bounded Weil form,
   and bounded discrete seventh mass. Strong compactness preserves this joint normalization.
3. On every fixed terminal fraction, the normalized polar matrix row converges in sampled
   square mean to
   `aφ√x[1/x−½log(1−x²)−ψ(1/x)−log(2π)]`, where `aφ=(∫φ)²/∫φ²`, `ψ(y)=Σ_{1≤k≤⌊y⌋}Λ(k)`, and `x=n/N`,
   with the convention `log 0=0` at `x=1`.
   Exact harmonic coordinates and annular Gamma quadrature give the interior limit.
   Squared-log endpoint tails and finite-jump ramps give compact Lipschitz approximation.
4. The rough Weil bound first gives a finite Gamma bound for the limit. A lower logarithmic
   cutoff costs arbitrarily little dual seventh mass. Weighted
   Cauchy–Schwarz and adjoint synthesis therefore approximate the polar functional uniformly
   on bounded collar balls. Fixed-window limits identify the same compact tests with the
   signed physical source. One-sided mollification and weighted source continuity extend
   that identification to the strong limit profile.
5. The critical Gamma lower bound and exact pole cost pass the charged nonpositivity
   inequality to the limit. Payment at `S>R>0` leaves a positive eighth-mass and pole-square
   reserve at `R`, contradicting unit joint mass. Thus every critical curve below a paying
   ratio is eventually positive. Compact-band lifting and suprema give
   `R_c^{polar}≤R_c`; the already proved necessity gives equality. The nonnegativity identity,
   exponential/logarithmic bounds, and infinite-threshold equivalences follow.

## Lean declarations

Paths below are relative to `formal/GaloisForLFunctions/`; `AHD` abbreviates
`ArithmeticHodgeTheoryOfDegenerations`, `CACT` abbreviates `CriticalArithmeticCorrelationTheory`.

| Result | Module / declarations |
|---|---|
| Arbitrarily small packet loss | `CACT/AdaptiveLowPacketSchurPayments`: `eventually_lowPacket_cross_sub_polar_le` |
| Exact charged finite comparison | `CACT/WholeSpaceGardingRetainsThePolarChannel`, `CACT/NonpositiveDirectionsHaveChargedCompactCollarProfiles` |
| Joint normalization and compactness | `AHD/NonpositiveDirectionsHaveNormalizedChargedProfiles`, `AHD/ChargedWeilProfilesHaveStrongLimits` |
| Explicit strong polar row | `AHD/ThePolarMatrixRowHasItsStrongProfile`: `tendsto_topWindow_polar_matrix_profile`, `tendsto_topWindow_polar_residual_profile` |
| Uniform physical transfer and signed limit | `AHD/PolarModeTopWindowLipschitzTransfer`: `exists_uniform_polar_window_L2_transfer`, `tendsto_polar_residual_pairing_of_strong_limit` |
| Charged limit exclusion | `AHD/PolarPaymentExcludesChargedLimitProfiles`: `no_charged_limit_profile_below_polarPayment` |
| Whole-space threshold equality | `AHD/WholeSpaceCriticalThresholdEqualsPolarThreshold`: `criticalPositivityThreshold_eq_polarPaymentCriticalThreshold`, `criticalNonnegativityThreshold_eq_polarPaymentCriticalThreshold` |
| Exponential/logarithmic bounds and equivalences | Same module: `exp_mul_le_criticalPositivityThreshold`, `log_criticalPositivityThreshold_ge_mul_onsetAperture`, `criticalThresholds_eq_top_equivalences` |
| Primitive threshold and sixth-exponential bound | `AHD/PrimitiveCriticalThresholdEqualsWindowThreshold` |

Transitive axiom audits: `propext, Classical.choice, Quot.sound` only.

## Boundary retained

Unrestricted atomic Gårding fails; collar restriction is essential. The positive survivor is
whole-space collar Gårding with scalar polar loss and terminal-window length
`A≤¼log(R+1)+C`. Formalization: `CACT/UnrestrictedAtomicGardingFailsAndCollarGardingHolds`,
`CACT/WholeSpaceCollarGarding`.

Companion: [prefix–collar decoupling and thresholds](critical-ratio-window-confinement-and-threshold-law.md).

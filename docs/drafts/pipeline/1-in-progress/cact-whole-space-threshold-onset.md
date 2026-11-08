# Whole-space critical threshold versus the onset aperture

- **ID:** cact-whole-space-threshold-onset
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (Part A) · THEOREM (Lean) for the finished parts
- **Source:** [Obstacles summary §3](../../../reports/review-0611/obstacles-summary.md), "The one question"
- **Statement:** `log R_c(ζ) ≥ c·a*(ζ) − C`, where `R_c(ζ) = criticalPositivityThreshold`.

## Goal
Answer §3: the whole-space critical threshold grows exponentially in the onset aperture
`a* = onsetAperture ζ`.

## Proved (Lean, axioms `propext, Classical.choice, Quot.sound`)
| Fact | Lean |
|---|---|
| Unrestricted atomic Gårding (A10 as stated) fails at every `R > 0`; top-collar Gårding holds | `CACT/UnrestrictedAtomicGardingFailsAndCollarGardingHolds` |
| Nonpositive directions cannot escape the top window of length `(1/8)log(R+1)+C₀` | `CACT/NegativeDirectionsCannotEscapeLogarithmicWindows` |
| `⨅_A R₁(A) ≥ c₀ e^{6a*}` | `AHD/TheContinuumWindowThresholdGrowsExponentially` |
| `R_c^{high} = ⨅_A R₁(A)`, `log R_c^{high} ≥ 6a* + log c₀`; `R_c = ⊤ ⇔ a* = ⊤ ⇔ RH` | `AHD/TheCriticalPositivityThresholdLaw` |
| `e^{−s}D(s) − κ₀ = −2e^{−s}Φ(2s) − 2e^{−2s}(log 2π − S) + r/e^s` (exact) | `poleDiagonalExplicit_div_exp_sub_sharp_eq` |
| Depth `≥ ¼` excluded up to height `exp(a/K)` under window positivity at `a` | `exists_abs_re_sub_half_lt_quarter_of_hodgeIndex` |
| `|Φ(L)| ≤ C e^{L/4}` for `K(L+2) ≤ a*`; Mertens lag `≤ C e^{−L/4}` | `exists_abs_weilLagFunctionReal_le_of_zetaWindowPositive`, `exists_abs_mertensLagPrimitive_le_of_zetaWindowPositive` |
| `|e^{−s}D(s) − κ₀| ≤ C e^{−s/2}` for `K(2s+2) ≤ a*` | `exists_abs_poleDiagonal_sharp_of_le_onsetAperture` (`AHD/ThePoleSelfEnergyIsSharpBelowTheOnset`) |
| B1–B3: `PolarPaymentAt R A` for all `A ≥ 0` and all `0 < R ≤ c₁ e^{c₂ a}`, `0 ≤ a ≤ a*` | `exists_polarPaymentAt_exp_of_le_onsetAperture` (`AHD/PolarPaymentGrowsExponentiallyBelowTheOnset`) |
| `R_c ≤ R_c^{nn} ≤ R_c^{polar} ≤ R_c^{high}`; `R_c^{polar} = ⊤ ⇔ RH` | `criticalThreshold_hierarchy` (`AHD/PolarPaymentThresholdHierarchy`) |
| `R_c^{polar} ≥ c₁ e^{c₂ a*}`, `log R_c^{polar} ≥ c₂ a* + log c₁` | `exp_mul_le_polarPaymentCriticalThreshold`, `log_polarPaymentCriticalThreshold_ge_mul_onsetAperture` (`AHD/PolarPaymentThresholdGrowsExponentially`) |

## Open steps
- **A (threshold identity):** `R_c = R_c^{polar}`, i.e. `PolarPaymentAt R₁ A` for all `A ≥ 0` implies
  `EventuallyCriticalPosDef R` for `R < R₁`. Necessity is `polarPaymentAt_of_eventually_nonneg`.
  Sufficiency: retain the exact pole energy and normalize by `‖U_w‖₂² + β² = 1`,
  where `β = b₁/√(log N)`. Collar Gårding gives compactness; polar payment at a larger
  ratio supplies a strict positive reserve in both limit coordinates. **Gap:** uniform
  convergence of the polar cross term along an arbitrary bad sequence. Lean has the limit
  `√L/c ⟪B v_m, ·⟫ → S(h)` (`m = 1`) or `→ 0` (`m ≥ 2`) only on window vectors
  `horizonProfileVector (horizonWeights h N) N` (`tendsto_complete_terminal_pole`,
  `tendsto_complete_terminal_nonpolar`); the nonpolar `D₇` Schur cost now vanishes (below). The polar functional still needs uniform transfer.
  Needed: a bound `|√L/c ⟪B v_m, z⟫| ≤ C_m (‖U_w‖₂ + W₈(U_w)^{1/2}) + o(1)·reserves(z)` uniform
  in `N` and `z ∈ V_Q^⊥`, so that window-vector limits transfer to strong `L²` limits of collar
  profiles.

## Collar cancellation (Lean)
For each fixed `m ≥ 2` on every positive critical curve,
`(log N / c_N²) D₇(N / linearDefectCutoff c_N, N; r_m) → 0`.
Splitting at `⌊δN⌋` bounds the lower piece by `O_m(δ)` and the upper piece by the
vanishing top-window norm. Finite-conductor tail reduction gives
`(c_N⁷ / log N) Σ_{2≤m≤Q₁} D₇(r_m)/E_m(c_N) → 0`, uniformly on positive compact
critical bands.

Lean (`CACT/NonpolarCollarResidualsVanish.lean`): `tendsto_nonpolar_collar_dualSeventh`,
`tendsto_nonpolar_lowPacket_collar_schur_cost`,
`eventually_uniform_nonpolar_lowPacket_collar_schur_cost` (CACT namespace).
Axioms: `propext, Classical.choice, Quot.sound`.

Deep inverse-energy residuals tend to zero at every critical ratio; the first band,
second band, and far prefix can therefore be paid while retaining the exact collar cost.
Lean: `eventually_critical_deep_residual_le`,
`eventually_critical_schur_pairing_except_collar` in `AllRatioDeepConductorPairings`.
Axioms: `propext, Classical.choice, Quot.sound`.

Whole-space Gårding now retains the packet diagonal, prefix, seventh-mass, eighth-mass,
and Lévy reserves with sole scalar loss `C c b₁² / log N`. Its mass term localizes to
`(-A, 1]`, where `A ≤ ¼ log(R + 1) + C_len`. On the primitive hyperplane the scalar loss
is absorbed, and the same far component has an arbitrarily accurate energy bridge.
Lean: `exists_wholeSpace_window_localized_collar_garding`,
`exists_critical_primitive_collar_garding_and_far_bridge` in `CACT/WholeSpaceCollarGarding`.
Axioms: `propext, Classical.choice, Quot.sound`.

## Polar transfer: remaining lemma
For each fixed `0 < δ < 1`, approximate the normalized conductor-one row on
`δN < n ≤ N` in `ℓ²` by sampled Lipschitz functions of `log(n/N)`.
The limiting kernel has a logarithmic singularity at `n/N = 1` and finitely many
prime jumps on this interval. Required estimates: interior row convergence,
uniform squared-log endpoint tails, and negligible neighborhoods of the jumps.
The existing adjoint synthesis estimate
`abs_integral_normalizedCentredAtomicTest_mul_sub_le` then transfers samples to
physical profiles. The collar seventh-mass reserve bounds coefficient `ℓ²`
after profile normalization, so a static arbitrarily accurate approximation suffices.
This row approximation and its application to polar threshold sufficiency remain unproved.

### Strong polar profile (conjecture)

Put `aφ = (∫φ)²/∫φ²`, `x = n/N`, and `ψ(y) = Σ_{k≤⌊y⌋} Λ(k)`.
On every fixed `δ < x ≤ 1`, the target is normalized square-mean convergence of
`√(N log N) (B_{c,N}v₁)_n / c` to
`aφ √x [1/x − ½ log(1−x²) − ψ(1/x) − log(2π)]`.

The near Gram identity cancels the `log c` and `log x` terms. Fixed far annuli
have row-independent means, with a remaining `O(1/T)` tail. The existing
`tendsto_joint_near_far_Gamma_integral` identifies their combined constant as
`−aφ log(2π)` after adding the harmonic collar constant.

Verified bricks: closed-annulus quadrature with `O(1/n)` error and terminal-strip
square-mean control (`LogarithmicAnnuliHaveUniformRowMeans`); summable squared-log
center tails and scaled Gram-defect decay (`PolarRowsHaveSummableTerminalTails`).
Full center-profile square-mean convergence is verified in
`ThePolarCenterRowHasItsStrongProfile`. Near-collar harmonic comparison, the sampled
Mangoldt row, and assembly of the full strong profile still require verification. Endpoint ramp multiplication and finite
jump ramps reduce Lipschitz approximation to compact-interval polynomial density.
The sampled finite-jump ramp estimate and compact smooth Lipschitz density have clean
Lean axiom audits (`SampledJumpsAdmitLipschitzApproximation`,
`ContinuousWindowsAdmitCompactLipschitzApproximation`).

## Verified scalar identification

If `x_N` is arbitrarily close to the line spanned by bounded vectors `v_N`, and bounded
tests `h_N` satisfy `⟨v_N,h_N⟩ ≥ a > 0`, then
`⟨x_N,h_N⟩ − s⟨v_N,h_N⟩ → 0` implies `‖x_N − s v_N‖ → 0`.
This holds for varying Hilbert spaces. Lean: `PolarRowScalarIsFixedByOneWindow`;
axioms `propext, Classical.choice, Quot.sound`.

## Source continuity

The physical polar source is `e^(−u/2) terminalPolarKernel(u)` on `u ≤ 0`.
Its dual exponential norm is `∫_{u≤0} e^u terminalPolarKernel(u)² du`.
Deep kernel boundedness and a squared-logarithm terminal majorant make this finite.
Combined with the existing `tendsto_exponentialSourceMass_sub`, Cauchy–Schwarz
then transfers polar source pairings through strong `L²` limits with bounded eighth mass.
The kernel estimate and source-continuity formalizations are drafted, not yet checked.

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
  Sufficiency: Schur-complete the low packet, `E(x) ≥ E(z) − Σ_{m≤Q} ⟪r_m, z⟫²/d_m` for
  `z = P_{V_Q^⊥} x`; run the compactness of `eventuallyHighConductorPosDef_of_lt_iInf_windowThreshold`
  on `z`. **Gap:** the limit of the Schur terms along an arbitrary bad sequence. Lean has the limit
  `√L/c ⟪B v_m, ·⟫ → S(h)` (`m = 1`) or `→ 0` (`m ≥ 2`) only on window vectors
  `horizonProfileVector (horizonWeights h N) N` (`tendsto_complete_terminal_pole`,
  `tendsto_complete_terminal_nonpolar`); the crude `D₇` bound leaves `O(R²/m⁵)` for `m ≤ m₀(R)`.
  Needed: a bound `|√L/c ⟪B v_m, z⟫| ≤ C_m (‖U_w‖₂ + W₈(U_w)^{1/2}) + o(1)·reserves(z)` uniform
  in `N` and `z ∈ V_Q^⊥`, so that window-vector limits transfer to strong `L²` limits of collar
  profiles.

## Log
- 2026-11-07 — card created; sharp pole self-energy below the onset formalized.
- 2026-11-07 — B1–B3 formalized; Part A gap isolated (uniform pole-pairing bound).

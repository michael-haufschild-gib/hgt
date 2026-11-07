# Whole-space critical threshold versus the onset aperture

- **ID:** cact-whole-space-threshold-onset
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (Part A, Part B3) · THEOREM (Lean) for the finished parts
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

## Open steps
- **A (threshold identity):** `R_c = sup{R : ∀A, PolarPaymentAt R A}`. Necessity is
  `polarPaymentAt_of_eventually_nonneg`. Sufficiency: Schur-complete the low packet; modes
  `m ≥ 2` and `c < m ≤ Q` are `o(c)‖w_top‖²`, absorbed by the `S₇` reserve; mode `1` converges to
  `S_polar(U_top)`; compactness as in `TheCriticalPositivityThresholdLaw`.
- **B1 (2×2 pole compression):** window positivity at `s ≤ a*` gives
  `|Q_s(u_pole, f)|² ≤ D(s) Q_s(f)` (Cauchy–Schwarz for `ccmRestrictedWeilSourceQuadratic ≥ 0`).
- **B2 (deep/top split):** cut `H` at `−a/4`; the deep part has `S(h_deep)² ≲ e^{−7a/2}M₈(H)`.
- **B3 (bridge):** identify `generalTerminalPolarSource A h_top` with the CCM cross pairing
  `Q_s(u_pole, f)` up to `O(e^{−cs})M₈^{1/2}`. Then B1 + sharp `D(s)` give
  `S²/D(R) ≤ a_φQ + (7J/R)M₈` for `R ≤ c e^{c a*}`.

## Log
- 2026-11-07 — card created; sharp pole self-energy below the onset formalized.

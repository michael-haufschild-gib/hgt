import GaloisForLFunctions.RHTower.ZetaGateRectangleLeftLine
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.RHTower.ZetaVerticalMeanSquare

set_option autoImplicit false

/-!
# Strip bounds for `ζ` and `χ` supplied to conditional window and edge estimates

* The horizontal-edge bounds of the dual-diagonal integrand take a `χ` decay constant on
  `1/2 ≤ σ ≤ 6/5` and a polynomial `ζ` bound on `|σ| ≤ 3`;
  `exists_norm_zetaChi_le_of_two_le_abs` and `exists_bound_norm_riemannZeta_strip 3` prove both.
* The vertical mean-square window bound takes the critical-line second moment and linear growth of
  the pole-cleared `ζ` on `1/2 ≤ σ ≤ 3`; `exists_integral_normSq_zeta_critical_le` and
  `exists_norm_zetaPoleCleared_le` prove both.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower.ZetaGateProductAFE

open RHTower

/-- Pointwise bound on the horizontal edges `Im s = ±|τ|/2`, `-7/10 ≤ Re s ≤ -1/4`. -/
theorem norm_dualDiagonalIntegrand_horizontal_rect_le_uniform :
    ∃ (CA Cζ : ℝ) (N : ℕ), 0 ≤ CA ∧ 0 ≤ Cζ ∧
      ∀ d c x τ : ℝ, 0 < d → d ≤ 1 / 20 → 0 < c → 0 < x → 1 ≤ c * x → 4 ≤ |τ| →
      ∀ u : ℝ, -(7 / 10) ≤ u → u ≤ -(1 / 4) → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
        ‖dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I)‖
          ≤ (CA * CA * Cζ * Real.exp 1) * (c * x) ^ (7 / 10 : ℝ)
              * (|τ| ^ N * Real.exp (-((|τ| / 2) ^ 2))) := by
  obtain ⟨CA, hCA, hA⟩ := exists_norm_zetaChi_le_of_two_le_abs
  obtain ⟨Cζ, N, hCζ, hζ⟩ := exists_bound_norm_riemannZeta_strip 3
  exact ⟨CA, Cζ, N, hCA, hCζ, fun d c x τ hd hd20 hc hx hcx hτ u hu1 hu2 ε hε =>
    norm_dualDiagonalIntegrand_horizontal_rect_le hd hd20 hc hx hcx hCA hA hζ hτ hu1 hu2 hε⟩

/-- Integrated bound on the horizontal edges, with `(1 + |τ|)^{-2}` decay. -/
theorem norm_intervalIntegral_dualDiagonalIntegrand_horizontal_rect_le_uniform :
    ∃ (CA Cζ : ℝ) (N : ℕ), 0 ≤ CA ∧ 0 ≤ Cζ ∧
      ∀ d c x τ : ℝ, 0 < d → d ≤ 1 / 20 → 0 < c → 0 < x → 1 ≤ c * x → 4 ≤ |τ| →
      ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
        ‖∫ u : ℝ in (-(7 / 10) : ℝ)..(-(1 / 4) : ℝ),
            dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I)‖
          ≤ (CA * CA * Cζ * Real.exp 1) * (c * x) ^ (7 / 10 : ℝ)
              * (((N + 2).factorial * Real.exp 2) * (1 + |τ|) ^ (-(2 : ℝ))) * (9 / 20) := by
  obtain ⟨CA, hCA, hA⟩ := exists_norm_zetaChi_le_of_two_le_abs
  obtain ⟨Cζ, N, hCζ, hζ⟩ := exists_bound_norm_riemannZeta_strip 3
  exact ⟨CA, Cζ, N, hCA, hCζ, fun d c x τ hd hd20 hc hx hcx hτ ε hε =>
    norm_intervalIntegral_dualDiagonalIntegrand_horizontal_rect_le hd hd20 hc hx hcx hCA hCζ hA
      hζ hτ hε⟩

end RHTower.ZetaGateProductAFE

namespace RHTower

/-- The window mean-square bound for `ζ` on `σ + i[T, 2T]`, `1/2 ≤ σ ≤ 3`, with the critical-line
second-moment constant and the pole-cleared growth constant supplied. -/
theorem integral_normSq_zeta_vertical_le_window_uniform :
    ∃ D Cg : ℝ, 0 ≤ D ∧ 0 < Cg ∧ ∀ T σ : ℝ, 2 ≤ T → 1 / 2 ≤ σ → σ ≤ 3 → ∀ N : ℕ,
      16 * T * (1 + Real.log T) ≤ N → 4 ≤ N →
      ∫ t in T..(2 * T), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        5 * ((Real.exp 1 * (D * N * (1 + Real.log N) ^ 2) + T * (Real.exp 1 * (64
            * Real.exp (-(((N : ℝ) - 3 * T / 2) ^ 2 / (8 * T) ^ 2))
            * (2 * (1 + 3 * T / 2) ^ 2 + 2 * (8 * T) ^ 2))))
          + 4 * Real.exp 1 ^ 2 * Real.sqrt (Real.pi / (2 / (8 * T) ^ 2))) := by
  obtain ⟨D, hD, hcrit⟩ := exists_integral_normSq_zeta_critical_le
  obtain ⟨Cg, hCg, hgrowth⟩ := exists_norm_zetaPoleCleared_le
  exact ⟨D, Cg, hD, hCg, fun T σ hT hσ hσ3 N hN1 hN4 =>
    integral_normSq_zeta_vertical_le_window hD hCg hcrit hgrowth hT hσ hσ3 hN1 hN4⟩

end RHTower

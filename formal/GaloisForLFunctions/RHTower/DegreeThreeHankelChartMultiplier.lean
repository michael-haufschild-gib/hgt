import GaloisForLFunctions.RHTower.DegreeThreeHankelTwistSymbolBound
import GaloisForLFunctions.RHTower.GammaRCubeVoronoiL2

/-!
# The chart multiplier of `ζ(s)³`'s Voronoi transform

In the cube-root chart `X = √3 x^{1/3}`, the Voronoi transform of `Γℝ(s)³` has Mellin multiplier
`m̃(u) = 3^{u-1/2} Γℝ((u+1)/3)³ / Γℝ((2-u)/3)³`. Two facts drive the Kulikov–Nazarov–Sodin
sampling argument:

* **Derivative bound.** On `Re u = -1/2`, `|u m̃(u)| ≤ 2πκ` with `κ = sup |v(3/2 + it)|`
  (`exists_bound_mul_chartMultiplier_neg_half`). It combines the factorization
  `m̃(u) = Γℝ(u+1)/Γℝ(2-u) · v(1-u)` with `|u Γℝ(u+1)/Γℝ(2-u)| = 2π` on that line, which follows
  from `Γℝ(z+2) = z Γℝ(z)/(2π)` and `Γℝ(z̄) = conj Γℝ(z)`.
* **Antisymmetry in the chart.** If `Ψ(s) = -G(s) Ψ(1-s)`, the chart symbol
  `Φ(w) = 3^{w/2-3/4} Ψ((w+1)/3)` satisfies `Φ(w) = -m̃(w) Φ(1-w)` (`chartSymbol_antisymm`).

Together with Mellin–Plancherel, these give `‖F'‖ ≤ 2πκ ‖XF‖` for antisymmetric chart functions.
-/

open Complex

noncomputable section

namespace RHTower.DegreeThreeHankel

/-- The Mellin multiplier of `ζ(s)³`'s Voronoi transform in the cube-root chart:
`m̃(u) = 3^{u-1/2} Γℝ((u+1)/3)³ / Γℝ((2-u)/3)³`. -/
def chartMultiplier (u : ℂ) : ℂ :=
  (3 : ℂ) ^ (u - 1 / 2) * (Gammaℝ ((u + 1) / 3) ^ 3 * (Gammaℝ ((2 - u) / 3) ^ 3)⁻¹)

/-- `|u Γℝ(u+1)/Γℝ(2-u)| = 2π` on `Re u = -1/2` (the derivative identity of the sine transform). -/
theorem norm_mul_sineMultiplier_neg_half (t : ℝ) :
    ‖((-1 / 2 : ℂ) + t * I) * (Gammaℝ ((-1 / 2 : ℂ) + t * I + 1) *
      (Gammaℝ (2 - ((-1 / 2 : ℂ) + t * I)))⁻¹)‖ = 2 * Real.pi := by
  set z : ℂ := (1 / 2 : ℂ) - t * I with hz
  have hz0 : z ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hz] at this
  have e1 : (-1 / 2 : ℂ) + t * I + 1 = (starRingEnd ℂ) z := by
    rw [hz]; simp only [map_sub, map_div₀, map_one, map_ofNat, map_mul, Complex.conj_ofReal,
      Complex.conj_I]; ring
  have e2 : 2 - ((-1 / 2 : ℂ) + t * I) = z + 2 := by rw [hz]; ring
  have e3 : (-1 / 2 : ℂ) + t * I = -z := by rw [hz]; ring
  have hG : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hz]; simp)
  rw [e1, e2, e3, Complex.Gammaℝ_add_two hz0, RHTower.gammaR_conj]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsimp : -z * ((starRingEnd ℂ) (Gammaℝ z) * (Gammaℝ z * z / 2 / (Real.pi : ℂ))⁻¹)
      = -(2 * (Real.pi : ℂ)) * ((starRingEnd ℂ) (Gammaℝ z) / Gammaℝ z) := by
    field_simp
  rw [hsimp, norm_mul, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hG), norm_neg]
  simp [abs_of_pos Real.pi_pos]

/-- **Derivative bound in the chart.** On `Re u = -1/2`, `|u m̃(u)| ≤ 2π κ` with
`κ = sup |twistSymbol(3/2 + it)|`. -/
theorem exists_bound_mul_chartMultiplier_neg_half :
    ∃ K : ℝ, ∀ t : ℝ, ‖((-1 / 2 : ℂ) + t * I) * chartMultiplier ((-1 / 2 : ℂ) + t * I)‖ ≤ K := by
  obtain ⟨κ, hκ⟩ := exists_bound_twistSymbol_three_halves
  refine ⟨2 * Real.pi * κ, fun t => ?_⟩
  have hre1 : -1 < ((-1 / 2 : ℂ) + t * I).re := by simp; norm_num
  have hre2 : ((-1 / 2 : ℂ) + t * I).re < 2 := by simp; norm_num
  have hfac := voronoi_multiplier_eq_sine_mul_twist hre1 hre2
  unfold chartMultiplier
  rw [show (((-1 / 2 : ℂ) + t * I) + 1) / 3 = ((-1 / 2 : ℂ) + t * I + 1) / 3 by ring] at hfac ⊢
  rw [hfac, ← mul_assoc, norm_mul]
  have h1 := norm_mul_sineMultiplier_neg_half t
  have h2 : 1 - ((-1 / 2 : ℂ) + t * I) = 3 / 2 + (-t : ℝ) * I := by push_cast; ring
  rw [h2]
  have h3 := hκ (-t)
  rw [h1]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

/-- The chart symbol of a Mellin symbol `Ψ`: `Φ(w) = 3^{w/2 - 3/4} Ψ((w+1)/3)`, the Mellin transform
of `3^{-1/4} X f(X³/(3√3))` when `Ψ` is the Mellin transform of `f`. -/
def chartSymbol (Ψ : ℂ → ℂ) (w : ℂ) : ℂ := (3 : ℂ) ^ (w / 2 - 3 / 4) * Ψ ((w + 1) / 3)

/-- Antisymmetry transfers to the chart: if `Ψ(s) = -G(s) Ψ(1-s)` with `G = Γℝ³/Γℝ(1-·)³`, then
`Φ(w) = -m̃(w) Φ(1-w)`. -/
theorem chartSymbol_antisymm {Ψ : ℂ → ℂ} {w : ℂ}
    (hΨ : Ψ ((w + 1) / 3) = -(Gammaℝ ((w + 1) / 3) ^ 3 / Gammaℝ (1 - (w + 1) / 3) ^ 3)
      * Ψ (1 - (w + 1) / 3)) :
    chartSymbol Ψ w = -chartMultiplier w * chartSymbol Ψ (1 - w) := by
  unfold chartSymbol chartMultiplier
  have e1 : (1 - w + 1) / 3 = 1 - (w + 1) / 3 := by ring
  have e2 : (2 - w) / 3 = 1 - (w + 1) / 3 := by ring
  rw [e1, e2, hΨ]
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  have hc : (3 : ℂ) ^ (w / 2 - 3 / 4) = (3 : ℂ) ^ (w - 1 / 2) * (3 : ℂ) ^ ((1 - w) / 2 - 3 / 4) := by
    rw [← Complex.cpow_add _ _ h3]; congr 1; ring
  rw [hc, div_eq_mul_inv]
  ring

end RHTower.DegreeThreeHankel

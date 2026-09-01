import GaloisForLFunctions.HTGeometry.WimanValironRadius

/-!
# The Wiman--Valiron selection, with its window data exposed

`WimanValironRadius` selects a radius and immediately consumes the window hypotheses to produce the
order-one estimate.  The order-two estimate needs the *same* hypotheses at the *same* point, so this
module repeats the selection and returns the data instead of the conclusion.
-/

open MeasureTheory Complex Set

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- **The selected radius, with its window data.**  Under the arithmetic conditions of
`exists_radius_norm_mul_logDeriv_sub_centralIndex_le` there is a radius in the sampling interval and
a maximum-modulus point of its circle at which the central index is Lipschitz on the window — every
hypothesis both Wiman--Valiron window estimates ask for. -/
theorem exists_radius_point_window_data
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {c d H v₀ s L : ℝ}
    (hcd : c ≤ d) (hH : 0 < H) (hv₀ : 0 < v₀) (hs : 0 < s) (_hL : 0 < L) (hsL : s ≤ L * v₀)
    (hsmall : 2 * H * ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)
        - (centralIndex a (Real.exp c) : ℝ)) / s < d - c) :
    ∃ x ∈ Icc (c + H) (d + H), ∃ z : ℂ, ‖z‖ = Real.exp x ∧
      maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖ ∧
      (∀ θ : ℝ, ‖coeffFun a (circleMap 0 (Real.exp x) θ)‖ ≤ ‖coeffFun a z‖) ∧
      (z * deriv (coeffFun a) z / coeffFun a z).im = 0 ∧
      (∃ u : ℂ, ‖u‖ = 1 ∧ ∑' n : ℕ, normalisedCoeff a (Real.exp x) z n
        = ((‖∑' n : ℕ, normalisedCoeff a (Real.exp x) z n‖ : ℝ) : ℂ) * u) ∧
      (∀ v : ℝ, v₀ ≤ v → v ≤ H →
        (centralIndex a (Real.exp (x + v)) : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) + L * v) ∧
      (∀ v : ℝ, v₀ ≤ v → v ≤ H →
        (centralIndex a (Real.exp x) : ℝ) - L * v
          ≤ (centralIndex a (Real.exp (x - v)) : ℝ)) := by
  obtain ⟨y, hy, hspread⟩ := exists_small_centralIndexSpread ha hn₀ hcd hH hs hsmall
  have hLge : centralIndexSpread a (y + H) H / v₀ ≤ L := by
    rw [div_le_iff₀ hv₀]
    linarith
  set x : ℝ := y + H with hxdef
  have hr : (0 : ℝ) < Real.exp x := Real.exp_pos x
  obtain ⟨z, hz, hmax⟩ := exists_max_on_circle ha hr
  have hfz := maxTerm_le_norm_of_max_on_circle ha hr hz hmax
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
  have hfpos : 0 < ‖coeffFun a z‖ := lt_of_lt_of_le hμpos hfz
  have hfne : coeffFun a z ≠ 0 := norm_pos_iff.mp hfpos
  have hcrit := im_mul_deriv_div_eq_zero_of_max_on_circle ha hr hz hfne hmax
  have hfac : coeffFun a z
      = (a (centralIndex a (Real.exp x)) * z ^ centralIndex a (Real.exp x))
        * ∑' n : ℕ, normalisedCoeff a (Real.exp x) z n :=
    coeffFun_eq_central_term_mul_tsum ha hr hn₀ hz
  have hWne : (∑' n : ℕ, normalisedCoeff a (Real.exp x) z n) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfac
    exact hfne hfac
  obtain ⟨u, hu, hWdir⟩ := exists_unit_dir hWne
  exact ⟨x, ⟨by linarith [hy.1], by linarith [hy.2]⟩, z, hz, hfz, hmax, hcrit, ⟨u, hu, hWdir⟩,
    centralIndex_le_add_of_spread_le ha hn₀ hv₀ hLge,
    sub_of_spread_le_le_centralIndex ha hn₀ hv₀ hLge⟩

end GaloisForLFunctions.HTGeometry

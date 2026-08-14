import GaloisForLFunctions.RHTower.BarnesMellinExpansion

/-!
# The remainder of the Barnes expansion

The whole dependence of the Mellin integrand on `x` sits in the factor `x^{-w}`, whose modulus on
the line `Re w = σ` is the constant `x^{-σ}`.  So the vertical integral at abscissa `σ` is bounded
by `x^{-σ}` times a constant depending only on `s`, `m` and `σ`.  Applied at the `K`-th abscissa
`K - 1/2` this turns the finite expansion into a Poincaré asymptotic: the error after `K` terms is
`O(x^{-(K-1/2)})` as `x → ∞`, for every Euler derivative.
-/

open Complex Filter Set MeasureTheory

namespace RHTower

noncomputable section

/-- The normalized vertical integral, as a real scalar multiple of the line integral. -/
theorem verticalIntegral'_eq_smul (f : ℂ → ℂ) (σ : ℝ) :
    VerticalIntegral' f σ = ((2 * Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, f ((σ : ℂ) + (t : ℂ) * I) := by
  rw [VerticalIntegral', VerticalIntegral, smul_smul, Complex.real_smul]
  have hpine : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos))
  congr 1
  push_cast
  field_simp

/-- All the `x`-dependence of the integrand is the constant modulus `x^{-σ}`. -/
theorem norm_barnesIntegrandPow_factor {s σ t x : ℝ} (m : ℕ) (hx : 0 < x) :
    ‖barnesIntegrandPow s x m ((σ : ℂ) + (t : ℂ) * I)‖
      = x ^ (-σ) * ‖barnesIntegrandPow s 1 m ((σ : ℂ) + (t : ℂ) * I)‖ := by
  have hre : (-((σ : ℂ) + (t : ℂ) * I)).re = -σ := by simp
  have h1 : ‖((x : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ = x ^ (-σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
  have h2 : ‖(((1 : ℝ)) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos one_pos, hre, Real.one_rpow]
  simp only [barnesIntegrandPow, barnesIntegrand, norm_mul, h1, h2]
  ring

/-- **The vertical integral is `O(x^{-σ})`.**  The constant depends only on `s`, `m` and the
abscissa. -/
theorem norm_verticalIntegral'_barnesPow_le {s σ x : ℝ} (m : ℕ) (hx : 0 < x) :
    ‖VerticalIntegral' (barnesIntegrandPow s x m) σ‖
      ≤ ((2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖barnesIntegrandPow s 1 m ((σ : ℂ) + (t : ℂ) * I)‖)
        * x ^ (-σ) := by
  have hxpow : (0 : ℝ) < x ^ (-σ) := Real.rpow_pos_of_pos hx _
  rw [verticalIntegral'_eq_smul, norm_smul]
  have hnormsmul : ‖((2 * Real.pi)⁻¹ : ℝ)‖ = (2 * Real.pi)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnormsmul]
  have hint : ‖∫ t : ℝ, barnesIntegrandPow s x m ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ ∫ t : ℝ, ‖barnesIntegrandPow s x m ((σ : ℂ) + (t : ℂ) * I)‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  have hsplit : (∫ t : ℝ, ‖barnesIntegrandPow s x m ((σ : ℂ) + (t : ℂ) * I)‖)
      = x ^ (-σ) * ∫ t : ℝ, ‖barnesIntegrandPow s 1 m ((σ : ℂ) + (t : ℂ) * I)‖ := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun t => norm_barnesIntegrandPow_factor m hx)
  rw [hsplit] at hint
  calc (2 * Real.pi)⁻¹ * ‖∫ t : ℝ, barnesIntegrandPow s x m ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ (2 * Real.pi)⁻¹
          * (x ^ (-σ) * ∫ t : ℝ, ‖barnesIntegrandPow s 1 m ((σ : ℂ) + (t : ℂ) * I)‖) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = ((2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖barnesIntegrandPow s 1 m ((σ : ℂ) + (t : ℂ) * I)‖)
          * x ^ (-σ) := by ring

/-- **The Barnes remainder after `K` terms is `O(x^{-(K-1/2)})`, for every Euler derivative.** -/
theorem exists_bound_barnes_remainder (s : ℝ) (m K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖VerticalIntegral' (barnesIntegrandPow s x m) (barnesAbscissa s (K + 1))‖
        ≤ C * x ^ (-((K : ℝ) + 1 / 2)) := by
  set σK : ℝ := (K : ℝ) + 1 / 2 with hσK
  set C : ℝ :=
    (2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖barnesIntegrandPow s 1 m ((σK : ℂ) + (t : ℂ) * I)‖ with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (by positivity) (MeasureTheory.integral_nonneg fun t => norm_nonneg _)
  refine ⟨C, hC0, fun x hx => ?_⟩
  have hσ : barnesAbscissa s (K + 1) = σK := rfl
  rw [hσ]
  exact norm_verticalIntegral'_barnesPow_le m hx

/-- **The Barnes expansion with explicit error.**  After the leading term and the first `K+1`
descending powers, the error is `O(x^{-(K+1/2)})` uniformly in `x > 0`. -/
theorem barnes_poincare_expansion {s : ℝ} (hs1 : 1 < s) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖(∑' n : ℕ, ((x : ℝ) : ℂ) / (((((n : ℝ) + 1) ^ s : ℝ) : ℂ) + ((x : ℝ) : ℂ)))
          + barnesLeadingResidue s x 0
          + ∑ k ∈ Finset.range (K + 1), barnesTailResidue s x 0 k‖
        ≤ C * x ^ (-((K : ℝ) + 1 / 2)) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_barnes_remainder s 0 K
  refine ⟨C, hC0, fun x hx => ?_⟩
  have hsum := hasSum_barnes_expansion hs1 hx (K + 1)
  have htsum := hsum.tsum_eq
  have hval : (∑' n : ℕ, ((x : ℝ) : ℂ) / (((((n : ℝ) + 1) ^ s : ℝ) : ℂ) + ((x : ℝ) : ℂ)))
      + barnesLeadingResidue s x 0
      + ∑ k ∈ Finset.range (K + 1), barnesTailResidue s x 0 k
      = VerticalIntegral' (barnesIntegrandPow s x 0) (barnesAbscissa s (K + 1)) := by
    rw [htsum]
    ring
  rw [hval]
  exact hC x hx

end

end RHTower

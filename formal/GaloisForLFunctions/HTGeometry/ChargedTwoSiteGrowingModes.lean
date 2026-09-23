import GaloisForLFunctions.HTGeometry.ChargedTwoSiteKernel

/-! # Exact frequency and growth equation for actual charged two-site modes -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Real part of the actual mode determinant, organized as a difference of squares. -/
theorem chargedTwoSiteDeterminant_re (k m c d : ℝ) (ω : ℂ) :
    (chargedTwoSiteDeterminant k m c d ω).re =
      ((ω.re - c) ^ (2 : ℕ) - ω.im ^ (2 : ℕ) - (chargedTwoSiteBase k m + d ^ (2 : ℕ))) ^ (2 : ℕ) -
        4 * (ω.re - c) ^ (2 : ℕ) * ω.im ^ (2 : ℕ) -
          ((Real.exp k) ^ (2 : ℕ) + 4 * chargedTwoSiteBase k m * d ^ (2 : ℕ)) := by
  rw [chargedTwoSiteDeterminant_centered_square]
  simp only [pow_two, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero, mul_zero, zero_mul, add_zero]
  ring

/-- The imaginary determinant equation forces either the central frequency or an impossible positive-discriminant branch. -/
theorem chargedTwoSiteDeterminant_im (k m c d : ℝ) (ω : ℂ) :
    (chargedTwoSiteDeterminant k m c d ω).im =
      4 * (ω.re - c) * ω.im *
        ((ω.re - c) ^ (2 : ℕ) - ω.im ^ (2 : ℕ) - (chargedTwoSiteBase k m + d ^ (2 : ℕ))) := by
  rw [chargedTwoSiteDeterminant_centered_square]
  simp only [pow_two, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero, mul_zero, zero_mul, add_zero]
  ring

/-- An actual growing mode exists at a given frequency exactly when its real part is the potential midpoint and its growth satisfies the displayed positive quadratic equation. -/
theorem chargedTwoSite_growing_mode_iff (k m c d : ℝ) (ω : ℂ) :
    (ChargedTwoSiteHasMode k m c d ω ∧ 0 < ω.im) ↔
      ω.re = c ∧ 0 < ω.im ∧
        (ω.im ^ (2 : ℕ) + chargedTwoSiteBase k m + d ^ (2 : ℕ)) ^ (2 : ℕ) =
          (Real.exp k) ^ (2 : ℕ) + 4 * chargedTwoSiteBase k m * d ^ (2 : ℕ) := by
  constructor
  · rintro ⟨hm, hy⟩
    have hd := (chargedTwoSiteHasMode_iff_determinant k m c d ω).1 hm
    have hr := congrArg Complex.re hd
    have hi := congrArg Complex.im hd
    rw [chargedTwoSiteDeterminant_re] at hr
    rw [chargedTwoSiteDeterminant_im] at hi
    change _ = (0 : ℝ) at hr hi
    have hprod : (4 * ω.im) * ((ω.re - c) *
        ((ω.re - c) ^ (2 : ℕ) - ω.im ^ (2 : ℕ) - (chargedTwoSiteBase k m + d ^ (2 : ℕ)))) = 0 := by
      linear_combination hi
    have hc := (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero (by norm_num) hy.ne')
    rcases mul_eq_zero.mp hc with hx | hz
    · have he : ω.re = c := by linarith
      refine ⟨he, hy, ?_⟩
      rw [hx] at hr
      nlinarith [hr]
    · rw [hz] at hr
      have hp := chargedTwoSiteDiscriminant_pos k m d
      have hn := mul_nonneg (sq_nonneg (ω.re - c)) (sq_nonneg ω.im)
      nlinarith
  · rintro ⟨hx, hy, hg⟩
    refine ⟨(chargedTwoSiteHasMode_iff_determinant k m c d ω).2 ?_, hy⟩
    apply Complex.ext
    · rw [chargedTwoSiteDeterminant_re]
      change _ = (0 : ℝ)
      rw [hx]
      nlinarith [hg]
    · rw [chargedTwoSiteDeterminant_im]
      simp [hx]

/-- The exact growth equation also exposes the sharp charge-independent coupling budget. -/
theorem chargedTwoSite_growth_equation_equiv (k m d y : ℝ) :
    ((y ^ (2 : ℕ) + chargedTwoSiteBase k m + d ^ (2 : ℕ)) ^ (2 : ℕ) =
      (Real.exp k) ^ (2 : ℕ) + 4 * chargedTwoSiteBase k m * d ^ (2 : ℕ)) ↔
      (d ^ (2 : ℕ) - chargedTwoSiteBase k m + y ^ (2 : ℕ)) ^ (2 : ℕ) +
        4 * chargedTwoSiteBase k m * y ^ (2 : ℕ) = (Real.exp k) ^ (2 : ℕ) := by
  constructor <;> intro h <;> nlinarith [h]

end
end GaloisForLFunctions.HTGeometry

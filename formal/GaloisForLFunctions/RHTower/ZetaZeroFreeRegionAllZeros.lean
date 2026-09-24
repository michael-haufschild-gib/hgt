import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionSharp

/-!
# The region covers every nontrivial zero

The region `riemannZeta_ne_zero_of_one_sub_lt_re` is valid from ordinate `4`, and every zero of `ξ`
has squared ordinate above `41/2 > 16`.  So there is no exceptional range: **every** nontrivial zero
of `ζ` obeys it, and by the functional equation the two-sided form

```text
1/(58 log |Im ρ|)  ≤  Re ρ  ≤  1 − 1/(58 log |Im ρ|)
```

holds for every nontrivial zero, with no threshold and no existential constant.
-/

open Complex

namespace RHTower

noncomputable section

/-- Every nontrivial zero has ordinate above `4`. -/
theorem four_le_abs_im_of_zeta_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) : 4 ≤ |ρ.im| := by
  have hne1 : ρ ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  have hxi : xi ρ = 0 := (xi_eq_zero_iff h0 hne1).mpr hzero
  have hgap := fortyOne_div_two_lt_im_sq_of_xi_eq_zero hxi
  nlinarith [sq_abs ρ.im, abs_nonneg ρ.im]

/-- **Every nontrivial zero of `ζ` obeys the region.** -/
theorem re_le_one_sub_of_zeta_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) :
    ρ.re ≤ 1 - 1 / 58 / Real.log |ρ.im| := by
  have hγ := four_le_abs_im_of_zeta_zero h0 h1 hzero
  have hsplit : ρ = ((ρ.re : ℝ) : ℂ) + ((ρ.im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im ρ).symm
  rw [hsplit] at hzero
  exact re_le_one_sub_of_riemannZeta_eq_zero hγ hzero

/-- **The two-sided form**, from the functional equation. -/
theorem one_div_le_re_of_zeta_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) :
    1 / 58 / Real.log |ρ.im| ≤ ρ.re := by
  have hrefl : riemannZeta (1 - ρ) = 0 := (riemannZeta_one_sub_eq_zero_iff h0 h1).mpr hzero
  have hre : (1 - ρ).re = 1 - ρ.re := by simp
  have him : |(1 - ρ).im| = |ρ.im| := by
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
  have h := re_le_one_sub_of_zeta_zero (ρ := 1 - ρ) (by rw [hre]; linarith)
    (by rw [hre]; linarith) hrefl
  rw [hre, him] at h
  linarith

/-- The resulting lower bound for `Re ρ (1 − Re ρ)`. -/
theorem mul_one_sub_re_ge_of_zeta_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) :
    (1 / 58 / Real.log |ρ.im|) * (1 - 1 / 58 / Real.log |ρ.im|) ≤ ρ.re * (1 - ρ.re) := by
  have hlow := one_div_le_re_of_zeta_zero h0 h1 hzero
  have hup := re_le_one_sub_of_zeta_zero h0 h1 hzero
  nlinarith [hlow, hup]

end

end RHTower

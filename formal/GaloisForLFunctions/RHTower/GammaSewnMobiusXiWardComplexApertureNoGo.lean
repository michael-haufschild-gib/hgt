import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardyContraction

/-!
# No common complex aperture for the Xi Ward Cayley cells

The fixed Xi Ward phase is contractive for nonnegative real aperture.  This
cannot be promoted to a holomorphic Schur family in aperture: the common
contractivity set of all right-half-plane Cayley cells is exactly the closed
nonnegative real ray.

This is an unconditional source-side no-go.  It rules out obtaining the Ward
column bound by applying Schwarz--Pick to a complexified scalar aperture.
-/

open Complex

namespace RHTower

noncomputable section

/-- Squared-norm form of simultaneous contractivity for every
right-half-plane Cayley cell.  This form remains meaningful without a
denominator side condition. -/
def XiWardComplexApertureCommonContractive (alpha : ℂ) : Prop :=
  ∀ a : ℂ, 0 < a.re →
    Complex.normSq (a - alpha) ≤ Complex.normSq (a + alpha)

/-- Exact polarization identity controlling one complex-aperture Cayley
cell. -/
theorem normSq_add_sub_xiWardComplexAperture
    (a alpha : ℂ) :
    Complex.normSq (a + alpha) - Complex.normSq (a - alpha) =
      4 * (a * star alpha).re := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, RCLike.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Away from its pole, squared-norm contractivity is exactly ordinary
Cayley contractivity. -/
theorem norm_xiWardComplexApertureCayley_le_one_iff
    {a alpha : ℂ} (hden : a + alpha ≠ 0) :
    ‖(a - alpha) / (a + alpha)‖ ≤ 1 ↔
      Complex.normSq (a - alpha) ≤ Complex.normSq (a + alpha) := by
  rw [norm_div, div_le_one (norm_pos_iff.mpr hden),
    ← Complex.sq_norm, ← Complex.sq_norm]
  constructor
  · intro h
    nlinarith [norm_nonneg (a - alpha), norm_nonneg (a + alpha)]
  · intro h
    nlinarith [norm_nonneg (a - alpha), norm_nonneg (a + alpha)]

/-- **Complex-aperture no-go.**  Simultaneous contractivity for every
right-half-plane Cayley cell holds exactly on the nonnegative real ray. -/
theorem xiWardComplexApertureCommonContractive_iff
    (alpha : ℂ) :
    XiWardComplexApertureCommonContractive alpha ↔
      alpha.im = 0 ∧ 0 ≤ alpha.re := by
  constructor
  · intro h
    constructor
    · by_contra him
      let t : ℝ := -(alpha.re + 1) / alpha.im
      let a : ℂ := ⟨1, t⟩
      have ha : 0 < a.re := by simp [a]
      have hineq := h a ha
      have hnonneg :
          0 ≤ Complex.normSq (a + alpha) -
            Complex.normSq (a - alpha) :=
        sub_nonneg.mpr hineq
      rw [normSq_add_sub_xiWardComplexAperture] at hnonneg
      have hdot : (a * star alpha).re = -1 := by
        simp only [a, t, Complex.mul_re, RCLike.star_def,
          Complex.conj_re, Complex.conj_im]
        field_simp [him]
        ring
      rw [hdot] at hnonneg
      norm_num at hnonneg
    · have hineq := h 1 (by norm_num)
      have hnonneg :
          0 ≤ Complex.normSq ((1 : ℂ) + alpha) -
            Complex.normSq ((1 : ℂ) - alpha) :=
        sub_nonneg.mpr hineq
      rw [normSq_add_sub_xiWardComplexAperture] at hnonneg
      have hone : ((1 : ℂ) * star alpha).re = alpha.re := by simp
      rw [hone] at hnonneg
      linarith
  · rintro ⟨him, hre⟩ a ha
    rw [← sub_nonneg,
      normSq_add_sub_xiWardComplexAperture]
    simp only [Complex.mul_re, RCLike.star_def, Complex.conj_re,
      Complex.conj_im, him, neg_zero, mul_zero, sub_zero]
    positivity

/-- Any aperture with nonzero imaginary part has an explicit
right-half-plane Cayley cell on which contractivity fails. -/
theorem exists_xiWardComplexApertureCayley_expansive_of_im_ne_zero
    {alpha : ℂ} (him : alpha.im ≠ 0) :
    ∃ a : ℂ, 0 < a.re ∧
      Complex.normSq (a + alpha) <
        Complex.normSq (a - alpha) := by
  let t : ℝ := -(alpha.re + 1) / alpha.im
  let a : ℂ := ⟨1, t⟩
  refine ⟨a, by simp [a], ?_⟩
  have hdot : (a * star alpha).re = -1 := by
    simp only [a, t, Complex.mul_re, RCLike.star_def,
      Complex.conj_re, Complex.conj_im]
    field_simp [him]
    ring
  have hgap :=
    normSq_add_sub_xiWardComplexAperture a alpha
  rw [hdot] at hgap
  linarith

end

end RHTower

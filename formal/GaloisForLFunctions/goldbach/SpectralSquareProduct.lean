import GaloisForLFunctions.RHTower.IharaBlockSelector

/-!
# Spectral squares and critical-line zeros

The normalized Li--Liu factor `1 - 4 μ² z(1-z)` is a specialization of
the existing Ihara quadratic block. Its critical-line condition is exactly
`μ² ≤ 1`. Finite products retain this equivalence factor by factor, so
functional-equation symmetry alone imposes no spectral bound.
-/

namespace GaloisForLFunctions.Goldbach

open Finset

noncomputable section

/-- The spectral factor normalized by the target operator scale. -/
def spectralSquareFactor (μ : ℝ) (z : ℂ) : ℂ :=
  iharaBlock (4 * μ ^ 2) (4 * μ ^ 2) z

/-- The quadratic Ihara specialization is precisely the symmetric spectral factor. -/
theorem spectralSquareFactor_eq (μ : ℝ) (z : ℂ) :
    spectralSquareFactor μ z = 1 - 4 * (μ : ℂ) ^ 2 * z * (1 - z) := by
  simp only [spectralSquareFactor, iharaBlock, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  ring

/-- Reflection about one half is automatic at every spectral scale. -/
theorem spectralSquareFactor_reflect (μ : ℝ) (z : ℂ) :
    spectralSquareFactor μ (1 - z) = spectralSquareFactor μ z := by
  rw [spectralSquareFactor_eq, spectralSquareFactor_eq]
  ring

/-- Centering removes the linear term and makes the even symmetry explicit. -/
theorem spectralSquareFactor_center (μ : ℝ) (z : ℂ) :
    spectralSquareFactor μ (1 / 2 + z) = 1 - (μ : ℂ) ^ 2 + 4 * (μ : ℂ) ^ 2 * z ^ 2 := by
  rw [spectralSquareFactor_eq]
  ring

/-- The zero spectral value contributes the constant factor one. -/
theorem spectralSquareFactor_zero (z : ℂ) : spectralSquareFactor 0 z = 1 := by
  simp only [spectralSquareFactor_eq, Complex.ofReal_zero, zero_pow two_ne_zero,
    mul_zero, zero_mul, sub_zero]

private theorem spectralSquareFactor_root_nonzero (μ : ℝ) (z : ℂ)
    (h : spectralSquareFactor μ z = 0) : μ ≠ 0 := by
  intro hm
  rw [hm, spectralSquareFactor_zero] at h
  exact one_ne_zero h

/-- Every nonreal zero is on the critical line. -/
theorem spectralSquareFactor_zero_location (μ : ℝ) (z : ℂ) :
    spectralSquareFactor μ z = 0 → z.re = 1 / 2 ∨ z.im = 0 := by
  intro h
  have hm := spectralSquareFactor_root_nonzero μ z h
  have hi := iharaBlock_im_eq_zero (4 * μ ^ 2) (4 * μ ^ 2) z h
  rcases mul_eq_zero.mp hi with him | hre
  · exact Or.inr him
  · left
    have hq : 0 < 4 * μ ^ 2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hm)
    have hx : (4 * μ ^ 2) * (2 * z.re - 1) = 0 := by nlinarith only [hre]
    have hz := (mul_eq_zero.mp hx).resolve_left hq.ne'
    linarith only [hz]

/-- Critical-line zeros are equivalent to the exact normalized spectral bound. -/
theorem spectralSquareFactor_critical_iff (μ : ℝ) :
    (∀ z : ℂ, spectralSquareFactor μ z = 0 → z.re = 1 / 2) ↔ μ ^ 2 ≤ 1 := by
  by_cases hm : μ = 0
  · subst μ
    simp only [spectralSquareFactor_zero, one_ne_zero, false_implies, implies_true,
      zero_pow two_ne_zero]
    norm_num
  have hq : 0 < 4 * μ ^ 2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hm)
  constructor
  · intro h
    have hc : zerosOnCriticalCircle (4 * μ ^ 2) (4 * μ ^ 2) := by
      intro z hz
      have hx := h z hz
      have hr := iharaBlock_re_eq_zero (4 * μ ^ 2) (4 * μ ^ 2) z hz
      rw [Complex.normSq_apply]
      apply mul_left_cancel₀ hq.ne'
      rw [mul_inv_cancel₀ hq.ne']
      rw [hx] at hr ⊢
      nlinarith only [hr]
    have hb := (zerosOnCriticalCircle_iff_spectral_bound hq).mp hc
    change (4 * μ ^ 2) ^ 2 ≤ 4 * (4 * μ ^ 2) at hb
    by_contra hn
    have hp : 0 < μ ^ 2 * (μ ^ 2 - 1) :=
      mul_pos (sq_pos_of_ne_zero hm) (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hb, hp]
  · intro hb z hz
    rcases spectralSquareFactor_zero_location μ z hz with hx | hy
    · exact hx
    have hr := iharaBlock_re_eq_zero (4 * μ ^ 2) (4 * μ ^ 2) z hz
    rw [hy] at hr
    have he : μ ^ 2 * (2 * z.re - 1) ^ 2 = μ ^ 2 - 1 := by
      nlinarith only [hr]
    have hp : μ ^ 2 * (2 * z.re - 1) ^ 2 = 0 :=
      le_antisymm (by linarith only [he, hb])
        (mul_nonneg (sq_nonneg μ) (sq_nonneg _))
    have hx := sq_eq_zero_iff.mp ((mul_eq_zero.mp hp).resolve_left (pow_ne_zero 2 hm))
    linarith only [hx]

/-- A finite spectral function, allowing zero eigenvalues and an empty spectrum. -/
def finiteSpectralSquareProduct {ι : Type*} [Fintype ι] (μ : ι → ℝ) (z : ℂ) : ℂ :=
  ∏ i, spectralSquareFactor (μ i) z

/-- No additional roots are created by a finite spectral product. -/
theorem finiteSpectralSquareProduct_eq_zero_iff {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (z : ℂ) :
    finiteSpectralSquareProduct μ z = 0 ↔ ∃ i, spectralSquareFactor (μ i) z = 0 := by
  classical
  simp only [finiteSpectralSquareProduct, prod_eq_zero_iff, mem_univ, true_and]

/-- The finite version of the spectral zero--norm correspondence. -/
theorem finiteSpectralSquareProduct_critical_iff {ι : Type*} [Fintype ι] (μ : ι → ℝ) :
    (∀ z : ℂ, finiteSpectralSquareProduct μ z = 0 → z.re = 1 / 2) ↔
      ∀ i, μ i ^ 2 ≤ 1 := by
  constructor
  · intro h i
    apply (spectralSquareFactor_critical_iff (μ i)).mp
    intro z hz
    exact h z ((finiteSpectralSquareProduct_eq_zero_iff μ z).mpr ⟨i, hz⟩)
  · intro h z hz
    obtain ⟨i, hi⟩ := (finiteSpectralSquareProduct_eq_zero_iff μ z).mp hz
    exact (spectralSquareFactor_critical_iff (μ i)).mpr (h i) z hi

/-- The functional equation survives arbitrary spectral values. -/
theorem finiteSpectralSquareProduct_reflect {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (z : ℂ) :
    finiteSpectralSquareProduct μ (1 - z) = finiteSpectralSquareProduct μ z := by
  simp only [finiteSpectralSquareProduct, spectralSquareFactor_reflect]

end

end GaloisForLFunctions.Goldbach

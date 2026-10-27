import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceTransformGrowth

/-!
# Explicit aperture bounds for compact source tests

The L¹ sizes of a test and its second derivative control its transform
homogeneously. On the zero strip, the squared transform costs only the
exponential of the physical aperture; a separate Gaussian envelope controls
the whole spectral plane.
-/

open Complex MeasureTheory Set
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

/-- Explicit C² source size used by the Fourier decay estimate. -/
def sourceTestSize (f : CompactTest) : ℝ :=
  4 * ((∫ u, ‖f.1 u‖) + ∫ u, ‖deriv (deriv f.1) u‖)

lemma sourceTestSize_nonneg (f : CompactTest) : 0 ≤ sourceTestSize f :=
  mul_nonneg (by norm_num)
    (add_nonneg (integral_nonneg fun _ => norm_nonneg _)
      (integral_nonneg fun _ => norm_nonneg _))

/-- The source norm and aperture remain explicit in the centred transform estimate. -/
theorem norm_tr_le_sourceTestSize (f : CompactTest) {a : ℝ}
    (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ a) (z : ℂ) :
    ‖tr f.1 z‖ ≤ Real.exp (|z.re - 1 / 2| * a) * sourceTestSize f /
      (1 + |z.im|) ^ 2 := by
  have hre : (gammaOf z).re = z.im := by
    rw [gammaOf, Complex.div_I]
    simp
  have him : |(gammaOf z).im| = |z.re - 1 / 2| := by
    rw [gammaOf, Complex.div_I]
    simp only [Complex.neg_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.I_re, Complex.I_im]
    norm_num
    exact abs_sub_comm _ _
  simpa only [tr, hre, him, sourceTestSize] using
    norm_paperFT_le_decay f.2.1 hsupp (gammaOf z)

/-- Fourth-order vertical decay with an explicit horizontal aperture cost. -/
theorem normSq_tr_le_sourceTestSize (f : CompactTest) {a : ℝ}
    (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ a) (z : ℂ) :
    Complex.normSq (tr f.1 z) ≤
      sourceTestSize f ^ 2 * Real.exp (2 * (|z.re - 1 / 2| * a)) /
        (1 + z.im ^ 2) ^ 2 := by
  have ht := norm_tr_le_sourceTestSize f hsupp z
  have hden : (1 + z.im ^ 2) ^ 2 ≤ (1 + |z.im|) ^ 4 := by
    have hb : 1 + z.im ^ 2 ≤ (1 + |z.im|) ^ 2 := by
      nlinarith only [abs_nonneg z.im, sq_abs z.im]
    calc
      (1 + z.im ^ 2) ^ 2 ≤ ((1 + |z.im|) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hb 2
      _ = _ := by ring
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖tr f.1 z‖ ^ 2 ≤
        (Real.exp (|z.re - 1 / 2| * a) * sourceTestSize f / (1 + |z.im|) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ht 2
    _ = sourceTestSize f ^ 2 * Real.exp (2 * (|z.re - 1 / 2| * a)) /
        (1 + |z.im|) ^ 4 := by
      rw [div_pow, mul_pow, ← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      ring
    _ ≤ _ := div_le_div_of_nonneg_left
      (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by positivity) hden

/-- On the critical strip, the square loses only `exp a` in physical aperture. -/
theorem normSq_tr_strip_le_sourceTestSize (f : CompactTest) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ a) {z : ℂ} (hz : 0 ≤ z.re ∧ z.re ≤ 1) :
    Complex.normSq (tr f.1 z) ≤
      sourceTestSize f ^ 2 * Real.exp a / (1 + z.im ^ 2) ^ 2 := by
  have hδ : |z.re - 1 / 2| ≤ (1 / 2 : ℝ) :=
    abs_le.mpr ⟨by linarith only [hz.1], by linarith only [hz.2]⟩
  have hm := mul_le_mul_of_nonneg_right hδ ha
  refine (normSq_tr_le_sourceTestSize f hsupp z).trans ?_
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith only [hm])) (sq_nonneg _)) (sq_nonneg _)

/-- A whole-plane Gaussian envelope, homogeneous in the explicit source norm. -/
theorem norm_tr_le_apertureGaussian (f : CompactTest) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ a) (z : ℂ) :
    ‖tr f.1 z‖ ≤ (sourceTestSize f * Real.exp (a ^ 2 + a)) * Real.exp (‖z‖ ^ 2) := by
  have hS := sourceTestSize_nonneg f
  have hden : 1 ≤ (1 + |z.im|) ^ 2 := by
    nlinarith only [abs_nonneg z.im, sq_nonneg |z.im|]
  have habs : |z.re - 1 / 2| ≤ ‖z‖ + 1 / 2 := by
    have h := abs_sub z.re (1 / 2)
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    linarith only [h, Complex.abs_re_le_norm z]
  have hm := mul_le_mul_of_nonneg_right habs ha
  have hexp : |z.re - 1 / 2| * a ≤ (a ^ 2 + a) + ‖z‖ ^ 2 := by
    nlinarith only [hm, sq_nonneg (‖z‖ - a), sq_nonneg a, sq_nonneg ‖z‖, ha]
  calc
    ‖tr f.1 z‖ ≤ Real.exp (|z.re - 1 / 2| * a) * sourceTestSize f /
        (1 + |z.im|) ^ 2 := norm_tr_le_sourceTestSize f hsupp z
    _ ≤ Real.exp (|z.re - 1 / 2| * a) * sourceTestSize f := by
      apply (div_le_iff₀ (by positivity)).2
      exact le_mul_of_one_le_right (mul_nonneg (Real.exp_pos _).le hS) hden
    _ = sourceTestSize f * Real.exp (|z.re - 1 / 2| * a) := mul_comm _ _
    _ ≤ sourceTestSize f * Real.exp ((a ^ 2 + a) + ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hS
    _ = _ := by rw [Real.exp_add]; ring

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.norm_tr_le_apertureGaussian
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.normSq_tr_strip_le_sourceTestSize

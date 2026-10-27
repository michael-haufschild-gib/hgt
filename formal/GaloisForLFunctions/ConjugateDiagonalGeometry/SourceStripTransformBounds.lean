import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceTestApertureBounds

/-!
# Height-independent transform bounds on vertical strips

The modulus of a centred transform depends on horizontal displacement.
Ordinate modulation therefore has no cost in a fixed strip. A unit-circle
Cauchy estimate retains this property for the first holomorphic derivative.
-/

open Complex Set Metric
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

/-- Horizontal aperture controls the transform uniformly in the ordinate. -/
theorem norm_tr_le_sourceTestSize_strip (f : CompactTest) {a R : ℝ}
    (ha : 0 ≤ a) (hsupp : ∀ u, f.1 u ≠ 0 → |u| ≤ a)
    {z : ℂ} (hz : |z.re - 1 / 2| ≤ R) :
    ‖tr f.1 z‖ ≤ sourceTestSize f * Real.exp (R * a) := by
  have hS := sourceTestSize_nonneg f
  have hden : 1 ≤ (1 + |z.im|) ^ 2 := by
    nlinarith only [abs_nonneg z.im, sq_nonneg |z.im|]
  calc
    ‖tr f.1 z‖ ≤ Real.exp (|z.re - 1 / 2| * a) * sourceTestSize f /
        (1 + |z.im|) ^ 2 := norm_tr_le_sourceTestSize f hsupp z
    _ ≤ Real.exp (|z.re - 1 / 2| * a) * sourceTestSize f := by
      apply (div_le_iff₀ (by positivity)).2
      exact le_mul_of_one_le_right (mul_nonneg (Real.exp_pos _).le hS) hden
    _ = sourceTestSize f * Real.exp (|z.re - 1 / 2| * a) := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz ha)) hS

/-- Real translation costs aperture, while arbitrary ordinate modulation is free in a strip. -/
theorem norm_shiftedSourceTransform_le_strip (f : CompactTest) {a R : ℝ}
    (ha : 0 ≤ a) (hsupp : ∀ x, f.1 x ≠ 0 → |x| ≤ a)
    (u τ : ℝ) {z : ℂ} (hz : |z.re - 1 / 2| ≤ R) :
    ‖shiftedSourceTransform f u τ z‖ ≤
      sourceTestSize f * Real.exp (R * (a + |u|)) := by
  have hz' : |(z - (τ : ℂ) * Complex.I).re - 1 / 2| ≤ R := by
    simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero] using hz
  have htr := norm_tr_le_sourceTestSize_strip f ha hsupp hz'
  have hx : u * (z.re - 1 / 2) ≤ |u| * R := by
    calc
      u * (z.re - 1 / 2) ≤ |u * (z.re - 1 / 2)| := le_abs_self _
      _ = |u| * |z.re - 1 / 2| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hz (abs_nonneg u)
  have hre : (((z - 1 / 2) * (u : ℂ)) : ℂ).re = u * (z.re - 1 / 2) := by
    simp
    ring
  rw [shiftedSourceTransform, norm_mul, Complex.norm_exp, hre]
  calc
    Real.exp (u * (z.re - 1 / 2)) * ‖tr f.1 (z - (τ : ℂ) * Complex.I)‖ ≤
        Real.exp (|u| * R) * (sourceTestSize f * Real.exp (R * a)) :=
      mul_le_mul (Real.exp_le_exp.mpr hx) htr (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      rw [show R * (a + |u|) = |u| * R + R * a by ring, Real.exp_add]
      ring

/-- Values and first derivatives share a height-independent strip envelope. -/
theorem shiftedSourceTransform_strip_bound (f : CompactTest) {a R : ℝ}
    (ha : 0 ≤ a) (hsupp : ∀ x, f.1 x ≠ 0 → |x| ≤ a)
    (u τ : ℝ) {z : ℂ} (hz : |z.re - 1 / 2| ≤ R) :
    ‖shiftedSourceTransform f u τ z‖ ≤
        sourceTestSize f * Real.exp ((R + 1) * (a + |u|)) ∧
      ‖deriv (shiftedSourceTransform f u τ) z‖ ≤
        sourceTestSize f * Real.exp ((R + 1) * (a + |u|)) := by
  have hb (w : ℂ) (hw : |w.re - 1 / 2| ≤ R + 1) :
      ‖shiftedSourceTransform f u τ w‖ ≤
        sourceTestSize f * Real.exp ((R + 1) * (a + |u|)) :=
    norm_shiftedSourceTransform_le_strip f ha hsupp u τ hw
  refine ⟨hb z (by linarith only [hz]), ?_⟩
  have hc : ∀ w ∈ sphere z 1,
      ‖shiftedSourceTransform f u τ w‖ ≤
        sourceTestSize f * Real.exp ((R + 1) * (a + |u|)) := by
    intro w hw
    apply hb
    have hdist : ‖w - z‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using hw
    have hre : |(w - z).re| ≤ 1 := by
      simpa only [hdist] using Complex.abs_re_le_norm (w - z)
    have ht := abs_add_le (w - z).re (z.re - 1 / 2)
    have he : (w - z).re + (z.re - 1 / 2) = w.re - 1 / 2 := by
      rw [Complex.sub_re]
      ring
    rw [he] at ht
    linarith only [ht, hre, hz]
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1
    (by norm_num : (0 : ℝ) < 1) (differentiable_shiftedSourceTransform f u τ).diffContOnCl hc
  simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, pow_one,
    div_one, one_mul] using h

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.shiftedSourceTransform_strip_bound

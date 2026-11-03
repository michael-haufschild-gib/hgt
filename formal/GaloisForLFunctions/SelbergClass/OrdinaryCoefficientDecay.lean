import GaloisForLFunctions.SelbergClass.OrdinaryUpperContinuation
import GaloisForLFunctions.SelbergClass.OrdinaryFourierExtraction
import GaloisForLFunctions.HTGeometry.CompactContinuousNormBound

/-!
# Exponential coefficient decay below degree one

The periodic upper-half-plane continuation transports a Fourier coefficient
integral to every vertical line. Compactness on each period then gives
exponential decay of the Dirichlet coefficients.
-/

noncomputable section
open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.SelbergClass

private def ordinaryCoefficientKernel (F : ExtendedSelbergClass) (n : ℕ) (z : ℂ) : ℂ :=
  ordinaryContinuation F (z + 2 * (Real.pi : ℂ) * I) * Complex.exp ((n : ℂ) * z)

private theorem analyticAt_ordinaryCoefficientKernel (F : ExtendedSelbergClass)
    (hd0 : 0 < F.gammaData.degree) (hd1 : F.gammaData.degree < 1)
    (n : ℕ) {z : ℂ} (hz : -(2 * Real.pi) < z.im) :
    AnalyticAt ℂ (ordinaryCoefficientKernel F n) z := by
  apply AnalyticAt.mul
  · refine AnalyticAt.comp (g := ordinaryContinuation F)
      (f := fun w : ℂ => w + 2 * (Real.pi : ℂ) * I) (x := z)
      (analyticOnNhd_ordinaryContinuation_upper F hd0 hd1 _ ?_) (by fun_prop)
    change 0 < (z + 2 * (Real.pi : ℂ) * I).im
    have he : (z + 2 * (Real.pi : ℂ) * I).im = z.im + 2 * Real.pi := by simp
    rw [he]
    linarith
  · fun_prop

private theorem ordinaryCoefficientKernel_periodic (F : ExtendedSelbergClass)
    (hd0 : 0 < F.gammaData.degree) (hd1 : F.gammaData.degree < 1)
    (n : ℕ) {z : ℂ} (hz : -(2 * Real.pi) < z.im) :
    ordinaryCoefficientKernel F n (z + 2 * (Real.pi : ℂ) * I) =
      ordinaryCoefficientKernel F n z := by
  have hz' : 0 < (z + 2 * (Real.pi : ℂ) * I).im := by
    have he : (z + 2 * (Real.pi : ℂ) * I).im = z.im + 2 * Real.pi := by simp
    rw [he]
    linarith
  have he : Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * I)) = 1 := by
    rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
  rw [ordinaryCoefficientKernel, ordinaryCoefficientKernel,
    ordinaryContinuation_periodic_upper F hd0 hd1 hz', mul_add, Complex.exp_add,
    he, mul_one]

private theorem integral_ordinaryCoefficientKernel_eq (F : ExtendedSelbergClass)
    (hd0 : 0 < F.gammaData.degree) (hd1 : F.gammaData.degree < 1)
    (n : ℕ) (a : ℝ) :
    (∫ t in (-Real.pi)..Real.pi, ordinaryCoefficientKernel F n ((a : ℂ) + (t : ℂ) * I)) =
      2 * (Real.pi : ℂ) * F.coeff n := by
  have hd : DifferentiableOn ℂ (ordinaryCoefficientKernel F n)
      (uIcc a 1 ×ℂ uIcc (-Real.pi) Real.pi) := by
    intro z hz
    have hzIm : z.im ∈ uIcc (-Real.pi) Real.pi := hz.2
    have hy : z.im ∈ Icc (-Real.pi) Real.pi := by
      simpa only [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] using hzIm
    exact (analyticAt_ordinaryCoefficientKernel F hd0 hd1 n
      (by linarith [hy.1, Real.pi_pos])).differentiableAt.differentiableWithinAt
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (ordinaryCoefficientKernel F n) ⟨a, -Real.pi⟩ ⟨1, Real.pi⟩ hd
  change ((∫ x in a..1, ordinaryCoefficientKernel F n ((x : ℂ) + ((-Real.pi : ℝ) : ℂ) * I)) -
      (∫ x in a..1, ordinaryCoefficientKernel F n ((x : ℂ) + (Real.pi : ℂ) * I))) +
      I • (∫ t in (-Real.pi)..Real.pi, ordinaryCoefficientKernel F n (1 + (t : ℂ) * I)) -
      I • (∫ t in (-Real.pi)..Real.pi, ordinaryCoefficientKernel F n ((a : ℂ) + (t : ℂ) * I)) = 0 at hc
  have hhor : (∫ x in a..1, ordinaryCoefficientKernel F n ((x : ℂ) + ((-Real.pi : ℝ) : ℂ) * I)) =
      ∫ x in a..1, ordinaryCoefficientKernel F n ((x : ℂ) + (Real.pi : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    have hp := ordinaryCoefficientKernel_periodic F hd0 hd1 n
      (z := (x : ℂ) + ((-Real.pi : ℝ) : ℂ) * I) (by simp; linarith [Real.pi_pos])
    have he : (x : ℂ) + ((-Real.pi : ℝ) : ℂ) * I + 2 * (Real.pi : ℂ) * I =
        (x : ℂ) + (Real.pi : ℂ) * I := by push_cast; ring
    rw [he] at hp
    exact hp.symm
  rw [hhor, sub_self, zero_add, smul_eq_mul, smul_eq_mul] at hc
  have hv : (∫ t in (-Real.pi)..Real.pi, ordinaryCoefficientKernel F n ((a : ℂ) + (t : ℂ) * I)) =
      ∫ t in (-Real.pi)..Real.pi, ordinaryCoefficientKernel F n (1 + (t : ℂ) * I) := by
    apply (mul_left_cancel₀ Complex.I_ne_zero)
    exact (sub_eq_zero.mp hc).symm
  rw [hv]
  rw [← integral_ordinaryExponentialSeries_mul_exp F n]
  apply intervalIntegral.integral_congr
  intro t _
  change ordinaryContinuation F (1 + (t : ℂ) * I + 2 * (Real.pi : ℂ) * I) *
      Complex.exp ((n : ℂ) * (1 + (t : ℂ) * I)) = _
  rw [ordinaryContinuation_eq_series F hd0 hd1 (by simp),
    ordinaryExponentialSeries_periodic F]

/-- Each negative vertical line yields its own exponential coefficient bound. -/
theorem exists_exponential_coeff_bound_of_degree_lt_one (F : ExtendedSelbergClass)
    (hd0 : 0 < F.gammaData.degree) (hd1 : F.gammaData.degree < 1) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖F.coeff n‖ ≤ C * Real.exp (-R * n) := by
  let g : ℝ → ℂ := fun t =>
    ordinaryContinuation F ((-R : ℂ) + (t : ℂ) * I + 2 * (Real.pi : ℂ) * I)
  have hg : ContinuousOn g (Icc (-Real.pi) Real.pi) := by
    intro t ht
    have hp : 0 < ((-R : ℂ) + (t : ℂ) * I + 2 * (Real.pi : ℂ) * I).im := by
      have he : ((-R : ℂ) + (t : ℂ) * I + 2 * (Real.pi : ℂ) * I).im = t + 2 * Real.pi := by simp
      rw [he]
      linarith [ht.1, Real.pi_pos]
    exact (ContinuousAt.comp (g := ordinaryContinuation F)
      (f := fun t : ℝ => (-R : ℂ) + (t : ℂ) * I + 2 * (Real.pi : ℂ) * I)
      (x := t) (analyticOnNhd_ordinaryContinuation_upper F hd0 hd1 _ hp).continuousAt
      (by fun_prop)).continuousWithinAt
  obtain ⟨C, hC0, hC⟩ := exists_compact_continuous_norm_bound isCompact_Icc g hg
  refine ⟨C, hC0, fun n => ?_⟩
  have hb : ∀ t ∈ uIoc (-Real.pi) Real.pi,
      ‖ordinaryCoefficientKernel F n (((-R : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        C * Real.exp (-R * n) := by
    intro t ht
    have ht' : t ∈ Icc (-Real.pi) Real.pi := by
      rw [uIoc_of_le (by linarith [Real.pi_pos])] at ht
      exact ⟨ht.1.le, ht.2⟩
    have he : ‖Complex.exp ((n : ℂ) * (((-R : ℝ) : ℂ) + (t : ℂ) * I))‖ =
        Real.exp (-R * n) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
      ring
    rw [ordinaryCoefficientKernel, norm_mul, he]
    simpa only [g, Complex.ofReal_neg] using
      mul_le_mul_of_nonneg_right (hC t ht') (Real.exp_pos (-R * n)).le
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [integral_ordinaryCoefficientKernel_eq F hd0 hd1 n (-R), norm_mul, norm_mul,
    htwo, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    show |Real.pi - -Real.pi| = 2 * Real.pi by rw [abs_of_pos (by linarith [Real.pi_pos])]; ring] at hi
  have hi' : (2 * Real.pi) * ‖F.coeff n‖ ≤ (2 * Real.pi) * (C * Real.exp (-R * n)) := by
    nlinarith only [hi]
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * Real.pi)).mp hi'

end GaloisForLFunctions.SelbergClass

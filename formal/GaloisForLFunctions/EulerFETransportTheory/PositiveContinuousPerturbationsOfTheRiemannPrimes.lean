import GaloisForLFunctions.EulerFETransportTheory.AContinuousPrimeDensityHasARationalMellinTransform

/-!
# Positive continuous perturbations of the Riemann primes

Adding `ε x exp(-x) dx` in the logarithmic prime coordinate multiplies
zeta by the zero-free factor `exp(ε/(s+1)²)`. The perturbed integer measure
is the positive multiplicative convolution exponential of its prime-power
measure, with no assumption on analytic continuation.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped ENNReal NNReal
open GaloisForLFunctions.ArithmeticPositiveDuality

namespace GaloisForLFunctions.EulerFETransportTheory

/-- The Riemann prime-power measure has all moments in the Euler half-plane. -/
theorem integrable_rpow_riemannPrimeMeasure {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun u : ℝ => u ^ (-σ)) riemannPrimeMeasure := by
  unfold riemannPrimeMeasure
  refine integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top) ?_
  have hc : LSeriesSummable (1 : ℕ → ℂ) (σ : ℂ) := LSeriesSummable_one_iff.mpr hσ
  have hcn := summable_norm_iff.mpr hc
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) hcn
  rcases eq_or_ne n 0 with rfl | hn
  · simp [riemannPrimeWeight, LSeries.term_zero]
  · rw [ENNReal.toReal_ofReal (riemannPrimeWeight_nonneg n), LSeries.term_of_ne_zero hn,
      norm_div, Pi.one_apply, norm_one,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), ofReal_re]
    have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnpos.le _),
      Real.rpow_neg hnpos.le, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (riemannPrimeWeight_le_one n)
      (Real.rpow_nonneg hnpos.le _)

local instance : SigmaFinite riemannPrimeMeasure :=
  sigmaFinite_of_measure_Iio_one_eq_zero
    (measure_mono_null Iio_subset_Iic_self riemannPrimeMeasure_Iic_one_eq_zero)
    (integrable_inv_sq_of_integrable_rpow_neg_three_halves
      (measure_mono_null Iio_subset_Iic_self riemannPrimeMeasure_Iic_one_eq_zero)
      integrable_rpow_neg_three_halves_riemannPrimeMeasure)

/-- Euler's exponential identity in the prime-power measure normalization. -/
theorem exp_measureDirichlet_riemannPrimeMeasure {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (measureDirichlet riemannPrimeMeasure s) = riemannZeta s := by
  rw [← measureDirichlet_beurlingIntegerMeasure riemannPrimeMeasure_Iic_one_eq_zero
    (integrable_rpow_riemannPrimeMeasure hs), beurlingIntegerMeasure_riemannPrimeMeasure]
  have hsmul : (Measure.sum fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) =
      Measure.sum (fun k : ℕ => (1 : ℝ≥0∞) • Measure.dirac ((k : ℝ) + 1)) := by
    congr 1
    ext k : 1
    simp
  unfold measureDirichlet
  rw [hsmul, integral_sum_dirac (fun _ => ENNReal.one_ne_top),
    zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  refine tsum_congr fun k => ?_
  rw [ENNReal.toReal_one, one_smul, Complex.cpow_neg, one_div,
    show (((k : ℝ) + 1 : ℝ) : ℂ) = (k : ℂ) + 1 by push_cast; ring]

/-- The continuous positive deformation of the classical prime-power measure. -/
def perturbedRiemannPrimeMeasure (ε : ℝ≥0) : Measure ℝ :=
  riemannPrimeMeasure + (ε : ℝ≥0∞) • continuousPrimeMeasure

/-- Its explicit meromorphic zeta function on `Re s > -1`. -/
def continuousEulerZeta (ε : ℝ≥0) (s : ℂ) : ℂ :=
  riemannZeta s * Complex.exp ((ε : ℂ) / (s + 1) ^ 2)

instance (ε : ℝ≥0) : SFinite (perturbedRiemannPrimeMeasure ε) := by
  unfold perturbedRiemannPrimeMeasure
  infer_instance

theorem perturbedRiemannPrimeMeasure_Iic_one (ε : ℝ≥0) :
    perturbedRiemannPrimeMeasure ε (Iic 1) = 0 := by
  simp [perturbedRiemannPrimeMeasure, riemannPrimeMeasure_Iic_one_eq_zero,
    continuousPrimeMeasure_Iic_one]

theorem integrable_rpow_perturbedRiemannPrimeMeasure (ε : ℝ≥0) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun u : ℝ => u ^ (-σ)) (perturbedRiemannPrimeMeasure ε) := by
  exact (integrable_rpow_riemannPrimeMeasure hσ).add_measure
    ((integrable_rpow_continuousPrimeMeasure (by linarith)).smul_measure
      ENNReal.coe_ne_top)

/-- The logarithm of the Euler transform acquires the explicit rational term. -/
theorem measureDirichlet_perturbedRiemannPrimeMeasure (ε : ℝ≥0) {s : ℂ}
    (hs : 1 < s.re) :
    measureDirichlet (perturbedRiemannPrimeMeasure ε) s =
      measureDirichlet riemannPrimeMeasure s + (ε : ℂ) / (s + 1) ^ 2 := by
  have hP := integrable_measureMellin_of_moment
    (measure_mono_null Iio_subset_Iic_self riemannPrimeMeasure_Iic_one_eq_zero)
    (integrable_rpow_riemannPrimeMeasure hs)
  have hQ := integrable_mellin_continuousPrimeMeasure (s := s) (by linarith)
  rw [perturbedRiemannPrimeMeasure, measureDirichlet,
    integral_add_measure hP (hQ.smul_measure ENNReal.coe_ne_top), integral_smul_measure]
  change measureDirichlet riemannPrimeMeasure s +
    (ε : ℝ≥0∞).toReal • measureDirichlet continuousPrimeMeasure s = _
  rw [measureDirichlet_continuousPrimeMeasure (by linarith)]
  simp only [ENNReal.coe_toReal, Complex.real_smul]
  ring

/-- The positive Euler measure has the stated zeta transform throughout its half-plane
of absolute convergence. -/
theorem measureDirichlet_perturbedRiemannIntegerMeasure (ε : ℝ≥0) {s : ℂ}
    (hs : 1 < s.re) :
    measureDirichlet (beurlingIntegerMeasure (perturbedRiemannPrimeMeasure ε)) s =
      continuousEulerZeta ε s := by
  rw [measureDirichlet_beurlingIntegerMeasure (perturbedRiemannPrimeMeasure_Iic_one ε)
    (integrable_rpow_perturbedRiemannPrimeMeasure ε hs),
    measureDirichlet_perturbedRiemannPrimeMeasure ε hs, Complex.exp_add,
    exp_measureDirichlet_riemannPrimeMeasure hs]
  rfl

/-- No nonzero continuous perturbation gives back the classical prime measure. -/
theorem perturbedRiemannPrimeMeasure_eq_iff (ε : ℝ≥0) :
    perturbedRiemannPrimeMeasure ε = riemannPrimeMeasure ↔ ε = 0 := by
  constructor
  · intro h
    have hh := congrArg (fun P : Measure ℝ => measureDirichlet P (2 : ℂ)) h
    rw [measureDirichlet_perturbedRiemannPrimeMeasure ε (by norm_num)] at hh
    have hz := add_eq_left.mp hh
    have he : (ε : ℂ) = 0 := (div_eq_zero_iff.mp hz).resolve_right (by norm_num)
    exact_mod_cast he
  · rintro rfl
    simp [perturbedRiemannPrimeMeasure]

/-- The deformation preserves every zero, since its multiplier never vanishes. -/
theorem continuousEulerZeta_eq_zero_iff (ε : ℝ≥0) (s : ℂ) :
    continuousEulerZeta ε s = 0 ↔ riemannZeta s = 0 := by
  simp only [continuousEulerZeta, mul_eq_zero, Complex.exp_ne_zero, or_false]

#print axioms measureDirichlet_perturbedRiemannIntegerMeasure
#print axioms continuousEulerZeta_eq_zero_iff

end GaloisForLFunctions.EulerFETransportTheory

import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.ScaleAveragingRemovesFourierZeros
import GaloisForLFunctions.BiScaleUncertainty.PairingRecurrenceLaw
import GaloisForLFunctions.RHTower.WeilPrimeFreeTest

/-!
# A scale-averaged logarithmic Denjoy–Carleman profile

The autocorrelation of the sinc-product profile has nonnegative Fourier
transform. Averaging its dilations removes real Fourier zeros while retaining
compact support and the logarithmic Denjoy–Carleman derivative bounds.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff Convolution FourierTransform

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

theorem sincProfile_nonneg (x : ℝ) : 0 ≤ sincProfile x := by
  have havg {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u) {a : ℝ} (ha : 0 < a) (u : ℝ) :
      0 ≤ steklovAvg a f u := by
    apply mul_nonneg (by positivity : 0 ≤ (2 * a)⁻¹)
    exact intervalIntegral.integral_nonneg (by linarith) (fun t _ => hf (u + t))
  have hbox {β : ℝ → ℝ} (hβ : ∀ u, 0 ≤ β u) : ∀ m u, 0 ≤ boxStek β m u := by
    intro m
    induction m with
    | zero => exact hβ
    | succ m ih => exact havg ih (sincRadius_pos m)
  apply le_of_tendsto (tendstoUniformly_boxSeq.tendsto_at x)
  apply Filter.Eventually.of_forall
  intro M
  apply hbox (m := M + 1)
  intro u
  exact mul_nonneg (inv_nonneg.mpr (steklovRadius_pos M).le) (steklovBase_nonneg _)

theorem integral_abs_sincProfile : ∫ x, |sincProfile x| = 1 := by
  simp_rw [abs_of_nonneg (sincProfile_nonneg _)]
  exact integral_sincProfile

private theorem integrable_sincProfile : Integrable sincProfile :=
  contDiff_sincProfile.continuous.integrable_of_hasCompactSupport hasCompactSupport_sincProfile

private theorem hasCompactSupport_sincProfile_derivative (q : ℕ) :
    HasCompactSupport (iteratedDeriv q sincProfile) := by
  induction q with
  | zero => simpa only [iteratedDeriv_zero] using hasCompactSupport_sincProfile
  | succ q ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- Autocorrelation of the unit-mass sinc-product profile. -/
def sincCorrelation : ℝ → ℝ :=
  (fun u => sincProfile (-u)) ⋆[ContinuousLinearMap.mul ℝ ℝ] sincProfile

theorem sincCorrelation_eq_integral (x : ℝ) :
    sincCorrelation x = ∫ u, sincProfile u * sincProfile (u + x) := by
  unfold sincCorrelation convolution
  simp only [ContinuousLinearMap.mul_apply']
  rw [← integral_neg_eq_self (fun u => sincProfile u * sincProfile (u + x))]
  congr 1
  funext u
  rw [show -u + x = x - u by ring]

theorem contDiff_sincCorrelation : ContDiff ℝ ∞ sincCorrelation :=
  hasCompactSupport_sincProfile.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    integrable_sincProfile.comp_neg.locallyIntegrable contDiff_sincProfile

theorem sincCorrelation_nonneg (x : ℝ) : 0 ≤ sincCorrelation x := by
  rw [sincCorrelation_eq_integral]
  exact integral_nonneg fun u => mul_nonneg (sincProfile_nonneg u) (sincProfile_nonneg (u + x))

theorem sincCorrelation_vanishesOff : ∀ x, 2 < |x| → sincCorrelation x = 0 := by
  intro x hx
  rw [sincCorrelation_eq_integral]
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro u
  by_cases hu : 1 < |u|
  · rw [sincProfile_vanishesOff u hu, zero_mul]
  · have hux : 1 < |u + x| := by
      have ht := abs_sub_abs_le_abs_sub x (-u)
      rw [abs_neg, sub_neg_eq_add, add_comm x u] at ht
      linarith only [hx, le_of_not_gt hu, ht]
    rw [sincProfile_vanishesOff (u + x) hux, mul_zero]

theorem hasCompactSupport_sincCorrelation : HasCompactSupport sincCorrelation :=
  hasCompactSupport_of_vanishes sincCorrelation_vanishesOff

theorem integral_sincCorrelation : ∫ x, sincCorrelation x = 1 := by
  rw [sincCorrelation, integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
    integrable_sincProfile.comp_neg integrable_sincProfile]
  simp only [ContinuousLinearMap.mul_apply', integral_neg_eq_self, integral_sincProfile, one_mul]

theorem fourier_sincCorrelation (ξ : ℝ) :
    𝓕 (fun x => (sincCorrelation x : ℂ)) ξ =
      ((‖𝓕 (fun x => (sincProfile x : ℂ)) ξ‖ ^ 2 : ℝ) : ℂ) := by
  have heq : sincCorrelation = RHTower.ArchimedeanAnomaly.autocorr sincProfile :=
    funext sincCorrelation_eq_integral
  simp_rw [RHTower.WeilDeletion.fourier_eq_paperFT]
  rw [heq, BiScaleUncertainty.ChebyshevGauge.paperFT_autocorr
    contDiff_sincProfile.continuous hasCompactSupport_sincProfile,
    Complex.conj_ofReal, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem iteratedDeriv_sincCorrelation (q : ℕ) :
    iteratedDeriv q sincCorrelation =
      (fun u => sincProfile (-u)) ⋆[ContinuousLinearMap.mul ℝ ℝ]
        iteratedDeriv q sincProfile := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    have hfq : ContDiff ℝ ∞ (iteratedDeriv q sincProfile) := by
      rw [iteratedDeriv_eq_iterate]
      exact contDiff_sincProfile.iterate_deriv q
    exact (HasCompactSupport.hasDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      integrable_sincProfile.comp_neg.locallyIntegrable
      (hasCompactSupport_sincProfile_derivative q) (hfq.of_le (natCast_le_infty 1)) x).deriv

theorem abs_iteratedDeriv_sincCorrelation_le (q : ℕ) (x : ℝ) :
    |iteratedDeriv q sincCorrelation x| ≤ 2 * 12 ^ q * dcLogWeight q := by
  rw [iteratedDeriv_sincCorrelation]
  simp only [convolution, ContinuousLinearMap.mul_apply']
  let B : ℝ := 2 * 12 ^ q * dcLogWeight q
  have hcont : Continuous (iteratedDeriv q sincProfile) :=
    contDiff_sincProfile.continuous_iteratedDeriv q (natCast_le_infty q)
  have hi : Integrable (fun u => |sincProfile (-u) * iteratedDeriv q sincProfile (x - u)|) :=
    (((contDiff_sincProfile.continuous.comp continuous_neg).mul
      (hcont.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      ((hasCompactSupport_sincProfile.comp_homeomorph (Homeomorph.neg ℝ)).mul_right)).abs
  calc |∫ u, sincProfile (-u) * iteratedDeriv q sincProfile (x - u)|
      ≤ ∫ u, |sincProfile (-u) * iteratedDeriv q sincProfile (x - u)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u, |sincProfile (-u)| * B := by
      apply integral_mono hi (integrable_sincProfile.comp_neg.abs.mul_const B)
      intro u
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_iteratedDeriv_sincProfile_le q _) (abs_nonneg _)
    _ = B := by
      rw [integral_mul_const, integral_neg_eq_self, integral_abs_sincProfile, one_mul]

/-- The unit-mass scale average, supported in `[-4,4]`. -/
def averagedSincProfile : ℝ → ℝ := scaleAverage sincCorrelation

theorem contDiff_averagedSincProfile : ContDiff ℝ ∞ averagedSincProfile :=
  contDiff_scaleAverage contDiff_sincCorrelation

theorem averagedSincProfile_nonneg (x : ℝ) : 0 ≤ averagedSincProfile x :=
  scaleAverage_nonneg sincCorrelation_nonneg x

theorem averagedSincProfile_vanishesOff : ∀ x, 4 < |x| → averagedSincProfile x = 0 :=
  scaleAverage_vanishesOff (by norm_num : (0 : ℝ) ≤ 2) sincCorrelation_vanishesOff

theorem hasCompactSupport_averagedSincProfile : HasCompactSupport averagedSincProfile :=
  hasCompactSupport_of_vanishes averagedSincProfile_vanishesOff

theorem abs_iteratedDeriv_averagedSincProfile_le (q : ℕ) (x : ℝ) :
    |iteratedDeriv q averagedSincProfile x| ≤ 4 * 12 ^ q * dcLogWeight q := by
  have h := abs_iteratedDeriv_scaleAverage_le contDiff_sincCorrelation q
    (abs_iteratedDeriv_sincCorrelation_le q) x
  change |iteratedDeriv q averagedSincProfile x| ≤ _ at h
  linarith only [h]

/-- Scale averaging and autocorrelation retain the logarithmic derivative weight. -/
theorem integral_abs_iteratedDeriv_averagedSincProfile_le (q : ℕ) :
    ∫ x, |iteratedDeriv q averagedSincProfile x| ≤ 32 * 12 ^ q * dcLogWeight q := by
  have hd : Continuous (iteratedDeriv q averagedSincProfile) :=
    contDiff_averagedSincProfile.continuous_iteratedDeriv q (natCast_le_infty q)
  have hv : ∀ x, x ∉ Set.Icc (-4 : ℝ) 4 → averagedSincProfile x = 0 := fun x hx =>
    averagedSincProfile_vanishesOff x (lt_of_not_ge fun h => hx (abs_le.mp h))
  have hds : SupportedIn 4 (iteratedDeriv q averagedSincProfile) := fun x hx =>
    iteratedDeriv_eq_zero_of_vanish hv q fun h => by
      have ha := abs_le.mpr h
      linarith only [ha, hx]
  have h := integral_abs_le_of_bound hd (hasCompactSupport_of_vanishes hds)
    (abs_iteratedDeriv_averagedSincProfile_le q) hds (by norm_num : (0 : ℝ) ≤ 4)
  linarith only [h]

end GaloisForLFunctions.TransMetzlerWeilPositivity

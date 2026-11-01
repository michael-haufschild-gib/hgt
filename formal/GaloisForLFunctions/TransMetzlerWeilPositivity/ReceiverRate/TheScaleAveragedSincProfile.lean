import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.ScaleAveragingRemovesFourierZeros
import GaloisForLFunctions.BiScaleUncertainty.PairingRecurrenceLaw
import GaloisForLFunctions.RHTower.WeilPrimeFreeTest
import GaloisForLFunctions.RHTower.SecondMoment
import GaloisForLFunctions.HTGeometry.CompactFourierEntire

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

/-- Its transform is the nonnegative average of sinc spectral energy. -/
theorem fourier_averagedSincProfile (ξ : ℝ) :
    𝓕 (fun x => (averagedSincProfile x : ℂ)) ξ =
      ((scaleBandAverage (fun u => ‖𝓕 (fun x => (sincProfile x : ℂ)) u‖ ^ 2) ξ : ℝ) : ℂ) := by
  rw [averagedSincProfile, fourier_scaleAverage contDiff_sincCorrelation.continuous
    (contDiff_sincCorrelation.continuous.integrable_of_hasCompactSupport
      hasCompactSupport_sincCorrelation)]
  simp_rw [fourier_sincCorrelation, ← Complex.ofReal_mul]
  exact intervalIntegral.integral_ofReal

private theorem fourier_sincProfile_zero :
    𝓕 (fun x => (sincProfile x : ℂ)) 0 = 1 := by
  rw [HTGeometry.fourier_zero_eq_integral, integral_ofReal, integral_sincProfile,
    Complex.ofReal_one]

/-- Unit mass is unchanged by the average of normalized dilations. -/
theorem integral_averagedSincProfile : ∫ x, averagedSincProfile x = 1 := by
  have h := fourier_averagedSincProfile 0
  rw [HTGeometry.fourier_zero_eq_integral, integral_ofReal] at h
  simp only [scaleBandAverage, mul_zero, fourier_sincProfile_zero, norm_one, one_pow,
    mul_one] at h
  rw [intervalIntegral.integral_const_mul, integral_id] at h
  norm_num at h
  exact_mod_cast h

private theorem exists_fourier_sincProfile_ne_zero_between {a b : ℝ} (hab : a < b) :
    ∃ u ∈ Set.Ioo a b, 𝓕 (fun x => (sincProfile x : ℂ)) u ≠ 0 := by
  let G : ℂ → ℂ := fun z =>
    Zeta23.paperFT (fun x => (sincProfile x : ℂ)) ((-(2 * Real.pi) : ℂ) * z)
  have hd : Differentiable ℂ G :=
    (_root_.RHTower.EvenSector.differentiable_paperFT_of_compact
      (Complex.continuous_ofReal.comp contDiff_sincProfile.continuous)
      (hasCompactSupport_sincProfile.comp_left Complex.ofReal_zero)).comp
        (differentiable_const.mul differentiable_id)
  have he (u : ℝ) : G (u : ℂ) = 𝓕 (fun x => (sincProfile x : ℂ)) u := by
    rw [RHTower.WeilDeletion.fourier_eq_paperFT]
    dsimp only [G]
    congr 1
    push_cast
    ring
  by_contra hn
  push_neg at hn
  have hz := HTGeometry.entire_eq_zero_of_vanishing_on_real_interval
    (t₀ := (a + b) / 2) hd (show 0 < (b - a) / 2 by linarith only [hab])
    (fun u hu => by
      rw [he]
      exact hn u ⟨by linarith only [(abs_lt.mp hu).1],
        by linarith only [(abs_lt.mp hu).2]⟩) (0 : ℂ)
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by rfl, he, fourier_sincProfile_zero] at hz
  exact one_ne_zero hz

private theorem integral_fourier_sincProfile_sq_pos {a b : ℝ} (hab : a < b) :
    0 < ∫ u in a..b, ‖𝓕 (fun x => (sincProfile x : ℂ)) u‖ ^ 2 := by
  apply _root_.RHTower.intervalIntegral_pos_of_continuous_nonneg_of_exists_pos
    (continuous_norm_fourier_sincProfile.pow 2) (fun u _ => sq_nonneg _)
  obtain ⟨u, hu, hne⟩ := exists_fourier_sincProfile_ne_zero_between hab
  exact ⟨u, hu, sq_pos_of_pos (norm_pos_iff.mpr hne)⟩

/-- Averaging over a nondegenerate scale interval removes every real Fourier zero. -/
theorem fourier_averagedSincProfile_re_pos (ξ : ℝ) :
    0 < (𝓕 (fun x => (averagedSincProfile x : ℂ)) ξ).re := by
  rw [fourier_averagedSincProfile, Complex.ofReal_re]
  have hc : Continuous (fun u => ‖𝓕 (fun x => (sincProfile x : ℂ)) u‖ ^ 2) :=
    continuous_norm_fourier_sincProfile.pow 2
  rcases lt_trichotomy ξ 0 with hξ | rfl | hξ
  · have hp := integral_fourier_sincProfile_sq_pos (show 2 * ξ < ξ by linarith only [hξ])
    rw [intervalIntegral.integral_symm, ← mul_scaleBandAverage _ hc] at hp
    nlinarith only [hp, hξ]
  · simp only [scaleBandAverage, mul_zero, fourier_sincProfile_zero, norm_one, one_pow,
      mul_one]
    rw [intervalIntegral.integral_const_mul, integral_id]
    norm_num
  · have hp := integral_fourier_sincProfile_sq_pos (show ξ < 2 * ξ by linarith only [hξ])
    rw [← mul_scaleBandAverage _ hc] at hp
    exact (mul_pos_iff_of_pos_left hξ).mp hp

theorem fourier_averagedSincProfile_ne_zero (ξ : ℝ) :
    𝓕 (fun x => (averagedSincProfile x : ℂ)) ξ ≠ 0 := by
  intro h
  have hp := fourier_averagedSincProfile_re_pos ξ
  rw [h, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

theorem norm_fourier_averagedSincProfile_eq_re (ξ : ℝ) :
    ‖𝓕 (fun x => (averagedSincProfile x : ℂ)) ξ‖ =
      (𝓕 (fun x => (averagedSincProfile x : ℂ)) ξ).re := by
  have hp := fourier_averagedSincProfile_re_pos ξ
  rw [fourier_averagedSincProfile, Complex.ofReal_re] at hp ⊢
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]

/-- The integrated sinc lower bound gives a pointwise logarithmic Fourier floor. -/
theorem eventually_fourier_averagedSincProfile_re_ge :
    ∀ᶠ ξ : ℝ in atTop,
      Real.exp (-(sincTailConst * (ξ / Real.log ξ ^ 2))) ≤
        (𝓕 (fun x => (averagedSincProfile x : ℂ)) ξ).re := by
  simpa only [fourier_averagedSincProfile, Complex.ofReal_re] using
    eventually_scaleBandAverage_sinc_ge

/-- One explicit floor controls the full Montgomery–Vaughan frequency band. -/
theorem eventually_fourier_averagedSincProfile_band_ge :
    ∀ᶠ c : ℝ in atTop, ∀ t ∈ Set.Icc c (101 * c),
      Real.exp (-(101 * sincTailConst * (c / Real.log c ^ 2))) ≤
        (𝓕 (fun x => (averagedSincProfile x : ℂ)) t).re := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp eventually_fourier_averagedSincProfile_re_ge
  filter_upwards [eventually_ge_atTop A, eventually_gt_atTop (Real.exp 1)] with c hcA hc
  have hc0 : 0 < c := (Real.exp_pos 1).trans hc
  have hlc : 0 < Real.log c := by
    have h := Real.log_le_log (Real.exp_pos 1) hc.le
    rw [Real.log_exp] at h
    linarith only [h]
  intro t ht
  have ht0 : 0 < t := hc0.trans_le ht.1
  have hlog : Real.log c ≤ Real.log t := Real.log_le_log hc0 ht.1
  have hden : Real.log c ^ 2 ≤ Real.log t ^ 2 := pow_le_pow_left₀ hlc.le hlog 2
  have hratio : t / Real.log t ^ 2 ≤ 101 * (c / Real.log c ^ 2) := by
    calc
      _ ≤ t / Real.log c ^ 2 :=
        div_le_div_of_nonneg_left ht0.le (sq_pos_of_pos hlc) hden
      _ ≤ (101 * c) / Real.log c ^ 2 :=
        div_le_div_of_nonneg_right ht.2 (sq_nonneg _)
      _ = 101 * (c / Real.log c ^ 2) := by ring
  apply le_trans (Real.exp_le_exp.mpr ?_) (hA t (hcA.trans ht.1))
  have h := mul_le_mul_of_nonneg_left hratio sincTailConst_pos.le
  nlinarith only [h]

end GaloisForLFunctions.TransMetzlerWeilPositivity

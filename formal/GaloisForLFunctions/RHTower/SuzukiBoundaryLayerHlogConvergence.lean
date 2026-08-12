import GaloisForLFunctions.RHTower.SuzukiBoundaryLayerCutoff
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral

/-!
# Suzuki boundary layers converge in `H^log`

This module closes the analytic estimate in Suzuki's equation (3.2).  It derives, for the explicit
product cutoff, the two simultaneous Fourier bounds

* the `L¹` bound from total boundary width;
* the `1 / |ξ|` bound from interval integration by parts, including endpoint jumps.

The general envelope theorem then gives convergence of the exact logarithmically weighted Fourier
energy.  No distributional derivative of the zero extension is used: its endpoint jumps are the
two explicit boundary terms in integration by parts.
-/

open MeasureTheory Set Complex intervalIntegral Filter Topology
open scoped ENNReal FourierTransform ContDiff

noncomputable section

namespace RHTower

def suzukiBoundaryErrorProfile (a ε κ x : ℝ) : ℂ :=
  suzukiApertureMode κ x * (1 - suzukiBoundaryCutoff a ε x : ℂ)

def suzukiBoundaryErrorProfileDeriv (a ε κ x : ℝ) : ℂ :=
  Complex.I * (κ : ℂ) * suzukiApertureMode κ x *
      (1 - suzukiBoundaryCutoff a ε x : ℂ) -
    suzukiApertureMode κ x *
      Complex.ofReal (deriv (suzukiBoundaryCutoff a ε) x)

theorem suzukiBoundaryError_eq_indicator_profile (a ε κ : ℝ) :
    suzukiBoundaryError a ε κ =
      (Icc (-a) a).indicator (suzukiBoundaryErrorProfile a ε κ) := rfl

theorem hasDerivAt_suzukiBoundaryErrorProfile (a ε κ x : ℝ) :
    HasDerivAt (suzukiBoundaryErrorProfile a ε κ)
      (suzukiBoundaryErrorProfileDeriv a ε κ x) x := by
  have hmode := hasDerivAt_suzukiApertureMode κ x
  have hcut : HasDerivAt (fun y : ℝ => (suzukiBoundaryCutoff a ε y : ℂ))
      (Complex.ofReal (deriv (suzukiBoundaryCutoff a ε) x)) x :=
    (hasDerivAt_suzukiBoundaryCutoff a ε x).ofReal_comp
  have hone : HasDerivAt (fun _ : ℝ => (1 : ℂ)) 0 x := hasDerivAt_const x 1
  unfold suzukiBoundaryErrorProfile suzukiBoundaryErrorProfileDeriv
  convert hmode.mul (hone.sub hcut) using 1 <;>
    first | rfl | simp only [Pi.add_apply, Pi.neg_apply, zero_add, mul_neg, sub_eq_add_neg]

theorem continuous_suzukiBoundaryErrorProfileDeriv (a ε κ : ℝ) :
    Continuous (suzukiBoundaryErrorProfileDeriv a ε κ) := by
  unfold suzukiBoundaryErrorProfileDeriv
  exact (((continuous_const.mul continuous_const).mul
      (contDiff_suzukiApertureMode κ).continuous).mul
        (continuous_const.sub
          ((contDiff_suzukiBoundaryCutoff a ε).continuousLinearMap_comp
            Complex.ofRealCLM).continuous)).sub
    ((contDiff_suzukiApertureMode κ).continuous.mul
      (Complex.ofRealCLM.continuous.comp
        (continuous_deriv_suzukiBoundaryCutoff a ε)))

theorem norm_suzukiBoundaryErrorProfileDeriv_le (a ε κ x : ℝ) :
    ‖suzukiBoundaryErrorProfileDeriv a ε κ x‖ ≤
      |κ| * ‖suzukiBoundaryErrorProfile a ε κ x‖ +
        |deriv (suzukiBoundaryCutoff a ε) x| := by
  unfold suzukiBoundaryErrorProfileDeriv suzukiBoundaryErrorProfile
  calc
    ‖Complex.I * (κ : ℂ) * suzukiApertureMode κ x *
          (1 - suzukiBoundaryCutoff a ε x : ℂ) -
        suzukiApertureMode κ x *
          Complex.ofReal (deriv (suzukiBoundaryCutoff a ε) x)‖
        ≤ ‖Complex.I * (κ : ℂ) * suzukiApertureMode κ x *
            (1 - suzukiBoundaryCutoff a ε x : ℂ)‖ +
          ‖suzukiApertureMode κ x *
            Complex.ofReal (deriv (suzukiBoundaryCutoff a ε) x)‖ :=
            norm_sub_le _ _
    _ = |κ| * ‖suzukiApertureMode κ x *
            (1 - suzukiBoundaryCutoff a ε x : ℂ)‖ +
          |deriv (suzukiBoundaryCutoff a ε) x| := by
            simp only [norm_mul, norm_suzukiApertureMode, Complex.norm_I,
              Complex.norm_real, Real.norm_eq_abs, one_mul]
            ring

theorem norm_suzukiBoundaryErrorProfile_endpoint_left {a ε κ : ℝ} (hε : 0 < ε) :
    ‖suzukiBoundaryErrorProfile a ε κ (-a)‖ = 1 := by
  unfold suzukiBoundaryErrorProfile
  rw [suzukiBoundaryCutoff_eq_zero_of_le_neg hε (le_refl _), norm_mul,
    norm_suzukiApertureMode]
  simp

theorem norm_suzukiBoundaryErrorProfile_endpoint_right {a ε κ : ℝ} (hε : 0 < ε) :
    ‖suzukiBoundaryErrorProfile a ε κ a‖ = 1 := by
  unfold suzukiBoundaryErrorProfile
  rw [suzukiBoundaryCutoff_eq_zero_of_aperture_le hε (le_refl _), norm_mul,
    norm_suzukiApertureMode]
  simp

theorem intervalIntegral_norm_suzukiBoundaryErrorProfile_eq {a ε κ : ℝ} (ha : 0 ≤ a) :
    (∫ x in (-a)..a, ‖suzukiBoundaryErrorProfile a ε κ x‖) =
      ∫ x : ℝ, ‖suzukiBoundaryError a ε κ x‖ := by
  rw [intervalIntegral.integral_of_le (by linarith),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← MeasureTheory.integral_indicator measurableSet_Icc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  unfold suzukiBoundaryError suzukiBoundaryErrorProfile
  by_cases hx : x ∈ Icc (-a) a <;> simp [hx]

theorem intervalIntegral_abs_deriv_suzukiBoundaryCutoff_le
    {C a ε : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hε : 0 < ε)
    (hbound : ∀ {a ε x : ℝ}, 0 < ε →
      |deriv (suzukiBoundaryCutoff a ε) x| ≤ 2 * C / ε) :
    (∫ x in (-a)..a, |deriv (suzukiBoundaryCutoff a ε) x|) ≤ 4 * C := by
  have hmaj := integrable_suzukiBoundaryCutoffDerivMajorant C a ε
  have hpoint : ∀ x : ℝ, |deriv (suzukiBoundaryCutoff a ε) x| ≤
      suzukiBoundaryCutoffDerivMajorant C a ε x :=
    fun x => abs_deriv_suzukiBoundaryCutoff_le_majorant hC hε hbound
  have hderivInt : Integrable (fun x : ℝ => |deriv (suzukiBoundaryCutoff a ε) x|) := by
    refine Integrable.mono' hmaj
      ((continuous_abs.comp (continuous_deriv_suzukiBoundaryCutoff a ε)).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact hpoint x
  rw [intervalIntegral.integral_of_le (by linarith),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  calc
    (∫ x in Icc (-a) a, |deriv (suzukiBoundaryCutoff a ε) x|)
        ≤ ∫ x : ℝ, |deriv (suzukiBoundaryCutoff a ε) x| :=
          integral_mono_measure Measure.restrict_le_self
            (ae_of_all _ fun x => abs_nonneg _) hderivInt
    _ ≤ ∫ x : ℝ, suzukiBoundaryCutoffDerivMajorant C a ε x :=
          integral_mono hderivInt hmaj hpoint
    _ = 4 * C := integral_suzukiBoundaryCutoffDerivMajorant hε

theorem intervalIntegral_norm_suzukiBoundaryErrorProfileDeriv_le
    {C a ε κ : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hε : 0 < ε) (hεa : ε ≤ a)
    (hbound : ∀ {a ε x : ℝ}, 0 < ε →
      |deriv (suzukiBoundaryCutoff a ε) x| ≤ 2 * C / ε) :
    (∫ x in (-a)..a, ‖suzukiBoundaryErrorProfileDeriv a ε κ x‖) ≤
      2 * |κ| * ε + 4 * C := by
  have hprofCont : Continuous fun x : ℝ => ‖suzukiBoundaryErrorProfile a ε κ x‖ :=
    (continuous_suzukiBoundaryErrorProfile a ε κ).norm
  have hderivAbsCont : Continuous fun x : ℝ =>
      |deriv (suzukiBoundaryCutoff a ε) x| :=
    continuous_abs.comp (continuous_deriv_suzukiBoundaryCutoff a ε)
  have hprofInt : IntervalIntegrable (fun x : ℝ =>
      |κ| * ‖suzukiBoundaryErrorProfile a ε κ x‖) volume (-a) a :=
    (continuous_const.mul hprofCont).intervalIntegrable _ _
  have hcutInt : IntervalIntegrable (fun x : ℝ =>
      |deriv (suzukiBoundaryCutoff a ε) x|) volume (-a) a :=
    hderivAbsCont.intervalIntegrable _ _
  have hmain := intervalIntegral.integral_mono (a := -a) (b := a) (μ := volume) (by linarith)
    ((continuous_suzukiBoundaryErrorProfileDeriv a ε κ).norm.intervalIntegrable _ _)
    (hprofInt.add hcutInt)
    (fun x => norm_suzukiBoundaryErrorProfileDeriv_le a ε κ x)
  rw [intervalIntegral.integral_add hprofInt hcutInt,
    intervalIntegral.integral_const_mul] at hmain
  have hprof : (∫ x in (-a)..a, ‖suzukiBoundaryErrorProfile a ε κ x‖) ≤ 2 * ε := by
    rw [intervalIntegral_norm_suzukiBoundaryErrorProfile_eq ha.le]
    exact integral_norm_suzukiBoundaryError_le_two_mul hε hεa
  have hcut : (∫ x in (-a)..a, |deriv (suzukiBoundaryCutoff a ε) x|) ≤ 4 * C :=
    intervalIntegral_abs_deriv_suzukiBoundaryCutoff_le ha.le hC hε hbound
  calc
    (∫ x in (-a)..a, ‖suzukiBoundaryErrorProfileDeriv a ε κ x‖)
        ≤ |κ| * (∫ x in (-a)..a, ‖suzukiBoundaryErrorProfile a ε κ x‖) +
          ∫ x in (-a)..a, |deriv (suzukiBoundaryCutoff a ε) x| := hmain
    _ ≤ |κ| * (2 * ε) + 4 * C :=
      add_le_add (mul_le_mul_of_nonneg_left hprof (abs_nonneg κ)) hcut
    _ = 2 * |κ| * ε + 4 * C := by ring

theorem fourier_suzukiBoundaryError_eq_intervalIntegral {a ε κ ξ : ℝ} (ha : 0 ≤ a) :
    𝓕 (suzukiBoundaryError a ε κ) ξ =
      ∫ x in (-a)..a, boundaryFourierPhase ξ x *
        suzukiBoundaryErrorProfile a ε κ x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [show (∫ v : ℝ,
      Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) •
        suzukiBoundaryError a ε κ v) =
      ∫ v in Icc (-a) a,
        Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) •
          suzukiBoundaryErrorProfile a ε κ v by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with v
    unfold suzukiBoundaryError
    by_cases hv : v ∈ Icc (-a) a <;> simp [hv, suzukiBoundaryErrorProfile]]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  apply intervalIntegral.integral_congr
  intro x hx
  change Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) *
      suzukiBoundaryErrorProfile a ε κ x =
    boundaryFourierPhase ξ x * suzukiBoundaryErrorProfile a ε κ x
  congr 1
  unfold boundaryFourierPhase
  congr 1
  push_cast
  ring

theorem norm_fourier_suzukiBoundaryError_le_two_mul {a ε κ ξ : ℝ}
    (hε : 0 < ε) (hεa : ε ≤ a) :
    ‖𝓕 (suzukiBoundaryError a ε κ) ξ‖ ≤ 2 * ε := by
  exact (GaloisForLFunctions.HTGeometry.norm_fourierReal_le_integral_norm
    (suzukiBoundaryError a ε κ) ξ).trans
      (integral_norm_suzukiBoundaryError_le_two_mul hε hεa)

theorem norm_fourier_suzukiBoundaryError_le_tail
    {C a ε κ ξ : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hε : 0 < ε) (hεa : ε ≤ a)
    (hbound : ∀ {a ε x : ℝ}, 0 < ε →
      |deriv (suzukiBoundaryCutoff a ε) x| ≤ 2 * C / ε) (hξ : ξ ≠ 0) :
    ‖𝓕 (suzukiBoundaryError a ε κ) ξ‖ ≤
      (2 + 2 * |κ| * ε + 4 * C) / (2 * Real.pi * |ξ|) := by
  rw [fourier_suzukiBoundaryError_eq_intervalIntegral ha.le]
  have hibp := norm_intervalFourier_le_boundary_add_integral_deriv
    (a := -a) (b := a) (ξ := ξ) (by linarith)
    (fun x hx => hasDerivAt_suzukiBoundaryErrorProfile a ε κ x)
    (continuous_suzukiBoundaryErrorProfileDeriv a ε κ).continuousOn hξ
  rw [norm_suzukiBoundaryErrorProfile_endpoint_left hε,
    norm_suzukiBoundaryErrorProfile_endpoint_right hε] at hibp
  have hderiv := intervalIntegral_norm_suzukiBoundaryErrorProfileDeriv_le
    (κ := κ) ha hC hε hεa hbound
  have hnum : 1 + 1 +
      (∫ x in (-a)..a, ‖suzukiBoundaryErrorProfileDeriv a ε κ x‖) ≤
        2 + 2 * |κ| * ε + 4 * C := by
    calc
      1 + 1 + (∫ x in (-a)..a, ‖suzukiBoundaryErrorProfileDeriv a ε κ x‖)
          ≤ 1 + 1 + (2 * |κ| * ε + 4 * C) := by linarith
      _ = 2 + 2 * |κ| * ε + 4 * C := by ring
  exact hibp.trans (div_le_div_of_nonneg_right hnum (by positivity))

def suzukiBoundaryErrorSequence (a κ : ℝ) (m : ℕ) : ℝ → ℂ :=
  suzukiBoundaryError a (suzukiBoundaryWidth a m) κ

/-- Exact simultaneous source bounds (3.3)--(3.4), with one constant independent of boundary
width and index. -/
theorem exists_uniform_fourier_envelope_suzukiBoundaryErrorSequence
    {a : ℝ} (ha : 0 < a) (κ : ℝ) :
    ∃ M : ℝ, ∀ m ξ, ξ ≠ 0 →
      ‖𝓕 (suzukiBoundaryErrorSequence a κ m) ξ‖ ≤
        min (2 / ((m : ℝ) + 1)) (|M| / |ξ|) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_deriv_bound_suzukiBoundaryCutoff
  let M : ℝ := (2 + 2 * |κ| * a + 4 * C) / (2 * Real.pi)
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ⟨M, fun m ξ hξ => le_min ?_ ?_⟩
  · have hε := suzukiBoundaryWidth_pos ha m
    have hεa := (suzukiBoundaryWidth_lt_aperture ha m).le
    have hinv : 0 ≤ 1 / ((m : ℝ) + 1) := by positivity
    exact (norm_fourier_suzukiBoundaryError_le_two_mul hε hεa).trans
      ((two_mul_suzukiBoundaryWidth_le_inv_succ ha m).trans (by
        have hden : 0 < (m : ℝ) + 1 := by positivity
        exact (div_le_div_iff₀ hden hden).2 (by nlinarith)))
  · have hε := suzukiBoundaryWidth_pos ha m
    have hεa := (suzukiBoundaryWidth_lt_aperture ha m).le
    have htail := norm_fourier_suzukiBoundaryError_le_tail
      (κ := κ) ha hC hε hεa hbound hξ
    have hnum : 2 + 2 * |κ| * suzukiBoundaryWidth a m + 4 * C ≤
        2 + 2 * |κ| * a + 4 * C := by
      nlinarith [abs_nonneg κ, suzukiBoundaryWidth_lt_aperture ha m]
    rw [abs_of_nonneg hM]
    dsimp [M]
    calc
      ‖𝓕 (suzukiBoundaryErrorSequence a κ m) ξ‖
          ≤ (2 + 2 * |κ| * suzukiBoundaryWidth a m + 4 * C) /
              (2 * Real.pi * |ξ|) := htail
      _ ≤ (2 + 2 * |κ| * a + 4 * C) / (2 * Real.pi * |ξ|) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = ((2 + 2 * |κ| * a + 4 * C) / (2 * Real.pi)) / |ξ| := by
        field_simp [abs_ne_zero.mpr hξ, Real.pi_ne_zero]

/-- Each explicit boundary error has finite logarithmically weighted Fourier energy.  Positivity
of the aperture is bundled, so this literature endpoint has no proposition-valued premise. -/
theorem integrable_suzukiBoundaryErrorSequence_hlogEnergy
    (a : SuzukiPositiveAperture) (κ : ℝ) (m : ℕ) :
    Integrable (fun ξ : ℝ => suzukiLogWeight ξ *
      ‖𝓕 (suzukiBoundaryErrorSequence a.1 κ m) ξ‖ ^ 2) := by
  obtain ⟨M, hM⟩ :=
    exists_uniform_fourier_envelope_suzukiBoundaryErrorSequence a.2 κ
  exact integrable_suzukiLogWeight_norm_sq_of_fourier_envelope
    (𝓕 (suzukiBoundaryErrorSequence a.1 κ m)) m M
    (GaloisForLFunctions.RHTower.continuous_fourier_of_integrable
      (integrable_suzukiBoundaryError a.1 (suzukiBoundaryWidth a.1 m) κ)).aestronglyMeasurable
    (hM m)

/-- **Suzuki equation (3.2), analytic content.**  The explicit smooth endpoint cutoffs of every
aperture exponential converge to the zero-extended mode in the exact logarithmic Fourier energy. -/
theorem tendsto_suzukiBoundaryErrorSequence_hlogEnergy
    {a : ℝ} (ha : 0 < a) (κ : ℝ) :
    Tendsto (fun m : ℕ => ∫ ξ : ℝ,
      suzukiLogWeight ξ * ‖𝓕 (suzukiBoundaryErrorSequence a κ m) ξ‖ ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := exists_uniform_fourier_envelope_suzukiBoundaryErrorSequence ha κ
  exact tendsto_integral_suzukiLogWeight_norm_sq_of_fourier_envelope
    (fun m => 𝓕 (suzukiBoundaryErrorSequence a κ m)) M
    (fun m => (GaloisForLFunctions.RHTower.continuous_fourier_of_integrable
      (integrable_suzukiBoundaryError a (suzukiBoundaryWidth a m) κ)).aestronglyMeasurable)
    hM

/-- Suzuki's boundary-layer `H^log` convergence with aperture positivity carried intrinsically. -/
theorem tendsto_suzukiBoundaryErrorSequence_hlogEnergy_positiveAperture
    (a : SuzukiPositiveAperture) (κ : ℝ) :
    Tendsto (fun m : ℕ => ∫ ξ : ℝ,
      suzukiLogWeight ξ *
        ‖𝓕 (suzukiBoundaryErrorSequence a.1 κ m) ξ‖ ^ 2)
      atTop (𝓝 0) :=
  tendsto_suzukiBoundaryErrorSequence_hlogEnergy a.2 κ

end RHTower

end

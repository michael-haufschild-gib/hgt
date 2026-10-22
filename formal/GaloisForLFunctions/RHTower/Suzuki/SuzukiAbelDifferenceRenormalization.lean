import GaloisForLFunctions.RHTower.Suzuki.SuzukiAbelDifferenceEnergy
import GaloisForLFunctions.RHTower.Suzuki.SuzukiHlogDenseFormCore

open Complex Filter MeasureTheory Set
open FourierTransform
open scoped Topology

namespace RHTower

noncomputable section

theorem integrable_abs_log_abs_mul_norm_sq
    (F : SchwartzMap ℝ ℂ) :
    Integrable (fun xi : ℝ => |Real.log (|xi|)| * ‖F xi‖ ^ 2) := by
  let C : ℝ := SchwartzMap.seminorm ℂ 0 0 F
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hlocalLog : IntegrableOn (fun xi : ℝ => |Real.log (|xi|)|) (Ioc (-1 : ℝ) 1) := by
    have h := intervalIntegral.intervalIntegrable_log' (a := (-1 : ℝ)) (b := (1 : ℝ))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
    change Integrable (fun xi : ℝ => |Real.log (|xi|)|)
      (volume.restrict (Ioc (-1 : ℝ) 1))
    simpa only [Real.norm_eq_abs, Real.log_abs] using h.norm
  have hlocal : IntegrableOn
      (fun xi : ℝ => |Real.log (|xi|)| * ‖F xi‖ ^ 2) (Ioc (-1 : ℝ) 1) := by
    refine hlocalLog.mul_bdd (c := C ^ 2)
      (F.continuous.norm.pow 2).aestronglyMeasurable.restrict ?_
    filter_upwards with xi
    have hF := SchwartzMap.norm_le_seminorm ℂ F xi
    simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using
      pow_le_pow_left₀ (norm_nonneg _) hF 2
  have hext : IntegrableOn
      (fun xi : ℝ => |Real.log (|xi|)| * ‖F xi‖ ^ 2) ((Ioc (-1 : ℝ) 1)ᶜ) := by
    refine (F.integrable_suzukiLogWeight_mul_norm_sq.integrableOn).mono'
      ((Real.measurable_log.comp measurable_abs).abs.mul
        (F.continuous.norm.measurable.pow_const 2)).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.compl)] with xi hxi
    have habsone : 1 ≤ |xi| := by
      simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hxi
      rcases hxi with hle | hgt
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        exact hgt.le
    have hlog0 : 0 ≤ Real.log |xi| := Real.log_nonneg habsone
    have hweight : 0 ≤ suzukiLogWeight xi := suzukiLogWeight_nonneg xi
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_norm,
      abs_of_nonneg hlog0]
    unfold suzukiLogWeight
    rw [max_eq_left hlog0]
    nlinarith [sq_nonneg ‖F xi‖]
  have hall := hlocal.union hext
  rw [union_compl_self] at hall
  simpa only [integrableOn_univ] using hall

theorem integrable_abs_log_two_pi_mul_mul_norm_sq
    (F : SchwartzMap ℝ ℂ) :
    Integrable (fun xi : ℝ => |Real.log (|2 * Real.pi * xi|)| * ‖F xi‖ ^ 2) := by
  let C : ℝ := SchwartzMap.seminorm ℂ 0 0 F
  have hF2 : Integrable (fun xi : ℝ => ‖F xi‖ ^ 2) := by
    have hF1 : Integrable (fun xi : ℝ => ‖F xi‖) := F.integrable.norm
    simpa only [pow_two] using hF1.mul_bdd (c := C)
      F.continuous.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun xi => by
        simpa only [Real.norm_eq_abs, abs_norm] using
          SchwartzMap.norm_le_seminorm ℂ F xi)
  have hlog := integrable_abs_log_abs_mul_norm_sq F
  have hmajor : Integrable (fun xi : ℝ =>
      |Real.log (2 * Real.pi)| * ‖F xi‖ ^ 2 +
        |Real.log (|xi|)| * ‖F xi‖ ^ 2) :=
    (hF2.const_mul |Real.log (2 * Real.pi)|).add hlog
  refine hmajor.mono'
    ((Real.measurable_log.comp
      ((measurable_const.mul measurable_id).abs)).abs.mul
        (F.continuous.norm.measurable.pow_const 2)).aestronglyMeasurable ?_
  have hne : ∀ᵐ xi : ℝ ∂volume, xi ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with xi hxi
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have habsxi : |xi| ≠ 0 := abs_ne_zero.mpr hxi
  have hlogmul : Real.log (|2 * Real.pi * xi|) =
      Real.log (2 * Real.pi) + Real.log (|xi|) := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos]
    exact Real.log_mul hc habsxi
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (abs_nonneg _) (sq_nonneg _)), hlogmul]
  nlinarith [abs_add_le (Real.log (2 * Real.pi)) (Real.log (|xi|)), sq_nonneg ‖F xi‖]

def suzukiAbelRenormalizedSpectralDensity
    (delta : ℝ) (f : SchwartzMap ℝ ℂ) (xi : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (delta ^ 2 + (2 * Real.pi * xi) ^ 2) *
    ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2

def suzukiLogFourierSpectralDensity
    (f : SchwartzMap ℝ ℂ) (xi : ℝ) : ℝ :=
  Real.log (|2 * Real.pi * xi|) * ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2

def suzukiAbelRenormalizationBound
    (f : SchwartzMap ℝ ℂ) (xi : ℝ) : ℝ :=
  |Real.log (|2 * Real.pi * xi|)| * ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2 +
    (1 / 2 : ℝ) * Real.log (1 + (2 * Real.pi * xi) ^ 2) *
      ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2

theorem integrable_abs_log_fourierSpectralDensity
    (f : SchwartzMap ℝ ℂ) :
    Integrable (fun xi : ℝ =>
      |Real.log (|2 * Real.pi * xi|)| * ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2) := by
  have h := integrable_abs_log_two_pi_mul_mul_norm_sq (𝓕 f)
  refine h.congr (Filter.Eventually.of_forall fun xi => ?_)
  change |Real.log (|2 * Real.pi * xi|)| * ‖(𝓕 f) xi‖ ^ 2 =
    |Real.log (|2 * Real.pi * xi|)| * ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2
  rw [congrFun (SchwartzMap.fourier_coe f) xi]

theorem integrable_suzukiAbelRenormalizationBound
    (f : SchwartzMap ℝ ℂ) :
    Integrable (suzukiAbelRenormalizationBound f) := by
  have hlog := integrable_abs_log_fourierSpectralDensity f
  have habel := integrable_abelSchwartzSpectralDensity (delta := (1 : ℝ))
    (by norm_num) f
  have hhalf := habel.const_mul (1 / 2 : ℝ)
  exact (hlog.add hhalf).congr (Filter.Eventually.of_forall fun xi => by
    simp only [suzukiAbelRenormalizationBound, Pi.add_apply, div_one]
    ring)

theorem norm_suzukiAbelRenormalizedSpectralDensity_le_bound
    {delta xi : ℝ} (hdelta : delta ∈ Ioc (0 : ℝ) 1) (hxi : xi ≠ 0)
    (f : SchwartzMap ℝ ℂ) :
    ‖suzukiAbelRenormalizedSpectralDensity delta f xi‖ ≤
      suzukiAbelRenormalizationBound f xi := by
  let b : ℝ := 2 * Real.pi * xi
  have hb : b ≠ 0 := by dsimp [b]; exact mul_ne_zero (by positivity) hxi
  have hb2pos : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hmidpos : 0 < delta ^ 2 + b ^ 2 := by positivity
  have hlowerArg : b ^ 2 ≤ delta ^ 2 + b ^ 2 := by nlinarith [sq_nonneg delta]
  have hdeltaSq : delta ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hdelta.1.le hdelta.2 2
  have hupperArg : delta ^ 2 + b ^ 2 ≤ 1 + b ^ 2 := by linarith
  have hlogLowerRaw : Real.log (b ^ 2) ≤ Real.log (delta ^ 2 + b ^ 2) :=
    Real.log_le_log hb2pos hlowerArg
  have hlogUpperRaw : Real.log (delta ^ 2 + b ^ 2) ≤ Real.log (1 + b ^ 2) :=
    Real.log_le_log hmidpos hupperArg
  have hlogPow : (1 / 2 : ℝ) * Real.log (b ^ 2) = Real.log |b| := by
    rw [Real.log_pow, Real.log_abs]
    ring
  have hLower : Real.log |b| ≤ (1 / 2 : ℝ) * Real.log (delta ^ 2 + b ^ 2) := by
    rw [← hlogPow]
    linarith
  have hUpper : (1 / 2 : ℝ) * Real.log (delta ^ 2 + b ^ 2) ≤
      (1 / 2 : ℝ) * Real.log (1 + b ^ 2) := by linarith
  have hUpperNonneg : 0 ≤ (1 / 2 : ℝ) * Real.log (1 + b ^ 2) := by
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith [sq_nonneg b]))
  have hscalar : |(1 / 2 : ℝ) * Real.log (delta ^ 2 + b ^ 2)| ≤
      |Real.log (|b|)| + (1 / 2 : ℝ) * Real.log (1 + b ^ 2) := by
    rw [abs_le]
    constructor
    · nlinarith [neg_abs_le (Real.log |b|)]
    · nlinarith [abs_nonneg (Real.log |b|)]
  have hdensity : 0 ≤ ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2 := sq_nonneg _
  rw [suzukiAbelRenormalizedSpectralDensity,
    suzukiAbelRenormalizationBound, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hdensity]
  change |(1 / 2 : ℝ) * Real.log (delta ^ 2 + b ^ 2)| * _ ≤
    |Real.log (|b|)| * _ + (1 / 2 : ℝ) * Real.log (1 + b ^ 2) * _
  nlinarith

theorem tendsto_suzukiAbelRenormalizedSpectralDensity_nhdsGT_zero
    {xi : ℝ} (hxi : xi ≠ 0) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun delta : ℝ => suzukiAbelRenormalizedSpectralDensity delta f xi)
      (𝓝[>] 0) (𝓝 (suzukiLogFourierSpectralDensity f xi)) := by
  let b : SuzukiNonzeroFrequency :=
    ⟨2 * Real.pi * xi, mul_ne_zero (by positivity) hxi⟩
  have hbase := (tendsto_abelLogKernelIntegral_add_log_nhdsGT_zero b).mul_const
    (‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2)
  apply hbase.congr'
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  rw [abelLogKernelIntegral_add_log_eq_half_log_add_sq_of_pos hdelta]
  rfl

theorem tendsto_integral_suzukiAbelRenormalizedSpectralDensity_nhdsGT_zero
    (f : SchwartzMap ℝ ℂ) :
    Tendsto
      (fun delta : ℝ => ∫ xi : ℝ,
        suzukiAbelRenormalizedSpectralDensity delta f xi)
      (𝓝[>] 0)
      (𝓝 (∫ xi : ℝ, suzukiLogFourierSpectralDensity f xi)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (suzukiAbelRenormalizationBound f)
  · exact Filter.Eventually.of_forall fun delta =>
      ((Real.measurable_log.comp
        (measurable_const.add ((measurable_const.mul measurable_id).pow_const 2))).const_mul
          (1 / 2 : ℝ)).mul
        ((GaloisForLFunctions.RHTower.continuous_fourier_of_integrable
          f.integrable).norm.measurable.pow_const 2) |>.aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with delta hdelta
    have hne : ∀ᵐ xi : ℝ ∂volume, xi ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with xi hxi
    exact norm_suzukiAbelRenormalizedSpectralDensity_le_bound hdelta hxi f
  · exact integrable_suzukiAbelRenormalizationBound f
  · have hne : ∀ᵐ xi : ℝ ∂volume, xi ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with xi hxi
    exact tendsto_suzukiAbelRenormalizedSpectralDensity_nhdsGT_zero hxi f

theorem integrable_fourierNormSq_schwartz (f : SchwartzMap ℝ ℂ) :
    Integrable (fun xi : ℝ => ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2) :=
  GaloisForLFunctions.RHTower.integrable_norm_sq_fourier f.integrable
    (SchwartzMap.memLp f 2 (volume : Measure ℝ))

theorem half_log_one_add_div_sq_add_log_eq_half_log_add_sq_of_pos
    {delta : ℝ} (hdelta : 0 < delta) (b : ℝ) :
    (1 / 2 : ℝ) * Real.log (1 + (b / delta) ^ 2) + Real.log delta =
      (1 / 2 : ℝ) * Real.log (delta ^ 2 + b ^ 2) := by
  rw [← integral_abelLogKernel_eq_half_log_one_add_div_sq_of_pos hdelta b]
  exact abelLogKernelIntegral_add_log_eq_half_log_add_sq_of_pos hdelta b

theorem integral_suzukiAbelRenormalizedSpectralDensity_eq
    {delta : ℝ} (hdelta : 0 < delta) (f : SchwartzMap ℝ ℂ) :
    (1 / 2 : ℝ) *
        (∫ xi : ℝ, Real.log (1 + ((2 * Real.pi * xi) / delta) ^ 2) *
          ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2) +
      Real.log delta * (∫ xi : ℝ, ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2) =
        ∫ xi : ℝ, suzukiAbelRenormalizedSpectralDensity delta f xi := by
  have habel := integrable_abelSchwartzSpectralDensity hdelta f
  have hmass := integrable_fourierNormSq_schwartz f
  rw [← integral_const_mul, ← integral_const_mul]
  rw [← integral_add (habel.const_mul (1 / 2 : ℝ))
    (hmass.const_mul (Real.log delta))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun xi => ?_)
  rw [suzukiAbelRenormalizedSpectralDensity]
  have hscalar := half_log_one_add_div_sq_add_log_eq_half_log_add_sq_of_pos
    hdelta (2 * Real.pi * xi)
  nlinarith [sq_nonneg ‖𝓕 (f : ℝ → ℂ) xi‖]

def abelSchwartzPhysicalEnergyR (delta : ℝ) (f : SchwartzMap ℝ ℂ) : ℝ :=
  (abelSchwartzPhysicalEnergyL delta f).toReal

theorem abelSchwartzPhysicalEnergyR_eq_integral_of_pos
    {delta : ℝ} (hdelta : 0 < delta) (f : SchwartzMap ℝ ℂ) :
    abelSchwartzPhysicalEnergyR delta f =
      ∫ xi : ℝ, Real.log (1 + ((2 * Real.pi * xi) / delta) ^ 2) *
        ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2 := by
  rw [abelSchwartzPhysicalEnergyR,
    abelSchwartzPhysicalEnergyL_eq_spectralEnergy hdelta,
    abelSchwartzSpectralEnergyL_eq_ofReal_integral hdelta]
  rw [ENNReal.toReal_ofReal]
  exact integral_nonneg fun xi =>
    mul_nonneg (Real.log_nonneg
      (by nlinarith [sq_nonneg ((2 * Real.pi * xi) / delta)])) (sq_nonneg _)

def suzukiAbelRenormalizedDifferenceEnergy
    (delta : ℝ) (f : SchwartzMap ℝ ℂ) : ℝ :=
  (1 / 2 : ℝ) * abelSchwartzPhysicalEnergyR delta f +
    Real.log delta * (∫ xi : ℝ, ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2)

theorem suzukiAbelRenormalizedDifferenceEnergy_eq_integral_of_pos
    {delta : ℝ} (hdelta : 0 < delta) (f : SchwartzMap ℝ ℂ) :
    suzukiAbelRenormalizedDifferenceEnergy delta f =
      ∫ xi : ℝ, suzukiAbelRenormalizedSpectralDensity delta f xi := by
  rw [suzukiAbelRenormalizedDifferenceEnergy,
    abelSchwartzPhysicalEnergyR_eq_integral_of_pos hdelta]
  exact integral_suzukiAbelRenormalizedSpectralDensity_eq hdelta f

/-- Unconditional Abel-to-logarithmic Fourier finite-part limit for every complex Schwartz map. -/
theorem tendsto_suzukiAbelRenormalizedDifferenceEnergy_nhdsGT_zero
    (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun delta : ℝ => suzukiAbelRenormalizedDifferenceEnergy delta f)
      (𝓝[>] 0)
      (𝓝 (∫ xi : ℝ, suzukiLogFourierSpectralDensity f xi)) := by
  apply (tendsto_integral_suzukiAbelRenormalizedSpectralDensity_nhdsGT_zero f).congr'
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  exact (suzukiAbelRenormalizedDifferenceEnergy_eq_integral_of_pos hdelta f).symm

end
end RHTower

import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellLevyTransfer
import GaloisForLFunctions.RHTower.CHMDStationaryConvolutionRepresentative

/-!
# Smoothing with both pole moments fixed

An even mollifier has equal exponential moments at ±1/2. Dividing by that
common moment gives a positive smooth kernel which fixes both pole degrees,
commutes with every translation, and contracts the Gamma jump energy.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped Convolution
open _root_.RHTower hiding mollifier
open _root_.RHTower.CHMDDoobGraph

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open HTGeometry

theorem mollifier_even (n : ℕ) (u : ℝ) : mollifier n (-u) = mollifier n u := by
  unfold mollifier
  rw [ContDiffBump.normed_def, ContDiffBump.normed_def, ContDiffBump.neg]

/-- The common exponential moment of the even smoothing kernel. -/
def poleNormalizer (n : ℕ) : ℝ := ∫ u, mollifier n u * Real.cosh (u / 2)

theorem integrable_mollifier_cosh (n : ℕ) :
    Integrable (fun u => mollifier n u * Real.cosh (u / 2)) :=
  ((mollifier_contDiff n).continuous.mul
    (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      (mollifier_compact n).mul_right

theorem integrable_mollifier_exp (n : ℕ) (s : ℝ) :
    Integrable (fun u => Real.exp (s * u) * mollifier n u) :=
  ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (mollifier_contDiff n).continuous).integrable_of_hasCompactSupport
      (mollifier_compact n).mul_left

theorem one_le_poleNormalizer (n : ℕ) : 1 ≤ poleNormalizer n := by
  rw [← mollifier_integral n]
  apply integral_mono (mollifier_integrable n) (integrable_mollifier_cosh n)
  intro u
  have h := mul_le_mul_of_nonneg_left (Real.one_le_cosh (u / 2)) (mollifier_nonneg n u)
  simpa only [mul_one] using h

theorem poleNormalizer_pos (n : ℕ) : 0 < poleNormalizer n :=
  lt_of_lt_of_le zero_lt_one (one_le_poleNormalizer n)

theorem poleNormalizer_tendsto : Tendsto poleNormalizer atTop (𝓝 1) := by
  change Tendsto (fun n => ∫ u, (WeilOneSided.narrowBump n).normed volume u *
    Real.cosh (u / 2)) atTop (𝓝 1)
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure ℝ)) narrowBump_rOut_tendsto
      (Real.continuous_cosh.comp (continuous_id.div_const 2)) 0
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
    zero_sub, Function.comp_def, id_eq, neg_div, Real.cosh_neg, zero_div, Real.cosh_zero, mollifier,
    poleNormalizer] using h

theorem integral_mollifier_exp_neg (n : ℕ) :
    (∫ u, Real.exp (-(u / 2)) * mollifier n u) =
      ∫ u, Real.exp (u / 2) * mollifier n u := by
  calc
    _ = ∫ u, Real.exp (-((-u) / 2)) * mollifier n (-u) :=
      (integral_neg_eq_self (fun u => Real.exp (-(u / 2)) * mollifier n u) volume).symm
    _ = _ := by simp only [neg_div, neg_neg, mollifier_even]

theorem poleNormalizer_eq_exp (n : ℕ) :
    poleNormalizer n = ∫ u, Real.exp (u / 2) * mollifier n u := by
  have hp : Integrable (fun u => Real.exp (u / 2) * mollifier n u) := by
    simpa only [one_div, inv_mul_eq_div] using integrable_mollifier_exp n (1 / 2)
  have hm : Integrable (fun u => Real.exp (-(u / 2)) * mollifier n u) := by
    simpa only [neg_mul, one_div, inv_mul_eq_div] using integrable_mollifier_exp n (-(1 / 2))
  have he : (fun u => mollifier n u * Real.cosh (u / 2)) =
      fun u => (Real.exp (u / 2) * mollifier n u +
        Real.exp (-(u / 2)) * mollifier n u) / 2 := by
    funext u
    rw [Real.cosh_eq]
    ring
  rw [poleNormalizer, he, integral_div, integral_add hp hm, integral_mollifier_exp_neg]
  ring

/-- A positive compact kernel with both exponential pole moments equal to one. -/
def poleKernel (n : ℕ) (u : ℝ) : ℝ := (poleNormalizer n)⁻¹ * mollifier n u

theorem poleKernel_nonneg (n : ℕ) (u : ℝ) : 0 ≤ poleKernel n u :=
  mul_nonneg (inv_nonneg.mpr (poleNormalizer_pos n).le) (mollifier_nonneg n u)

theorem poleKernel_contDiff (n : ℕ) : ContDiff ℝ 2 (poleKernel n) :=
  contDiff_const.mul (mollifier_contDiff n)

theorem poleKernel_compact (n : ℕ) : HasCompactSupport (poleKernel n) :=
  (mollifier_compact n).mul_left

theorem poleKernel_expMoment (n : ℕ) :
    (∫ u, Real.exp (u / 2) * poleKernel n u) = 1 ∧
      (∫ u, Real.exp (-(u / 2)) * poleKernel n u) = 1 := by
  have hp : (∫ u, Real.exp (u / 2) * poleKernel n u) =
      (poleNormalizer n)⁻¹ * ∫ u, Real.exp (u / 2) * mollifier n u := by
    simp only [poleKernel, mul_left_comm (Real.exp _), integral_const_mul]
  have hm : (∫ u, Real.exp (-(u / 2)) * poleKernel n u) =
      (poleNormalizer n)⁻¹ * ∫ u, Real.exp (-(u / 2)) * mollifier n u := by
    simp only [poleKernel, mul_left_comm (Real.exp _), integral_const_mul]
  rw [integral_mollifier_exp_neg] at hm
  rw [← poleNormalizer_eq_exp, inv_mul_cancel₀ (poleNormalizer_pos n).ne'] at hp hm
  exact ⟨hp, hm⟩

/-- Exponential weighting turns convolution into the convolution of the weighted factors. -/
theorem real_exp_mul_convolution (k f : ℝ → ℝ) (s : ℝ) :
    (fun x => Real.exp (s * x) * lineConvolution k f x) =
      lineConvolution (fun x => Real.exp (s * x) * k x)
        (fun x => Real.exp (s * x) * f x) := by
  funext x
  unfold lineConvolution
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  have he : Real.exp (s * x) = Real.exp (s * t) * Real.exp (s * (x - t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

theorem integral_exp_mul_convolution {k f : ℝ → ℝ} (s : ℝ)
    (hk : Integrable (fun x => Real.exp (s * x) * k x))
    (hf : Integrable (fun x => Real.exp (s * x) * f x)) :
    (∫ x, Real.exp (s * x) * lineConvolution k f x) =
      (∫ x, Real.exp (s * x) * k x) * ∫ x, Real.exp (s * x) * f x := by
  rw [real_exp_mul_convolution]
  exact integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hk hf

/-- Smooth regularization on the original source line. -/
def poleSmooth (f : ℝ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (poleNormalizer n)⁻¹ * smooth f n u

theorem poleSmooth_eq_convolution (f : ℝ → ℝ) (n : ℕ) :
    poleSmooth f n = lineConvolution (poleKernel n) f := by
  funext u
  simp only [poleSmooth, smooth, lineConvolution, poleKernel, mul_assoc, integral_const_mul]

theorem poleSmooth_contDiff {f : ℝ → ℝ} (hf : MemLp f 2 volume) (n : ℕ) :
    ContDiff ℝ 2 (poleSmooth f n) := contDiff_const.mul (smooth_contDiff hf n)

theorem poleSmooth_compact {f : ℝ → ℝ} (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (poleSmooth f n) := (smooth_compact hf n).mul_left

/-- Every translation, hence every Hecke shift, commutes with the same smoothing map. -/
theorem poleSmooth_translate (f : ℝ → ℝ) (n : ℕ) (t u : ℝ) :
    poleSmooth (fun x => f (x - t)) n u = poleSmooth f n (u - t) := by
  unfold poleSmooth smooth lineConvolution
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show u - x - t = u - t - x by ring]

/-- Both pole degrees are preserved exactly, for every admissible source. -/
theorem poleSmooth_expMoments {f : ℝ → ℝ}
    (hp : Integrable (fun u => Real.exp (u / 2) * f u))
    (hm : Integrable (fun u => Real.exp (-(u / 2)) * f u)) (n : ℕ) :
    (∫ u, Real.exp (u / 2) * poleSmooth f n u) = ∫ u, Real.exp (u / 2) * f u ∧
      (∫ u, Real.exp (-(u / 2)) * poleSmooth f n u) =
        ∫ u, Real.exp (-(u / 2)) * f u := by
  have hk (s : ℝ) : Integrable (fun u => Real.exp (s * u) * poleKernel n u) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (poleKernel_contDiff n).continuous).integrable_of_hasCompactSupport
        (poleKernel_compact n).mul_left
  have hplus := integral_exp_mul_convolution (k := poleKernel n) (f := f) (1 / 2)
    (hk (1 / 2)) (by simpa only [one_div, inv_mul_eq_div] using hp)
  have hminus := integral_exp_mul_convolution (k := poleKernel n) (f := f) (-(1 / 2))
    (hk (-(1 / 2))) (by simpa only [neg_mul, one_div, inv_mul_eq_div] using hm)
  simp only [one_div, inv_mul_eq_div, ← poleSmooth_eq_convolution,
    (poleKernel_expMoment n).1, one_mul] at hplus
  simp only [neg_mul, one_div, inv_mul_eq_div, ← poleSmooth_eq_convolution,
    (poleKernel_expMoment n).2, one_mul] at hminus
  exact ⟨hplus, hminus⟩


theorem poleNormalizer_inv_le_one (n : ℕ) : (poleNormalizer n)⁻¹ ≤ 1 := by
  exact (inv_le_one₀ (poleNormalizer_pos n)).mpr (one_le_poleNormalizer n)

theorem levyEnergy_const_mul (c : ℝ) (f : ℝ → ℝ) :
    levyEnergy (fun u => c * f u) = c ^ 2 * levyEnergy f := by
  have h (x t : ℝ) : (c * f x - c * f (x + t)) ^ 2 =
      c ^ 2 * (f x - f (x + t)) ^ 2 := by ring
  simp only [levyEnergy, h, integral_const_mul, mul_left_comm (archLevyDensity _)]

theorem levyEnergy_nonneg_bv {f : ℝ → ℝ} (hv : BoundedVariationOn f univ)
    (hc : HasCompactSupport f) : 0 ≤ levyEnergy f := by
  rw [← norm_levyVector_sq f hv hc]
  exact sq_nonneg _

theorem memLp_compact_bv {f : ℝ → ℝ} (hv : BoundedVariationOn f univ)
    (hc : HasCompactSupport f) : MemLp f 2 volume := by
  apply bounded_compact_memLp_volume (measurable_of_boundedVariation_univ hv) hc
    (show 0 ≤ ‖f 0‖ + (eVariationOn f univ).toReal by positivity)
  intro x
  simpa only [Real.norm_eq_abs] using norm_le_of_boundedVariation_univ hv x

/-- Pole-preserving regularization contracts the entire Gamma jump form. -/
theorem levyEnergy_poleSmooth_le {f : ℝ → ℝ} (hv : BoundedVariationOn f univ)
    (hc : HasCompactSupport f) (n : ℕ) : levyEnergy (poleSmooth f n) ≤ levyEnergy f := by
  have hs := smooth_contDiff (memLp_compact_bv hv hc) n
  have hsc := smooth_compact hc n
  have hsv := boundedVariationOn_of_contDiff_compact (hs.of_le (by norm_num)) hsc
  have hE : levyEnergy (smooth f n) ≤ levyEnergy f := by
    rw [← stationaryEnergy_eq_levyEnergy hsv hsc, ← stationaryEnergy_eq_levyEnergy hv hc]
    apply stationaryEnergy_smooth_le (measurable_of_boundedVariation_univ hv) hc
      (bv_memLp_difference hv) (show 0 ≤ ‖f 0‖ + (eVariationOn f univ).toReal by positivity)
    intro x
    simpa only [Real.norm_eq_abs] using norm_le_of_boundedVariation_univ hv x
  have hC0 : 0 ≤ (poleNormalizer n)⁻¹ := inv_nonneg.mpr (poleNormalizer_pos n).le
  have hC2 : (poleNormalizer n)⁻¹ ^ 2 ≤ 1 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ hC0 (poleNormalizer_inv_le_one n) 2)
  change levyEnergy (fun u => (poleNormalizer n)⁻¹ * smooth f n u) ≤ _
  rw [levyEnergy_const_mul]
  exact (mul_le_of_le_one_left (levyEnergy_nonneg_bv hsv hsc) hC2).trans hE

theorem poleSmooth_add {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hfb : ∀ x, |f x| ≤ M) (hgb : ∀ x, |g x| ≤ K) (n : ℕ) :
    poleSmooth (fun x => f x + g x) n = fun x => poleSmooth f n x + poleSmooth g n x := by
  funext x
  simp only [poleSmooth, smooth, lineConvolution, mul_add]
  rw [integral_add (integrable_mollifier_mul hf hM hfb n x)
    (integrable_mollifier_mul hg hK hgb n x), mul_add]

theorem poleSmooth_const_mul (c : ℝ) (f : ℝ → ℝ) (n : ℕ) :
    poleSmooth (fun x => c * f x) n = fun x => c * poleSmooth f n x := by
  funext x
  simp only [poleSmooth, smooth, lineConvolution, mul_left_comm (mollifier n _),
    integral_const_mul]
  ring

open scoped InnerProductSpace

theorem volume_norm_sq (u : StationaryVolumeSpace) : ‖u‖ ^ 2 = ∫ x, u x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, volume_inner_realLp]
  simp only [pow_two]

theorem volume_norm_sq_of_ae {f : ℝ → ℝ} (u : StationaryVolumeSpace)
    (hu : u =ᵐ[volume] f) : ‖u‖ ^ 2 = ∫ x, f x ^ 2 := by
  rw [volume_norm_sq]
  exact integral_congr_ae (hu.fun_comp (fun x : ℝ => x ^ 2))

/-- The Hilbert-space realization of the same pointwise regularization. -/
def volumePoleSmooth (n : ℕ) (u : StationaryVolumeSpace) : StationaryVolumeSpace :=
  (poleNormalizer n)⁻¹ • volumeSmooth n u

theorem volumePoleSmooth_ae {f : ℝ → ℝ} (hf : MemLp f 2 volume) (n : ℕ) :
    volumePoleSmooth n (hf.toLp f) =ᵐ[volume] poleSmooth f n := by
  have he := smooth_congr_ae hf.coeFn_toLp n
  filter_upwards [Lp.coeFn_smul ((poleNormalizer n)⁻¹) (volumeSmooth n (hf.toLp f)),
    volumeSmooth_ae n (hf.toLp f)] with x hsm hs
  change ((poleNormalizer n)⁻¹ • volumeSmooth n (hf.toLp f)) x = _
  simp only [hsm, Pi.smul_apply, smul_eq_mul, hs, he, poleSmooth]

theorem volumePoleSmooth_tendsto (u : StationaryVolumeSpace) :
    Tendsto (fun n => volumePoleSmooth n u) atTop (𝓝 u) := by
  have h := (poleNormalizer_tendsto.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).smul
    (volumeSmooth_tendsto u)
  simpa only [inv_one, one_smul, volumePoleSmooth] using h

theorem memLp_poleSmooth {f : ℝ → ℝ} (hf : MemLp f 2 volume) (n : ℕ) :
    MemLp (poleSmooth f n) 2 volume :=
  (memLp_congr_ae (volumePoleSmooth_ae hf n)).mp
    (Lp.memLp (volumePoleSmooth n (hf.toLp f)))

/-- Source mass is recovered in ordinary Lebesgue L². -/
theorem tendsto_poleSmooth_L2_error {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    Tendsto (fun n => ∫ x, (poleSmooth f n x - f x) ^ 2) atTop (𝓝 0) := by
  have h := ((volumePoleSmooth_tendsto (hf.toLp f)).sub
    (tendsto_const_nhds (x := hf.toLp f))).norm.pow 2
  simp only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at h
  convert h using 1
  funext n
  symm
  apply volume_norm_sq_of_ae
  filter_upwards [Lp.coeFn_sub (volumePoleSmooth n (hf.toLp f)) (hf.toLp f),
    volumePoleSmooth_ae hf n, hf.coeFn_toLp] with x hx hs hf'
  simp only [hx, Pi.sub_apply, hs, hf']

theorem volume_shift_difference_norm {f : ℝ → ℝ} (u : StationaryVolumeSpace)
    (hu : u =ᵐ[volume] f) (t : ℝ) :
    ‖u - volumeTranslate t u‖ ^ 2 = ∫ x, (f x - f (x + t)) ^ 2 := by
  apply volume_norm_sq_of_ae
  filter_upwards [Lp.coeFn_sub u (volumeTranslate t u), hu, volumeTranslate_ae t u,
    (measurePreserving_add_right volume t).quasiMeasurePreserving.ae hu]
    with x hx hf ht hf'
  simp only [hx, Pi.sub_apply, hf, ht, hf']

theorem tendsto_poleSmooth_shift_energy {f : ℝ → ℝ} (hf : MemLp f 2 volume) (t : ℝ) :
    Tendsto (fun n => ∫ x, (poleSmooth f n x - poleSmooth f n (x + t)) ^ 2)
      atTop (𝓝 (∫ x, (f x - f (x + t)) ^ 2)) := by
  have h := volumePoleSmooth_tendsto (hf.toLp f)
  have hs := (h.sub ((volumeTranslate t).continuous.tendsto (hf.toLp f) |>.comp h)).norm.pow 2
  simpa only [Function.comp_apply, volume_shift_difference_norm _ (volumePoleSmooth_ae hf _) t,
    volume_shift_difference_norm _ hf.coeFn_toLp t] using hs

theorem tendsto_poleSmooth_square_mass {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    Tendsto (fun n => ∫ x, poleSmooth f n x ^ 2) atTop (𝓝 (∫ x, f x ^ 2)) := by
  have h := (volumePoleSmooth_tendsto (hf.toLp f)).norm.pow 2
  simpa only [volume_norm_sq_of_ae _ (volumePoleSmooth_ae hf _),
    volume_norm_sq_of_ae _ hf.coeFn_toLp] using h

theorem poleSmooth_shift_energy_le {f : ℝ → ℝ} (hv : BoundedVariationOn f univ)
    (hc : HasCompactSupport f) (n : ℕ) (t : ℝ) :
    (∫ x, (poleSmooth f n x - poleSmooth f n (x + t)) ^ 2) ≤
      ∫ x, (f x - f (x + t)) ^ 2 := by
  have h := smooth_difference_L2_le (measurable_of_boundedVariation_univ hv) hc
    (show 0 ≤ ‖f 0‖ + (eVariationOn f univ).toReal by positivity)
    (fun x => by simpa only [Real.norm_eq_abs] using norm_le_of_boundedVariation_univ hv x) n t
  have he (x : ℝ) : (poleSmooth f n x - poleSmooth f n (x + t)) ^ 2 =
      (poleNormalizer n)⁻¹ ^ 2 * (smooth f n x - smooth f n (x + t)) ^ 2 := by
    simp only [poleSmooth]
    ring
  simp only [he, integral_const_mul]
  have hC2 : (poleNormalizer n)⁻¹ ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀
      (inv_nonneg.mpr (poleNormalizer_pos n).le) (poleNormalizer_inv_le_one n) 2
  exact (mul_le_of_le_one_left (integral_nonneg fun x => sq_nonneg _) hC2).trans h

/-- No Gamma mass is lost at the singular small-jump end. -/
theorem tendsto_poleSmooth_levyEnergy {f : ℝ → ℝ} (hv : BoundedVariationOn f univ)
    (hc : HasCompactSupport f) :
    Tendsto (fun n => levyEnergy (poleSmooth f n)) atTop (𝓝 (levyEnergy f)) := by
  have hf2 := memLp_compact_bv hv hc
  have hj : Integrable (stationaryJump f) archBase :=
    (memLp_levyRoot hv hc).integrable_sq.congr (levyRoot_sq_ae f)
  change Tendsto (fun n => ∫ t in Ioi (0 : ℝ), archLevyDensity t *
    ∫ x, (poleSmooth f n x - poleSmooth f n (x + t)) ^ 2) atTop
    (𝓝 (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x, (f x - f (x + t)) ^ 2))
  apply tendsto_integral_of_dominated_convergence
    (fun t => archLevyDensity t * ∫ x, (f x - f (x + t)) ^ 2)
  · intro n
    have hs := poleSmooth_contDiff hf2 n
    have hsc := poleSmooth_compact hc n
    have hsv := boundedVariationOn_of_contDiff_compact (hs.of_le (by norm_num)) hsc
    exact (integrable_stationary_outer
      ((memLp_levyRoot hsv hsc).integrable_sq.congr (levyRoot_sq_ae _))).aestronglyMeasurable
  · exact integrable_stationary_outer hj
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg (archLevyDensity_pos ht).le
      (integral_nonneg fun x => sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (poleSmooth_shift_energy_le hv hc n t)
      (archLevyDensity_pos ht).le
  · exact Eventually.of_forall fun t => tendsto_const_nhds.mul (tendsto_poleSmooth_shift_energy hf2 t)


#print axioms tendsto_poleSmooth_levyEnergy
#print axioms levyEnergy_poleSmooth_le
#print axioms tendsto_poleSmooth_L2_error
#print axioms poleNormalizer_tendsto
#print axioms poleKernel_expMoment
#print axioms poleSmooth_expMoments
#print axioms poleSmooth_translate

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

import GaloisForLFunctions.RHTower.Suzuki.SuzukiSmallApertureFormScaling
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarConstrainedSmoothCore

/-!
# Amplitude-preserving concentration in the actual archimedean form norm

A smooth source may retain its value at the origin while its actual Gamma form norm tends
to zero.  The proof uses logarithmic Fourier dilation, not a change of an L2 representative
at a null set.  The bound applies to the whole source and therefore retains its cross terms.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

theorem norm_suzukiHlogFourierScaleCLM_le (r : ℝ) (hr : 0 < r)
    (f : SuzukiHlogFourierL2) :
    ‖suzukiHlogFourierScaleCLM r hr f‖ ≤
      Real.sqrt (suzukiHlogScaleBound r) * ‖f‖ := by
  change ‖suzukiHlogDensityUnitary.symm
    (suzukiHlogScaleRatioMul r hr
      (dilation r⁻¹ (inv_pos.mpr hr) (suzukiHlogDensityUnitary f)))‖ ≤ _
  rw [suzukiHlogDensityUnitary.symm.norm_map]
  calc
    _ ≤ ‖suzukiHlogScaleRatioMul r hr‖ *
        ‖dilation r⁻¹ (inv_pos.mpr hr) (suzukiHlogDensityUnitary f)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ Real.sqrt (suzukiHlogScaleBound r) *
        ‖dilation r⁻¹ (inv_pos.mpr hr) (suzukiHlogDensityUnitary f)‖ := by
      gcongr
      exact norm_lpBoundedMulCLM_le _ _ _
    _ = _ := by rw [(dilation r⁻¹ (inv_pos.mpr hr)).norm_map,
      suzukiHlogDensityUnitary.norm_map]

/-- Shrink physical support while retaining the original amplitude at corresponding points. -/
def CCMComplexSmoothInteriorSource.shrink {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) (r : ℝ) (hr : 1 ≤ r) :
    CCMComplexSmoothInteriorSource a where
  toFun := fun x => g (r * x)
  smooth := g.smooth.comp (contDiff_const.mul contDiff_id)
  hasCompactSupport := g.hasCompactSupport.comp_homeomorph
    (Homeomorph.mulLeft₀ r (by linarith))
  tsupport_subset := by
    intro x hx
    have hx' := g.tsupport_subset
      (tsupport_comp_subset_preimage (g : ℝ → ℂ)
        (continuous_const.mul continuous_id) hx)
    change -a.1 < r * x ∧ r * x < a.1 at hx'
    constructor
    · by_contra h
      have hx0 : x < 0 := lt_of_le_of_lt (not_lt.mp h) (neg_neg_of_pos a.property)
      have := mul_le_mul_of_nonpos_right hr hx0.le
      nlinarith [hx'.1]
    · by_contra h
      have hx0 : 0 < x := lt_of_lt_of_le a.property (not_lt.mp h)
      have := mul_le_mul_of_nonneg_right hr hx0.le
      nlinarith [hx'.2]

@[simp] theorem CCMComplexSmoothInteriorSource.shrink_apply
    {a : SuzukiPositiveAperture} (g : CCMComplexSmoothInteriorSource a)
    (r : ℝ) (hr : 1 ≤ r) (x : ℝ) : g.shrink r hr x = g (r * x) := rfl

private theorem shrink_fourier_vector {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) (r : ℝ) (hr : 1 ≤ r) :
    (g.shrink r hr).toCCMFormVector.1 =
      ccmLogToArchimedean ((Real.sqrt r : ℂ)⁻¹ •
        suzukiHlogFourierScaleCLM r (by linarith)
          (ccmArchimedeanToLog g.toCCMFormVector.1)) := by
  apply ccmArchimedeanFourierToTime_injective
  rw [ccmArchimedeanFourierToTime_logToArchimedean, map_smul,
    suzukiHlogFourierToTime_fourierScale, suzukiHlogFourierToTime_archimedeanToLog]
  let f : SoninL2 := ccmArchimedeanFormToAperture a g.toCCMFormVector
  have hg := g.toCCMFormVector_physical_coeFn.comp_tendsto
    (realMul_quasiMeasurePreserving r (by linarith)).tendsto_ae
  apply Lp.ext
  filter_upwards [(g.shrink r hr).toCCMFormVector_physical_coeFn,
    Lp.coeFn_smul (Real.sqrt r : ℂ)⁻¹ (dilation r (by linarith) f),
    dilation_ae r (by linarith) f, hg] with x hs hsm hd hgx
  change ((ccmArchimedeanFormToAperture a (g.shrink r hr).toCCMFormVector : SoninL2) :
    ℝ → ℂ) x = ((Real.sqrt r : ℂ)⁻¹ • dilation r (by linarith) f : SoninL2) x
  rw [hs, hsm]
  change g (r * x) = (Real.sqrt r : ℂ)⁻¹ * (dilation r (by linarith) f) x
  rw [hd]
  change f (r * x) = g (r * x) at hgx
  rw [hgx, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast Real.sqrt_ne_zero'.mpr (show 0 < r by linarith)

/-- An independent bound in the actual Gamma form norm, uniform over complete smooth sources. -/
theorem norm_ccmSmoothShrink_le {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) (r : ℝ) (hr : 1 ≤ r) :
    ‖(g.shrink r hr).toCCMFormVector‖ ≤
      (‖ccmLogToArchimedean‖ * ‖ccmArchimedeanToLog‖ * ‖g.toCCMFormVector‖) *
        Real.sqrt (suzukiHlogScaleBound r / r) := by
  have hr0 : 0 < r := by linarith
  change ‖(g.shrink r hr).toCCMFormVector.1‖ ≤ _
  rw [shrink_fourier_vector]
  calc
    _ ≤ ‖ccmLogToArchimedean‖ * ‖(Real.sqrt r : ℂ)⁻¹ •
        suzukiHlogFourierScaleCLM r hr0
          (ccmArchimedeanToLog g.toCCMFormVector.1)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖ccmLogToArchimedean‖ * ((Real.sqrt r)⁻¹ *
        ‖suzukiHlogFourierScaleCLM r hr0
          (ccmArchimedeanToLog g.toCCMFormVector.1)‖) := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg r)]
    _ ≤ ‖ccmLogToArchimedean‖ * ((Real.sqrt r)⁻¹ *
        (Real.sqrt (suzukiHlogScaleBound r) *
          (‖ccmArchimedeanToLog‖ * ‖g.toCCMFormVector.1‖))) := by
      gcongr
      exact (norm_suzukiHlogFourierScaleCLM_le r hr0 _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _)
          (Real.sqrt_nonneg _))
    _ = _ := by
      rw [Real.sqrt_div (suzukiHlogScaleBound_pos hr0).le]
      change ‖ccmLogToArchimedean‖ * ((Real.sqrt r)⁻¹ *
        (Real.sqrt (suzukiHlogScaleBound r) *
          (‖ccmArchimedeanToLog‖ * ‖g.toCCMFormVector‖))) = _
      ring

theorem tendsto_suzukiHlogScaleBound_div :
    Tendsto (fun r : ℝ => suzukiHlogScaleBound r / r) atTop (nhds 0) := by
  have hlog : Tendsto (fun r : ℝ => Real.log r / r) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hinv : Tendsto (fun r : ℝ => 1 / r) atTop (nhds 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (nhds 0))
  have h := hinv.add hlog
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  rw [suzukiHlogScaleBound, Real.posLog_eq_log (by simpa [abs_of_nonneg (by linarith : 0 ≤ r)] using hr),
    add_div]

/-- Preserving amplitude while shrinking support drives the actual Gamma form norm to zero. -/
theorem tendsto_ccmSmoothShrink_norm {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) :
    Tendsto (fun n : ℕ =>
      ‖(g.shrink (n + 1) (le_add_of_nonneg_left (Nat.cast_nonneg n))).toCCMFormVector‖)
      atTop (nhds 0) := by
  have hs : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  have h := (tendsto_suzukiHlogScaleBound_div.comp hs).sqrt.const_mul
    (‖ccmLogToArchimedean‖ * ‖ccmArchimedeanToLog‖ * ‖g.toCCMFormVector‖)
  simp only [Real.sqrt_zero, mul_zero] at h
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_ccmSmoothShrink_le g (n + 1) (le_add_of_nonneg_left (Nat.cast_nonneg n))) h

end RHTower

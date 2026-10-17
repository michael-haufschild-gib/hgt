import GaloisForLFunctions.BiScaleUncertainty.ForcedFirstCollar

/-!
# Uniform gain from the unavoidable first signed collar

Every physical partition has two sign norms at least one on a fixed interval.
Rationalizing the paired radial support then gives a positive integral gain
independent of the cutoff and of all remaining allocation choices.
-/

set_option autoImplicit false
open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

def firstCollarOriginBound : ℝ :=
  2 / (1 - Real.exp (-2 * firstCollarGapLeft))

def firstCollarGapDensity : ℝ := 1 / (firstCollarOriginBound + 2)

/-- Explicit improvement forced by the first two signed collars. -/
def uniformPairedCollarGap : ℝ :=
  (firstCollarGapRight - firstCollarGapLeft) * firstCollarGapDensity

theorem firstCollarOriginBound_pos : 0 < firstCollarOriginBound := by
  unfold firstCollarOriginBound
  apply div_pos (by norm_num)
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  linarith [firstCollarGap_geometry.1]

theorem firstCollarGapDensity_pos : 0 < firstCollarGapDensity := by
  have h := firstCollarOriginBound_pos
  unfold firstCollarGapDensity
  positivity

theorem uniformPairedCollarGap_pos : 0 < uniformPairedCollarGap :=
  mul_pos (sub_pos.mpr firstCollarGap_geometry.2.1) firstCollarGapDensity_pos

theorem archWeight_le_firstCollarOriginBound {y : ℝ}
    (hy : y ∈ Ioc firstCollarGapLeft firstCollarGapRight) :
    archLevySinhWeight y ≤ firstCollarOriginBound := by
  have h := archWeight_le_cutoff_exponential firstCollarGap_geometry.1 hy.1.le
  have he : Real.exp (-(1 / 2 : ℝ) * y) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [(firstCollarGapInterval_subset hy).1])
  change archLevySinhWeight y ≤ firstCollarOriginBound * Real.exp (-(1 / 2 : ℝ) * y) at h
  exact h.trans (by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left he firstCollarOriginBound_pos.le)

/-- Two nontrivial sign norms force a gain even when either norm grows arbitrarily. -/
theorem pairedRadialGain_lower {W W₀ A B : ℝ} (hW : 0 < W) (hW₀ : W ≤ W₀)
    (hA : 1 ≤ A) (hB : 1 ≤ B) :
    1 / (W₀ + 2) ≤ 2 * A * B /
      (Real.sqrt (W ^ 2 + (A + B) ^ 2) + Real.sqrt (W ^ 2 + A ^ 2 + B ^ 2)) := by
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hW00 : 0 ≤ W₀ := by linarith
  have hc : 0 < W₀ + 2 := by linarith
  have hAA : A ≤ A * B := by
    nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hB)]
  have hBB : B ≤ A * B := by
    nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hA)]
  have hAB : 1 ≤ A * B := hA.trans hAA
  have hs₁ : Real.sqrt (W ^ 2 + (A + B) ^ 2) ≤ W + A + B := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith [mul_nonneg hW.le (add_nonneg hA0 hB0)]
  have hs₂ : Real.sqrt (W ^ 2 + A ^ 2 + B ^ 2) ≤ W + A + B := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith [mul_nonneg hW.le hA0, mul_nonneg hW.le hB0, mul_nonneg hA0 hB0]
  have hWroot : W ≤ Real.sqrt (W ^ 2 + (A + B) ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (A + B)])
  have hd : 0 < Real.sqrt (W ^ 2 + (A + B) ^ 2) + Real.sqrt (W ^ 2 + A ^ 2 + B ^ 2) := by
    linarith [Real.sqrt_nonneg (W ^ 2 + A ^ 2 + B ^ 2)]
  have hscale : W + A + B ≤ (W₀ + 2) * (A * B) := by
    nlinarith [mul_nonneg hW00 (sub_nonneg.mpr hAB)]
  have hden : Real.sqrt (W ^ 2 + (A + B) ^ 2) + Real.sqrt (W ^ 2 + A ^ 2 + B ^ 2) ≤
      2 * (W₀ + 2) * (A * B) := by linarith
  apply (le_div_iff₀ hd).mpr
  calc
    _ ≤ (1 / (W₀ + 2)) * (2 * (W₀ + 2) * (A * B)) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = _ := by field_simp [hc.ne']

namespace PhysicalCollarPartition
variable {n : ℕ}

theorem pairedKernel_uniform_gain (ρ : PhysicalCollarPartition n) (hn : 1 ≤ n)
    {y : ℝ} (hy : y ∈ Ioc firstCollarGapLeft firstCollarGapRight) :
    firstCollarGapDensity ≤ ρ.pairedKernel y - ρ.kernel y := by
  have hy0 := (firstCollarGapInterval_subset hy).1
  rw [ρ.pairedKernel_sub_kernel hy0, ρ.blockNorm_eq_signBlockNorm_add]
  exact pairedRadialGain_lower (archLevySinhWeight_pos hy0)
    (archWeight_le_firstCollarOriginBound hy)
    (ρ.one_le_signBlockNorm_on_first_interval hn false hy)
    (ρ.one_le_signBlockNorm_on_first_interval hn true hy)

/-- The gain survives integration uniformly over every admissible physical allocation. -/
theorem coefficient_add_uniformGap_le_paired (ρ : PhysicalCollarPartition n) (hn : 1 ≤ n) :
    ρ.coefficient + uniformPairedCollarGap ≤ ρ.pairedCoefficient := by
  have hi : IntegrableOn (fun y => ρ.pairedKernel y - ρ.kernel y)
      (Ioo 0 logarithmicCollarRadius) :=
    ρ.integrableOn_pairedKernel.sub ρ.integrableOn_kernel
  have hc : IntegrableOn (fun _ : ℝ => firstCollarGapDensity)
      (Ioc firstCollarGapLeft firstCollarGapRight) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hs := setIntegral_mono_on hc (hi.mono_set firstCollarGapInterval_subset)
    measurableSet_Ioc (fun y hy => ρ.pairedKernel_uniform_gain hn hy)
  have hl := setIntegral_mono_set hi
    (Filter.Eventually.of_forall (fun y => sub_nonneg.mpr (ρ.kernel_le_pairedKernel y)))
    (Filter.Eventually.of_forall (fun y hy => firstCollarGapInterval_subset hy))
  have he : (∫ _ : ℝ in Ioc firstCollarGapLeft firstCollarGapRight, firstCollarGapDensity) =
      uniformPairedCollarGap := by
    simp only [setIntegral_const, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr firstCollarGap_geometry.2.1.le),
      smul_eq_mul, uniformPairedCollarGap]
  rw [he] at hs
  have h := hs.trans hl
  rw [integral_sub ρ.integrableOn_pairedKernel ρ.integrableOn_kernel] at h
  change uniformPairedCollarGap ≤ ρ.pairedCoefficient - ρ.coefficient at h
  linarith

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty

import GaloisForLFunctions.RHTower.MobiusDivisorCriticalBVProfile
import GaloisForLFunctions.RHTower.CHMDBVUniformConvergence

/-! # Literal complete clocks in the arithmetic source graph

A fixed continuous compact BV cutoff admits every translated clock. The
family is continuous in the full graph norm, including all prime jumps.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower
open CHMDDoobGraph

def criticalClockCutoff (χ : ℝ → ℝ) (t x : ℝ) : ℝ :=
  χ x * criticalAbelLogProfile (t - x)

theorem criticalClockCutoff_boundedVariation (χ : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (t : ℝ) :
    BoundedVariationOn (criticalClockCutoff χ t) univ :=
  boundedVariationOn_mul hχ (boundedVariationOn_criticalAbelLogProfile_translate t)

theorem criticalClockCutoff_compact (χ : ℝ → ℝ)
    (hχc : HasCompactSupport χ) (t : ℝ) : HasCompactSupport (criticalClockCutoff χ t) :=
  hχc.mul_right

theorem criticalClockCutoff_variation_bound (χ : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (t : ℝ) :
    (eVariationOn (criticalClockCutoff χ t) univ).toReal ≤
      (‖χ 0‖ + (eVariationOn χ univ).toReal) *
          (eVariationOn criticalAbelLogProfile univ).toReal +
        (∫ u in Ioi (0 : ℝ), |criticalAbelLogVelocity u|) *
          (eVariationOn χ univ).toReal := by
  let A := ‖χ 0‖ + (eVariationOn χ univ).toReal
  let B := ∫ u in Ioi (0 : ℝ), |criticalAbelLogVelocity u|
  have hA : 0 ≤ A := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hB : 0 ≤ B := integral_nonneg (fun _ => abs_nonneg _)
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eVariationOn_mul_le_of_bounds hχ (boundedVariationOn_criticalAbelLogProfile_translate t)
      hA hB (fun x _ => norm_le_of_boundedVariation_univ hχ x)
      (fun x _ => by simpa only [Real.norm_eq_abs] using criticalAbelLogProfile_uniform_bound (t - x)))
  rw [ENNReal.toReal_ofReal (add_nonneg (mul_nonneg hA ENNReal.toReal_nonneg)
    (mul_nonneg hB ENNReal.toReal_nonneg))] at h
  have hY := ENNReal.toReal_mono boundedVariationOn_criticalAbelLogProfile
    (eVariationOn_criticalAbelLogProfile_translate_le t)
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hY hA) le_rfl)

def criticalClockGraph (χ : ℝ → ℝ) (hχ : BoundedVariationOn χ univ) (t : ℝ) : SourceGraph :=
  bvLift (criticalClockCutoff χ t) (criticalClockCutoff_boundedVariation χ hχ t)

theorem criticalClockGraph_source (χ : ℝ → ℝ) (hχ : BoundedVariationOn χ univ) (t : ℝ) :
    (criticalClockGraph χ hχ t).val.fst =ᵐ[massMeasure] criticalClockCutoff χ t :=
  bvLift_source _ _

theorem continuous_criticalClockGraph (χ : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hχcont : Continuous χ)
    (hχc : HasCompactSupport χ) : Continuous (criticalClockGraph χ hχ) := by
  apply continuous_bvLift_of_common_compact
    (fun t => criticalClockCutoff_boundedVariation χ hχ t)
    (fun t => criticalClockCutoff_compact χ hχc t)
    (K := tsupport χ) (V := (‖χ 0‖ + (eVariationOn χ univ).toReal) *
      (eVariationOn criticalAbelLogProfile univ).toReal +
        (∫ u in Ioi (0 : ℝ), |criticalAbelLogVelocity u|) * (eVariationOn χ univ).toReal)
  · exact (hχcont.comp continuous_snd).mul
      (continuous_criticalAbelLogProfile.comp (continuous_fst.sub continuous_snd))
  · exact hχc
  · intro t x hx
    have hz : χ x = 0 := by
      by_contra h
      exact hx (subset_tsupport χ h)
    simp only [criticalClockCutoff, hz, zero_mul]
  · exact criticalClockCutoff_variation_bound χ hχ

end RHTower

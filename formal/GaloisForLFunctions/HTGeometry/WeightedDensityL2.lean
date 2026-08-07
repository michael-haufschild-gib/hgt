import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The weighted `L²` space of a positive density

For a measurable, everywhere positive real weight `w` on a measure space `(α, μ)`, the map

`f ↦ √w · f`

is a linear isometry of `L²(μ.withDensity w)` onto `L²(μ)`, because

`∫ |√w · f|² dμ = ∫ w |f|² dμ = ∫ |f|² d(μ.withDensity w)`.

Positivity of `w` makes `μ` and `μ.withDensity w` mutually absolutely continuous, so the two
almost-everywhere relations coincide and the map is well defined on equivalence classes.
-/

open MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The `ℝ≥0∞`-valued density attached to a real weight. -/
def realDensity (w : α → ℝ) : α → ℝ≥0∞ := fun x => ENNReal.ofReal (w x)

theorem measurable_realDensity {w : α → ℝ} (hw : Measurable w) :
    Measurable (realDensity w) :=
  ENNReal.measurable_ofReal.comp hw

/-- With an everywhere positive weight the weighted measure has the same null sets as `μ`. -/
theorem withDensity_realDensity_ae_eq {w : α → ℝ} (hw : Measurable w) (hpos : ∀ x, 0 < w x)
    {β : Type*} {f g : α → β} :
    f =ᵐ[μ.withDensity (realDensity w)] g ↔ f =ᵐ[μ] g := by
  refine withDensity_ae_eq (measurable_realDensity hw).aemeasurable ?_
  filter_upwards with x
  simpa [realDensity] using hpos x

theorem aestronglyMeasurable_withDensity_realDensity_iff {w : α → ℝ} (hw : Measurable w)
    (hpos : ∀ x, 0 < w x) {β : Type*} [TopologicalSpace β] {f : α → β} :
    AEStronglyMeasurable f (μ.withDensity (realDensity w)) ↔ AEStronglyMeasurable f μ := by
  constructor
  · rintro ⟨g, hg, hfg⟩
    exact ⟨g, hg, (withDensity_realDensity_ae_eq hw hpos).mp hfg⟩
  · rintro ⟨g, hg, hfg⟩
    exact ⟨g, hg, (withDensity_realDensity_ae_eq hw hpos).mpr hfg⟩

/-- The extended norm of a nonnegative real, read in `ℂ`. -/
theorem enorm_ofReal_of_nonneg {a : ℝ} (ha : 0 ≤ a) : ‖(a : ℂ)‖ₑ = ENNReal.ofReal a := by
  rw [show ‖(a : ℂ)‖ₑ = ENNReal.ofReal ‖(a : ℂ)‖ from (ofReal_norm _).symm]
  simp [Complex.norm_real, abs_of_nonneg ha]

/-- The pointwise square-root weight, as a complex scalar. -/
def sqrtWeight (w : α → ℝ) (x : α) : ℂ := (Real.sqrt (w x) : ℂ)

theorem measurable_sqrtWeight {w : α → ℝ} (hw : Measurable w) : Measurable (sqrtWeight w) := by
  unfold sqrtWeight
  fun_prop

omit [MeasurableSpace α] in
theorem sqrtWeight_ne_zero {w : α → ℝ} (hpos : ∀ x, 0 < w x) (x : α) : sqrtWeight w x ≠ 0 := by
  have hs : Real.sqrt (w x) ≠ 0 := (Real.sqrt_pos.mpr (hpos x)).ne'
  simpa [sqrtWeight, Complex.ofReal_eq_zero] using hs

omit [MeasurableSpace α] in
theorem enorm_sqrtWeight_mul {w : α → ℝ} (hpos : ∀ x, 0 < w x) (f : α → ℂ) (x : α) :
    ‖sqrtWeight w x * f x‖ₑ ^ 2 = realDensity w x * ‖f x‖ₑ ^ 2 := by
  have hw0 : 0 ≤ w x := (hpos x).le
  have hs : 0 ≤ Real.sqrt (w x) := Real.sqrt_nonneg _
  rw [enorm_mul, mul_pow]
  congr 1
  rw [sqrtWeight, enorm_ofReal_of_nonneg hs, realDensity, ← ENNReal.ofReal_pow hs,
    Real.sq_sqrt hw0]

/-- The weighted `L²` energy is the plain `L²` energy of the `√w`-multiple. -/
theorem lintegral_enorm_sq_withDensity {w : α → ℝ} (hw : Measurable w) (hpos : ∀ x, 0 < w x)
    {f : α → ℂ} (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(μ.withDensity (realDensity w)) =
      ∫⁻ x, ‖sqrtWeight w x * f x‖ₑ ^ 2 ∂μ := by
  rw [lintegral_withDensity_eq_lintegral_mul₀ (measurable_realDensity hw).aemeasurable
    (hf.enorm.pow_const 2)]
  refine lintegral_congr fun x => ?_
  simpa [Pi.mul_apply] using (enorm_sqrtWeight_mul hpos f x).symm

theorem eLpNorm_two_withDensity {w : α → ℝ} (hw : Measurable w) (hpos : ∀ x, 0 < w x)
    {f : α → ℂ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 (μ.withDensity (realDensity w)) = eLpNorm (fun x => sqrtWeight w x * f x) 2 μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hcast : ∀ y : ℝ≥0∞, y ^ (2 : ℝ) = y ^ (2 : ℕ) := by
    intro y
    rw [← ENNReal.rpow_natCast y 2]
    norm_num
  rw [h2]
  simp_rw [hcast]
  rw [lintegral_enorm_sq_withDensity hw hpos hf]

/-- Membership in the weighted `L²` space is membership of the `√w`-multiple in plain `L²`. -/
theorem memLp_two_withDensity_iff {w : α → ℝ} (hw : Measurable w) (hpos : ∀ x, 0 < w x)
    {f : α → ℂ} :
    MemLp f 2 (μ.withDensity (realDensity w)) ↔ MemLp (fun x => sqrtWeight w x * f x) 2 μ := by
  constructor
  · intro hf
    have hmeas : AEStronglyMeasurable f μ :=
      (aestronglyMeasurable_withDensity_realDensity_iff hw hpos).mp hf.1
    refine ⟨(measurable_sqrtWeight hw).aestronglyMeasurable.mul hmeas, ?_⟩
    rw [← eLpNorm_two_withDensity hw hpos hmeas]
    exact hf.2
  · intro hf
    have hmeas : AEStronglyMeasurable f μ := by
      have hinv : AEStronglyMeasurable
          (fun x => (sqrtWeight w x)⁻¹ * (sqrtWeight w x * f x)) μ :=
        ((measurable_sqrtWeight hw).inv).aestronglyMeasurable.mul hf.1
      refine hinv.congr ?_
      filter_upwards with x
      rw [← mul_assoc, inv_mul_cancel₀ (sqrtWeight_ne_zero hpos x), one_mul]
    refine ⟨(aestronglyMeasurable_withDensity_realDensity_iff hw hpos).mpr hmeas, ?_⟩
    rw [eLpNorm_two_withDensity hw hpos hmeas]
    exact hf.2

end

end GaloisForLFunctions.HTGeometry

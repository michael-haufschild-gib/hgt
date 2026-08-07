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

/-! ### The unitary `f ↦ √w · f` -/

variable (w : α → ℝ) (hw : Measurable w) (hpos : ∀ x, 0 < w x)

/-- The weighted `L²` space of a positive real density. -/
abbrev WeightedL2 : Type _ := Lp ℂ 2 (μ.withDensity (realDensity w))

/-- Multiplication by `√w`, from the weighted space to the plain space. -/
def densityMul (f : WeightedL2 (μ := μ) w) : Lp ℂ 2 μ :=
  ((memLp_two_withDensity_iff hw hpos).mp (Lp.memLp f)).toLp _

theorem densityMul_ae (f : WeightedL2 (μ := μ) w) :
    densityMul w hw hpos f =ᵐ[μ] fun x => sqrtWeight w x * f x :=
  MemLp.coeFn_toLp _

/-- Multiplication by `(√w)⁻¹`, from the plain space to the weighted space. -/
def densityDiv (g : Lp ℂ 2 μ) : WeightedL2 (μ := μ) w := by
  refine MemLp.toLp (fun x => (sqrtWeight w x)⁻¹ * g x) ?_
  refine (memLp_two_withDensity_iff hw hpos).mpr ?_
  refine MemLp.ae_eq ?_ (Lp.memLp g)
  filter_upwards with x
  rw [← mul_assoc, mul_inv_cancel₀ (sqrtWeight_ne_zero hpos x), one_mul]

theorem densityDiv_ae (g : Lp ℂ 2 μ) :
    densityDiv w hw hpos g =ᵐ[μ] fun x => (sqrtWeight w x)⁻¹ * g x := by
  have h := MemLp.coeFn_toLp (μ := μ.withDensity (realDensity w))
    (p := 2) (f := fun x => (sqrtWeight w x)⁻¹ * g x)
    ((memLp_two_withDensity_iff hw hpos).mpr
      (MemLp.ae_eq (by
        filter_upwards with x
        rw [← mul_assoc, mul_inv_cancel₀ (sqrtWeight_ne_zero hpos x), one_mul])
        (Lp.memLp g)))
  exact (withDensity_realDensity_ae_eq hw hpos).mp h

theorem norm_densityMul (f : WeightedL2 (μ := μ) w) : ‖densityMul w hw hpos f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (densityMul_ae w hw hpos f)]
  congr 1
  exact (eLpNorm_two_withDensity hw hpos
    ((aestronglyMeasurable_withDensity_realDensity_iff hw hpos).mp (Lp.aestronglyMeasurable f))).symm

theorem densityMul_add (f g : WeightedL2 (μ := μ) w) :
    densityMul w hw hpos (f + g) = densityMul w hw hpos f + densityMul w hw hpos g := by
  apply Lp.ext
  have hfg : ((f + g : WeightedL2 (μ := μ) w) : α → ℂ) =ᵐ[μ] fun x => f x + g x :=
    (withDensity_realDensity_ae_eq hw hpos).mp (Lp.coeFn_add f g)
  filter_upwards [densityMul_ae w hw hpos (f + g), densityMul_ae w hw hpos f,
    densityMul_ae w hw hpos g, hfg,
    Lp.coeFn_add (densityMul w hw hpos f) (densityMul w hw hpos g)] with x h1 h2 h3 h4 h5
  rw [h1, h5]
  simp only [Pi.add_apply]
  rw [h2, h3, h4]
  ring

theorem densityMul_smul (c : ℂ) (f : WeightedL2 (μ := μ) w) :
    densityMul w hw hpos (c • f) = c • densityMul w hw hpos f := by
  apply Lp.ext
  have hcf : ((c • f : WeightedL2 (μ := μ) w) : α → ℂ) =ᵐ[μ] fun x => c * f x := by
    refine (withDensity_realDensity_ae_eq hw hpos).mp ?_
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simpa using hx
  filter_upwards [densityMul_ae w hw hpos (c • f), densityMul_ae w hw hpos f, hcf,
    Lp.coeFn_smul c (densityMul w hw hpos f)] with x h1 h2 h3 h4
  rw [h1, h4]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h2, h3]
  ring

theorem densityDiv_densityMul (f : WeightedL2 (μ := μ) w) :
    densityDiv w hw hpos (densityMul w hw hpos f) = f := by
  apply Lp.ext
  refine (withDensity_realDensity_ae_eq hw hpos).mpr ?_
  filter_upwards [densityDiv_ae w hw hpos (densityMul w hw hpos f),
    densityMul_ae w hw hpos f] with x h1 h2
  rw [h1, h2, ← mul_assoc, inv_mul_cancel₀ (sqrtWeight_ne_zero hpos x), one_mul]

theorem densityMul_densityDiv (g : Lp ℂ 2 μ) :
    densityMul w hw hpos (densityDiv w hw hpos g) = g := by
  apply Lp.ext
  filter_upwards [densityMul_ae w hw hpos (densityDiv w hw hpos g),
    densityDiv_ae w hw hpos g] with x h1 h2
  rw [h1, h2, ← mul_assoc, mul_inv_cancel₀ (sqrtWeight_ne_zero hpos x), one_mul]

/-- **The positive-density unitary.**  Multiplication by `√w` identifies the weighted space
`L²(μ.withDensity w)` with the plain space `L²(μ)`. -/
def weightedDensityUnitary : WeightedL2 (μ := μ) w ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := densityMul w hw hpos
  map_add' := densityMul_add w hw hpos
  map_smul' := densityMul_smul w hw hpos
  norm_map' := norm_densityMul w hw hpos
  invFun := densityDiv w hw hpos
  left_inv := densityDiv_densityMul w hw hpos
  right_inv := densityMul_densityDiv w hw hpos

@[simp] theorem weightedDensityUnitary_apply (f : WeightedL2 (μ := μ) w) :
    weightedDensityUnitary w hw hpos f = densityMul w hw hpos f := rfl

@[simp] theorem weightedDensityUnitary_symm_apply (g : Lp ℂ 2 μ) :
    (weightedDensityUnitary w hw hpos).symm g = densityDiv w hw hpos g := rfl

end

end GaloisForLFunctions.HTGeometry

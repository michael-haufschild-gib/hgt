import GaloisForLFunctions.HTGeometry.GomesHausdorffVisibleSource

/-!
# Reflection infrastructure for complementary source observations

Experimental transport of the reconstruction distinction in arXiv:2607.24901, section 4,
to the existing Hausdorff source corpus. Reflection exchanges the endpoint invisible to
Stieltjes observations with the endpoint invisible to the fixed Clark kernel. The parameter
map `t ↦ -t/(1+t)` is an involution of the nonsingular domain `t > -1`.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- The other endpoint of the compact source coordinate. -/
def gomesHausdorffOne : HausdorffSourceSpace := ⟨1, zero_le_one, le_rfl⟩

/-- A unit atom at the endpoint invisible to fixed Clark observations. -/
def gomesHausdorffOneAtom : FiniteMeasure HausdorffSourceSpace :=
  ⟨Measure.dirac gomesHausdorffOne, inferInstance⟩

/-- Reverse the compact source coordinate while preserving its topology. -/
def gomesHausdorffReflection : HausdorffSourceSpace ≃ₜ HausdorffSourceSpace where
  toFun y := ⟨1 - (y : ℝ), by constructor <;> linarith [y.property.1, y.property.2]⟩
  invFun y := ⟨1 - (y : ℝ), by constructor <;> linarith [y.property.1, y.property.2]⟩
  left_inv y := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  continuous_toFun := (continuous_const.sub continuous_subtype_val).subtype_mk
    (fun y => by
      change 0 ≤ 1 - (y : ℝ) ∧ 1 - (y : ℝ) ≤ 1
      constructor <;> linarith [y.property.1, y.property.2])
  continuous_invFun := (continuous_const.sub continuous_subtype_val).subtype_mk
    (fun y => by
      change 0 ≤ 1 - (y : ℝ) ∧ 1 - (y : ℝ) ≤ 1
      constructor <;> linarith [y.property.1, y.property.2])

/-- Reflecting the coordinate twice is the identity. -/
theorem gomesHausdorffReflection_involutive : Function.Involutive gomesHausdorffReflection := by
  intro y
  apply Subtype.ext
  dsimp [gomesHausdorffReflection]
  ring

/-- Reflection exchanges the two endpoints exactly. -/
theorem gomesHausdorffReflection_zero :
    gomesHausdorffReflection gomesHausdorffZero = gomesHausdorffOne := by
  apply Subtype.ext
  simp [gomesHausdorffReflection, gomesHausdorffZero, gomesHausdorffOne]

/-- Reflect the actual finite source measure. -/
def gomesHausdorffReflectSource (μ : FiniteMeasure HausdorffSourceSpace) :
    FiniteMeasure HausdorffSourceSpace := μ.map gomesHausdorffReflection

/-- Reflection loses no measure information. -/
theorem gomesHausdorffReflectSource_involutive :
    Function.Involutive gomesHausdorffReflectSource := by
  intro μ
  apply FiniteMeasure.toMeasure_injective
  change Measure.map gomesHausdorffReflection
    (Measure.map gomesHausdorffReflection (μ : Measure HausdorffSourceSpace)) = μ
  rw [Measure.map_map gomesHausdorffReflection.measurable gomesHausdorffReflection.measurable]
  have hi : gomesHausdorffReflection ∘ gomesHausdorffReflection = id :=
    funext gomesHausdorffReflection_involutive
  rw [hi, Measure.map_id]

/-- The source reflection is injective without normalization assumptions. -/
theorem gomesHausdorffReflectSource_injective : Function.Injective gomesHausdorffReflectSource :=
  gomesHausdorffReflectSource_involutive.injective

/-- Source addition commutes with reflection. -/
theorem gomesHausdorffReflectSource_add (μ ν : FiniteMeasure HausdorffSourceSpace) :
    gomesHausdorffReflectSource (μ + ν) =
      gomesHausdorffReflectSource μ + gomesHausdorffReflectSource ν :=
  FiniteMeasure.map_add gomesHausdorffReflection.measurable μ ν

/-- Nonnegative source scaling commutes with reflection. -/
theorem gomesHausdorffReflectSource_smul (w : ℝ≥0) (μ : FiniteMeasure HausdorffSourceSpace) :
    gomesHausdorffReflectSource (w • μ) = w • gomesHausdorffReflectSource μ :=
  FiniteMeasure.map_smul w μ

/-- The hidden Stieltjes atom reflects to the hidden Clark atom. -/
theorem gomesHausdorffReflectSource_zeroAtom :
    gomesHausdorffReflectSource gomesHausdorffZeroAtom = gomesHausdorffOneAtom := by
  apply FiniteMeasure.toMeasure_injective
  change Measure.map gomesHausdorffReflection (Measure.dirac gomesHausdorffZero) =
    Measure.dirac gomesHausdorffOne
  rw [Measure.map_dirac, gomesHausdorffReflection_zero]

/-- Reflection returns the hidden Clark atom to the hidden Stieltjes atom. -/
theorem gomesHausdorffReflectSource_oneAtom :
    gomesHausdorffReflectSource gomesHausdorffOneAtom = gomesHausdorffZeroAtom := by
  apply gomesHausdorffReflectSource_injective
  rw [gomesHausdorffReflectSource_involutive, gomesHausdorffReflectSource_zeroAtom]

/-- Reflection preserves total source mass. -/
theorem gomesHausdorffReflectSource_mass (μ : FiniteMeasure HausdorffSourceSpace) :
    (gomesHausdorffReflectSource μ).mass = μ.mass := by
  change (μ.map gomesHausdorffReflection) Set.univ = μ Set.univ
  rw [FiniteMeasure.map_apply μ gomesHausdorffReflection.measurable MeasurableSet.univ]
  rfl

/-- Every scalar observation transports exactly through reflection, including nonintegrable tests. -/
theorem gomesHausdorffReflectSource_integral (μ : FiniteMeasure HausdorffSourceSpace)
    (f : HausdorffSourceSpace → ℝ) :
    (∫ y, f y ∂(gomesHausdorffReflectSource μ : Measure HausdorffSourceSpace)) =
      ∫ y, f (gomesHausdorffReflection y) ∂(μ : Measure HausdorffSourceSpace) :=
  gomesHausdorffReflection.measurableEmbedding.integral_map f

/-- The parameter change preserving the entire nonsingular Stieltjes domain. -/
def gomesHausdorffDualParameter (t : Set.Ioi (-1 : ℝ)) : Set.Ioi (-1 : ℝ) :=
  ⟨-(t : ℝ) / (1 + (t : ℝ)), by
    have ht : (-1 : ℝ) < t := t.property
    apply (lt_div_iff₀ (show 0 < 1 + (t : ℝ) by linarith)).mpr
    linarith⟩

/-- Dualizing the parameter twice restores it. -/
theorem gomesHausdorffDualParameter_involutive : Function.Involutive gomesHausdorffDualParameter := by
  intro t
  apply Subtype.ext
  have ht : (-1 : ℝ) < t := t.property
  have hd : 1 + (t : ℝ) ≠ 0 := by linarith
  have hd' : 1 + (gomesHausdorffDualParameter t : ℝ) ≠ 0 := by
    have hp : (-1 : ℝ) < gomesHausdorffDualParameter t := (gomesHausdorffDualParameter t).property
    linarith
  dsimp [gomesHausdorffDualParameter] at hd' ⊢
  field_simp [hd, hd']
  ring

/-- Exact kernel duality: reflection turns a fixed Clark test into a Stieltjes test. -/
theorem gomesHausdorffStieltjes_reflection (t : Set.Ioi (-1 : ℝ))
    (y : HausdorffSourceSpace) :
    stieltjesKernel (gomesHausdorffDualParameter t) (gomesHausdorffReflection y) =
      (1 + (t : ℝ)) * (1 - ((t : ℝ) + 1) * stieltjesKernel t y) := by
  have ht : (-1 : ℝ) < t := t.property
  have hd : 1 + (t : ℝ) ≠ 0 := by linarith
  have hy := ne_of_gt (gomesHausdorffStieltjes_denominator_pos t y)
  dsimp [stieltjesKernel, gomesHausdorffDualParameter, gomesHausdorffReflection]
  have he : 1 + (-(t : ℝ) / (1 + (t : ℝ))) * (1 - (y : ℝ)) =
      (1 + (t : ℝ) * (y : ℝ)) / (1 + (t : ℝ)) := by
    field_simp [hd]
    ring
  rw [he]
  have hinv : (1 + (y : ℝ) * (t : ℝ)) * (1 + (y : ℝ) * (t : ℝ))⁻¹ = 1 :=
    mul_inv_cancel₀ (by simpa [mul_comm] using hy)
  field_simp [hd, hy]
  linear_combination hinv

/-- The compact Stieltjes record varies continuously throughout its nonsingular parameter domain. -/
theorem gomesHausdorffStieltjesRecord_continuous (μ : FiniteMeasure HausdorffSourceSpace) :
    Continuous (gomesHausdorffStieltjesRecord μ) := by
  letI : LocallyCompactSpace (Set.Ioi (-1 : ℝ)) := isOpen_Ioi.locallyCompactSpace
  have hf : Continuous (Function.uncurry
      (fun (t : Set.Ioi (-1 : ℝ)) (y : HausdorffSourceSpace) => stieltjesKernel t y)) :=
    (continuous_subtype_val.comp continuous_snd).div
      (continuous_const.add ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)))
      (fun p => ne_of_gt (gomesHausdorffStieltjes_denominator_pos p.1 p.2))
  change Continuous (fun t : Set.Ioi (-1 : ℝ) =>
    ∫ y : HausdorffSourceSpace, stieltjesKernel t y ∂(μ : Measure HausdorffSourceSpace))
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ := (μ : Measure HausdorffSourceSpace))
      hf isCompact_univ)

/-- Erasing any one parameter sample loses no Stieltjes-record information. -/
theorem gomesHausdorffStieltjesRecord_eq_iff_offPoint
    (μ ν : FiniteMeasure HausdorffSourceSpace) (p : Set.Ioi (-1 : ℝ)) :
    gomesHausdorffStieltjesRecord μ = gomesHausdorffStieltjesRecord ν ↔
      ∀ t : {t : Set.Ioi (-1 : ℝ) // t ≠ p},
        gomesHausdorffStieltjesRecord μ t = gomesHausdorffStieltjesRecord ν t := by
  constructor
  · intro h t
    exact congrFun h t
  · intro h
    apply Continuous.ext_on (dense_compl_singleton p)
      (gomesHausdorffStieltjesRecord_continuous μ) (gomesHausdorffStieltjesRecord_continuous ν)
    intro t ht
    exact h ⟨t, ht⟩

end GaloisForLFunctions.HTGeometry

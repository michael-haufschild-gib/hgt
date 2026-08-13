import GaloisForLFunctions.RHTower.FieldOneFiniteStageIdeleFundamentalDomain
import GaloisForLFunctions.RHTower.FieldOneFiniteStageIdeleLocusMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Multiplicative Haar from additive Haar on the finite-stage idele locus

Connes--Marcolli's unfolding formula uses the local identity `da = |a| d* a`.  This file proves
its global finite-stage measure-theoretic foundation on the literal adelic objects.  The
coordinatewise value map is an open embedding from ideles onto the conull idele locus.  Pulling
additive Haar back along this embedding gives the exact scaling law under idele multiplication.
Dividing that pullback measure by the module will therefore produce multiplicative Haar.
-/

open scoped ENNReal NNReal Pointwise

namespace GaloisForLFunctions.RHTower

noncomputable section

open Function IsDedekindDomain MeasureTheory MeasureTheory.Measure Set Topology

noncomputable instance fieldOneRealUnitsBorelSpace : BorelSpace ℝˣ := by
  constructor
  unfold Units.instMeasurableSpace
  calc
    MeasurableSpace.comap Units.val
        (inferInstance : MeasurableSpace ℝ) =
        MeasurableSpace.comap Units.val (borel ℝ) :=
      congrArg (MeasurableSpace.comap Units.val)
        (BorelSpace.measurable_eq (α := ℝ))
    _ = borel ℝˣ := by
      rw [Units.isEmbedding_val₀.toIsInducing.eq_induced]
      exact borel_comap.symm

noncomputable instance fieldOneAdicCompletionUnitsBorelSpace
    (v : HeightOneSpectrum ℤ) :
    BorelSpace (v.adicCompletion ℚ)ˣ := by
  constructor
  unfold Units.instMeasurableSpace
  calc
    MeasurableSpace.comap Units.val
        (inferInstance : MeasurableSpace (v.adicCompletion ℚ)) =
      MeasurableSpace.comap Units.val (borel (v.adicCompletion ℚ)) :=
        congrArg (MeasurableSpace.comap Units.val)
          (BorelSpace.measurable_eq (α := v.adicCompletion ℚ))
    _ = borel (v.adicCompletion ℚ)ˣ := by
      rw [Units.isEmbedding_val₀.toIsInducing.eq_induced]
      exact borel_comap.symm

/-- Coordinatewise units are homeomorphic to the coordinatewise nonzero adelic locus. -/
def fieldOneFiniteStageIdeleLocusHomeomorph
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageIdele S ≃ₜ ↥(fieldOneFiniteStageIdeleLocus S) where
  toFun u := ⟨fieldOneFiniteStageIdeleVal S u,
    ⟨Units.ne_zero u.1, fun v => Units.ne_zero (u.2 v)⟩⟩
  invFun x :=
    (Units.mk0 x.1.1 x.2.1,
      fun v => Units.mk0 (x.1.2 v) (x.2.2 v))
  left_inv u := by
    apply Prod.ext
    · apply Units.ext
      rfl
    · funext v
      apply Units.ext
      rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    exact (fieldOneFiniteStageIdeleVal_continuous S).subtype_mk _
  continuous_invFun := by
    apply Continuous.prodMk
    · have hbase : Continuous
          ((fun x : ↥(fieldOneFiniteStageIdeleLocus S) =>
            ⟨x.1.1, x.2.1⟩) :
            ↥(fieldOneFiniteStageIdeleLocus S) → ↥({r : ℝ | r ≠ 0})) :=
        Continuous.subtype_mk
        (continuous_fst.comp continuous_subtype_val) _
      have h := (unitsHomeomorphNeZero (G₀ := ℝ)).symm.continuous.comp hbase
      convert h using 1
      funext x
      apply Units.ext
      symm
      exact congrArg Subtype.val <|
        (unitsHomeomorphNeZero (G₀ := ℝ)).apply_symm_apply
          ⟨x.1.1, x.2.1⟩
    · apply continuous_pi
      intro v
      have hbase : Continuous
          ((fun x : ↥(fieldOneFiniteStageIdeleLocus S) =>
            ⟨x.1.2 v, x.2.2 v⟩) :
            ↥(fieldOneFiniteStageIdeleLocus S) →
              ↥({r : v.1.adicCompletion ℚ | r ≠ 0})) :=
        Continuous.subtype_mk
        ((continuous_apply v).comp
          (continuous_snd.comp continuous_subtype_val)) _
      have h := (unitsHomeomorphNeZero
        (G₀ := v.1.adicCompletion ℚ)).symm.continuous.comp hbase
      convert h using 1
      funext x
      apply Units.ext
      symm
      exact congrArg Subtype.val <|
        (unitsHomeomorphNeZero
          (G₀ := v.1.adicCompletion ℚ)).apply_symm_apply
            ⟨x.1.2 v, x.2.2 v⟩

theorem fieldOneFiniteStageIdeleVal_isOpenEmbedding
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsOpenEmbedding (fieldOneFiniteStageIdeleVal S) := by
  have hlocus : IsOpenEmbedding
      (fun x : ↥(fieldOneFiniteStageIdeleLocus S) =>
        (x.1 : FieldOneFiniteStageAdele S)) :=
    IsOpen.isOpenEmbedding_subtypeVal (fieldOneFiniteStageIdeleLocus_isOpen S)
  have hcomp := hlocus.comp
    (fieldOneFiniteStageIdeleLocusHomeomorph S).isOpenEmbedding
  change IsOpenEmbedding
    ((fun x : ↥(fieldOneFiniteStageIdeleLocus S) => x.1) ∘
      fieldOneFiniteStageIdeleLocusHomeomorph S)
  exact hcomp

/-- Additive Haar restricted to the idele locus, expressed on the idele group itself. -/
def fieldOneFiniteStageIdeleAdditivePullbackMeasure
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measure (FieldOneFiniteStageIdele S) :=
  (fieldOneFiniteStageProductAddHaar S).comap
    (fieldOneFiniteStageIdeleVal S)

instance fieldOneFiniteStageProductAddHaar_isAddHaar
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsAddHaarMeasure (fieldOneFiniteStageProductAddHaar S) := by
  change IsAddHaarMeasure
    ((addHaar : Measure ℝ).prod
      (Measure.pi fun v : ↥S =>
        (addHaar : Measure (v.1.adicCompletion ℚ))))
  infer_instance

instance fieldOneFiniteStageIdeleAdditivePullback_isFiniteOnCompacts
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsFiniteMeasureOnCompacts
      (fieldOneFiniteStageIdeleAdditivePullbackMeasure S) :=
  IsFiniteMeasureOnCompacts.comap'
    (fieldOneFiniteStageProductAddHaar S)
    (fieldOneFiniteStageIdeleVal_continuous S)
    (fieldOneFiniteStageIdeleVal_isOpenEmbedding S).measurableEmbedding

instance fieldOneFiniteStageIdeleAdditivePullback_isOpenPos
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsOpenPosMeasure
      (fieldOneFiniteStageIdeleAdditivePullbackMeasure S) :=
  IsOpenPosMeasure.comap
    (fieldOneFiniteStageProductAddHaar S)
    (fieldOneFiniteStageIdeleVal_isOpenEmbedding S)

/-- Pullback additive Haar scales under left multiplication by the inverse module. -/
theorem fieldOneFiniteStageIdeleAdditivePullback_map_mul_left
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) :
    Measure.map (u * ·)
        (fieldOneFiniteStageIdeleAdditivePullbackMeasure S) =
      (fieldOneFiniteStageModule S u⁻¹ : ℝ≥0∞) •
        fieldOneFiniteStageIdeleAdditivePullbackMeasure S := by
  apply Measure.ext
  intro s hs
  have hmul : Measurable (u * ·) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hmul hs,
    fieldOneFiniteStageIdeleAdditivePullbackMeasure,
    (fieldOneFiniteStageIdeleVal_isOpenEmbedding S).measurableEmbedding.comap_apply,
    Measure.smul_apply]
  have himage :
      fieldOneFiniteStageIdeleVal S '' ((u * ·) ⁻¹' s) =
        u⁻¹ • (fieldOneFiniteStageIdeleVal S '' s) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨fieldOneFiniteStageIdeleVal S (u * v), ⟨u * v, hv, rfl⟩, ?_⟩
      rw [fieldOneFiniteStageIdeleVal_mul]
      simp
    · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨u⁻¹ * v, ?_, ?_⟩
      · simpa using hv
      · rw [fieldOneFiniteStageIdeleVal_mul]
  rw [himage, fieldOneFiniteStage_measure_smul]
  rw [(fieldOneFiniteStageIdeleVal_isOpenEmbedding S).measurableEmbedding.comap_apply]
  rfl

private theorem map_withDensity_measurableEquiv
    {α : Type*} [MeasurableSpace α]
    (e : α ≃ᵐ α) (μ : Measure α) (f : α → ℝ≥0∞)
    (hf : Measurable f) :
    Measure.map e (μ.withDensity f) =
      (Measure.map e μ).withDensity (f ∘ e.symm) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs]
  let g : α → ℝ≥0∞ := s.indicator (f ∘ e.symm)
  have hg : Measurable g :=
    (hf.comp e.symm.measurable).indicator hs
  calc
    (∫⁻ x in e ⁻¹' s, f x ∂μ) =
        ∫⁻ x, (e ⁻¹' s).indicator f x ∂μ :=
      (lintegral_indicator (hs.preimage e.measurable) _).symm
    _ = ∫⁻ x, g (e x) ∂μ := by
      apply lintegral_congr
      intro x
      by_cases hx : e x ∈ s
      · simp [g, hx]
      · simp [g, hx]
    _ = ∫⁻ y, g y ∂Measure.map e μ :=
      (lintegral_map hg e.measurable).symm
    _ = ∫⁻ y in s, f (e.symm y) ∂Measure.map e μ :=
      lintegral_indicator hs _

/-- Reciprocal module, the exact Radon--Nikodym density `d* a = da / |a|`. -/
def fieldOneFiniteStageIdeleModuleInvDensity
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) : ℝ≥0∞ :=
  ((fieldOneFiniteStageModule S u)⁻¹ : ℝ≥0)

theorem fieldOneFiniteStageIdeleModuleInvDensity_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageIdeleModuleInvDensity S) := by
  exact ENNReal.continuous_coe.comp
    (continuous_inv₀.comp (fieldOneFiniteStageModule_continuous S))

theorem fieldOneFiniteStageIdeleModuleInvDensity_mul_left
    (S : Finset (HeightOneSpectrum ℤ))
    (u x : FieldOneFiniteStageIdele S) :
    fieldOneFiniteStageIdeleModuleInvDensity S (u⁻¹ * x) =
      (fieldOneFiniteStageModule S u : ℝ≥0∞) *
        fieldOneFiniteStageIdeleModuleInvDensity S x := by
  simp only [fieldOneFiniteStageIdeleModuleInvDensity, map_mul]
  have hu : fieldOneFiniteStageModule S u ≠ 0 :=
    (map_ne_zero_iff (fieldOneFiniteStageModule S)).2 (Units.ne_zero <|
      (fieldOneFiniteStageModule S).toHomUnits u)
  rw [show fieldOneFiniteStageModule S u⁻¹ =
      (fieldOneFiniteStageModule S u)⁻¹ by
    exact map_inv₀ (fieldOneFiniteStageModule S) hu]
  rw [inv_mul, inv_inv]
  norm_cast

/-- Multiplicative measure obtained by dividing pulled-back additive Haar by the module. -/
def fieldOneFiniteStageIdeleMultiplicativeFromAdditive
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measure (FieldOneFiniteStageIdele S) :=
  (fieldOneFiniteStageIdeleAdditivePullbackMeasure S).withDensity
    (fieldOneFiniteStageIdeleModuleInvDensity S)

instance fieldOneFiniteStageIdeleMultiplicativeFromAdditive_isMulLeftInvariant
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsMulLeftInvariant
      (fieldOneFiniteStageIdeleMultiplicativeFromAdditive S) where
  map_mul_left_eq_self u := by
    let e : FieldOneFiniteStageIdele S ≃ᵐ FieldOneFiniteStageIdele S :=
      (Homeomorph.mulLeft u).toMeasurableEquiv
    have he : (e : FieldOneFiniteStageIdele S → FieldOneFiniteStageIdele S) =
        (u * ·) := rfl
    have hesymm : (e.symm : FieldOneFiniteStageIdele S →
        FieldOneFiniteStageIdele S) = (u⁻¹ * ·) := rfl
    rw [fieldOneFiniteStageIdeleMultiplicativeFromAdditive,
      ← he, map_withDensity_measurableEquiv e _ _
        (fieldOneFiniteStageIdeleModuleInvDensity_continuous S).measurable,
      he, fieldOneFiniteStageIdeleAdditivePullback_map_mul_left,
      withDensity_smul_measure, hesymm]
    have hdensity :
        fieldOneFiniteStageIdeleModuleInvDensity S ∘ (u⁻¹ * ·) =
          (fieldOneFiniteStageModule S u : ℝ≥0∞) •
            fieldOneFiniteStageIdeleModuleInvDensity S := by
      funext x
      exact fieldOneFiniteStageIdeleModuleInvDensity_mul_left S u x
    rw [hdensity, withDensity_smul,
      smul_smul]
    have hu0 : (fieldOneFiniteStageModule S u : ℝ≥0∞) ≠ 0 := by
      simp
    have huTop : (fieldOneFiniteStageModule S u : ℝ≥0∞) ≠ ∞ :=
      ENNReal.coe_ne_top
    rw [show (fieldOneFiniteStageModule S u⁻¹ : ℝ≥0∞) =
        (fieldOneFiniteStageModule S u : ℝ≥0∞)⁻¹ by
      rw [map_inv₀]
      · exact ENNReal.coe_inv (by simp)
      · simp,
      ENNReal.inv_mul_cancel hu0 huTop, one_smul]

end

end GaloisForLFunctions.RHTower

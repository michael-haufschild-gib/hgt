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

open scoped ENNReal NNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open Function IsDedekindDomain MeasureTheory MeasureTheory.Measure Set Topology

noncomputable instance fieldOneRealUnitsBorelSpace : BorelSpace ℝˣ := by
  constructor
  unfold Units.instMeasurableSpace
  calc
    MeasurableSpace.comap Units.val Real.instMeasurableSpace =
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
    · exact ((unitsHomeomorphNeZero (G₀ := ℝ)).symm.continuous.comp <|
        continuous_fst.comp continuous_subtype_val)
    · apply continuous_pi
      intro v
      exact ((unitsHomeomorphNeZero
        (G₀ := v.1.adicCompletion ℚ)).symm.continuous.comp <|
        (continuous_apply v).comp (continuous_snd.comp continuous_subtype_val)

theorem fieldOneFiniteStageIdeleVal_isOpenEmbedding
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsOpenEmbedding (fieldOneFiniteStageIdeleVal S) := by
  have hlocus : IsOpenEmbedding
      (fun x : ↥(fieldOneFiniteStageIdeleLocus S) =>
        (x.1 : FieldOneFiniteStageAdele S)) :=
    IsOpen.isOpenEmbedding_subtypeVal (fieldOneFiniteStageIdeleLocus_isOpen S)
  have hcomp := hlocus.comp
    (fieldOneFiniteStageIdeleLocusHomeomorph S).isOpenEmbedding
  convert hcomp using 1

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
  rfl

end

end GaloisForLFunctions.RHTower

import GaloisForLFunctions.RHTower.FieldOneFiniteStageModuleOneCompact
import GaloisForLFunctions.RHTower.FieldOneFiniteStageIdeleClassHaarL2
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Haar splitting of finite-stage idele classes

The canonical topological group splitting
`C_S ≃ K_S × ℝ₊ˣ` is upgraded to the source normalization of Haar
measure: `K_S` receives probability Haar and the positive factor receives
multiplicative Haar.  The resulting product measure is transported to `C_S`,
and the transport is proved measure preserving and unitary on `L²`.

The positive-factor pullback is also constructed as an isometric embedding
and proved pointwise fixed by every `K_S` translation.  The reverse fixed-point
classification is a separate theorem, since it requires Haar averaging and
Fubini rather than formal transport alone.
-/

open scoped NNReal ENNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain MeasureTheory MeasureTheory.Measure Set TopologicalSpace

noncomputable instance fieldOnePositiveUnitsSecondCountableTopology :
    SecondCountableTopology ℝ≥0ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

noncomputable instance fieldOnePositiveUnitsBorelSpace : BorelSpace ℝ≥0ˣ := by
  constructor
  unfold Units.instMeasurableSpace
  calc
    MeasurableSpace.comap Units.val NNReal.measurableSpace =
        MeasurableSpace.comap Units.val (borel ℝ≥0) :=
      congrArg (MeasurableSpace.comap Units.val)
        (BorelSpace.measurable_eq (α := ℝ≥0))
    _ = borel ℝ≥0ˣ := by
      rw [Units.isEmbedding_val₀.toIsInducing.eq_induced]
      exact borel_comap.symm

noncomputable instance fieldOneFiniteStageModuleOneSecondCountableTopology
    (S : Finset (HeightOneSpectrum ℤ)) :
    SecondCountableTopology (FieldOneFiniteStageModuleOneClass S) :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

def fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageIdeleClassGroup S ≃ₜ*
      FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ where
  toMulEquiv := fieldOneFiniteStageIdeleClassSplitMulEquiv S
  continuous_toFun :=
    (fieldOneFiniteStageIdeleClassSplitHomeomorph S).continuous
  continuous_invFun :=
    (fieldOneFiniteStageIdeleClassSplitHomeomorph S).symm.continuous

def fieldOneFiniteStageModuleOnePositiveCompact
    (S : Finset (HeightOneSpectrum ℤ)) :
    PositiveCompacts (FieldOneFiniteStageModuleOneClass S) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

def fieldOneFiniteStageModuleOneProbabilityHaarMeasure
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measure (FieldOneFiniteStageModuleOneClass S) :=
  haarMeasure (fieldOneFiniteStageModuleOnePositiveCompact S)

instance fieldOneFiniteStageModuleOneProbabilityHaar_isHaar
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsHaarMeasure (fieldOneFiniteStageModuleOneProbabilityHaarMeasure S) := by
  change IsHaarMeasure (haarMeasure (fieldOneFiniteStageModuleOnePositiveCompact S))
  infer_instance

instance fieldOneFiniteStageModuleOneProbabilityHaar_isProbability
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsProbabilityMeasure (fieldOneFiniteStageModuleOneProbabilityHaarMeasure S) where
  measure_univ := by
    simpa [fieldOneFiniteStageModuleOneProbabilityHaarMeasure,
      fieldOneFiniteStageModuleOnePositiveCompact] using
      (haarMeasure_self (K₀ := fieldOneFiniteStageModuleOnePositiveCompact S))

abbrev fieldOnePositiveUnitsHaarMeasure : Measure ℝ≥0ˣ := haar

def fieldOneFiniteStageSplitProductHaarMeasure
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measure (FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ) :=
  (fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod fieldOnePositiveUnitsHaarMeasure

instance fieldOneFiniteStageSplitProductHaar_isHaar
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsHaarMeasure (fieldOneFiniteStageSplitProductHaarMeasure S) := by
  change IsHaarMeasure
    ((fieldOneFiniteStageModuleOneProbabilityHaarMeasure S).prod
      (haar : Measure ℝ≥0ˣ))
  infer_instance

def fieldOneFiniteStageSplitHaarMeasure
    (S : Finset (HeightOneSpectrum ℤ)) :
    Measure (FieldOneFiniteStageIdeleClassGroup S) :=
  (fieldOneFiniteStageSplitProductHaarMeasure S).map
    (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).symm

instance fieldOneFiniteStageSplitHaar_isHaar
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsHaarMeasure (fieldOneFiniteStageSplitHaarMeasure S) := by
  change IsHaarMeasure
    ((fieldOneFiniteStageSplitProductHaarMeasure S).map
      (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).symm)
  infer_instance

theorem fieldOneFiniteStageSplit_measurePreserving
    (S : Finset (HeightOneSpectrum ℤ)) :
    MeasurePreserving (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S)
      (fieldOneFiniteStageSplitHaarMeasure S) (fieldOneFiniteStageSplitProductHaarMeasure S) where
  measurable := (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).continuous.measurable
  map_eq := by
    exact (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).toMeasurableEquiv.map_map_symm

theorem fieldOneFiniteStageSplit_symm_measurePreserving
    (S : Finset (HeightOneSpectrum ℤ)) :
    MeasurePreserving (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).symm
      (fieldOneFiniteStageSplitProductHaarMeasure S) (fieldOneFiniteStageSplitHaarMeasure S) where
  measurable := (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).symm.continuous.measurable
  map_eq := rfl

abbrev FieldOneFiniteStageSplitClassL2 (S : Finset (HeightOneSpectrum ℤ)) :=
  Lp (α := FieldOneFiniteStageIdeleClassGroup S) ℂ 2
    (fieldOneFiniteStageSplitHaarMeasure S)

abbrev FieldOneFiniteStageSplitProductL2 (S : Finset (HeightOneSpectrum ℤ)) :=
  Lp (α := FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ) ℂ 2
    (fieldOneFiniteStageSplitProductHaarMeasure S)

def fieldOneFiniteStageSplitL2Unitary (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageSplitClassL2 S ≃ₗᵢ[ℂ] FieldOneFiniteStageSplitProductL2 S where
  __ := Lp.compMeasurePreservingₗᵢ ℂ
    (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).symm
      (fieldOneFiniteStageSplit_symm_measurePreserving S)
  invFun := Lp.compMeasurePreserving (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S)
    (fieldOneFiniteStageSplit_measurePreserving S)
  left_inv f := by
    change
      Lp.compMeasurePreserving (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S)
          (fieldOneFiniteStageSplit_measurePreserving S)
        (Lp.compMeasurePreserving (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).symm
          (fieldOneFiniteStageSplit_symm_measurePreserving S) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f
      (fieldOneFiniteStageSplit_symm_measurePreserving S)
      (fieldOneFiniteStageSplit_measurePreserving S)]
    simp
  right_inv f := by
    change
      Lp.compMeasurePreserving (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).symm
          (fieldOneFiniteStageSplit_symm_measurePreserving S)
        (Lp.compMeasurePreserving (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S)
          (fieldOneFiniteStageSplit_measurePreserving S) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f
      (fieldOneFiniteStageSplit_measurePreserving S)
      (fieldOneFiniteStageSplit_symm_measurePreserving S)]
    simp

abbrev FieldOnePositiveUnitsL2 :=
  Lp (α := ℝ≥0ˣ) ℂ 2 fieldOnePositiveUnitsHaarMeasure

def fieldOneFiniteStageRadialInclusion (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOnePositiveUnitsL2 →ₗᵢ[ℂ] FieldOneFiniteStageSplitProductL2 S :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.snd
    (measurePreserving_snd (μ := fieldOneFiniteStageModuleOneProbabilityHaarMeasure S)
      (ν := fieldOnePositiveUnitsHaarMeasure))

theorem fieldOneFiniteStageRadialInclusion_ae
    (S : Finset (HeightOneSpectrum ℤ)) (f : FieldOnePositiveUnitsL2) :
    fieldOneFiniteStageRadialInclusion S f =ᵐ[fieldOneFiniteStageSplitProductHaarMeasure S]
      fun x => f x.2 :=
  Lp.coeFn_compMeasurePreserving f
    (measurePreserving_snd (μ := fieldOneFiniteStageModuleOneProbabilityHaarMeasure S)
      (ν := fieldOnePositiveUnitsHaarMeasure))

def fieldOneFiniteStageProductModuleOneLeftRegular
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S) :
    FieldOneFiniteStageSplitProductL2 S ≃ₗᵢ[ℂ] FieldOneFiniteStageSplitProductL2 S where
  __ := Lp.compMeasurePreservingₗᵢ ℂ ((k⁻¹, 1) * ·)
    (measurePreserving_mul_left (fieldOneFiniteStageSplitProductHaarMeasure S) (k⁻¹, 1))
  invFun := Lp.compMeasurePreserving ((k, 1) * ·)
    (measurePreserving_mul_left (fieldOneFiniteStageSplitProductHaarMeasure S) (k, 1))
  left_inv f := by
    change Lp.compMeasurePreserving ((k, 1) * ·)
        (measurePreserving_mul_left (fieldOneFiniteStageSplitProductHaarMeasure S) (k, 1))
      (Lp.compMeasurePreserving ((k⁻¹, 1) * ·)
        (measurePreserving_mul_left (fieldOneFiniteStageSplitProductHaarMeasure S) (k⁻¹, 1)) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f
      (measurePreserving_mul_left (fieldOneFiniteStageSplitProductHaarMeasure S) (k⁻¹, 1))
      (measurePreserving_mul_left (fieldOneFiniteStageSplitProductHaarMeasure S) (k, 1))]
    have hfun : (((k⁻¹, 1) * ·) ∘ ((k, 1) * ·)) =
        (id : (FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ) → _) := by
      funext x
      apply Prod.ext <;> simp [← mul_assoc]
    simpa only [hfun] using Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    change Lp.compMeasurePreserving ((k⁻¹, 1) * ·)
        (measurePreserving_mul_left (fieldOneFiniteStageSplitProductHaarMeasure S) (k⁻¹, 1))
      (Lp.compMeasurePreserving ((k, 1) * ·)
        (measurePreserving_mul_left (fieldOneFiniteStageSplitProductHaarMeasure S) (k, 1)) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f
      (measurePreserving_mul_left (fieldOneFiniteStageSplitProductHaarMeasure S) (k, 1))
      (measurePreserving_mul_left (fieldOneFiniteStageSplitProductHaarMeasure S) (k⁻¹, 1))]
    have hfun : (((k, 1) * ·) ∘ ((k⁻¹, 1) * ·)) =
        (id : (FieldOneFiniteStageModuleOneClass S × ℝ≥0ˣ) → _) := by
      funext x
      apply Prod.ext <;> simp [← mul_assoc]
    simpa only [hfun] using Lp.compMeasurePreserving_id_apply f

def fieldOneFiniteStageProductModuleOneInvariantSubmodule
    (S : Finset (HeightOneSpectrum ℤ)) :
    Submodule ℂ (FieldOneFiniteStageSplitProductL2 S) where
  carrier := {f | ∀ k, fieldOneFiniteStageProductModuleOneLeftRegular S k f = f}
  zero_mem' := by intro k; simp
  add_mem' := by
    intro f g hf hg k
    rw [map_add, hf k, hg k]
  smul_mem' := by
    intro c f hf k
    rw [map_smul, hf k]

theorem fieldOneFiniteStageRadialInclusion_mem_invariants
    (S : Finset (HeightOneSpectrum ℤ)) (f : FieldOnePositiveUnitsL2) :
    fieldOneFiniteStageRadialInclusion S f ∈ fieldOneFiniteStageProductModuleOneInvariantSubmodule S := by
  intro k
  change Lp.compMeasurePreserving ((k⁻¹, 1) * ·)
      (measurePreserving_mul_left
        (fieldOneFiniteStageSplitProductHaarMeasure S) (k⁻¹, 1))
      (fieldOneFiniteStageRadialInclusion S f) = fieldOneFiniteStageRadialInclusion S f
  apply Lp.ext
  have hrad := fieldOneFiniteStageRadialInclusion_ae S f
  have hrad' := (measurePreserving_mul_left
    (fieldOneFiniteStageSplitProductHaarMeasure S) (k⁻¹, 1)).quasiMeasurePreserving
      |>.ae_eq_comp hrad
  filter_upwards [Lp.coeFn_compMeasurePreserving (fieldOneFiniteStageRadialInclusion S f)
      (measurePreserving_mul_left
        (fieldOneFiniteStageSplitProductHaarMeasure S) (k⁻¹, 1)), hrad', hrad]
      with x hleft hcomp hout
  rw [hleft, hcomp, hout]
  simp

def fieldOneFiniteStageRadialSubmodule (S : Finset (HeightOneSpectrum ℤ)) :
    Submodule ℂ (FieldOneFiniteStageSplitProductL2 S) :=
  LinearMap.range (fieldOneFiniteStageRadialInclusion S).toLinearMap

theorem fieldOneFiniteStageRadialSubmodule_le_invariants
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageRadialSubmodule S ≤ fieldOneFiniteStageProductModuleOneInvariantSubmodule S := by
  rintro _ ⟨f, rfl⟩
  exact fieldOneFiniteStageRadialInclusion_mem_invariants S f

end

end GaloisForLFunctions.RHTower

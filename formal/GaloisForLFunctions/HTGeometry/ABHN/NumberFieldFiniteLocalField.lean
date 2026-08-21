/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NumberFieldFiniteValuationSequence
import GaloisForLFunctions.HTGeometry.MilnorKTameResidueFinite
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Finite completions of number fields are nonarchimedean local fields

For every finite place of a number field, this module transports finite residue-field data through
adic completion and assembles the complete discretely valued local-field package. In particular,
the packaged completion is locally compact, henselian, has finite residue field, and has a DVR of
integers. These are prerequisites for local class field theory, not a construction of its
reciprocity map or Brauer invariant.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain NumberField
open scoped ValuativeRel WithZero WithZeroMulInt

universe u

noncomputable section

variable (K : Type u) [Field K] [NumberField K]

/-- The integral ring of a finite number-field completion is canonically its valued-integer ring. -/
noncomputable def numberFieldAdicCompletionIntegersEquivValuedInteger
    (v : NumberField.FinitePlace K) :
    v.maximalIdeal.adicCompletionIntegers K ≃+*
      (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).integer := by
  let h := HeightOneSpectrum.adicCompletionIntegers.integers K v.maximalIdeal
  let f : v.maximalIdeal.adicCompletionIntegers K →+*
      (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).integer :=
    (algebraMap (v.maximalIdeal.adicCompletionIntegers K)
      (v.maximalIdeal.adicCompletion K)).codRestrict _ (fun x => h.map_le_one x)
  refine RingEquiv.ofBijective f ?_
  constructor
  · intro x y hxy
    exact h.hom_inj (congrArg Subtype.val hxy)
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := h.exists_of_le_one hx
    exact ⟨y, Subtype.ext hy⟩

/-- The completed valuation extends the finite-place valuation of the number field. -/
noncomputable instance numberFieldAdicCompletionValuationHasExtension
    (v : NumberField.FinitePlace K) :
    (v.maximalIdeal.valuation K).HasExtension
      (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰) where
  val_isEquiv_comap := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    simp only [Valuation.comap_apply]
    change (v.maximalIdeal.valuation K) x ≤ 1 ↔
      Valued.v (↑x : v.maximalIdeal.adicCompletion K) ≤ 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      v.maximalIdeal x]

/-- Reduction from the pre-completion valuation ring onto the completed residue field is onto. -/
theorem numberFieldAdicCompletion_residueField_map_surjective
    (v : NumberField.FinitePlace K) :
    Function.Surjective <|
      IsLocalRing.ResidueField.map
        (algebraMap (v.maximalIdeal.valuation K).integer
          (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).integer) := by
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective
    (R := (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).integer) z
  have hball : IsOpen {a : v.maximalIdeal.adicCompletion K | Valued.v.restrict a < 1} :=
    Valued.isOpen_ball (v.maximalIdeal.adicCompletion K) 1
  have hpreimage : IsOpen {a : v.maximalIdeal.adicCompletion K |
      Valued.v.restrict (a - x) < 1} :=
    hball.preimage (continuous_id.sub continuous_const)
  obtain ⟨y, hy⟩ :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v.maximalIdeal |>.mem_nhds
      (hpreimage.mem_nhds (show Valued.v.restrict
        ((x : v.maximalIdeal.adicCompletion K) - x) < 1 by simp))
  change Valued.v.restrict ((↑y : v.maximalIdeal.adicCompletion K) - x) < 1 at hy
  have hy_lt : Valued.v ((↑y : v.maximalIdeal.adicCompletion K) - x) < 1 := by
    exact (Valued.v).restrict_lt_one_iff.mp hy
  have hy_comp : Valued.v (↑y : v.maximalIdeal.adicCompletion K) ≤ 1 := by
    calc
      Valued.v (↑y : v.maximalIdeal.adicCompletion K) =
          Valued.v (x + ((↑y : v.maximalIdeal.adicCompletion K) - x)) := by
        congr 1
        abel
      _ ≤ max (Valued.v (x : v.maximalIdeal.adicCompletion K))
          (Valued.v ((↑y : v.maximalIdeal.adicCompletion K) - x)) :=
        Valued.v.map_add _ _
      _ ≤ 1 := max_le x.2 (le_of_lt hy_lt)
  have hy_integer : (v.maximalIdeal.valuation K) y ≤ 1 := by
    rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      v.maximalIdeal y]
    exact hy_comp
  let y' : (v.maximalIdeal.valuation K).integer := ⟨y, hy_integer⟩
  refine ⟨IsLocalRing.residue _ y', ?_⟩
  rw [IsLocalRing.ResidueField.map_residue]
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal]
  change ¬ IsUnit ((algebraMap (v.maximalIdeal.valuation K).integer
    (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).integer y') - x)
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change Valued.v (
    ((algebraMap (v.maximalIdeal.valuation K).integer
      (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).integer y' :
      (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).integer) :
        v.maximalIdeal.adicCompletion K) - (x : v.maximalIdeal.adicCompletion K)) < 1
  rw [Valuation.HasExtension.val_algebraMap]
  change Valued.v ((algebraMap K (v.maximalIdeal.adicCompletion K) y) - x) < 1
  simpa only [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
    Algebra.algebraMap_self, RingHom.id_apply, Function.comp_apply] using hy_lt

/-- The residue field of every finite number-field completion is finite. -/
noncomputable instance numberFieldAdicCompletionFiniteResidueField
    (v : NumberField.FinitePlace K) :
    Finite (IsLocalRing.ResidueField
      ((Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).integer)) := by
  letI : Finite (RingOfIntegers K ⧸ v.maximalIdeal.asIdeal) :=
    GaloisForLFunctions.HTGeometry.finite_quotient_asIdeal K v.maximalIdeal
  letI : Finite (IsLocalRing.ResidueField
      ((v.maximalIdeal.valuation K).valuationSubring)) :=
    GaloisForLFunctions.HTGeometry.finite_residueField_valuationSubring K v.maximalIdeal
  let e : (v.maximalIdeal.valuation K).valuationSubring ≃+*
      (v.maximalIdeal.valuation K).integer := RingEquiv.subringCongr rfl
  letI : Finite (IsLocalRing.ResidueField ((v.maximalIdeal.valuation K).integer)) :=
    Finite.of_equiv (IsLocalRing.ResidueField
      ((v.maximalIdeal.valuation K).valuationSubring))
      (IsLocalRing.ResidueField.mapEquiv e).toEquiv
  apply Finite.of_surjective
    (IsLocalRing.ResidueField.map
      (algebraMap (v.maximalIdeal.valuation K).integer
        (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).integer))
  exact numberFieldAdicCompletion_residueField_map_surjective K v

/-- The valued-integer ring at a finite number-field completion is a DVR. -/
noncomputable instance numberFieldAdicCompletionValuedIntegerDVR
    (v : NumberField.FinitePlace K) :
    IsDiscreteValuationRing
      (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).integer :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (numberFieldAdicCompletionIntegersEquivValuedInteger K v)

noncomputable instance numberFieldAdicCompletionRankOne
    (v : NumberField.FinitePlace K) :
    (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 from one_lt_two)

noncomputable instance numberFieldAdicCompletionNormedField
    (v : NumberField.FinitePlace K) : NormedField (v.maximalIdeal.adicCompletion K) :=
  Valued.toNormedField (v.maximalIdeal.adicCompletion K) ℤᵐ⁰

/-- Complete DVR with finite residue field is proper, hence locally compact. -/
noncomputable instance numberFieldAdicCompletionProperSpace
    (v : NumberField.FinitePlace K) : ProperSpace (v.maximalIdeal.adicCompletion K) :=
  Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

noncomputable instance numberFieldAdicCompletionValuativeRel
    (v : NumberField.FinitePlace K) : ValuativeRel (v.maximalIdeal.adicCompletion K) :=
  .ofValuation (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰)

instance numberFieldAdicCompletionValuationCompatible
    (v : NumberField.FinitePlace K) :
    (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).Compatible :=
  .ofValuation _

/-- Every finite completion of a number field is a nonarchimedean local field. -/
noncomputable instance numberFieldAdicCompletionIsNonarchimedeanLocalField
    (v : NumberField.FinitePlace K) :
    IsNonarchimedeanLocalField (v.maximalIdeal.adicCompletion K) := by
  letI : ValuativeRel (v.maximalIdeal.adicCompletion K) :=
    .ofValuation (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰)
  letI : (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).Compatible :=
    .ofValuation _
  refine {
    toIsValuativeTopology := ?_
    toLocallyCompactSpace := inferInstance
    toIsNontrivial := ?_ }
  · apply IsValuativeTopology.of_mem_nhds_zero_iff_vle
      (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰)
    intro s
    exact Valued.is_topological_valuation s
  · exact
      (ValuativeRel.isNontrivial_iff_isNontrivial
        (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰)).mpr
        (show (Valued.v : Valuation (v.maximalIdeal.adicCompletion K) ℤᵐ⁰).IsNontrivial
          from inferInstance)

/-- The packaged finite-place completion retains its integer-valued adic valuation. -/
noncomputable instance numberFieldFinitePlaceCompletionValued
    (v : NumberField.FinitePlace K) : Valued (completion K (.finite v)) ℤᵐ⁰ := by
  change Valued (v.maximalIdeal.adicCompletion K) ℤᵐ⁰
  infer_instance

noncomputable instance numberFieldFinitePlaceCompletionTopologicalSpace
    (v : NumberField.FinitePlace K) : TopologicalSpace (completion K (.finite v)) := by
  change TopologicalSpace (v.maximalIdeal.adicCompletion K)
  infer_instance

noncomputable instance numberFieldFinitePlaceCompletionUniformSpace
    (v : NumberField.FinitePlace K) : UniformSpace (completion K (.finite v)) := by
  change UniformSpace (v.maximalIdeal.adicCompletion K)
  infer_instance

noncomputable instance numberFieldFinitePlaceCompletionIsUniformAddGroup
    (v : NumberField.FinitePlace K) : IsUniformAddGroup (completion K (.finite v)) := by
  change IsUniformAddGroup (v.maximalIdeal.adicCompletion K)
  infer_instance

noncomputable instance numberFieldFinitePlaceCompletionIsTopologicalAddGroup
    (v : NumberField.FinitePlace K) : IsTopologicalAddGroup (completion K (.finite v)) := by
  change IsTopologicalAddGroup (v.maximalIdeal.adicCompletion K)
  infer_instance

noncomputable instance numberFieldFinitePlaceCompletionLocallyCompact
    (v : NumberField.FinitePlace K) : LocallyCompactSpace (completion K (.finite v)) := by
  change LocallyCompactSpace (v.maximalIdeal.adicCompletion K)
  infer_instance

noncomputable instance numberFieldFinitePlaceCompletionValuativeRel
    (v : NumberField.FinitePlace K) : ValuativeRel (completion K (.finite v)) := by
  change ValuativeRel (v.maximalIdeal.adicCompletion K)
  infer_instance

/-- Every packaged finite completion of a number field is a nonarchimedean local field. -/
noncomputable instance numberFieldFinitePlaceCompletionIsNonarchimedeanLocalField
    (v : NumberField.FinitePlace K) :
    IsNonarchimedeanLocalField (completion K (.finite v)) := by
  change IsNonarchimedeanLocalField (v.maximalIdeal.adicCompletion K)
  infer_instance

noncomputable instance numberFieldFinitePlaceCompletionIsDiscreteValuationRing
    (v : NumberField.FinitePlace K) :
    IsDiscreteValuationRing 𝒪[completion K (.finite v)] := by
  change IsDiscreteValuationRing 𝒪[v.maximalIdeal.adicCompletion K]
  infer_instance

noncomputable instance numberFieldFinitePlaceCompletionFiniteResidueField
    (v : NumberField.FinitePlace K) : Finite 𝓀[completion K (.finite v)] := by
  change Finite 𝓀[v.maximalIdeal.adicCompletion K]
  infer_instance

/-- The valuation ring of a finite number-field completion is complete for its maximal-ideal
adic topology. -/
theorem numberFieldFinitePlaceCompletion_isAdicComplete
    (v : NumberField.FinitePlace K) :
    IsAdicComplete 𝓂[completion K (.finite v)] 𝒪[completion K (.finite v)] := by
  letI := IsTopologicalAddGroup.rightUniformSpace (completion K (.finite v))
  letI := isUniformAddGroup_of_addCommGroup (G := completion K (.finite v))
  infer_instance

/-- The valuation ring of every finite number-field completion is henselian. -/
theorem numberFieldFinitePlaceCompletion_henselianRing
    (v : NumberField.FinitePlace K) :
    HenselianRing 𝒪[completion K (.finite v)] 𝓂[completion K (.finite v)] := by
  letI : IsAdicComplete 𝓂[completion K (.finite v)] 𝒪[completion K (.finite v)] :=
    numberFieldFinitePlaceCompletion_isAdicComplete K v
  infer_instance

/-- The valuation ring of a finite number-field completion is a henselian local ring. -/
theorem numberFieldFinitePlaceCompletion_henselianLocalRing
    (v : NumberField.FinitePlace K) : HenselianLocalRing 𝒪[completion K (.finite v)] := by
  letI : HenselianRing 𝒪[completion K (.finite v)] 𝓂[completion K (.finite v)] :=
    numberFieldFinitePlaceCompletion_henselianRing K v
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a₀ ha₀ hderivative
  exact HenselianRing.is_henselian f hf a₀ ha₀ (hderivative.map (Ideal.Quotient.mk _))

end

end GaloisForLFunctions.HTGeometry.ABHN

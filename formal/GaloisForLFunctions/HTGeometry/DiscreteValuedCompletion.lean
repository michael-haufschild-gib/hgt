import GaloisForLFunctions.HTGeometry.ABHN.RationalFiniteLocalField
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Completion of discretely valued fields with finite residue

Density preserves the residue field: approximate each completed integer within
the open maximal ideal. A nontrivial integer-valued valuation remains discrete
after completion, so finite residue implies compactness of its integer ring and
local compactness of the completed field.
-/

namespace GaloisForLFunctions.HTGeometry.DiscreteValuedCompletion

open scoped WithZero WithZeroMulInt ValuativeRel

noncomputable section

variable (K : Type*) [Field K] [Valued K ℤᵐ⁰]

/-- The completed valuation is an extension of the original valuation. -/
instance valuationHasExtension :
    (Valued.v : Valuation K ℤᵐ⁰).HasExtension
      (Valued.v : Valuation (UniformSpace.Completion K) ℤᵐ⁰) where
  val_isEquiv_comap := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    change Valued.v x ≤ 1 ↔ Valued.v (↑x : UniformSpace.Completion K) ≤ 1
    rw [Valued.valuedCompletion_apply]

/-- Density supplies an original-field representative of every completed residue. -/
theorem residueField_map_surjective :
    Function.Surjective <| IsLocalRing.ResidueField.map
      (algebraMap (Valued.v : Valuation K ℤᵐ⁰).integer
        (Valued.v : Valuation (UniformSpace.Completion K) ℤᵐ⁰).integer) := by
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective
    (R := (Valued.v : Valuation (UniformSpace.Completion K) ℤᵐ⁰).integer) z
  have hball : IsOpen {a : UniformSpace.Completion K | Valued.v.restrict a < 1} :=
    Valued.isOpen_ball (UniformSpace.Completion K) 1
  have hopen : IsOpen {a : UniformSpace.Completion K | Valued.v.restrict (a - x) < 1} :=
    hball.preimage (continuous_id.sub continuous_const)
  obtain ⟨y, hy⟩ := UniformSpace.Completion.denseRange_coe.mem_nhds
    (hopen.mem_nhds (show Valued.v.restrict
      ((x : UniformSpace.Completion K) - x) < 1 by simp))
  have hy_lt : Valued.v ((↑y : UniformSpace.Completion K) - x) < 1 :=
    (Valued.v).restrict_lt_one_iff.mp hy
  have hy_comp : Valued.v (↑y : UniformSpace.Completion K) ≤ 1 := by
    calc
      Valued.v (↑y : UniformSpace.Completion K) =
          Valued.v (x + ((↑y : UniformSpace.Completion K) - x)) := by congr 1; abel
      _ ≤ max (Valued.v (x : UniformSpace.Completion K))
          (Valued.v ((↑y : UniformSpace.Completion K) - x)) := Valued.v.map_add _ _
      _ ≤ 1 := max_le x.2 hy_lt.le
  have hy_integer : (Valued.v : Valuation K ℤᵐ⁰) y ≤ 1 := by
    rwa [Valued.valuedCompletion_apply] at hy_comp
  let y' : (Valued.v : Valuation K ℤᵐ⁰).integer := ⟨y, hy_integer⟩
  refine ⟨IsLocalRing.residue _ y', ?_⟩
  rw [IsLocalRing.ResidueField.map_residue, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
  change ¬ IsUnit ((algebraMap (Valued.v : Valuation K ℤᵐ⁰).integer
    (Valued.v : Valuation (UniformSpace.Completion K) ℤᵐ⁰).integer y') - x)
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change Valued.v
    (((algebraMap (Valued.v : Valuation K ℤᵐ⁰).integer
      (Valued.v : Valuation (UniformSpace.Completion K) ℤᵐ⁰).integer y') :
      (Valued.v : Valuation (UniformSpace.Completion K) ℤᵐ⁰).integer) -
      (x : UniformSpace.Completion K)) < 1
  rw [Valuation.HasExtension.val_algebraMap]
  exact hy_lt

/-- Completion does not change the residue field of a discretely valued field. -/
def residueFieldEquiv :
    IsLocalRing.ResidueField (Valued.v : Valuation K ℤᵐ⁰).integer ≃+*
      IsLocalRing.ResidueField (Valued.v : Valuation (UniformSpace.Completion K) ℤᵐ⁰).integer :=
  RingEquiv.ofBijective
    (IsLocalRing.ResidueField.map
      (algebraMap (Valued.v : Valuation K ℤᵐ⁰).integer
        (Valued.v : Valuation (UniformSpace.Completion K) ℤᵐ⁰).integer))
    ⟨RingHom.injective _, residueField_map_surjective K⟩

instance finiteResidueField
    [Finite (IsLocalRing.ResidueField (Valued.v : Valuation K ℤᵐ⁰).integer)] :
    Finite (IsLocalRing.ResidueField
      (Valued.v : Valuation (UniformSpace.Completion K) ℤᵐ⁰).integer) :=
  Finite.of_equiv _ (residueFieldEquiv K).toEquiv

variable [(Valued.v : Valuation K ℤᵐ⁰).IsNontrivial]

instance completedValuationNontrivial :
    (Valued.v : Valuation (UniformSpace.Completion K) ℤᵐ⁰).IsNontrivial := by
  obtain ⟨a, ha0, ha1⟩ := Valuation.IsNontrivial.exists_val_nontrivial
    (v := (Valued.v : Valuation K ℤᵐ⁰))
  refine ⟨↑a, ?_, ?_⟩ <;> rwa [Valued.valuedCompletion_apply]

instance completedIntegerDVR :
    IsDiscreteValuationRing
      (Valued.v : Valuation (UniformSpace.Completion K) ℤᵐ⁰).integer :=
  (Valued.v : Valuation (UniformSpace.Completion K) ℤᵐ⁰).valuationSubring_isDiscreteValuationRing

instance completedRankOne :
    (Valued.v : Valuation (UniformSpace.Completion K) ℤᵐ⁰).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 from one_lt_two)

instance completedNormedField : NormedField (UniformSpace.Completion K) :=
  Valued.toNormedField (UniformSpace.Completion K) ℤᵐ⁰

variable [Finite (IsLocalRing.ResidueField (Valued.v : Valuation K ℤᵐ⁰).integer)]

/-- Finite residue and completeness make the completed field locally compact. -/
instance completedProperSpace : ProperSpace (UniformSpace.Completion K) :=
  Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

instance completedIntegerCompact :
    CompactSpace (Valued.v : Valuation (UniformSpace.Completion K) ℤᵐ⁰).integer :=
  Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance

instance completedValuativeRel : ValuativeRel (UniformSpace.Completion K) :=
  .ofValuation (Valued.v : Valuation (UniformSpace.Completion K) ℤᵐ⁰)

instance completedValuationCompatible :
    (Valued.v : Valuation (UniformSpace.Completion K) ℤᵐ⁰).Compatible := .ofValuation _

/-- The completion of an integer-valued field with finite residue is a nonarchimedean local field. -/
instance completedLocalField : IsNonarchimedeanLocalField (UniformSpace.Completion K) :=
  ABHN.isNonarchimedeanLocalField_of_valued_of_locallyCompact (UniformSpace.Completion K) ℤᵐ⁰

end

noncomputable section WithVal

variable {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)

/-- Transporting a field to its valuation topology preserves its valuation integers. -/
def withValIntegerEquiv :
    (Valued.v : Valuation (WithVal v) ℤᵐ⁰).integer ≃+* v.integer where
  toFun x := ⟨WithVal.equiv v x, x.2⟩
  invFun x := ⟨(WithVal.equiv v).symm x, x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

instance withValFiniteResidue [Finite (IsLocalRing.ResidueField v.integer)] :
    Finite (IsLocalRing.ResidueField (Valued.v : Valuation (WithVal v) ℤᵐ⁰).integer) :=
  Finite.of_equiv _ (IsLocalRing.ResidueField.mapEquiv (withValIntegerEquiv v)).symm.toEquiv

instance withValNontrivial [v.IsNontrivial] :
    (Valued.v : Valuation (WithVal v) ℤᵐ⁰).IsNontrivial := by
  obtain ⟨a, ha0, ha1⟩ := Valuation.IsNontrivial.exists_val_nontrivial (v := v)
  exact ⟨WithVal.toVal v a, ha0, ha1⟩

/-- The original residue field is canonically the residue field of the completion. -/
def valuationCompletionResidueEquiv :
    IsLocalRing.ResidueField v.integer ≃+*
      IsLocalRing.ResidueField (Valued.v : Valuation v.Completion ℤᵐ⁰).integer :=
  (IsLocalRing.ResidueField.mapEquiv (withValIntegerEquiv v)).symm.trans
    (residueFieldEquiv (WithVal v))

/-- A discrete nontrivial valuation with finite residue gives an actual local field. -/
theorem valuationCompletionLocalField [v.IsNontrivial]
    [Finite (IsLocalRing.ResidueField v.integer)] :
    IsNonarchimedeanLocalField v.Completion := inferInstance

end WithVal
end GaloisForLFunctions.HTGeometry.DiscreteValuedCompletion

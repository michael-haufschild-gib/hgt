import GaloisForLFunctions.HTGeometry.ABHN.RationalFiniteLocalField
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Finite-coefficient Laurent series are local fields

For a finite field `F`, this file equips the standard local function field `F((X))` with the
interfaces needed for local class field theory: a discrete rank-one valuation, finite residue
field, local compactness, and Hensel lifting.  It is the concrete Laurent-series model for the
place at infinity of `F(t)`; identifying it with the separately packaged completion remains a
subsequent comparison result.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped LaurentSeries PowerSeries ValuativeRel WithZero WithZeroMulInt

universe u

noncomputable section

/-- The `X`-adic valuation of a Laurent series attains every value in its ambient value group. -/
theorem laurentSeries_valueGroup_eq_top (F : Type u) [Field F] :
    MonoidWithZeroHom.valueGroup
      (.ofClass (Valued.v : Valuation F⸨X⸩ ℤᵐ⁰)) = ⊤ := by
  apply top_unique
  intro x _
  rw [MonoidWithZeroHom.mem_valueGroup_iff_of_comm]
  obtain ⟨a, ha⟩ := LaurentSeries.valuation_surjective F ((x⁻¹ : (ℤᵐ⁰)ˣ) : ℤᵐ⁰)
  refine ⟨a, ?_, 1, ?_⟩
  · change Valued.v a ≠ 0
    rw [ha]
    exact Units.ne_zero _
  · change Valued.v a * (x : ℤᵐ⁰) = Valued.v (1 : F⸨X⸩)
    rw [ha]
    simp

/-- The Laurent-series valuation is discrete of rank one. -/
noncomputable instance laurentSeriesValuationIsRankOneDiscrete
    (F : Type u) [Field F] :
    (Valued.v : Valuation F⸨X⸩ ℤᵐ⁰).IsRankOneDiscrete := by
  letI : IsCyclic (MonoidWithZeroHom.valueGroup
      (.ofClass (Valued.v : Valuation F⸨X⸩ ℤᵐ⁰))) := by
    rw [laurentSeries_valueGroup_eq_top F]
    infer_instance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup
      (.ofClass (Valued.v : Valuation F⸨X⸩ ℤᵐ⁰))) := by
    rw [laurentSeries_valueGroup_eq_top F]
    infer_instance
  exact Valuation.IsRankOneDiscrete.mk' _

/-- The valuation ring of `F((X))` is canonically the power-series ring `F[[X]]`. -/
noncomputable def laurentPowerSeriesEquivValuedInteger
    (F : Type u) [Field F] :
    F⟦X⟧ ≃+* (Valued.v : Valuation F⸨X⸩ ℤᵐ⁰).integer := by
  let f : F⟦X⟧ →+* (Valued.v : Valuation F⸨X⸩ ℤᵐ⁰).integer :=
    (algebraMap F⟦X⟧ F⸨X⸩).codRestrict _ (fun x => by
      change (PowerSeries.idealX F).valuation F⸨X⸩
        (algebraMap F⟦X⟧ F⸨X⸩ x) ≤ 1
      exact (PowerSeries.idealX F).valuation_le_one x)
  refine RingEquiv.ofBijective f ?_
  constructor
  · exact fun x y hxy => HahnSeries.ofPowerSeries_injective (congrArg Subtype.val hxy)
  · rintro ⟨x, hx⟩
    obtain ⟨p, hp⟩ := (LaurentSeries.val_le_one_iff_eq_coe F x).mp hx
    exact ⟨p, Subtype.ext hp⟩

noncomputable instance laurentSeriesValuedIntegerDVR
    (F : Type u) [Field F] :
    IsDiscreteValuationRing (Valued.v : Valuation F⸨X⸩ ℤᵐ⁰).integer :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (laurentPowerSeriesEquivValuedInteger F)

/-- The residue field of `F((X))` is finite when `F` is finite. -/
noncomputable instance laurentSeriesFiniteResidueField
    (F : Type u) [Field F] [Finite F] :
    Finite (IsLocalRing.ResidueField
      ((Valued.v : Valuation F⸨X⸩ ℤᵐ⁰).integer)) := by
  letI : Finite (IsLocalRing.ResidueField F⟦X⟧) :=
    Finite.of_equiv F PowerSeries.residueFieldOfPowerSeries.symm.toEquiv
  exact Finite.of_equiv (IsLocalRing.ResidueField F⟦X⟧)
    (IsLocalRing.ResidueField.mapEquiv
      (laurentPowerSeriesEquivValuedInteger F)).toEquiv

/-- The residue field of the Laurent-series valuation is canonically the coefficient field. -/
noncomputable def laurentSeriesResidueFieldEquiv
    (F : Type u) [Field F] :
    IsLocalRing.ResidueField ((Valued.v : Valuation F⸨X⸩ ℤᵐ⁰).integer) ≃+* F :=
  (IsLocalRing.ResidueField.mapEquiv
    (laurentPowerSeriesEquivValuedInteger F)).symm.trans
      PowerSeries.residueFieldOfPowerSeries

noncomputable instance laurentSeriesRankOne
    (F : Type u) [Field F] :
    (Valued.v : Valuation F⸨X⸩ ℤᵐ⁰).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 from one_lt_two)

noncomputable instance laurentSeriesNormedField
    (F : Type u) [Field F] : NormedField F⸨X⸩ :=
  Valued.toNormedField F⸨X⸩ ℤᵐ⁰

/-- Complete discrete valuation plus finite residue makes `F((X))` proper. -/
noncomputable instance laurentSeriesProperSpace
    (F : Type u) [Field F] [Finite F] : ProperSpace F⸨X⸩ :=
  Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

noncomputable instance laurentSeriesValuativeRel
    (F : Type u) [Field F] : ValuativeRel F⸨X⸩ :=
  .ofValuation (Valued.v : Valuation F⸨X⸩ ℤᵐ⁰)

instance laurentSeriesValuationCompatible
    (F : Type u) [Field F] :
    (Valued.v : Valuation F⸨X⸩ ℤᵐ⁰).Compatible :=
  .ofValuation _

/-- For finite `F`, the Laurent series field `F((X))` is a nonarchimedean local field. -/
noncomputable instance laurentSeriesIsNonarchimedeanLocalField
    (F : Type u) [Field F] [Finite F] :
    IsNonarchimedeanLocalField F⸨X⸩ :=
  isNonarchimedeanLocalField_of_valued_of_locallyCompact F⸨X⸩ ℤᵐ⁰

noncomputable instance laurentSeriesIsDiscreteValuationRing
    (F : Type u) [Field F] [Finite F] :
    IsDiscreteValuationRing 𝒪[F⸨X⸩] := by
  infer_instance

noncomputable instance laurentSeriesFiniteResidueFieldAtInteger
    (F : Type u) [Field F] [Finite F] :
    Finite 𝓀[F⸨X⸩] := by
  infer_instance

/-- The Laurent-series valuation ring is complete in its maximal-ideal adic topology. -/
theorem laurentSeries_isAdicComplete
    (F : Type u) [Field F] [Finite F] :
    IsAdicComplete 𝓂[F⸨X⸩] 𝒪[F⸨X⸩] := by
  letI := IsTopologicalAddGroup.rightUniformSpace F⸨X⸩
  letI := isUniformAddGroup_of_addCommGroup (G := F⸨X⸩)
  infer_instance

/-- The integer ring of the standard infinite local model is henselian. -/
theorem laurentSeries_henselianRing
    (F : Type u) [Field F] [Finite F] :
    HenselianRing 𝒪[F⸨X⸩] 𝓂[F⸨X⸩] := by
  letI : IsAdicComplete 𝓂[F⸨X⸩] 𝒪[F⸨X⸩] := laurentSeries_isAdicComplete F
  infer_instance

/-- Hensel lifting holds for the Laurent-series valuation ring. -/
theorem laurentSeries_henselianLocalRing
    (F : Type u) [Field F] [Finite F] :
    HenselianLocalRing 𝒪[F⸨X⸩] := by
  letI : HenselianRing 𝒪[F⸨X⸩] 𝓂[F⸨X⸩] := laurentSeries_henselianRing F
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a₀ ha₀ hderivative
  exact HenselianRing.is_henselian f hf a₀ ha₀ (hderivative.map (Ideal.Quotient.mk _))

end

end GaloisForLFunctions.HTGeometry.ABHN

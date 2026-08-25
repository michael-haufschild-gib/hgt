import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionUnramifiedMaximalSubfieldTopology
import GaloisForLFunctions.HTGeometry.ABHN.RationalFiniteLocalField

/-!
# Intrinsic local-field structure on determinant-unramified maximal subfields

The local-field API uses the intrinsic valuation attached to a `ValuativeRel`, whereas the local
division-algebra degree calculation uses the norm valuation.  For the valuative relation induced
by the norm, these two integer rings are canonically identical on underlying field elements.

This file packages that identity as ring and residue equivalences, transports the local scalar
map through it, and proves that the intrinsic residue extension of the residue-exhausting maximal
subfield has degree exactly the degree of the division algebra.  This is the degree statement
needed to compare that subfield with a canonical unramified Hensel lift.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open scoped NormedField ValuativeRel Valued

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- For the valuative relation induced by a nonarchimedean norm, its intrinsic integer ring is
canonically the norm valuation ring.  Both sides contain exactly the field elements of norm at
most one. -/
noncomputable def normValuationIntrinsicIntegerEquiv :
    letI : ValuativeRel K := .ofValuation (NormedField.valuation (K := K))
    (ValuativeRel.valuation K).integer ≃+* NormValuationSubring (F := K) := by
  letI : ValuativeRel K := .ofValuation (NormedField.valuation (K := K))
  letI : (NormedField.valuation (K := K)).Compatible := .ofValuation _
  let h : (ValuativeRel.valuation K).integer =
      (NormedField.valuation (K := K)).valuationSubring.toSubring := by
    ext x
    change ValuativeRel.valuation K x ≤ ValuativeRel.valuation K 1 ↔
      NormedField.valuation x ≤ 1
    simpa only [map_one] using
      (Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation K) x 1).symm.trans
          (Valuation.Compatible.vle_iff_le
            (v := NormedField.valuation (K := K)) x 1)
  exact RingEquiv.subringCongr h

/-- Intrinsic local-field residue and norm-valuation residue are canonically ring-equivalent. -/
noncomputable def normValuationIntrinsicResidueEquiv :
    letI : ValuativeRel K := .ofValuation (NormedField.valuation (K := K))
    IsLocalRing.ResidueField (ValuativeRel.valuation K).integer ≃+*
      NormValuationResidue (F := K) := by
  letI : ValuativeRel K := .ofValuation (NormedField.valuation (K := K))
  exact IsLocalRing.ResidueField.mapEquiv (normValuationIntrinsicIntegerEquiv (K := K))

variable {F A : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [LocallyCompactSpace F] [DivisionRing A] [Algebra F A]
  [Module.Finite F A] [Algebra.IsCentral F A]

/-- Root-determinant topology makes every commutative subfield a nonarchimedean local field for
the valuative relation induced by that norm. -/
theorem divisionAlgebraRestrictedRootDeterminant_isNonarchimedeanLocalField
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    letI : NormedSpace F T :=
      divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
    letI : CompleteSpace T :=
      divisionAlgebraRestrictedRootDeterminantCompleteSpace (F := F) (A := A) T hT
    letI : IsUltrametricDist T :=
      divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
    letI : ProperSpace T :=
      divisionAlgebraRestrictedRootDeterminantProperSpace (F := F) (A := A) T hT
    letI : ValuativeRel T := .ofValuation (NormedField.valuation (K := T))
    IsNonarchimedeanLocalField T := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
  letI : CompleteSpace T :=
    divisionAlgebraRestrictedRootDeterminantCompleteSpace (F := F) (A := A) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
  letI : ProperSpace T :=
    divisionAlgebraRestrictedRootDeterminantProperSpace (F := F) (A := A) T hT
  letI : ValuativeRel T := .ofValuation (NormedField.valuation (K := T))
  letI : (Valued.v : Valuation T NNReal).IsNontrivial := by
    change (NormedField.valuation (K := T)).IsNontrivial
    exact Valuation.RankOne.toIsNontrivial
  exact isNonarchimedeanLocalField_of_valued_of_locallyCompact T NNReal

/-- Intrinsic integral elements of the base map locally into intrinsic integral elements of a
root-determinant subfield.  The definition transports the already-proved norm-valuation local
map through the identity-on-elements integer-ring equivalences. -/
noncomputable def divisionAlgebraRestrictedIntrinsicIntegerMap
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    letI : NormedSpace F T :=
      divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
    letI : IsUltrametricDist T :=
      divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
    letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
    letI : ValuativeRel T := .ofValuation (NormedField.valuation (K := T))
    (ValuativeRel.valuation F).integer →+* (ValuativeRel.valuation T).integer := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
  letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
  letI : (NormedField.valuation (K := F)).Compatible := .ofValuation _
  letI : ValuativeRel T := .ofValuation (NormedField.valuation (K := T))
  letI : (NormedField.valuation (K := T)).Compatible := .ofValuation _
  exact (normValuationIntrinsicIntegerEquiv (K := T)).symm.toRingHom.comp
    ((normValuationSubringToDivisionAlgebraRestrictedNormValuationSubring
      (F := F) (A := A) T hT).comp
        (normValuationIntrinsicIntegerEquiv (K := F)).toRingHom)

/-- Intrinsic integral subfield elements form an algebra over intrinsic integral base elements. -/
noncomputable instance divisionAlgebraRestrictedIntrinsicIntegerAlgebra
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    letI : NormedSpace F T :=
      divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
    letI : IsUltrametricDist T :=
      divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
    letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
    letI : ValuativeRel T := .ofValuation (NormedField.valuation (K := T))
    Algebra (ValuativeRel.valuation F).integer
      (ValuativeRel.valuation T).integer := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
  letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
  letI : ValuativeRel T := .ofValuation (NormedField.valuation (K := T))
  exact (divisionAlgebraRestrictedIntrinsicIntegerMap (F := F) (A := A) T hT).toAlgebra

/-- Intrinsic integral scalar extension is local, so it induces the canonical intrinsic residue
field extension. -/
instance divisionAlgebraRestrictedIntrinsicIntegerAlgebra_isLocalHom
    (T : Subalgebra F A) (hT : IsField T) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    letI : NormedSpace F T :=
      divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
    letI : IsUltrametricDist T :=
      divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
    letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
    letI : ValuativeRel T := .ofValuation (NormedField.valuation (K := T))
    IsLocalHom (algebraMap (ValuativeRel.valuation F).integer
      (ValuativeRel.valuation T).integer) := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
  letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
  letI : (NormedField.valuation (K := F)).Compatible := .ofValuation _
  letI : ValuativeRel T := .ofValuation (NormedField.valuation (K := T))
  letI : (NormedField.valuation (K := T)).Compatible := .ofValuation _
  letI : IsLocalHom (normValuationIntrinsicIntegerEquiv (K := F)).toRingHom :=
    IsLocalHom.of_surjective _ (normValuationIntrinsicIntegerEquiv (K := F)).surjective
  letI : IsLocalHom (normValuationIntrinsicIntegerEquiv (K := T)).symm.toRingHom :=
    IsLocalHom.of_surjective _
      (normValuationIntrinsicIntegerEquiv (K := T)).symm.surjective
  letI : IsLocalHom
      (normValuationSubringToDivisionAlgebraRestrictedNormValuationSubring
        (F := F) (A := A) T hT) := by
    change IsLocalHom (algebraMap (NormValuationSubring (F := F))
      (NormValuationSubring (F := T)))
    infer_instance
  change IsLocalHom (divisionAlgebraRestrictedIntrinsicIntegerMap
    (F := F) (A := A) T hT)
  unfold divisionAlgebraRestrictedIntrinsicIntegerMap
  infer_instance

/-- The intrinsic residue extension of a residue-exhausting root-determinant subfield has degree
equal to the degree of the central division algebra.  Cardinal comparison transports the exact
norm-residue degree through the intrinsic/norm residue equivalences. -/
theorem divisionAlgebraRestrictedIntrinsicResidue_finrank_eq_degree
    (T : Subalgebra F A) (hT : IsField T)
    (hres :
      letI : NormedDivisionRing A :=
        divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
      letI : NontriviallyNormedField T :=
        divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
          (F := F) (A := A) T hT
      letI : NormedSpace F T :=
        divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
      letI : IsUltrametricDist T :=
        divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
      NormValuationResidue (F := T) ≃ₐ[NormValuationResidue (F := F)]
        DivisionAlgebraDeterminantResidue (F := F) (A := A)) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    letI : NormedSpace F T :=
      divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
    letI : IsUltrametricDist T :=
      divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
    letI : ProperSpace T :=
      divisionAlgebraRestrictedRootDeterminantProperSpace (F := F) (A := A) T hT
    letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
    letI : ValuativeRel T := .ofValuation (NormedField.valuation (K := T))
    Module.finrank
        (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer)
        (IsLocalRing.ResidueField (ValuativeRel.valuation T).integer) =
      divisionAlgebraDegree (F := F) (A := A) := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
  letI : ProperSpace T :=
    divisionAlgebraRestrictedRootDeterminantProperSpace (F := F) (A := A) T hT
  letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
  letI : (NormedField.valuation (K := F)).Compatible := .ofValuation _
  letI : ValuativeRel T := .ofValuation (NormedField.valuation (K := T))
  letI : (NormedField.valuation (K := T)).Compatible := .ofValuation _
  let kF := IsLocalRing.ResidueField (ValuativeRel.valuation F).integer
  let kT := IsLocalRing.ResidueField (ValuativeRel.valuation T).integer
  let eF : kF ≃+* NormValuationResidue (F := F) :=
    normValuationIntrinsicResidueEquiv (K := F)
  let eT : kT ≃+* NormValuationResidue (F := T) :=
    normValuationIntrinsicResidueEquiv (K := T)
  letI : Finite (NormValuationResidue (F := F)) := normValuationResidue_finite (F := F)
  letI : Finite (NormValuationResidue (F := T)) := normValuationResidue_finite (F := T)
  letI : Finite kF := Finite.of_surjective eF.symm eF.symm.surjective
  letI : Finite kT := Finite.of_surjective eT.symm eT.symm.surjective
  letI : Module.Finite kF kT := Module.Finite.of_finite
  have hnorm : Module.finrank (NormValuationResidue (F := F))
      (NormValuationResidue (F := T)) = divisionAlgebraDegree (F := F) (A := A) := by
    rw [hres.toLinearEquiv.finrank_eq]
    exact finrank_divisionAlgebraDeterminantResidue_eq_degree (F := F) (A := A)
  apply Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card kF)
  change Nat.card kF ^ Module.finrank kF kT =
    Nat.card kF ^ divisionAlgebraDegree (F := F) (A := A)
  rw [← Module.natCard_eq_pow_finrank (K := kF) (V := kT)]
  calc
    Nat.card kT = Nat.card (NormValuationResidue (F := T)) := Nat.card_congr eT.toEquiv
    _ = Nat.card (NormValuationResidue (F := F)) ^
        Module.finrank (NormValuationResidue (F := F))
          (NormValuationResidue (F := T)) := Module.natCard_eq_pow_finrank
    _ = Nat.card (NormValuationResidue (F := F)) ^
        divisionAlgebraDegree (F := F) (A := A) := by rw [hnorm]
    _ = Nat.card kF ^ divisionAlgebraDegree (F := F) (A := A) := by
      rw [Nat.card_congr eF.toEquiv]

end

end GaloisForLFunctions.HTGeometry.ABHN

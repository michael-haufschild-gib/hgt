import GaloisForLFunctions.HTGeometry.GroupAlgebraConnectedSaturation

/-!
# Saturation from connectedness of a mixed affine-exponential subgroup

The group algebra classified by the torus projection embeds into the coordinate quotient of the
original mixed subgroup.  Therefore connectedness of the mixed subgroup's prime spectrum already
excludes finite character torsion and forces saturation of the exact torus-relation lattice; no
separate connectedness theorem for the scheme-theoretic projection is needed.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace MixedTorusProjectionSaturation

noncomputable section

open AffineExponentialGroup AffineExponentialProjectionImages
open AffineExponentialProjectionClassification
open GroupAlgebraHopfIdealClassification
open ConnectedPrimeSpectrumIdempotent GroupAlgebraConnectedSaturation
open CharacterLatticeSaturation

variable (k : Type*) [Field k]

/-- A Hopf ideal over a field is proper: its counit condition excludes the unit. -/
theorem hopfIdeal_ne_top
    {A : Type*} [CommRing A] [HopfAlgebra k A]
    (J : Ideal A) [J.IsHopfIdeal k] : J ≠ ⊤ := by
  intro htop
  have hone : (1 : A) ∈ Submodule.restrictScalars k J := by
    change (1 : A) ∈ J
    rw [htop]
    trivial
  have hzero := Submodule.IsCoideal.counit_eq_zero hone
  exact one_ne_zero (Bialgebra.counit_one.symm.trans hzero)

variable {n : ℕ} (I : Ideal (CoordinateAlgebra k n)) [I.IsHopfIdeal k]

local instance subgroupQuotientNontrivial :
    Nontrivial (CoordinateAlgebra k n ⧸ I) :=
  Ideal.Quotient.nontrivial_iff.mpr (hopfIdeal_ne_top k I)

local instance torusProjectionHopfIdeal :
    (torusProjectionIdeal k I).IsHopfIdeal k :=
  torusProjectionIdeal_isHopfIdeal k I

/-- The quotient by the contracted torus ideal maps canonically into the mixed subgroup quotient. -/
noncomputable def torusProjectionQuotientAlgHom :
    TorusCoordinateAlgebra k n ⧸ torusProjectionIdeal k I →ₐ[k]
      CoordinateAlgebra k n ⧸ I :=
  Ideal.Quotient.liftₐ (torusProjectionIdeal k I)
    (torusProjectionMap k I).toAlgHom (by
      intro x hx
      exact hx)

@[simp] theorem torusProjectionQuotientAlgHom_mk
    (x : TorusCoordinateAlgebra k n) :
    torusProjectionQuotientAlgHom k I (Ideal.Quotient.mk _ x) =
      torusProjectionMap k I x := rfl

/-- The quotient map is injective because its defining ideal is exactly the contraction kernel. -/
theorem torusProjectionQuotientAlgHom_injective :
    Function.Injective (torusProjectionQuotientAlgHom k I) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.eq]
  change torusProjectionMap k I (a - b) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr hxy

/-- The classified quotient character group algebra embedded in the actual mixed subgroup
coordinate quotient. -/
noncomputable def torusRelationGroupAlgHomIntoSubgroupQuotient :
    AddMonoidAlgebra k
        ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I) →ₐ[k]
      CoordinateAlgebra k n ⧸ I :=
  (torusProjectionQuotientAlgHom k I).comp
    (quotientGroupAlgHom (torusProjectionIdeal k I))

theorem torusRelationGroupAlgHomIntoSubgroupQuotient_injective :
    Function.Injective (torusRelationGroupAlgHomIntoSubgroupQuotient k I) :=
  (torusProjectionQuotientAlgHom_injective k I).comp
    (quotientGroupAlgHom_injective (torusProjectionIdeal k I))

/-- An injective map into a ring with preconnected prime spectrum forces all source idempotents to
be trivial. -/
theorem isIdempotentElem_eq_zero_or_one_of_injective_to_preconnected_primeSpectrum
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial R] [Nontrivial S]
    [PreconnectedSpace (PrimeSpectrum S)]
    (f : R →+* S) (hf : Function.Injective f) {e : R}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases isIdempotentElem_eq_zero_or_one_of_preconnected_primeSpectrum
      (he.map f) with hzero | hone
  · left
    apply hf
    simpa using hzero
  · right
    apply hf
    simpa using hone

/-- Preconnectedness of the actual mixed affine-exponential subgroup quotient forces integral
saturation of its scheme-theoretic torus projection's character-relation lattice. -/
theorem torusRelationLattice_integerSaturated_of_preconnected_mixed_primeSpectrum
    [CharZero k]
    [PreconnectedSpace (PrimeSpectrum (CoordinateAlgebra k n ⧸ I))] :
    IntegerSaturated (torusRelationLattice k I).toIntSubmodule := by
  rw [torusRelationLattice_integerSaturated_iff_quotient_nsmul_eq_zero]
  intro d q hd hdq
  apply eq_zero_of_nsmul_eq_zero_of_groupAlgebra_idempotents_trivial
    (k := k) (M := (Fin n →₀ ℤ) ⧸ torusRelationLattice k I) _ hd hdq
  intro e he
  exact isIdempotentElem_eq_zero_or_one_of_injective_to_preconnected_primeSpectrum
    (R := AddMonoidAlgebra k
      ((Fin n →₀ ℤ) ⧸ torusRelationLattice k I))
    (S := CoordinateAlgebra k n ⧸ I)
    (torusRelationGroupAlgHomIntoSubgroupQuotient k I).toRingHom
    (torusRelationGroupAlgHomIntoSubgroupQuotient_injective k I) he

end
end MixedTorusProjectionSaturation
end GaloisForLFunctions.HTGeometry

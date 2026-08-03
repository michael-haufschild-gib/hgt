import GaloisForLFunctions.RHTower.DeningerRatVectorSpace
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.RepresentationTheory.Equiv

/-!
# Shapiro's lemma for permutation representations
-/

namespace RHTower

open Representation Rep CategoryTheory MonoidAlgebra

universe u

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)

/-- The `k`-linear map `k[G] → k[G ⧸ S]` sending the basis element at `h` to the one at the coset
of `h⁻¹`. -/
noncomputable def deningerCosetMap : k[G] →ₗ[k] k[G ⧸ S] :=
  MonoidAlgebra.mapDomainLinearMap k k (fun h => (QuotientGroup.mk h⁻¹ : G ⧸ S))

theorem deningerCosetMap_single (h : G) (c : k) :
    deningerCosetMap S (MonoidAlgebra.single h c) =
      MonoidAlgebra.single (QuotientGroup.mk h⁻¹ : G ⧸ S) c := by
  simp [deningerCosetMap, MonoidAlgebra.mapDomainLinearMap]

/-- The underlying linear map of `Ind_S^G(k) → k[G ⧸ S]`. -/
noncomputable def deningerIndToCoset :
    IndV S.subtype (Rep.trivial k S k).ρ →ₗ[k] k[G ⧸ S] :=
  Coinvariants.lift _
    (deningerCosetMap S ∘ₗ (TensorProduct.rid k k[G]).toLinearMap)
    (fun s => by
      refine TensorProduct.ext (MonoidAlgebra.lhom_ext' fun h => LinearMap.ext_ring ?_)
      refine LinearMap.ext_ring ?_
      simp [deningerCosetMap, Representation.tprod_apply, MonoidAlgebra.mapDomainLinearMap])

/-- The underlying linear map of `k[G ⧸ S] → Ind_S^G(k)`. -/
noncomputable def deningerCosetToInd :
    k[G ⧸ S] →ₗ[k] IndV S.subtype (Rep.trivial k S k).ρ :=
  Finsupp.lift _ k _
    (fun x => Quotient.liftOn' x (fun g => IndV.mk S.subtype (Rep.trivial k S k).ρ g⁻¹ (1 : k))
      (fun a b hab => by
        have hs : a⁻¹ * b ∈ S := QuotientGroup.leftRel_apply.1 hab
        show Coinvariants.mk _ (MonoidAlgebra.single a⁻¹ (1:k) ⊗ₜ[k] (1:k)) =
             Coinvariants.mk _ (MonoidAlgebra.single b⁻¹ (1:k) ⊗ₜ[k] (1:k))
        rw [← Coinvariants.mk_self_apply _ (⟨a⁻¹ * b, hs⟩ : S)
          (MonoidAlgebra.single b⁻¹ (1:k) ⊗ₜ[k] (1:k))]
        congr 1
        simp [Representation.tprod_apply])) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem deningerIndToCoset_mk (h : G) (c : k) :
    deningerIndToCoset S (IndV.mk S.subtype (Rep.trivial k S k).ρ h c) =
      MonoidAlgebra.single (QuotientGroup.mk h⁻¹ : G ⧸ S) c := by
  simp [deningerIndToCoset, IndV.mk, deningerCosetMap, MonoidAlgebra.mapDomainLinearMap]

theorem deningerCosetToInd_single (g : G) (c : k) :
    deningerCosetToInd S (MonoidAlgebra.single (QuotientGroup.mk g : G ⧸ S) c) =
      IndV.mk S.subtype (Rep.trivial k S k).ρ g⁻¹ c := by
  show Finsupp.lift _ k _ _ (Finsupp.single (QuotientGroup.mk g : G ⧸ S) c) = _
  rw [Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]
  show c • IndV.mk S.subtype (Rep.trivial k S k).ρ g⁻¹ (1:k) = _
  rw [← map_smul]
  simp

theorem deningerCosetToInd_comp :
    deningerCosetToInd S ∘ₗ deningerIndToCoset S =
      (LinearMap.id : IndV S.subtype (Rep.trivial k S k).ρ →ₗ[k]
        IndV S.subtype (Rep.trivial k S k).ρ) := by
  refine IndV.hom_ext _ _ fun h => LinearMap.ext_ring ?_
  show deningerCosetToInd S (deningerIndToCoset S (IndV.mk _ _ h (1:k))) = _
  rw [deningerIndToCoset_mk, deningerCosetToInd_single, inv_inv]
  rfl

theorem deningerIndToCoset_comp :
    deningerIndToCoset S ∘ₗ deningerCosetToInd S =
      (LinearMap.id : k[G ⧸ S] →ₗ[k] k[G ⧸ S]) := by
  refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
  induction x using QuotientGroup.induction_on with
  | _ g =>
    show deningerIndToCoset S (deningerCosetToInd S (MonoidAlgebra.single _ (1:k))) = _
    rw [deningerCosetToInd_single, deningerIndToCoset_mk, inv_inv]
    rfl

/-- The linear equivalence `Ind_S^G(k) ≃ k[G ⧸ S]`. -/
noncomputable def deningerIndCosetLinearEquiv :
    IndV S.subtype (Rep.trivial k S k).ρ ≃ₗ[k] k[G ⧸ S] :=
  LinearEquiv.ofLinear (deningerIndToCoset S) (deningerCosetToInd S)
    (deningerIndToCoset_comp S) (deningerCosetToInd_comp S)

theorem deningerIndCosetLinearEquiv_comm (g : G) :
    (deningerIndCosetLinearEquiv S).toLinearMap ∘ₗ
        (Representation.ind S.subtype (Rep.trivial k S k).ρ) g =
      Representation.ofMulAction k G (G ⧸ S) g ∘ₗ (deningerIndCosetLinearEquiv S).toLinearMap := by
  refine IndV.hom_ext _ _ fun h => LinearMap.ext_ring ?_
  show deningerIndToCoset S ((Representation.ind S.subtype _) g (IndV.mk _ _ h (1:k))) =
    Representation.ofMulAction k G (G ⧸ S) g (deningerIndToCoset S (IndV.mk _ _ h (1:k)))
  rw [Representation.ind_mk, deningerIndToCoset_mk, deningerIndToCoset_mk,
    Representation.ofMulAction_single]
  congr 1
  simp [mul_inv_rev]

/-- **The induced representation of the trivial representation is the permutation representation
on cosets**: `Ind_S^G(k) ≅ k[G ⧸ S]`. -/
noncomputable def deningerIndTrivialIso :
    Rep.ind S.subtype (Rep.trivial k S k) ≅ Rep.ofMulAction k G (G ⧸ S) :=
  Rep.mkIso (Representation.Equiv.mk (deningerIndCosetLinearEquiv S)
    (deningerIndCosetLinearEquiv_comm S))

/-- **Shapiro's lemma for permutation representations**: the homology of `G` with coefficients in
the permutation representation on the cosets of `S` is the homology of `S` with trivial
coefficients. -/
noncomputable def deningerPermutationShapiro [DecidableEq G] (n : ℕ) :
    groupHomology (Rep.ofMulAction k G (G ⧸ S)) n ≅ groupHomology (Rep.trivial k S k) n :=
  (groupHomology.mapIso (MulEquiv.refl G) (deningerIndCosetLinearEquiv S)
      (fun g => deningerIndCosetLinearEquiv_comm S g) n).symm ≪≫
    groupHomology.indIso S (Rep.trivial k S k) n

end RHTower

import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ListParabolicLevi
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.InducedCharacterDoubleCosets
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularParabolicCosets
import GaloisForLFunctions.RHTower.Artin.ArtinVirtualFrobeniusReciprocity

/-! Permutations represent flag-parabolic double cosets. Conjugating the
overlap by the inverse representative exchanges the two parabolics. -/

noncomputable section
open scoped Classical

namespace GaloisForLFunctions

section Swap

variable {G : Type*} [Group G] (H K : Subgroup G) (x : G)

private def swapOverlapEquiv : doubleCosetOverlap H K x ≃* doubleCosetOverlap K H x⁻¹ where
  toFun u := ⟨doubleCosetOverlapConj H K x u, (mem_doubleCosetOverlap K H x⁻¹ _).mpr (by
    change (x⁻¹)⁻¹ * (x⁻¹ * u.val.val * x) * x⁻¹ ∈ H
    have he : (x⁻¹)⁻¹ * (x⁻¹ * u.val.val * x) * x⁻¹ = u.val.val := by group
    rw [he]
    exact u.val.property)⟩
  invFun v := by
    have hv : x * v.val.val * x⁻¹ ∈ H := by
      simpa only [inv_inv] using (mem_doubleCosetOverlap K H x⁻¹ v.val).mp v.property
    refine ⟨⟨x * v.val.val * x⁻¹, hv⟩, (mem_doubleCosetOverlap H K x _).mpr ?_⟩
    change x⁻¹ * (x * v.val.val * x⁻¹) * x ∈ K
    have he : x⁻¹ * (x * v.val.val * x⁻¹) * x = v.val.val := by group
    rw [he]
    exact v.val.property
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    change x * (x⁻¹ * u.val.val * x) * x⁻¹ = u.val.val
    group
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    change x⁻¹ * (x * v.val.val * x⁻¹) * x = v.val.val
    group
  map_mul' u v := Subtype.ext (map_mul (doubleCosetOverlapConj H K x) u v)

/-- Exchanging the inducing groups replaces the representative by its inverse. -/
theorem doubleCosetPairing_swap_inv [Fintype G] (α : H → ℂ) (β : K → ℂ)
    [Fintype (doubleCosetOverlap H K x)] [Fintype (doubleCosetOverlap K H x⁻¹)] :
    doubleCosetPairing H K α β x = doubleCosetPairing K H β α x⁻¹ := by
  let O := doubleCosetOverlap H K x
  let Q := doubleCosetOverlap K H x⁻¹
  let e := swapOverlapEquiv H K x
  rw [doubleCosetPairing_eq_pairing H K α β x, doubleCosetPairing_eq_pairing K H β α x⁻¹,
    characterPairing_comm Q _ _]
  unfold characterPairing
  rw [← Nat.card_congr e.toEquiv]
  apply congrArg (((Nat.card O : ℂ)⁻¹) * ·)
  simp only [map_inv]
  let F (v : Q) := β v.val * α (doubleCosetOverlapConj K H x⁻¹ v)⁻¹
  refine (Finset.sum_congr rfl fun u _ => ?_).trans (Equiv.sum_comp e.toEquiv F)
  have h (u : O) : doubleCosetOverlapConj K H x⁻¹ (e u) = u.val := by
    apply Subtype.ext
    change (x⁻¹)⁻¹ * (x⁻¹ * u.val.val * x) * x⁻¹ = u.val.val
    group
  change β (doubleCosetOverlapConj H K x u) * α u.val⁻¹ = F (e u)
  exact congrArg (fun t : H => β (doubleCosetOverlapConj H K x u) * α t⁻¹) (h u).symm

end Swap

end GaloisForLFunctions

namespace GlobalTheory.GLq

open GaloisForLFunctions.HTGeometry

variable {g n : ℕ} [Fact g.Prime]

/-- Every double coset of two standard flag parabolics contains a permutation matrix. -/
theorem exists_listParabolic_permutation_rep (L M : List (Pc g)) (hL : degL L = n)
    (hM : degL M = n) (x : Gn g n) :
    ∃ σ : Equiv.Perm (Fin n),
      DoubleCoset.mk (listParabolicAt L hL) (listParabolicAt M hM) (permutationUnit σ) =
        DoubleCoset.mk (listParabolicAt L hL) (listParabolicAt M hM) x := by
  let P := listParabolicAt L hL
  let Q := listParabolicAt M hM
  obtain ⟨l, r, σ, c, hx⟩ := exists_unitriangular_monomial g n x
  let d : Gn g n := monomialUnit (Equiv.refl (Fin n)) c
  have hd : d ∈ Q := (mem_listParabolicAt_iff M hM d).mpr fun i j h => by
    have hij : i ≠ j := fun he => (ne_of_lt h) (congrArg (listBlockOfAt M hM) he.symm)
    simp [d, monomialUnit, signedMonomialMatrix, hij]
  have hσ : monomialUnit σ c = permutationUnit σ * d := by
    apply Units.ext
    change signedMonomialMatrix σ c =
      signedMonomialMatrix σ (fun _ => 1) * signedMonomialMatrix (Equiv.refl _) c
    simp only [signedMonomialMatrix_mul, Equiv.refl_trans, one_mul]
  refine ⟨σ, (DoubleCoset.eq P Q _ _).mpr ⟨l.val,
    upperUnitriangular_le_listParabolicAt L hL l.property, d * r.val,
    Q.mul_mem hd (upperUnitriangular_le_listParabolicAt M hM r.property), ?_⟩⟩
  simp only [hx, hσ, mul_assoc]

end GlobalTheory.GLq

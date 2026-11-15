import GaloisForLFunctions.RepresentationLifting.KTheory.VirtualFreenessDetection
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Fixed points and virtual freeness of permutation modules

For a finite action, the ordinary character counts fixed points. Consequently
its virtual class is regular exactly when every stabilizer is trivial. For a
coset action this is equivalent to the defining subgroup being trivial. These
are applications of nonidentity-trace detection to permutation and coset modules.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

variable (G X : Type*) [Group G] [Fintype G] [MulAction G X] [Fintype X]

/-- The virtual class of the actual permutation representation on `X`. -/
def permutationVirtualRepresentation : VirtualRepresentationRing G :=
  ⟨(Representation.ofMulAction ℂ G X).character,
    AddSubgroup.subset_closure
      (representation_character_mem_fdCharacterSet G (Representation.ofMulAction ℂ G X))⟩

/-- Number of basis vectors fixed by an element. -/
def permutationFixedCount (g : G) : ℕ := by
  classical
  exact (Finset.univ.filter fun x : X => g • x = x).card

/-- The permutation character counts fixed basis vectors. -/
theorem permutationVirtualRepresentation_apply (g : G) :
    (permutationVirtualRepresentation G X).val g = (permutationFixedCount G X g : ℂ) := by
  classical
  change LinearMap.trace ℂ (MonoidAlgebra ℂ X) (Representation.ofMulAction ℂ G X g) = _
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis X ℂ)]
  change (∑ x : X, (LinearMap.toMatrix (MonoidAlgebra.basis X ℂ)
    (MonoidAlgebra.basis X ℂ) (Representation.ofMulAction ℂ G X g)) x x) = _
  have hdiag (x : X) : (LinearMap.toMatrix (MonoidAlgebra.basis X ℂ)
      (MonoidAlgebra.basis X ℂ) (Representation.ofMulAction ℂ G X g)) x x =
      if g • x = x then 1 else 0 := by
    rw [LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply]
    change (Representation.ofMulAction ℂ G X g (MonoidAlgebra.single x 1)).coeff x = _
    rw [Representation.ofMulAction_single, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp only [hdiag, permutationFixedCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- A vanishing permutation trace is precisely absence of fixed points. -/
theorem permutationVirtualRepresentation_eq_zero_iff (g : G) :
    (permutationVirtualRepresentation G X).val g = 0 ↔ ∀ x : X, g • x ≠ x := by
  classical
  rw [permutationVirtualRepresentation_apply, Nat.cast_eq_zero]
  simp [permutationFixedCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

/-- Regularity of a permutation character is equivalent to freeness of the action. -/
theorem permutation_isVirtuallyFree_iff :
    IsVirtuallyFree G (permutationVirtualRepresentation G X) ↔
      ∀ (g : G) (x : X), g • x = x → g = 1 := by
  rw [isVirtuallyFree_iff]
  constructor
  · intro h g x hx
    by_contra hg
    exact ((permutationVirtualRepresentation_eq_zero_iff G X g).mp (h g hg) x) hx
  · intro h g hg
    apply (permutationVirtualRepresentation_eq_zero_iff G X g).mpr
    exact fun x hx => hg (h g x hx)

/-- A coset permutation class is virtually free exactly for the trivial subgroup. -/
theorem coset_isVirtuallyFree_iff (H : Subgroup G) :
    IsVirtuallyFree G (permutationVirtualRepresentation G (G ⧸ H)) ↔ H = ⊥ := by
  classical
  rw [permutation_isVirtuallyFree_iff]
  constructor
  · intro h
    apply le_antisymm _ bot_le
    intro g hg
    apply Subgroup.mem_bot.mpr
    apply h g (QuotientGroup.mk (1 : G))
    change QuotientGroup.mk (g * 1) = (QuotientGroup.mk (1 : G) : G ⧸ H)
    apply QuotientGroup.eq.mpr
    simpa using H.inv_mem hg
  · rintro rfl g x hx
    induction x using Quotient.inductionOn with
    | h a =>
      change (QuotientGroup.mk (g * a) : G ⧸ (⊥ : Subgroup G)) = QuotientGroup.mk a at hx
      have hm := Subgroup.mem_bot.mp (QuotientGroup.eq.mp hx)
      have he : g * a = a := (inv_mul_eq_one.mp hm)
      exact mul_right_cancel (he.trans (one_mul a).symm)

#print axioms permutationVirtualRepresentation_apply
#print axioms permutation_isVirtuallyFree_iff
#print axioms coset_isVirtuallyFree_iff

end GaloisForLFunctions.RepresentationLifting

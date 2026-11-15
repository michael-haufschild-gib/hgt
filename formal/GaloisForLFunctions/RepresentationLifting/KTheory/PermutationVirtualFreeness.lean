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

variable (G X : Type*) [Group G] [MulAction G X] [Fintype X]

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

/-- A permutation has maximal trace exactly when it fixes every basis vector. -/
theorem permutationFixedCount_eq_card_iff (g : G) :
    permutationFixedCount G X g = Fintype.card X ↔ ∀ x : X, g • x = x := by
  classical
  constructor
  · intro h
    have he : Finset.univ.filter (fun x : X => g • x = x) = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by
        simpa only [permutationFixedCount, Finset.card_univ] using h.ge)
    intro x
    have hx : x ∈ Finset.univ.filter (fun y : X => g • y = y) := he.symm ▸ Finset.mem_univ x
    have hx' := Finset.mem_filter.mp hx
    exact hx'.2
  · intro h
    simp [permutationFixedCount, h]

variable [Fintype G]

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

/-- The permutation class after subtracting its ordinary dimension. -/
def reducedPermutationVirtualRepresentation : VirtualRepresentationRing G :=
  permutationVirtualRepresentation G X - (Fintype.card X : VirtualRepresentationRing G)

omit [Fintype G] in
theorem reducedPermutationVirtualRepresentation_apply (g : G) :
    (reducedPermutationVirtualRepresentation G X).val g =
      (permutationFixedCount G X g : ℂ) - (Fintype.card X : ℂ) := by
  change (permutationVirtualRepresentation G X).val g - (Fintype.card X : ℂ) = _
  rw [permutationVirtualRepresentation_apply]

omit [Fintype G] in
/-- Dimension subtraction kills exactly the permutation classes of trivial actions. -/
theorem reducedPermutation_eq_zero_iff :
    reducedPermutationVirtualRepresentation G X = 0 ↔ ∀ (g : G) (x : X), g • x = x := by
  constructor
  · intro h g
    have he := congrArg (fun χ : VirtualRepresentationRing G => χ.val g) h
    change (reducedPermutationVirtualRepresentation G X).val g = 0 at he
    rw [reducedPermutationVirtualRepresentation_apply] at he
    exact (permutationFixedCount_eq_card_iff G X g).mp
      (Nat.cast_injective (R := ℂ) (sub_eq_zero.mp he))
  · intro h
    apply Subtype.ext
    funext g
    change (reducedPermutationVirtualRepresentation G X).val g = 0
    rw [reducedPermutationVirtualRepresentation_apply,
      (permutationFixedCount_eq_card_iff G X g).mpr (h g), sub_self]

omit [Fintype G] in
/-- Every reduced permutation class lies in the dimension augmentation ideal. -/
theorem reducedPermutation_augmentation :
    virtualRepresentationAugmentation G (reducedPermutationVirtualRepresentation G X) = 0 := by
  apply Int.cast_injective (α := ℂ)
  change (virtualRepresentationDegree G (reducedPermutationVirtualRepresentation G X) : ℂ) =
    ((0 : ℤ) : ℂ)
  rw [Int.cast_zero, virtualRepresentationDegree_cast, reducedPermutationVirtualRepresentation_apply]
  simp [permutationFixedCount]

/-- A reduced permutation class is virtually free exactly when the action is trivial. -/
theorem reducedPermutation_isVirtuallyFree_iff :
    IsVirtuallyFree G (reducedPermutationVirtualRepresentation G X) ↔
      ∀ (g : G) (x : X), g • x = x := by
  rw [← reducedPermutation_eq_zero_iff]
  constructor
  · intro h
    exact (isVirtuallyFree_and_degree_zero_iff G _).mp
      ⟨h, reducedPermutation_augmentation G X⟩
  · intro h
    exact ((isVirtuallyFree_and_degree_zero_iff G _).mpr h).1

omit [Fintype G] in
/-- Field K-zero sees none of the reduced permutation character. -/
theorem reducedPermutation_K0Action_zero :
    ∀ x : FieldK0 ℂ, virtualRepresentationK0Action G
      (reducedPermutationVirtualRepresentation G X) x = 0 := by
  apply (virtualRepresentationK0Action_zero_iff G _).mpr
  exact reducedPermutation_augmentation G X

/-- Every nontrivial finite group has a nonfree virtual class invisible to field K-zero. -/
theorem exists_K0_invisible_nonfree_iff :
    (∃ χ : VirtualRepresentationRing G,
      (∀ x : FieldK0 ℂ, virtualRepresentationK0Action G χ x = 0) ∧
      ¬ IsVirtuallyFree G χ) ↔ Nontrivial G := by
  constructor
  · rintro ⟨χ, _, hχ⟩
    obtain ⟨g, hg, _⟩ := (not_isVirtuallyFree_iff G χ).mp hχ
    exact ⟨⟨g, 1, hg⟩⟩
  · intro hG
    refine ⟨reducedPermutationVirtualRepresentation G G, reducedPermutation_K0Action_zero G G, ?_⟩
    intro hfree
    have ht := (reducedPermutation_isVirtuallyFree_iff G G).mp hfree
    obtain ⟨a, b, hab⟩ := hG.exists_pair_ne
    have ha : a = 1 := by simpa only [smul_eq_mul, mul_one] using ht a 1
    have hb : b = 1 := by simpa only [smul_eq_mul, mul_one] using ht b 1
    exact hab (ha.trans hb.symm)

local instance (H : Subgroup G) : Fintype (G ⧸ H) := Fintype.ofFinite _

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
#print axioms reducedPermutation_isVirtuallyFree_iff
#print axioms reducedPermutation_K0Action_zero
#print axioms exists_K0_invisible_nonfree_iff
#print axioms coset_isVirtuallyFree_iff

end GaloisForLFunctions.RepresentationLifting

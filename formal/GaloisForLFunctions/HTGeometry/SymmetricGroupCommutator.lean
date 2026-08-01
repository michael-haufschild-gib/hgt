import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Index

/-!
# The commutator subgroup of a symmetric group is its alternating group

A commutator has trivial sign, because the sign takes values in a commutative group.  Conversely a
three-cycle is conjugate to its own inverse, and conjugating by a witness of that turns the
three-cycle into a commutator of the witness with itself.

Since the three-cycles generate the alternating group, the two subgroups coincide.  So every
abelian quotient of a symmetric group factors through the sign.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv Equiv.Perm
open scoped commutatorElement

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem sign_commutatorElement (g h : Equiv.Perm α) : Equiv.Perm.sign ⁅g, h⁆ = 1 := by
  have h1 : Equiv.Perm.sign ⁅g, h⁆ = ⁅Equiv.Perm.sign g, Equiv.Perm.sign h⁆ := by
    rw [commutatorElement_def, commutatorElement_def, map_mul, map_mul, map_inv, map_inv,
      map_mul]
  rw [h1, commutatorElement_eq_one_iff_commute]
  exact Commute.all _ _

/-- A three-cycle is a commutator: it is conjugate to its inverse, and the square of the inverse is
the three-cycle again. -/
theorem isThreeCycle_mem_commutator {σ : Equiv.Perm α} (hσ : σ.IsThreeCycle) :
    σ ∈ commutator (Equiv.Perm α) := by
  have hconj : IsConj σ σ⁻¹ := by
    rw [Equiv.Perm.isConj_iff_cycleType_eq, Equiv.Perm.cycleType_inv]
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  have hcube : σ * σ * σ = 1 := by
    have h3 : σ ^ 3 = 1 := by
      rw [← hσ.orderOf]
      exact pow_orderOf_eq_one σ
    calc σ * σ * σ = σ ^ 3 := by rw [pow_succ, pow_succ, pow_one]
      _ = 1 := h3
  have hkey : ⁅g, σ⁆ = σ := by
    rw [commutatorElement_def, show g * σ * g⁻¹ = σ⁻¹ from hg]
    have hsq : σ * σ = σ⁻¹ := eq_inv_of_mul_eq_one_left hcube
    calc σ⁻¹ * σ⁻¹ = (σ * σ)⁻¹ := (mul_inv_rev σ σ).symm
      _ = (σ⁻¹)⁻¹ := by rw [hsq]
      _ = σ := inv_inv σ
  rw [← hkey]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top σ)

/-- **The commutator subgroup of a symmetric group is its alternating group.** -/
theorem commutator_perm_eq_alternatingGroup :
    commutator (Equiv.Perm α) = alternatingGroup α := by
  refine le_antisymm ?_ ?_
  · rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    exact Equiv.Perm.mem_alternatingGroup.2 (sign_commutatorElement g h)
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro σ hσ
    exact isThreeCycle_mem_commutator hσ

/-! ## Abelian quotients factor through the sign -/

/-- **A normal subgroup with abelian quotient contains the alternating group.** -/
theorem alternatingGroup_le_of_abelian_quotient {N : Subgroup (Equiv.Perm α)} [N.Normal]
    (h : ∀ x y : Equiv.Perm α ⧸ N, x * y = y * x) : alternatingGroup α ≤ N := by
  rw [← commutator_perm_eq_alternatingGroup, commutator_def, Subgroup.commutator_le]
  intro g _ k _
  have hmk : (QuotientGroup.mk ⁅g, k⁆ : Equiv.Perm α ⧸ N) =
      ⁅(QuotientGroup.mk g : Equiv.Perm α ⧸ N), (QuotientGroup.mk k : Equiv.Perm α ⧸ N)⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    rfl
  have hone : (QuotientGroup.mk ⁅g, k⁆ : Equiv.Perm α ⧸ N) = 1 := by
    rw [hmk, commutatorElement_eq_one_iff_commute]
    exact h _ _
  exact (QuotientGroup.eq_one_iff _).1 hone

/-- **The only normal subgroups with abelian quotient are the alternating group and the whole
group.**  So the only nontrivial abelian, in particular cyclic, quotient of a symmetric group is
the sign quotient. -/
theorem eq_alternatingGroup_or_top_of_abelian_quotient [Nontrivial α]
    {N : Subgroup (Equiv.Perm α)} [N.Normal]
    (h : ∀ x y : Equiv.Perm α ⧸ N, x * y = y * x) :
    N = alternatingGroup α ∨ N = ⊤ := by
  have hle : alternatingGroup α ≤ N := alternatingGroup_le_of_abelian_quotient h
  have hindex : (alternatingGroup α).index = 2 := alternatingGroup.index_eq_two
  have hdvd : N.index ∣ 2 := by
    rw [← hindex]
    exact Subgroup.index_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · right
    exact Subgroup.index_eq_one.1 h1
  · left
    have hcardA := Subgroup.card_mul_index (alternatingGroup α)
    have hcardN := Subgroup.card_mul_index N
    rw [hindex] at hcardA
    rw [h2] at hcardN
    have hcards : Nat.card N ≤ Nat.card (alternatingGroup α) := by omega
    exact (Subgroup.eq_of_le_of_card_ge hle hcards).symm

end GaloisForLFunctions.HTGeometry

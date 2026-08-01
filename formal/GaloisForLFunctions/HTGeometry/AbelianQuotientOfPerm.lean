import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Every abelian quotient of a symmetric group factors through the sign

A homomorphism from a symmetric group to an abelian group kills every three-cycle, hence the whole
alternating group.  So the only quotients of a symmetric group that are abelian are quotients of the
sign character, and in particular the only nontrivial cyclic one has order two.

This is the group-theoretic content of a Kummer base-change argument: a cyclic extension inside a
symmetric Galois extension can only be the quadratic one cut out by the discriminant.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv Equiv.Perm

universe u v

variable {α : Type u} [DecidableEq α] [Fintype α] {H : Type v} [CommGroup H]

/-- **A three-cycle dies in any abelian quotient.**  It is conjugate to its own inverse, so its image
has order dividing two, while its order divides three. -/
theorem eq_one_of_isThreeCycle (φ : Equiv.Perm α →* H) {σ : Equiv.Perm α}
    (hσ : σ.IsThreeCycle) : φ σ = 1 := by
  have hconj : IsConj σ σ⁻¹ := by
    rw [Equiv.Perm.isConj_iff_cycleType_eq, Equiv.Perm.cycleType_inv]
  have himg : φ σ⁻¹ = φ σ := by
    obtain ⟨c, hc⟩ := hconj
    have hce : (c : Equiv.Perm α) * σ * (c : Equiv.Perm α)⁻¹ = σ⁻¹ := by
      rw [SemiconjBy] at hc
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [← hce, map_mul, map_mul, map_inv, mul_comm (φ (c : Equiv.Perm α)) (φ σ), mul_assoc,
      mul_inv_cancel, mul_one]
  have hinv : (φ σ)⁻¹ = φ σ := by rw [← map_inv, himg]
  have hsq : φ σ ^ 2 = 1 := by
    rw [pow_two]
    calc φ σ * φ σ = φ σ * (φ σ)⁻¹ := by rw [hinv]
      _ = 1 := mul_inv_cancel _
  have h3 : σ ^ 3 = 1 := by
    have hpow := pow_orderOf_eq_one σ
    rwa [hσ.orderOf] at hpow
  have hcube : φ σ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  calc φ σ = φ σ ^ 3 * (φ σ ^ 2)⁻¹ := by group
    _ = 1 := by rw [hcube, hsq, inv_one, mul_one]

/-- **The alternating group lies in the kernel of any map to an abelian group.** -/
theorem alternatingGroup_le_ker (φ : Equiv.Perm α →* H) :
    alternatingGroup α ≤ φ.ker := by
  rw [← closure_three_cycles_eq_alternating]
  exact (Subgroup.closure_le _).2 (fun σ hσ => eq_one_of_isThreeCycle φ hσ)

/-- **A normal subgroup with cyclic quotient contains the alternating group.**  So the only
nontrivial cyclic quotient of a symmetric group is the sign quotient. -/
theorem alternatingGroup_le_of_isCyclic_quotient (N : Subgroup (Equiv.Perm α)) [N.Normal]
    (h : IsCyclic (Equiv.Perm α ⧸ N)) : alternatingGroup α ≤ N := by
  letI : CommGroup (Equiv.Perm α ⧸ N) := IsCyclic.commGroup
  have hle := alternatingGroup_le_ker (QuotientGroup.mk' N)
  rwa [QuotientGroup.ker_mk'] at hle

/-- **And therefore has index at most two.** -/
theorem index_dvd_two_of_isCyclic_quotient [Nontrivial α] (N : Subgroup (Equiv.Perm α))
    [N.Normal] (h : IsCyclic (Equiv.Perm α ⧸ N)) : N.index ∣ 2 := by
  have hle := alternatingGroup_le_of_isCyclic_quotient N h
  have hdvd := Subgroup.index_dvd_of_le hle
  rwa [alternatingGroup.index_eq_two] at hdvd

/-- **A cyclic quotient of odd order is trivial.**  So a cyclic base change of odd degree cannot cut
down a symmetric Galois group at all — the discriminant subfield is the only obstruction, and it is
quadratic. -/
theorem eq_top_of_isCyclic_quotient_of_odd_index [Nontrivial α] (N : Subgroup (Equiv.Perm α))
    [N.Normal] (h : IsCyclic (Equiv.Perm α ⧸ N)) (hodd : Odd N.index) : N = ⊤ := by
  have hdvd := index_dvd_two_of_isCyclic_quotient N h
  have h1 : N.index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h2 | h2
    · exact h2
    · rw [h2] at hodd
      exact absurd hodd (by decide)
  exact Subgroup.index_eq_one.1 h1

end GaloisForLFunctions.HTGeometry

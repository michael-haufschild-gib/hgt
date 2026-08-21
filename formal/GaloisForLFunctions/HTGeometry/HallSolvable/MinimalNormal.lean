import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Sylow

/-!
# Minimal normal subgroups of finite solvable groups

Mathlib has no notion of a minimal normal subgroup.  This file supplies the two facts about them
that the proof of P. Hall's theorem needs.

* `exists_minimal_normal` — a nontrivial finite group has a nontrivial normal subgroup that is
  minimal among the nontrivial normal subgroups.
* `exists_abelian_normal_prime_pow_card` — a nontrivial finite **solvable** group has a nontrivial
  normal subgroup which is abelian and whose order is a prime power.

The second statement is the standard "a minimal normal subgroup of a solvable group is elementary
abelian".  Abelianness comes from `IsSolvable.commutator_lt_of_ne_bot` together with the normality
of `⁅N, N⁆`; the prime-power order comes from applying minimality to the subgroup of elements
killed by a prime `p ∣ Nat.card N`, which is a subgroup precisely because `N` is abelian.
-/

namespace GaloisForLFunctions.HTGeometry.HallSolvable

open Subgroup

variable {G : Type*} [Group G]

/-- A nontrivial finite group has a nontrivial normal subgroup minimal among such. -/
theorem exists_minimal_normal [Finite G] [Nontrivial G] :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧
      ∀ M : Subgroup G, M.Normal → M ≠ ⊥ → M ≤ N → M = N := by
  obtain ⟨N, hN, hmin⟩ :=
    wellFounded_lt.has_min {N : Subgroup G | N.Normal ∧ N ≠ ⊥}
      ⟨⊤, ⟨inferInstance, Ne.symm bot_ne_top⟩⟩
  refine ⟨N, hN.1, hN.2, fun M hM hMbot hMle => ?_⟩
  by_contra hne
  exact hmin M ⟨hM, hMbot⟩ (lt_of_le_of_ne hMle hne)

/-- The elements of a subgroup with pairwise commuting elements that are killed by `p`. -/
def powTorsion (N : Subgroup G) (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (p : ℕ) :
    Subgroup G where
  carrier := {x | x ∈ N ∧ x ^ p = 1}
  one_mem' := ⟨N.one_mem, one_pow p⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨N.mul_mem ha.1 hb.1, by
      rw [Commute.mul_pow (hcomm a ha.1 b hb.1), ha.2, hb.2, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨N.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

@[simp] theorem mem_powTorsion {N : Subgroup G} {hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a} {p : ℕ}
    {x : G} : x ∈ powTorsion N hcomm p ↔ x ∈ N ∧ x ^ p = 1 := Iff.rfl

theorem powTorsion_le {N : Subgroup G} {hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a} {p : ℕ} :
    powTorsion N hcomm p ≤ N := fun _ hx => hx.1

theorem powTorsion_normal {N : Subgroup G} (hN : N.Normal)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (p : ℕ) : (powTorsion N hcomm p).Normal :=
  ⟨fun x hx g => ⟨hN.conj_mem x hx.1 g, by rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩⟩

/-- **A minimal normal subgroup of a finite solvable group is abelian of prime-power order.**
Stated as the existence of a nontrivial normal abelian subgroup of prime-power order. -/
theorem exists_abelian_normal_prime_pow_card [Finite G] [IsSolvable G] [Nontrivial G] :
    ∃ (N : Subgroup G) (p k : ℕ), N.Normal ∧ N ≠ ⊥ ∧ p.Prime ∧ 0 < k ∧
      Nat.card N = p ^ k ∧ ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
  obtain ⟨N, hNnorm, hNbot, hmin⟩ := exists_minimal_normal (G := G)
  haveI : N.Normal := hNnorm
  -- `N` is abelian.
  have hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    have hlt : ⁅N, N⁆ < N := IsSolvable.commutator_lt_of_ne_bot hNbot
    have hbot : ⁅N, N⁆ = ⊥ := by
      by_contra h
      exact hlt.ne (hmin ⁅N, N⁆ (commutator_normal N N) h hlt.le)
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    intro a ha b hb
    exact ((Subgroup.mem_centralizer_iff).mp (this ha) b hb).symm
  -- `Nat.card N` is not one, so it has a prime divisor `p`.
  have hcard : Nat.card N ≠ 1 := fun h => hNbot (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
  haveI : Fact p.Prime := ⟨hp⟩
  -- The `p`-torsion of `N` is a nontrivial normal subgroup of `G` inside `N`, hence equals `N`.
  have hMnorm : (powTorsion N hcomm p).Normal := powTorsion_normal hNnorm hcomm p
  have hMbot : powTorsion N hcomm p ≠ ⊥ := by
    haveI : Fintype N := Fintype.ofFinite _
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := N) p
      (by rwa [← Nat.card_eq_fintype_card])
    have hx1 : (x : G) ≠ 1 := by
      intro h
      rw [show x = 1 from Subtype.ext h, orderOf_one] at hx
      exact hp.ne_one hx.symm
    have hxM : (x : G) ∈ powTorsion N hcomm p := by
      refine ⟨x.2, ?_⟩
      have : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
      simpa using congrArg (Subtype.val (p := fun g => g ∈ N)) this
    intro h
    exact hx1 (by simpa [h] using hxM)
  have hMN : powTorsion N hcomm p = N :=
    hmin (powTorsion N hcomm p) hMnorm hMbot powTorsion_le
  -- Hence every element of `N` is killed by `p`, so `N` is a `p`-group.
  have hpg : IsPGroup p N := by
    intro g
    refine ⟨1, ?_⟩
    have hgM : (g : G) ∈ powTorsion N hcomm p := by rw [hMN]; exact g.2
    have hgp : (g : G) ^ p = 1 := (mem_powTorsion.mp hgM).2
    refine Subtype.ext ?_
    simpa [pow_one] using hgp
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hpg
  refine ⟨N, p, k, hNnorm, hNbot, hp, ?_, hk, hcomm⟩
  rcases Nat.eq_zero_or_pos k with h | h
  · exact absurd (by simp [hk, h]) hcard
  · exact h

end GaloisForLFunctions.HTGeometry.HallSolvable

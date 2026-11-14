import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.MaximalAvoidingCharacters
import GaloisForLFunctions.HTGeometry.CyclicSubgroupUnique
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum

/-!
# Involution avoidance and cyclic two-primary quotients

A maximal subgroup avoiding an involution has cyclic quotient of two-power order.
To remove odd torsion, raise a detecting character to the odd part of the group
order. This still detects the involution, so maximality preserves its kernel.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

variable {G : Type*} [CommGroup G] [Finite G]

/-- An involution outside a subgroup is detected by a maximal character kernel
whose quotient is both cyclic and a two-group. -/
theorem subgroup_involution_or_twoPrimary_character (K : Subgroup G) (g : G) :
    g ^ 2 ≠ 1 ∨ g ∈ K ∨ ∃ χ : G →* ℂˣ,
      K ≤ χ.ker ∧ χ g = -1 ∧ IsCyclic (G ⧸ χ.ker) ∧ IsPGroup 2 (G ⧸ χ.ker) ∧
        ∀ L : Subgroup G, χ.ker ≤ L → g ∉ L → L = χ.ker := by
  classical
  by_cases hg : g ^ 2 = 1
  swap
  · exact Or.inl hg
  right
  rcases subgroup_target_or_maximal_character K g with hK | ⟨χ, hK, hχ, hcyclic, hmax⟩
  · exact Or.inl hK
  right
  have hvalue : χ g = -1 := by
    have hs : (χ g : ℂ) ^ 2 = 1 := by
      have hpow : (χ g) ^ 2 = 1 := by rw [← map_pow, hg, map_one]
      simpa using congrArg (fun z : ℂˣ => (z : ℂ)) hpow
    rcases sq_eq_one_iff.mp hs with h | h
    · exact False.elim (hχ (Units.ext h))
    · exact Units.ext h
  obtain ⟨k, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos.ne' : Nat.card G ≠ 0)
  let ψ : G →* ℂˣ := χ ^ m
  have hψg : ψ g = -1 := by
    change χ g ^ m = -1
    rw [hvalue, hm.neg_one_pow]
  have hker : ψ.ker = χ.ker := by
    apply hmax ψ.ker
    · intro x hx
      change χ x ^ m = 1
      rw [show χ x = 1 from hx, one_pow]
    · intro hx
      have he : (-1 : ℂˣ) = 1 := hψg.symm.trans hx
      have he' := congrArg (fun z : ℂˣ => (z : ℂ)) he
      norm_num at he'
  have hpower (x : G) : ψ (x ^ (2 ^ k)) = 1 := by
    change χ (x ^ (2 ^ k)) ^ m = 1
    rw [← map_pow, ← pow_mul, ← hcard, pow_card_eq_one', map_one]
  have htwo : IsPGroup 2 (G ⧸ χ.ker) := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective χ.ker z
    refine ⟨k, ?_⟩
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff (x ^ (2 ^ k))).mpr
    rw [← hker]
    exact hpower x
  exact ⟨χ, hK, hvalue, hcyclic, htwo, hmax⟩

/-- The cyclic quotient detecting an involution has a strictly positive two-power order. -/
theorem subgroup_involution_or_twoPower_quotient (K : Subgroup G) (g : G) :
    g ^ 2 ≠ 1 ∨ g ∈ K ∨ ∃ (H : Subgroup G) (j : ℕ),
      K ≤ H ∧ g ∉ H ∧ IsCyclic (G ⧸ H) ∧ 0 < j ∧ Nat.card (G ⧸ H) = 2 ^ j := by
  rcases subgroup_involution_or_twoPrimary_character K g with h | h | ⟨χ, hK, hχ, hc, hp, _⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  have hnot : g ∉ χ.ker := by
    intro hg
    have he : (-1 : ℂˣ) = 1 := hχ.symm.trans hg
    have he' := congrArg (fun z : ℂˣ => (z : ℂ)) he
    norm_num at he'
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hp
  have hpos : 0 < j := by
    by_contra hn
    have hj0 : j = 0 := by omega
    have hcard : Nat.card (G ⧸ χ.ker) = 1 := by simpa only [hj0, pow_zero] using hj
    haveI : Subsingleton (G ⧸ χ.ker) := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact hnot ((QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _))
  exact Or.inr (Or.inr ⟨χ.ker, j, hK, hnot, hc, hpos, hj⟩)

private theorem cyclic_twoGroup_involution_mem_or_bot {A : Type*}
    [Group A] [Fintype A] [DecidableEq A] [IsCyclic A]
    (hA : IsPGroup 2 A) (g : A) (hg : g ^ 2 = 1) (L : Subgroup A) :
    g ∈ L ∨ L = ⊥ := by
  classical
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hA.to_subgroup L)
  cases k with
  | zero =>
    right
    haveI : Subsingleton L := (Nat.card_eq_one_iff_unique.mp hk).1
    apply le_antisymm _ bot_le
    intro x hx
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val
      (Subsingleton.elim (⟨x, hx⟩ : L) 1))
  | succ k =>
    left
    have hp : g ^ Fintype.card L = 1 := by
      rw [← Nat.card_eq_fintype_card, hk, pow_succ', pow_mul, hg, one_pow]
    have hs := GaloisForLFunctions.HTGeometry.subgroup_toFinset_eq_filter L
    have hm : g ∈ (L : Set A).toFinset := by
      rw [hs]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ g, hp⟩
    exact Set.mem_toFinset.mp hm

/-- Maximal avoidance of an involution is exactly a cyclic two-primary quotient. -/
theorem maximal_involution_avoidance_classification (H : Subgroup G) (g : G) :
    g ^ 2 ≠ 1 ∨
      ((g ∉ H ∧ ∀ L : Subgroup G, H ≤ L → g ∉ L → L = H) ↔
        g ∉ H ∧ IsCyclic (G ⧸ H) ∧ IsPGroup 2 (G ⧸ H)) := by
  classical
  by_cases hg : g ^ 2 = 1
  swap
  · exact Or.inl hg
  right
  constructor
  · rintro ⟨hnot, hmax⟩
    rcases subgroup_involution_or_twoPrimary_character H g with h | h | ⟨χ, hH, hχ, hc, hp, _⟩
    · exact False.elim (h hg)
    · exact False.elim (hnot h)
    have hnotχ : g ∉ χ.ker := by
      intro hx
      have he : (-1 : ℂˣ) = 1 := hχ.symm.trans hx
      have he' := congrArg (fun z : ℂˣ => (z : ℂ)) he
      norm_num at he'
    have hker := hmax χ.ker hH hnotχ
    subst H
    exact ⟨hnot, hc, hp⟩
  · rintro ⟨hnot, hc, hp⟩
    refine ⟨hnot, ?_⟩
    intro L hHL hgL
    letI : Fintype (G ⧸ H) := Fintype.ofFinite _
    letI : IsCyclic (G ⧸ H) := hc
    have hgq : (QuotientGroup.mk' H g) ^ 2 = 1 := by rw [← map_pow, hg, map_one]
    rcases cyclic_twoGroup_involution_mem_or_bot hp (QuotientGroup.mk' H g) hgq
      (L.map (QuotientGroup.mk' H)) with hmem | hbot
    · obtain ⟨x, hx, hxg⟩ := hmem
      have hxgH : x⁻¹ * g ∈ H := by
        apply (QuotientGroup.eq_one_iff (x⁻¹ * g)).mp
        change QuotientGroup.mk' H (x⁻¹ * g) = 1
        rw [map_mul, map_inv, hxg, inv_mul_cancel]
      have hgL' := L.mul_mem hx (hHL hxgH)
      exact False.elim (hgL (by simpa only [mul_inv_cancel_left] using hgL'))
    · apply le_antisymm _ hHL
      intro x hx
      have hxq : QuotientGroup.mk' H x ∈ L.map (QuotientGroup.mk' H) := ⟨x, hx, rfl⟩
      rw [hbot] at hxq
      exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp hxq)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.subgroup_involution_or_twoPrimary_character
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.subgroup_involution_or_twoPower_quotient
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.maximal_involution_avoidance_classification

import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LongPrimeReciprocals
import Mathlib.GroupTheory.Perm.Centralizer

/-! A permutation contains at most one cycle longer than half
its degree. Counting the permutations separately for each
possible prime length gives an exact reciprocal sum. -/

noncomputable section

open Equiv Equiv.Perm Finset

namespace WindowedLandauTheory.ConcN

private theorem card_disjoint_perm {α : Type} [Fintype α] [DecidableEq α] (c : Perm α)
    (B : Finset (Perm α)) (hB : ∀ τ, τ ∈ B ↔ c.Disjoint τ) :
    B.card = (Fintype.card α - c.support.card).factorial := by
  classical
  have hB' : B = Finset.univ.filter (fun τ => c.Disjoint τ) := by
    ext τ
    simp [hB]
  rw [hB', ← Fintype.card_subtype]

  have e : {τ : Perm α // c.Disjoint τ} ≃ {f : Perm α // ∀ a, ¬ (a ∉ c.support) → f a = a} :=
    Equiv.subtypeEquivRight fun τ => by
      constructor
      · intro h a ha
        rcases h a with h1 | h1
        · exact absurd (Perm.mem_support.1 (not_not.1 ha)) (not_not.2 h1)
        · exact h1
      · intro h a
        by_cases ha : a ∈ c.support
        · exact Or.inr (h a (not_not.2 ha))
        · left
          by_contra h1
          exact ha (Perm.mem_support.2 h1)
  rw [Fintype.card_congr (e.trans (Equiv.Perm.subtypeEquivSubtypePerm _).symm), Fintype.card_perm,
    Fintype.card_subtype_compl, Fintype.card_coe]

private theorem prime_cycle_perm_count (N p : ℕ) (hp : p.Prime) (hpN : p ≤ N) (hN2 : N < 2 * p)
    (S : Finset (Perm (Fin N))) (hS : ∀ σ, σ ∈ S ↔ p ∈ σ.cycleType) :
    p * S.card = N.factorial := by
  classical
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨C, hCdef⟩ : ∃ C : Finset (Perm (Fin N)), C = Finset.univ.filter (fun g => g.cycleType = {p}) :=
    ⟨_, rfl⟩
  have hmemT : ∀ σ : Perm (Fin N), p ∈ σ.cycleType ↔ ∃ c ∈ σ.cycleFactorsFinset, c.support.card = p := by
    intro σ
    rw [Equiv.Perm.cycleType_def, Multiset.mem_map]
    simp only [Finset.mem_val, Function.comp_apply]

  have hCsupp : ∀ c ∈ C, c.IsCycle ∧ c.support.card = p := by
    intro c hc
    rw [hCdef, Finset.mem_filter] at hc
    have h2 : c.support.card = p := by rw [← Equiv.Perm.sum_cycleType, hc.2, Multiset.sum_singleton]
    refine ⟨?_, h2⟩
    rw [← Equiv.Perm.card_cycleType_eq_one, hc.2, Multiset.card_singleton]
  have hmemC : ∀ c : Perm (Fin N), c.IsCycle → c.support.card = p → c ∈ C := by
    intro c hc hs
    rw [hCdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hc.cycleType, hs]⟩

  have hSU : S = C.biUnion (fun c => S.filter (fun σ => c ∈ σ.cycleFactorsFinset)) := by
    ext σ
    constructor
    · intro hσ
      obtain ⟨c, hc, hcp⟩ := (hmemT σ).1 ((hS σ).1 hσ)
      exact Finset.mem_biUnion.2 ⟨c, hmemC c (Equiv.Perm.mem_cycleFactorsFinset_iff.1 hc).1 hcp,
        Finset.mem_filter.2 ⟨hσ, hc⟩⟩
    · intro h
      obtain ⟨c, _, hσ⟩ := Finset.mem_biUnion.1 h
      exact (Finset.mem_filter.1 hσ).1

  have hdisj : (C : Set (Perm (Fin N))).PairwiseDisjoint
      (fun c => S.filter (fun σ => c ∈ σ.cycleFactorsFinset)) := by
    intro c hc c' hc' hne
    show _root_.Disjoint _ _
    show _root_.Disjoint _ _
    rw [Finset.disjoint_left]
    intro σ h1 h2
    have hd := Equiv.Perm.cycleFactorsFinset_pairwise_disjoint σ
      (Finset.mem_coe.2 (Finset.mem_filter.1 h1).2) (Finset.mem_coe.2 (Finset.mem_filter.1 h2).2) hne
    have hcard := Finset.card_le_univ (c.support ∪ c'.support)
    rw [Finset.card_union_of_disjoint hd.disjoint_support, (hCsupp c (Finset.mem_coe.1 hc)).2,
      (hCsupp c' (Finset.mem_coe.1 hc')).2, Fintype.card_fin] at hcard
    omega

  have hF : ∀ c ∈ C, (S.filter (fun σ => c ∈ σ.cycleFactorsFinset)).card = (N - p).factorial := by
    intro c hc
    obtain ⟨hcyc, hcs⟩ := hCsupp c hc
    have hB := card_disjoint_perm c (Finset.univ.filter fun τ => c.Disjoint τ) (fun τ => by simp)
    rw [Fintype.card_fin, hcs] at hB
    rw [← hB]
    symm
    refine Finset.card_bij (fun τ _ => c * τ) ?_ ?_ ?_
    · intro τ hτ
      have hd : c.Disjoint τ := (Finset.mem_filter.1 hτ).2
      have hmem : c ∈ (c * τ).cycleFactorsFinset := by
        rw [hd.cycleFactorsFinset_mul_eq_union, hcyc.cycleFactorsFinset_eq_singleton]
        exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
      exact Finset.mem_filter.2 ⟨(hS _).2 ((hmemT _).2 ⟨c, hmem, hcs⟩), hmem⟩
    · intro τ _ τ' _ h
      exact mul_left_cancel h
    · intro σ hσ
      have hmem := (Finset.mem_filter.1 hσ).2
      have hd : c.Disjoint (σ * c⁻¹) := (Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hmem).symm
      refine ⟨σ * c⁻¹, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩, ?_⟩
      rw [hd.commute.eq, inv_mul_cancel_right]
  have hcard : S.card = C.card * (N - p).factorial := by
    rw [hSU, Finset.card_biUnion hdisj, Finset.sum_congr rfl hF, Finset.sum_const, smul_eq_mul]
  have hC : C.card = (p - 1).factorial * N.choose p := by
    have h := Equiv.Perm.card_of_cycleType_singleton (α := Fin N) hp2 (by rw [Fintype.card_fin]; exact hpN)
    rw [Fintype.card_fin] at h
    rw [hCdef]
    exact h
  rw [hcard, hC]
  calc p * ((p - 1).factorial * N.choose p * (N - p).factorial)
      = N.choose p * (p * (p - 1).factorial) * (N - p).factorial := by ring
    _ = N.factorial := by
      rw [Nat.mul_factorial_pred hp.ne_zero, Nat.choose_mul_factorial_mul_factorial hpN]

open Classical in
theorem long_prime_cycle_count (N : ℕ) :
    (((univ : Finset (Perm (Fin N))).filter
      (fun σ => ∃ p ∈ σ.cycleType, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)).card : ℝ) =
      ∑ p ∈ longPrimes N, (N.factorial : ℝ) / p := by
  classical
  have hdisj : (longPrimes N : Set ℕ).PairwiseDisjoint
      (fun p => univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType) := by
    intro p hp q hq hpq
    simp only [longPrimes, Finset.mem_coe, mem_filter, mem_range] at hp hq
    show _root_.Disjoint _ _
    rw [Finset.disjoint_left]
    intro σ h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    have hq' : q ∈ σ.cycleType.erase p := (Multiset.mem_erase_of_ne hpq.symm).2 h2
    have hsum : σ.cycleType.sum ≤ N := by
      rw [Equiv.Perm.sum_cycleType]
      exact (Finset.card_le_univ _).trans (by simp)
    have hsplit : σ.cycleType.sum = p + (σ.cycleType.erase p).sum := by
      conv_lhs => rw [← Multiset.cons_erase h1]
      rw [Multiset.sum_cons]
    have hle : q ≤ (σ.cycleType.erase p).sum := Multiset.le_sum_of_mem hq'
    omega
  have hset : (univ.filter fun σ : Equiv.Perm (Fin N) => ∃ p ∈ σ.cycleType, Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N) =
      (longPrimes N).biUnion
        (fun p => univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.cycleType) := by
    ext σ
    simp only [longPrimes, mem_filter, mem_univ, true_and, mem_biUnion, mem_range]
    constructor
    · rintro ⟨p, hp, hpr, h2, h3⟩
      exact ⟨p, ⟨by omega, hpr, h2, h3⟩, hp⟩
    · rintro ⟨p, ⟨-, hpr, h2, h3⟩, hp⟩
      exact ⟨p, hp, hpr, h2, h3⟩
  rw [hset, Finset.card_biUnion hdisj, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  simp only [longPrimes, mem_filter, mem_range] at hp
  obtain ⟨hpN, hpr, h2, h3⟩ := hp
  have hk := prime_cycle_perm_count N p hpr (by omega) h2
    ((univ : Finset (Perm (Fin N))).filter (fun σ => p ∈ σ.cycleType)) (fun σ => by simp)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpr.ne_zero
  rw [eq_div_iff hp0, ← hk]
  push_cast
  ring

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.long_prime_cycle_count

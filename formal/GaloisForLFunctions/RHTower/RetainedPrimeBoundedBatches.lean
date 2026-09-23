import GaloisForLFunctions.RHTower.RetainedPrimeWindowSupply

/-!
# Unconditional growing batches for every finite retained prime field

Finite directional margins, exact prepared-state transport and simultaneous
prime-window supply produce arbitrarily long distinct actual prime batches
at cofinal parent cutoffs. Every preparation subset has the explicit finite
core-cardinality quadratic bound, and every subsequent batch prefix is below
the prepared energy. The retained field and other unselected source primes
remain; no exhaustive order or uniform bound over growing fields is asserted.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

/-- Every finite retained prime field has a fixed complementary core and
arbitrarily long actual prime batches at cofinal parent cutoffs. Every
preparation subset has the explicit core-cardinality quadratic bound, and
every batch prefix stays below the prepared energy. -/
theorem exists_retainedPrimeField_bounded_batches (Q : Finset Nat.Primes) :
    ∃ B : ℕ, ∃ P : Finset ℕ,
      P = mobiusDivisorSelectionPrimes B \ Q.image (fun q : Nat.Primes => (q : ℕ)) ∧
      Disjoint P (Q.image (fun q : Nat.Primes => (q : ℕ))) ∧
      ∀ n T : ℕ, ∃ M : ℕ, T ≤ M ∧
        Q.image (fun q : Nat.Primes => (q : ℕ)) ⊆ mobiusDivisorSelectionPrimes M ∧
        (∀ A ⊆ P, mobiusDivisorSelectionEnergy M A ≤ (2:ℝ)^P.card * 722 * (M:ℝ)^(2 : ℕ)) ∧
        ∃ l : List ℕ, l.Nodup ∧ l.length = n ∧
          Disjoint l.toFinset (P ∪ Q.image (fun q : Nat.Primes => (q : ℕ))) ∧
          (∀ p ∈ l, p.Prime ∧ p < M) ∧
          ∀ j : ℕ, mobiusDivisorSelectionEnergy M (P ∪ (l.take j).toFinset) ≤
            mobiusDivisorSelectionEnergy M P := by
  obtain ⟨K, hK, hK2, δ, hδ, hδ1, horders⟩ := exists_retainedPrimeField_pool_orders Q
  let S := Q.image (fun q : Nat.Primes => (q : ℕ))
  let B := K.sup id + S.sup id + 2
  let P := mobiusDivisorSelectionPrimes B \ S
  have hB2 : 2 ≤ B := by dsimp [B]; omega
  have hkB (k : ℕ) (hk : k ∈ K) : k+1 ≤ B := by
    have h : k ≤ K.sup id := le_sup (f := id) hk
    dsimp [B]
    omega
  have hqB (q : ℕ) (hq : q ∈ S) : q < B := by
    have h : q ≤ S.sup id := le_sup (f := id) hq
    dsimp [B]
    omega
  have hdis : Disjoint P S := by exact sdiff_disjoint
  have hcore (k : ℕ) (hk : k ∈ K) : mobiusDivisorSelectionPrimes (k+1) \ S ⊆ P := by
    intro p hp
    obtain ⟨hp, hpS⟩ := mem_sdiff.mp hp
    obtain ⟨hp, hprime⟩ := mem_filter.mp hp
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr
      ((mem_range.mp hp).trans_le (hkB k hk)), hprime⟩, hpS⟩
  obtain ⟨b0, hb0⟩ := exists_nat_gt ((2*(B:ℝ)*(B+1))/δ)
  let b := max B b0
  have hBb : B ≤ b := le_max_left _ _
  have hbδ : 2*(B:ℝ)*(B+1) ≤ (b:ℝ)*δ := by
    have hbb : (b0:ℝ) ≤ b := by exact_mod_cast (le_max_right B b0)
    have hh := (div_lt_iff₀ hδ).mp hb0
    nlinarith
  let A := ∏ k ∈ K, k
  have hA : 0 < A := prod_pos (fun k hk => by have := hK2 k hk; omega)
  have hkA (k : ℕ) (hk : k ∈ K) : k ∣ A := dvd_prod_of_mem id hk
  refine ⟨B, P, rfl, hdis, ?_⟩
  intro n T
  have hsupply : ∀ᶠ N : ℕ in atTop,
      ∀ k ∈ K, n ≤ (retainedPrimeWitnessWindow A b N k).card := by
    rw [eventually_all_finset]
    intro k hk
    exact eventually_retainedPrimeWitnessWindow_card_ge hA (hkA k hk) (by omega) n
  obtain ⟨N, hN, hcount⟩ := ((eventually_ge_atTop (T+1)).and hsupply).exists
  let M := A*(b+1)*N
  have hN1 : 1 ≤ N := by omega
  have hM : b < M := by
    have hAN : 1 ≤ A*N := Nat.mul_pos hA (by omega)
    have he : M = (b+1)*(A*N) := by dsimp [M]; ring
    nlinarith
  have hTM : T ≤ M := by
    have hAb : 1 ≤ A*(b+1) := Nat.mul_pos hA (by omega)
    dsimp [M]
    nlinarith
  have hQM : S ⊆ mobiusDivisorSelectionPrimes M := by
    intro q hq
    obtain ⟨q', hq', heq⟩ := mem_image.mp hq
    exact mem_filter.mpr ⟨mem_range.mpr ((hqB q hq).trans_le (by omega)), heq ▸ q'.property⟩
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p < M := by
    obtain ⟨hp, _⟩ := mem_sdiff.mp hp
    obtain ⟨hp, hprime⟩ := mem_filter.mp hp
    exact ⟨hprime, (mem_range.mp hp).trans_le (by omega)⟩
  let pool := retainedPrimeWitnessWindow A b N
  have hpool (k : ℕ) (hk : k ∈ K) (p : ℕ) (hp : p ∈ pool k) :
      p.Prime ∧ p < M ∧ p ∉ P ∧ p ∉ S ∧ M/p = k ∧ divisorPrimeClipWeight M p ≤ δ := by
    have hk2 := hK2 k hk
    have hkb : k ≤ b := by have := hkB k hk; omega
    obtain ⟨hpp, hpM, hbp, hquot, hw⟩ :=
      retainedPrimeWitnessWindow_data hk2 hkb hA (hkA k hk) hN1 hp
    have hpP : p ∉ P := by
      intro hpP
      have hpB := mem_range.mp (mem_filter.mp (mem_sdiff.mp hpP).1).1
      omega
    have hpS : p ∉ S := by intro hpS; have := hqB p hpS; omega
    refine ⟨hpp, hpM, hpP, hpS, hquot, ?_⟩
    have hkBR : (k:ℝ) ≤ B := by exact_mod_cast (Nat.le_of_succ_le (hkB k hk))
    have hbound : 2*(k:ℝ)*(k+1) ≤ 2*(B:ℝ)*(B+1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) B]
    have hbpos : (0:ℝ) < b := by exact_mod_cast (show 0<b by omega)
    change divisorPrimeClipWeight (A*(b+1)*N) p ≤ δ
    nlinarith only [hw, hbound, hbδ, hbpos]
  obtain ⟨l, hnd, hlen, hsub, hbound⟩ := horders M P pool n hQM hdis hcore hcount hpool
  have hl (p : ℕ) (hp : p ∈ l.toFinset) : p.Prime ∧ p < M ∧ p ∉ P ∧ p ∉ S := by
    obtain ⟨k, hk, hp⟩ := mem_biUnion.mp (hsub hp)
    obtain ⟨hpp, hpM, hpP, hpS, _, _⟩ := hpool k hk p hp
    exact ⟨hpp, hpM, hpP, hpS⟩
  refine ⟨M, hTM, hQM, fun D hD => mobiusDivisorSelectionEnergy_subcore_le M P D hP hD,
    l, hnd, hlen, ?_, ?_, hbound⟩
  · apply disjoint_left.mpr
    intro p hp hpPS
    have hp' := hl p hp
    exact (mem_union.mp hpPS).elim hp'.2.2.1 hp'.2.2.2
  · intro p hp
    have hp' := hl p (List.mem_toFinset.mpr hp)
    exact ⟨hp'.1, hp'.2.1⟩

end RHTower

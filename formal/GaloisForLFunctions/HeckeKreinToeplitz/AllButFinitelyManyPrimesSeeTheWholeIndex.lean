import GaloisForLFunctions.HeckeKreinToeplitz.OneGridHidesTwoGridsDecide

/-!
# All but finitely many primes see the whole index

The quantitative form of the local-to-global law for arithmetic pairs.

**A pair aliases at most at one prime** (`eq_of_alias_of_alias`). If two distinct exponents `ρ ≠ ρ'`
satisfy `p^{ρ−1/2} = p^{ρ'−1/2}` and `q^{ρ−1/2} = q^{ρ'−1/2}`, then `(ρ − ρ') log p` and
`(ρ − ρ') log q` are nonzero multiples of `2πi`, so `log q / log p ∈ ℚ`, and `p = q`.

**Blind primes** (`ncard_blindPrimes_le`). For `κ` distinct points right of the critical line, the
primes at which two of the characters `u ↦ u^{ρ_j−1/2}` alias number at most `κ(κ−1)/2`: each blind
prime determines an unordered pair `{j, k}`, and distinct primes give distinct pairs.

**Every other prime decides** (`negIndex_prime_eq_of_not_blind`). At a prime outside this set the
values `p^{ρ_j−1/2}` are distinct and the restriction of a Krein–Langer kernel to the tower `⟨p⟩` has
the full index `κ`. So the index of a finite arithmetic configuration is read by all primes but at
most `κ(κ−1)/2`; one tower can hide pairs only at finitely many primes.
-/

open Complex Finset
open scoped Real

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- **A pair of exponents aliases at most at one prime.** -/
theorem eq_of_alias_of_alias {ρ ρ' : ℂ} (hne : ρ ≠ ρ') {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpa : zeroChar ρ (primeElt hp) = zeroChar ρ' (primeElt hp))
    (hqa : zeroChar ρ (primeElt hq) = zeroChar ρ' (primeElt hq)) : p = q := by
  obtain ⟨n, hn⟩ := (zeroChar_prime_eq_iff hp).mp hpa
  obtain ⟨m, hm⟩ := (zeroChar_prime_eq_iff hq).mp hqa
  by_contra hpq
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hd : ρ - ρ' ≠ 0 := sub_ne_zero.mpr hne
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, zero_mul, mul_eq_zero, Complex.ofReal_eq_zero, hlp.ne',
      or_false] at hn
    exact hd hn
  -- `m log p = n log q`
  have hrel : (m : ℂ) * Real.log p = n * Real.log q := by
    have h2 : (2 * π * I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hd
    calc (ρ - ρ') * ((m : ℂ) * Real.log p) = m * ((ρ - ρ') * Real.log p) := by ring
      _ = m * (n * (2 * π * I)) := by rw [hn]
      _ = n * (m * (2 * π * I)) := by ring
      _ = n * ((ρ - ρ') * Real.log q) := by rw [hm]
      _ = (ρ - ρ') * (n * Real.log q) := by ring
  have hrel' : (m : ℝ) * Real.log p = n * Real.log q := by exact_mod_cast hrel
  have hirr := RHTower.irrational_log_ratio hp hq hpq
  exact hirr ⟨(m : ℚ) / n, by
    push_cast
    field_simp
    linarith [hrel']⟩

/-- The primes at which two of the characters `u ↦ u^{ρ_j−1/2}` alias. -/
def blindPrimes {κ : ℕ} (ρ : Fin κ → ℂ) : Set ℕ :=
  {p | ∃ hp : p.Prime, ¬ Function.Injective fun j => zeroChar (ρ j) (primeElt hp)}

/-- **At most `κ(κ−1)/2` primes are blind.** -/
theorem ncard_blindPrimes_le {κ : ℕ} (ρ : Fin κ → ℂ) (hρ : Function.Injective ρ) :
    (blindPrimes ρ).Finite ∧ (blindPrimes ρ).ncard ≤ κ.choose 2 := by
  classical
  -- each blind prime chooses an aliasing pair
  have hpair : ∀ p : blindPrimes ρ, ∃ j k : Fin κ, j ≠ k ∧
      zeroChar (ρ j) (primeElt p.2.1) = zeroChar (ρ k) (primeElt p.2.1) := fun p => by
    obtain ⟨hp, hni⟩ := p.2
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨j, k, h, hjk⟩ := hni
    exact ⟨j, k, hjk, h⟩
  choose j k hjk heq using hpair
  let F : blindPrimes ρ → (powersetCard 2 (univ : Finset (Fin κ))) := fun p =>
    ⟨{j p, k p}, mem_powersetCard.mpr ⟨subset_univ _, card_pair (hjk p)⟩⟩
  have hF : Function.Injective F := fun p p' h => by
    have hset : ({j p, k p} : Finset (Fin κ)) = {j p', k p'} := congrArg Subtype.val h
    have hp := heq p
    have hp' := heq p'
    -- the same unordered pair aliases at both primes
    have hsame : (j p = j p' ∧ k p = k p') ∨ (j p = k p' ∧ k p = j p') := by
      have h1 : j p ∈ ({j p', k p'} : Finset (Fin κ)) := hset ▸ mem_insert_self _ _
      have h2 : k p ∈ ({j p', k p'} : Finset (Fin κ)) := hset ▸ mem_insert_of_mem (mem_singleton_self _)
      simp only [mem_insert, mem_singleton] at h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) (hjk p)
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact absurd (h1.trans h2.symm) (hjk p)
    have hne : ρ (j p) ≠ ρ (k p) := fun h => hjk p (hρ h)
    refine Subtype.ext (eq_of_alias_of_alias hne p.2.1 p'.2.1 hp ?_)
    rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hp'
    · rw [h1, h2]; exact hp'.symm
  have hfin : Finite (blindPrimes ρ) := Finite.of_injective F hF
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq]
  calc Nat.card (blindPrimes ρ) ≤ Nat.card (powersetCard 2 (univ : Finset (Fin κ))) :=
        Nat.card_le_card_of_injective F hF
    _ = κ.choose 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_powersetCard,
        card_univ, Fintype.card_fin]

/-- **Every prime that is not blind sees the whole index.** -/
theorem negIndex_prime_eq_of_not_blind {κ : ℕ} {p : HeckeLattice → ℂ} (hp : IsPosDefKernel p)
    (ρ : Fin κ → ℂ) (hre : ∀ j, 1 / 2 < (ρ j).re) (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0)
    {q : ℕ} (hq : q.Prime) (hnb : q ∉ blindPrimes ρ) :
    negIndex ((fun g => p g + ∑ j, pairKernel (zeroChar (ρ j)) (ω j) g) ∘
      zpowersHom _ (primeElt hq)) = κ := by
  classical
  have hinj : Function.Injective fun j => zeroChar (ρ j) (primeElt hq) := by
    by_contra h
    exact hnb ⟨hq, h⟩
  rw [negIndex_prime_eq_card_classes hp ρ hre ω hq, filter_true_of_mem fun v hv => ?_,
    card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  obtain ⟨j, -, rfl⟩ := mem_image.mp hv
  have hfib : univ.filter (fun i => zeroChar (ρ i) (primeElt hq) =
      zeroChar (ρ j) (primeElt hq)) = {j} := by
    ext i; simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun h => hinj h, fun h => h ▸ rfl⟩
  rw [classWeight, hfib, sum_singleton]
  exact hω j

end GaloisForLFunctions.HeckeKreinToeplitz

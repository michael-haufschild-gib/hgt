import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenFiniteIterationSource
import GaloisForLFunctions.RHTower.Sieve.HarmanMinorant

/-!
# Terminal remainder in Matomäki--Teräväinen Lemma 2.3(ii)

A nonzero depth-`d` remainder supplies `d+1` primes from strictly descending, pairwise disjoint
blocks.  They are distinct prime divisors of `n`, all at least `z₀`.  Consequently the remainder
vanishes once `d` reaches `largePrimeCount n z₀`, exactly the terminal argument after (2.16).
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Existence of a strictly descending chain of chosen block primes. -/
def mtHasPrimeChain {t : ℕ} (block : Fin t → Finset ℕ) :
    ℕ → Fin (t + 1) → ℕ → Prop
  | 0, _, _ => True
  | length + 1, j, n =>
      ∃ i ∈ mtBlockPrefix j, ∃ q ∈ block i,
        q ∣ n ∧ mtHasPrimeChain block length i.castSucc (n / q)

/-- Every nonzero terminal operator coefficient exposes a descending prime chain of the displayed
length. -/
theorem mtFiniteIterationRemainder_ne_zero_hasPrimeChain {t : ℕ}
    (block : Fin t → Finset ℕ) (cutoff : Fin (t + 1) → ℕ)
    (depth : ℕ) (j : Fin (t + 1)) (n : ℕ)
    (hne : mtFiniteIterationRemainder block cutoff depth j n ≠ 0) :
    mtHasPrimeChain block (depth + 1) j n := by
  induction depth generalizing j n with
  | zero =>
      simp only [mtFiniteIterationRemainder] at hne
      have hsumAF : (∑ i ∈ mtBlockPrefix j,
          mtPrimeBlockAF (block i) * mtRhoAF (cutoff i.castSucc)) n ≠ 0 := by
        intro hz
        apply hne
        rw [ArithmeticFunction.neg_apply, hz, neg_zero]
      have hsum : (∑ i ∈ mtBlockPrefix j,
          (mtPrimeBlockAF (block i) * mtRhoAF (cutoff i.castSucc)) n) ≠ 0 := by
        simpa only [arithmeticFunction_finset_sum_apply] using hsumAF
      obtain ⟨i, hi, hiNe⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
      rw [ArithmeticFunction.mul_apply] at hiNe
      obtain ⟨x, hx, hxNe⟩ := Finset.exists_ne_zero_of_sum_ne_zero hiNe
      have hblockNe : mtPrimeBlockAF (block i) x.1 ≠ 0 := by
        intro hz
        apply hxNe
        rw [hz, zero_mul]
      have hq0 : x.1 ≠ 0 := by
        intro hq0
        apply hblockNe
        simp [mtPrimeBlockAF, hq0]
      have hqPos : 0 < x.1 := Nat.pos_of_ne_zero hq0
      have hqMem : x.1 ∈ block i := by
        rw [mtPrimeBlockAF_apply_of_pos (block i) hqPos] at hblockNe
        by_contra hnot
        simp [hnot] at hblockNe
      have hprod := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have hdiv : n / x.1 = x.2 := by
        rw [← hprod, Nat.mul_div_cancel_left _ hqPos]
      rw [mtHasPrimeChain]
      refine ⟨i, hi, x.1, hqMem, ⟨x.2, hprod.symm⟩, ?_⟩
      trivial
  | succ depth ih =>
      simp only [mtFiniteIterationRemainder] at hne
      have hsumAF : (∑ i ∈ mtBlockPrefix j,
          mtPrimeBlockAF (block i) *
            mtFiniteIterationRemainder block cutoff depth i.castSucc) n ≠ 0 := by
        intro hz
        apply hne
        rw [ArithmeticFunction.neg_apply, hz, neg_zero]
      have hsum : (∑ i ∈ mtBlockPrefix j,
          (mtPrimeBlockAF (block i) *
            mtFiniteIterationRemainder block cutoff depth i.castSucc) n) ≠ 0 := by
        simpa only [arithmeticFunction_finset_sum_apply] using hsumAF
      obtain ⟨i, hi, hiNe⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
      rw [ArithmeticFunction.mul_apply] at hiNe
      obtain ⟨x, hx, hxNe⟩ := Finset.exists_ne_zero_of_sum_ne_zero hiNe
      have hblockNe : mtPrimeBlockAF (block i) x.1 ≠ 0 := by
        intro hz
        apply hxNe
        rw [hz, zero_mul]
      have htailNe :
          mtFiniteIterationRemainder block cutoff depth i.castSucc x.2 ≠ 0 := by
        intro hz
        apply hxNe
        rw [hz, mul_zero]
      have hq0 : x.1 ≠ 0 := by
        intro hq0
        apply hblockNe
        simp [mtPrimeBlockAF, hq0]
      have hqPos : 0 < x.1 := Nat.pos_of_ne_zero hq0
      have hqMem : x.1 ∈ block i := by
        rw [mtPrimeBlockAF_apply_of_pos (block i) hqPos] at hblockNe
        by_contra hnot
        simp [hnot] at hblockNe
      have hprod := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have hdiv : n / x.1 = x.2 := by
        rw [← hprod, Nat.mul_div_cancel_left _ hqPos]
      rw [mtHasPrimeChain]
      refine ⟨i, hi, x.1, hqMem, ⟨x.2, hprod.symm⟩, ?_⟩
      simpa [hdiv] using ih i.castSucc x.2 htailNe

/-- A descending chain yields that many distinct large prime divisors.  Block disjointness is the
step that rules out repeated primes. -/
theorem MTFiniteIterationSourceData.exists_primeWitness_of_hasPrimeChain {t : ℕ}
    (data : MTFiniteIterationSourceData t) {length : ℕ} {j : Fin (t + 1)}
    {n : ℕ} (hn : 0 < n) (hchain : mtHasPrimeChain data.block length j n) :
    ∃ S : Finset ℕ,
      S.card = length ∧
      (∀ p ∈ S, p.Prime ∧ data.z₀ ≤ p ∧ p ∣ n) ∧
      (∀ p ∈ S, ∃ i ∈ mtBlockPrefix j, p ∈ data.block i) := by
  induction length generalizing j n with
  | zero =>
      exact ⟨∅, by simp, by simp, by simp⟩
  | succ length ih =>
      rw [mtHasPrimeChain] at hchain
      obtain ⟨i, hi, q, hqBlock, hqDvd, htail⟩ := hchain
      have hqPrime : q.Prime := data.block_prime i q hqBlock
      have hquotPos : 0 < n / q :=
        Nat.div_pos (Nat.le_of_dvd hn hqDvd) hqPrime.pos
      obtain ⟨S, hScard, hSprime, hSloc⟩ := ih hquotPos htail
      have hqNotMem : q ∉ S := by
        intro hqS
        obtain ⟨k, hk, hqBlockK⟩ := hSloc q hqS
        have hki : k ≠ i := by
          rw [mem_mtBlockPrefix] at hk
          change k.1 < i.1 at hk
          intro hEq
          exact (Nat.ne_of_lt hk) (congrArg Fin.val hEq)
        exact (Finset.disjoint_left.mp (data.block_disjoint k i hki)) hqBlockK hqBlock
      refine ⟨insert q S, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hqNotMem, hScard]
      · intro p hp
        rw [Finset.mem_insert] at hp
        rcases hp with hpEq | hp
        · subst p
          exact ⟨hqPrime, data.block_lower i q hqBlock, hqDvd⟩
        · obtain ⟨hpPrime, hpLower, hpDvd⟩ := hSprime p hp
          exact ⟨hpPrime, hpLower, hpDvd.trans (Nat.div_dvd_of_dvd hqDvd)⟩
      · intro p hp
        rw [Finset.mem_insert] at hp
        rcases hp with hpEq | hp
        · subst p
          exact ⟨i, hi, hqBlock⟩
        · obtain ⟨k, hk, hpBlock⟩ := hSloc p hp
          refine ⟨k, ?_, hpBlock⟩
          rw [mem_mtBlockPrefix] at hk
          change k.1 < i.1 at hk
          have hilt : i.1 < j.1 := mem_mtBlockPrefix.mp hi
          exact mem_mtBlockPrefix.mpr (hk.trans hilt)

/-- Chain length is bounded by the number of distinct prime factors of `n` above `z₀`. -/
theorem MTFiniteIterationSourceData.chainLength_le_largePrimeCount {t : ℕ}
    (data : MTFiniteIterationSourceData t) {length : ℕ} {j : Fin (t + 1)}
    {n : ℕ} (hn : 0 < n) (hchain : mtHasPrimeChain data.block length j n) :
    length ≤ largePrimeCount n data.z₀ := by
  obtain ⟨S, hScard, hSprime, -⟩ :=
    data.exists_primeWitness_of_hasPrimeChain hn hchain
  have hsubset : S ⊆ n.primeFactors.filter (fun p => data.z₀ ≤ p) := by
    intro p hp
    obtain ⟨hpPrime, hpLower, hpDvd⟩ := hSprime p hp
    rw [Finset.mem_filter, Nat.mem_primeFactors]
    exact ⟨⟨hpPrime, hpDvd, hn.ne'⟩, hpLower⟩
  rw [← hScard]
  exact Finset.card_le_card hsubset

/-- Terminal statement used in Lemma 2.3(ii): the depth-`L` remainder vanishes pointwise once
`L` dominates the large-prime count. -/
theorem MTFiniteIterationSourceData.remainder_apply_eq_zero_of_largePrimeCount_le {t : ℕ}
    (data : MTFiniteIterationSourceData t) {depth : ℕ} {j : Fin (t + 1)}
    {n : ℕ} (hn : 0 < n) (hcount : largePrimeCount n data.z₀ ≤ depth) :
    mtFiniteIterationRemainder data.block data.cutoff depth j n = 0 := by
  by_contra hne
  have hchain := mtFiniteIterationRemainder_ne_zero_hasPrimeChain
    data.block data.cutoff depth j n hne
  have hle := data.chainLength_le_largePrimeCount hn hchain
  omega

/-- Exact logarithmic upper bound for the large-prime count. -/
theorem largePrimeCount_le_floor_log_ratio {n z N : ℕ}
    (hn : 0 < n) (hz : 1 < z) (hnN : n ≤ N) :
    largePrimeCount n z ≤
      Nat.floor (Real.log (N : ℝ) / Real.log (z : ℝ)) := by
  have hpowN : z ^ largePrimeCount n z ≤ N :=
    (pow_largePrimeCount_le hn).trans hnN
  have hN : 0 < N := hn.trans_le hnN
  have hlog :
      Real.log (((z ^ largePrimeCount n z : ℕ) : ℝ)) ≤ Real.log (N : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact_mod_cast hpowN
  rw [Nat.cast_pow, Real.log_pow] at hlog
  apply Nat.le_floor
  exact (le_div_iff₀ (Real.log_pos (by exact_mod_cast hz))).2 hlog

/-- Source terminal depth `⌊log N / log z₀⌋` kills the remainder for every `n ≤ N`. -/
theorem MTFiniteIterationSourceData.remainder_apply_eq_zero_at_logDepth {t : ℕ}
    (data : MTFiniteIterationSourceData t) {j : Fin (t + 1)} {n N : ℕ}
    (hn : 0 < n) (hz₀ : 1 < data.z₀) (hnN : n ≤ N) :
    mtFiniteIterationRemainder data.block data.cutoff
      (Nat.floor (Real.log (N : ℝ) / Real.log (data.z₀ : ℝ))) j n = 0 := by
  apply data.remainder_apply_eq_zero_of_largePrimeCount_le hn
  exact largePrimeCount_le_floor_log_ratio hn hz₀ hnN

/-- Lemma 2.3(ii) after the source logarithmic terminal depth: only alternating truncated
Legendre layers and the accumulated literal error remain. -/
theorem matomakiTeravainen_lemma23ii_terminal_exact {t : ℕ}
    (data : MTFiniteIterationSourceData t) (α : ℕ → ℂ)
    (j : Fin (t + 1)) {n N : ℕ} (hn : 0 < n)
    (hz₀ : 1 < data.z₀) (hnN : n ≤ N) :
    let L := Nat.floor (Real.log (N : ℝ) / Real.log (data.z₀ : ℝ))
    mtDivisorSiftSum α (data.cutoff j) n =
      ((mtCoefficientAF α *
          mtFiniteIterationMain data.truncation data.block data.cutoff L j) +
        mtAccumulatedSourceErrorAF data (mtCoefficientAF α) L j) n := by
  dsimp only
  rw [matomakiTeravainen_lemma23ii_finite_exact data α
    (Nat.floor (Real.log (N : ℝ) / Real.log (data.z₀ : ℝ))) j hn]
  have hconv :
      (mtCoefficientAF α *
        mtFiniteIterationRemainder data.block data.cutoff
          (Nat.floor (Real.log (N : ℝ) / Real.log (data.z₀ : ℝ))) j) n = 0 := by
    rw [ArithmeticFunction.mul_apply]
    rw [show (∑ x ∈ n.divisorsAntidiagonal,
        mtCoefficientAF α x.1 *
          mtFiniteIterationRemainder data.block data.cutoff
            (Nat.floor (Real.log (N : ℝ) / Real.log (data.z₀ : ℝ))) j x.2) =
        ∑ m ∈ n.divisors, mtCoefficientAF α m *
          mtFiniteIterationRemainder data.block data.cutoff
            (Nat.floor (Real.log (N : ℝ) / Real.log (data.z₀ : ℝ))) j (n / m) by
      exact Nat.sum_divisorsAntidiagonal (M := ℂ) (n := n)
        (fun m k => mtCoefficientAF α m *
          mtFiniteIterationRemainder data.block data.cutoff
            (Nat.floor (Real.log (N : ℝ) / Real.log (data.z₀ : ℝ))) j k)]
    apply Finset.sum_eq_zero
    intro m hm
    have hmPos : 0 < m := Nat.pos_of_mem_divisors hm
    have hqPos : 0 < n / m :=
      Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hm)) hmPos
    have hqN : n / m ≤ N := (Nat.div_le_self n m).trans hnN
    rw [data.remainder_apply_eq_zero_at_logDepth hqPos hz₀ hqN, mul_zero]
  simp only [ArithmeticFunction.add_apply]
  rw [hconv, add_zero]

end

end RHTower.Sieve

import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBlockChainFactor
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenChainProducts
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenSelectedPrimeProduct

/-!
# Joint envelope for every active recursive chain

Strictly descending chains select distinct prime blocks.  At a positive integer, their unsigned
block-product coefficients are therefore mutually exclusive, both within one depth and across
different depths.  The whole recursive family has the exact ordinary-zeta envelope `1`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Active chains have the recursion depth used to construct them. -/
theorem length_eq_of_mem_mtActiveBlockChains
    {t depth : ℕ} {block : Fin t → Finset ℕ} {j : Fin (t + 1)}
    {chain : List (Fin t)} (hchain : chain ∈ mtActiveBlockChains block depth j) :
    chain.length = depth := by
  induction depth generalizing j chain with
  | zero =>
      simp [mtActiveBlockChains] at hchain
      subst chain
      simp
  | succ depth ih =>
      rw [mtActiveBlockChains] at hchain
      obtain ⟨i, hi, tail, htail, rfl⟩ := by
        simpa only [Finset.mem_biUnion, Finset.mem_image] using hchain
      simp [ih htail]

/-- Membership in a depth-`d` chain-product family forces exactly `d` distinct prime factors. -/
theorem card_primeFactors_eq_of_mem_mtChainProducts
    {t : ℕ} (data : MTFiniteIterationSourceData t)
    (depth : ℕ) (j : Fin (t + 1)) {n : ℕ}
    (hn : n ∈ mtChainProducts data depth j) :
    n.primeFactors.card = depth := by
  induction depth generalizing j n with
  | zero =>
      simp only [mtChainProducts, Finset.mem_singleton] at hn
      subst n
      simp
  | succ depth ih =>
      rw [mtChainProducts] at hn
      obtain ⟨i, hi, q, hq, d, hd, rfl⟩ := by
        simpa only [Finset.mem_biUnion, Finset.mem_image] using hn
      have hqPrime := data.block_prime i q hq
      have hdPos := mtChainProducts_pos data depth i.castSucc hd
      have hqNotMem : q ∉ d.primeFactors := by
        intro hqMem
        exact (not_dvd_mtChainProducts_of_mem_block data depth i hq hd)
          (Nat.mem_primeFactors.mp hqMem).2.1
      rw [Nat.primeFactors_mul hqPrime.ne_zero hdPos.ne', hqPrime.primeFactors,
        Finset.singleton_union, Finset.card_insert_of_notMem hqNotMem, ih i.castSucc hd]

/-- Unsigned fixed-chain block products sum to the recursive coefficient with unit tail. -/
theorem mtIteratedCoefficientAF_one_eq_sum_activeChainFamilies
    {t : ℕ} (data : MTFiniteIterationSourceData t)
    (depth : ℕ) (j : Fin (t + 1)) :
    mtIteratedCoefficientAF data (1 : ArithmeticFunction ℂ) depth j =
      ∑ chain ∈ mtActiveBlockChains data.block depth j,
        mtPrimeBlockFamilyAF data.block chain.toFinset := by
  induction depth generalizing j with
  | zero =>
      simp [mtIteratedCoefficientAF, mtActiveBlockChains, mtPrimeBlockFamilyAF]
  | succ depth ih =>
      rw [mtIteratedCoefficientAF, ← sum_mtActiveBlockPrefix_eq]
      rw [mtActiveBlockChains]
      have hpair :
          (↑(mtActiveBlockPrefix data.block j) : Set (Fin t)).PairwiseDisjoint fun i =>
            (mtActiveBlockChains data.block depth i.castSucc).image fun chain => i :: chain := by
        intro i hi k hk hik
        change Disjoint
          ((mtActiveBlockChains data.block depth i.castSucc).image fun chain => i :: chain)
          ((mtActiveBlockChains data.block depth k.castSucc).image fun chain => k :: chain)
        rw [Finset.disjoint_left]
        intro chain hchainI hchainK
        obtain ⟨tailI, htailI, rfl⟩ := Finset.mem_image.mp hchainI
        obtain ⟨tailK, htailK, heq⟩ := Finset.mem_image.mp hchainK
        exact hik (List.cons.inj heq.symm).1
      rw [Finset.sum_biUnion hpair]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_image (by
        intro a ha b hb hab
        exact (List.cons.inj hab).2)]
      rw [ih i.castSucc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chain hchain
      have hiNot : i ∉ chain := by
        intro hiMem
        have hlt := mem_activeBlockChain_lt hchain i hiMem
        simp at hlt
      simp [mtPrimeBlockFamilyAF, hiNot]

/-- At fixed depth, all active-chain coefficient norms form one membership indicator. -/
theorem sum_norm_mtPrimeBlockFamilyAF_activeChains_eq_indicator
    {t : ℕ} (data : MTFiniteIterationSourceData t)
    (depth : ℕ) (j : Fin (t + 1)) {n : ℕ} (hn : 0 < n) :
    ∑ chain ∈ mtActiveBlockChains data.block depth j,
        ‖mtPrimeBlockFamilyAF data.block chain.toFinset n‖ =
      if n ∈ mtChainProducts data depth j then 1 else 0 := by
  have hnorm : ∀ chain ∈ mtActiveBlockChains data.block depth j,
      ‖mtPrimeBlockFamilyAF data.block chain.toFinset n‖ =
        (mtPrimeBlockFamilyAF data.block chain.toFinset n).re := by
    intro chain hchain
    rw [mtPrimeBlockFamilyAF_eq_enumeratedTypeIIPrimeCoefficientAF]
    · rw [mtCoefficientAF_apply_of_pos _ hn]
      simp [mtTypeIIPrimeCoefficient]
    · intro i hi q hq
      exact (data.block_prime i q hq).pos
  calc
    ∑ chain ∈ mtActiveBlockChains data.block depth j,
        ‖mtPrimeBlockFamilyAF data.block chain.toFinset n‖ =
        ∑ chain ∈ mtActiveBlockChains data.block depth j,
          (mtPrimeBlockFamilyAF data.block chain.toFinset n).re := by
      apply Finset.sum_congr rfl
      intro chain hchain
      exact hnorm chain hchain
    _ = ((∑ chain ∈ mtActiveBlockChains data.block depth j,
          mtPrimeBlockFamilyAF data.block chain.toFinset) n).re := by
      simp [arithmeticFunction_finset_sum_apply]
    _ = (mtIteratedCoefficientAF data (1 : ArithmeticFunction ℂ) depth j n).re := by
      rw [mtIteratedCoefficientAF_one_eq_sum_activeChainFamilies]
    _ = (∑ d ∈ mtChainProducts data depth j,
          if n = d then (1 : ℂ) else 0).re := by
      rw [mtIteratedCoefficientAF_apply_eq_chainProducts data
        (1 : ArithmeticFunction ℂ) depth j hn]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      have hdPos := mtChainProducts_pos data depth j hd
      by_cases hdvd : d ∣ n
      · have hdiv : n / d = 1 ↔ n = d := by
          rw [Nat.div_eq_iff_eq_mul_left hdPos hdvd]
          simp
        simp [hdvd, ArithmeticFunction.one_apply, hdiv]
      · have hne : n ≠ d := by
          intro h
          subst n
          exact hdvd dvd_rfl
        simp [hdvd, hne]
    _ = if n ∈ mtChainProducts data depth j then 1 else 0 := by
      split_ifs <;> simp [Finset.sum_ite_eq, *]

/-- Every active recursive chain through every depth has the exact ordinary-zeta envelope. -/
theorem sum_norm_mtPrimeBlockFamilyAF_allActiveChains_le_one
    {t : ℕ} (data : MTFiniteIterationSourceData t)
    (maxDepth : ℕ) (j : Fin (t + 1)) (n : ℕ) :
    ∑ depth ∈ Finset.range (maxDepth + 1),
      ∑ chain ∈ mtActiveBlockChains data.block depth j,
        ‖mtPrimeBlockFamilyAF data.block chain.toFinset n‖ ≤ 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [mtPrimeBlockFamilyAF]
  · rw [Finset.sum_congr rfl (fun depth hdepth =>
      sum_norm_mtPrimeBlockFamilyAF_activeChains_eq_indicator data depth j hn)]
    rw [Finset.sum_boole]
    exact_mod_cast (Finset.card_le_one.mpr (by
      intro a ha b hb
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have hca := card_primeFactors_eq_of_mem_mtChainProducts data a j ha'
      have hcb := card_primeFactors_eq_of_mem_mtChainProducts data b j hb'
      omega))

end

end RHTower.Sieve

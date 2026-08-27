import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenChainProducts
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenErrorLayers

/-!
# Terminal coefficient fibres in the Matomäki--Teräväinen iteration

A fixed error depth contains many descending block chains but only finitely many terminal cutoffs.
This file groups all chains with the same terminal cutoff.  Strict block ordering still identifies
their prime products, so every terminal coefficient has one ordinary divisor-function envelope.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Products of depth-many descending block primes whose recursion terminates at `k`. -/
def mtTerminalChainProducts {t : ℕ} (data : MTFiniteIterationSourceData t) :
    ℕ → Fin (t + 1) → Fin (t + 1) → Finset ℕ
  | 0, j, k => if j = k then {1} else ∅
  | depth + 1, j, k =>
      (mtBlockPrefix j).biUnion fun i =>
        (data.block i).biUnion fun q =>
          (mtTerminalChainProducts data depth i.castSucc k).image fun d => q * d

/-- One terminal fibre is a subset of the full chain-product family. -/
theorem mtTerminalChainProducts_subset {t : ℕ} (data : MTFiniteIterationSourceData t)
    (depth : ℕ) (j k : Fin (t + 1)) :
    mtTerminalChainProducts data depth j k ⊆ mtChainProducts data depth j := by
  induction depth generalizing j with
  | zero =>
      by_cases hjk : j = k
      · simp [mtTerminalChainProducts, mtChainProducts, hjk]
      · simp [mtTerminalChainProducts, hjk]
  | succ depth ih =>
      intro d hd
      rw [mtTerminalChainProducts] at hd
      obtain ⟨i, hi, q, hq, e, he, rfl⟩ := by
        simpa only [Finset.mem_biUnion, Finset.mem_image] using hd
      rw [mtChainProducts]
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_biUnion.mpr
        ⟨q, hq, Finset.mem_image.mpr ⟨e, ih i.castSucc he, rfl⟩⟩⟩

/-- Prime-product images of terminal fibres remain pairwise disjoint within one block. -/
theorem mtTerminalChainProducts_block_pairwiseDisjoint {t : ℕ}
    (data : MTFiniteIterationSourceData t) (depth : ℕ)
    (i : Fin t) (k : Fin (t + 1)) :
    (↑(data.block i) : Set ℕ).PairwiseDisjoint fun q =>
      (mtTerminalChainProducts data depth i.castSucc k).image fun d => q * d := by
  intro q hq r hr hqr
  apply (mtChainProducts_images_disjoint_of_ne data depth i hq hr hqr).mono
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr
      ⟨d, mtTerminalChainProducts_subset data depth i.castSucc k hd, rfl⟩
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr
      ⟨d, mtTerminalChainProducts_subset data depth i.castSucc k hd, rfl⟩

/-- Highest-block families of one terminal fibre remain pairwise disjoint. -/
theorem mtTerminalChainProducts_prefix_pairwiseDisjoint {t : ℕ}
    (data : MTFiniteIterationSourceData t) (depth : ℕ)
    (j k : Fin (t + 1)) :
    (↑(mtBlockPrefix j) : Set (Fin t)).PairwiseDisjoint fun i =>
      (data.block i).biUnion fun q =>
        (mtTerminalChainProducts data depth i.castSucc k).image fun d => q * d := by
  intro i hi u hu hiu
  apply (mtChainProducts_blocks_disjoint_of_ne data depth hiu).mono
  · intro x hx
    obtain ⟨q, hq, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_image.mpr
      ⟨d, mtTerminalChainProducts_subset data depth i.castSucc k hd, rfl⟩⟩
  · intro x hx
    obtain ⟨q, hq, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_image.mpr
      ⟨d, mtTerminalChainProducts_subset data depth u.castSucc k hd, rfl⟩⟩

/-- Aggregate coefficient from all depth-many chains ending at one terminal cutoff. -/
def mtTerminalCoefficientAF {t : ℕ} (data : MTFiniteIterationSourceData t)
    (a : ArithmeticFunction ℂ) :
    ℕ → Fin (t + 1) → Fin (t + 1) → ArithmeticFunction ℂ
  | 0, j, k => if j = k then a else 0
  | depth + 1, j, k =>
      ∑ i ∈ mtBlockPrefix j,
        mtPrimeBlockAF (data.block i) *
          mtTerminalCoefficientAF data a depth i.castSucc k

/-- Terminal aggregation commutes with convolution by a fixed coefficient. -/
theorem mtTerminalCoefficientAF_mul {t : ℕ} (data : MTFiniteIterationSourceData t)
    (a b : ArithmeticFunction ℂ) (depth : ℕ) (j k : Fin (t + 1)) :
    mtTerminalCoefficientAF data (a * b) depth j k =
      a * mtTerminalCoefficientAF data b depth j k := by
  induction depth generalizing j with
  | zero =>
      by_cases hjk : j = k
      · simp [mtTerminalCoefficientAF, hjk]
      · simp [mtTerminalCoefficientAF, hjk]
  | succ depth ih =>
      rw [mtTerminalCoefficientAF, mtTerminalCoefficientAF, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih]
      ring

/-- Exact divisor-sum formula for one terminal coefficient fibre. -/
theorem mtTerminalCoefficientAF_apply_eq_chainProducts {t : ℕ}
    (data : MTFiniteIterationSourceData t) (a : ArithmeticFunction ℂ)
    (depth : ℕ) (j k : Fin (t + 1)) {n : ℕ} (hn : 0 < n) :
    mtTerminalCoefficientAF data a depth j k n =
      ∑ d ∈ mtTerminalChainProducts data depth j k,
        if d ∣ n then a (n / d) else 0 := by
  induction depth generalizing j n with
  | zero =>
      by_cases hjk : j = k
      · subst k
        simp [mtTerminalCoefficientAF, mtTerminalChainProducts]
      · simp [mtTerminalCoefficientAF, mtTerminalChainProducts, hjk]
  | succ depth ih =>
      rw [mtTerminalCoefficientAF, mtTerminalChainProducts,
        arithmeticFunction_finset_sum_apply]
      rw [Finset.sum_biUnion
        (mtTerminalChainProducts_prefix_pairwiseDisjoint data depth j k)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_biUnion
        (mtTerminalChainProducts_block_pairwiseDisjoint data depth i k)]
      rw [mtPrimeBlockAF_mul_apply_eq_sum _ _ hn]
      apply Finset.sum_congr rfl
      intro q hq
      rw [sum_image_mul_ite_dvd _ _ (data.block_prime i q hq).pos]
      by_cases hqn : q ∣ n
      · simp only [hqn, if_true]
        rw [ih i.castSucc (Nat.div_pos (Nat.le_of_dvd hn hqn)
          (data.block_prime i q hq).pos)]
      · simp [hqn]

/-- Every terminal coefficient has a depth-uniform ordinary-divisor envelope. -/
theorem MTFiniteIterationSourceData.norm_mtTerminalCoefficientAF_le_card_divisors
    {t : ℕ} (data : MTFiniteIterationSourceData t)
    (a : ArithmeticFunction ℂ) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ {m : ℕ}, 0 < m → ‖a m‖ ≤ B)
    (depth : ℕ) (j k : Fin (t + 1)) {n : ℕ} (hn : 0 < n) :
    ‖mtTerminalCoefficientAF data a depth j k n‖ ≤
      B * (n.divisors.card : ℝ) := by
  rw [mtTerminalCoefficientAF_apply_eq_chainProducts data a depth j k hn]
  let S := (mtTerminalChainProducts data depth j k).filter fun d => d ∣ n
  have hrewrite :
      (∑ d ∈ mtTerminalChainProducts data depth j k,
          if d ∣ n then a (n / d) else 0) =
        ∑ d ∈ S, a (n / d) := by
    dsimp [S]
    rw [← Finset.sum_filter]
  rw [hrewrite]
  have hsubset : S ⊆ n.divisors := by
    intro d hd
    simp only [S, Finset.mem_filter] at hd
    exact Nat.mem_divisors.mpr ⟨hd.2, hn.ne'⟩
  calc
    ‖∑ d ∈ S, a (n / d)‖ ≤ ∑ d ∈ S, ‖a (n / d)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ S, B := by
      apply Finset.sum_le_sum
      intro d hd
      have hdDvd : d ∣ n := (Nat.mem_divisors.mp (hsubset hd)).1
      exact ha (Nat.div_pos (Nat.le_of_dvd hn hdDvd)
        (Nat.pos_of_mem_divisors (hsubset hd)))
    _ = B * (S.card : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ B * (n.divisors.card : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact_mod_cast Finset.card_le_card hsubset

/-- Unsigned sum of one-step error kernels after grouping chains by terminal cutoff. -/
def mtTerminalErrorSumAF {t : ℕ} (data : MTFiniteIterationSourceData t)
    (a : ArithmeticFunction ℂ) (depth : ℕ) (j : Fin (t + 1)) :
    ArithmeticFunction ℂ :=
  ∑ k : Fin (t + 1),
    mtTerminalCoefficientAF data a depth j k *
      mtOneStepErrorKernel data.truncation data.block data.cutoff k

@[simp] theorem mtTerminalErrorSumAF_zero {t : ℕ}
    (data : MTFiniteIterationSourceData t) (a : ArithmeticFunction ℂ)
    (j : Fin (t + 1)) :
    mtTerminalErrorSumAF data a 0 j =
      a * mtOneStepErrorKernel data.truncation data.block data.cutoff j := by
  simp [mtTerminalErrorSumAF, mtTerminalCoefficientAF]

/-- Advancing one depth distributes terminal aggregation over the next descending block. -/
theorem mtTerminalErrorSumAF_succ {t : ℕ}
    (data : MTFiniteIterationSourceData t) (a : ArithmeticFunction ℂ)
    (depth : ℕ) (j : Fin (t + 1)) :
    mtTerminalErrorSumAF data a (depth + 1) j =
      ∑ i ∈ mtBlockPrefix j,
        mtTerminalErrorSumAF data
          (a * mtPrimeBlockAF (data.block i)) depth i.castSucc := by
  unfold mtTerminalErrorSumAF
  simp only [mtTerminalCoefficientAF, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  have hcoeff :
      mtTerminalCoefficientAF data
          (a * mtPrimeBlockAF (data.block i)) depth i.castSucc k =
        mtPrimeBlockAF (data.block i) *
          mtTerminalCoefficientAF data a depth i.castSucc k := by
    rw [mul_comm]
    exact mtTerminalCoefficientAF_mul data
      (mtPrimeBlockAF (data.block i)) a depth i.castSucc k
  rw [hcoeff]

/-- A signed source layer is the alternating terminal-fibre error sum. -/
theorem mtSignedSourceErrorLayerAF_eq_sign_smul_terminalErrorSumAF {t : ℕ}
    (data : MTFiniteIterationSourceData t) (a : ArithmeticFunction ℂ)
    (depth : ℕ) (j : Fin (t + 1)) :
    mtSignedSourceErrorLayerAF data a depth j =
      ((-1 : ℂ) ^ depth) • mtTerminalErrorSumAF data a depth j := by
  induction depth generalizing a j with
  | zero => simp [mtSignedSourceErrorLayerAF]
  | succ depth ih =>
      rw [mtSignedSourceErrorLayerAF, mtTerminalErrorSumAF_succ]
      simp_rw [ih]
      rw [pow_succ]
      simp only [mul_neg, mul_one, neg_smul, Finset.smul_sum,
        Finset.sum_neg_distrib]

/-- Literal signed layer as a finite sum of terminal one-step errors. -/
theorem mtLiteralSignedSourceErrorLayer_eq_terminalErrors {t : ℕ}
    (data : MTFiniteIterationSourceData t) (a : ArithmeticFunction ℂ)
    (depth : ℕ) (j : Fin (t + 1)) {n : ℕ} (hn : 0 < n) :
    mtLiteralSignedSourceErrorLayer data a depth j n =
      ((-1 : ℂ) ^ depth) *
        ∑ k : Fin (t + 1),
          mtLemma23Error
            (fun m => mtTerminalCoefficientAF data a depth j k m)
            data.z₀ data.D (data.lowerSpill k) (data.upperSpill k)
            (primesIco data.z₀ (data.cutoff k)) (data.lower k) n := by
  have h := congrArg (fun F : ArithmeticFunction ℂ => F n)
    (mtSignedSourceErrorLayerAF_eq_sign_smul_terminalErrorSumAF
      data a depth j)
  rw [mtSignedSourceErrorLayerAF_apply_eq_literal data a depth j hn] at h
  unfold mtTerminalErrorSumAF at h
  rw [ArithmeticFunction.smul_apply, arithmeticFunction_finset_sum_apply] at h
  have hsum :
      (∑ k : Fin (t + 1),
          (mtTerminalCoefficientAF data a depth j k *
            mtOneStepErrorKernel data.truncation data.block data.cutoff k) n) =
        ∑ k : Fin (t + 1),
          mtLemma23Error
            (fun m => mtTerminalCoefficientAF data a depth j k m)
            data.z₀ data.D (data.lowerSpill k) (data.upperSpill k)
            (primesIco data.z₀ (data.cutoff k)) (data.lower k) n := by
    apply Finset.sum_congr rfl
    intro k hk
    exact data.oneStepError_apply
      (mtTerminalCoefficientAF data a depth j k) k hn
  rw [hsum] at h
  exact h

end

end RHTower.Sieve

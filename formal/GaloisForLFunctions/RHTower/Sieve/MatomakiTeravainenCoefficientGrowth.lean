import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenFiniteIterationSource
import GaloisForLFunctions.RHTower.Sieve.HarmanMinorant

/-!
# Coefficient growth in Matomäki--Teräväinen Lemma 2.3(ii)

The coefficient sequence after `d` descending block choices is bounded by `B K^d`, where `K`
bounds the number of prime divisors at least `z₀`.  This is the exact finite combinatorial estimate
used after equation (2.15), with block disjointness preventing an extra adic-grid factor.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Convolution by one prime-block indicator is the literal prime-divisor sum. -/
theorem mtPrimeBlockAF_mul_apply_eq_sum (a : ArithmeticFunction ℂ)
    (S : Finset ℕ) {n : ℕ} (hn : 0 < n) :
    (mtPrimeBlockAF S * a) n =
      ∑ q ∈ S, if q ∣ n then a (n / q) else 0 := by
  rw [ArithmeticFunction.mul_apply]
  rw [show (∑ x ∈ n.divisorsAntidiagonal,
      mtPrimeBlockAF S x.1 * a x.2) =
      ∑ q ∈ n.divisors, mtPrimeBlockAF S q * a (n / q) by
    exact Nat.sum_divisorsAntidiagonal (M := ℂ) (n := n)
      (fun q m => mtPrimeBlockAF S q * a m)]
  calc
    (∑ q ∈ n.divisors, mtPrimeBlockAF S q * a (n / q)) =
        ∑ q ∈ n.divisors, if q ∈ S then a (n / q) else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [mtPrimeBlockAF_apply_of_pos S (Nat.pos_of_mem_divisors hq)]
      split_ifs <;> ring
    _ = ∑ q ∈ S, if q ∣ n then a (n / q) else 0 :=
      sum_divisors_indicator_eq_sum_finset_dvd hn S (fun q => a (n / q))

/-- Total number of block/divisor choices in a prefix is bounded by the large-prime count. -/
theorem MTFiniteIterationSourceData.sum_card_blockDivisors_le_largePrimeCount
    {t : ℕ} (data : MTFiniteIterationSourceData t)
    (j : Fin (t + 1)) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ mtBlockPrefix j, ((data.block i).filter (fun q => q ∣ n)).card ≤
      largePrimeCount n data.z₀ := by
  classical
  let filtered : Fin t → Finset ℕ :=
    fun i => (data.block i).filter (fun q => q ∣ n)
  have hpair : (↑(mtBlockPrefix j) : Set (Fin t)).PairwiseDisjoint filtered := by
    intro i hi k hk hik
    exact (data.block_disjoint i k hik).mono (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)
  have hcard :
      ((mtBlockPrefix j).biUnion filtered).card =
        ∑ i ∈ mtBlockPrefix j, (filtered i).card := by
    simpa using
      (Finset.sum_biUnion (f := fun _ : ℕ => (1 : ℕ)) hpair)
  have hsubset :
      (mtBlockPrefix j).biUnion filtered ⊆
        n.primeFactors.filter (fun p => data.z₀ ≤ p) := by
    intro q hq
    obtain ⟨i, hi, hqFiltered⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hqBlock, hqDvd⟩ := Finset.mem_filter.mp hqFiltered
    rw [Finset.mem_filter, Nat.mem_primeFactors]
    exact ⟨⟨data.block_prime i q hqBlock, hqDvd, hn.ne'⟩,
      data.block_lower i q hqBlock⟩
  rw [← hcard]
  exact Finset.card_le_card hsubset

/-- Coefficient sequence obtained by choosing exactly `depth` strictly descending prime blocks. -/
def mtIteratedCoefficientAF {t : ℕ} (data : MTFiniteIterationSourceData t)
    (a : ArithmeticFunction ℂ) : ℕ → Fin (t + 1) → ArithmeticFunction ℂ
  | 0, _ => a
  | depth + 1, j =>
      ∑ i ∈ mtBlockPrefix j,
        mtPrimeBlockAF (data.block i) *
          mtIteratedCoefficientAF data a depth i.castSucc

/-- The source's coefficient-growth estimate: at most `K` admissible prime-divisor choices per
layer, hence `B K^depth` after `depth` layers. -/
theorem MTFiniteIterationSourceData.norm_mtIteratedCoefficientAF_le
    {t : ℕ} (data : MTFiniteIterationSourceData t)
    (a : ArithmeticFunction ℂ) (N K : ℕ) (B : ℝ)
    (hB : 0 ≤ B)
    (ha : ∀ {n : ℕ}, 0 < n → n ≤ N → ‖a n‖ ≤ B)
    (hcount : ∀ {n : ℕ}, 0 < n → n ≤ N → largePrimeCount n data.z₀ ≤ K)
    (depth : ℕ) (j : Fin (t + 1)) {n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    ‖mtIteratedCoefficientAF data a depth j n‖ ≤
      B * (K : ℝ) ^ depth := by
  induction depth generalizing j n with
  | zero => simpa [mtIteratedCoefficientAF] using ha hn hnN
  | succ depth ih =>
      rw [mtIteratedCoefficientAF, arithmeticFunction_finset_sum_apply]
      calc
        ‖∑ i ∈ mtBlockPrefix j,
            (mtPrimeBlockAF (data.block i) *
              mtIteratedCoefficientAF data a depth i.castSucc) n‖ ≤
            ∑ i ∈ mtBlockPrefix j,
              ‖(mtPrimeBlockAF (data.block i) *
                mtIteratedCoefficientAF data a depth i.castSucc) n‖ :=
          norm_sum_le _ _
        _ ≤ ∑ i ∈ mtBlockPrefix j,
            ((data.block i).filter (fun q => q ∣ n)).card *
              (B * (K : ℝ) ^ depth) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [mtPrimeBlockAF_mul_apply_eq_sum _ _ hn]
          calc
            ‖∑ q ∈ data.block i,
                if q ∣ n then mtIteratedCoefficientAF data a depth i.castSucc (n / q)
                else 0‖ ≤
                ∑ q ∈ data.block i,
                  ‖if q ∣ n then
                    mtIteratedCoefficientAF data a depth i.castSucc (n / q)
                    else 0‖ := norm_sum_le _ _
            _ ≤ ∑ q ∈ data.block i,
                if q ∣ n then B * (K : ℝ) ^ depth else 0 := by
              apply Finset.sum_le_sum
              intro q hq
              by_cases hqn : q ∣ n
              · have hqPrime := data.block_prime i q hq
                have hquotPos : 0 < n / q :=
                  Nat.div_pos (Nat.le_of_dvd hn hqn) hqPrime.pos
                have hquotN : n / q ≤ N := (Nat.div_le_self n q).trans hnN
                simpa [hqn] using ih i.castSucc hquotPos hquotN
              · simp [hqn]
            _ = ((data.block i).filter (fun q => q ∣ n)).card *
                (B * (K : ℝ) ^ depth) := by
              rw [← Finset.sum_filter]
              simp [Finset.sum_const, nsmul_eq_mul]
        _ = (∑ i ∈ mtBlockPrefix j,
              ((data.block i).filter (fun q => q ∣ n)).card : ℕ) *
            (B * (K : ℝ) ^ depth) := by
          push_cast
          rw [Finset.sum_mul]
        _ ≤ (K : ℝ) * (B * (K : ℝ) ^ depth) := by
          gcongr
          exact_mod_cast data.sum_card_blockDivisors_le_largePrimeCount j hn |>.trans
            (hcount hn hnN)
        _ = B * (K : ℝ) ^ (depth + 1) := by ring

end

end RHTower.Sieve

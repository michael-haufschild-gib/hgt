import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPairBoxTypeII
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanCellConvolution

/-!
# Exact factorization of a triple Harman cell

The Type-I/II grouping separates `q1` from the pair `(q2,q3)`.  This file proves that the literal
triple tuple coefficient is exactly the corresponding Dirichlet convolution, not merely bounded
by it.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

private theorem sum_finset_if_mul_eq
    (S : Finset ℕ) {d n : ℕ} (hd : 0 < d) :
    (∑ q ∈ S, if q * d = n then (1 : ℂ) else 0) =
      if d ∣ n then if n / d ∈ S then 1 else 0 else 0 := by
  by_cases hdvd : d ∣ n
  · rw [if_pos hdvd]
    let q0 := n / d
    have hq0 : q0 * d = n := Nat.div_mul_cancel hdvd
    by_cases hmem : q0 ∈ S
    · rw [if_pos hmem, Finset.sum_eq_single q0]
      · simp [hq0]
      · intro q hq hne
        have hnot : q * d ≠ n := by
          intro heq
          apply hne
          apply Nat.eq_of_mul_eq_mul_right hd
          exact heq.trans hq0.symm
        simp [hnot]
      · exact fun hnot => (hnot hmem).elim
    · rw [if_neg hmem]
      apply Finset.sum_eq_zero
      intro q hq
      have hnot : q * d ≠ n := by
        intro heq
        apply hmem
        have hq0eq : q = q0 := by
          apply Nat.eq_of_mul_eq_mul_right hd
          exact heq.trans hq0.symm
        simpa [hq0eq] using hq
      simp [hnot]
  · rw [if_neg hdvd]
    apply Finset.sum_eq_zero
    intro q hq
    have hnot : q * d ≠ n := by
      intro heq
      apply hdvd
      exact ⟨q, by simpa [Nat.mul_comm] using heq.symm⟩
    simp [hnot]

/-- Triple tuple coefficient equals pair coefficient convolved with the first prime block. -/
theorem mtCoefficientAF_tripleCell_eq_pairCell_mul_primeBlock
    (S1 S2 S3 : Finset ℕ)
    (hpos2 : ∀ q ∈ S2, 0 < q) (hpos3 : ∀ q ∈ S3, 0 < q) :
    mtCoefficientAF (mtHarmanTripleCellCoefficient S1 S2 S3) =
      mtCoefficientAF (mtHarmanPairCellCoefficient S2 S3) * mtPrimeBlockAF S1 := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [mtCoefficientAF]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    rw [mtCoefficientAF_apply_of_pos _ hnPos, ArithmeticFunction.mul_apply]
    rw [show (∑ de ∈ n.divisorsAntidiagonal,
        mtCoefficientAF (mtHarmanPairCellCoefficient S2 S3) de.1 *
          mtPrimeBlockAF S1 de.2) =
      ∑ m ∈ n.divisors,
        mtCoefficientAF (mtHarmanPairCellCoefficient S2 S3) m *
          mtPrimeBlockAF S1 (n / m) by
      exact Nat.sum_divisorsAntidiagonal (M := ℂ) (n := n)
        (fun m q => mtCoefficientAF (mtHarmanPairCellCoefficient S2 S3) m *
          mtPrimeBlockAF S1 q)]
    simp only [mtHarmanTripleCellCoefficient_eq_source_sum]
    calc
      (∑ q1 ∈ S1, ∑ q2 ∈ S2, ∑ q3 ∈ S3,
          if q1 * q2 * q3 = n then (1 : ℂ) else 0) =
          ∑ q2 ∈ S2, ∑ q3 ∈ S3, ∑ q1 ∈ S1,
            if q1 * (q2 * q3) = n then (1 : ℂ) else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q2 hq2
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q3 hq3
        apply Finset.sum_congr rfl
        intro q1 hq1
        simp only [Nat.mul_assoc]
      _ = ∑ q2 ∈ S2, ∑ q3 ∈ S3,
          if q2 * q3 ∣ n then if n / (q2 * q3) ∈ S1 then 1 else 0 else 0 := by
        apply Finset.sum_congr rfl
        intro q2 hq2
        apply Finset.sum_congr rfl
        intro q3 hq3
        exact sum_finset_if_mul_eq S1 (Nat.mul_pos (hpos2 q2 hq2) (hpos3 q3 hq3))
      _ = ∑ m ∈ n.divisors,
          (∑ q2 ∈ S2, ∑ q3 ∈ S3, if q2 * q3 = m then 1 else 0) *
            mtPrimeBlockAF S1 (n / m) := by
        calc
          _ = ∑ q2 ∈ S2, ∑ q3 ∈ S3, ∑ m ∈ n.divisors,
              if q2 * q3 = m then mtPrimeBlockAF S1 (n / m) else 0 := by
            apply Finset.sum_congr rfl
            intro q2 hq2
            apply Finset.sum_congr rfl
            intro q3 hq3
            have hsum := sum_divisors_eq_if_dvd
              (fun k => mtPrimeBlockAF S1 k) (n := n) (d := q2 * q3) hnPos
            by_cases hdvd : q2 * q3 ∣ n
            · have hquotPos : 0 < n / (q2 * q3) :=
                Nat.div_pos (Nat.le_of_dvd hnPos hdvd)
                  (Nat.mul_pos (hpos2 q2 hq2) (hpos3 q3 hq3))
              rw [mtPrimeBlockAF_apply_of_pos S1 hquotPos] at hsum
              simpa [hdvd] using hsum.symm
            · rw [if_neg hdvd]
              rw [if_neg hdvd] at hsum
              exact hsum.symm
          _ = ∑ q2 ∈ S2, ∑ m ∈ n.divisors, ∑ q3 ∈ S3,
              if q2 * q3 = m then mtPrimeBlockAF S1 (n / m) else 0 := by
            apply Finset.sum_congr rfl
            intro q2 hq2
            rw [Finset.sum_comm]
          _ = ∑ m ∈ n.divisors, ∑ q2 ∈ S2, ∑ q3 ∈ S3,
              if q2 * q3 = m then mtPrimeBlockAF S1 (n / m) else 0 :=
            Finset.sum_comm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro q2 hq2
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro q3 hq3
            split_ifs <;> simp
      _ = ∑ m ∈ n.divisors,
        mtCoefficientAF (mtHarmanPairCellCoefficient S2 S3) m *
          mtPrimeBlockAF S1 (n / m) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmPos : 0 < m := Nat.pos_of_mem_divisors hm
        rw [mtCoefficientAF_apply_of_pos _ hmPos,
          mtHarmanPairCellCoefficient_eq_source_sum]

end

end RHTower.Sieve

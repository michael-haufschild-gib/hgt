import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanAggregateCoefficients
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAlignedSchedule

/-!
# Base and one-prime Harman source coefficients

The first two Harman terms are one sifted divisor sum with a zero-one signed coefficient.  The
prime-window part also splits exactly across the independent outer aligned schedule.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

def mtUnitCoefficient (n : ℕ) : ℂ := if n = 1 then 1 else 0

def mtFinsetIndicatorCoefficient (S : Finset ℕ) (n : ℕ) : ℂ :=
  if n ∈ S then 1 else 0

def mtHarmanBaseOneCoefficient (P : Finset ℕ) (n : ℕ) : ℂ :=
  mtUnitCoefficient n - mtFinsetIndicatorCoefficient P n

theorem norm_mtUnitCoefficient_le_one (n : ℕ) : ‖mtUnitCoefficient n‖ ≤ 1 := by
  unfold mtUnitCoefficient
  split <;> simp

theorem norm_mtFinsetIndicatorCoefficient_le_one (S : Finset ℕ) (n : ℕ) :
    ‖mtFinsetIndicatorCoefficient S n‖ ≤ 1 := by
  unfold mtFinsetIndicatorCoefficient
  split <;> simp

theorem norm_mtHarmanBaseOneCoefficient_le_one
    {P : Finset ℕ} (hone : 1 ∉ P) (n : ℕ) :
    ‖mtHarmanBaseOneCoefficient P n‖ ≤ 1 := by
  unfold mtHarmanBaseOneCoefficient mtUnitCoefficient mtFinsetIndicatorCoefficient
  by_cases hn : n = 1
  · subst n
    simp [hone]
  · by_cases hnP : n ∈ P <;> simp [hn, hnP]

theorem one_not_mem_primesIco (z Q : ℕ) : 1 ∉ primesIco z Q := by
  intro h
  exact (mem_primesIco.mp h).2.2.ne_one rfl

theorem mtUnitCoefficient_polynomialDivisorBounded :
    MTPolynomialDivisorBounded mtUnitCoefficient := by
  refine ⟨1, by norm_num, 0, ?_⟩
  intro n hn
  simpa using norm_mtUnitCoefficient_le_one n

theorem mtFinsetIndicatorCoefficient_polynomialDivisorBounded (S : Finset ℕ) :
    MTPolynomialDivisorBounded (mtFinsetIndicatorCoefficient S) := by
  refine ⟨1, by norm_num, 0, ?_⟩
  intro n hn
  simpa using norm_mtFinsetIndicatorCoefficient_le_one S n

theorem mtHarmanBaseOneCoefficient_polynomialDivisorBounded
    {P : Finset ℕ} (hone : 1 ∉ P) :
    MTPolynomialDivisorBounded (mtHarmanBaseOneCoefficient P) := by
  refine ⟨1, by norm_num, 0, ?_⟩
  intro n hn
  simpa using norm_mtHarmanBaseOneCoefficient_le_one hone n

theorem mtDivisorSiftSum_unitCoefficient_eq_rho
    (z : ℕ) {n : ℕ} (hn : 0 < n) :
    mtDivisorSiftSum mtUnitCoefficient z n = (rho n z : ℂ) := by
  unfold mtDivisorSiftSum
  simpa [mtUnitCoefficient, eq_comm] using
    (sum_divisors_eq_if_dvd (fun k => (rho k z : ℂ))
      (n := n) (d := 1) hn)

theorem mtDivisorSiftSum_finsetIndicator_eq_harmanS1
    (z Q : ℕ) {n : ℕ} (hn : 0 < n) :
    mtDivisorSiftSum
        (mtFinsetIndicatorCoefficient (primesIco z Q)) z n =
      (harmanS1 z Q n : ℂ) := by
  let P := primesIco z Q
  calc
    mtDivisorSiftSum (mtFinsetIndicatorCoefficient P) z n =
        ∑ q ∈ n.divisors,
          if q ∈ P then (rho (n / q) z : ℂ) else 0 := by
      unfold mtDivisorSiftSum mtFinsetIndicatorCoefficient
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs <;> simp
    _ = ∑ q ∈ P, if q ∣ n then (rho (n / q) z : ℂ) else 0 :=
      sum_divisors_indicator_eq_sum_finset_dvd hn P _
    _ = (harmanS1 z Q n : ℂ) := by
      unfold harmanS1
      rw [primeWindow_eq_primesIco_filter_dvd, Finset.sum_filter]
      push_cast
      rfl

theorem mtDivisorSiftSum_baseOneCoefficient_eq
    (z Q : ℕ) {n : ℕ} (hn : 0 < n) :
    mtDivisorSiftSum
        (mtHarmanBaseOneCoefficient (primesIco z Q)) z n =
      (rho n z : ℂ) - (harmanS1 z Q n : ℂ) := by
  rw [← mtDivisorSiftSum_unitCoefficient_eq_rho z hn,
    ← mtDivisorSiftSum_finsetIndicator_eq_harmanS1 z Q hn]
  unfold mtDivisorSiftSum mtHarmanBaseOneCoefficient
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- A source subset of one complete adjacent interval splits into exactly one block per member. -/
theorem mtFinsetIndicatorCoefficient_eq_sum_sourceBlocks
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    {P : Finset ℕ} (hP : P ⊆ primesIco (endpoint 0) (endpoint t)) (n : ℕ) :
    mtFinsetIndicatorCoefficient P n =
      ∑ i : Fin t,
        mtFinsetIndicatorCoefficient (mtHarmanSourceBlock endpoint P i) n := by
  classical
  by_cases hnP : n ∈ P
  · have hnFull := hP hnP
    obtain ⟨i, hni⟩ := exists_mem_mtAdjacentPrimeBlock_of_mem_primesIco hmono hnFull
    have hniSource : n ∈ mtHarmanSourceBlock endpoint P i :=
      Finset.mem_inter.mpr ⟨hni, hnP⟩
    rw [mtFinsetIndicatorCoefficient, if_pos hnP, Finset.sum_eq_single i]
    · simp [mtFinsetIndicatorCoefficient, hniSource]
    · intro j hj hji
      have hnNot : n ∉ mtHarmanSourceBlock endpoint P j := by
        intro hnj
        have hnjBlock := (Finset.mem_inter.mp hnj).1
        exact (Finset.disjoint_left.mp
          (mtAdjacentPrimeBlock_disjoint endpoint hmono i j (Ne.symm hji))) hni hnjBlock
      simp [mtFinsetIndicatorCoefficient, hnNot]
    · simp
  · rw [mtFinsetIndicatorCoefficient, if_neg hnP]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hnNot : n ∉ mtHarmanSourceBlock endpoint P i := by
      intro hni
      exact hnP (Finset.mem_inter.mp hni).2
    simp [mtFinsetIndicatorCoefficient, hnNot]

/-- Literal `[z,Q)` source partition on a padded aligned outer schedule beginning at `outerStart`. -/
theorem mtFinsetIndicatorCoefficient_primesIco_eq_sum_paperAlignedSourceBlocks
    {outerStart z Q : ℕ} {delta : ℝ}
    (houterStart : 1 ≤ outerStart) (houterZ : outerStart ≤ z) (hzQ : z ≤ Q)
    (hdelta : 0 ≤ delta)
    (hprogress : 1 ≤ delta * ((outerStart - 1 : ℕ) : ℝ)) (n : ℕ) :
    mtFinsetIndicatorCoefficient (primesIco z Q) n =
      ∑ i : Fin (Q - outerStart),
        mtFinsetIndicatorCoefficient
          (mtHarmanSourceBlock (mtPaperAlignedEndpoint outerStart Q delta)
            (primesIco z Q) i) n := by
  apply mtFinsetIndicatorCoefficient_eq_sum_sourceBlocks
    (mtPaperAlignedEndpoint_monotone houterStart (houterZ.trans hzQ)
      hdelta hprogress)
  intro p hp
  have hp' := mem_primesIco.mp hp
  rw [mtPaperAlignedEndpoint_zero,
    mtPaperAlignedEndpoint_sub_eq houterStart (houterZ.trans hzQ) hdelta hprogress]
  exact mem_primesIco.mpr ⟨houterZ.trans hp'.1, hp'.2⟩

end

end RHTower.Sieve

import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheDeficitOfThePrimeFormIsADirichletEnergy

/-!
# Localization of the prime defect at a macroscopic cutoff

Prime edges crossing a fixed multiplicative interval have bounded outgoing
Mertens mass. Reindexing by their upper endpoints therefore controls the
logarithmic tail mass by the full defect without a factor equal to the
horizon-to-cutoff ratio. The same edges compare the full defect with the
retained low block and its logarithmically weighted tail.
-/

noncomputable section

set_option autoImplicit false

open Finset
open scoped Chebyshev

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction

/-- Uniform outgoing prime-edge cost between two integer cutoffs. -/
def cutoffPrimeCost (M N : ℕ) : ℝ :=
  Real.log N - Real.log M + (Real.log 4 + 4) + (Real.log 8 + 4)

/-- The whole interval of outgoing prime powers costs only its logarithmic length. -/
theorem mertens_quotient_difference_le {M N m : ℕ} (hM : 1 ≤ M)
    (hm : 1 ≤ m) (hmN : m ≤ N) :
    mertensSum (N / m) - mertensSum (M / m) ≤ cutoffPrimeCost M N := by
  have hupper := row_le hm hmN
  by_cases hmM : m ≤ M
  · have hlower := row_ge hm hmM
    unfold cutoffPrimeCost
    linarith only [hupper, hlower]
  · have hzero : mertensSum (M / m) = 0 := by
      rw [Nat.div_eq_of_lt (lt_of_not_ge hmM)]
      simp only [mertensSum, Icc_eq_empty_of_lt (by omega : 0 < 1), sum_empty]
    have hlog : Real.log M ≤ Real.log m :=
      Real.log_le_log (by exact_mod_cast hM) (by exact_mod_cast (lt_of_not_ge hmM).le)
    have hlog8 := Real.log_nonneg (show (1 : ℝ) ≤ 8 by norm_num)
    rw [hzero, sub_zero]
    unfold cutoffPrimeCost
    linarith only [hupper, hlog, hlog8]

/-- The logarithmic coefficient mass above a cutoff. -/
def logarithmicTailMass (M N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, if M < n then Real.log n * x n ^ 2 else 0

private theorem sum_Icc_tail {M N : ℕ} (hMN : M ≤ N) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, if M < n then f n else 0) =
      (∑ n ∈ Icc 1 N, f n) - ∑ n ∈ Icc 1 M, f n := by
  have hfilter : (Icc 1 N).filter (fun n => n ≤ M) = Icc 1 M := by
    ext n
    simp only [mem_filter, mem_Icc]
    omega
  have hlow : (∑ n ∈ Icc 1 N, if n ≤ M then f n else 0) =
      ∑ n ∈ Icc 1 M, f n := by rw [← sum_filter, hfilter]
  have hsplit : (∑ n ∈ Icc 1 N, if M < n then f n else 0) +
      (∑ n ∈ Icc 1 N, if n ≤ M then f n else 0) = ∑ n ∈ Icc 1 N, f n := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    by_cases h : M < n
    · rw [if_pos h, if_neg (not_le.mpr h), add_zero]
    · rw [if_neg h, if_pos (le_of_not_gt h), zero_add]
  rw [hlow] at hsplit
  linarith only [hsplit]

private theorem outgoing_cutoff_row {M N m : ℕ} (hMN : M ≤ N)
    (hm : 1 ≤ m) (x : ℕ → ℝ) :
    (∑ t ∈ Icc 1 (N / m), if M < m * t then
      Λ t * (x m / Real.sqrt t) ^ 2 else 0) =
      (mertensSum (N / m) - mertensSum (M / m)) * x m ^ 2 := by
  calc
    _ = (∑ t ∈ Icc 1 (N / m), if M / m < t then Λ t / t else 0) * x m ^ 2 := by
      rw [sum_mul]
      refine sum_congr rfl fun t _ => ?_
      have hiff : M / m < t ↔ M < m * t := by
        simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hm : M / m < t ↔ M < t * m)
      by_cases h : M / m < t
      · rw [if_pos h, if_pos (hiff.mp h), div_pow, Real.sq_sqrt (Nat.cast_nonneg t)]
        ring
      · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h')), zero_mul]
    _ = _ := by rw [sum_Icc_tail (Nat.div_le_div_right hMN)]; rfl

/-- Outgoing tail edges cost only the logarithmic size of the cutoff interval. -/
theorem outgoing_cutoff_edges_le {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N)
    (x : ℕ → ℝ) :
    (∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), if M < m * t then
      Λ t * (x m / Real.sqrt t) ^ 2 else 0) ≤
      cutoffPrimeCost M N * ∑ m ∈ Icc 1 N, x m ^ 2 := by
  rw [mul_sum]
  refine sum_le_sum fun m hm => ?_
  obtain ⟨hm1, hmN⟩ := mem_Icc.mp hm
  rw [outgoing_cutoff_row hMN hm1]
  exact mul_le_mul_of_nonneg_right (mertens_quotient_difference_le hM hm1 hmN) (sq_nonneg _)

/-- Reindexing incoming tail edges gives their exact logarithmic mass. -/
theorem logarithmicTailMass_eq_edges (M N : ℕ) (x : ℕ → ℝ) :
    logarithmicTailMass M N x =
      ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m),
        if M < m * t then Λ t * x (m * t) ^ 2 else 0 := by
  rw [sum_edges_eq_sum_divisors N (fun n t => if M < n then Λ t * x n ^ 2 else 0)]
  unfold logarithmicTailMass
  refine sum_congr rfl fun n _ => ?_
  by_cases h : M < n
  · simp only [if_pos h, ← sum_mul, vonMangoldt_sum]
  · simp only [if_neg h, sum_const_zero]

private theorem square_le_defect_young (a b : ℝ) {u : ℝ} (hu : 0 < u) :
    a ^ 2 ≤ (1 + 1 / u) * (a - b) ^ 2 + (1 + u) * b ^ 2 := by
  calc
    a ^ 2 ≤ a ^ 2 + ((a - b) - u * b) ^ 2 / u :=
      le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hu.le)
    _ = _ := by field_simp; ring

/-- The full defect pays the logarithmic tail with arbitrarily near-unit coefficient.
The remainder grows only with the logarithmic cutoff ratio. -/
theorem logarithmicTailMass_le_poleDefect {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N)
    (x : ℕ → ℝ) {u : ℝ} (hu : 0 < u) :
    logarithmicTailMass M N x ≤ (1 + 1 / u) * poleDefect N x +
      (1 + u) * cutoffPrimeCost M N * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hpoint : ∀ m ∈ Icc 1 N, ∀ t ∈ Icc 1 (N / m),
      (if M < m * t then Λ t * x (m * t) ^ 2 else 0) ≤
        (1 + 1 / u) * (Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2) +
          (1 + u) * (if M < m * t then Λ t * (x m / Real.sqrt t) ^ 2 else 0) := by
    intro m _ t _
    by_cases h : M < m * t
    · rw [if_pos h, if_pos h]
      have hy := mul_le_mul_of_nonneg_left
        (square_le_defect_young (x (m * t)) (x m / Real.sqrt t) hu)
        (vonMangoldt_nonneg (n := t))
      calc
        _ ≤ Λ t * ((1 + 1 / u) * (x (m * t) - x m / Real.sqrt t) ^ 2 +
          (1 + u) * (x m / Real.sqrt t) ^ 2) := hy
        _ = _ := by ring
    · rw [if_neg h, if_neg h, mul_zero, add_zero]
      exact mul_nonneg (by positivity)
        (mul_nonneg vonMangoldt_nonneg (sq_nonneg _))
  have hsum := sum_le_sum fun m hm => sum_le_sum fun t ht => hpoint m hm t ht
  simp only [sum_add_distrib, ← mul_sum] at hsum
  rw [← logarithmicTailMass_eq_edges, ← poleDefect] at hsum
  have hout := mul_le_mul_of_nonneg_left (outgoing_cutoff_edges_le hM hMN x)
    (show 0 ≤ 1 + u by positivity)
  linarith only [hsum, hout]

/-- The same defect, indexed by the upper endpoint of each prime-power edge. -/
theorem poleDefect_eq_divisor_sum (N : ℕ) (x : ℕ → ℝ) :
    poleDefect N x = ∑ n ∈ Icc 1 N, ∑ t ∈ n.divisors,
      Λ t * (x n - x (n / t) / Real.sqrt t) ^ 2 := by
  unfold poleDefect
  calc
    _ = ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m),
        Λ t * (x (m * t) - x (m * t / t) / Real.sqrt t) ^ 2 := by
      refine sum_congr rfl fun m _ => sum_congr rfl fun t ht => ?_
      rw [Nat.mul_div_cancel m (mem_Icc.mp ht).1]
    _ = _ := sum_edges_eq_sum_divisors N
      (fun n t => Λ t * (x n - x (n / t) / Real.sqrt t) ^ 2)

/-- Cutting the horizon removes exactly the edges whose upper endpoints cross the cutoff. -/
theorem poleDefect_eq_cutoff_add_tail {M N : ℕ} (hMN : M ≤ N) (x : ℕ → ℝ) :
    poleDefect N x = poleDefect M x +
      ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), if M < m * t then
        Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2 else 0 := by
  have hedge : (∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), if M < m * t then
      Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2 else 0) =
      ∑ n ∈ Icc 1 N, if M < n then
        ∑ t ∈ n.divisors, Λ t * (x n - x (n / t) / Real.sqrt t) ^ 2 else 0 := by
    calc
      _ = ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), if M < m * t then
          Λ t * (x (m * t) - x (m * t / t) / Real.sqrt t) ^ 2 else 0 := by
        refine sum_congr rfl fun m _ => sum_congr rfl fun t ht => ?_
        rw [Nat.mul_div_cancel m (mem_Icc.mp ht).1]
      _ = ∑ n ∈ Icc 1 N, ∑ t ∈ n.divisors, if M < n then
          Λ t * (x n - x (n / t) / Real.sqrt t) ^ 2 else 0 :=
        sum_edges_eq_sum_divisors N
          (fun n t => if M < n then Λ t * (x n - x (n / t) / Real.sqrt t) ^ 2 else 0)
      _ = _ := by
        refine sum_congr rfl fun n _ => ?_
        by_cases h : M < n <;> simp only [h, if_true, if_false, sum_const_zero]
  rw [hedge, sum_Icc_tail hMN, ← poleDefect_eq_divisor_sum, ← poleDefect_eq_divisor_sum]
  ring

/-- A retained low block and its logarithmic tail control the full prime defect.
The coefficient-mass loss depends only on the logarithmic cutoff ratio. -/
theorem poleDefect_le_cutoff_add_logarithmicTail {M N : ℕ} (hM : 1 ≤ M)
    (hMN : M ≤ N) (x : ℕ → ℝ) :
    poleDefect N x ≤ poleDefect M x + 2 * logarithmicTailMass M N x +
      2 * cutoffPrimeCost M N * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hpoint : ∀ m ∈ Icc 1 N, ∀ t ∈ Icc 1 (N / m),
      (if M < m * t then Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2 else 0) ≤
        2 * (if M < m * t then Λ t * x (m * t) ^ 2 else 0) +
          2 * (if M < m * t then Λ t * (x m / Real.sqrt t) ^ 2 else 0) := by
    intro m _ t _
    by_cases h : M < m * t
    · simp only [if_pos h]
      have hs : (x (m * t) - x m / Real.sqrt t) ^ 2 ≤
          2 * x (m * t) ^ 2 + 2 * (x m / Real.sqrt t) ^ 2 := by
        nlinarith only [sq_nonneg (x (m * t) + x m / Real.sqrt t)]
      have hw := mul_le_mul_of_nonneg_left hs (vonMangoldt_nonneg (n := t))
      calc
        _ ≤ Λ t * (2 * x (m * t) ^ 2 + 2 * (x m / Real.sqrt t) ^ 2) := hw
        _ = _ := by ring
    · simp only [if_neg h, mul_zero, add_zero, le_refl]
  have hsum := sum_le_sum fun m hm => sum_le_sum fun t ht => hpoint m hm t ht
  simp only [sum_add_distrib, ← mul_sum] at hsum
  rw [← logarithmicTailMass_eq_edges] at hsum
  have hsplit := poleDefect_eq_cutoff_add_tail hMN x
  have hout := outgoing_cutoff_edges_le hM hMN x
  linarith only [hsum, hsplit, hout]

#print axioms logarithmicTailMass_le_poleDefect
#print axioms poleDefect_le_cutoff_add_logarithmicTail

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

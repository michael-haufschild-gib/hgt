import GaloisForLFunctions.HyperbolicArakelovTheory.TheSuspensionOfThePrimeGreenKernel
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# An arithmetic mass clock for the prime Green channels

Fill successive prime capacities to a prescribed real mass. The final prime
may carry a fractional weight. Every bounded mass uses finitely many primes,
and each fixed prime eventually has weight one. The construction depends on
the prime Green kernels alone, independently of the packet.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators Topology

namespace GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension

theorem capacity_pos {p : ℕ} (hp : p.Prime) : 0 < capacity p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hs : 1 < Real.sqrt p := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hp1
  exact div_pos (mul_pos (by norm_num) (Real.log_pos hp1)) (sub_pos.mpr hs)

/-- Zero capacities at nonprimes let the mass clock use the natural ordering. -/
def primeCapacity (n : ℕ) : ℝ := if n.Prime then capacity n else 0

theorem primeCapacity_nonneg (n : ℕ) : 0 ≤ primeCapacity n := by
  by_cases hn : n.Prime
  · simpa only [primeCapacity, if_pos hn] using (capacity_pos hn).le
  · simp only [primeCapacity, if_neg hn, le_refl]

/-- Total capacity of the primes strictly below the cutoff. -/
def cumulativeCapacity (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, primeCapacity n

@[simp] theorem cumulativeCapacity_zero : cumulativeCapacity 0 = 0 := by
  simp only [cumulativeCapacity, Finset.range_zero, Finset.sum_empty]

theorem cumulativeCapacity_succ (N : ℕ) :
    cumulativeCapacity (N + 1) = cumulativeCapacity N + primeCapacity N :=
  Finset.sum_range_succ _ _

theorem cumulativeCapacity_nonneg (N : ℕ) : 0 ≤ cumulativeCapacity N :=
  Finset.sum_nonneg (fun n _ => primeCapacity_nonneg n)

theorem cumulativeCapacity_mono : Monotone cumulativeCapacity := by
  apply monotone_nat_of_le_succ
  intro N
  rw [cumulativeCapacity_succ]
  exact le_add_of_nonneg_right (primeCapacity_nonneg N)

private theorem capacity_lower {p : ℕ} (hp : p.Prime) :
    2 * Real.log 2 / p ≤ capacity p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp1
  have hs : 1 < Real.sqrt p := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hp1
  have hsle : Real.sqrt p - 1 ≤ p := by
    nlinarith only [Real.sq_sqrt hp0.le, sq_nonneg (Real.sqrt p - 1), hp1]
  have hl : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  have hl0 : 0 ≤ 2 * Real.log 2 := mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  rw [capacity, div_le_div_iff₀ hp0 (sub_pos.mpr hs)]
  calc
    2 * Real.log 2 * (Real.sqrt p - 1) ≤ 2 * Real.log 2 * p :=
      mul_le_mul_of_nonneg_left hsle hl0
    _ ≤ 2 * Real.log p * p :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by norm_num)) hp0.le

theorem primeCapacity_not_summable : ¬ Summable primeCapacity := by
  intro h
  have hC : 0 < 2 * Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  apply Nat.Primes.not_summable_one_div
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _
    ((h.subtype Nat.Prime).div_const (2 * Real.log 2))
  intro p
  change 1 / (p.1 : ℝ) ≤ primeCapacity p.1 / (2 * Real.log 2)
  rw [primeCapacity, if_pos p.2]
  apply (le_div_iff₀ hC).mpr
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using capacity_lower p.2

/-- Euler's prime reciprocal divergence makes every finite mass attainable. -/
theorem tendsto_cumulativeCapacity_atTop : Tendsto cumulativeCapacity atTop atTop :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg primeCapacity_nonneg).mp
    primeCapacity_not_summable

/-- The capacity assigned to a prime by filling the ordered spectrum up to `S`. -/
def filledCapacity (S : ℝ) (n : ℕ) : ℝ :=
  min S (cumulativeCapacity (n + 1)) - min S (cumulativeCapacity n)

theorem filledCapacity_nonneg (S : ℝ) (n : ℕ) : 0 ≤ filledCapacity S n :=
  sub_nonneg.mpr (min_le_min_left S (cumulativeCapacity_mono (Nat.le_succ n)))

theorem filledCapacity_le (S : ℝ) (n : ℕ) :
    filledCapacity S n ≤ primeCapacity n := by
  rw [filledCapacity, cumulativeCapacity_succ]
  have hc := primeCapacity_nonneg n
  rcases le_total S (cumulativeCapacity n) with h | h
  · rw [min_eq_left h, min_eq_left (h.trans (le_add_of_nonneg_right hc)), sub_self]
    exact hc
  · rw [min_eq_right h]
    apply sub_le_iff_le_add.mpr
    simpa only [add_comm] using min_le_right S (cumulativeCapacity n + primeCapacity n)

theorem filledCapacity_eq_zero {S : ℝ} {N n : ℕ}
    (hS : S ≤ cumulativeCapacity N) (hn : N ≤ n) : filledCapacity S n = 0 := by
  have hSn := hS.trans (cumulativeCapacity_mono hn)
  rw [filledCapacity, min_eq_left (hSn.trans (cumulativeCapacity_mono (Nat.le_succ n))),
    min_eq_left hSn, sub_self]

theorem filledCapacity_eq_full {S : ℝ} {n : ℕ}
    (hS : cumulativeCapacity (n + 1) ≤ S) : filledCapacity S n = primeCapacity n := by
  have hnS := (cumulativeCapacity_mono (Nat.le_succ n)).trans hS
  rw [filledCapacity, min_eq_right hS, min_eq_right hnS, cumulativeCapacity_succ,
    add_sub_cancel_left]

/-- Exact mass conservation, including the fractional terminal prime. -/
theorem sum_filledCapacity (S : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, filledCapacity S n) =
      min S (cumulativeCapacity N) - min S 0 := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, cumulativeCapacity_zero, sub_self]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, filledCapacity]
    ring

/-- The dimensionless weight of each translated prime Green channel. -/
def clockWeight (S : ℝ) (n : ℕ) : ℝ := filledCapacity S n / primeCapacity n

theorem clockWeight_nonneg (S : ℝ) (n : ℕ) : 0 ≤ clockWeight S n :=
  div_nonneg (filledCapacity_nonneg S n) (primeCapacity_nonneg n)

theorem clockWeight_le_one (S : ℝ) (n : ℕ) : clockWeight S n ≤ 1 := by
  by_cases hn : n.Prime
  · apply (div_le_one (by simpa only [primeCapacity, if_pos hn] using capacity_pos hn)).mpr
    exact filledCapacity_le S n
  · simp only [clockWeight, primeCapacity, if_neg hn, div_zero, zero_le_one]

theorem clockWeight_mul_capacity (S : ℝ) (n : ℕ) :
    clockWeight S n * primeCapacity n = filledCapacity S n := by
  by_cases hn : n.Prime
  · exact div_mul_cancel₀ _ (by simpa only [primeCapacity, if_pos hn]
      using (capacity_pos hn).ne')
  · have hz : filledCapacity S n = 0 := le_antisymm
      (by simpa only [primeCapacity, if_neg hn] using filledCapacity_le S n)
      (filledCapacity_nonneg S n)
    simp only [clockWeight, hz, zero_div, zero_mul]

theorem clockWeight_eq_one {S : ℝ} {p : ℕ} (hp : p.Prime)
    (hS : cumulativeCapacity (p + 1) ≤ S) : clockWeight S p = 1 := by
  rw [clockWeight, filledCapacity_eq_full hS, div_self]
  simpa only [primeCapacity, if_pos hp] using (capacity_pos hp).ne'

theorem clockWeight_finite_support (S : ℝ) :
    (Function.support (clockWeight S)).Finite := by
  obtain ⟨N, hN⟩ :=
    (tendsto_cumulativeCapacity_atTop.eventually (eventually_ge_atTop S)).exists
  apply (Finset.finite_toSet (Finset.range N)).subset
  intro n hn
  by_contra hmem
  have hnN : N ≤ n := by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hmem
  exact hn (by rw [clockWeight, filledCapacity_eq_zero hN hnN, zero_div])

/-- A fixed prime is fully present once the clock passes its cumulative capacity. -/
theorem eventually_clockWeight_eq_one {p : ℕ} (hp : p.Prime) :
    ∀ᶠ S in atTop, clockWeight S p = 1 := by
  filter_upwards [eventually_ge_atTop (cumulativeCapacity (p + 1))] with S hS
  exact clockWeight_eq_one hp hS

/-- One normalization attains the prescribed mass exactly and has finite support. -/
theorem clockWeight_total {S : ℝ} (hS : 0 ≤ S) :
    (∑ᶠ n, clockWeight S n * primeCapacity n) = S := by
  obtain ⟨N, hN⟩ :=
    (tendsto_cumulativeCapacity_atTop.eventually (eventually_ge_atTop S)).exists
  have hs : Function.support (fun n => clockWeight S n * primeCapacity n) ⊆
      (Finset.range N : Set ℕ) := by
    intro n hn
    by_contra hmem
    have hnN : N ≤ n := by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hmem
    exact hn (by
      change clockWeight S n * primeCapacity n = 0
      rw [clockWeight_mul_capacity, filledCapacity_eq_zero hN hnN])
  rw [finsum_eq_sum_of_support_subset _ hs]
  simp_rw [clockWeight_mul_capacity]
  rw [sum_filledCapacity, min_eq_left hN, min_eq_right hS, sub_zero]

#print axioms tendsto_cumulativeCapacity_atTop
#print axioms clockWeight_finite_support
#print axioms clockWeight_total

end GaloisForLFunctions.HyperbolicArakelovTheory.PrimeSuspension

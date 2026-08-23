import GaloisForLFunctions.RHTower.MertensPrimeWindowWeakConvergence
import GaloisForLFunctions.RHTower.WeightedEulerCoefficientSpaces

/-!
# Mertens mass in a square-root prime window

The explicit Mertens error bound forces at least half a logarithm of
prime-log mass between `sqrt N` and `N`, up to a fixed error.  This is the
finite lower-window infrastructure used by left-of-critical-line Euler
coefficient obstructions.
-/

noncomputable section

namespace RHTower

open Finset Filter Topology

/-- Prime-log mass in the finite interval from `sqrt N` to `N`, written as a
difference of cumulative Mertens masses. -/
def mertensPrimeSqrtWindow (N : ℕ) : ℝ :=
  mertensPrimeWeightSum N - mertensPrimeWeightSum ⌊Real.sqrt (N : ℝ)⌋₊

/-- The square-root prime window has half the ambient logarithmic mass, up to
the explicit two-sided Mertens error. -/
theorem le_mertensPrimeSqrtWindow (N : ℕ) (hN : 4 ≤ N) :
    Real.log N / 2 - (2 * mertensPrimeWindowBound + 1) ≤ mertensPrimeSqrtWindow N := by
  have hsqrt : (2 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      (by exact_mod_cast Nat.zero_le N)).2
    norm_num
    exact hN
  have hlow := (abs_le.mp (abs_mertensPrimeWeightSum_sub_log_le N (by omega))).1
  have hupp := (abs_le.mp (abs_mertensPrimeWeightSum_floor_sub_log_le hsqrt)).2
  rw [Real.log_sqrt (by exact_mod_cast Nat.zero_le N)] at hupp
  unfold mertensPrimeSqrtWindow
  linarith

/-- A nonnegative prime power dominates the square-root-window mass by its
value at the lower endpoint. -/
theorem primeLogMass_rpow_lower_mertensPrimeSqrtWindow {δ : ℝ} (hδ : 0 ≤ δ)
    (N : ℕ) (hN : 4 ≤ N) :
    (Real.sqrt (N : ℝ)) ^ δ * mertensPrimeSqrtWindow N ≤
      primeLogMass (fun n => (n : ℝ) ^ δ) N := by
  set Q : ℕ := ⌊Real.sqrt (N : ℝ)⌋₊ with hQ
  have hN1 : 1 ≤ N := by omega
  have hsqrtle : Real.sqrt (N : ℝ) ≤ N := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact_mod_cast Nat.zero_le N
    · have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      nlinarith
  have hQN : Q ≤ N := by
    have hQNreal : (Q : ℝ) ≤ N := by
      rw [hQ]
      exact le_trans (Nat.floor_le (Real.sqrt_nonneg _)) hsqrtle
    exact_mod_cast hQNreal
  have hwindow :
      mertensPrimeSqrtWindow N = primeLogMass (primeCoefficientTail (fun _ => (1 : ℝ)) Q) N := by
    change mertensPrimeWeightSum N - mertensPrimeWeightSum Q = _
    rw [primeLogMass_tail_eq_sub _ hQN, primeLogMass_unit N, primeLogMass_unit Q,
      ← mertensPrimeWeightSum_eq N, ← mertensPrimeWeightSum_eq Q]
  rw [hwindow, primeLogMass_tail, primeLogMass, Finset.mul_sum]
  calc
    ∑ n ∈ Finset.Icc 1 N with (n.Prime ∧ Q < n),
        (Real.sqrt (N : ℝ)) ^ δ * (Real.log n / n * |(1 : ℝ)|)
      ≤ ∑ n ∈ Finset.Icc 1 N with (n.Prime ∧ Q < n),
          Real.log n / n * |(n : ℝ) ^ δ| := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_filter] at hn
        have hnroot : Real.sqrt (N : ℝ) < n := by
          exact (Nat.floor_lt (Real.sqrt_nonneg _)).mp hn.2.2
        have hpow : (Real.sqrt (N : ℝ)) ^ δ ≤ (n : ℝ) ^ δ :=
          Real.rpow_le_rpow (Real.sqrt_nonneg _) hnroot.le hδ
        have hweight : 0 ≤ Real.log n / n :=
          div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)
        rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
        simp only [abs_one]
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_right hpow hweight
    _ ≤ ∑ n ∈ Finset.Icc 1 N with n.Prime, Real.log n / n * |(n : ℝ) ^ δ| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [Finset.mem_filter] at hn ⊢
          exact ⟨hn.1, hn.2.1⟩
        · intro n _ _
          exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n))
            (abs_nonneg _)

end RHTower

end

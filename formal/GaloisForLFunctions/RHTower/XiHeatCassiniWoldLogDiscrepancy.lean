import GaloisForLFunctions.RHTower.XiHeatCassiniWoldHalfDensityTraceReduction
import GaloisForLFunctions.RHTower.MertensPrimeWindowWeakConvergence

/-!
# Bounded logarithmic discrepancy of the pure Wold producer

The depth-one Wold measure differs from the Mertens logarithmic prime measure by the positive
finite Euler-depletion measure isolated in the half-density trace reduction.  Hence its cumulative
mass differs from Lebesgue logarithmic mass by a uniformly bounded amount.  This identifies the
remaining Route-T source as a bounded-discrepancy logarithmic quadrature, not a coefficient-growth
problem.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Depth-one Wold weight on natural numbers, extended by zero away from primes. -/
def xiHeatCassiniWoldNatWeight (n : ℕ) : ℝ :=
  if hn : n.Prime then woldCoeff 1 ⟨n, hn⟩ else 0

/-- Positive Euler-depletion correction on natural numbers. -/
def xiHeatCassiniWoldNatTraceCorrection (n : ℕ) : ℝ :=
  if hn : n.Prime then xiHeatCassiniWoldEulerTraceCorrection ⟨n, hn⟩ else 0

/-- Cumulative Wold logarithmic mass up to a natural cutoff. -/
def xiHeatCassiniWoldNatWeightSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 N, xiHeatCassiniWoldNatWeight n

/-- Cumulative finite Euler correction up to a natural cutoff. -/
def xiHeatCassiniWoldNatTraceCorrectionSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 N, xiHeatCassiniWoldNatTraceCorrection n

/-- Natural Wold weight plus trace correction is exactly the Mertens prime weight. -/
theorem xiHeatCassiniWoldNatWeight_add_traceCorrection
    (n : ℕ) :
    xiHeatCassiniWoldNatWeight n +
      xiHeatCassiniWoldNatTraceCorrection n = mertensPrimeWeight n := by
  by_cases hn : n.Prime
  · simp only [xiHeatCassiniWoldNatWeight,
      xiHeatCassiniWoldNatTraceCorrection, dif_pos hn,
      mertensPrimeWeight, if_pos hn]
    rw [xiHeatCassiniWoldEulerTraceCorrection,
      xiMassPrimeHarmonicRealCoefficient]
    ring
  · simp [xiHeatCassiniWoldNatWeight,
      xiHeatCassiniWoldNatTraceCorrection, mertensPrimeWeight, hn]

/-- Cumulative Mertens mass splits into pure Wold mass and finite Euler correction. -/
theorem mertensPrimeWeightSum_eq_wold_add_traceCorrection (N : ℕ) :
    mertensPrimeWeightSum N =
      xiHeatCassiniWoldNatWeightSum N +
        xiHeatCassiniWoldNatTraceCorrectionSum N := by
  rw [mertensPrimeWeightSum, xiHeatCassiniWoldNatWeightSum,
    xiHeatCassiniWoldNatTraceCorrectionSum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n hn =>
    (xiHeatCassiniWoldNatWeight_add_traceCorrection n).symm

/-- Natural Euler correction is nonnegative. -/
theorem xiHeatCassiniWoldNatTraceCorrection_nonneg (n : ℕ) :
    0 ≤ xiHeatCassiniWoldNatTraceCorrection n := by
  unfold xiHeatCassiniWoldNatTraceCorrection
  split_ifs with hn
  · exact xiHeatCassiniWoldEulerTraceCorrection_nonneg ⟨n, hn⟩
  · exact le_rfl

/-- Natural Euler correction is summable. -/
theorem summable_xiHeatCassiniWoldNatTraceCorrection :
    Summable xiHeatCassiniWoldNatTraceCorrection := by
  have hmajor : Summable (fun n : ℕ =>
      3 * (|Real.log n| ^ 1 * (n : ℝ) ^ (-2 : ℝ))) :=
    (summable_abs_log_natCast_pow_mul_rpow_neg 1 2 (by norm_num)).mul_left 3
  apply hmajor.of_nonneg_of_le xiHeatCassiniWoldNatTraceCorrection_nonneg
  intro n
  by_cases hn : n.Prime
  · let p : Nat.Primes := ⟨n, hn⟩
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast hn.one_lt)
    have hle := xiHeatCassiniWoldEulerTraceCorrection_le p
    rw [xiHeatCassiniWoldNatTraceCorrection, dif_pos hn]
    calc
      xiHeatCassiniWoldEulerTraceCorrection p ≤
          3 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := hle
      _ = 3 * (|Real.log n| ^ 1 * (n : ℝ) ^ (-2 : ℝ)) := by
        dsimp only [p]
        rw [abs_of_pos hlog, pow_one,
          show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_neg (by positivity), Real.rpow_natCast,
          div_eq_mul_inv]
  · rw [xiHeatCassiniWoldNatTraceCorrection, dif_neg hn]
    positivity

/-- Total positive mass of the Euler-depletion correction. -/
def xiHeatCassiniWoldNatTraceCorrectionMass : ℝ :=
  ∑' n : ℕ, xiHeatCassiniWoldNatTraceCorrection n

/-- Every finite correction prefix is bounded by the complete correction mass. -/
theorem xiHeatCassiniWoldNatTraceCorrectionSum_le_mass (N : ℕ) :
    xiHeatCassiniWoldNatTraceCorrectionSum N ≤
      xiHeatCassiniWoldNatTraceCorrectionMass := by
  rw [xiHeatCassiniWoldNatTraceCorrectionSum,
    xiHeatCassiniWoldNatTraceCorrectionMass]
  exact summable_xiHeatCassiniWoldNatTraceCorrection.sum_le_tsum
    (Finset.Icc 0 N) (fun n hn => xiHeatCassiniWoldNatTraceCorrection_nonneg n)

/-- **Bounded Wold log-discrepancy law.** -/
theorem abs_xiHeatCassiniWoldNatWeightSum_sub_log_le
    (N : ℕ) (hN : 1 ≤ N) :
    |xiHeatCassiniWoldNatWeightSum N - Real.log N| ≤
      mertensPrimeWindowBound + xiHeatCassiniWoldNatTraceCorrectionMass := by
  have hMertens := abs_mertensPrimeWeightSum_sub_log_le N hN
  have hcorrection0 :
      0 ≤ xiHeatCassiniWoldNatTraceCorrectionSum N :=
    Finset.sum_nonneg fun n hn => xiHeatCassiniWoldNatTraceCorrection_nonneg n
  have hcorrection := xiHeatCassiniWoldNatTraceCorrectionSum_le_mass N
  rw [mertensPrimeWeightSum_eq_wold_add_traceCorrection] at hMertens
  calc
    |xiHeatCassiniWoldNatWeightSum N - Real.log N| =
        |(xiHeatCassiniWoldNatWeightSum N +
            xiHeatCassiniWoldNatTraceCorrectionSum N - Real.log N) -
          xiHeatCassiniWoldNatTraceCorrectionSum N| := by ring_nf
    _ ≤ |xiHeatCassiniWoldNatWeightSum N +
          xiHeatCassiniWoldNatTraceCorrectionSum N - Real.log N| +
        |xiHeatCassiniWoldNatTraceCorrectionSum N| := by
      simpa using abs_sub_le
        (xiHeatCassiniWoldNatWeightSum N +
          xiHeatCassiniWoldNatTraceCorrectionSum N - Real.log N)
        0 (xiHeatCassiniWoldNatTraceCorrectionSum N)
    _ ≤ mertensPrimeWindowBound + xiHeatCassiniWoldNatTraceCorrectionMass := by
      rw [abs_of_nonneg hcorrection0]
      exact add_le_add hMertens hcorrection

/-- The bounded discrepancy applies in particular at every ordered-prime logarithmic cutoff. -/
theorem abs_xiHeatCassiniWoldNatWeightSum_nthPrime_sub_log_le (N : ℕ) :
    |xiHeatCassiniWoldNatWeightSum (nthPrimeSubtype N : ℕ) -
        Real.log (nthPrimeSubtype N : ℝ)| ≤
      mertensPrimeWindowBound + xiHeatCassiniWoldNatTraceCorrectionMass := by
  exact abs_xiHeatCassiniWoldNatWeightSum_sub_log_le
    (nthPrimeSubtype N : ℕ) (nthPrimeSubtype N).2.one_le

end

end RHTower

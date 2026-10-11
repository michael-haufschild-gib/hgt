import GaloisForLFunctions.RHTower.WeilLogShiftRawConvexOrder
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Convex order gives unconditional even-moment, variance, and exponential-moment domination. -/

open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalRaw_even_moment_le (r k p : ℕ) :
    (∑ i, finiteWeilCanonicalEdgeMass r k i * (finiteWeilCanonicalRawCorrectionValue r k i) ^ (2 * p)) ≤
      ∑ i, finiteWeilCanonicalEdgeMass r k i * (finiteWeilCanonicalRawIndexValue r k i) ^ (2 * p) := by
  have hp : Even (2 * p) := ⟨p, by omega⟩
  have hc : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ (2 * p)) := hp.convexOn_pow
  exact finiteWeilCanonicalRaw_convex_sum_le r k ⟨_, hc⟩

theorem finiteWeilCanonicalRaw_variance_le (r k : ℕ) :
    ((r + 1 : ℕ) : ℝ) ^ 2 * finiteWeilCanonicalEdgeLogCorrectionVariance r k ≤
      finiteWeilCanonicalEdgeIndexVariance r k := by
  calc
    _ = ∑ i, finiteWeilCanonicalEdgeMass r k i * (finiteWeilCanonicalRawCorrectionValue r k i) ^ 2 := by
      unfold finiteWeilCanonicalEdgeLogCorrectionVariance finiteWeilCanonicalRawCorrectionValue
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, finiteWeilCanonicalEdgeMass r k i * (finiteWeilCanonicalRawIndexValue r k i) ^ 2 := by
      simpa only [Nat.mul_one] using finiteWeilCanonicalRaw_even_moment_le r k 1
    _ = _ := rfl

theorem finiteWeilCanonicalRaw_exponential_moment_le (r k : ℕ) (a : ℝ) :
    (∑ i, finiteWeilCanonicalEdgeMass r k i * Real.exp (a * finiteWeilCanonicalRawCorrectionValue r k i)) ≤
      ∑ i, finiteWeilCanonicalEdgeMass r k i * Real.exp (a * finiteWeilCanonicalRawIndexValue r k i) := by
  have hc := convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ a)
  change ConvexOn ℝ Set.univ (fun x : ℝ => Real.exp (a * x)) at hc
  exact finiteWeilCanonicalRaw_convex_sum_le r k ⟨_, hc⟩

end RHTower

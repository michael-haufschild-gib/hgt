/-
# Closed conductor-cutoff Dirichlet L zero-density boxes

This is the finite-conductor aggregation layer built from the literal vertical
zero boxes.  It sums every nonprincipal Dirichlet character at every concrete
modulus up to a fixed cutoff.  The constant is constructed from that finite
range inside Lean.  It is deliberately not described as the conductor-uniform
Chen--Gupta--Li density exponent needed by Bondarenko--Heap Proposition 2.

No RH, GRH, exceptional-zero, or zero-density premise is used.
-/
import GaloisForLFunctions.RHTower.DirichletLZeroDensityBox

open Complex Metric

noncomputable section

namespace RHTower

/-- Total literal vertical zero-box count over all nonprincipal character families at moduli
`1` through `Q`.  The index `n` represents the concrete modulus `n + 1`. -/
def completedLFunctionRangeZeroDensityBoxCount (Q : ℕ) (σ H : ℝ) : ℝ :=
  ∑ n ∈ Finset.range Q, completedLFunctionFamilyZeroDensityBoxCount n σ H

/-- Every finite conductor range has a closed literal vertical zero-box bound.  Its constant is
constructed by summing the already closed fixed-modulus constants.  The result is a finite-range
foundation, not the missing uniform density exponent. -/
theorem completedLFunction_range_zeroDensityBoxCount_growth
    (Q : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ σ H : ℝ,
      completedLFunctionRangeZeroDensityBoxCount Q σ H ≤
        C * (5 + |σ| + |H|) * Real.log (6 + |σ| + |H|) := by
  choose C hCpos hCbound using completedLFunction_family_zeroDensityBoxCount_growth
  have hCsum : 0 ≤ ∑ n ∈ Finset.range Q, C n :=
    Finset.sum_nonneg (fun n hn ↦ (hCpos n).le)
  refine ⟨1 + ∑ n ∈ Finset.range Q, C n, by linarith, ?_⟩
  intro σ H
  have hshape : 0 ≤ (5 + |σ| + |H|) * Real.log (6 + |σ| + |H|) := by
    apply mul_nonneg (by positivity)
    exact Real.log_nonneg (by linarith [abs_nonneg σ, abs_nonneg H])
  rw [completedLFunctionRangeZeroDensityBoxCount]
  calc
    _ ≤ ∑ n ∈ Finset.range Q,
        C n * (5 + |σ| + |H|) * Real.log (6 + |σ| + |H|) := by
      exact Finset.sum_le_sum (fun n hn ↦ hCbound n σ H)
    _ = (∑ n ∈ Finset.range Q, C n) *
        ((5 + |σ| + |H|) * Real.log (6 + |σ| + |H|)) := by
      simp_rw [mul_assoc]
      rw [Finset.sum_mul]
    _ ≤ (1 + ∑ n ∈ Finset.range Q, C n) *
        ((5 + |σ| + |H|) * Real.log (6 + |σ| + |H|)) := by
      nlinarith [mul_le_mul_of_nonneg_right (by linarith :
        (∑ n ∈ Finset.range Q, C n) ≤ 1 + ∑ n ∈ Finset.range Q, C n) hshape]
    _ = _ := by ring

end RHTower

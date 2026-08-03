import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The convergence estimate behind the analytic iteration

The iteration that solves `∂ξ∂η u = (Δ⊥ u + V u)/4` in the scale of analytic spaces pays two
transverse derivatives per step and earns a double integration. After `m` steps, with the radius of
analyticity shrunk in `m` equal instalments, the two effects combine into

`(loss) × (gain) = (m/δ)^{2m} × T^{2m}/(m!)² = (m^m/m!)² (T/δ)^{2m}`.

The whole convergence rests on the elementary bound `m^m/m! ≤ e^m`, which is nothing but the single
term `m^m/m!` of the exponential series at `m`. Squared, it turns the combination into a geometric
term, so the iteration converges as soon as `T e < δ`.

This file proves that bound and the resulting summability. It is stated for an abstract ratio `A`,
so it applies to either form of the scale — the coefficient form, where two derivatives cost
`4/(ρ-ρ')²`, or the sup-norm form, where they cost `16/(ρ-ρ')²`.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

/-- **The exponential dominates its own leading term.** -/
theorem pow_self_le_exp_mul_factorial (n : ℕ) :
    (n : ℝ) ^ n ≤ Real.exp n * (n.factorial : ℝ) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hsum := Real.sum_le_exp_of_nonneg hn (n + 1)
  have hmem : n ∈ Finset.range (n + 1) := Finset.self_mem_range_succ n
  have hle : (n : ℝ) ^ n / (n.factorial : ℝ)
      ≤ ∑ i ∈ Finset.range (n + 1), (n : ℝ) ^ i / (i.factorial : ℝ) := by
    refine Finset.single_le_sum (f := fun i : ℕ => (n : ℝ) ^ i / (i.factorial : ℝ)) ?_ hmem
    intro i _
    positivity
  have hterm : (n : ℝ) ^ n / (n.factorial : ℝ) ≤ Real.exp n := le_trans hle hsum
  rw [div_le_iff₀ hfac] at hterm
  linarith

/-- The ratio `m^m / m!` is at most `e^m`. -/
theorem pow_self_div_factorial_le_exp (n : ℕ) :
    (n : ℝ) ^ n / (n.factorial : ℝ) ≤ Real.exp n := by
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hfac]
  exact pow_self_le_exp_mul_factorial n

/-- **The squared ratio is geometric.** This is the exact shape produced by a step that loses two
derivatives and gains a double integration. -/
theorem sq_pow_self_div_factorial_le (m : ℕ) :
    ((m : ℝ) ^ m / (m.factorial : ℝ)) ^ 2 ≤ (Real.exp 2) ^ m := by
  have hbase := pow_self_div_factorial_le_exp m
  have hnn : (0 : ℝ) ≤ (m : ℝ) ^ m / (m.factorial : ℝ) := by positivity
  have h2 : ((m : ℝ) ^ m / (m.factorial : ℝ)) ^ 2 ≤ (Real.exp m) ^ 2 := by
    nlinarith [hbase, hnn, Real.exp_pos (m : ℝ)]
  have e1 : (Real.exp (m : ℝ)) ^ 2 = Real.exp ((m : ℝ) * 2) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have e2 : (Real.exp 2) ^ m = Real.exp ((m : ℝ) * 2) := by
    rw [← Real.exp_nat_mul]
  rw [e2]
  rw [e1] at h2
  exact h2

/-- **The Ovsyannikov term bound.** -/
theorem ovsyannikov_term_le {A : ℝ} (hA : 0 ≤ A) (m : ℕ) :
    A ^ m * ((m : ℝ) ^ m / (m.factorial : ℝ)) ^ 2 ≤ (A * Real.exp 2) ^ m := by
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left (sq_pow_self_div_factorial_le m) (pow_nonneg hA m)

/-- **The iteration converges once the rectangle is small compared with the radius.** -/
theorem summable_ovsyannikov {A : ℝ} (hA : 0 ≤ A) (hlt : A * Real.exp 2 < 1) :
    Summable fun m : ℕ => A ^ m * ((m : ℝ) ^ m / (m.factorial : ℝ)) ^ 2 := by
  have hgeo : Summable fun m : ℕ => (A * Real.exp 2) ^ m :=
    summable_geometric_of_lt_one (by positivity) hlt
  exact hgeo.of_nonneg_of_le (fun m => by positivity) (fun m => ovsyannikov_term_le hA m)

end GaloisForLFunctions.HTGeometry

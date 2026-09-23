import GaloisForLFunctions.HTGeometry.WeightedDegreeFunction
import GaloisForLFunctions.HTGeometry.ExponentialTowerLowAlgebra

/-!
# Weighted degrees in the exponential tower model

The tower monomials are products of distinct coordinates, so their weighted degree is the partial sum
of the weights.  The partial sums of tower monomials have the weighted degree of their top monomial,
because positive weights make that term the unique maximum and a degree function reads a unique
maximum off a finite sum.

These are the first two rows of the chain-gradient matrix whose staircase drives the cascade
observability determinant.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- The weight of the `k`-th tower monomial: the sum of the first `k` weights. -/
def towerWeight (w : ℕ → ℕ) (k : ℕ) : ℤ := ∑ j ∈ Finset.Icc 1 k, (w j : ℤ)

@[simp] theorem towerWeight_zero (w : ℕ → ℕ) : towerWeight w 0 = 0 := by
  simp [towerWeight]

theorem towerWeight_succ (w : ℕ → ℕ) (k : ℕ) :
    towerWeight w (k + 1) = towerWeight w k + (w (k + 1) : ℤ) := by
  rw [towerWeight, towerWeight, Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]

theorem towerWeight_lt (w : ℕ → ℕ) (hw : ∀ j, 0 < w j) {a b : ℕ} (h : a < b) :
    towerWeight w a < towerWeight w b := by
  induction b with
  | zero => omega
  | succ b ih =>
      rw [towerWeight_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
      · have := ih h'
        have : (0 : ℤ) < (w (b + 1) : ℤ) := by exact_mod_cast hw (b + 1)
        omega
      · subst h'
        have : (0 : ℤ) < (w (a + 1) : ℤ) := by exact_mod_cast hw (a + 1)
        omega

theorem towerMonomial_ne_zero_towerWeightedDegree (k : ℕ) : towerMonomial k ≠ 0 := by
  rw [towerMonomial]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => MvPolynomial.X_ne_zero i

/-- **The weighted degree of a tower monomial.** -/
theorem wdeg_towerMonomial (w : ℕ → ℕ) (k : ℕ) :
    wdeg w (towerMonomial k) = ((towerWeight w k : ℤ) : WithBot ℤ) := by
  induction k with
  | zero =>
      rw [towerMonomial_zero, towerWeight_zero, (isDegree_wdeg w).map_one]
      rfl
  | succ k ih =>
      rw [towerMonomial_succ, (isDegree_wdeg w).map_mul, ih, wdeg_X, towerWeight_succ]
      rfl

/-- **The weighted degree of a partial sum of tower monomials.**  Positive weights make the top
monomial the unique maximum. -/
theorem wdeg_towerSum (w : ℕ → ℕ) (hw : ∀ j, 0 < w j) (m : ℕ) :
    wdeg w (towerSum m) = ((towerWeight w m : ℤ) : WithBot ℤ) := by
  classical
  rw [towerSum]
  rw [(isDegree_wdeg w).map_sum_of_unique_max (Finset.self_mem_range_succ m)
    (towerMonomial_ne_zero_towerWeightedDegree m) ?_]
  · exact wdeg_towerMonomial w m
  · intro k hk hkm
    have hlt : k < m := by
      have := Finset.mem_range.mp hk
      omega
    rw [wdeg_towerMonomial, wdeg_towerMonomial]
    exact_mod_cast towerWeight_lt w hw hlt

end GaloisForLFunctions.HTGeometry

end

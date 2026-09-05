import GaloisForLFunctions.HTGeometry.CascadeFieldWeightedDegree
import GaloisForLFunctions.HTGeometry.TowerWeightedDegree

/-!
# Normalized-state recurrence in the cascade field

The tower monomial of height `k` has weighted degree `towerWeight w k`; its inverse therefore has
the opposite degree in the rational cascade model.  Consequently, a residue whose degree is below
that tower weight becomes a negative-degree perturbation after normalization.  Adding such a
perturbation preserves the invariant `deg (σ - 1) < 0`.

This is the exact algebraic recurrence used by the normalized logarithmic states in the cascade
separation argument.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- The `k`-th tower monomial, embedded in the rational cascade field. -/
def cascadeTowerMonomial (k : ℕ) : CascadeField :=
  algebraMap (MvPolynomial ℕ ℂ) CascadeField (towerMonomial k)

/-- The inverse tower monomial has the negative of its tower weight. -/
theorem cascadeDeg_inv_cascadeTowerMonomial (w : ℕ → ℕ) (k : ℕ) :
    cascadeDeg w (cascadeTowerMonomial k)⁻¹ =
      ((-towerWeight w k : ℤ) : WithBot ℤ) := by
  have hP : cascadeTowerMonomial k ≠ 0 :=
    algebraMap_fractionRing_ne_zero_of_ne_zero (towerMonomial_ne_zero k)
  have hPinv : (cascadeTowerMonomial k)⁻¹ ≠ 0 := inv_ne_zero hP
  have hdegP : cascadeDeg w (cascadeTowerMonomial k) =
      ((towerWeight w k : ℤ) : WithBot ℤ) := by
    rw [cascadeTowerMonomial, cascadeDeg_algebraMap, wdeg_towerMonomial]
  have hmul := (isDegree_cascadeDeg w).map_mul
    (cascadeTowerMonomial k) (cascadeTowerMonomial k)⁻¹
  rw [mul_inv_cancel₀ hP, (isDegree_cascadeDeg w).map_one, hdegP] at hmul
  cases hinv : cascadeDeg w (cascadeTowerMonomial k)⁻¹ with
  | bot => exact absurd hinv ((isDegree_cascadeDeg w).ne_bot hPinv)
  | coe a =>
      rw [hinv] at hmul
      have ha : a = -towerWeight w k := by
        have hZ : (0 : ℤ) = towerWeight w k + a := by exact_mod_cast hmul
        omega
      exact_mod_cast ha

/-- Dividing by the `k`-th tower monomial subtracts its tower weight. -/
theorem cascadeDeg_div_cascadeTowerMonomial (w : ℕ → ℕ) (k : ℕ) (r : CascadeField) :
    cascadeDeg w (r / cascadeTowerMonomial k) =
      cascadeDeg w r + ((-towerWeight w k : ℤ) : WithBot ℤ) := by
  rw [div_eq_mul_inv, (isDegree_cascadeDeg w).map_mul,
    cascadeDeg_inv_cascadeTowerMonomial]

/-- A lower-degree residue preserves the normalized-state invariant `deg (σ - 1) < 0`. -/
theorem cascadeDeg_normalizedState_step_lt_zero (w : ℕ → ℕ) (k : ℕ) (σ r : CascadeField)
    (hσ : cascadeDeg w (σ - 1) < 0)
    (hr : cascadeDeg w r < ((towerWeight w k : ℤ) : WithBot ℤ)) :
    cascadeDeg w (σ + r / cascadeTowerMonomial k - 1) < 0 := by
  have hpert : cascadeDeg w (r / cascadeTowerMonomial k) < 0 := by
    rw [cascadeDeg_div_cascadeTowerMonomial]
    cases hrdeg : cascadeDeg w r with
    | bot => simp
    | coe a =>
        rw [hrdeg] at hr
        have hrZ : a < towerWeight w k := by exact_mod_cast hr
        exact_mod_cast (by omega : a + (-towerWeight w k) < 0)
  calc
    cascadeDeg w (σ + r / cascadeTowerMonomial k - 1) =
        cascadeDeg w ((σ - 1) + r / cascadeTowerMonomial k) := by
      congr 1
      ring
    _ ≤ max (cascadeDeg w (σ - 1))
        (cascadeDeg w (r / cascadeTowerMonomial k)) :=
      (isDegree_cascadeDeg w).map_add_le _ _
    _ < 0 := max_lt hσ hpert

end GaloisForLFunctions.HTGeometry

end

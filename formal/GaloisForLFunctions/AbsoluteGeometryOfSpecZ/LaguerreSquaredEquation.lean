import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheLaguerreTailsOfTheCombTendToTheLiCoefficients
import GaloisForLFunctions.KodairaParshinAbc.Periods.DifferentialSymmetricSquare

/-!
# Differential equations for the Laguerre profiles of the arithmetic comb

The existing Li-tail coefficients form the associated Laguerre polynomial
`L_n^1`. Its exact coefficient recurrence gives the second-order Laguerre
equation and, by the Picard--Fuchs symmetric-square mechanism, a third-order
equation for its square. The zero coefficient tail is included explicitly.
-/

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open PowerSeries KodairaParshinAbc.Periods

/-- The existing Laguerre tail profile as a formal series of finite support. -/
def laguerreProfileSeries (n : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk (laguerreCoeff (n + 1))

@[simp] theorem coeff_laguerreProfileSeries (n k : ℕ) :
    PowerSeries.coeff k (laguerreProfileSeries n) = laguerreCoeff (n + 1) k := by
  simp [laguerreProfileSeries]

/-- Every coefficient strictly beyond the polynomial degree vanishes. -/
theorem laguerreProfileSeries_coeff_above (n k : ℕ) :
    PowerSeries.coeff (n + k + 1) (laguerreProfileSeries n) = 0 := by
  rw [coeff_laguerreProfileSeries]
  simp [laguerreCoeff, Nat.choose_eq_zero_of_lt (by omega : n + 1 < n + k + 1 + 1)]

/-- The exact recurrence includes the terminating coefficient and its zero tail. -/
theorem laguerreProfile_coefficient_recurrence (n k : ℕ) :
    (k + 1 : ℝ) * (k + 2) * laguerreCoeff (n + 1) (k + 1) +
      ((n : ℝ) - k) * laguerreCoeff (n + 1) k = 0 := by
  by_cases hkn : k ≤ n
  · have h := congrArg (fun t : ℕ => (t : ℝ)) (Nat.choose_succ_right_eq (n + 1) (k + 1))
    push_cast [Nat.cast_sub hkn, Nat.cast_sub (show k + 1 ≤ n + 1 by omega)] at h
    have hc : (k + 2 : ℝ) * ((n + 1).choose (k + 2) : ℝ) =
        ((n : ℝ) - k) * ((n + 1).choose (k + 1) : ℝ) := by
      linear_combination h
    have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hk : (k + 1 : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simp only [laguerreCoeff, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, pow_succ]
    field_simp
    linear_combination -(-1 : ℝ) ^ k * hc
  · have h₁ : n + 1 < k + 1 := by omega
    have h₂ : n + 1 < k + 1 + 1 := by omega
    simp [laguerreCoeff, Nat.choose_eq_zero_of_lt h₁, Nat.choose_eq_zero_of_lt h₂]

/-- The arithmetic comb's Laguerre profile satisfies its genuine second-order equation. -/
theorem laguerreProfile_differential_equation (n : ℕ) :
    secondOrderD (derivative ℝ) PowerSeries.X (C 2 - PowerSeries.X) (C (n : ℝ))
      (laguerreProfileSeries n) = 0 := by
  unfold secondOrderD
  rw [sub_mul]
  ext k
  cases k with
  | zero =>
      simp only [map_add, map_sub, coeff_zero_X_mul, coeff_C_mul, coeff_derivative,
        coeff_laguerreProfileSeries, map_zero, Nat.cast_zero, zero_add, mul_one]
      have h := laguerreProfile_coefficient_recurrence n 0
      norm_num only [Nat.cast_zero, zero_add, sub_zero, one_mul] at h
      linear_combination h
  | succ k =>
      simp only [map_add, map_sub, coeff_succ_X_mul, coeff_C_mul, coeff_derivative,
        coeff_laguerreProfileSeries, map_zero, Nat.cast_add, Nat.cast_one]
      have h := laguerreProfile_coefficient_recurrence n (k + 1)
      push_cast at h
      linear_combination h

/-- Squared Li-tail profiles satisfy the third-order symmetric-square equation at every degree. -/
theorem laguerreProfile_squared_equation (n : ℕ) :
    symmetricSquareD (derivative ℝ) PowerSeries.X (C 2 - PowerSeries.X) (C (n : ℝ))
      (laguerreProfileSeries n ^ 2) = 0 := by
  rw [symmetricSquareD_square, laguerreProfile_differential_equation,
    map_zero, mul_zero, mul_zero, add_zero]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ

#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.coeff_laguerreProfileSeries
#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.laguerreProfileSeries_coeff_above
#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.laguerreProfile_coefficient_recurrence
#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.laguerreProfile_differential_equation
#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.laguerreProfile_squared_equation

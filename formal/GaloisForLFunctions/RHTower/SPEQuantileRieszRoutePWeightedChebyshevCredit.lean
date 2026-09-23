import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePArithmeticVarianceNull

/-!
# Signed weighted-Chebyshev credit and two square debts

The full normalized P/SP-E history admits an exact decomposition around the
prime-number-theorem baseline. Linear endpoint mass error cancels. What remains
is one signed square-root-weighted Chebyshev credit, a strictly negative
matched-centroid excess, two nonnegative square debts, and bounded cubic width.
No sign is asserted for the credit.
-/

open scoped BigOperators Chebyshev

namespace RHTower

noncomputable def routePWeightedChebyshevNullCredit (K : ℕ) : ℝ :=
  routePSqrtChebyshevMoment K -
    (2 / 3) * ((K + 2 : ℕ) : ℝ) * Real.sqrt ((K + 2 : ℕ) : ℝ) -
    Real.sqrt ((K + 2 : ℕ) : ℝ) *
      (Chebyshev.psi ((K + 2 : ℕ) : ℝ) - ((K + 2 : ℕ) : ℝ))

theorem routeP_normalized_history_eq_credit_sub_two_square_debts (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K =
      4 * routePWeightedChebyshevNullCredit K -
        2 * Real.sqrt ((K + 2 : ℕ) : ℝ) *
          ccmActualHeadMatchedCentroidChebyshevExcess K -
        (2 * (Chebyshev.psi ((K + 2 : ℕ) : ℝ) - ((K + 2 : ℕ) : ℝ)) +
            ccmActualHeadMatchedCentroidChebyshevExcess K -
            Real.sqrt ((K + 2 : ℕ) : ℝ) *
              (ccmActualHeadParabolicMass K -
                2 * Real.sqrt ((K + 2 : ℕ) : ℝ))) ^ (2 : ℕ) /
          ccmActualHeadParabolicMass K -
        (4 * Real.sqrt ((K + 2 : ℕ) : ℝ) + ccmActualHeadParabolicMass K) / 12 *
          (ccmActualHeadParabolicMass K -
            2 * Real.sqrt ((K + 2 : ℕ) : ℝ)) ^ (2 : ℕ) +
        4 * routePWidthCubePrefix K / 3 := by
  let x : ℝ := ((K + 2 : ℕ) : ℝ)
  let r := Real.sqrt x
  let m := ccmActualHeadParabolicMass K
  let p := Chebyshev.psi x
  let e := ccmActualHeadMatchedCentroidChebyshevExcess K
  let A := routePSqrtChebyshevMoment K
  let q := routePWidthCubePrefix K
  have hr : r ^ (2 : ℕ) = x := Real.sq_sqrt (by positivity)
  have hm : m ≠ 0 := (ccmActualHeadParabolicMass_pos K).ne'
  rw [routeP_normalized_history_eq_arithmetic_null]
  unfold routePWeightedChebyshevNullCredit
  change 4 * A + 4 * q / 3 - (2 * p + e) ^ (2 : ℕ) / m -
      m ^ (3 : ℕ) / 12 =
    4 * (A - (2 / 3) * x * r - r * (p - x)) -
      2 * r * e -
      (2 * (p - x) + e - r * (m - 2 * r)) ^ (2 : ℕ) / m -
      (4 * r + m) / 12 * (m - 2 * r) ^ (2 : ℕ) + 4 * q / 3
  rw [← hr]
  field_simp [hm]; ring

end RHTower

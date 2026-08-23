import GaloisForLFunctions.RHTower.NearDiagonalInnerSum
import GaloisForLFunctions.RHTower.Sieve.ReciprocalPhaseStability

/-!
# The dilated near-diagonal phase, and the type-I sums

Dilating the summation variable of the near-diagonal phase only rescales the offset:
`F_r(d·v) = F_{r/d}(v)`, because `1 + r/(dv) = 1 + (r/d)/v`.  The type-I sums produced by Vaughan's
identity are therefore near-diagonal sums at the scaled offset `r/d`, and the dyadic block estimate
applies to them verbatim — no new derivative test is needed for that half of the decomposition.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- **Dilation rescales the offset.** -/
theorem nearDiagonalPhase_mul (T r d u : ℝ) :
    nearDiagonalPhase T r (d * u) = nearDiagonalPhase T (r / d) u := by
  rw [nearDiagonalPhase, nearDiagonalPhase]
  congr 2
  rw [div_div]

/-- The dilated exponential sum is a near-diagonal sum at the scaled offset. -/
theorem dilated_nearDiagonalSum_eq (T r d : ℝ) (A B : ℕ) :
    ∑ m ∈ Finset.Ico A B,
        Complex.exp (((2 * Real.pi * nearDiagonalPhase T r (d * (m : ℝ)) : ℝ) : ℂ) * Complex.I)
      = nearDiagonalSum T (r / d) A B := by
  rw [nearDiagonalSum]
  exact Finset.sum_congr rfl fun m _ => by rw [nearDiagonalPhase_mul T r d (m : ℝ)]

/-- **The type-I inner sum.**  The dyadic block estimate at the scaled offset. -/
theorem norm_dilated_nearDiagonalSum_le {T r d : ℝ} (hT : 0 < T) (hr : 0 < r) (hd : 0 < d)
    (A B : ℕ) (hA : 1 ≤ A) (hrA : r / d ≤ (A : ℝ))
    (hlam : nearDiagonalLambda T (r / d) (A : ℝ) ≤ 1) :
    ‖∑ m ∈ Finset.Ico A B,
        Complex.exp (((2 * Real.pi * nearDiagonalPhase T r (d * (m : ℝ)) : ℝ) : ℂ)
          * Complex.I)‖
      ≤ 2500 * Real.sqrt (T * (r / d) / (36 * Real.pi * A))
        + 22 * Real.sqrt (36 * Real.pi / (T * (r / d))) * Real.sqrt (((B : ℝ)) ^ 3) := by
  rw [dilated_nearDiagonalSum_eq T r d A B]
  exact norm_nearDiagonalSum_le_final hT (by positivity) A B hA hrA hlam

end

end RHTower.Sieve

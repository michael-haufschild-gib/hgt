import GaloisForLFunctions.RHTower.Sieve.TypeIBound
import GaloisForLFunctions.RHTower.Sieve.TypeILogWeight
import GaloisForLFunctions.RHTower.Sieve.DilatedNearDiagonalSum
import GaloisForLFunctions.RHTower.Sieve.NearDiagonalThirdDerivative

/-!
# Third-derivative type-I bound

The third-derivative estimate is stable under the type-I dilation `n = d m`: the offset becomes
`r/d`, while the summation interval is unchanged.
-/

namespace RHTower.Sieve

open RHTower

noncomputable section

/-- Explicit third-derivative envelope for one type-I fibre. -/
def thirdDerivativeTypeIBound (T r : ℝ) (d A B : ℕ) : ℝ :=
  256 * (((B - A : ℕ) : ℝ) *
        (1368 ^ 2 * nearDiagonalLambda3 T (r / d) A) ^ (1 / 6 : ℝ)
      + ((B - A : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
        nearDiagonalLambda3 T (r / d) A ^ (-(1 / 4 : ℝ)))

/-- Third-derivative estimate for one type-I fibre. -/
theorem norm_sum_ndExp_third_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {d : ℕ} (hd : 1 ≤ d) (A B : ℕ) (hA : 1 ≤ A) (hspan : B - A - 1 ≤ A)
    (hrA : r / d ≤ (A : ℝ)) (hlam1 : nearDiagonalLambda3 T (r / d) A ≤ 1) :
    ‖∑ m ∈ Finset.Ico A B, ndExp T r m d‖
      ≤ thirdDerivativeTypeIBound T r d A B := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [sum_ndExp_eq_dilated, dilated_nearDiagonalSum_eq T r d A B]
  exact norm_nearDiagonalSum_third_le hT (div_pos hr hd0) A B hA hspan hrA hlam1

theorem thirdDerivativeTypeIBound_nonneg {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {d A B : ℕ} (hd : 1 ≤ d) (hA : 1 ≤ A) :
    0 ≤ thirdDerivativeTypeIBound T r d A B := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hlam0 : 0 < nearDiagonalLambda3 T (r / d) A :=
    nearDiagonalLambda3_pos hT (div_pos hr hd0) hA0
  rw [thirdDerivativeTypeIBound]
  positivity

/-- The third-derivative fibre envelope increases with its right endpoint. -/
theorem thirdDerivativeTypeIBound_mono {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {d A J B : ℕ} (hd : 1 ≤ d) (hA : 1 ≤ A) (hJB : J ≤ B) :
    thirdDerivativeTypeIBound T r d A J ≤ thirdDerivativeTypeIBound T r d A B := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hlam0 : 0 < nearDiagonalLambda3 T (r / d) A :=
    nearDiagonalLambda3_pos hT (div_pos hr hd0) hA0
  have hsub : J - A ≤ B - A := Nat.sub_le_sub_right hJB A
  have hsubR : (((J - A : ℕ) : ℝ)) ≤ (((B - A : ℕ) : ℝ)) := by exact_mod_cast hsub
  have hsqrt : (((J - A : ℕ) : ℝ)) ^ (1 / 2 : ℝ) ≤
      (((B - A : ℕ) : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hsubR (by norm_num)
  have hfirst0 : 0 ≤ (1368 ^ 2 * nearDiagonalLambda3 T (r / d) A) ^ (1 / 6 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hsecond0 : 0 ≤ nearDiagonalLambda3 T (r / d) A ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_nonneg hlam0.le _
  rw [thirdDerivativeTypeIBound, thirdDerivativeTypeIBound]
  have hfirst := mul_le_mul_of_nonneg_right hsubR hfirst0
  have hsecond := mul_le_mul_of_nonneg_right hsqrt hsecond0
  nlinarith

/-- Third-derivative estimate for a logarithmically weighted type-I fibre. -/
theorem norm_sum_log_ndExp_third_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {d : ℕ} (hd : 1 ≤ d) {A B : ℕ} (hAB : A < B) (hA : 1 ≤ A)
    (hspan : B - A - 1 ≤ A) (hrA : r / d ≤ (A : ℝ))
    (hlam1 : nearDiagonalLambda3 T (r / d) A ≤ 1) :
    ‖∑ k ∈ Finset.Ico A B, ((Real.log k : ℝ) : ℂ) * ndExp T r k d‖
      ≤ 2 * thirdDerivativeTypeIBound T r d A B * Real.log ((B - 1 : ℕ) : ℝ) := by
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  refine norm_sum_Ico_mul_le_of_bounded_partial_mono hAB (fun k => Real.log k)
    (fun k => ndExp T r k d) (Real.log_nonneg hA1) ?_ ?_
  · intro i hi
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by
      exact_mod_cast le_trans hA hi
    refine Real.log_le_log (by linarith) ?_
    push_cast
    linarith
  · intro k hk
    have hle : A + k ≤ B := by omega
    have hspan' : A + k - A - 1 ≤ A := by omega
    refine (norm_sum_ndExp_third_le hT hr hd A (A + k) hA hspan' hrA hlam1).trans ?_
    exact thirdDerivativeTypeIBound_mono hT hr hd hA hle

end

end RHTower.Sieve

import GaloisForLFunctions.RHTower.Sieve.TypeIBound
import GaloisForLFunctions.RHTower.Sieve.TypeILogWeight
import GaloisForLFunctions.RHTower.Sieve.DilatedNearDiagonalSum
import GaloisForLFunctions.RHTower.Sieve.NearDiagonalThirdDerivativeSharp

namespace RHTower.Sieve

open RHTower

noncomputable section

def sharpThirdDerivativeTypeIBound (T r : ℝ) (d A B : ℕ) : ℝ :=
  16 * 1368 * ((((B - A : ℕ) : ℝ) * nearDiagonalLambda3 T (r / d) A ^ (1 / 6 : ℝ))
    + Real.sqrt (((B - A : ℕ) : ℝ)) *
      nearDiagonalLambda3 T (r / d) A ^ (-(1 / 6 : ℝ)))

theorem norm_sum_ndExp_third_sharp_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {d : ℕ} (hd : 1 ≤ d) (A B : ℕ) (hA : 1 ≤ A) (hspan : B - A - 1 ≤ A)
    (hrA : r / d ≤ (A : ℝ)) (hlam1 : nearDiagonalLambda3 T (r / d) A ≤ 1) :
    ‖∑ m ∈ Finset.Ico A B, ndExp T r m d‖
      ≤ sharpThirdDerivativeTypeIBound T r d A B := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [sum_ndExp_eq_dilated, dilated_nearDiagonalSum_eq T r d A B]
  exact norm_nearDiagonalSum_third_sharp_le hT (div_pos hr hd0) A B hA hspan hrA hlam1

theorem sharpThirdDerivativeTypeIBound_nonneg {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {d A B : ℕ} (hd : 1 ≤ d) (hA : 1 ≤ A) :
    0 ≤ sharpThirdDerivativeTypeIBound T r d A B := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hlam0 : 0 < nearDiagonalLambda3 T (r / d) A :=
    nearDiagonalLambda3_pos hT (div_pos hr hd0) hA0
  rw [sharpThirdDerivativeTypeIBound]
  positivity

theorem sharpThirdDerivativeTypeIBound_mono {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {d A J B : ℕ} (hd : 1 ≤ d) (hA : 1 ≤ A) (hJB : J ≤ B) :
    sharpThirdDerivativeTypeIBound T r d A J ≤
      sharpThirdDerivativeTypeIBound T r d A B := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hlam0 : 0 < nearDiagonalLambda3 T (r / d) A :=
    nearDiagonalLambda3_pos hT (div_pos hr hd0) hA0
  have hsub : J - A ≤ B - A := Nat.sub_le_sub_right hJB A
  have hsubR : (((J - A : ℕ) : ℝ)) ≤ (((B - A : ℕ) : ℝ)) := by exact_mod_cast hsub
  have hsqrt : Real.sqrt (((J - A : ℕ) : ℝ)) ≤ Real.sqrt (((B - A : ℕ) : ℝ)) :=
    Real.sqrt_le_sqrt hsubR
  have hfirst0 : 0 ≤ nearDiagonalLambda3 T (r / d) A ^ (1 / 6 : ℝ) := by positivity
  have hsecond0 : 0 ≤ nearDiagonalLambda3 T (r / d) A ^ (-(1 / 6 : ℝ)) := by positivity
  rw [sharpThirdDerivativeTypeIBound, sharpThirdDerivativeTypeIBound]
  nlinarith [mul_le_mul_of_nonneg_right hsubR hfirst0,
    mul_le_mul_of_nonneg_right hsqrt hsecond0]

theorem norm_sum_log_ndExp_third_sharp_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {d : ℕ} (hd : 1 ≤ d) {A B : ℕ} (hAB : A < B) (hA : 1 ≤ A)
    (hspan : B - A - 1 ≤ A) (hrA : r / d ≤ (A : ℝ))
    (hlam1 : nearDiagonalLambda3 T (r / d) A ≤ 1) :
    ‖∑ k ∈ Finset.Ico A B, ((Real.log k : ℝ) : ℂ) * ndExp T r k d‖
      ≤ 2 * sharpThirdDerivativeTypeIBound T r d A B * Real.log ((B - 1 : ℕ) : ℝ) := by
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  refine norm_sum_Ico_mul_le_of_bounded_partial_mono hAB (fun k => Real.log k)
    (fun k => ndExp T r k d) (Real.log_nonneg hA1) ?_ ?_
  · intro i hi
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast le_trans hA hi
    refine Real.log_le_log (by linarith) ?_
    push_cast
    linarith
  · intro k hk
    have hle : A + k ≤ B := by omega
    have hspan' : A + k - A - 1 ≤ A := by omega
    refine (norm_sum_ndExp_third_sharp_le hT hr hd A (A + k) hA hspan' hrA hlam1).trans ?_
    exact sharpThirdDerivativeTypeIBound_mono hT hr hd hA hle

end

end RHTower.Sieve

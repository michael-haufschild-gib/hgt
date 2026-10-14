import GaloisForLFunctions.RHTower.JointAncestryPhaseBudgetPositivity
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.Fourier.AddCircle

/-! # Exact squared norm of the signed local JAS density

Parseval retains both complex Fourier tails. The resulting rational norm budget
avoids the exponential loss of a bound based only on the sum of local variances.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace RHTower

theorem hasSum_sq_norm_jasLocalCoeff {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    HasSum (fun k : ℤ => ‖jasLocalCoeff a b k‖ ^ 2)
      ((1 - ‖a‖ ^ 2)⁻¹ + ((1 - ‖b‖ ^ 2)⁻¹ - 1)) := by
  have ha2 : ‖(‖a‖ ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg a]
  have hb2 : ‖(‖b‖ ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg b]
  have hf : HasSum (fun n : ℕ => ‖jasLocalCoeff a b (n : ℤ)‖ ^ 2)
      (1 - ‖a‖ ^ 2)⁻¹ := by
    have heq : (fun n : ℕ => ‖jasLocalCoeff a b (n : ℤ)‖ ^ 2) =
        fun n : ℕ => (‖a‖ ^ 2) ^ n := by
      funext n
      rw [jasLocalCoeff, if_pos (Int.natCast_nonneg n), Int.toNat_natCast, norm_pow,
        ← pow_mul, ← pow_mul, Nat.mul_comm n 2]
    rw [heq]
    exact hasSum_geometric_of_norm_lt_one ha2
  have hg : HasSum (fun n : ℕ => ‖jasLocalCoeff a b (-((n : ℤ) + 1))‖ ^ 2)
      ((1 - ‖b‖ ^ 2)⁻¹ - 1) := by
    have h : HasSum (fun n : ℕ => (‖b‖ ^ 2) ^ (n + 1))
        ((1 - ‖b‖ ^ 2)⁻¹ - ∑ i ∈ Finset.range 1, (‖b‖ ^ 2) ^ i) :=
      (hasSum_nat_add_iff' 1).mpr (hasSum_geometric_of_norm_lt_one hb2)
    simp only [Finset.sum_range_one, pow_zero] at h
    convert h using 1
    funext n
    have hcast : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [jasLocalCoeff, if_neg (by omega), neg_neg, hcast]
    rw [Int.toNat_natCast, norm_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (n + 1) 2]
  exact hf.of_nat_of_neg_add_one hg

theorem memLp_two_jasHoloCircle {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    MemLp (jasHoloCircle a b) 2 jasCircleHaar :=
  ContinuousMap.memLp (μ := jasCircleHaar) ℂ
    ⟨jasHoloCircle a b, continuous_jasHoloCircle ha hb⟩

theorem integral_sq_norm_jasHoloCircle {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ∫ θ, ‖jasHoloCircle a b θ‖ ^ 2 ∂jasCircleHaar =
      (1 - ‖a‖ ^ 2)⁻¹ + ((1 - ‖b‖ ^ 2)⁻¹ - 1) := by
  let hf := memLp_two_jasHoloCircle ha hb
  have hcoeff : ∀ k : ℤ, fourierCoeff (hf.toLp _) k = jasLocalCoeff a b k := by
    intro k
    rw [fourierCoeff_congr_ae hf.coeFn_toLp]
    exact integral_fourier_neg_mul_jasHoloCircle ha hb k
  have h := hasSum_sq_fourierCoeff (hf.toLp _)
  simp_rw [hcoeff] at h
  have hi : (∫ θ, ‖(hf.toLp _) θ‖ ^ 2 ∂jasCircleHaar) =
      ∫ θ, ‖jasHoloCircle a b θ‖ ^ 2 ∂jasCircleHaar := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with θ hθ
    rw [hθ]
  rw [hi] at h
  exact h.unique (hasSum_sq_norm_jasLocalCoeff ha hb)

theorem integral_sq_norm_jasHoloCircle_factorized {a b : ℂ}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ∫ θ, ‖jasHoloCircle a b θ‖ ^ 2 ∂jasCircleHaar =
      (1 - ‖a * b‖ ^ 2) / ((1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2)) := by
  rw [integral_sq_norm_jasHoloCircle ha hb, norm_mul]
  have ha0 : 1 - ‖a‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg a]
  have hb0 : 1 - ‖b‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg b]
  field_simp [ha0, hb0]
  ring

theorem integral_sq_norm_jasHoloCircle_le {a b : ℂ}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ∫ θ, ‖jasHoloCircle a b θ‖ ^ 2 ∂jasCircleHaar ≤
      (1 - ‖a‖ ^ 2)⁻¹ * (1 - ‖b‖ ^ 2)⁻¹ := by
  rw [integral_sq_norm_jasHoloCircle_factorized ha hb, ← mul_inv, ← one_div]
  apply div_le_div_of_nonneg_right
  · exact sub_le_self _ (sq_nonneg _)
  · apply mul_nonneg <;> nlinarith [norm_nonneg a, norm_nonneg b]

end RHTower

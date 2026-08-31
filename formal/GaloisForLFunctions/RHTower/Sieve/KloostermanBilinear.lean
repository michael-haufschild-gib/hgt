import GaloisForLFunctions.RHTower.Sieve.KloostermanTransform

/-!
# Complete Kloosterman bilinear form

The sharp finite `L²` bound for the complete Kloosterman transform gives a bilinear estimate with
operator norm at most `q`.  This is the fixed-modulus finite Fourier layer underlying spectral
large-sieve estimates.
-/

open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Complete fixed-modulus Kloosterman bilinear form. -/
def kloostermanBilinear (q : ℕ) [NeZero q]
    (a b : ZMod q → ℂ) : ℂ :=
  ∑ n : ZMod q, b n * kloostermanTransform q a n

/-- Expansion of the transform form as the usual complete Kloosterman double sum. -/
theorem kloostermanBilinear_eq
    (q : ℕ) [NeZero q] (a b : ZMod q → ℂ) :
    kloostermanBilinear q a b =
      ∑ m : ZMod q, a m * ∑ n : ZMod q, b n * kloostermanSum q m n := by
  unfold kloostermanBilinear kloostermanTransform
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Sharp fixed-modulus bilinear square bound for the complete Kloosterman kernel. -/
theorem norm_kloostermanBilinear_sq_le
    (q : ℕ) [NeZero q] (a b : ZMod q → ℂ) :
    ‖kloostermanBilinear q a b‖ ^ 2 ≤
      (q : ℝ) ^ 2 * (∑ m : ZMod q, ‖a m‖ ^ 2) *
        ∑ n : ZMod q, ‖b n‖ ^ 2 := by
  have htri : ‖kloostermanBilinear q a b‖ ≤
      ∑ n : ZMod q, ‖b n‖ * ‖kloostermanTransform q a n‖ := by
    unfold kloostermanBilinear
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum fun n _ =>
      le_of_eq (norm_mul (b n) (kloostermanTransform q a n))
  have hnn : (0 : ℝ) ≤
      ∑ n : ZMod q, ‖b n‖ * ‖kloostermanTransform q a n‖ :=
    Finset.sum_nonneg fun n _ => by positivity
  have hsq : ‖kloostermanBilinear q a b‖ ^ 2 ≤
      (∑ n : ZMod q, ‖b n‖ * ‖kloostermanTransform q a n‖) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖kloostermanBilinear q a b‖ := norm_nonneg _
    nlinarith
  have hcs :
      (∑ n : ZMod q, ‖b n‖ * ‖kloostermanTransform q a n‖) ^ 2 ≤
        (∑ n : ZMod q, ‖b n‖ ^ 2) *
          ∑ n : ZMod q, ‖kloostermanTransform q a n‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun n : ZMod q => ‖b n‖) (fun n => ‖kloostermanTransform q a n‖)
  have htransform := sum_norm_kloostermanTransform_sq_le q a
  calc
    _ ≤ (∑ n : ZMod q, ‖b n‖ * ‖kloostermanTransform q a n‖) ^ 2 := hsq
    _ ≤ (∑ n : ZMod q, ‖b n‖ ^ 2) *
        ∑ n : ZMod q, ‖kloostermanTransform q a n‖ ^ 2 := hcs
    _ ≤ (∑ n : ZMod q, ‖b n‖ ^ 2) *
        ((q : ℝ) ^ 2 * ∑ m : ZMod q, ‖a m‖ ^ 2) :=
      mul_le_mul_of_nonneg_left htransform
        (Finset.sum_nonneg fun n _ => by positivity)
    _ = _ := by ring

end

end RHTower.Sieve

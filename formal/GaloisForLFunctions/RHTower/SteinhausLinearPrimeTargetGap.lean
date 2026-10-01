import GaloisForLFunctions.RHTower.SteinhausLinearPrimeTargetEnergy

open Complex MeasureTheory Finset
noncomputable section
namespace RHTower
open SteinhausModel

/-- A normalized linear square density has a nonzero target-error floor,
with the exact single-prime collision correction retained. -/
theorem primeTarget_linearDensity_error_lower
    (P : Finset ℕ) (u b : ℕ → ℂ) (a g : ℂ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hnorm : ‖a‖ ^ 2 + ∑ p ∈ P, ‖b p‖ ^ 2 = 1) :
    (3 / 4 : ℝ) * ‖g‖ ^ 2 - ∑ p ∈ P, ‖u p‖ ^ 2 * ‖b p‖ ^ 2 ≤
      ∫ ω, ‖(∑ p ∈ P, u p * X p ω) - g‖ ^ 2 *
        ‖a + ∑ p ∈ P, b p * X p ω‖ ^ 2 ∂steinhausMeasure := by
  let V := ∑ p ∈ P, ‖u p‖ ^ 2
  let B := ∑ p ∈ P, ‖b p‖ ^ 2
  let S := ∑ p ∈ P, ‖u p‖ * ‖b p‖
  have hV : 0 ≤ V := sum_nonneg (fun _ _ => sq_nonneg _)
  have hB : 0 ≤ B := sum_nonneg (fun _ _ => sq_nonneg _)
  have hCS : S ^ 2 ≤ V * B := sum_mul_sq_le_sq_mul_sq P (fun p => ‖u p‖) (fun p => ‖b p‖)
  have hn : ‖a‖ ^ 2 + B = 1 := hnorm
  have hAB : 4 * ‖a‖ ^ 2 * B ≤ 1 := by nlinarith [sq_nonneg (‖a‖ ^ 2 - B)]
  have hAS : 4 * ‖a‖ ^ 2 * S ^ 2 ≤ V := by
    have h1 := mul_le_mul_of_nonneg_left hCS (show 0 ≤ 4 * ‖a‖ ^ 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hAB hV
    nlinarith
  have hfloor : (3 / 4 : ℝ) * ‖g‖ ^ 2 ≤ V + ‖g‖ ^ 2 - 2 * ‖g‖ * ‖a‖ * S := by
    nlinarith [sq_nonneg (2 * ‖a‖ * S - ‖g‖ / 2)]
  have hterm (p : ℕ) : ‖a‖ ^ 2 * ‖u p‖ ^ 2 + ‖g‖ ^ 2 * ‖b p‖ ^ 2 -
      2 * ‖g‖ * ‖a‖ * (‖u p‖ * ‖b p‖) ≤ ‖a * u p - g * b p‖ ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (‖a * u p‖ - ‖g * b p‖))
      (abs_norm_sub_norm_le (a * u p) (g * b p)) 2
    rw [sq_abs, norm_mul, norm_mul] at h
    nlinarith
  have hsum : ‖a‖ ^ 2 * V + ‖g‖ ^ 2 * B - 2 * ‖g‖ * ‖a‖ * S ≤
      ∑ p ∈ P, ‖a * u p - g * b p‖ ^ 2 := by
    have h := sum_le_sum (fun p (_ : p ∈ P) => hterm p)
    simpa only [sum_sub_distrib, sum_add_distrib, ← mul_sum, V, B, S] using h
  rw [integral_primeTarget_linearDensity_energy P u b a g hP, norm_mul, mul_pow]
  have hz := sq_nonneg ‖∑ p ∈ P, u p * (starRingEnd ℂ) (b p)‖
  change _ ≤ ‖g‖ ^ 2 * ‖a‖ ^ 2 + _ + V * B + _ - _
  have he : ‖g‖ ^ 2 * ‖a‖ ^ 2 +
      (‖a‖ ^ 2 * V + ‖g‖ ^ 2 * B - 2 * ‖g‖ * ‖a‖ * S) + V * B =
        V + ‖g‖ ^ 2 - 2 * ‖g‖ * ‖a‖ * S := by
    calc
      _ = (‖a‖ ^ 2 + B) * (V + ‖g‖ ^ 2) - 2 * ‖g‖ * ‖a‖ * S := by ring
      _ = _ := by rw [hn, one_mul]
  linarith

/-- In particular the correction is at most the largest channel square.
This excludes only linear positive mean-square certificates. -/
theorem primeTarget_linearDensity_error_lower_of_channel_bound
    (P : Finset ℕ) (u b : ℕ → ℂ) (a g : ℂ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hnorm : ‖a‖ ^ 2 + ∑ p ∈ P, ‖b p‖ ^ 2 = 1)
    {η : ℝ} (hη : 0 ≤ η) (hu : ∀ p ∈ P, ‖u p‖ ^ 2 ≤ η) :
    (3 / 4 : ℝ) * ‖g‖ ^ 2 - η ≤
      ∫ ω, ‖(∑ p ∈ P, u p * X p ω) - g‖ ^ 2 *
        ‖a + ∑ p ∈ P, b p * X p ω‖ ^ 2 ∂steinhausMeasure := by
  have hdiag : (∑ p ∈ P, ‖u p‖ ^ 2 * ‖b p‖ ^ 2) ≤ η := by
    calc
      _ ≤ ∑ p ∈ P, η * ‖b p‖ ^ 2 :=
        sum_le_sum (fun p hp => mul_le_mul_of_nonneg_right (hu p hp) (sq_nonneg _))
      _ = η * (∑ p ∈ P, ‖b p‖ ^ 2) := (mul_sum _ _ _).symm
      _ ≤ η := by nlinarith [sq_nonneg ‖a‖]
  exact (sub_le_sub_left hdiag _).trans (primeTarget_linearDensity_error_lower P u b a g hP hnorm)

end RHTower

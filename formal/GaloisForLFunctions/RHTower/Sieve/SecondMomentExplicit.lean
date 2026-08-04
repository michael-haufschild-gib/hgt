import GaloisForLFunctions.RHTower.Sieve.BalancedImageBound

/-!
# The second moment with explicit constants

Chaining the reductions at `S = [y, 2y] = (y-1, 2y]`, so `b - a = y + 1` and `M = 2y`:

`∑_{d₁,d₂ ∈ [y,2y]} 1/lcm(d₁,d₂) ≤ y^{-2} ((y+1)²(1 + log 2y) + 2(y+1)(2y) + (2y)²)`,

which is `O(log y)`.  Substituted into the second moment of the balanced divisor count and then into
`card_image_mul_ge`, the distinct-product bound becomes fully explicit.
-/

namespace RHTower.Sieve

open Finset

/-- The balanced window as a half-open interval. -/
theorem Icc_eq_Ioc_pred {y : ℕ} (hy : 1 ≤ y) :
    Finset.Icc y (2 * y) = Finset.Ioc (y - 1) (2 * y) := by
  ext d
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- **The reciprocal lcm sum over a balanced window, explicitly.** -/
theorem sum_inv_lcm_explicit {y : ℕ} (hy : 1 ≤ y) :
    ∑ p ∈ (Finset.Icc y (2 * y)) ×ˢ (Finset.Icc y (2 * y)), 1 / ((Nat.lcm p.1 p.2 : ℕ) : ℝ)
      ≤ (1 / (y : ℝ) ^ 2)
        * (((y : ℝ) + 1) ^ 2 * (1 + Real.log (2 * y)) + 2 * ((y : ℝ) + 1) * (2 * (y : ℝ))
            + (2 * (y : ℝ)) ^ 2) := by
  classical
  have hyR : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hgcd := sum_gcd_eq_sum_totient_mul_sq (S := Finset.Icc y (2 * y)) (M := 2 * y)
    (fun d hd => by rw [Finset.mem_Icc] at hd; omega)
    (fun d hd => by rw [Finset.mem_Icc] at hd; omega)
  have hconv : ∀ g : ℕ,
      (((Finset.Icc y (2 * y)).filter (fun d => g ∣ d)).card : ℝ)
        = (((Finset.Ioc (y - 1) (2 * y)).filter (fun d => g ∣ d)).card : ℝ) := by
    intro g
    rw [Icc_eq_Ioc_pred hy]
  have htot := sum_totient_mul_card_sq_le (y - 1) (2 * y) (2 * y) (by omega)
  have hlen : ((2 * y : ℕ) : ℝ) - ((y - 1 : ℕ) : ℝ) = (y : ℝ) + 1 := by
    have h1 : ((y - 1 : ℕ) : ℝ) = (y : ℝ) - 1 := by
      have : (1 : ℕ) ≤ y := hy
      push_cast [Nat.cast_sub this]
      ring
    rw [h1]
    push_cast
    ring
  rw [hlen] at htot
  have hMcast : ((2 * y : ℕ) : ℝ) = 2 * (y : ℝ) := by push_cast; ring
  rw [hMcast] at htot
  have hgcdbound : ∑ p ∈ (Finset.Icc y (2 * y)) ×ˢ (Finset.Icc y (2 * y)),
      ((Nat.gcd p.1 p.2 : ℕ) : ℝ)
      ≤ ((y : ℝ) + 1) ^ 2 * (1 + Real.log (2 * y)) + 2 * ((y : ℝ) + 1) * (2 * (y : ℝ))
          + (2 * (y : ℝ)) ^ 2 := by
    rw [hgcd]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun g _ => ?_)) htot
    rw [hconv g]
  refine le_trans (sum_inv_lcm_le_gcd_sum hy) ?_
  have hy2 : (0 : ℝ) < 1 / (y : ℝ) ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left hgcdbound (le_of_lt hy2)

/-- The explicit second-moment constant for a balanced window. -/
noncomputable def balancedMomentConst (y : ℕ) : ℝ :=
  (1 / (y : ℝ) ^ 2)
    * (((y : ℝ) + 1) ^ 2 * (1 + Real.log (2 * y)) + 2 * ((y : ℝ) + 1) * (2 * (y : ℝ))
        + (2 * (y : ℝ)) ^ 2)

/-- **The second moment of the balanced divisor count, explicitly.** -/
theorem sum_sq_card_divisors_explicit {y : ℕ} (hy : 1 ≤ y) (X : ℕ) :
    ∑ m ∈ Finset.Icc 1 X,
        ((((Finset.Icc y (2 * y)).filter (fun d => d ∣ m)).card : ℕ) : ℝ) ^ 2
      ≤ (X : ℝ) * balancedMomentConst y := by
  refine le_trans (sum_sq_card_divisors_window_le X y) ?_
  exact mul_le_mul_of_nonneg_left (sum_inv_lcm_explicit hy) (Nat.cast_nonneg X)

/-- **The distinct-product bound, fully explicit.** -/
theorem card_image_mul_ge_explicit {y X : ℕ} (hy : 1 ≤ y) (S : Finset (ℕ × ℕ))
    (hV : 0 < (X : ℝ) * balancedMomentConst y)
    (hd : ∀ p ∈ S, p.1 ∈ Finset.Icc y (2 * y))
    (himg : ∀ p ∈ S, p.1 * p.2 ∈ Finset.Icc 1 X) :
    ((S.card : ℕ) : ℝ) ^ 2 / ((X : ℝ) * balancedMomentConst y)
      ≤ (((S.image (fun p => p.1 * p.2)).card : ℕ) : ℝ) :=
  card_image_mul_ge hy S hV hd himg (sum_sq_card_divisors_explicit hy X)

end RHTower.Sieve

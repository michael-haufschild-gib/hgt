import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

/-!
# Exact cost of the quartic local valuation bound

The local coefficient exponent is `min(v, k, floor(2k/3) + l)`.
Its weighted denominator costs at least this exponent times
`min(3σ/2, σ + θ/3)`. Both linear pieces are attained on integral rays:
`(v,k,l) = (2n,3n,0)` and `(3n,3n,n)`. The resulting correction loss
is therefore the exact boundary of this local majorant.
-/

namespace GaloisForLFunctions.FamilyContinuationTheory.Quartic

/-- Valuation exponent in the quartic prime-power coefficient bound. -/
def localExponent (v k l : ℕ) : ℕ := min v (min k (2 * k / 3 + l))

/-- Lower envelope of the two weighted costs. -/
def denominatorCost (σ θ : ℝ≥0) : ℝ := min (3 * (σ : ℝ) / 2) ((σ : ℝ) + θ / 3)

/-- Nonnegative loss after division by the two Euler weights. -/
def localLoss (σ θ : ℝ≥0) : ℝ := max 0 (1 - denominatorCost σ θ)

/-- The finite valuation constraints imply the sharp weighted cost inequality. -/
theorem localExponent_cost (v k l : ℕ) (σ θ : ℝ≥0) :
    (localExponent v k l : ℝ) * denominatorCost σ θ ≤
      (k : ℝ) * σ + (l : ℝ) * θ := by
  let a : ℝ := localExponent v k l
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hak : a ≤ k := by
    exact_mod_cast (min_le_right v _).trans (min_le_left k (2 * k / 3 + l))
  have hat : a ≤ (2 : ℝ) * k / 3 + l := by
    have hn : localExponent v k l ≤ 2 * k / 3 + l :=
      (min_le_right v _).trans (min_le_right k (2 * k / 3 + l))
    have hd : 3 * (2 * k / 3) ≤ 2 * k := by omega
    have hn' : a ≤ ((2 * k / 3 : ℕ) : ℝ) + l := by exact_mod_cast hn
    have hd' : 3 * ((2 * k / 3 : ℕ) : ℝ) ≤ 2 * k := by exact_mod_cast hd
    linarith only [hn', hd']
  have hm₁ : denominatorCost σ θ ≤ 3 * (σ : ℝ) / 2 := min_le_left _ _
  have hm₂ : denominatorCost σ θ ≤ (σ : ℝ) + θ / 3 := min_le_right _ _
  change a * denominatorCost σ θ ≤ _
  by_cases hk : 3 * a / 2 ≤ (k : ℝ)
  · have h₁ := mul_nonneg (sub_nonneg.mpr hk) σ.coe_nonneg
    have h₂ := mul_nonneg (Nat.cast_nonneg l : (0 : ℝ) ≤ l) θ.coe_nonneg
    have h₃ := mul_nonneg ha (sub_nonneg.mpr hm₁)
    nlinarith only [h₁, h₂, h₃]
  · have h₁ := mul_nonneg (show 0 ≤ 3 * a - 2 * k by linarith only [hk])
      (sub_nonneg.mpr hm₂)
    have h₂ := mul_nonneg (show 0 ≤ 2 * k - 2 * a by linarith only [hak])
      (sub_nonneg.mpr hm₁)
    have h₃ := mul_nonneg (show 0 ≤ (l : ℝ) - (a - 2 * k / 3) by linarith only [hat])
      θ.coe_nonneg
    nlinarith only [h₁, h₂, h₃]

/-- The local Euler quotient loses at most `v` times the exact cost deficit. -/
theorem localExponent_sub_cost (v k l : ℕ) (σ θ : ℝ≥0) :
    (localExponent v k l : ℝ) - (k : ℝ) * σ - (l : ℝ) * θ ≤
      (v : ℝ) * localLoss σ θ := by
  have hc := localExponent_cost v k l σ θ
  have hav : (localExponent v k l : ℝ) ≤ v := by exact_mod_cast (min_le_left v _)
  have ha : (0 : ℝ) ≤ localExponent v k l := Nat.cast_nonneg _
  have hL : 1 - denominatorCost σ θ ≤ localLoss σ θ := le_max_right _ _
  have hL0 : 0 ≤ localLoss σ θ := le_max_left _ _
  have h₁ := mul_le_mul_of_nonneg_left hL ha
  have h₂ := mul_le_mul_of_nonneg_right hav hL0
  nlinarith only [hc, h₁, h₂]

/-- The first extremal integral ray realizes the cost `3σ/2`. -/
theorem first_cost_ray (n : ℕ) : localExponent (2 * n) (3 * n) 0 = 2 * n := by
  unfold localExponent
  omega

/-- The second extremal integral ray realizes the cost `σ + θ/3`. -/
theorem second_cost_ray (n : ℕ) : localExponent (3 * n) (3 * n) n = 3 * n := by
  unfold localExponent
  omega

/-- One of the two integral rays attains the denominator-cost lower bound exactly. -/
theorem cost_attained (n : ℕ) (σ θ : ℝ≥0) :
    ((localExponent (2 * n) (3 * n) 0 : ℝ) * denominatorCost σ θ =
      (3 * n : ℕ) * (σ : ℝ)) ∨
    ((localExponent (3 * n) (3 * n) n : ℝ) * denominatorCost σ θ =
      (3 * n : ℕ) * (σ : ℝ) + n * θ) := by
  rw [first_cost_ray, second_cost_ray]
  unfold denominatorCost
  rcases le_total (3 * (σ : ℝ) / 2) ((σ : ℝ) + θ / 3) with h | h
  · left
    rw [min_eq_left h]
    push_cast
    ring
  · right
    rw [min_eq_right h]
    push_cast
    ring

end GaloisForLFunctions.FamilyContinuationTheory.Quartic

/-
# Power-scale bootstrap in Bourgain's curve decoupling

The recurrence at the end of Bourgain Section 1 is

`b(N) ≲ N^δ b(N^(2/3))`,

not a dyadic additive contraction.  This file proves the exact finite
iteration formula.  It also records that the accumulated exponent loss is at
most `3δ`, since `Σ_{i<k}(2/3)^i ≤ 3`.
-/
import GaloisForLFunctions.RHTower.BourgainSquareRootOsculatingGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Exact `k`-fold iteration of a multiplicative power-scale recurrence. -/
theorem bourgain_powerScale_iterate
    (b : ℝ → ℝ) {C δ α x : ℝ}
    (hC : 0 ≤ C) (hα : 0 ≤ α) (hx : 1 ≤ x)
    (hrec : ∀ y : ℝ, 1 ≤ y →
      b y ≤ C * y ^ δ * b (y ^ α)) :
    ∀ k : ℕ,
      b x ≤ C ^ k *
        x ^ (δ * ∑ i ∈ Finset.range k, α ^ i) *
          b (x ^ (α ^ k)) := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      let y : ℝ := x ^ (α ^ k)
      have hαpow : 0 ≤ α ^ k := pow_nonneg hα k
      have hy : 1 ≤ y := Real.one_le_rpow hx hαpow
      have hr := hrec y hy
      have hpref : 0 ≤ C ^ k *
          x ^ (δ * ∑ i ∈ Finset.range k, α ^ i) := by
        positivity
      have hcombine :
          x ^ (δ * ∑ i ∈ Finset.range k, α ^ i) *
              x ^ (α ^ k * δ) =
            x ^ (δ *
              (∑ i ∈ Finset.range k, α ^ i + α ^ k)) := by
        rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hx)]
        congr 1
        ring
      calc
        b x ≤ C ^ k *
            x ^ (δ * ∑ i ∈ Finset.range k, α ^ i) * b y := by
          simpa only [y] using ih
        _ ≤ C ^ k *
            x ^ (δ * ∑ i ∈ Finset.range k, α ^ i) *
              (C * y ^ δ * b (y ^ α)) :=
          mul_le_mul_of_nonneg_left hr hpref
        _ = C ^ (k + 1) *
            x ^ (δ * ∑ i ∈ Finset.range (k + 1), α ^ i) *
              b (x ^ (α ^ (k + 1))) := by
          dsimp only [y]
          rw [← Real.rpow_mul (le_trans zero_le_one hx),
            ← Real.rpow_mul (le_trans zero_le_one hx)]
          rw [Finset.sum_range_succ, pow_succ, pow_succ]
          rw [show α ^ k * α = α * α ^ k by ring]
          rw [show
            C ^ k * x ^ (δ * ∑ i ∈ Finset.range k, α ^ i) *
                (C * x ^ (α ^ k * δ) *
                  b (x ^ (α * α ^ k))) =
              (C ^ k * C) *
                (x ^ (δ * ∑ i ∈ Finset.range k, α ^ i) *
                  x ^ (α ^ k * δ)) *
                b (x ^ (α * α ^ k)) by ring]
          rw [hcombine]

/-- The geometric exponent loss for Bourgain's scale `α=2/3` is at most
three times the one-step loss. -/
theorem bourgain_twoThirds_geometricSum_le_three (k : ℕ) :
    (∑ i ∈ Finset.range k, (2 / 3 : ℝ) ^ i) ≤ 3 := by
  have hgeom := geom_sum_mul_neg (2 / 3 : ℝ) k
  have hpow : 0 ≤ (2 / 3 : ℝ) ^ k := by positivity
  norm_num at hgeom ⊢
  nlinarith

end

end RHTower

import Mathlib

/-!
# Closed forms for shifted weighted geometric tails

The Wiman--Valiron window estimate carries two tail sums, both starting at index `N + 1` and both
weighted by a power of the index.  Their exact values are classical; what is needed downstream are
the two bounds

`sum_j q^{N+1+j} = q^{N+1} / (1 - q)`,
`sum_j (N+1+j)^2 q^{N+1+j} <= 2 (N+1)^2 q^{N+1} / (1 - q)^3`.

The second uses the negative-binomial series `sum_n C(n+2,2) q^n = (1-q)^{-3}` together with the
elementary comparison `(N+1+j)^2 <= (N+1)^2 (1+j)(2+j)`, which avoids computing the second moment of
the geometric distribution outright.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Twice a binomial coefficient of the second kind is a product of consecutive integers. -/
private theorem two_mul_choose_two (n : ℕ) : 2 * ((n + 2).choose 2) = (n + 1) * (n + 2) := by
  have h := Nat.add_one_mul_choose_eq (n + 1) 1
  rw [Nat.choose_one_right] at h
  calc 2 * ((n + 2).choose 2) = (n + 2).choose 2 * 2 := by ring
    _ = (n + 2) * (n + 1) := h.symm
    _ = (n + 1) * (n + 2) := by ring

/-- **The shifted geometric tail.** -/
theorem tsum_shifted_geom {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    ∑' j : ℕ, q ^ (N + 1 + j) = q ^ (N + 1) / (1 - q) := by
  have h : ∀ j : ℕ, q ^ (N + 1 + j) = q ^ (N + 1) * q ^ j := fun j => by rw [pow_add]
  rw [tsum_congr h, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]

/-- The negative-binomial series of order three, in product form. -/
private theorem tsum_consecutive_mul_geometric {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∑' n : ℕ, ((n : ℝ) + 1) * ((n : ℝ) + 2) * q ^ n = 2 / (1 - q) ^ 3 := by
  have hnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have hchoose := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hnorm
  have hid : ∀ n : ℕ, ((n : ℝ) + 1) * ((n : ℝ) + 2) * q ^ n
      = 2 * ((((n + 2).choose 2 : ℕ) : ℝ) * q ^ n) := by
    intro n
    have h := two_mul_choose_two n
    have hcast : (2 : ℝ) * (((n + 2).choose 2 : ℕ) : ℝ) = ((n : ℝ) + 1) * ((n : ℝ) + 2) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) h
    rw [← mul_assoc, ← hcast]
  rw [tsum_congr hid, tsum_mul_left, hchoose.tsum_eq]
  ring

/-- Summability of the product-weighted geometric series. -/
private theorem summable_consecutive_mul_geometric {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) * ((n : ℝ) + 2) * q ^ n := by
  have hnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have hchoose := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hnorm
  refine (hchoose.summable.mul_left 2).congr fun n => ?_
  have h := two_mul_choose_two n
  have hcast : (2 : ℝ) * (((n + 2).choose 2 : ℕ) : ℝ) = ((n : ℝ) + 1) * ((n : ℝ) + 2) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) h
  rw [← mul_assoc, hcast]

/-- **The shifted geometric tail with a squared weight.** -/
theorem tsum_shifted_sq_weight_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    ∑' j : ℕ, ((N : ℝ) + 1 + j) ^ 2 * q ^ (N + 1 + j)
      ≤ 2 * ((N : ℝ) + 1) ^ 2 * q ^ (N + 1) / (1 - q) ^ 3 := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  have hpow : (0 : ℝ) < q ^ (N + 1) := by positivity
  have hcons := summable_consecutive_mul_geometric hq0 hq1
  -- the pointwise comparison
  have hpt : ∀ j : ℕ, ((N : ℝ) + 1 + j) ^ 2 * q ^ j
      ≤ ((N : ℝ) + 1) ^ 2 * (((j : ℝ) + 1) * ((j : ℝ) + 2) * q ^ j) := by
    intro j
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hqj : (0 : ℝ) < q ^ j := by positivity
    have h1 : (N : ℝ) + 1 + j ≤ ((N : ℝ) + 1) * ((j : ℝ) + 1) := by nlinarith
    have h2 : ((N : ℝ) + 1 + j) ^ 2 ≤ (((N : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2 := by
      have hnn : (0 : ℝ) ≤ (N : ℝ) + 1 + j := by linarith
      nlinarith
    have h3 : (((N : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2
        ≤ ((N : ℝ) + 1) ^ 2 * (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by nlinarith
    nlinarith [h2, h3, hqj]
  have hsummable : Summable fun j : ℕ => ((N : ℝ) + 1 + j) ^ 2 * q ^ j := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) hpt
      (hcons.mul_left (((N : ℝ) + 1) ^ 2))
  have hmid : ∑' j : ℕ, ((N : ℝ) + 1 + j) ^ 2 * q ^ j
      ≤ ((N : ℝ) + 1) ^ 2 * (2 / (1 - q) ^ 3) := by
    refine le_trans (Summable.tsum_le_tsum hpt hsummable (hcons.mul_left _)) ?_
    rw [tsum_mul_left, tsum_consecutive_mul_geometric hq0 hq1]
  have hshift : ∑' j : ℕ, ((N : ℝ) + 1 + j) ^ 2 * q ^ (N + 1 + j)
      = q ^ (N + 1) * ∑' j : ℕ, ((N : ℝ) + 1 + j) ^ 2 * q ^ j := by
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [pow_add]
    ring
  rw [hshift]
  calc q ^ (N + 1) * ∑' j : ℕ, ((N : ℝ) + 1 + j) ^ 2 * q ^ j
      ≤ q ^ (N + 1) * (((N : ℝ) + 1) ^ 2 * (2 / (1 - q) ^ 3)) :=
        mul_le_mul_of_nonneg_left hmid hpow.le
    _ = 2 * ((N : ℝ) + 1) ^ 2 * q ^ (N + 1) / (1 - q) ^ 3 := by
        field_simp

end GaloisForLFunctions.HTGeometry

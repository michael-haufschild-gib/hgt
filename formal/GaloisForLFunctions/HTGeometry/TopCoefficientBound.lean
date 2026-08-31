import GaloisForLFunctions.HTGeometry.PolynomialMagnitudeBalance

/-!
# Bounding the variable by the top coefficient

In a vanishing sum whose terms have magnitudes `A k · t^k`, the leading term is at most the sum of
the others.  When `t ≥ 1` every lower power is at most `t^{n-1}`, so dividing by `t^{n-1}` turns
that into `A n · t ≤ ∑_{j<n} A j`: the variable itself is bounded by the ratio of the lower
coefficients to the leading one.

Applied to `∑ c_k(F)·(F′)^k = 0` with `F′ = W/z` and `|z| = r`, the terms have magnitudes
`|c_k(F)|·(|W|/r)^k`, and the conclusion reads `|W| ≤ r · (∑_{j<n}|c_j(F)|)/|c_n(F)|` — the upper
half of the estimate `ν(r) = O(r)` that an order-one bound needs.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The top-coefficient bound.**  If the leading term of a vanishing sum `∑ b_k = 0` with
`‖b_k‖ = A k · t^k` is dominated by the rest, and `t ≥ 1`, then `t` is bounded by the ratio of the
lower coefficients to the leading one. -/
theorem mul_le_sum_of_top_dominated {n : ℕ} {A : ℕ → ℝ} (hA : ∀ i, 0 ≤ A i)
    {t : ℝ} (ht : 1 ≤ t)
    (hrel : A n * t ^ n ≤ ∑ j ∈ Finset.range n, A j * t ^ j) :
    A n * t ≤ ∑ j ∈ Finset.range n, A j := by
  have ht0 : (0 : ℝ) < t := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Finset.range_zero, Finset.sum_empty, pow_zero, mul_one] at hrel ⊢
    have h0 : A 0 = 0 := le_antisymm hrel (hA 0)
    rw [h0, zero_mul]
  -- divide the relation by `t^{n-1}`
  have hterm : ∀ j ∈ Finset.range n, A j * t ^ j ≤ A j * t ^ (n - 1) := by
    intro j hj
    refine mul_le_mul_of_nonneg_left ?_ (hA j)
    refine pow_le_pow_right₀ ht ?_
    have := Finset.mem_range.mp hj
    omega
  have hsum : ∑ j ∈ Finset.range n, A j * t ^ j
      ≤ (∑ j ∈ Finset.range n, A j) * t ^ (n - 1) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hterm
  have hpow : A n * t ^ n = (A n * t) * t ^ (n - 1) := by
    rw [mul_assoc, ← pow_succ']
    congr 2
    omega
  rw [hpow] at hrel
  have hposn : (0 : ℝ) < t ^ (n - 1) := by positivity
  exact le_of_mul_le_mul_right (by linarith [hrel, hsum]) hposn

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.TopCoefficientBound

/-!
# Two-sided balancing of a vanishing sum

The balancing principle says that in a vanishing sum the largest term is within a factor of the term
count of some other term.  Combining that with the maximality of the largest term pins the variable:
if the terms are `A k · t^k`, and index `k` is maximal with partner `j`, then

```text
A u / ((n+1) A v) ≤ t^{v-u} ≤ (n+1) · A u / A v
```

where `{u, v} = {j, k}` ordered.  Both inequalities come from the same two facts read in opposite
directions — maximality gives one, the balancing partner the other — so the exponent `v − u` and the
coefficient ratio determine `t` up to a bounded factor.

This is the step that converts an algebraic relation into a growth law: with `t = |W|/r` and
`A k = |c_k(F)|`, it says `|W|/r` is comparable to a fixed power of the maximum modulus.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Two-sided balancing.**  If the term at index `k` is maximal and is within a factor `n+1` of the
term at a different index `j`, then the corresponding power of `t` is pinned two-sidedly by the ratio
of the two coefficients. -/
theorem exists_pow_between_of_balanced {n : ℕ} {A : ℕ → ℝ}
    {t : ℝ} (ht : 0 < t) {k j : ℕ} (hkn : k ≤ n) (hjn : j ≤ n) (hkj : j ≠ k)
    (hAk : 0 < A k) (hAj : 0 < A j)
    (hmax : A j * t ^ j ≤ A k * t ^ k)
    (hbal : A k * t ^ k ≤ ((n : ℝ) + 1) * (A j * t ^ j)) :
    ∃ u v : ℕ, u < v ∧ v ≤ n ∧ 0 < A u ∧ 0 < A v ∧
      A u / (((n : ℝ) + 1) * A v) ≤ t ^ (v - u) ∧ t ^ (v - u) ≤ ((n : ℝ) + 1) * (A u / A v) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rcases lt_or_gt_of_ne hkj with hjk | hkj'
  · -- `j < k`
    refine ⟨j, k, hjk, hkn, hAj, hAk, ?_, ?_⟩
    · -- lower bound from maximality
      have hsplit : t ^ k = t ^ j * t ^ (k - j) := by
        rw [pow_mul_pow_sub t hjk.le]
      rw [hsplit] at hmax
      have htj : (0 : ℝ) < t ^ j := by positivity
      have hstep : A j ≤ A k * t ^ (k - j) := by
        nlinarith [hmax, htj]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hstep, hAk, hn1, pow_pos ht (k - j)]
    · -- upper bound from the balancing partner
      have hsplit : t ^ k = t ^ j * t ^ (k - j) := by
        rw [pow_mul_pow_sub t hjk.le]
      rw [hsplit] at hbal
      have htj : (0 : ℝ) < t ^ j := by positivity
      have hstep : A k * t ^ (k - j) ≤ ((n : ℝ) + 1) * A j := by
        nlinarith [hbal, htj]
      rw [mul_div_assoc', le_div_iff₀ hAk]
      nlinarith [hstep]
  · -- `k < j`
    refine ⟨k, j, hkj', hjn, hAk, hAj, ?_, ?_⟩
    · have hsplit : t ^ j = t ^ k * t ^ (j - k) := by
        rw [pow_mul_pow_sub t hkj'.le]
      rw [hsplit] at hbal
      have htk : (0 : ℝ) < t ^ k := by positivity
      have hstep : A k ≤ ((n : ℝ) + 1) * (A j * t ^ (j - k)) := by
        nlinarith [hbal, htk]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hstep, hAj, hn1]
    · have hsplit : t ^ j = t ^ k * t ^ (j - k) := by
        rw [pow_mul_pow_sub t hkj'.le]
      rw [hsplit] at hmax
      have htk : (0 : ℝ) < t ^ k := by positivity
      have hstep : A j * t ^ (j - k) ≤ A k := by
        nlinarith [hmax, htk]
      rw [mul_div_assoc', le_div_iff₀ hAj]
      nlinarith [hstep, hn1, pow_pos ht (j - k)]

end GaloisForLFunctions.HTGeometry

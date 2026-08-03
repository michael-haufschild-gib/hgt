import GaloisForLFunctions.RHTower.Sieve.DirichletKernelBound

/-!
# Abel's inequality

If the partial sums of `g` never exceed `B` in absolute value and `w` is nonnegative and
nonincreasing, then

`|∑_{i < n} w i · g i| ≤ B · w 0`.

Summation by parts writes the weighted sum as `w_{n-1} S_n` minus a sum of increments
`(w_{i+1} - w_i) S_{i+1}`; the increments are nonpositive, so their absolute values telescope to
`w_0 - w_{n-1}`, and every partial sum is capped by `B`.

This is Dirichlet's test in quantitative form.  Applied with `g d = sin(dθ)` — whose partial sums
`DirichletKernelBound.lean` caps by `1/|sin(θ/2)|` — and `w d = 1/(d+1)`, it is the estimate that
turns the Toeplitz kernel `1/(m-n)` into a bounded Fourier multiplier.
-/

namespace RHTower.Sieve

open Finset

/-- **Abel's inequality.**  Bounded partial sums against a nonincreasing nonnegative weight. -/
theorem abs_sum_mul_le_of_bounded_partial {g w : ℕ → ℝ} {B : ℝ} (n : ℕ)
    (hB : ∀ k, |∑ j ∈ Finset.range k, g j| ≤ B)
    (hw0 : ∀ i, 0 ≤ w i) (hwanti : ∀ i, w (i + 1) ≤ w i) :
    |∑ i ∈ Finset.range n, w i * g i| ≤ B * w 0 := by
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hparts := Finset.sum_range_by_parts w g n
  simp only [smul_eq_mul] at hparts
  rw [hparts]
  have hhead : |w (n - 1) * ∑ i ∈ Finset.range n, g i| ≤ w (n - 1) * B := by
    rw [abs_mul, abs_of_nonneg (hw0 (n - 1))]
    exact mul_le_mul_of_nonneg_left (hB n) (hw0 (n - 1))
  have htail : |∑ i ∈ Finset.range (n - 1),
      (w (i + 1) - w i) * ∑ j ∈ Finset.range (i + 1), g j| ≤ B * (w 0 - w (n - 1)) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ i ∈ Finset.range (n - 1),
        |(w (i + 1) - w i) * ∑ j ∈ Finset.range (i + 1), g j| ≤ B * (w i - w (i + 1)) := by
      intro i _
      rw [abs_mul]
      have habs : |w (i + 1) - w i| = w i - w (i + 1) := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [hwanti i])]
      rw [habs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hB (i + 1)) (by linarith [hwanti i])
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum, Finset.sum_range_sub' w (n - 1)]
  have hsub : |w (n - 1) * ∑ i ∈ Finset.range n, g i
      - ∑ i ∈ Finset.range (n - 1),
          (w (i + 1) - w i) * ∑ j ∈ Finset.range (i + 1), g j|
      ≤ |w (n - 1) * ∑ i ∈ Finset.range n, g i|
        + |∑ i ∈ Finset.range (n - 1),
            (w (i + 1) - w i) * ∑ j ∈ Finset.range (i + 1), g j| := abs_sub _ _
  have hmono : w (n - 1) ≤ w 0 :=
    (antitone_nat_of_succ_le hwanti) (Nat.zero_le (n - 1))
  nlinarith [hhead, htail, hsub, hBnn, hw0 (n - 1)]

end RHTower.Sieve

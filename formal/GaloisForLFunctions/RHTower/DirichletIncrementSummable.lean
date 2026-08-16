import GaloisForLFunctions.RHTower.DirichletKernelEstimate

/-!
# The Dirichlet kernel increments are absolutely summable

The increments `n^{−s} − (n+1)^{−s}` of the Dirichlet kernel are absolutely summable in the open
half-plane `Re s > 0`, with total mass at most `‖s‖ / Re s`.  The reason is the increment estimate
together with the fact that the real increments telescope: their partial sums are
`1 − (N+1)^{−Re s} ≤ 1`.

This is the second ingredient of Abel summation for Dirichlet series — the first being the increment
estimate itself, and the third the vanishing of the boundary term `N^{−Re s} → 0`, also proved here.
Together they give: bounded coefficient partial sums imply convergence throughout `Re s > 0`.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- The real kernel increments telescope, so they are summable with total mass at most one. -/
theorem summable_rpow_neg_increment {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-σ) - ((n : ℝ) + 2) ^ (-σ)) := by
  refine summable_of_sum_range_le (c := 1) (fun n => ?_) (fun n => ?_)
  · have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : ((n : ℝ) + 1) ≤ ((n : ℝ) + 2) := by linarith
    have h := Real.rpow_le_rpow_of_nonpos h1 h2 (neg_nonpos.2 hσ.le)
    linarith
  · have hf : ∀ i : ℕ, ((i : ℝ) + 1) ^ (-σ) - ((i : ℝ) + 2) ^ (-σ)
        = (fun k : ℕ => ((k : ℝ) + 1) ^ (-σ)) i
          - (fun k : ℕ => ((k : ℝ) + 1) ^ (-σ)) (i + 1) := by
      intro i
      push_cast
      ring_nf
    rw [Finset.sum_congr rfl (fun i _ => hf i),
      Finset.sum_range_sub' (fun k : ℕ => ((k : ℝ) + 1) ^ (-σ)) n]
    have hzero : (((0 : ℕ) : ℝ) + 1) ^ (-σ) = 1 := by
      norm_num
    have hnn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (-σ) := by positivity
    rw [hzero]
    linarith

/-- **The Dirichlet kernel increments are absolutely summable in the right half-plane.** -/
theorem summable_norm_cpow_increment {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ =>
      ‖((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((n : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_rpow_neg_increment hs).mul_left (‖s‖ / s.re))
  exact norm_cpow_neg_sub_le hs (by positivity) (by linarith)

/-- The boundary term of Abel summation vanishes. -/
theorem tendsto_rpow_neg_nat_atTop {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun N : ℕ => ((N : ℝ)) ^ (-σ)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hσ).comp tendsto_natCast_atTop_atTop

/-- The total mass of the increments is at most `‖s‖ / Re s`. -/
theorem tsum_norm_cpow_increment_le {s : ℂ} (hs : 0 < s.re) :
    (∑' n : ℕ, ‖((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((n : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)‖)
      ≤ (‖s‖ / s.re) * 1 := by
  refine Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) fun N => ?_
  have hbound : ∀ n : ℕ,
      ‖((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((n : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)‖
        ≤ (‖s‖ / s.re) * (((n : ℝ) + 1) ^ (-s.re) - ((n : ℝ) + 2) ^ (-s.re)) :=
    fun n => norm_cpow_neg_sub_le hs (by positivity) (by linarith)
  refine (Finset.sum_le_sum fun n _ => hbound n).trans ?_
  rw [← Finset.mul_sum]
  have hf : ∀ i : ℕ, ((i : ℝ) + 1) ^ (-s.re) - ((i : ℝ) + 2) ^ (-s.re)
      = (fun k : ℕ => ((k : ℝ) + 1) ^ (-s.re)) i
        - (fun k : ℕ => ((k : ℝ) + 1) ^ (-s.re)) (i + 1) := by
    intro i
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl (fun i _ => hf i),
    Finset.sum_range_sub' (fun k : ℕ => ((k : ℝ) + 1) ^ (-s.re)) N]
  have hzero : (((0 : ℕ) : ℝ) + 1) ^ (-s.re) = 1 := by norm_num
  have hnn : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ (-s.re) := by positivity
  have hc : (0 : ℝ) ≤ ‖s‖ / s.re := by positivity
  rw [hzero]
  nlinarith [hc, hnn]

end GaloisForLFunctions.RHTower

end

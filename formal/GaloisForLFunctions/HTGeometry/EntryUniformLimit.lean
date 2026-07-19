import GaloisForLFunctions.HTGeometry.NevanlinnaEntire

/-!
# Uniform convergence of the entry series

The holomorphy proof for the limiting entries already establishes a uniform Cauchy estimate on any
set carrying uniform kernel bounds; only its differentiability consequence was recorded.  The uniform
convergence itself is what identifies the support of a weak limit, so it is extracted here.

Combined with the ball bounds this gives uniform convergence of each entry series on every ball —
uniformly, not merely locally uniformly.
-/

open scoped BigOperators
open Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The bilinear partial sums converge uniformly** on any set carrying a uniform kernel bound. -/
theorem tendstoUniformlyOn_bilinearLimit (h : PositiveMomentForm s) (f : ℕ → ℂ) {Kf Kg : ℝ}
    (hf : ∀ n, kernelRoot s f n ≤ Kf)
    (G : ℂ → ℕ → ℂ) (U : Set ℂ) (hG : ∀ z ∈ U, ∀ n, kernelRoot s (G z) n ≤ Kg) :
    TendstoUniformlyOn (bilinearPartialSum s f G)
      (fun z => ∑' k, f k * G z k /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)) atTop U := by
  have hfs := summable_normSq_of_kernelRoot_le h f hf
  have hcauchy := uniformCauchySeqOn_bilinearPartialSum h f hfs Kg G U hG
  refine hcauchy.tendstoUniformlyOn_of_tendsto ?_
  intro z hz
  exact (summable_weighted_of_bounds h f (G z) hf (hG z hz)).hasSum.tendsto_sum_nat

/-- **The `D` series converges uniformly on every ball.** -/
theorem tendstoUniformlyOn_nevD_series (h : PositiveMomentForm s) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j 0) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j 0) N ≤ P) (r : ℝ) :
    TendstoUniformlyOn
      (bilinearPartialSum s (fun k => monicOrthoC s k 0) (fun z k => monicOrthoC s k z))
      (fun z => ∑' k, monicOrthoC s k 0 * monicOrthoC s k z /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
      atTop (Metric.ball 0 r) := by
  refine tendstoUniformlyOn_bilinearLimit (Kg := ballBoundQ s S P r) h _ hS _ _ ?_
  intro z hz N
  have hnorm : ‖z‖ ≤ r := by
    have := Metric.mem_ball.mp hz
    rw [dist_zero_right] at this
    exact this.le
  exact kernelRoot_le_ballBoundQ h hS hP hnorm N

/-- **The `B` series converges uniformly on every ball.**  Indexed with the constant factor first;
the summand differs from the `B` entry's by a commutation. -/
theorem tendstoUniformlyOn_nevB_series (h : PositiveMomentForm s) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j 0) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j 0) N ≤ P) (r : ℝ) :
    TendstoUniformlyOn
      (bilinearPartialSum s (fun k => secondKindC s k 0) (fun z k => monicOrthoC s k z))
      (fun z => ∑' k, secondKindC s k 0 * monicOrthoC s k z /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
      atTop (Metric.ball 0 r) := by
  refine tendstoUniformlyOn_bilinearLimit (Kg := ballBoundQ s S P r) h _ hP _ _ ?_
  intro z hz N
  have hnorm : ‖z‖ ≤ r := by
    have := Metric.mem_ball.mp hz
    rw [dist_zero_right] at this
    exact this.le
  exact kernelRoot_le_ballBoundQ h hS hP hnorm N

/-- The `B` summand in the order the entry uses. -/
theorem bilinearPartialSum_secondKind_comm (s : ℕ → ℝ) (N : ℕ) (z : ℂ) :
    bilinearPartialSum s (fun k => secondKindC s k 0) (fun z k => monicOrthoC s k z) N z
      = ∑ k ∈ Finset.range N, monicOrthoC s k z * secondKindC s k 0 /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
  rw [bilinearPartialSum]
  exact Finset.sum_congr rfl fun k _ => by ring

end HTGeometry

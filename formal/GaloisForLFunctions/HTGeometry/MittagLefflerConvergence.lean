import GaloisForLFunctions.HTGeometry.TaylorPartialSumApproximation

/-!
# The convergence engine of the Mittag-Leffler construction

A series of corrected principal parts converges because each term is small on a disc whose radius
grows without bound.  Two facts are all that is needed.

* At any point the series is summable: all but finitely many terms are within the disc where their
  bound applies.
* On any fixed disc the tail beyond a suitable index consists of terms holomorphic there and
  dominated by a summable sequence, so it converges uniformly and its sum is holomorphic.

Splitting a fixed disc into that holomorphic tail and a finite head is what exhibits the sum as
meromorphic with exactly the prescribed principal parts.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Filter

/-- **Pointwise summability.**  Beyond the index where the radius passes the point, every term is
dominated by a summable sequence. -/
theorem summable_of_growing_radii {g : ℕ → ℂ → ℂ} {u : ℕ → ℝ} {R : ℕ → ℝ}
    (hu : Summable u) (hR : Tendsto R atTop atTop)
    (hg : ∀ n z, ‖z‖ < R n → ‖g n z‖ ≤ u n) (z : ℂ) :
    Summable fun n => g n z := by
  refine Summable.of_norm_bounded_eventually_nat hu ?_
  filter_upwards [hR.eventually_gt_atTop ‖z‖] with n hn
  exact hg n z hn

/-- The tail of the series, reindexed from a cut-off. -/
noncomputable def seriesTail (g : ℕ → ℂ → ℂ) (N : ℕ) : ℂ → ℂ :=
  fun z => ∑' k : ℕ, g (k + N) z

/-- **The tail is holomorphic on a disc where all its terms are.** -/
theorem differentiableOn_seriesTail {g : ℕ → ℂ → ℂ} {u : ℕ → ℝ} {M : ℝ} {N : ℕ}
    (hu : Summable u)
    (hgd : ∀ k : ℕ, DifferentiableOn ℂ (g (k + N)) (ball (0 : ℂ) M))
    (hgb : ∀ (k : ℕ), ∀ z ∈ ball (0 : ℂ) M, ‖g (k + N) z‖ ≤ u (k + N)) :
    DifferentiableOn ℂ (seriesTail g N) (ball (0 : ℂ) M) := by
  have husub : Summable fun k : ℕ => u (k + N) :=
    (summable_nat_add_iff N).mpr hu
  have htu : TendstoUniformlyOn (fun (t : Finset ℕ) (z : ℂ) => ∑ k ∈ t, g (k + N) z)
      (seriesTail g N) atTop (ball (0 : ℂ) M) :=
    tendstoUniformlyOn_tsum husub hgb
  refine (htu.tendstoLocallyUniformlyOn).differentiableOn ?_ isOpen_ball
  filter_upwards with t
  have h : DifferentiableOn ℂ (∑ k ∈ t, fun z : ℂ => g (k + N) z) (ball (0 : ℂ) M) :=
    DifferentiableOn.sum fun k _ => hgd k
  have heq : (∑ k ∈ t, fun z : ℂ => g (k + N) z) = fun z : ℂ => ∑ k ∈ t, g (k + N) z := by
    funext z
    exact Finset.sum_apply z t _
  rwa [heq] at h

/-- **Head–tail splitting.**  The full series is a finite head plus the tail. -/
theorem tsum_eq_head_add_seriesTail {g : ℕ → ℂ → ℂ} {z : ℂ} (N : ℕ)
    (hs : Summable fun n => g n z) :
    ∑' n : ℕ, g n z = (∑ n ∈ Finset.range N, g n z) + seriesTail g N z := by
  rw [seriesTail]
  exact (hs.sum_add_tsum_nat_add N).symm

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.EntryNumeratorUniform

/-!
# The truncated entries converge at every complex point

The uniform estimates are stated on complex balls; only their `ofReal` specialisations were restricted
to the real axis.  Packaging the truncations as complex functions and reading the estimates at a
complex point gives convergence of all four entries on all of `ℂ`.
-/

open scoped BigOperators
open Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The truncated `A` entry as a complex function. -/
noncomputable def nevAtruncC (s : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
    bilinearPartialSum s (fun k => secondKindC s k 0) (fun w k => secondKindC s k w) (n + 1) z

/-- The truncated `B` entry as a complex function. -/
noncomputable def nevBtruncC (s : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  -1 + ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
    bilinearPartialSum s (fun k => secondKindC s k 0) (fun w k => monicOrthoC s k w) (n + 1) z

/-- The truncated `C` entry as a complex function. -/
noncomputable def nevCtruncC (s : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  1 + ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
    bilinearPartialSum s (fun k => monicOrthoC s k 0) (fun w k => secondKindC s k w) (n + 1) z

/-- The truncated `D` entry as a complex function. -/
noncomputable def nevDtruncC (s : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
    bilinearPartialSum s (fun k => monicOrthoC s k 0) (fun w k => monicOrthoC s k w) (n + 1) z

/-- Membership of a point in a ball of radius exceeding its norm. -/
theorem mem_ball_norm_add_one (z : ℂ) : z ∈ Metric.ball (0 : ℂ) (‖z‖ + 1) := by
  rw [Metric.mem_ball, dist_zero_right]
  linarith

/-- **The truncated `D` entry converges to the limiting one at every complex point.** -/
theorem tendsto_nevDtruncC (h : PositiveMomentForm s) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j 0) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j 0) N ≤ P) (z : ℂ) :
    Tendsto (fun n => nevDtruncC s n z) atTop (nhds (nevDinf s z)) := by
  have huni := tendstoUniformlyOn_nevD_series h hS hP (‖z‖ + 1)
  have hpt := huni.tendsto_at (mem_ball_norm_add_one z)
  have hshift := hpt.comp (Filter.tendsto_add_atTop_nat 1)
  exact (hshift.const_mul _)

/-- **The truncated `A` entry converges at every complex point.** -/
theorem tendsto_nevAtruncC (h : PositiveMomentForm s) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j 0) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j 0) N ≤ P) (z : ℂ) :
    Tendsto (fun n => nevAtruncC s n z) atTop (nhds (nevAinf s z)) := by
  have huni := tendstoUniformlyOn_nevA_series h hS hP (‖z‖ + 1)
  have hpt := huni.tendsto_at (mem_ball_norm_add_one z)
  have hshift := hpt.comp (Filter.tendsto_add_atTop_nat 1)
  exact (hshift.const_mul _)

/-- **The truncated `C` entry converges at every complex point.** -/
theorem tendsto_nevCtruncC (h : PositiveMomentForm s) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j 0) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j 0) N ≤ P) (z : ℂ) :
    Tendsto (fun n => nevCtruncC s n z) atTop (nhds (nevCinf s z)) := by
  have huni := tendstoUniformlyOn_nevC_series h hS hP (‖z‖ + 1)
  have hpt := huni.tendsto_at (mem_ball_norm_add_one z)
  have hshift := hpt.comp (Filter.tendsto_add_atTop_nat 1)
  exact ((hshift.const_mul _).const_add _)

/-- **The truncated `B` entry converges at every complex point.** -/
theorem tendsto_nevBtruncC (h : PositiveMomentForm s) {S P : ℝ}
    (hS : ∀ N, kernelRoot s (fun j => monicOrthoC s j 0) N ≤ S)
    (hP : ∀ N, kernelRoot s (fun j => secondKindC s j 0) N ≤ P) (z : ℂ) :
    Tendsto (fun n => nevBtruncC s n z) atTop (nhds (nevBinf s z)) := by
  have huni := tendstoUniformlyOn_nevB_series h hS hP (‖z‖ + 1)
  have hpt := huni.tendsto_at (mem_ball_norm_add_one z)
  have hshift := hpt.comp (Filter.tendsto_add_atTop_nat 1)
  have hlim : nevBinf s z
      = -1 + ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
          ∑' k, secondKindC s k 0 * monicOrthoC s k z /
            ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) :=
    nevBinf_comm_tsum s z
  rw [hlim]
  exact ((hshift.const_mul _).const_add _)

end HTGeometry

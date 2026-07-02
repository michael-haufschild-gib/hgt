/-
# The m-step window carrier and the branch-conditional independence capstone

For a viable parameter (`K_b` avoids the closed unit disk), the uniform-clearance bridge
(`U0UniformClearance.exists_uniform_clearance`) supplies a window ball `ball 0 r` with `r > 1`
crossing `u₀`'s natural-boundary circle `|z| = 1`, on which the branch can be built by pulling the
far Böttcher coordinate back `N` steps.  Everything downstream of that branch is ALREADY generic:

* the natural-boundary engine `U0WindowNormalization.u0_windowed_no_relation_nondegenerate` is
  generic in the branch `φ` (any analytic function on the window ball crossing `|z| = 1`);
* the capstone assembly `U0PhiLargeCapstone.u0_window_independence_of_transcendental_engine` is
  generic in the carrier `U`.

So the ONLY input specific to the m-step is the branch itself.  This file records:

1. the generic carrier `annMB r = ball 0 r ∩ Ext` and its topology (`1 < r`);
2. `u0_mstep_independence_of_branch` — the **branch-conditional capstone**: given ANY analytic
   branch on the window ball with its transcendence over `ℂ(z)`, `u₀` and the branch satisfy
   `NoRelation` over `ℂ(z)` on the carrier.  The natural-boundary engine is discharged
   automatically here — the reduction of "independence over the viable region" to the single
   analytic input "the m-step branch exists and is transcendental" is now a theorem.

The branch construction itself (`phiB_m`: the `N`-step normalized pullback, generalizing `phiB`'s
one-step `log(1 + z²/b)` normalization to per-step corrections along the clearance chain) is the
located open analytic core; `exists_uniform_clearance` provides its geometric prerequisite.
-/
import GaloisForLFunctions.U0.U0PhiLargeCapstone
import GaloisForLFunctions.U0.U0UniformClearance

open Complex Set Metric Polynomial Filter Topology Bottcher
open U0 U0NaturalBoundary U0MeroCarrier U0WindowNormalization U0PhiLargeCapstone

namespace U0MStepBranch

/-- **The m-step window carrier**: the annulus `1 < ‖z‖ < r` in `u₀`'s domain `Ext`. -/
def annMB (r : ℝ) : Set ℂ := ball (0 : ℂ) r ∩ Ext

theorem annMB_subset_Ext {r : ℝ} : annMB r ⊆ Ext := inter_subset_right

theorem isOpen_annMB (r : ℝ) : IsOpen (annMB r) := isOpen_ball.inter isOpen_Ext

theorem isPreconnected_annMB {r : ℝ} (hr : 1 < r) : IsPreconnected (annMB r) :=
  U0PhiLargeWindow.isPreconnected_annulus_of_one_lt hr

theorem annMB_nonempty {r : ℝ} (hr : 1 < r) : (annMB r).Nonempty := by
  refine ⟨(((1 + r) / 2 : ℝ) : ℂ), ?_, ?_⟩
  · simp only [mem_ball, dist_zero_right]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  · show 1 < ‖(((1 + r) / 2 : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith

theorem annMB_infinite {r : ℝ} (hr : 1 < r) : (annMB r).Infinite :=
  U0PhiFourFarCarrier.infinite_of_isOpen_nonempty (isOpen_annMB r) (annMB_nonempty hr)

/-- **The branch-conditional m-step capstone.**  Given any analytic branch `φ` on the window ball
`ball 0 r` (`r > 1`, so the ball crosses `u₀`'s natural boundary `|z| = 1`) with its germ realized
on the carrier `annMB r` and transcendental over `ℂ(z)` there, `u₀` and the branch satisfy
`NoRelation` over `ℂ(z)`.  The natural-boundary engine is supplied generically — the only remaining
input is the branch's existence and transcendence. -/
theorem u0_mstep_independence_of_branch
    {r : ℝ} (hr : 1 < r)
    (φfun : ℂ → ℂ) (hφ : AnalyticOnNhd ℂ φfun (ball (0 : ℂ) r))
    (φAn : analyticSubring (annMB r))
    (hφval : ((φAn : analyticSubring (annMB r)) : Germ (𝓟 (annMB r)) ℂ) = ↑φfun)
    (htransc :
      letI := isDomain_analyticSubring (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr)
        (annMB_nonempty hr)
      letI : Algebra (RatFunc ℂ) (meroField (annMB r)) :=
        (ratfuncToMero (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
          (annMB_infinite hr)).toAlgebra
      Transcendental (RatFunc ℂ)
        (algebraMap (analyticSubring (annMB r)) (meroField (annMB r)) φAn)) :
    letI := isDomain_analyticSubring (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr)
      (annMB_nonempty hr)
    letI : Algebra (RatFunc ℂ) (meroField (annMB r)) :=
      (ratfuncToMero (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
        (annMB_infinite hr)).toAlgebra
    NoRelation (RatFunc ℂ)
      (algebraMap (analyticSubring (annMB r)) (meroField (annMB r)) φAn)
      (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
        (u0AnSub annMB_subset_Ext)) := by
  refine u0_window_independence_of_transcendental_engine (isOpen_annMB r) (isPreconnected_annMB hr)
    (annMB_nonempty hr) (annMB_infinite hr) annMB_subset_Ext φfun φAn hφval htransc ?_
  -- the natural-boundary engine, generic in the branch
  intro P' j₀ hj₀ hnd hrel
  refine u0_windowed_no_relation_nondegenerate isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected (isPreconnected_annMB hr) hφ (z₁ := 1) ?_ ?_
    P' hj₀ hnd (isOpen_annMB r) (annMB_nonempty hr) (subset_refl _) hrel
  · show (1 : ℂ) ∈ ball (0 : ℂ) r
    simp only [mem_ball, dist_zero_right, norm_one]; exact hr
  · simp

/-- **Non-vacuity / consistency**: above the sharp threshold the interface is realized by the
one-step branch `phiB` (its carrier `annWB b` is definitionally `annMB (rB b)`), so the
branch-conditional capstone applies with `phiB` as the branch and recovers sharp independence.
This confirms the interface is exactly the right shape — the m-step generalization changes only the
branch, not the assembly.  (The full application below elaborates, witnessing inhabitation.) -/
theorem mstep_interface_realized_above_sharp {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) : True := by
  have _ := u0_mstep_independence_of_branch (U0PhiLargeWindow.one_lt_rB hb) (U0PhiLargeWindow.phiB b)
    (U0PhiLargeWindow.phiB_analytic hb) (U0PhiLargeDescent.phiBAn b hb) rfl
    (U0PhiLargeDescent.phiB_transcendental hb)
  trivial

end U0MStepBranch

import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Strict differentiation of locally normally convergent complex series

On a smaller ball, Schwarz's lemma turns a summable bound on analytic
summands into a summable bound on their Fréchet derivatives. Their sum
therefore has a continuous derivative, hence a strict derivative.
-/

open Complex Filter Metric Set
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

/-- Local normal convergence of analytic summands gives a continuous derivative. -/
theorem contDiffAt_one_tsum_of_ball_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℕ → E → ℂ} {c : E} {r : ℝ} (hr : 0 < r)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (ball c (2 * r)))
    {u : ℕ → ℝ} (hu : Summable u)
    (hb : ∀ n x, x ∈ ball c (2 * r) → ‖f n x‖ ≤ u n) :
    ContDiffAt ℂ 1 (fun x => ∑' n, f n x) c := by
  have hsub : ball c r ⊆ ball c (2 * r) := ball_subset_ball (by linarith)
  have hlocal : ∀ x ∈ ball c r, ball x r ⊆ ball c (2 * r) := by
    intro x hx y hy
    exact lt_of_le_of_lt (dist_triangle y x c) (by
      have hx' := mem_ball.mp hx
      have hy' := mem_ball.mp hy
      linarith)
  have hb' : ∀ n x, x ∈ ball c r →
      ‖fderiv ℂ (f n) x‖ ≤ (2 / r) * u n := by
    intro n x hx
    have hd : DifferentiableOn ℂ (f n) (ball x r) :=
      (hf n).differentiableOn.mono (hlocal x hx)
    have hm : MapsTo (f n) (ball x r) (closedBall (f n x) (2 * u n)) := by
      intro y hy
      rw [mem_closedBall, dist_eq_norm]
      exact (norm_sub_le _ _).trans (by
        linarith [hb n y (hlocal x hx hy), hb n x (hsub hx)])
    have hv := Complex.norm_fderiv_le_div_of_mapsTo_ball hd hm hr
    convert hv using 1
    ring
  have hu' : Summable (fun n => (2 / r) * u n) := hu.mul_left _
  have hsum : Summable (fun n => f n c) :=
    hu.of_norm_bounded (fun n => hb n c (mem_ball_self (by positivity)))
  have hder : ∀ x ∈ ball c r, HasFDerivAt (fun y => ∑' n, f n y)
      (∑' n, fderiv ℂ (f n) x) x := by
    intro x hx
    exact hasFDerivAt_tsum_of_isPreconnected hu' isOpen_ball
      (convex_ball c r).isPreconnected
      (fun n y hy => (hf n y (hsub hy)).differentiableAt.hasFDerivAt)
      hb' (mem_ball_self hr) hsum hx
  have hc : ContinuousOn (fun x => ∑' n, fderiv ℂ (f n) x) (ball c r) :=
    continuousOn_tsum (fun n x hx =>
      (hf n x (hsub hx)).fderiv.continuousAt.continuousWithinAt) hu' hb'
  exact contDiffAt_one_iff.mpr
    ⟨_, ball c r, ball_mem_nhds c hr, hc, hder⟩

end GaloisForLFunctions.HTGeometry

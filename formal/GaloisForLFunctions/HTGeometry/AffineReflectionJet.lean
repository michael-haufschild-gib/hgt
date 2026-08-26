import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic

/-!
# Jets under affine reflection

This module isolates the local analytic chain rule for `z ↦ 1 - z`. It is shared by
projective-horizon caustics and reflected bi-heat channels, avoiding a dependency from generic
HT-geometry infrastructure back into the Riemann--Hilbert tower.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Local affine chain rule for reflection about `1/2`. -/
theorem iteratedDeriv_comp_one_sub_of_analyticAt :
    ∀ (n : ℕ) {f : ℂ → ℂ} {z : ℂ}, AnalyticAt ℂ f (1 - z) →
      iteratedDeriv n (fun w => f (1 - w)) z =
        (-1 : ℂ) ^ n * iteratedDeriv n f (1 - z) := by
  intro n
  induction n with
  | zero =>
      intro f z _
      simp [iteratedDeriv_zero]
  | succ n ih =>
      intro f z hf
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      have hdiff : ∀ᶠ u in nhds (1 - z), DifferentiableAt ℂ f u := by
        have h := (hf.contDiffAt (n := (1 : ℕ∞))).eventually (by simp)
        filter_upwards [h] with u hu
        exact hu.differentiableAt (by simp)
      have hpre : ∀ᶠ w in nhds z, DifferentiableAt ℂ f (1 - w) :=
        (continuousAt_const.sub continuousAt_id).tendsto hdiff
      have hderiv : deriv (fun w : ℂ => f (1 - w)) =ᶠ[nhds z]
          fun w : ℂ => -deriv f (1 - w) := by
        filter_upwards [hpre] with w hw
        have hinner : HasDerivAt (fun u : ℂ => 1 - u) (-1) w := by
          simpa using (hasDerivAt_id w).const_sub 1
        simpa [Function.comp_def] using (hw.hasDerivAt.comp w hinner).deriv
      rw [hderiv.iteratedDeriv_eq n]
      change iteratedDeriv n (-(fun w : ℂ => deriv f (1 - w))) z = _
      rw [iteratedDeriv_neg, ih hf.deriv]
      ring

end GaloisForLFunctions.HTGeometry

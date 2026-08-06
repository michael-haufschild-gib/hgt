import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The zero set of an analytic function on a ball is finite

A function analytic on a closed ball and not identically zero has finitely many zeros in the open
ball.  Zeros of an analytic function are isolated, and the closed ball is compact; the divisor
machinery packages both facts, since for a function in meromorphic normal form the zero set *is* the
support of the divisor.

The non-degeneracy hypothesis is the usual one: the function is nonzero somewhere on the ball.  A
ball is preconnected, so the identity theorem upgrades that to "nowhere locally zero".
-/

namespace HTGeometry

open Metric

/-- On a ball, a single nonzero value forbids local vanishing anywhere. -/
theorem eventually_ne_zero_of_analyticOnNhd_ball {f : ℂ → ℂ} {c z₀ u : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball c R)) (hz₀ : z₀ ∈ ball c R) (hfz₀ : f z₀ ≠ 0)
    (hu : u ∈ ball c R) :
    ∀ᶠ z in nhdsWithin u {u}ᶜ, f z ≠ 0 := by
  rcases (hf u hu).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso
    have hEq : Set.EqOn f 0 (ball c R) :=
      hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero (isPreconnected_ball) hu hzero
    exact hfz₀ (hEq hz₀)
  · exact hne

/-- **Finiteness of the zero set.**  An analytic function on a closed ball that is nonzero somewhere
on the open ball has finitely many zeros there. -/
theorem finite_zeros_of_analyticOnNhd_closedBall {f : ℂ → ℂ} {c z₀ : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hz₀ : z₀ ∈ ball c R) (hfz₀ : f z₀ ≠ 0) :
    (ball c R ∩ f ⁻¹' {0}).Finite := by
  have hfball : AnalyticOnNhd ℂ f (ball c R) := fun z hz => hf z (ball_subset_closedBall hz)
  have hNF : MeromorphicNFOn f (ball c R) := hfball.meromorphicNFOn
  have hord : ∀ u : ball c R, meromorphicOrderAt f (u : ℂ) ≠ ⊤ := by
    rintro ⟨u, hu⟩
    exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (hfball u hu).meromorphicAt).mpr
        (eventually_ne_zero_of_analyticOnNhd_ball hfball hz₀ hfz₀ hu)
  rw [hNF.zero_set_eq_divisor_support hord]
  exact hf.meromorphicOn.divisor_ball_support_finite

end HTGeometry

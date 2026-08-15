import GaloisForLFunctions.RHTower.SelbergClass.Basic
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Localized Selberg functional equation

The functional equation in `ExtendedSelbergClass` is a codiscrete equality, as
is appropriate for meromorphic functions with totalized values at poles.  This
module records the exact upgrade available at points where both sides are
analytic.  It deliberately does not assert that an arbitrary vertical contour
lies in this locus: that requires separate gamma-pole avoidance and residue
work.
-/

open Complex Filter Set
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- A codiscrete equality restricts to punctured neighbourhood equality. -/
theorem eventuallyEq_nhdsNE_of_codiscrete {f g : ℂ → ℂ}
    (h : f =ᶠ[codiscrete ℂ] g) (s : ℂ) : f =ᶠ[𝓝[≠] s] g := by
  apply h.filter_mono
  rw [Filter.codiscrete, Filter.codiscreteWithin]
  calc
    𝓝[≠] s ≤ 𝓝[(Set.univ : Set ℂ) \ {s}] s := by
      apply nhdsWithin_mono s
      intro x hx
      simp only [mem_compl_iff, mem_singleton_iff] at hx
      exact ⟨mem_univ x, hx⟩
    _ ≤ ⨆ x ∈ (Set.univ : Set ℂ), 𝓝[(Set.univ : Set ℂ) \ {x}] x := by
      exact le_iSup_of_le s (le_iSup_of_le (mem_univ s) le_rfl)

/-- The represented continuation is analytic away from its sole displayed
singularity. -/
theorem SelbergAnalyticContinuation.analyticAt_value_of_ne_one
    (A : SelbergAnalyticContinuation) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ A.value s := by
  unfold SelbergAnalyticContinuation.value
  apply (A.regularized.analytic s (mem_univ s)).div
  · exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ ↦ (z - 1) ^ A.poleOrder) s)
  · exact pow_ne_zero _ (sub_ne_zero.mpr hs)

/-- A codiscrete equality of functions analytic at a point is an exact equality
at that point. -/
theorem pointwise_eq_of_codiscrete_of_analyticAt {f g : ℂ → ℂ}
    (h : f =ᶠ[codiscrete ℂ] g) {s : ℂ}
    (hf : AnalyticAt ℂ f s) (hg : AnalyticAt ℂ g s) : f s = g s := by
  apply Filter.EventuallyEq.eq_of_nhds
  exact (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hf.continuousAt hg.continuousAt).mp
      (eventuallyEq_nhdsNE_of_codiscrete h s)

/-- Analyticity transports through the anti-holomorphic reflection appearing in
the Selberg functional equation. -/
theorem analyticAt_selbergConjugateReflection {f : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f (1 - star s)) :
    AnalyticAt ℂ (selbergConjugateReflection f) s := by
  obtain ⟨r, hr, han⟩ := hf.exists_ball_analyticOnNhd
  let U : Set ℂ := (fun z : ℂ ↦ 1 - star z) ⁻¹' Metric.ball (1 - star s) r
  have hUopen : IsOpen U := by
    exact Metric.isOpen_ball.preimage (continuous_const.sub continuous_star)
  have hsU : s ∈ U := by
    change dist (1 - star s) (1 - star s) < r
    simpa using hr
  have hdiff : DifferentiableOn ℂ (selbergConjugateReflection f) U := by
    intro z hz
    have hfz : AnalyticAt ℂ f (1 - star z) := han (1 - star z) hz
    have hg : DifferentiableAt ℂ (fun w : ℂ ↦ f (1 - w)) (star z) := by
      apply hfz.differentiableAt.comp (star z)
      exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ ↦ (1 : ℂ) - w) (star z))
    change DifferentiableWithinAt ℂ (fun x : ℂ ↦ star (f (1 - star x))) U z
    simpa [Function.comp_def] using (hg.star_conj.differentiableWithinAt (s := U))
  exact (hdiff.analyticOnNhd hUopen) s hsU

/-- The completed functional equation holds pointwise at every point where the
completed value is analytic both at the point and at its reflected point. -/
theorem ExtendedSelbergClass.completedFE_eq_of_analytic_pair
    (F : ExtendedSelbergClass) {s : ℂ}
    (hs : AnalyticAt ℂ (selbergCompletedValue F.gammaData F.continuation) s)
    (hreflection : AnalyticAt ℂ
      (selbergCompletedValue F.gammaData F.continuation) (1 - star s)) :
    selbergCompletedValue F.gammaData F.continuation s =
      F.gammaData.rootNumber *
        selbergConjugateReflection (selbergCompletedValue F.gammaData F.continuation) s := by
  apply pointwise_eq_of_codiscrete_of_analyticAt F.functionalEquation hs
  exact analyticAt_const.mul (analyticAt_selbergConjugateReflection hreflection)

/-- Pair-analytic locus on which the completed functional equation is an exact
pointwise equality. -/
def ExtendedSelbergClass.completedFEContourSafeSet (F : ExtendedSelbergClass) : Set ℂ :=
  {s | AnalyticAt ℂ (selbergCompletedValue F.gammaData F.continuation) s ∧
    AnalyticAt ℂ (selbergCompletedValue F.gammaData F.continuation) (1 - star s)}

theorem ExtendedSelbergClass.completedFE_eqOn_contourSafeSet (F : ExtendedSelbergClass) :
    Set.EqOn (selbergCompletedValue F.gammaData F.continuation)
      (fun z ↦ F.gammaData.rootNumber *
        selbergConjugateReflection (selbergCompletedValue F.gammaData F.continuation) z)
      F.completedFEContourSafeSet := by
  intro s hs
  exact F.completedFE_eq_of_analytic_pair hs.1 hs.2

end

end RHTower

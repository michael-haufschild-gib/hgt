module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
-- The installed preparatory bounded-embedding lemma is private to this mathlib module.
import all Mathlib.Analysis.Complex.RiemannMapping
public import Mathlib.Analysis.Complex.CauchyIntegral

public section

open Topology Set Function
open scoped Manifold ContDiff

namespace GaloisForLFunctions.HTGeometry

/-- On a simply connected complex manifold admitting no bounded analytic embedding,
every analytic open embedding into the complex plane is already surjective. -/
theorem surjective_analytic_openEmbedding_of_no_bounded_embedding
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [SimplyConnectedSpace M]
    (hnb : ¬ ∃ v : M → ℂ,
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω v ∧ Injective v ∧ Bornology.IsBounded (range v))
    {u : M → ℂ} (hu : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω u) (he : IsOpenEmbedding u) :
    Surjective u := by
  by_contra hs
  have hr : range u ≠ univ := by
    intro hr
    apply hs
    intro z
    have hz : z ∈ range u := hr ▸ mem_univ z
    exact hz
  have hsc : IsSimplyConnected (range u) :=
    he.isEmbedding.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨f, hball, hinj, hderiv⟩ :=
    Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero he.isOpen_range hsc hr
  apply hnb
  refine ⟨f ∘ u, ?_, ?_, ?_⟩
  · have hd : DifferentiableOn ℂ f (range u) := fun z hz =>
      (differentiableAt_of_deriv_ne_zero (hderiv z hz)).differentiableWithinAt
    intro x
    have ha : AnalyticAt ℂ f (u x) := hd.analyticAt (he.isOpen_range.mem_nhds (mem_range_self x))
    exact ha.contDiffAt.contMDiffAt.comp x (hu x)
  · intro x y hxy
    exact he.injective (hinj (mem_range_self x) (mem_range_self y) hxy)
  · apply (Metric.isBounded_ball : Bornology.IsBounded (Metric.ball (0 : ℂ) 1)).subset
    rintro z ⟨x, rfl⟩
    exact hball (mem_range_self x)

end GaloisForLFunctions.HTGeometry

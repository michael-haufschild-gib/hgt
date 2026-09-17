import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Complex.Basic

/-!
# Dense closed complex scalar relations are automatically bounded

The complex analogue of `DenseClosedScalarRigidity`: a closed densely-defined
complex-linear scalar reader has a closed domain, hence density forces it to be
everywhere defined.  On a Banach source it is therefore the restriction of a
continuous complex-linear functional.

This is the exact obstruction needed when a proposed boundary construction is
allowed to be a partial complex-linear reader, rather than an ambient continuous
functional from the outset.
-/

open Topology

namespace GaloisForLFunctions.HilbertMetric

/-- **Dense closed complex scalar-domain rigidity.** Every closed densely defined
complex-linear scalar functional on a normed complex space has full domain. -/
theorem dense_closed_complexScalarLinearPMap_domain_eq_top
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    (f : K →ₗ.[ℂ] ℂ) (hf : f.IsClosed)
    (hdense : Dense (f.domain : Set K)) : f.domain = ⊤ := by
  let ι : K →ₗ[ℂ] K × ℂ := (LinearMap.id : K →ₗ[ℂ] K).prod 0
  let N : Submodule ℂ K := f.graph.comap ι
  have hNclosed : IsClosed (N : Set K) := by
    have hι : Continuous ι := by
      change Continuous (fun x : K => (x, 0))
      fun_prop
    exact hf.preimage hι
  have hNdomain : N ≤ f.domain := by
    intro x hx
    change (x, 0) ∈ f.graph at hx
    obtain ⟨y, hy, _⟩ := f.mem_graph_iff.mp hx
    change (y : K) = x at hy
    rw [← hy]
    exact y.property
  have hclosedDomain : IsClosed (f.domain : Set K) := by
    by_cases hnonzero : ∃ v : f.domain, f v ≠ 0
    · obtain ⟨v, hv⟩ := hnonzero
      have hdomainEq : f.domain = N ⊔ ℂ ∙ (v : K) := by
        apply le_antisymm
        · intro x hx
          let x' : f.domain := ⟨x, hx⟩
          let c : ℂ := f x' / f v
          have hz : x - c • (v : K) ∈ N := by
            change (x - c • (v : K), 0) ∈ f.graph
            have hg := f.mem_graph (x' - c • v)
            rw [show (x - c • (v : K), 0) =
                (((x' - c • v : f.domain) : K), f (x' - c • v)) by
              apply Prod.ext
              · rfl
              · dsimp [c]
                rw [LinearPMap.map_sub, LinearPMap.map_smul]
                change 0 = f x' - (f x' / f v) * f v
                field_simp [hv]
                ring]
            exact hg
          have hspan : c • (v : K) ∈ ℂ ∙ (v : K) :=
            Submodule.smul_mem _ c (Submodule.mem_span_singleton_self (v : K))
          have hadd := (N ⊔ ℂ ∙ (v : K)).add_mem
            (show x - c • (v : K) ∈ N ⊔ ℂ ∙ (v : K) from
              Submodule.mem_sup_left hz)
            (show c • (v : K) ∈ N ⊔ ℂ ∙ (v : K) from
              Submodule.mem_sup_right hspan)
          simpa using hadd
        · apply sup_le hNdomain
          apply Submodule.span_le.mpr
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          subst x
          exact v.property
      rw [hdomainEq]
      exact Submodule.isClosed_sup_finiteDimensional N (ℂ ∙ (v : K)) hNclosed
    · have hzero : ∀ v : f.domain, f v = 0 := by
        intro v
        exact not_ne_iff.mp (not_exists.mp hnonzero v)
      have hdomainEq : f.domain = N := by
        apply le_antisymm
        · intro x hx
          change (x, 0) ∈ f.graph
          have hg := f.mem_graph (⟨x, hx⟩ : f.domain)
          simpa [hzero] using hg
        · exact hNdomain
      rw [hdomainEq]
      exact hNclosed
  have hclosure : closure (f.domain : Set K) = Set.univ :=
    dense_iff_closure_eq.mp hdense
  rw [hclosedDomain.closure_eq] at hclosure
  exact SetLike.coe_injective (by simpa using hclosure)

/-- A closed densely defined complex scalar functional on a complex Banach space is the
restriction of a continuous full-domain functional. -/
theorem dense_closed_complexScalarLinearPMap_exists_continuous_extension
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K]
    (f : K →ₗ.[ℂ] ℂ) (hf : f.IsClosed)
    (hdense : Dense (f.domain : Set K)) :
    ∃ g : K →L[ℂ] ℂ, ∀ x : f.domain, g x = f x := by
  have hdom := dense_closed_complexScalarLinearPMap_domain_eq_top f hf hdense
  let ι : K →ₗ[ℂ] f.domain :=
    { toFun := fun x => ⟨x, by rw [hdom]; trivial⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  let g : K →ₗ[ℂ] ℂ := f.toFun.comp ι
  have hgraph : g.graph = f.graph := by
    ext z
    constructor
    · intro hz
      rw [LinearMap.mem_graph_iff] at hz
      rw [f.mem_graph_iff]
      refine ⟨ι z.1, rfl, ?_⟩
      exact hz.symm
    · intro hz
      rw [f.mem_graph_iff] at hz
      obtain ⟨y, hy₁, hy₂⟩ := hz
      rw [LinearMap.mem_graph_iff]
      have hiy : ι z.1 = y := Subtype.ext hy₁.symm
      change z.2 = f (ι z.1)
      rw [hiy, hy₂]
  have hgclosed : IsClosed (g.graph : Set (K × ℂ)) := by
    rw [hgraph]
    exact hf
  let gc : K →L[ℂ] ℂ := ContinuousLinearMap.ofIsClosedGraph hgclosed
  refine ⟨gc, ?_⟩
  intro x
  change g (x : K) = f x
  change f (ι (x : K)) = f x
  congr

/-- Every closable densely defined complex scalar functional on a complex Banach space already
has a bounded full-domain extension. -/
theorem dense_closable_complexScalarLinearPMap_exists_continuous_extension
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K]
    (f : K →ₗ.[ℂ] ℂ) (hf : f.IsClosable)
    (hdense : Dense (f.domain : Set K)) :
    ∃ g : K →L[ℂ] ℂ, ∀ x : f.domain, g x = f x := by
  have hdomain : f.domain ≤ f.closure.domain := f.le_closure.1
  have hdenseClosure : Dense (f.closure.domain : Set K) :=
    hdense.mono fun x hx => hdomain hx
  obtain ⟨g, hg⟩ := dense_closed_complexScalarLinearPMap_exists_continuous_extension
    f.closure hf.closure_isClosed hdenseClosure
  refine ⟨g, ?_⟩
  intro x
  let y : f.closure.domain := ⟨x, hdomain x.property⟩
  have hxy : (x : K) = y := rfl
  have hle : f x = f.closure y := f.le_closure.2 hxy
  exact (hg y).trans hle.symm

end GaloisForLFunctions.HilbertMetric

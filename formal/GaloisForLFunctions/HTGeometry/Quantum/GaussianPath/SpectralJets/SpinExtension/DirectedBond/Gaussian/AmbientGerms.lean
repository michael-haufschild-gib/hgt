import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.RootGraph
import GaloisForLFunctions.HTGeometry.GeneralParametricEigenbranch

/-! # Extending a sparse energy germ to the full matrix parameter -/
open Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "M" => Matrix I I ℂ
variable {E : Type*} [NormedAddCommGroup E]

/-- Every continuous sparse branch through a simple root is the restriction
of a single analytic function of all matrix entries. -/
theorem ambient_branch (H : E→M) (f : E→ℂ) (x : E)
    (hH : ContinuousAt H x) (hf : ContinuousAt f x)
    (hr : ∀ᶠ p in 𝓝 x, matrixCharpolyRelation (H p,f p)=0)
    (hs : (H x).charpoly.derivative.eval (f x)≠0) :
    ∃ G : M→ℂ, AnalyticAt ℂ G (H x) ∧ G (H x)=f x ∧
      (∀ᶠ K in 𝓝 (H x), matrixCharpolyRelation (K,G K)=0) ∧ G ∘ H =ᶠ[𝓝 x] f := by
  obtain ⟨G,ha,h₀,hg⟩ := analytic_simple_root_graph (matrixCharpolyRelation_analyticAt (H x,f x))
    hr.self_of_nhds ((matrixCharpolyRelation_partial_w _ _).trans_ne hs)
  refine ⟨G,ha,h₀,?_,root_graph_restrict hg H f hH.tendsto hf.tendsto hr⟩
  have ht : Tendsto (fun K : M => (K,G K)) (𝓝 (H x)) (𝓝 (H x,f x)) := by
    have h₂ : Tendsto G (𝓝 (H x)) (𝓝 (f x)) := h₀ ▸ ha.continuousAt.tendsto
    exact tendsto_id.prodMk_nhds h₂
  exact (ht.eventually hg).mono fun K h => h.mpr rfl

#print axioms ambient_branch
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond

import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

/-! # Identifying spectral branches on restricted parameter families -/
open Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
noncomputable section
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]

/-- In a neighbourhood in parameter times energy, the zero set is the graph
of the simple root. This gives uniqueness also after restricting parameters. -/
theorem analytic_simple_root_graph {F : P × ℂ → ℂ} {x : P} {z : ℂ}
    (hF : AnalyticAt ℂ F (x,z)) (hz : F (x,z)=0)
    (hp : fderiv ℂ F (x,z) (0,1) ≠ 0) :
    ∃ f : P → ℂ, AnalyticAt ℂ f x ∧ f x=z ∧
      ∀ᶠ q in 𝓝 (x,z), F q=0 ↔ f q.1=q.2 := by
  have hD : ContDiffAt ℂ ω F (x,z) := hF.contDiffAt
  have hI : (fderiv ℂ F (x,z) ∘L (.inr ℂ P ℂ)).IsInvertible :=
    HolomorphicIFT.clm_invertible_of_apply_one_ne (by simpa using hp)
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by decide
  refine ⟨hD.implicitFunction hω hI,(hD.contDiffAt_implicitFunction hω hI).analyticAt,
    hD.implicitFunction_apply_self hω hI,?_⟩
  simpa only [hz] using hD.eventually_apply_eq_iff_implicitFunction hω hI

/-- Restricting the graph along a convergent family identifies any continuous
candidate root satisfying the same equation. -/
theorem root_graph_restrict {T : Type*} {l : Filter T} {F : P × ℂ → ℂ} {f : P→ℂ}
    {x : P} {z : ℂ} (hg : ∀ᶠ q in 𝓝 (x,z), F q=0 ↔ f q.1=q.2)
    (p : T→P) (r : T→ℂ) (hp : Tendsto p l (𝓝 x)) (hr : Tendsto r l (𝓝 z))
    (hz : ∀ᶠ t in l, F (p t,r t)=0) : (f ∘ p) =ᶠ[l] r := by
  filter_upwards [(hp.prodMk_nhds hr).eventually hg,hz] with t ht h
  exact ht.mp h

end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension

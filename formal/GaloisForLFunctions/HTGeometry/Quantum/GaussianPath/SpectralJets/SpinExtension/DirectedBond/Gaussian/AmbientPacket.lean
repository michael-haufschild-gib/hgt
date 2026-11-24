import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.AmbientGerms
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.SparseEmbedding
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.EnergySeparation

/-! # Lifting a complete sparse energy packet to the physical Pauli coordinates -/
open Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {D n m : ℕ}
local notation "M" => Matrix (Fin D) (Fin D) ℂ

/-- The entire sparse energy germ, including all coordinate derivatives, is
preserved when its simple branches are lifted to the larger pencil. -/
theorem ambient_slice_packet (P : Fin m→M) (x : Controls m) (ι : Fin n→Fin m)
    (f : Fin D → Controls n→ℂ) (hi : Function.Injective (fun l => f l 0))
    (hf : ∀ l, AnalyticAt ℂ (f l) 0 ∧ ∀ᶠ y in 𝓝 0,
      matrixCharpolyRelation (synthesis P (embed x ι y),f l y)=0) :
    ∃ F : Fin D → Controls m→ℂ, Function.Injective (fun l => F l x) ∧
      (∀ l, AnalyticAt ℂ (F l) x ∧ ∀ᶠ z in 𝓝 x, matrixCharpolyRelation (synthesis P z,F l z)=0) ∧
      ∀ l v, mixed (v.map ι) (F l) x=mixed v (f l) 0 := by
  let H := (synthesis P) ∘ embed x ι
  have h₀ : H 0=synthesis P x := by simp [H]
  have hH : ContinuousAt H 0 :=
    (synthesis P).continuous.continuousAt.comp (embed_analytic x ι).continuousAt
  have hr (l) : (H 0).charpoly.eval (f l 0)=0 := by
    simpa only [H,Function.comp_apply,matrixCharpolyRelation,←Matrix.eval_charpoly] using (hf l).2.self_of_nhds
  have hg (l) := ambient_branch H (f l) 0 hH (hf l).1.continuousAt (hf l).2
    (simple_packet (H 0) (fun i => f i 0) hi hr l)
  choose G ha hv hz he using hg
  let F (l : Fin D) := G l ∘ synthesis P
  have hvalue (l) : F l x=f l 0 := by
    change G l (synthesis P x)=f l 0
    rw [←h₀]
    exact hv l
  refine ⟨F,fun i j hij => hi ((hvalue i).symm.trans (hij.trans (hvalue j))),?_,?_⟩
  · intro l
    have h := ha l
    have h' := hz l
    rw [h₀] at h h'
    exact ⟨h.comp (f:=synthesis P) ((synthesis P).analyticAt x),
      (synthesis P).continuous.continuousAt.tendsto.eventually h'⟩
  · intro l v
    rw [← mixed_embed]
    have h : F l ∘ embed x ι =ᶠ[𝓝 0] f l := he l
    exact (response_coordinate v _ _).symm.trans
      ((response_germ (v.map axis) h).self_of_nhds.trans (response_coordinate v _ _))

end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond

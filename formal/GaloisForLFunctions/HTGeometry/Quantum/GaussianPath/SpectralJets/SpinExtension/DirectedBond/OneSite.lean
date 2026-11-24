import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Extension
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.PauliChain
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.CoordinateChart

/-! # The first spin has two simple branches and both terminal responses -/
open Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

/-- The zero-spin register supplies the constant row. Its first extension has
no earlier bond derivatives, so the unused zero-spin field drops out. -/
theorem one_site_chart :
    ∃ (B : Fin 1→ℕ) (k : Config 1) (f : Config 1 → Controls 0 × ℂ → ℂ),
      Function.Injective (fun l => f l 0) ∧
      (∀ l, AnalyticAt ℂ (f l) 0 ∧ ∀ᶠ p : Controls 0 × ℂ in 𝓝 0,
        matrixCharpolyRelation (background 0 B p.1+p.2 • lastPauli 0 0,f l p)=0) ∧
      ∀ j, (readings k (fun _ => ([] : List (Controls 0))) j f).det≠0 := by
  let k₀ : Config 0 := fun _ => false
  let H : Controls 0→Register 0 := fun _ => 0
  let f : Config 0 → Controls 0 × ℂ → ℂ := fun _ _ => 0
  let w : Config 0→List (Controls 0) := fun _ => []
  have hi : Function.Injective (fun l => f l 0) := fun _ _ _ => Subsingleton.elim _ _
  have hf (l : Config 0) : AnalyticAt ℂ (f l) 0 ∧ ∀ᶠ p : Controls 0 × ℂ in 𝓝 0,
      matrixCharpolyRelation (H p.1+p.2 • (0:Register 0),f l p)=0 := by
    refine ⟨analyticAt_const,Eventually.of_forall fun p => ?_⟩
    simp [H,f,matrixCharpolyRelation]
  have hd (j : Bool) : (readings k₀ w j f).det≠0 := by
    have he : readings k₀ w j f=1 := by
      ext i l
      rw [Subsingleton.elim i k₀,Subsingleton.elim l k₀]
      simp [readings]
    rw [he,det_one]
    exact one_ne_zero
  obtain ⟨n,g,hin,hg,hm⟩ := extend_chart H 0 k₀ w f analyticAt_const hi hf hd
  let B : Fin 1→ℕ := fun _ => n
  let π (p : Controls 0 × ℂ) := ((p.1,(0:ℂ)),p.2)
  have hπ₀ : π 0=0 := rfl
  have hπ : AnalyticAt ℂ π 0 := (analyticAt_fst.prod analyticAt_const).prod analyticAt_snd
  let d := blockConfig 0
  let F (l : Config 0⊕Config 0) := g l ∘ π
  have hw (i) : nextWords k₀ w i=[] := by cases i with
    | inl l => simp [nextWords,Subsingleton.elim l k₀]
    | inr l => simp [nextWords,Subsingleton.elim l k₀]
  refine ⟨B,d (.inl k₀),fun l => F (d.symm l),hin.comp d.symm.injective,?_,?_⟩
  · intro l
    let a := d.symm l
    have h₁ : AnalyticAt ℂ (g a) (π 0) := hπ₀.symm ▸ (hg a).1
    refine ⟨h₁.comp hπ,?_⟩
    have h₂ : Tendsto π (𝓝 0) (𝓝 0) := by simpa only [hπ₀] using hπ.continuousAt.tendsto
    filter_upwards [h₂.eventually (hg a).2] with p hp
    have h := (relation_onRegister 0 (baseNext H 0 n (π p).1+(π p).2 • tip (Config 0)) (F a p)).trans hp
    simpa only [onRegister_add,onRegister_smul,onRegister_tip,H,π,B,background,baseNext,smul_zero] using h
  · intro j
    have hsame : readings (.inl k₀) (fun _ => ([] : List (Controls 0))) j F =
        readings (.inl k₀) (nextWords k₀ w) j g := by
      ext i l
      by_cases hi' : i=Sum.inl k₀
      · simp [readings,hi']
      · simp only [readings,of_apply,if_neg hi',hw]
        change response _ _ ((0:Controls 0),0)=response _ _ ((0:Controls 0 × ℂ),0)
        rw [read_extendWord,read_extendWord]
        rfl
    rw [readings_reindex d (.inl k₀) (fun _ => ([] : List (Controls 0))) j F,hsame]
    exact hm j

#print axioms one_site_chart
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond

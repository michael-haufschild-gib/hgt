import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.SeparatedSplittings
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.PhysicalSplit

/-! # Two physical paths differing in one boundary field separate spectral actions -/
open Matrix Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
private abbrev Labels (k : ℕ) := seedIndex k × Bool

/-- A nonzero balanced packet at one boundary splitting avoids any prescribed
packet at another, with every independent labeling of the two spectra. Only
one onsite Z coefficient differs between the two nearest-neighbour chains. -/
theorem exists_boundary_pair (k : ℕ) (c d : Labels k → ℂ) (hc : c≠0) (hb : ∑ i, c i=0) :
    ∃ H ∈ pauliChainSpan (k+3), ∃ z w : ℝ, ∃ F G : Labels k → ℂ,
      Function.Injective F ∧ Function.Injective G ∧
      (∀ i, matrixCharpolyRelation (H+(z:ℂ) • SpinExtension.lastPauli (k+2) 2,F i)=0) ∧
      (∀ i, matrixCharpolyRelation (H+(w:ℂ) • SpinExtension.lastPauli (k+2) 2,G i)=0) ∧
      ∀ σ τ : Equiv.Perm (Labels k), (∑ i, c (σ i)*F i)≠∑ i, d (τ i)*G i := by
  classical
  obtain ⟨E,U,P,hmax,_,hl,hr,_,hP,hH,hM⟩ := exists_pauliChainSeed k
  let e := fun i => (E i : ℂ)
  have hi : Function.Injective e := Complex.ofReal_injective.comp (MaximallyProjectiveEnergy.injective hmax)
  have hg (a b i j : seedIndex k) (hab : a≠b) (hij : i≠j) (he : e b-e a=e j-e i) : (a,b)=(i,j) := by
    have hd : E b-E a=E j-E i := Complex.ofReal_injective (by push_cast; exact he)
    have hp : (⟨(b,a),hab.symm⟩ : {p : seedIndex k × seedIndex k // p.1≠p.2})=⟨(j,i),hij.symm⟩ :=
      maximallyProjectiveEnergy_orientedGap_injective E hmax hd
    exact congrArg (fun p => (p.val.2,p.val.1)) hp
  obtain ⟨w,hw⟩ := exists_real_admissible_split_shift E
  let J := Equiv.Perm (Labels k) × Equiv.Perm (Labels k)
  let C (p : J) (i : Labels k) := c (p.1 i)
  let D (p : J) (i : Labels k) := d (p.2 i)
  have hbal (p : J) : ∑ i, C p i=0 := (Equiv.sum_comp p.1 c).trans hb
  have hne (p : J) : C p≠0 := by
    intro he
    exact hc (funext fun i => by simpa only [C,Equiv.apply_symm_apply,Pi.zero_apply] using congrFun he (p.1.symm i))
  obtain ⟨z,_,hz⟩ := separated_real_fields (three_le_card_seedIndex k) hi hg hM C D hbal hne
    w (injective_layerSplitEnergy hi hw) (T := Set.univ) Set.infinite_univ
  obtain ⟨u,F,G,hf,hg',hiF,hiG,hsep⟩ := hz.exists
  let B := U*diagonal e*Uᴴ
  have roots (v : ℝ) (f : Labels k → ℂ) (h : ∀ i, matrixCharpolyRelation
      (diagonal (layerSplitEnergy e (v:ℂ))+(u:ℂ) • layerCrossPerturbation (Uᴴ*P*U),f i)=0) (i) :
      matrixCharpolyRelation (splitPath B P 0 u+((v/2:ℝ):ℂ) • SpinExtension.lastPauli (k+2) 2,f i)=0 := by
    rw [←splitPath_shift]
    simpa only [B,matrixCharpolyRelation,←Matrix.eval_charpoly,splitPath_charpoly U hl hr] using h i
  exact ⟨splitPath B P 0 u,splitPath_mem hH hP _ _,z/2,w/2,F,G,hiF,hiG,roots z F hf,roots w G hg',
    fun σ τ => hsep (σ,τ)⟩

#print axioms exists_boundary_pair
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField

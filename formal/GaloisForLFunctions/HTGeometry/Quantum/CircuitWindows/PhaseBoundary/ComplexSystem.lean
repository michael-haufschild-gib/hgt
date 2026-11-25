import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.MatrixEntries

/-! # Finite complex equations with real witness coordinates -/
open Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section
variable {A X ι κ : Type*} [CommRing A]

/-- Evaluate witness polynomials at the base point and the chosen real tuple. -/
def witnessEval (ρ : X → A →+* ℝ) (z : X × (ι → ℝ)) : MvPolynomial ι A →+* ℝ :=
  MvPolynomial.eval₂Hom (ρ z.1) z.2

theorem witness_coordinate (ρ : X → A →+* ℝ) (i : ι) :
    Represents (witnessEval ρ) (fun z : X × (ι → ℝ) => z.2 i) :=
  ⟨MvPolynomial.X i,fun _ => MvPolynomial.eval₂Hom_X' ..⟩

theorem Represents.on_base {ρ : X → A →+* ℝ} {f : X → ℝ} (hf : Represents ρ f) :
    Represents (witnessEval ρ) (fun z : X × (ι → ℝ) => f z.1) := by
  obtain ⟨a,ha⟩ := hf
  exact ⟨MvPolynomial.C a,fun z => (MvPolynomial.eval₂Hom_C ..).trans (ha z.1)⟩

theorem ComplexRep.on_base {ρ : X → A →+* ℝ} {f : X → ℂ} (hf : ComplexRep ρ f) :
    ComplexRep (witnessEval ρ) (fun z : X × (ι → ℝ) => f z.1) :=
  ⟨hf.1.on_base,hf.2.on_base⟩

/-- Complex residuals represented by polynomials give two real equations each. -/
theorem exists_real_residual_system (ρ : X → A →+* ℝ) (F : κ → X × (ι → ℝ) → ℂ)
    (hF : ∀ k, ComplexRep (witnessEval ρ) (F k)) :
    ∃ p : κ × Bool → MvPolynomial ι A, {x | ∃ w : ι → ℝ, ∀ k, F k (x,w)=0} =
      {x | ∃ w : ι → ℝ, ∀ k, MvPolynomial.eval₂Hom (ρ x) w (p k)=0} := by
  let R (k : κ × Bool) (z : X × (ι → ℝ)) := if k.2 then (F k.1 z).im else (F k.1 z).re
  have hr (k : κ × Bool) : Represents (witnessEval ρ) (R k) := by
    rcases k with ⟨k,b⟩
    cases b
    · exact (hF k).1
    · exact (hF k).2
  choose p hp using hr
  have he : {x | ∃ w : ι → ℝ, ∀ k, F k (x,w) = 0} =
      {x | ∃ w : ι → ℝ, ∀ k, MvPolynomial.eval₂Hom (ρ x) w (p k) = 0} := by
    ext x
    constructor
    · rintro ⟨w,hw⟩
      refine ⟨w,fun k => (hp k (x,w)).trans ?_⟩
      simp only [R,hw,Complex.zero_im,Complex.zero_re,ite_self]
    · rintro ⟨w,hw⟩
      refine ⟨w,fun k => Complex.ext ?_ ?_⟩
      · exact (hp (k,false) (x,w)).symm.trans (hw (k,false))
      · exact (hp (k,true) (x,w)).symm.trans (hw (k,true))
  exact ⟨p,he⟩

/-- Split all complex residuals into real and imaginary parts, then project
the single sum-of-squares equation in all real coordinates. -/
theorem certified_complex_system [TopologicalSpace X] [Fintype ι] [Fintype κ]
    (ρ : X → A →+* ℝ) (hc : ∀ a, Continuous fun x => ρ x a)
    (F : κ → X × (ι → ℝ) → ℂ) (hF : ∀ k, ComplexRep (witnessEval ρ) (F k)) :
    LocallyCertified ρ {x | ∃ w : ι → ℝ, ∀ k, F k (x,w) = 0} := by
  obtain ⟨p,he⟩ := exists_real_residual_system ρ F hF
  rw [he]
  exact certified_exists_system ρ hc p

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary

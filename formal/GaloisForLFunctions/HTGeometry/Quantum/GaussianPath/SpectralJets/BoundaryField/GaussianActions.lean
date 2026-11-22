import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.GaussianFibers
import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum

/-! # Every balanced integer action on a fixed Gaussian boundary line -/
open Matrix MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
private abbrev Size (k : ℕ) := 2^(k+3)
private abbrev Basis (k : ℕ) := Fin (k+3)→Bool
private abbrev Mat (k : ℕ) := Matrix (Basis k) (Basis k) ℂ

/-- A Gaussian prefix with a real increment added to its last onsite Z field. -/
def boundaryHamiltonian (ω : PathPauliDisorder) (k : ℕ) (t : ℝ) : Mat k :=
  pathHamiltonian (pathPauliDisorderShell ω (k+1))+(t:ℂ) • SpinExtension.lastPauli (k+2) 2

theorem boundaryHermitian (ω : PathPauliDisorder) (k : ℕ) (t : ℝ) :
    (boundaryHamiltonian ω k t).IsHermitian := by
  have hz : (SpinExtension.lastPauli (k+2) 2).IsHermitian := by
    rw [SpinExtension.lastPauli_word]
    exact finitePauliMatrix_isHermitian _
  exact (isSelfAdjoint_pathHamiltonian _).isHermitian.add (hz.smul (Complex.conj_ofReal t))

/-- On every prefix of at least three spins, every nonzero balanced integer
action has finite level sets when one varies just the last onsite field.
The exceptional field settings also include every repeated energy. -/
theorem gaussian_integer_action_levels :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ m : Basis k→ℤ, m≠0 → (∑ i, m i)=0 → ∀ v : ℝ,
      let E (t : ℝ) := (boundaryHermitian ω k t).eigenvalues
      {t : ℝ | ¬Function.Injective (E t) ∨ ∃ σ : Equiv.Perm (Basis k), (∑ i, (m i:ℝ)*E t (σ i))=v}.Finite := by
  apply ae_all_iff.mpr
  intro k
  apply ae_all_iff.mpr
  intro m
  by_cases hm : m=0
  · exact Filter.Eventually.of_forall fun _ hn => (hn hm).elim
  by_cases hb : (∑ i, m i)=0
  · let e := qubitConfigFin (k+3)
    let c (j : Fin (Size k)) := (m (e.symm j):ℂ)
    have hc : c≠0 := by
      intro hz
      apply hm
      funext i
      have h : (m i:ℂ)=0 := by simpa only [c,Equiv.symm_apply_apply,Pi.zero_apply] using congrFun hz (e i)
      exact_mod_cast h
    have hbal : ∑ j, c j=0 := (Equiv.sum_comp e.symm (fun i => (m i:ℂ))).trans (by exact_mod_cast hb)
    filter_upwards [gaussian_boundary_action_fibers k c hc hbal] with ω hω
    intro _ _ v E
    let F (t : ℝ) (j : Fin (Size k)) := (E t (e.symm j):ℂ)
    have ht (t : ℝ) (j : ℕ) : ((Matrix.reindex e e (boundaryHamiltonian ω k t))^j).trace=∑ i, F t i^j := by
      rw [trace_pow_reindex,trace_pow_eq_sum_eigenvalues_pow (boundaryHermitian ω k t)]
      exact (Equiv.sum_comp e.symm (fun i => (E t i:ℂ)^j)).symm
    have h := hω F ht (v:ℂ)
    apply h.subset
    intro t ht'
    rcases ht' with hn | ⟨σ,hs⟩
    · exact Or.inl fun hi => hn (fun {i j} he => e.injective (@hi (e i) (e j)
        (by simpa only [F,Equiv.symm_apply_apply] using congrArg Complex.ofReal he)))
    · let τ := (e.symm.trans σ).trans e
      refine Or.inr ⟨τ,?_⟩
      calc ∑ i, c i*F t (τ i) = ∑ i, (m i:ℂ)*(E t (σ i):ℂ) := by
             simpa only [c,F,τ,Equiv.trans_apply,Equiv.symm_apply_apply] using
               Equiv.sum_comp e.symm (fun i => (m i:ℂ)*(E t (σ i):ℂ))
           _ = (v:ℂ) := by exact_mod_cast hs
  · exact Filter.Eventually.of_forall fun _ _ hs => (hb hs).elim

#print axioms gaussian_integer_action_levels
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField

import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.PhysicalWitness
import GaloisForLFunctions.HTGeometry.ChainPauliFinEscape
import GaloisForLFunctions.HTGeometry.RootPacketPowerSum

/-! # Numbered spectral packets for a single boundary-field variation -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
private abbrev Size (k : ℕ) := 2^(k+3)
private abbrev Coeff (k : ℕ) := Fin (Fintype.card (ChainLabel (k+3)))

/-- The terminal Pauli Z in the same basis as the numbered path pencil. -/
def terminalZ (k : ℕ) : Matrix (Fin (Size k)) (Fin (Size k)) ℂ :=
  let e := qubitConfigFin (k+3)
  Matrix.reindex e e (SpinExtension.lastPauli (k+2) 2)

/-- Two field settings on a single path avoid a common action under any
independent labelings. Power traces identify their root packets. -/
theorem numbered_boundary_pair (k : ℕ) (c : Fin (Size k)→ℂ) (hc : c≠0) (hb : ∑ i, c i=0) :
    ∃ θ : Coeff k→ℝ, ∃ z w : ℝ, ∃ F G : Fin (Size k)→ℂ,
      let H := spectralEnsembleMatrix (chainPauliFin (k+3)) θ
      Function.Injective F ∧ Function.Injective G ∧
      (∀ j : ℕ, ((H+(z:ℂ) • terminalZ k)^j).trace=∑ i, F i^j) ∧
      (∀ j : ℕ, ((H+(w:ℂ) • terminalZ k)^j).trace=∑ i, G i^j) ∧
      ∀ σ τ : Equiv.Perm (Fin (Size k)), (∑ i, c i*F (σ i))≠∑ i, c i*G (τ i) := by
  classical
  let e := seedLeafFin k
  let q := qubitConfigFin (k+3)
  have hc' : c ∘ e≠0 := fun he => hc (funext fun i => by
    simpa only [Function.comp_apply,Equiv.apply_symm_apply,Pi.zero_apply] using congrFun he (e.symm i))
  obtain ⟨H,hH,z,w,F,G,hF,hG,hf,hg,hs⟩ := exists_boundary_pair k (c ∘ e) (c ∘ e) hc' ((e.sum_comp c).trans hb)
  obtain ⟨θ,hθ⟩ := mem_range_spectralEnsembleMatrix_of_mem_span (reindexFin_mem_span_range_chainPauliFin hH)
  have trace_packet (v : ℝ) (A : seedIndex k × Bool→ℂ) (hA : Function.Injective A)
      (hr : ∀ i, matrixCharpolyRelation (H+(v:ℂ) • SpinExtension.lastPauli (k+2) 2,A i)=0) (j : ℕ) :
      ((spectralEnsembleMatrix (chainPauliFin (k+3)) θ+(v:ℂ) • terminalZ k)^j).trace=∑ i, (A (e.symm i))^j := by
    apply (sum_pow_rootPacket_eq_trace_pow_fin _ _ (hA.comp e.symm.injective) ?_ j).symm
    intro i
    rw [hθ]
    change matrixCharpolyRelation (Matrix.reindex q q (H+(v:ℂ) • SpinExtension.lastPauli (k+2) 2),A (e.symm i))=0
    simpa only [matrixCharpolyRelation,←Matrix.eval_charpoly,Matrix.charpoly_reindex] using hr (e.symm i)
  let perm (σ : Equiv.Perm (Fin (Size k))) := (e.trans σ.symm).trans e.symm
  have reorder (A : seedIndex k × Bool→ℂ) (σ : Equiv.Perm (Fin (Size k))) :
      (∑ i, (c ∘ e) (perm σ i)*A i)=∑ i, c i*A (e.symm (σ i)) := by
    rw [←(e.trans σ.symm).sum_comp (fun i => c i*A (e.symm (σ i)))]
    simp only [Function.comp_apply,perm,Equiv.trans_apply,Equiv.apply_symm_apply,Equiv.symm_apply_apply]
  exact ⟨θ,z,w,F ∘ e.symm,G ∘ e.symm,hF.comp e.symm.injective,hG.comp e.symm.injective,
    trace_packet z F hF hf,trace_packet w G hG hg,fun σ τ he =>
      hs (perm σ) (perm τ) ((reorder F σ).trans (he.trans (reorder G τ).symm))⟩

#print axioms numbered_boundary_pair
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField

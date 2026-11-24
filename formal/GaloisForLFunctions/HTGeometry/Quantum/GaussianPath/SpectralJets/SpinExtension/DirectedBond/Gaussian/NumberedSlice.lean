import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.SparseEmbedding
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.PhysicalSlice
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.PauliDetector
import GaloisForLFunctions.HTGeometry.ChainPauliFinEscape

/-! # The directed bond pencil in the coordinates of the Gaussian chain -/
open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

/-- One entry of the Gaussian coefficient vector for each directed bond or terminal field. -/
def fieldIndex (n : ℕ) (i : Fin (n+1)) : Coordinates (n+1) :=
  Fintype.equivFin (ChainLabel (n+1)) (fieldLabels n i)

theorem generator_field (n : ℕ) (i : Fin (n+1)) :
    chainPauliFin (n+1) (fieldIndex n i) = reindex (qubitConfigFin (n+1)) (qubitConfigFin (n+1))
      (finitePauliMatrix (fieldLabels n i).1) := by
  simp only [chainPauliFin,fieldIndex,Equiv.symm_apply_apply]

/-- The slice has a real background and follows literal Gaussian coefficient axes. -/
theorem numbered_slice (n : ℕ) (B : Fin (n+1)→ℕ) :
    ∃ θ : Coordinates (n+1)→ℝ, ∀ y : Controls (n+1),
      reindex (qubitConfigFin (n+1)) (qubitConfigFin (n+1)) (chain B y) =
        synthesis (chainPauliFin (n+1)) (embed (fun a => (θ a:ℂ)) (fieldIndex n) y) := by
  let q := qubitConfigFin (n+1)
  obtain ⟨θ,hθ⟩ := mem_range_spectralEnsembleMatrix_of_mem_span
    (reindexFin_mem_span_range_chainPauliFin (background_zero_mem n B))
  have he : synthesis (chainPauliFin (n+1)) (fun a => (θ a:ℂ)) = reindex q q (background n B 0) := by
    rw [synthesis_apply]
    exact hθ
  refine ⟨θ,fun y => ?_⟩
  rw [chain_affine,synthesis_embed,he,synthesis_apply]
  ext l j
  simp only [q,Function.comp_apply,generator_field,Matrix.reindex_apply,Matrix.submatrix_apply,
    Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply]

#print axioms numbered_slice
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond

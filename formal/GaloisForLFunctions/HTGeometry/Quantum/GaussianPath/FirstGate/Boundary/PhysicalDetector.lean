import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.FirstSite
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.SlopeDetector
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.PhysicalTraceWitness
import GaloisForLFunctions.HTGeometry.ChainPauliFinEscape

/-! # A nonzero polynomial for the fixed first-site observable -/
open Matrix MvPolynomial
open GaloisForLFunctions.HTGeometry.SpectralJets
open GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
namespace GaloisForLFunctions.HTGeometry.FirstGate.Boundary
noncomputable section

def firstSign (n : ℕ) (j : Fin (2^(n+2))) := spinCoefficient (n+2) j 0

def firstDetector (n : ℕ) := slopeDetector (pencil (integralGenerators (n+2))) (firstSign n)

theorem reindex_firstZ (n : ℕ) :
    let e := qubitConfigFin (n+2)
    Matrix.reindex e e (finitePauliMatrix (pauliZLabel (0:Fin (n+2)))) =
      diagonal (fun i => GaussianInt.toComplex (firstSign n i)) := by
  intro e
  ext i j
  change finitePauliMatrix _ (e.symm i) (e.symm j)=_
  rw [finitePauliMatrix_pauliZLabel]
  by_cases hij : i=j
  · subst j
    simp only [if_true,diagonal_apply_eq,firstSign,spinCoefficient,zSign,e]
    split <;> simp
  · simp only [if_neg (e.symm.injective.ne hij),diagonal_apply_ne _ hij]

theorem firstDetector_witness (n : ℕ) : ∃ θ : Coordinates (n+2) → ℝ,
    eval₂Hom GaussianInt.toComplex (fun i => (θ i:ℂ)) (firstDetector n)≠0 := by
  obtain ⟨H,hH,hr⟩ := exists_resolved_first (n+1)
  obtain ⟨θ,hθ⟩ := mem_range_spectralEnsembleMatrix_of_mem_span (reindexFin_mem_span_range_chainPauliFin hH)
  let e := qubitConfigFin (n+2)
  have hh : numberedBackground n θ=Matrix.reindex e e H := (numberedBackground_eq n θ).trans hθ
  have hm := hr.reindex e
  rw [←hh,reindex_firstZ] at hm
  obtain ⟨f,hf,hi,hd⟩ := hm
  exact ⟨θ,(slopeDetector_iff _ _ GaussianInt.toComplex (fun i => (θ i:ℂ)) f hf hi).mpr hd⟩

#print axioms firstDetector_witness
end
end GaloisForLFunctions.HTGeometry.FirstGate.Boundary

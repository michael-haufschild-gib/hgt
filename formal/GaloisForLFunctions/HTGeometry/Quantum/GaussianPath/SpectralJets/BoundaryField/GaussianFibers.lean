import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.PairedModes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.ActionLevels
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FieldPencils
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NumberedWitness
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.RealWitness
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates

/-! # Finite spectral-action fibers when only the terminal field varies -/
open Matrix MvPolynomial MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
private abbrev Size (k : ℕ) := 2^(k+3)
private abbrev Coeff (k : ℕ) := Fin (Fintype.card (ChainLabel (k+3)))

/-- With all couplings fixed to one Gaussian draw, every prescribed balanced
nonzero packet takes each complex value only finitely often along the
terminal Z field. The finite set allows every labeling and includes every
degenerate field setting. -/
theorem gaussian_boundary_action_fibers (k : ℕ) (c : Fin (Size k)→ℂ) (hc : c≠0) (hb : ∑ i, c i=0) :
    ∀ᵐ ω ∂pathPauliDisorderLaw,
      let q := qubitConfigFin (k+3)
      let H := Matrix.reindex q q (pathHamiltonian (pathPauliDisorderShell ω (k+1)))
      ∀ E : ℝ→Fin (Size k)→ℂ, (∀ (t : ℝ) (j : ℕ),
        ((H+(t:ℂ) • terminalZ k)^j).trace=∑ i, E t i^j) → ∀ v : ℂ,
        {t : ℝ | ¬Function.Injective (E t) ∨ ∃ σ : Equiv.Perm (Fin (Size k)), (∑ i, c i*E t (σ i))=v}.Finite := by
  obtain ⟨θ,z,w,F,G,hF,hG,htrF,htrG,hs⟩ := numbered_boundary_pair k c hc hb
  let P := chainPauliFin (k+3)
  let M (t : ℝ) := fixedFieldPencil P (terminalZ k) t
  let x (a : Coeff k→ℝ) (i : Coeff k) := (a i:ℂ)
  let Q := separationTest (M z) (M w) c c
  have trace_at (a : Coeff k→ℝ) (t : ℝ) (j : ℕ) :
      eval (x a) ((M t)^j).trace=((spectralEnsembleMatrix P a+(t:ℂ) • terminalZ k)^j).trace :=
    eval_trace_of_map _ _ (eval_fixedFieldPencil P _ t a) j
  have hw : eval (x θ) Q≠0 := (separationTest_ne_zero_iff _ _ _ F G c c
    (fun j => (trace_at θ z j).trans (htrF j)) (fun j => (trace_at θ w j).trans (htrG j))).mpr ⟨hF,hG,hs⟩
  have hgauss := gaussian_ae_of_real_witness (RingHom.id ℂ) Q (v := 1) one_ne_zero ⟨θ,hw⟩
  filter_upwards [(gaussian_pauli_prefix_coordinates_law (k+1)).quasiMeasurePreserving.ae hgauss] with ω hω
  intro q H E ht v
  let a (i : Coeff k) := pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  have he : H=spectralEnsembleMatrix P a := reindex_pathHamiltonian _
  have hh (t : ℝ) (j : ℕ) : eval (x a) ((M t)^j).trace=∑ i, E t i^j :=
    (trace_at a t j).trans (he ▸ ht t j)
  obtain ⟨hi,hj,hsep⟩ := (separationTest_ne_zero_iff _ _ _ (E z) (E w) c c (hh z) (hh w)).mp hω
  refine finite_action_fibers (variableFieldPencil H (terminalZ k)) (fun _ => Polynomial.X) E c ?_ hi hj hsep v
  intro t j
  simp only [Polynomial.eval_X]
  exact (eval_trace_of_map _ _ (eval_variableFieldPencil H _ t) j).trans (ht t j)

#print axioms gaussian_boundary_action_fibers
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField

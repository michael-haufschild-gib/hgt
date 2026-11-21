import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.SimpleContacts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.GapSpectrum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliPrefixPhaseLaw

/-! # Simple endpoint contacts on every Gaussian prefix at a fixed radius -/
open Matrix MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.FirstGate
noncomputable section

private theorem root_reindex {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (q : I ≃ J) (H : Matrix I I ℂ) (z : ℂ) :
    matrixCharpolyRelation (Matrix.reindex q q H,z)=matrixCharpolyRelation (H,z) := by
  simp only [matrixCharpolyRelation,←Matrix.eval_charpoly,Matrix.charpoly_reindex]

/-- For a specified real separation, no positive relative phase clock has
a tied endpoint, on every prefix of one draw. Both orientations hold. -/
theorem gaussian_fixed_contacts (r : ℝ) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let u := pathPauliDisorderShell ω (k+1)
      let E := fun i => -(isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues i
      AvoidsTie E r ∧ AvoidsTie E (-r) := by
  apply ae_all_iff.mpr
  intro k
  let n := k+1
  let N := k+3
  let P := chainPauliFin N
  let q := qubitConfigFin N
  have hp := chainPauliFin_spectrumEscapesRealRelations k
  have hac : centredProductGaussian (Fin (Fintype.card (ChainLabel N))) 1 ≪ volume := by
    simpa [centredProductGaussian] using productGaussian_absolutelyContinuous (Fintype.card (ChainLabel N)) one_ne_zero (fun _ => 0)
  have ha := (gaussian_pauli_prefix_coordinates_law n).quasiMeasurePreserving.ae (hac.ae_le
    ((ae_avoids_tie P hp r).and (ae_avoids_tie P hp (-r))))
  filter_upwards [ha,gaussian_path_all_prefixes_maximally_projective] with ω hw hω
  intro u E
  let F := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
  let θ := fun i => u (pathCoeffEquiv n i)
  have hroot (j : Fin (2^N)) : matrixCharpolyRelation (spectralEnsembleMatrix P θ,(F (q.symm j):ℂ))=0 := by
    rw [←reindex_pathHamiltonian u,root_reindex]
    exact hermitianEigenvalue_matrixCharpolyRelation _ _ _
  have hi := (hω k).injective.comp q.symm.injective
  have transport (s : ℝ) (h : AvoidsTie (F ∘ q.symm) s) : AvoidsTie E s := by
    intro a b c hab hca hcb m l hm he
    apply h (q a) (q b) (q c) (q.injective.ne hab) (q.injective.ne hca) (q.injective.ne hcb) m l hm
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
    change (m:ℝ)*(-F c- -F a)=((l:ℝ)+s)*(-F b- -F a) at he
    linarith only [he]
  exact ⟨transport _ (hw.1 _ hi hroot),transport _ (hw.2 _ hi hroot)⟩

#print axioms gaussian_fixed_contacts
end
end GaloisForLFunctions.HTGeometry.FirstGate

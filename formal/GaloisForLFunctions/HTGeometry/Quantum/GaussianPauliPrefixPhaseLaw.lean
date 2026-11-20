import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates
import GaloisForLFunctions.HTGeometry.ChainShellMaximalProjectivity
import GaloisForLFunctions.HTGeometry.GaussianAffinePauliProjectiveGenericityLaw

/-! # Generic spectra of all finite prefixes of one Gaussian Pauli chain -/
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem chain_spectrum_ae_gaussian (k : ℕ) :
    ∀ᵐ θ ∂(centredProductGaussian (Fin (Fintype.card (ChainLabel (k+3)))) 1),
      MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
        (chainPauliFin_isHermitian (k+3)) θ).eigenvalues := by
  obtain ⟨θ₀,hθ₀⟩ := exists_chainShell_maximallyProjective_witness k
  let P := chainPauliFin (k+3)
  have hP := chainPauliFin_isHermitian (k+3)
  have hnull := (polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure
    (spectralGenericMatrix P) θ₀ (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues
    hθ₀ hθ₀.injective (by
      intro i
      rw [map_spectralGenericMatrix_eq θ₀]
      exact charpolyRelation_eigenvalues (isHermitian_spectralEnsembleMatrix hP θ₀) i)).2.2
  have hac : centredProductGaussian (Fin (Fintype.card (ChainLabel (k+3)))) 1 ≪ volume := by
    simpa [centredProductGaussian] using productGaussian_absolutelyContinuous
      (Fintype.card (ChainLabel (k+3))) one_ne_zero (fun _ => 0)
  have hg : ∀ᵐ θ ∂(centredProductGaussian (Fin (Fintype.card (ChainLabel (k+3)))) 1),
      θ ∈ polynomialMatrixProjectiveGenericSet (spectralGenericMatrix P) := ae_iff.mpr (hac hnull)
  filter_upwards [hg] with θ hθ
  exact (mem_genericSet_iff_maximallyProjective hP θ).mp hθ

/-- A single infinite iid Gaussian Pauli disorder almost surely gives
maximally projective spectra for every open prefix of at least three sites. -/
theorem gaussian_path_all_prefixes_maximally_projective :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      MaximallyProjectiveEnergy (isSelfAdjoint_pathHamiltonian
        (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues := by
  apply ae_all_iff.mpr
  intro k
  have hg := (gaussian_pauli_prefix_coordinates_law (k+1)).quasiMeasurePreserving.ae (chain_spectrum_ae_gaussian k)
  filter_upwards [hg] with ω hω
  let u := pathPauliDisorderShell ω (k+1)
  let θ := fun i => u (pathCoeffEquiv (k+1) i)
  let e := qubitConfigFin (k+3)
  let M := spectralEnsembleMatrix (chainPauliFin (k+3)) θ
  have hM : M.IsHermitian := isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian _) θ
  have hm : ∃ hh : (Matrix.reindex e.symm e.symm M).IsHermitian,
      MaximallyProjectiveEnergy hh.eigenvalues :=
    ⟨hM.reindex e.symm,Matrix.IsHermitian.maximallyProjective_reindexAlgEquiv e.symm hM hω⟩
  have he : Matrix.reindex e.symm e.symm M = pathHamiltonian u := by
    have hh : Matrix.reindex e e (pathHamiltonian u) = M := reindex_pathHamiltonian u
    rw [← hh]
    ext x y
    simp [Matrix.reindex_apply]
  rw [he] at hm
  exact hm.choose_spec

#print axioms gaussian_path_all_prefixes_maximally_projective
end
end GaloisForLFunctions.HTGeometry

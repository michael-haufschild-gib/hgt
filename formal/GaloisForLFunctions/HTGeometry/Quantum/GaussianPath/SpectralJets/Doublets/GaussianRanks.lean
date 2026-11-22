import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.PhysicalTraceWitness
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.RealWitness

/-! # Exponential longitudinal response rank on a single Gaussian path draw -/
open Matrix MvPolynomial MeasureTheory ProbabilityTheory Filter
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section

private theorem typical_trace (n : ℕ) :
    ∃ k, ∀ᵐ θ ∂centredProductGaussian (Coordinates (n+2)) 1,
      eval₂Hom GaussianInt.toComplex (fun i => (θ i:ℂ)) (physicalTrace n k) ≠ 0 := by
  obtain ⟨k,z,hz⟩ := physicalTrace_witness n
  exact ⟨k,gaussian_ae_of_real_witness _ _ one_ne_zero ⟨z,hz⟩⟩

/-- On every prefix of at least three spins, the same Gaussian sample has 2^(N−1)
independent eigenvalue responses at the single even order N−1 rounded up. The
background remains fixed while the derivatives vary the actual onsite Z fields. -/
theorem gaussian_longitudinal_response_rank :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let n := k+1
      let a := pathPauliDisorderShell ω n
      let θ := fun i => a (pathCoeffEquiv n i)
      hasFieldMinor (numberedBackground n θ) (fun j => GaussianInt.toComplex ∘ spinCoefficient (n+2) j)
        (physicalWords n) := by
  apply ae_all_iff.mpr
  intro k
  let n := k+1
  obtain ⟨t,ht⟩ := typical_trace n
  have ha := (gaussian_pauli_prefix_coordinates_law n).quasiMeasurePreserving.ae ht
  filter_upwards [ha,gaussian_path_all_prefixes_maximally_projective] with ω hω hspec
  let a := pathPauliDisorderShell ω n
  let θ := fun i => a (pathCoeffEquiv n i)
  let e := qubitConfigFin (n+2)
  let H := (isSelfAdjoint_pathHamiltonian a).isHermitian
  have he : numberedBackground n θ = Matrix.reindex e e (pathHamiltonian a) :=
    (numberedBackground_eq n θ).trans (reindex_pathHamiltonian a).symm
  have hh : (numberedBackground n θ).IsHermitian := by rw [he]; exact H.reindex e
  have hs : (numberedBackground n θ).charpoly.Separable := by
    rw [he,Matrix.charpoly_reindex,H.charpoly_eq]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr (Complex.ofReal_injective.comp (hspec k).injective)
  exact (fieldTrace_iff (pencil (integralGenerators (n+2))) (spinCoefficient (n+2)) (physicalWords n)
    _ (fun j => maskWord_length _) GaussianInt.toComplex (fun i => (θ i:ℂ)) hh hs).mp ⟨t,hω⟩

#print axioms gaussian_longitudinal_response_rank
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets

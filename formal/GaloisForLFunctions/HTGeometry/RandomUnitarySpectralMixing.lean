import GaloisForLFunctions.HTGeometry.FiniteNoiseMixingApplications
import GaloisForLFunctions.HTGeometry.BistochasticKrausDeterminant
import GaloisForLFunctions.HTGeometry.FiniteQuantumOperationalMemoryLaw

/-!
# Ordinal-mixing inequalities for actual random-unitary quantum channels

The finite bistochastic argument of Sapienza, arXiv:2608.22463v1, Appendix A,
extends from diagonal observations to complete channel output spectra. A finite
probability law and arbitrary unitary operators construct the corpus's
`FiniteKrausChannel` directly. Both completeness identities are proved, and the
existing Kraus eigenbasis formula supplies the exact bistochastic spectral map.
-/

open scoped BigOperators ComplexOrder NNReal
open Matrix
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {n k : ℕ}

/-- Kraus operators of a probability mixture of arbitrary unitaries. -/
def probabilityUnitaryKraus (p : FiniteProbabilityLaw (Fin k))
    (U : Fin k → Matrix.unitaryGroup (Fin n) ℂ) (j : Fin k) : Matrix (Fin n) (Fin n) ℂ :=
  ((Real.sqrt (p.prob j) : ℝ) : ℂ) • (U j : Matrix (Fin n) (Fin n) ℂ)

/-- Every Kraus operator has scalar input effect equal to its probability. -/
theorem probabilityUnitaryKraus_adjoint_self (p : FiniteProbabilityLaw (Fin k))
    (U : Fin k → Matrix.unitaryGroup (Fin n) ℂ) (j : Fin k) :
    (probabilityUnitaryKraus p U j)ᴴ * probabilityUnitaryKraus p U j =
      (p.prob j : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold probabilityUnitaryKraus
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← Matrix.star_eq_conjTranspose]
  have hU : star (U j : Matrix (Fin n) (Fin n) ℂ) * (U j : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem (U j).property
  rw [hU]
  congr 1
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (p.nonneg j)]

/-- The output effect is the same scalar, proving unitality as well. -/
theorem probabilityUnitaryKraus_self_adjoint (p : FiniteProbabilityLaw (Fin k))
    (U : Fin k → Matrix.unitaryGroup (Fin n) ℂ) (j : Fin k) :
    probabilityUnitaryKraus p U j * (probabilityUnitaryKraus p U j)ᴴ =
      (p.prob j : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold probabilityUnitaryKraus
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← Matrix.star_eq_conjTranspose]
  have hU : (U j : Matrix (Fin n) (Fin n) ℂ) * star (U j : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Unitary.mul_star_self_of_mem (U j).property
  rw [hU]
  congr 1
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (p.nonneg j)]

/-- The constructed Kraus family is trace preserving. -/
theorem probabilityUnitaryKraus_complete (p : FiniteProbabilityLaw (Fin k))
    (U : Fin k → Matrix.unitaryGroup (Fin n) ℂ) :
    (∑ j, (probabilityUnitaryKraus p U j)ᴴ * probabilityUnitaryKraus p U j) = 1 := by
  simp_rw [probabilityUnitaryKraus_adjoint_self, ← Finset.sum_smul,
    ← Complex.ofReal_sum, p.sum_prob, Complex.ofReal_one, one_smul]

/-- The constructed Kraus family is unital. -/
theorem probabilityUnitaryKraus_unital (p : FiniteProbabilityLaw (Fin k))
    (U : Fin k → Matrix.unitaryGroup (Fin n) ℂ) :
    (∑ j, probabilityUnitaryKraus p U j * (probabilityUnitaryKraus p U j)ᴴ) = 1 := by
  simp_rw [probabilityUnitaryKraus_self_adjoint, ← Finset.sum_smul,
    ← Complex.ofReal_sum, p.sum_prob, Complex.ofReal_one, one_smul]

/-- An actual corpus quantum channel, requiring no completeness premise. -/
def probabilityUnitaryChannel (p : FiniteProbabilityLaw (Fin k))
    (U : Fin k → Matrix.unitaryGroup (Fin n) ℂ) : RHTower.FiniteKrausChannel n k where
  operator := probabilityUnitaryKraus p U
  completeness := probabilityUnitaryKraus_complete p U

/-- Channel evolution of an arbitrary Gram state is positive semidefinite. -/
theorem probabilityUnitaryChannel_gram_posSemidef (p : FiniteProbabilityLaw (Fin k))
    (U : Fin k → Matrix.unitaryGroup (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ((probabilityUnitaryChannel p U).evolveMatrix (Aᴴ * A)).PosSemidef :=
  (probabilityUnitaryChannel p U).evolveMatrix_posSemidef (Matrix.posSemidef_conjTranspose_mul_self A)

/-- The channel's exact spectral mixing, assembled from the existing Kraus eigenweights. -/
def probabilityUnitarySpectralMixing (p : FiniteProbabilityLaw (Fin k))
    (U : Fin k → Matrix.unitaryGroup (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    doublyStochastic ℝ (Fin n) := by
  let hX := Matrix.isHermitian_conjTranspose_mul_self A
  let hY := (probabilityUnitaryChannel_gram_posSemidef p U A).isHermitian
  refine ⟨bistochasticKrausEigenWeight (probabilityUnitaryKraus p U) hX hY,
    mem_doublyStochastic_iff_sum.mpr ⟨?_, ?_, ?_⟩⟩
  · exact bistochasticKrausEigenWeight_nonneg _ _ _
  · exact sum_bistochasticKrausEigenWeight_row _ _ _ (probabilityUnitaryKraus_unital p U)
  · exact sum_bistochasticKrausEigenWeight_column _ _ _ (probabilityUnitaryKraus_complete p U)

/-- The output eigenvalues are the actual bistochastic image of the input spectrum. -/
theorem probabilityUnitarySpectralMixing_eigenvalues (p : FiniteProbabilityLaw (Fin k))
    (U : Fin k → Matrix.unitaryGroup (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (probabilityUnitaryChannel_gram_posSemidef p U A).isHermitian.eigenvalues =
      (probabilityUnitarySpectralMixing p U A).val *ᵥ
        (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues := by
  funext i
  exact eigenvalues_kraus_sum_eq_weighted_sum (probabilityUnitaryKraus p U)
    (Matrix.isHermitian_conjTranspose_mul_self A)
    (probabilityUnitaryChannel_gram_posSemidef p U A).isHermitian rfl i

/-- Every spectral top-sum decreases under an actual probability-unitary channel. -/
theorem probabilityUnitaryChannel_spectral_topSum_le (p : FiniteProbabilityLaw (Fin k))
    (U : Fin k → Matrix.unitaryGroup (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (r : Fin (n + 1)) :
    topSum r.val (probabilityUnitaryChannel_gram_posSemidef p U A).isHermitian.eigenvalues ≤
      topSum r.val (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues := by
  rw [probabilityUnitarySpectralMixing_eigenvalues]
  exact bistochasticMixing_topSum_le _ _ r

/-- Spectral purity contracts without an input nondegeneracy or full-rank premise. -/
theorem probabilityUnitaryChannel_spectral_purity_le (p : FiniteProbabilityLaw (Fin k))
    (U : Fin k → Matrix.unitaryGroup (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, (probabilityUnitaryChannel_gram_posSemidef p U A).isHermitian.eigenvalues i ^ 2) ≤
      ∑ i, (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i ^ 2 := by
  rw [probabilityUnitarySpectralMixing_eigenvalues]
  exact bistochasticMixing_sum_sq_le _ _

/-- The corpus's Shannon functional increases on the full channel spectrum. -/
theorem probabilityUnitaryChannel_spectral_entropy_le (p : FiniteProbabilityLaw (Fin k))
    (U : Fin k → Matrix.unitaryGroup (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    entropy (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues ≤
      entropy (probabilityUnitaryChannel_gram_posSemidef p U A).isHermitian.eigenvalues := by
  let x : Fin n → ℝ≥0 := fun i => ⟨(Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i,
    (Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg i⟩
  have h := bistochasticMixing_negMulLog_sum_le (probabilityUnitarySpectralMixing p U A) x
  change (∑ i, Real.negMulLog ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)) ≤
    ∑ i, Real.negMulLog (((probabilityUnitarySpectralMixing p U A).val *ᵥ
      (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues) i) at h
  rw [← probabilityUnitarySpectralMixing_eigenvalues] at h
  simpa only [entropy, tsum_fintype, Real.negMulLog, neg_mul] using h

end
end GaloisForLFunctions.HTGeometry

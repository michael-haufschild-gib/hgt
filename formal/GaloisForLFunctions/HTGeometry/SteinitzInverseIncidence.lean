import GaloisForLFunctions.HTGeometry.SteinitzInverseCovariance
import GaloisForLFunctions.HTGeometry.CrouzeixWeightedIncidence
import GaloisForLFunctions.HTGeometry.CrouzeixKrausEnergy

/-!
# Inverse remainder on weighted incidence and quantum outputs

Apply the Steinitz inverse-branch matrix lift to existing weighted synthesis and
Kraus output synthesis. Both applications give rank-free inverse stability and
identify their zero remainder with saturation of the Crouzeix Gram energy bound.
-/

open Matrix
open scoped Matrix NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Weighted

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The inverse remainder detects equality of the existing weighted covariance matrices. -/
theorem finiteWeightedInverseRemainder_saturation
    (a : ι → ℝ≥0) (u : ι → Fin d → ℂ) (b : κ → ℝ≥0) (v : κ → Fin d → ℂ) :
    (synthesisInverseRemainder (finiteWeightedSynthesisMatrix a u)
      (finiteWeightedSynthesisMatrix b v)).trace.re = 0 ↔
        finiteWeightedCovarianceMatrix a u = finiteWeightedCovarianceMatrix b v := by
  simpa only [finiteWeightedSynthesisMatrix_mul_conjTranspose] using
    synthesisInverseRemainder_trace_eq_zero_iff (finiteWeightedSynthesisMatrix a u)
      (finiteWeightedSynthesisMatrix b v)

/-- Weighted inverse-covariance stability is controlled without a rank premise. -/
theorem finiteWeightedInverseRemainder_distance_bound
    (a : ι → ℝ≥0) (u : ι → Fin d → ℂ) (b : κ → ℝ≥0) (v : κ → Fin d → ℂ) :
    finiteMatrixHilbertSchmidtSq
      ((finitePositiveMatrixRegularization (finiteWeightedCovarianceMatrix a u) 1)⁻¹ -
        (finitePositiveMatrixRegularization (finiteWeightedCovarianceMatrix b v) 1)⁻¹) ≤
      (synthesisInverseRemainder (finiteWeightedSynthesisMatrix a u)
        (finiteWeightedSynthesisMatrix b v)).trace.re := by
  simpa only [synthesisResolvent, synthesisRegularizedCovariance,
    finiteWeightedSynthesisMatrix_mul_conjTranspose] using
    synthesisResolvent_distance_bound (finiteWeightedSynthesisMatrix a u)
      (finiteWeightedSynthesisMatrix b v)

variable [DecidableEq ι] [DecidableEq κ]

/-- The Crouzeix coupling gap and Steinitz inverse remainder have identical zero sets. -/
theorem finiteWeightedCrouzeix_saturation_iff_inverse_remainder_zero
    (a : ι → ℝ≥0) (u : ι → Fin d → ℂ) (b : κ → ℝ≥0) (v : κ → Fin d → ℂ) :
    (2 * finiteMatrixHilbertSchmidtSq (finiteWeightedIncidenceMatrix a u b v) =
      finiteMatrixHilbertSchmidtSq (finiteWeightedCovarianceMatrix a u) +
        finiteMatrixHilbertSchmidtSq (finiteWeightedCovarianceMatrix b v)) ↔
    (synthesisInverseRemainder (finiteWeightedSynthesisMatrix a u)
      (finiteWeightedSynthesisMatrix b v)).trace.re = 0 := by
  rw [finiteWeightedIncidence_energy_saturation, finiteWeightedInverseRemainder_saturation]

end Weighted

section Kraus

variable {d e o : ℕ} {κ τ ι ν : Type*}
  [Fintype κ] [Fintype τ] [Fintype ι] [Fintype ν]
  [DecidableEq κ] [DecidableEq τ]

/-- The inverse remainder detects equality of quantum-channel outputs, independent of presentation. -/
theorem FiniteRectangularKrausChannel.output_inverse_remainder_saturation
    (Phi : FiniteRectangularKrausChannel d o κ) (Psi : FiniteRectangularKrausChannel e o τ)
    (A : Matrix (Fin d) ι ℂ) (B : Matrix (Fin e) ν ℂ) :
    (synthesisInverseRemainder (Phi.outputSynthesis A) (Psi.outputSynthesis B)).trace.re = 0 ↔
      Phi.evolveMatrix (A * Aᴴ) = Psi.evolveMatrix (B * Bᴴ) := by
  simpa only [outputSynthesis_covariance] using
    synthesisInverseRemainder_trace_eq_zero_iff (Phi.outputSynthesis A) (Psi.outputSynthesis B)

/-- Output inverse stability applies even when the channels have different input dimensions. -/
theorem FiniteRectangularKrausChannel.output_inverse_remainder_distance_bound
    (Phi : FiniteRectangularKrausChannel d o κ) (Psi : FiniteRectangularKrausChannel e o τ)
    (A : Matrix (Fin d) ι ℂ) (B : Matrix (Fin e) ν ℂ) :
    finiteMatrixHilbertSchmidtSq
      ((finitePositiveMatrixRegularization (Phi.evolveMatrix (A * Aᴴ)) 1)⁻¹ -
        (finitePositiveMatrixRegularization (Psi.evolveMatrix (B * Bᴴ)) 1)⁻¹) ≤
      (synthesisInverseRemainder (Phi.outputSynthesis A) (Psi.outputSynthesis B)).trace.re := by
  simpa only [synthesisResolvent, synthesisRegularizedCovariance, outputSynthesis_covariance] using
    synthesisResolvent_distance_bound (Phi.outputSynthesis A) (Psi.outputSynthesis B)

variable [DecidableEq ι] [DecidableEq ν]

/-- Crouzeix saturation and zero inverse remainder are equivalent for arbitrary channel outputs. -/
theorem FiniteRectangularKrausChannel.output_crouzeix_iff_inverse_remainder_zero
    (Phi : FiniteRectangularKrausChannel d o κ) (Psi : FiniteRectangularKrausChannel e o τ)
    (A : Matrix (Fin d) ι ℂ) (B : Matrix (Fin e) ν ℂ) :
    (2 * finiteMatrixHilbertSchmidtSq ((Phi.outputSynthesis A)ᴴ * Psi.outputSynthesis B) =
      finiteMatrixHilbertSchmidtSq (Phi.evolveMatrix (A * Aᴴ)) +
        finiteMatrixHilbertSchmidtSq (Psi.evolveMatrix (B * Bᴴ))) ↔
    (synthesisInverseRemainder (Phi.outputSynthesis A) (Psi.outputSynthesis B)).trace.re = 0 := by
  rw [output_energy_saturation, output_inverse_remainder_saturation]

end Kraus

end

end GaloisForLFunctions.HTGeometry

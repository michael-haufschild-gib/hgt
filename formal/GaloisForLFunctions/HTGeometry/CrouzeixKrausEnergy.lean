import GaloisForLFunctions.HTGeometry.CrouzeixGramEnergy
import GaloisForLFunctions.HTGeometry.FiniteBuresKrausDataProcessingLaw

/-!
# Positive-block energy of quantum channel outputs

A horizontal synthesis of the Kraus images factors the evolved covariance. Applying the
Crouzeix Gram-block identity to two such syntheses measures the exact output discrepancy.
The channels may have different input dimensions, Kraus counts, and synthesis ranks.
-/

open Matrix
open scoped BigOperators ComplexConjugate Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d e o : ℕ} {κ τ x y : Type*}
  [Fintype κ] [Fintype τ] [Fintype x] [Fintype y]
  [DecidableEq κ] [DecidableEq τ] [DecidableEq x] [DecidableEq y]

omit [Fintype x] [DecidableEq x] in
/-- Horizontal synthesis of the images of every input feature under every Kraus operator. -/
def FiniteRectangularKrausChannel.outputSynthesis
    (Phi : FiniteRectangularKrausChannel d o κ) (A : Matrix (Fin d) x ℂ) :
    Matrix (Fin o) (κ × x) ℂ :=
  fun i p => (Phi.operator p.1 * A) i p.2

omit [DecidableEq x] in
/-- The channel output has a canonical Gram factor with all Kraus labels retained. -/
theorem FiniteRectangularKrausChannel.outputSynthesis_covariance
    (Phi : FiniteRectangularKrausChannel d o κ) (A : Matrix (Fin d) x ℂ) :
    Phi.outputSynthesis A * (Phi.outputSynthesis A)ᴴ = Phi.evolveMatrix (A * Aᴴ) := by
  calc
    _ = ∑ a, (Phi.operator a * A) * (Phi.operator a * A)ᴴ := by
      ext i j
      simp only [outputSynthesis, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Matrix.sum_apply]
    _ = _ := by
      unfold evolveMatrix
      apply Finset.sum_congr rfl
      intro a _
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Cross-collision energy between two channels has exactly the output-covariance deficit. -/
theorem FiniteRectangularKrausChannel.output_energy_identity
    (Phi : FiniteRectangularKrausChannel d o κ)
    (Psi : FiniteRectangularKrausChannel e o τ)
    (A : Matrix (Fin d) x ℂ) (B : Matrix (Fin e) y ℂ) :
    finiteMatrixHilbertSchmidtSq (Phi.evolveMatrix (A * Aᴴ)) +
        finiteMatrixHilbertSchmidtSq (Psi.evolveMatrix (B * Bᴴ)) -
        2 * finiteMatrixHilbertSchmidtSq ((Phi.outputSynthesis A)ᴴ * Psi.outputSynthesis B) =
      finiteMatrixHilbertSchmidtSq
        (Phi.evolveMatrix (A * Aᴴ) - Psi.evolveMatrix (B * Bᴴ)) := by
  simpa only [finiteMatrixHilbertSchmidtSq_gram_duality, outputSynthesis_covariance] using
    crouzeix_gram_energy_identity (Phi.outputSynthesis A) (Psi.outputSynthesis B)

/-- Every pair of Kraus output syntheses obeys the same positive-block energy bound. -/
theorem FiniteRectangularKrausChannel.output_energy_bound
    (Phi : FiniteRectangularKrausChannel d o κ)
    (Psi : FiniteRectangularKrausChannel e o τ)
    (A : Matrix (Fin d) x ℂ) (B : Matrix (Fin e) y ℂ) :
    2 * finiteMatrixHilbertSchmidtSq ((Phi.outputSynthesis A)ᴴ * Psi.outputSynthesis B) ≤
      finiteMatrixHilbertSchmidtSq (Phi.evolveMatrix (A * Aᴴ)) +
        finiteMatrixHilbertSchmidtSq (Psi.evolveMatrix (B * Bᴴ)) := by
  simpa only [finiteMatrixHilbertSchmidtSq_gram_duality, outputSynthesis_covariance] using
    crouzeix_gram_energy_bound (Phi.outputSynthesis A) (Psi.outputSynthesis B)

/-- Saturation means indistinguishable output covariances, regardless of the Kraus presentation. -/
theorem FiniteRectangularKrausChannel.output_energy_saturation
    (Phi : FiniteRectangularKrausChannel d o κ)
    (Psi : FiniteRectangularKrausChannel e o τ)
    (A : Matrix (Fin d) x ℂ) (B : Matrix (Fin e) y ℂ) :
    2 * finiteMatrixHilbertSchmidtSq ((Phi.outputSynthesis A)ᴴ * Psi.outputSynthesis B) =
        finiteMatrixHilbertSchmidtSq (Phi.evolveMatrix (A * Aᴴ)) +
          finiteMatrixHilbertSchmidtSq (Psi.evolveMatrix (B * Bᴴ)) ↔
      Phi.evolveMatrix (A * Aᴴ) = Psi.evolveMatrix (B * Bᴴ) := by
  simpa only [finiteMatrixHilbertSchmidtSq_gram_duality, outputSynthesis_covariance] using
    crouzeix_gram_energy_saturation (Phi.outputSynthesis A) (Psi.outputSynthesis B)

/-- A single output entry discrepancy lower-bounds the total cross-collision deficit. -/
theorem FiniteRectangularKrausChannel.output_energy_entry_bound
    (Phi : FiniteRectangularKrausChannel d o κ)
    (Psi : FiniteRectangularKrausChannel e o τ)
    (A : Matrix (Fin d) x ℂ) (B : Matrix (Fin e) y ℂ) (i j : Fin o) :
    ‖Phi.evolveMatrix (A * Aᴴ) i j - Psi.evolveMatrix (B * Bᴴ) i j‖ ^ 2 ≤
      finiteMatrixHilbertSchmidtSq (Phi.evolveMatrix (A * Aᴴ)) +
        finiteMatrixHilbertSchmidtSq (Psi.evolveMatrix (B * Bᴴ)) -
        2 * finiteMatrixHilbertSchmidtSq ((Phi.outputSynthesis A)ᴴ * Psi.outputSynthesis B) := by
  simpa only [finiteMatrixHilbertSchmidtSq_gram_duality, outputSynthesis_covariance] using
    crouzeix_gram_energy_entry_bound (Phi.outputSynthesis A) (Psi.outputSynthesis B) i j

end

end GaloisForLFunctions.HTGeometry

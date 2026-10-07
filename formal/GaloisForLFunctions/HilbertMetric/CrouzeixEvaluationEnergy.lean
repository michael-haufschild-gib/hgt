import GaloisForLFunctions.HTGeometry.CrouzeixGramEnergy
import GaloisForLFunctions.HilbertMetric.ComplexPrescribedEvaluationReconstruction

/-!
# Positive-block energy on prescribed evaluation packets

The diagonal blocks are the existing feature Grams on two prescribed packets. Their
cross-coupling deficit is exactly the discrepancy of the sample-side reproducing kernels.
Thus maximal coupling is characterized by equality of sample kernels, even when the two
feature systems and their sample spaces differ.
-/

open Matrix
open scoped BigOperators ComplexConjugate Matrix

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

open HTGeometry

variable {κ X Y : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- The sample-side kernel sums feature products at each ordered pair of packet points. -/
theorem complexEvaluationMatrix_mul_conjTranspose
    (u : κ → X → ℂ) (p : κ → X) (i j : κ) :
    (complexEvaluationMatrix u p * (complexEvaluationMatrix u p)ᴴ) i j =
      ∑ k, u k (p i) * star (u k (p j)) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, complexEvaluationMatrix]

/-- Coupling two prescribed feature packets gives an exact sample-kernel discrepancy. -/
theorem complexEvaluation_energy_identity
    (u : κ → X → ℂ) (p : κ → X) (v : κ → Y → ℂ) (q : κ → Y) :
    finiteMatrixHilbertSchmidtSq (complexEvaluationGram u p) +
        finiteMatrixHilbertSchmidtSq (complexEvaluationGram v q) -
        2 * finiteMatrixHilbertSchmidtSq
          ((complexEvaluationMatrix u p)ᴴ * complexEvaluationMatrix v q) =
      finiteMatrixHilbertSchmidtSq
        (complexEvaluationMatrix u p * (complexEvaluationMatrix u p)ᴴ -
          complexEvaluationMatrix v q * (complexEvaluationMatrix v q)ᴴ) := by
  simpa only [complexEvaluationGram_eq_conjTranspose_mul] using
    crouzeix_gram_energy_identity (complexEvaluationMatrix u p) (complexEvaluationMatrix v q)

/-- The existing prescribed evaluation Grams bound all cross-feature collision energy. -/
theorem complexEvaluation_energy_bound
    (u : κ → X → ℂ) (p : κ → X) (v : κ → Y → ℂ) (q : κ → Y) :
    2 * finiteMatrixHilbertSchmidtSq
        ((complexEvaluationMatrix u p)ᴴ * complexEvaluationMatrix v q) ≤
      finiteMatrixHilbertSchmidtSq (complexEvaluationGram u p) +
        finiteMatrixHilbertSchmidtSq (complexEvaluationGram v q) := by
  simpa only [complexEvaluationGram_eq_conjTranspose_mul] using
    crouzeix_gram_energy_bound (complexEvaluationMatrix u p) (complexEvaluationMatrix v q)

/-- Saturation is equivalent to equality of every sample-side reproducing-kernel entry. -/
theorem complexEvaluation_energy_saturation
    (u : κ → X → ℂ) (p : κ → X) (v : κ → Y → ℂ) (q : κ → Y) :
    2 * finiteMatrixHilbertSchmidtSq
        ((complexEvaluationMatrix u p)ᴴ * complexEvaluationMatrix v q) =
        finiteMatrixHilbertSchmidtSq (complexEvaluationGram u p) +
          finiteMatrixHilbertSchmidtSq (complexEvaluationGram v q) ↔
      ∀ i j, (∑ k, u k (p i) * star (u k (p j))) =
        ∑ k, v k (q i) * star (v k (q j)) := by
  rw [complexEvaluationGram_eq_conjTranspose_mul,
    complexEvaluationGram_eq_conjTranspose_mul, crouzeix_gram_energy_saturation]
  constructor
  · intro he i j
    simpa only [complexEvaluationMatrix_mul_conjTranspose] using
      congrArg (fun M : Matrix κ κ ℂ => M i j) he
  · intro he
    ext i j
    simpa only [complexEvaluationMatrix_mul_conjTranspose] using he i j

/-- A discrepancy between two sampled kernel entries certifies a quantitative coupling deficit. -/
theorem complexEvaluation_kernel_entry_bound
    (u : κ → X → ℂ) (p : κ → X) (v : κ → Y → ℂ) (q : κ → Y) (i j : κ) :
    ‖(∑ k, u k (p i) * star (u k (p j))) -
        ∑ k, v k (q i) * star (v k (q j))‖ ^ 2 ≤
      finiteMatrixHilbertSchmidtSq (complexEvaluationGram u p) +
        finiteMatrixHilbertSchmidtSq (complexEvaluationGram v q) -
        2 * finiteMatrixHilbertSchmidtSq
          ((complexEvaluationMatrix u p)ᴴ * complexEvaluationMatrix v q) := by
  simpa only [complexEvaluationGram_eq_conjTranspose_mul,
    complexEvaluationMatrix_mul_conjTranspose] using
    crouzeix_gram_energy_entry_bound (complexEvaluationMatrix u p)
      (complexEvaluationMatrix v q) i j

end

end GaloisForLFunctions.HilbertMetric

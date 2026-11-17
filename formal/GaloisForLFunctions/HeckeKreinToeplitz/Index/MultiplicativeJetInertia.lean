import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Coleman.MomentFunctionalJets
import GaloisForLFunctions.HTGeometry.SignedAtomicMomentInertia

/-!
# Exact inertia of multiplicative-jet Hankel matrices

The finite Amice transform converts coefficients to invariant-derivative
moments. Its full Hankel block is consequently congruent to the diagonal
coefficient form: positive, negative and null indices count coefficient signs.
-/

noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz
open Polynomial
open ArithmeticHarmonicAnalysis.Coleman

/-- Hankel matrix of all invariant jets of a finite Amice transform. -/
def multiplicativeJetHankel {d : ℕ} (a : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  HTGeometry.algebraicHankelMatrix
    (fun k => multiplicativeJet k ((Polynomial.ofFn d a).comp (1 + X))) d

private theorem integralNodes_injective (d : ℕ) :
    Function.Injective (fun i : Fin d => (i.val : ℝ)) := by
  intro i j h
  apply Fin.ext
  change (i.val : ℝ) = (j.val : ℝ) at h
  exact_mod_cast h

private theorem jetHankel_eq {d : ℕ} (a : Fin d → ℝ) :
    multiplicativeJetHankel a =
      HTGeometry.algebraicHankelMatrix
        (HTGeometry.finiteModalSequence a (fun i => (i.val : ℝ))) d := by
  unfold multiplicativeJetHankel
  congr 1
  funext k
  rw [multiplicativeJet_ofFn]
  rfl

/-- Negative directions in the full jet Hankel block count precisely negative coefficients. -/
theorem sigNeg_multiplicativeJetHankel {d : ℕ} (a : Fin d → ℝ) :
    sigNeg (multiplicativeJetHankel a).toQuadraticForm' = {i | a i < 0}.ncard := by
  rw [jetHankel_eq]
  exact HTGeometry.sigNeg_algebraicHankelMatrix_finiteModalSequence
    (integralNodes_injective d)

/-- Positive directions count precisely positive coefficients. -/
theorem sigPos_multiplicativeJetHankel {d : ℕ} (a : Fin d → ℝ) :
    sigPos (multiplicativeJetHankel a).toQuadraticForm' = {i | 0 < a i}.ncard := by
  rw [jetHankel_eq]
  exact HTGeometry.sigPos_algebraicHankelMatrix_finiteModalSequence
    (integralNodes_injective d)

/-- Null directions count precisely zero coefficients. -/
theorem finrank_radical_multiplicativeJetHankel {d : ℕ} (a : Fin d → ℝ) :
    Module.finrank ℝ (multiplicativeJetHankel a).toQuadraticForm'.radical =
      {i | a i = 0}.ncard := by
  rw [jetHankel_eq]
  exact HTGeometry.finrank_radical_algebraicHankelMatrix_finiteModalSequence
    (integralNodes_injective d)

end GaloisForLFunctions.HeckeKreinToeplitz

#print axioms GaloisForLFunctions.HeckeKreinToeplitz.sigNeg_multiplicativeJetHankel
#print axioms GaloisForLFunctions.HeckeKreinToeplitz.sigPos_multiplicativeJetHankel
#print axioms GaloisForLFunctions.HeckeKreinToeplitz.finrank_radical_multiplicativeJetHankel

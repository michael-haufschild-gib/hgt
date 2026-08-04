import GaloisForLFunctions.HTGeometry.ProductLawAssembly
import GaloisForLFunctions.HTGeometry.UniformScaledDeterminant

/-!
# The head product's Jacobian as a bordered determinant

The head product is logarithmically linear, so its jets are the product times Bell values, and its
Jacobian has the uniformly scaled shape.  Row reduction against the first row therefore turns its
determinant into a power of the product times the bordered determinant whose first row is the gradient
of the product itself.

This is as far as the algebra goes without further input: what is left is a determinant of gradients
of Bell values, bordered by the gradient of the product, in the rational model.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-- The gradient of the head product. -/
noncomputable def headGradient (n : ℕ) : Fin (n + 1) → CascadeField :=
  fun j => fpderiv ((j : ℕ) + 1) (prodHead Q (n + 2))

/-- The gradients of the positive Bell values of the head product's multiplier. -/
noncomputable def headBellGradient (n : ℕ) : Fin n → Fin (n + 1) → CascadeField :=
  fun r j => fpderiv ((j : ℕ) + 1)
    (prodBell Q v (logSum Q v (n + 2)) ((r : ℕ) + 1))

/-- **The head product's Jacobian has the uniformly scaled shape.** -/
theorem headJetJacobian_eq_uniform {Q : ℕ → Polynomial ℂ} (hQ : ∀ j, Q j ≠ 0) (n : ℕ) :
    headJetJacobian Q v (n + 1)
      = uniformScaledMatrix (prodHead Q (n + 2)) (headGradient Q n)
          (fun r : Fin n => prodBell Q v (logSum Q v (n + 2)) ((r : ℕ) + 1))
          (headBellGradient Q v n) := by
  funext i j
  refine Fin.cases ?_ (fun r => ?_) i
  · simp [headJetJacobian, uniformScaledMatrix, headGradient]
  · have hjet : ((prodDerivation Q v : CascadeField → CascadeField)^[((r.succ : Fin (n + 1)) : ℕ)])
        (prodHead Q (n + 1 + 1))
        = prodHead Q (n + 2) * prodBell Q v (logSum Q v (n + 2)) ((r : ℕ) + 1) := by
      rw [Fin.val_succ]
      exact iterate_prodHead v hQ (n + 2) ((r : ℕ) + 1)
    simp only [headJetJacobian, Matrix.of_apply, uniformScaledMatrix, Fin.cases_succ, hjet,
      Derivation.leibniz, smul_eq_mul, headGradient, headBellGradient]

/-- **The head product's Jacobian determinant, reduced.** -/
theorem headJetJacobian_det_eq {Q : ℕ → Polynomial ℂ} (hQ : ∀ j, Q j ≠ 0) (n : ℕ) :
    (headJetJacobian Q v (n + 1)).det
      = prodHead Q (n + 2) ^ n
        * (uniformBordered (headGradient Q n) (headBellGradient Q v n)).det := by
  rw [headJetJacobian_eq_uniform v hQ n, uniformScaledMatrix_det]

/-- **Nonvanishing reduces to the bordered determinant.** -/
theorem headJetJacobian_det_ne_zero_of_bordered {Q : ℕ → Polynomial ℂ} (hQ : ∀ j, Q j ≠ 0) (n : ℕ)
    (hb : (uniformBordered (headGradient Q n) (headBellGradient Q v n)).det ≠ 0) :
    (headJetJacobian Q v (n + 1)).det ≠ 0 := by
  rw [headJetJacobian_det_eq v hQ n]
  exact mul_ne_zero (pow_ne_zero _ (prodHead_ne_zero hQ (n + 2))) hb

end GaloisForLFunctions.HTGeometry

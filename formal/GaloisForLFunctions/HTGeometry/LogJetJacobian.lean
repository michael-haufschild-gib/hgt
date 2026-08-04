import GaloisForLFunctions.HTGeometry.HeadGradientLogarithmic
import GaloisForLFunctions.HTGeometry.ProductLawBorderedRows

/-!
# The reformulated determinant

Collecting the reductions: the head product's jet Jacobian is a power of the product times the
Jacobian of the jets of the logarithm `L = ∑_k log Q_k(X_k)` — the border row being `∂_j L` and the
rest the gradients of the jets of `δL`.

This isolates the one open statement of the polynomial-coefficient programme in its simplest form.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-- The Jacobian of the jets of the logarithm: border row `∂_j L`, remaining rows `∂_j δ^r (δL)`. -/
noncomputable def logJetJacobian (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) CascadeField :=
  uniformBordered (logGradient Q n)
    (fun r : Fin n => fun j : Fin (n + 1) =>
      fpderiv ((j : ℕ) + 1)
        (((prodDerivation Q v : CascadeField → CascadeField)^[(r : ℕ)])
          (logSum Q v (n + 2))))

/-- **The head Jacobian is a power of the head product times the logarithmic Jacobian.** -/
theorem headJetJacobian_det_eq_log {Q : ℕ → Polynomial ℂ} (hQ : ∀ j, Q j ≠ 0) (n : ℕ) :
    (headJetJacobian Q v (n + 1)).det
      = prodHead Q (n + 2) ^ (n + 1) * (logJetJacobian Q v n).det := by
  rw [headJetJacobian_det_eq v hQ n, uniformBordered_headGradient_det hQ n,
    logJetJacobian]
  have hbell : (uniformBordered (logGradient Q n) (headBellGradient Q v n)).det
      = (uniformBordered (logGradient Q n)
          (fun r : Fin n => fun j : Fin (n + 1) =>
            fpderiv ((j : ℕ) + 1)
              (((prodDerivation Q v : CascadeField → CascadeField)^[(r : ℕ)])
                (logSum Q v (n + 2))))).det :=
    uniformBordered_bell_det_eq Q v (logSum Q v (n + 2)) n (logGradient Q n)
  rw [hbell]
  ring

/-- **Nonvanishing reduces to the logarithmic Jacobian.** -/
theorem headJetJacobian_det_ne_zero_of_log {Q : ℕ → Polynomial ℂ} (hQ : ∀ j, Q j ≠ 0) (n : ℕ)
    (hlog : (logJetJacobian Q v n).det ≠ 0) :
    (headJetJacobian Q v (n + 1)).det ≠ 0 := by
  rw [headJetJacobian_det_eq_log v hQ n]
  exact mul_ne_zero (pow_ne_zero _ (prodHead_ne_zero hQ (n + 2))) hlog

/-- **The base case of the logarithmic Jacobian.** -/
theorem logJetJacobian_det_zero {Q : ℕ → Polynomial ℂ} (hQ1 : (Q 1).derivative ≠ 0)
    (hQ1' : Q 1 ≠ 0) :
    (logJetJacobian Q v 0).det ≠ 0 := by
  rw [Matrix.det_fin_one]
  have hval : logJetJacobian Q v 0 0 0 = logFactor (Q 1) 1 := by
    simp [logJetJacobian, uniformBordered, logGradient]
  rw [hval, logFactor]
  exact div_ne_zero (fact_ne_zero hQ1 1) (fact_ne_zero hQ1' 1)

end GaloisForLFunctions.HTGeometry

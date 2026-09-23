import GaloisForLFunctions.HTGeometry.LogJetJacobian
import GaloisForLFunctions.HTGeometry.ScaledLogModel

/-!
# The logarithmic Jacobian at height three

Writing out the `2×2` determinant with the closed-form entries: the border row is the pair of
logarithmic derivatives, the second row is the pair of Wronskian terms plus, in the lower column, the
tail of the sum multiplied by that column's logarithmic derivative.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-- **The height-three logarithmic determinant, in closed form.** -/
theorem logJetJacobian_one_det {Q : ℕ → Polynomial ℂ} (v : ℕ → Polynomial ℂ)
    (hQ : ∀ i, Q i ≠ 0) :
    (logJetJacobian Q v 1).det
      = logFactor (Q 1) 1
          * (prodHead Q 2
              * (fact (scaledLogWronskian (Q 2) (v 2)) 2 / fact (Q 2) 2 ^ (2 : ℕ)))
        - logFactor (Q 2) 2
          * (prodHead Q 1
                * (fact (scaledLogWronskian (Q 1) (v 1)) 1 / fact (Q 1) 1 ^ (2 : ℕ))
              + logFactor (Q 1) 1 * (logFactor (Q 2) 2 * prodJet Q v 2)) := by
  have h00 : logJetJacobian Q v 1 0 0 = logFactor (Q 1) 1 := by
    simp [logJetJacobian, uniformBordered, logGradient]
  have h01 : logJetJacobian Q v 1 0 1 = logFactor (Q 2) 2 := by
    simp [logJetJacobian, uniformBordered, logGradient]
  have h10 : logJetJacobian Q v 1 1 0 = fpderiv 1 (logSum Q v 3) := by
    simp only [logJetJacobian, uniformBordered, Matrix.of_apply]
    rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cases_succ]
    simp
  have h11 : logJetJacobian Q v 1 1 1 = fpderiv 2 (logSum Q v 3) := by
    simp only [logJetJacobian, uniformBordered, Matrix.of_apply]
    rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cases_succ]
    simp
  have hrow0 : fpderiv 1 (logSum Q v 3)
      = prodHead Q 1 * (fact (scaledLogWronskian (Q 1) (v 1)) 1 / fact (Q 1) 1 ^ (2 : ℕ))
        + logFactor (Q 1) 1 * (logFactor (Q 2) 2 * prodJet Q v 2) := by
    have h := fpderiv_logSum_row (Q := Q) v hQ (n := 1) (j := 0) (by omega)
    rw [h]
    congr 2
    simp only [show (1 : ℕ) + 2 = 3 from rfl, show (0 : ℕ) + 2 = 2 from rfl]
    rw [show (3 : ℕ) = 2 + 1 from rfl, logSum_succ]
    ring
  have hrow1 : fpderiv 2 (logSum Q v 3)
      = prodHead Q 2 * (fact (scaledLogWronskian (Q 2) (v 2)) 2 / fact (Q 2) 2 ^ (2 : ℕ)) := by
    have h := fpderiv_logSum_row (Q := Q) v hQ (n := 1) (j := 1) (by omega)
    rw [h]
    simp
  rw [Matrix.det_fin_two, h00, h01, h10, h11, hrow0, hrow1]

end GaloisForLFunctions.HTGeometry

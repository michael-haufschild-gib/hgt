import GaloisForLFunctions.HTGeometry.BellSubstitutionJacobian
import GaloisForLFunctions.HTGeometry.TerminalLinearJacobian

/-!
# Terminal-linear Bell output Jacobian

This module combines the two algebraic reductions used in the terminal-linear observability
induction.  A polynomial lower-jet family is first transformed by the universal Bell coordinates;
adjoining a terminal variable and multiplying every positive output jet by that variable produces
the full terminal-linear output family.  Its Jacobian determinant is the lower-jet determinant
times the exact terminal power and sign.
-/

noncomputable section

open MvPolynomial

namespace GaloisForLFunctions

/-- Embed the Bell-transformed lower-state Jacobian into a frame with one terminal variable. -/
def embeddedBellOutputJacobian (n : ℕ)
    (u : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 2)) ℂ) :=
  (polynomialOutputJacobian (bellSubstitutionFamily n u)).map (rename Fin.castSucc)

/-- The terminal-linear output and its first `n+1` Bell jets, all in the extended polynomial
frame. -/
def terminalLinearBellOutput (n : ℕ)
    (u : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ) :
    Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ :=
  Fin.cases (X (Fin.last (n + 1))) fun i =>
    X (Fin.last (n + 1)) * rename Fin.castSucc (bellSubstitutionFamily n u i)

/-- The actual polynomial output Jacobian has the terminal-linear bordered form. -/
theorem polynomialOutputJacobian_terminalLinearBellOutput (n : ℕ)
    (u : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ) :
    polynomialOutputJacobian (terminalLinearBellOutput n u) =
      terminalLinearJacobianMatrix
        (X (Fin.last (n + 1)))
        (fun i => rename Fin.castSucc (bellSubstitutionFamily n u i))
        (embeddedBellOutputJacobian n u) := by
  funext i j
  refine Fin.cases ?_ (fun r => ?_) i
  · refine Fin.lastCases ?_ (fun c => ?_) j
    · simp [polynomialOutputJacobian, terminalLinearBellOutput,
        terminalLinearJacobianMatrix]
    · simp [polynomialOutputJacobian, terminalLinearBellOutput,
        terminalLinearJacobianMatrix]
  · refine Fin.lastCases ?_ (fun c => ?_) j
    · simp [polynomialOutputJacobian, terminalLinearBellOutput,
        terminalLinearJacobianMatrix, pderiv_notMem_rename_castSucc]
    · simp [polynomialOutputJacobian, terminalLinearBellOutput,
        terminalLinearJacobianMatrix, embeddedBellOutputJacobian,
        MvPolynomial.pderiv_rename (Fin.castSucc_injective (n + 1))]

/-- The embedded Bell-output determinant is the renamed lower-jet determinant. -/
theorem embeddedBellOutputJacobian_det (n : ℕ)
    (u : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ) :
    (embeddedBellOutputJacobian n u).det =
      rename Fin.castSucc (polynomialOutputJacobian u).det := by
  have hmap := (rename (R := ℂ) Fin.castSucc).map_det
    (polynomialOutputJacobian (bellSubstitutionFamily n u))
  rw [polynomialOutputJacobian_bellSubstitutionFamily_det] at hmap
  simpa [embeddedBellOutputJacobian] using hmap.symm

/-- **Terminal-linear Bell row reduction.**  For `n+1` lower coordinates, the complete output-jet
Jacobian is the lower-jet Jacobian times `X_terminal^(n+1)` and the exact cofactor sign. -/
theorem polynomialOutputJacobian_terminalLinearBellOutput_det (n : ℕ)
    (u : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ) :
    (polynomialOutputJacobian (terminalLinearBellOutput n u)).det =
      (-1 : MvPolynomial (Fin (n + 2)) ℂ) ^ (n + 1) *
        X (Fin.last (n + 1)) ^ (n + 1) *
          rename Fin.castSucc (polynomialOutputJacobian u).det := by
  rw [polynomialOutputJacobian_terminalLinearBellOutput,
    terminalLinearJacobianMatrix_det, embeddedBellOutputJacobian_det]

/-- The full terminal-linear Bell output Jacobian is nonzero whenever the lower-jet Jacobian is
nonzero. -/
theorem polynomialOutputJacobian_terminalLinearBellOutput_det_ne_zero (n : ℕ)
    (u : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ)
    (hu : (polynomialOutputJacobian u).det ≠ 0) :
    (polynomialOutputJacobian (terminalLinearBellOutput n u)).det ≠ 0 := by
  rw [polynomialOutputJacobian_terminalLinearBellOutput_det]
  have hrename : rename Fin.castSucc (polynomialOutputJacobian u).det ≠ 0 := by
    intro hzero
    apply hu
    apply MvPolynomial.rename_injective Fin.castSucc (Fin.castSucc_injective (n + 1))
    simpa using hzero
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (X_ne_zero (Fin.last (n + 1)))))
    hrename

end GaloisForLFunctions

end

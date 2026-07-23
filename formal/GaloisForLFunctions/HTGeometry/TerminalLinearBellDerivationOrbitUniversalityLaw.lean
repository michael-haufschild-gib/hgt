import GaloisForLFunctions.HTGeometry.DerivationTerminalLinearJacobian
import GaloisForLFunctions.HTGeometry.TerminalLinearBellJacobian

/-!
# Terminal-linear Bell polynomial/derivation-orbit universality

The universal terminal-linear Bell polynomial chart is not merely analogous to an actual
derivation orbit.  Evaluating its lower coordinates at the finite logarithmic-derivative jet and
its terminal coordinate at the state gives the actual finite orbit exactly.  Its universal
Jacobian monomial specializes to the lower-jet determinant formula and hence to algebraic
independence.
-/

noncomputable section

open MvPolynomial

namespace GaloisForLFunctions

/-- Evaluation coordinates that place the lower logarithmic-derivative jet before the terminal
state coordinate. -/
def derivationTerminalLinearBellCoordinates
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ) (x A : R) :
    Fin (n + 2) → R :=
  Fin.lastCases x fun i => ((δ : R → R)^[(i : ℕ)]) A

/-- The generic terminal-linear Bell output evaluates to the actual derivation orbit. -/
theorem aeval_terminalLinearBellOutput_identity_eq_derivationIterate
    {R : Type*} [CommRing R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ) (x A : R)
    (hδx : δ x = A * x) (i : Fin (n + 2)) :
    aeval (derivationTerminalLinearBellCoordinates δ n x A)
        (terminalLinearBellOutput n (fun j => X j) i) =
      ((δ : R → R)^[(i : ℕ)]) x := by
  refine Fin.cases ?_ (fun r => ?_) i
  · simp [terminalLinearBellOutput, derivationTerminalLinearBellCoordinates]
  · rw [show (r.succ : ℕ) = (r : ℕ) + 1 by simp,
      derivation_iterate_terminalLinear_eq_derivationBellValue δ x A hδx n r]
    simp [terminalLinearBellOutput, derivationTerminalLinearBellCoordinates,
      bellSubstitutionFamily, derivationBellValue, MvPolynomial.aeval_rename,
      Function.comp_def]

/-- The identity lower-coordinate family makes the generic terminal-linear Bell chart have a
pure monomial Jacobian determinant. -/
theorem polynomialOutputJacobian_terminalLinearBellOutput_identity_det (n : ℕ) :
    (polynomialOutputJacobian
        (terminalLinearBellOutput n (fun j => X j))).det =
      (-1 : MvPolynomial (Fin (n + 2)) ℂ) ^ (n + 1) *
        X (Fin.last (n + 1)) ^ (n + 1) := by
  have hid :
      polynomialOutputJacobian (fun j : Fin (n + 1) => X j) = 1 := by
    funext i j
    simp [polynomialOutputJacobian, Matrix.one_apply, Pi.single_apply]
  rw [polynomialOutputJacobian_terminalLinearBellOutput_det, hid, Matrix.det_one]
  simp

/-- **Terminal-linear Bell polynomial/derivation-orbit universality law.**  The actual first
`n+2` derivation iterates are the exact evaluation of one universal polynomial chart.  The chart
has the pure terminal-coordinate Jacobian monomial, while every compatible actual coordinate
frame has the corresponding lower-jet determinant.  Nonvanishing therefore makes the actual
orbit algebraically independent. -/
theorem terminalLinearBell_derivationOrbitUniversality
    {R : Type*} [Field R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (n : ℕ)
    (partials : Fin (n + 2) → Derivation ℂ R R) (x A : R)
    (hδx : δ x = A * x)
    (hlowerx : ∀ j : Fin (n + 1), partials j.castSucc x = 0)
    (hterminalx : partials (Fin.last (n + 1)) x = 1)
    (hterminalA : ∀ i : Fin (n + 1),
      partials (Fin.last (n + 1)) (((δ : R → R)^[(i : ℕ)]) A) = 0)
    (hx : x ≠ 0)
    (hlower : (derivationLowerJetJacobian δ n partials A).det ≠ 0) :
    (∀ i : Fin (n + 2),
        aeval (derivationTerminalLinearBellCoordinates δ n x A)
            (terminalLinearBellOutput n (fun j => X j) i) =
          ((δ : R → R)^[(i : ℕ)]) x) ∧
      (polynomialOutputJacobian
          (terminalLinearBellOutput n (fun j => X j))).det =
        (-1 : MvPolynomial (Fin (n + 2)) ℂ) ^ (n + 1) *
          X (Fin.last (n + 1)) ^ (n + 1) ∧
      (derivationIterateOutputJacobian δ n partials x).det =
        (-1 : R) ^ (n + 1) * x ^ (n + 1) *
          (derivationLowerJetJacobian δ n partials A).det ∧
      AlgebraicIndependent ℂ
        (fun i : Fin (n + 2) ↦ ((δ : R → R)^[(i : ℕ)]) x) := by
  exact ⟨
    aeval_terminalLinearBellOutput_identity_eq_derivationIterate δ n x A hδx,
    polynomialOutputJacobian_terminalLinearBellOutput_identity_det n,
    derivationIterateOutputJacobian_det δ n partials x A
      hδx hlowerx hterminalx hterminalA,
    algebraicIndependent_derivationIterates_terminalLinear δ n partials x A
      hδx hlowerx hterminalx hterminalA hx hlower⟩

end GaloisForLFunctions

end

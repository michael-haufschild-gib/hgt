import GaloisForLFunctions.HTGeometry.AutonomousSeparant
import GaloisForLFunctions.HTGeometry.DigammaHypertranscendental

/-!
# Realizations of the autonomous-annihilator interfaces

The zero polynomial annihilates every source, and the exponential clock is annihilated by the
autonomous relation `y' - y`, which is nonzero.  The minimal-degree selection theorem therefore
applies to the exponential with no interface premise.
-/

namespace GaloisForLFunctions

theorem autonomousAnnihilator_zero (f : ℂ → ℂ) (n : ℕ) :
    AutonomousAnnihilator f n 0 := by
  intro z
  simp

theorem annihilatesDigamma_zero (m : ℕ) : AnnihilatesDigamma m 0 := by
  intro z _
  simp

/-- The first-order autonomous relation `y' - y` of the exponential clock. -/
noncomputable def expAutonomousRelation :
    Polynomial (MvPolynomial (Fin 1) ℂ) :=
  Polynomial.X - Polynomial.C (MvPolynomial.X 0)

theorem expAutonomousRelation_ne_zero : expAutonomousRelation ≠ 0 := by
  rw [expAutonomousRelation]
  exact Polynomial.X_sub_C_ne_zero _

/-- **The exponential clock has a nonzero autonomous annihilator.** -/
theorem autonomousAnnihilator_exp :
    AutonomousAnnihilator Complex.exp 1 expAutonomousRelation := by
  intro z
  rw [expAutonomousRelation]
  simp [iteratedDeriv_succ, iteratedDeriv_zero, Complex.deriv_exp]

/-- Minimal-degree autonomous annihilator of the exponential clock, with no interface premise. -/
theorem exists_minimal_autonomousAnnihilator_exp :
    ∃ P : Polynomial (MvPolynomial (Fin 1) ℂ), P ≠ 0 ∧
      AutonomousAnnihilator Complex.exp 1 P ∧
      ∀ Q : Polynomial (MvPolynomial (Fin 1) ℂ), Q ≠ 0 →
        AutonomousAnnihilator Complex.exp 1 Q → P.natDegree ≤ Q.natDegree :=
  exists_minimal_autonomousAnnihilator
    ⟨expAutonomousRelation, expAutonomousRelation_ne_zero, autonomousAnnihilator_exp⟩

end GaloisForLFunctions

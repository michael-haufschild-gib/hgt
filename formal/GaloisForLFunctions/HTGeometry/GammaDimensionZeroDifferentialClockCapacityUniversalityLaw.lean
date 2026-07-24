import GaloisForLFunctions.HTGeometry.GammaInversePoleClockObservability
import GaloisForLFunctions.HTGeometry.GammaUniversalClockHorizon

/-!
# Gamma dimension-zero differential-clock capacity universality

The formal nonlinear inverse-Gamma clock and the finite-depth decorations of the actual
irreversible Gamma horizon use one coefficient source.  Sequence representatives used on the
horizon recover the same eventual germs that generate the formal power series.  Thus formal
differential non-saturation and all-finite-depth polynomial detection coexist on a
Hausdorff-dimension-zero, aperiodic horizon.
-/

open MvPolynomial

namespace GaloisForLFunctions

noncomputable section

local instance gammaDimensionZeroClockNatGermAlgebra : Algebra ℂ NatGerm :=
  complexNatGerm.toAlgebra

/-- One inverse-Gamma coefficient source carries both formal differential capacity and
finite-depth algebraic capacity on the actual dimension-zero irreversible horizon. -/
structure GammaDimensionZeroDifferentialClockCapacityCertificate : Prop where
  coefficientSource :
    ∀ j : ℕ,
      (gammaInversePoleBranchCoefficientSequence j : NatGerm) =
        gammaInversePoleBranchCoefficientGerm j
  formalDifferentialCapacity :
    ∀ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ), P ≠ 0 →
      MvPolynomial.aeval
        (formalJetsOver n gammaInversePoleClockObservableFormalGerm) P ≠ 0
  horizonAlgebraicCapacity :
    ∀ (m d : ℕ) (P : MvPolynomial (GammaHorizonJetVariables m d) ℂ), P ≠ 0 →
      dimH gammaConstrainedHorizon = 0 ∧
        (∃ w : GammaHorizonPoleWords d,
          MvPolynomial.eval (fun q => gammaHorizonJetEvaluation m d q w) P ≠ 0 ∧
            gammaBaireCode gammaThinSchedule (gammaHorizonPoleWordExtension d w) ∈
              gammaConstrainedHorizon) ∧
        (∀ z ∈ gammaConstrainedHorizon, ∀ r, 0 < r →
          (Complex.Gamma^[r]) z ≠ z) ∧
        (⋂ r : ℕ, (Complex.Gamma^[r]) '' gammaConstrainedHorizon) = ∅

/-- **Gamma dimension-zero differential-clock capacity universality law.**  The coefficient
germs of the normalized inverse-Gamma branch simultaneously generate a formally
hypertranscendental clock and furnish every finite-depth polynomial detector on the actual
dimension-zero irreversible Gamma horizon. -/
theorem gamma_dimensionZero_differentialClockCapacityUniversality :
    GammaDimensionZeroDifferentialClockCapacityCertificate := by
  refine ⟨gammaInversePoleBranchCoefficientSequence_germ, ?_, ?_⟩
  · intro n P hP
    exact
      gammaInversePoleClockObservableFormalGerm_formallyHypertranscendental hP
  · intro m d P hP
    exact
      gamma_dimensionZero_algebraicallyUniversal_irreversibleClockHorizon m d P hP

end

end GaloisForLFunctions

import GaloisForLFunctions.HTGeometry.GammaInversePoleBranchCoefficientFreeness
import GaloisForLFunctions.HTGeometry.AlgebraicallyIndependentCoefficientFormalGerm

/-!
# The nonlinear inverse-Gamma clock observation germ

The normalized pole branch

`B_n(T) = T + b_{n,0} T^(2 : ℕ) + b_{n,1} T^(3 : ℕ) + ...`

has a fixed origin and unit tangent.  Removing those two gauge coordinates leaves the nonlinear
observation germ

`C_n(T) = (B_n(T) - T) / T^(2 : ℕ) = b_{n,0} + b_{n,1} T + ...`.

Its coefficients, viewed as eventual germs in the pole label, are already known to be countably
algebraically independent.  This file records the exact formal consequence: the clock observation
germ satisfies no finite algebraic differential relation.  The derivative order is observation
resolution, not a temporal parameter.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions

noncomputable section

local instance gammaInverseClockNatGermAlgebra : Algebra ℂ NatGerm :=
  complexNatGerm.toAlgebra

/-- The nonlinear observation germ of the normalized inverse-Gamma clock. -/
def gammaInversePoleClockObservableFormalGerm : NatGerm⟦X⟧ :=
  PowerSeries.mk gammaInversePoleBranchCoefficientGerm

/-- **Formal hypertranscendence of the inverse-Gamma clock observation.**  No nonzero finite-order
algebraic differential observable vanishes on the nonlinear branch-deformation germ. -/
theorem gammaInversePoleClockObservableFormalGerm_formallyHypertranscendental
    {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0) :
    MvPolynomial.aeval
      (formalJetsOver n gammaInversePoleClockObservableFormalGerm) P ≠ 0 := by
  exact aeval_formalJetsOver_ne_zero_of_coeff_algebraicIndependent
    gammaInversePoleBranchCoefficientGerm
    algebraicIndependent_gammaInversePoleBranchCoefficientGerm hP

end

end GaloisForLFunctions

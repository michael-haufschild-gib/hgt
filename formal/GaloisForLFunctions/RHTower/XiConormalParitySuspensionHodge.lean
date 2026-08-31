import GaloisForLFunctions.HTGeometry.ConstitutiveParitySuspensionHodge
import GaloisForLFunctions.RHTower.XiEntireOnShellWronskianInternalization

/-!
# Actual Xi conormal parity suspension

The literal Xi conormal current is suspended to a faithful square-zero BRST charge. Its odd output
retains the exact top multiplicity jet at every Xi divisor point. The functional-equation Real
action, which anticommutes with the unsuspended current, becomes a commuting involutive chain
symmetry after the parity sign is included.

This is algebraic comparison cohomology. A bounded conservative realization in an independently
formed prime--Gamma source Hilbert complex remains the RH-bearing obligation.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Parity double of actual Xi entire comparison cohomology. -/
abbrev XiConormalParityDouble := DeningerEntireH1 × DeningerEntireH1

/-- Unconditional square-zero BRST charge carrying the actual Xi conormal current. -/
def xiConormalParityCharge :
    Module.End DeningerEntireH1 XiConormalParityDouble :=
  paritySuspensionCharge (R := DeningerEntireH1) xiEntireConormalCurrent

@[simp]
theorem xiConormalParityCharge_apply (p : XiConormalParityDouble) :
    xiConormalParityCharge p = (0, xiEntireConormalCurrent p.1) :=
  rfl

/-- The actual Xi parity charge is a genuine differential. -/
theorem xiConormalParityCharge_sq :
    xiConormalParityCharge * xiConormalParityCharge = 0 :=
  paritySuspensionCharge_sq (R := DeningerEntireH1) xiEntireConormalCurrent

/-- Parity suspension does not erase the nonzero actual Xi conormal current. -/
theorem xiConormalParityCharge_ne_zero :
    xiConormalParityCharge ≠ 0 := by
  change paritySuspensionCharge (R := DeningerEntireH1) xiEntireConormalCurrent ≠ 0
  intro hzero
  apply xiEntireConormalCurrent_ne_zero
  exact (paritySuspensionCharge_eq_zero_iff
    (R := DeningerEntireH1) xiEntireConormalCurrent).mp hzero

/-- Every Xi zero detects the odd charge by its exact top conormal jet. -/
theorem xiConormalParityCharge_top_jet (rho : XiDivisorSupport) :
    deningerArithmeticJetCompact rho (xiEntireConormalTopJetIndex rho)
        (xiConormalParityCharge (1, 0)).2 =
      -iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho) :=
  xiEntireConormalCurrent_top_jet rho

/-- The multiplicity-adapted odd charge output is nonzero at every Xi divisor point. -/
theorem xiConormalParityCharge_top_jet_ne_zero (rho : XiDivisorSupport) :
    deningerArithmeticJetCompact rho (xiEntireConormalTopJetIndex rho)
        (xiConormalParityCharge (1, 0)).2 ≠ 0 := by
  rw [xiConormalParityCharge_top_jet]
  exact neg_ne_zero.mpr (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)

/-- Parity-corrected lift of the actual functional-equation Real action. -/
def xiConormalFunctionalEquationEvenLift
    (p : XiConormalParityDouble) : XiConormalParityDouble :=
  paritySuspensionEvenLift deningerArithmeticH1EvenKReal.sigma p

/-- Unsigned diagonal lift of the actual functional-equation Real action. -/
def xiConormalFunctionalEquationDiagonalLift
    (p : XiConormalParityDouble) : XiConormalParityDouble :=
  paritySuspensionDiagonalLift deningerArithmeticH1EvenKReal.sigma p

/-- The parity-corrected functional-equation lift is information-neutral and involutive. -/
theorem xiConormalFunctionalEquationEvenLift_sq (p : XiConormalParityDouble) :
    xiConormalFunctionalEquationEvenLift
        (xiConormalFunctionalEquationEvenLift p) = p := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · simpa [xiConormalFunctionalEquationEvenLift, paritySuspensionEvenLift,
      GaloisForLFunctions.RHTower.kRealParityAction] using
      deningerArithmeticH1EvenKReal.sq x
  · change -deningerArithmeticH1EvenKReal.sigma
      (-deningerArithmeticH1EvenKReal.sigma y) = y
    rw [map_neg, neg_neg]
    simpa [GaloisForLFunctions.RHTower.kRealParityAction] using
      deningerArithmeticH1EvenKReal.sq y

/-- Functional-equation oddness becomes a commuting symmetry of the suspended Xi complex. -/
theorem xiConormalParityCharge_functionalEquationEven_commutes
    (p : XiConormalParityDouble) :
    xiConormalParityCharge (xiConormalFunctionalEquationEvenLift p) =
      xiConormalFunctionalEquationEvenLift (xiConormalParityCharge p) := by
  exact paritySuspensionCharge_evenLift
    (R := DeningerEntireH1) (J := xiEntireConormalCurrent)
    (tau := deningerArithmeticH1EvenKReal.sigma)
    xiEntireConormalCurrent_functionalEquation_odd
    deningerArithmeticH1EvenKReal.sigma.map_zero p

/-- The unsigned lift records the same source action as an odd anticommuting symmetry. -/
theorem xiConormalParityCharge_functionalEquationDiagonal_odd
    (p : XiConormalParityDouble) :
    xiConormalParityCharge (xiConormalFunctionalEquationDiagonalLift p) =
      -xiConormalFunctionalEquationDiagonalLift (xiConormalParityCharge p) := by
  exact paritySuspensionCharge_diagonalLift
    (R := DeningerEntireH1) (J := xiEntireConormalCurrent)
    (tau := deningerArithmeticH1EvenKReal.sigma)
    xiEntireConormalCurrent_functionalEquation_odd
    deningerArithmeticH1EvenKReal.sigma.map_zero p

end

end RHTower

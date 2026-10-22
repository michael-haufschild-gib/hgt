import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapCofactorModel
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapLowCoefficients
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapSourceZeroSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReflectedTwoSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReflectedFourSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReflectedSixSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReflectedEightSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReflectedTenSlices
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapReflectedTwelveSlices

/-! # Proof-assisted normal forms for bounded cofactor coefficients -/
namespace HTGeometry
open Lean Meta Elab Term Tactic
set_option maxRecDepth 10000

meta section
elab "compactGapCofactorSlice% " e:term : term => do
  let e ← elabTermAndSynthesize e (some (mkConst ``Real))
  let (rhs, g) ← Conv.mkConvGoalFor e
  let goals ← Tactic.run g.mvarId! do
    evalTactic (← `(conv| norm_num [evenCompactGapHeadPolynomial,
      evenCompactGapCofactorTerm1,
      evenCompactGapCofactorTerm2,
      evenCompactGapCofactorTerm3,
      evenCompactGapCofactorTerm4,
      evenCompactGapCofactorTerm5,
      evenCompactGapCofactorTerm6,
      pow_succ,
      Polynomial.coeff_add,
      Polynomial.coeff_sub,
      Polynomial.coeff_neg,
      Polynomial.coeff_mul_C,
      Polynomial.coeff_C_mul,
      Polynomial.coeff_C,
      Polynomial.mul_coeff_zero,
      Polynomial.mul_coeff_one,
      evenCompactGapCoeff_mul_2]))
    evalTactic (← `(conv| norm_num [evenCompactGapSourceZeroPolynomial_coeff_slice0,
      evenCompactGapSourceZeroPolynomial_coeff_slice1,
      evenCompactGapSourceZeroPolynomial_coeff_above,
      evenCompactGapReflectedTwoPolynomial_coeff_slice0,
      evenCompactGapReflectedTwoPolynomial_coeff_slice1,
      evenCompactGapReflectedTwoPolynomial_coeff_slice2,
      evenCompactGapReflectedTwoPolynomial_coeff_slice3,
      evenCompactGapReflectedTwoPolynomial_coeff_above,
      evenCompactGapReflectedFourPolynomial_coeff_slice0,
      evenCompactGapReflectedFourPolynomial_coeff_slice1,
      evenCompactGapReflectedFourPolynomial_coeff_slice2,
      evenCompactGapReflectedFourPolynomial_coeff_slice3,
      evenCompactGapReflectedFourPolynomial_coeff_slice4,
      evenCompactGapReflectedFourPolynomial_coeff_above,
      evenCompactGapReflectedSixPolynomial_coeff_slice0,
      evenCompactGapReflectedSixPolynomial_coeff_slice1,
      evenCompactGapReflectedSixPolynomial_coeff_slice2,
      evenCompactGapReflectedSixPolynomial_coeff_slice3,
      evenCompactGapReflectedSixPolynomial_coeff_slice4,
      evenCompactGapReflectedSixPolynomial_coeff_slice5,
      evenCompactGapReflectedSixPolynomial_coeff_above,
      evenCompactGapReflectedEightPolynomial_coeff_slice0,
      evenCompactGapReflectedEightPolynomial_coeff_slice1,
      evenCompactGapReflectedEightPolynomial_coeff_slice2,
      evenCompactGapReflectedEightPolynomial_coeff_slice3,
      evenCompactGapReflectedEightPolynomial_coeff_slice4,
      evenCompactGapReflectedEightPolynomial_coeff_slice5,
      evenCompactGapReflectedEightPolynomial_coeff_slice6,
      evenCompactGapReflectedEightPolynomial_coeff_above,
      evenCompactGapReflectedTenPolynomial_coeff_slice0,
      evenCompactGapReflectedTenPolynomial_coeff_slice1,
      evenCompactGapReflectedTenPolynomial_coeff_slice2,
      evenCompactGapReflectedTenPolynomial_coeff_slice3,
      evenCompactGapReflectedTenPolynomial_coeff_slice4,
      evenCompactGapReflectedTenPolynomial_coeff_slice5,
      evenCompactGapReflectedTenPolynomial_coeff_slice6,
      evenCompactGapReflectedTenPolynomial_coeff_slice7,
      evenCompactGapReflectedTenPolynomial_coeff_above,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice0,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice1,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice2,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice3,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice4,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice5,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice6,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice7,
      evenCompactGapReflectedTwelvePolynomial_coeff_slice8,
      evenCompactGapReflectedTwelvePolynomial_coeff_above]))
    evalTactic (← `(conv| dsimp only [evenCompactGapSourceZeroSlice0,
      evenCompactGapSourceZeroSlice1,
      evenCompactGapReflectedTwoSlice0,
      evenCompactGapReflectedTwoSlice1,
      evenCompactGapReflectedTwoSlice2,
      evenCompactGapReflectedTwoSlice3,
      evenCompactGapReflectedFourSlice0,
      evenCompactGapReflectedFourSlice1,
      evenCompactGapReflectedFourSlice2,
      evenCompactGapReflectedFourSlice3,
      evenCompactGapReflectedFourSlice4,
      evenCompactGapReflectedSixSlice0,
      evenCompactGapReflectedSixSlice1,
      evenCompactGapReflectedSixSlice2,
      evenCompactGapReflectedSixSlice3,
      evenCompactGapReflectedSixSlice4,
      evenCompactGapReflectedSixSlice5,
      evenCompactGapReflectedEightSlice0,
      evenCompactGapReflectedEightSlice1,
      evenCompactGapReflectedEightSlice2,
      evenCompactGapReflectedEightSlice3,
      evenCompactGapReflectedEightSlice4,
      evenCompactGapReflectedEightSlice5,
      evenCompactGapReflectedEightSlice6,
      evenCompactGapReflectedTenSlice0,
      evenCompactGapReflectedTenSlice1,
      evenCompactGapReflectedTenSlice2,
      evenCompactGapReflectedTenSlice3,
      evenCompactGapReflectedTenSlice4,
      evenCompactGapReflectedTenSlice5,
      evenCompactGapReflectedTenSlice6,
      evenCompactGapReflectedTenSlice7,
      evenCompactGapReflectedTwelveSlice0,
      evenCompactGapReflectedTwelveSlice1,
      evenCompactGapReflectedTwelveSlice2,
      evenCompactGapReflectedTwelveSlice3,
      evenCompactGapReflectedTwelveSlice4,
      evenCompactGapReflectedTwelveSlice5,
      evenCompactGapReflectedTwelveSlice6,
      evenCompactGapReflectedTwelveSlice7,
      evenCompactGapReflectedTwelveSlice8]))
    evalTactic (← `(conv| ring_nf))
    for goal in (← getGoals) do
      goal.refl
    pruneSolvedGoals
  unless goals.isEmpty do
    throwError "cofactor normalization left open goals"
  instantiateMVars rhs
end

end HTGeometry

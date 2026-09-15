import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapHigherCoefficients
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCofactorModel
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapLowCoefficients
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapSourceZeroSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedTwoSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedFourSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedSixSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedEightSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedTenSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapReflectedTwelveSlices
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapCertifiedNormalizer

/-! # Proof-assisted normal forms for cofactor coefficients through index ten -/
namespace HTGeometry
open Lean Meta Elab Term Tactic
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

meta section
private meta def compactGapCofactorHigherNormalize (e : Expr) : TermElabM (Expr × Expr) := do
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
      evenCompactGapCoeff_mul_2,
      evenCompactGapCoeff_mul_3,
      evenCompactGapCoeff_mul_4,
      evenCompactGapCoeff_mul_5,
      evenCompactGapCoeff_mul_6,
      evenCompactGapCoeff_mul_7,
      evenCompactGapCoeff_mul_8,
      evenCompactGapCoeff_mul_9,
      evenCompactGapCoeff_mul_10]))
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
  let rhs ← instantiateMVars rhs
  let proof ← instantiateMVars g
  return (rhs, proof)

elab "compactGapCofactorHigherSlice% " e:term : term => do
  let e ← elabTermAndSynthesize e (some (mkConst ``Real))
  let (rhs, _) ← compactGapCofactorHigherNormalize e
  return rhs

/-- Normalize a higher cofactor coefficient once and retain its exact equality proof. -/
elab "compactGapCofactorHigherCertified% " e:term : term => do
  let e ← elabTermAndSynthesize e (some (mkConst ``Real))
  let (rhs, proof) ← compactGapCofactorHigherNormalize e
  return mkApp3 (mkConst ``CompactGapNormalForm.mk) e rhs proof
end

end HTGeometry

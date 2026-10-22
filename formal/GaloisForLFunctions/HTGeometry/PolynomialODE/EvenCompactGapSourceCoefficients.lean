import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapLift

/-! # Reusable exact source coefficients in the gap variable

Coefficient expressions retain the original summands and explicit index tests.
The elaborator performs no coefficient arithmetic; the following theorems verify
these expressions independently from polynomial coefficient laws.
-/
namespace HTGeometry
open Lean Meta Elab Term Qq
set_option maxRecDepth 10000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

meta section
partial def compactGapCoefficientExpression (n : Q(ℕ))
    (p : Q(Polynomial ℝ)) : MetaM Q(ℝ) := do
  match p with
  | ~q(Polynomial.C $c) => return q(if $n = 0 then $c else 0)
  | ~q((Polynomial.X : Polynomial ℝ)) => return q(if 1 = $n then 1 else 0)
  | ~q((Polynomial.X : Polynomial ℝ)^($k : ℕ)) => return q(if $n = $k then 1 else 0)
  | ~q($a + $b) =>
    let ca ← compactGapCoefficientExpression n a
    let cb ← compactGapCoefficientExpression n b
    return q($ca + $cb)
  | ~q($a - $b) =>
    let ca ← compactGapCoefficientExpression n a
    let cb ← compactGapCoefficientExpression n b
    return q($ca - $cb)
  | ~q(-$a) =>
    let ca ← compactGapCoefficientExpression n a
    return q(-$ca)
  | ~q((Polynomial.C $c) * $a) =>
    let ca ← compactGapCoefficientExpression n a
    return q($c * $ca)
  | ~q($a * (Polynomial.C $c)) =>
    let ca ← compactGapCoefficientExpression n a
    return q($ca * $c)
  | _ => throwError "source expression is not a sum of gap monomials: {p}"

elab "compactGapCoefficient% " "(" n:term ")" p:term : term => do
  let n ← elabTerm n (some q(ℕ))
  let p ← elabTerm p (some q(Polynomial ℝ))
  let names := [``evenCompactGapSourceZeroPolynomial,
    ``evenCompactGapReflectedTwoPolynomial, ``evenCompactGapReflectedFourPolynomial,
    ``evenCompactGapReflectedSixPolynomial, ``evenCompactGapReflectedEightPolynomial,
    ``evenCompactGapReflectedTenPolynomial, ``evenCompactGapReflectedTwelvePolynomial]
  let p ← deltaExpand p names.contains
  compactGapCoefficientExpression n p
end

noncomputable section

/-- Exact source coefficient expression with every original summand retained. -/
def evenCompactGapSourceZeroCoeff (n : ℕ) (u : ℝ) : ℝ :=
  compactGapCoefficient% (n) (evenCompactGapSourceZeroPolynomial u)

/-- Polynomial coefficient extraction agrees with the copied source expression. -/
theorem evenCompactGapSourceZeroPolynomial_coeff (n : ℕ) (u : ℝ) :
    (evenCompactGapSourceZeroPolynomial u).coeff n = evenCompactGapSourceZeroCoeff n u := by
  dsimp only [evenCompactGapSourceZeroPolynomial, evenCompactGapSourceZeroCoeff]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_mul_C, Polynomial.coeff_sub, Polynomial.coeff_X]

/-- Exact source coefficient expression with every original summand retained. -/
def evenCompactGapReflectedTwoCoeff (n : ℕ) (u w : ℝ) : ℝ :=
  compactGapCoefficient% (n) (evenCompactGapReflectedTwoPolynomial u w)

/-- Polynomial coefficient extraction agrees with the copied source expression. -/
theorem evenCompactGapReflectedTwoPolynomial_coeff (n : ℕ) (u w : ℝ) :
    (evenCompactGapReflectedTwoPolynomial u w).coeff n = evenCompactGapReflectedTwoCoeff n u w := by
  dsimp only [evenCompactGapReflectedTwoPolynomial, evenCompactGapReflectedTwoCoeff]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow]

/-- Exact source coefficient expression with every original summand retained. -/
def evenCompactGapReflectedFourCoeff (n : ℕ) (u w : ℝ) : ℝ :=
  compactGapCoefficient% (n) (evenCompactGapReflectedFourPolynomial u w)

/-- Polynomial coefficient extraction agrees with the copied source expression. -/
theorem evenCompactGapReflectedFourPolynomial_coeff (n : ℕ) (u w : ℝ) :
    (evenCompactGapReflectedFourPolynomial u w).coeff n = evenCompactGapReflectedFourCoeff n u w := by
  dsimp only [evenCompactGapReflectedFourPolynomial, evenCompactGapReflectedFourCoeff]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow]

/-- Exact source coefficient expression with every original summand retained. -/
def evenCompactGapReflectedSixCoeff (n : ℕ) (u w : ℝ) : ℝ :=
  compactGapCoefficient% (n) (evenCompactGapReflectedSixPolynomial u w)

/-- Polynomial coefficient extraction agrees with the copied source expression. -/
theorem evenCompactGapReflectedSixPolynomial_coeff (n : ℕ) (u w : ℝ) :
    (evenCompactGapReflectedSixPolynomial u w).coeff n = evenCompactGapReflectedSixCoeff n u w := by
  dsimp only [evenCompactGapReflectedSixPolynomial, evenCompactGapReflectedSixCoeff]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow]

/-- Exact source coefficient expression with every original summand retained. -/
def evenCompactGapReflectedEightCoeff (n : ℕ) (u w : ℝ) : ℝ :=
  compactGapCoefficient% (n) (evenCompactGapReflectedEightPolynomial u w)

/-- Polynomial coefficient extraction agrees with the copied source expression. -/
theorem evenCompactGapReflectedEightPolynomial_coeff (n : ℕ) (u w : ℝ) :
    (evenCompactGapReflectedEightPolynomial u w).coeff n = evenCompactGapReflectedEightCoeff n u w := by
  dsimp only [evenCompactGapReflectedEightPolynomial, evenCompactGapReflectedEightCoeff]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow]

/-- Exact source coefficient expression with every original summand retained. -/
def evenCompactGapReflectedTenCoeff (n : ℕ) (u w : ℝ) : ℝ :=
  compactGapCoefficient% (n) (evenCompactGapReflectedTenPolynomial u w)

/-- Polynomial coefficient extraction agrees with the copied source expression. -/
theorem evenCompactGapReflectedTenPolynomial_coeff (n : ℕ) (u w : ℝ) :
    (evenCompactGapReflectedTenPolynomial u w).coeff n = evenCompactGapReflectedTenCoeff n u w := by
  dsimp only [evenCompactGapReflectedTenPolynomial, evenCompactGapReflectedTenCoeff]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow]

/-- Exact source coefficient expression with every original summand retained. -/
def evenCompactGapReflectedTwelveCoeff (n : ℕ) (u w : ℝ) : ℝ :=
  compactGapCoefficient% (n) (evenCompactGapReflectedTwelvePolynomial u w)

/-- Polynomial coefficient extraction agrees with the copied source expression. -/
theorem evenCompactGapReflectedTwelvePolynomial_coeff (n : ℕ) (u w : ℝ) :
    (evenCompactGapReflectedTwelvePolynomial u w).coeff n = evenCompactGapReflectedTwelveCoeff n u w := by
  dsimp only [evenCompactGapReflectedTwelvePolynomial, evenCompactGapReflectedTwelveCoeff]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_X_pow]

end
end HTGeometry

import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactRawModel

/-! # Exact polynomial lift in the modular gap coordinate

The elaborator only copies the existing algebraic expressions into `Polynomial ℝ`.
Independent evaluation theorems below identify their semantics with the original source.
No coefficient or sign computation is admitted as a premise.
-/
namespace HTGeometry
open Lean Meta Elab Term Qq
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

meta section
partial def liftCompactGapExpression (gap : FVarId) (e : Q(ℝ)) : MetaM Q(Polynomial ℝ) := do
  if e.isFVar && e.fvarId! == gap then
    return q(Polynomial.X)
  if !e.containsFVar gap then
    return q(Polynomial.C $e)
  match e with
  | ~q($x + $y) =>
    let px ← liftCompactGapExpression gap x
    let py ← liftCompactGapExpression gap y
    return q($px + $py)
  | ~q($x - $y) =>
    let px ← liftCompactGapExpression gap x
    let py ← liftCompactGapExpression gap y
    return q($px - $py)
  | ~q($x * $y) =>
    let px ← liftCompactGapExpression gap x
    let py ← liftCompactGapExpression gap y
    return q($px * $py)
  | ~q(-$x) =>
    let px ← liftCompactGapExpression gap x
    return q(-$px)
  | ~q($x / $y) =>
    if y.containsFVar gap then throwError "gap occurs in denominator"
    let px ← liftCompactGapExpression gap x
    return q($px * Polynomial.C ($y⁻¹))
  | ~q($x ^ ($n : ℕ)) =>
    if n.containsFVar gap then throwError "gap occurs in exponent"
    let px ← liftCompactGapExpression gap x
    return q($px ^ $n)
  | _ => throwError "unsupported gap-dependent expression: {e}"

elab "compactGapPolynomial% " f:term : term => do
  let f ← elabTerm f (some q(ℝ → ℝ))
  lambdaTelescope f fun xs body => do
    unless xs.size == 1 do throwError "expected one real gap variable"
    let names := [``HTGeometry.evenCompactRawPolynomial,
      ``HTGeometry.oddCompactSourceZero,
      ``HTGeometry.oddCompactReflectedScalar2,
      ``HTGeometry.oddCompactReflectedScalar4,
      ``HTGeometry.oddCompactReflectedScalar6,
      ``HTGeometry.oddCompactReflectedScalar8,
      ``HTGeometry.oddCompactReflectedScalar10,
      ``HTGeometry.evenCompactReflectedScalar12]
    let body ← deltaExpand body names.contains
    liftCompactGapExpression xs[0]!.fvarId! body
end

noncomputable section

/-- The exact source value viewed as a polynomial in the gap. -/
def evenCompactGapSourceZeroPolynomial (u : ℝ) : Polynomial ℝ :=
  compactGapPolynomial% (fun a : ℝ => oddCompactSourceZero u a)

/-- Evaluation returns the original source value. -/
theorem evenCompactGapSourceZeroPolynomial_eval (u a : ℝ) :
    (evenCompactGapSourceZeroPolynomial u).eval a = oddCompactSourceZero u a := by
  dsimp only [evenCompactGapSourceZeroPolynomial, oddCompactSourceZero]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, div_eq_mul_inv]

/-- The source value is affine in the gap coordinate. -/
theorem evenCompactGapSourceZeroPolynomial_degree (u : ℝ) :
    (evenCompactGapSourceZeroPolynomial u).natDegree ≤ 1 := by
  unfold evenCompactGapSourceZeroPolynomial
  compute_degree

/-- The full order-2 reflected scalar as a polynomial in the gap. -/
def evenCompactGapReflectedTwoPolynomial (u w : ℝ) : Polynomial ℝ :=
  compactGapPolynomial% (fun a : ℝ => oddCompactReflectedScalar2 u a w)

/-- Evaluation retains every original reflected-source term. -/
theorem evenCompactGapReflectedTwoPolynomial_eval (u a w : ℝ) :
    (evenCompactGapReflectedTwoPolynomial u w).eval a = oddCompactReflectedScalar2 u a w := by
  dsimp only [evenCompactGapReflectedTwoPolynomial, oddCompactReflectedScalar2]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, div_eq_mul_inv]

/-- The gap degree has the source grading required by the determinant. -/
theorem evenCompactGapReflectedTwoPolynomial_degree (u w : ℝ) :
    (evenCompactGapReflectedTwoPolynomial u w).natDegree ≤ 3 := by
  unfold evenCompactGapReflectedTwoPolynomial
  compute_degree

/-- The full order-4 reflected scalar as a polynomial in the gap. -/
def evenCompactGapReflectedFourPolynomial (u w : ℝ) : Polynomial ℝ :=
  compactGapPolynomial% (fun a : ℝ => oddCompactReflectedScalar4 u a w)

/-- Evaluation retains every original reflected-source term. -/
theorem evenCompactGapReflectedFourPolynomial_eval (u a w : ℝ) :
    (evenCompactGapReflectedFourPolynomial u w).eval a = oddCompactReflectedScalar4 u a w := by
  dsimp only [evenCompactGapReflectedFourPolynomial, oddCompactReflectedScalar4]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, div_eq_mul_inv]

/-- The gap degree has the source grading required by the determinant. -/
theorem evenCompactGapReflectedFourPolynomial_degree (u w : ℝ) :
    (evenCompactGapReflectedFourPolynomial u w).natDegree ≤ 4 := by
  unfold evenCompactGapReflectedFourPolynomial
  compute_degree

/-- The full order-6 reflected scalar as a polynomial in the gap. -/
def evenCompactGapReflectedSixPolynomial (u w : ℝ) : Polynomial ℝ :=
  compactGapPolynomial% (fun a : ℝ => oddCompactReflectedScalar6 u a w)

/-- Evaluation retains every original reflected-source term. -/
theorem evenCompactGapReflectedSixPolynomial_eval (u a w : ℝ) :
    (evenCompactGapReflectedSixPolynomial u w).eval a = oddCompactReflectedScalar6 u a w := by
  dsimp only [evenCompactGapReflectedSixPolynomial, oddCompactReflectedScalar6]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, div_eq_mul_inv]

/-- The gap degree has the source grading required by the determinant. -/
theorem evenCompactGapReflectedSixPolynomial_degree (u w : ℝ) :
    (evenCompactGapReflectedSixPolynomial u w).natDegree ≤ 5 := by
  unfold evenCompactGapReflectedSixPolynomial
  compute_degree

/-- The full order-8 reflected scalar as a polynomial in the gap. -/
def evenCompactGapReflectedEightPolynomial (u w : ℝ) : Polynomial ℝ :=
  compactGapPolynomial% (fun a : ℝ => oddCompactReflectedScalar8 u a w)

/-- Evaluation retains every original reflected-source term. -/
theorem evenCompactGapReflectedEightPolynomial_eval (u a w : ℝ) :
    (evenCompactGapReflectedEightPolynomial u w).eval a = oddCompactReflectedScalar8 u a w := by
  dsimp only [evenCompactGapReflectedEightPolynomial, oddCompactReflectedScalar8]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, div_eq_mul_inv]

/-- The gap degree has the source grading required by the determinant. -/
theorem evenCompactGapReflectedEightPolynomial_degree (u w : ℝ) :
    (evenCompactGapReflectedEightPolynomial u w).natDegree ≤ 6 := by
  unfold evenCompactGapReflectedEightPolynomial
  compute_degree

/-- The full order-10 reflected scalar as a polynomial in the gap. -/
def evenCompactGapReflectedTenPolynomial (u w : ℝ) : Polynomial ℝ :=
  compactGapPolynomial% (fun a : ℝ => oddCompactReflectedScalar10 u a w)

/-- Evaluation retains every original reflected-source term. -/
theorem evenCompactGapReflectedTenPolynomial_eval (u a w : ℝ) :
    (evenCompactGapReflectedTenPolynomial u w).eval a = oddCompactReflectedScalar10 u a w := by
  dsimp only [evenCompactGapReflectedTenPolynomial, oddCompactReflectedScalar10]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, div_eq_mul_inv]

/-- The gap degree has the source grading required by the determinant. -/
theorem evenCompactGapReflectedTenPolynomial_degree (u w : ℝ) :
    (evenCompactGapReflectedTenPolynomial u w).natDegree ≤ 7 := by
  unfold evenCompactGapReflectedTenPolynomial
  compute_degree

/-- The full order-12 reflected scalar as a polynomial in the gap. -/
def evenCompactGapReflectedTwelvePolynomial (u w : ℝ) : Polynomial ℝ :=
  compactGapPolynomial% (fun a : ℝ => evenCompactReflectedScalar12 u a w)

/-- Evaluation retains every original reflected-source term. -/
theorem evenCompactGapReflectedTwelvePolynomial_eval (u a w : ℝ) :
    (evenCompactGapReflectedTwelvePolynomial u w).eval a = evenCompactReflectedScalar12 u a w := by
  dsimp only [evenCompactGapReflectedTwelvePolynomial, evenCompactReflectedScalar12]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, div_eq_mul_inv]

/-- The gap degree has the source grading required by the determinant. -/
theorem evenCompactGapReflectedTwelvePolynomial_degree (u w : ℝ) :
    (evenCompactGapReflectedTwelvePolynomial u w).natDegree ≤ 8 := by
  unfold evenCompactGapReflectedTwelvePolynomial
  compute_degree

end
end HTGeometry

import GaloisForLFunctions.RHTower.XiShiftedReciprocalHankelTailCriterion

/-!
# Square-half-density covariance and the shifted-Hankel boundary pole

Ordinary denominator-cleared polynomial transport does not preserve a shifted Xi trace-Hankel
summand: it pays an odd, atom-dependent complex cocycle.  The unique elementary repair at the
level of the squared test is the rational square-half-density pullback.  It preserves every
multiplicity-labelled summand exactly, forms the additive Möbius semigroup, and exposes the odd
moving pole through which a witness can escape polynomial coefficient cones.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Möbius mass shift on an arbitrary complex reciprocal coordinate. -/
def reciprocalMassShift (y : ℝ) (z : ℂ) : ℂ :=
  z / (1 + (y : ℂ) * z)

/-- Pullback of a *squared* test by the Möbius mass shift.  The denominator is the square of the
weight-one-half multiplier selected by the quadratic trace. -/
def mobiusSquareHalfDensityTransport
    (y : ℝ) (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  F (w / (1 - (y : ℂ) * w)) / (1 - (y : ℂ) * w)

/-- Exact distance from a shifted point to the moving boundary pole. -/
theorem one_sub_mul_reciprocalMassShift
    {y : ℝ} {z : ℂ} (hden : 1 + (y : ℂ) * z ≠ 0) :
    1 - (y : ℂ) * reciprocalMassShift y z =
      (1 + (y : ℂ) * z)⁻¹ := by
  rw [reciprocalMassShift]
  field_simp [hden]
  ring

/-- The inverse chart of the shifted reciprocal coordinate recovers the original atom. -/
theorem reciprocalMassShift_div_one_sub
    {y : ℝ} {z : ℂ} (hden : 1 + (y : ℂ) * z ≠ 0) :
    reciprocalMassShift y z /
        (1 - (y : ℂ) * reciprocalMassShift y z) = z := by
  rw [one_sub_mul_reciprocalMassShift hden, reciprocalMassShift]
  have hden' : 1 + z * (y : ℂ) ≠ 0 := by
    simpa only [mul_comm] using hden
  field_simp [hden, hden']

/-- **Termwise trace covariance.**  Square-half-density pullback is exactly the multiplier which
preserves `z * F z` under Möbius mass shift. -/
theorem reciprocalMassShift_mul_squareHalfDensityTransport
    {y : ℝ} {z : ℂ} (hden : 1 + (y : ℂ) * z ≠ 0) (F : ℂ → ℂ) :
    reciprocalMassShift y z *
        mobiusSquareHalfDensityTransport y F (reciprocalMassShift y z) =
      z * F z := by
  rw [mobiusSquareHalfDensityTransport,
    reciprocalMassShift_div_one_sub hden,
    one_sub_mul_reciprocalMassShift hden, reciprocalMassShift]
  have hden' : 1 + z * (y : ℂ) ≠ 0 := by
    simpa only [mul_comm] using hden
  field_simp [hden, hden']

/-- The square-half-density pullbacks form the additive Möbius semigroup away from their poles. -/
theorem mobiusSquareHalfDensityTransport_add
    {y u : ℝ} {w : ℂ}
    (hu : 1 - (u : ℂ) * w ≠ 0)
    (hyu : 1 - ((y + u : ℝ) : ℂ) * w ≠ 0)
    (F : ℂ → ℂ) :
    mobiusSquareHalfDensityTransport u
        (mobiusSquareHalfDensityTransport y F) w =
      mobiusSquareHalfDensityTransport (y + u) F w := by
  have hu' : 1 - w * (u : ℂ) ≠ 0 := by
    simpa only [mul_comm] using hu
  have hyu' : 1 - w * ((y + u : ℝ) : ℂ) ≠ 0 := by
    simpa only [mul_comm] using hyu
  have hdeneq :
      1 - (y : ℂ) * (w / (1 - (u : ℂ) * w)) =
        (1 - ((y + u : ℝ) : ℂ) * w) / (1 - (u : ℂ) * w) := by
    field_simp [hu, hu']
    push_cast
    ring
  have harg :
      (w / (1 - (u : ℂ) * w)) /
          (1 - (y : ℂ) * (w / (1 - (u : ℂ) * w))) =
        w / (1 - ((y + u : ℝ) : ℂ) * w) := by
    rw [hdeneq]
    field_simp [hu, hu', hyu, hyu']
  unfold mobiusSquareHalfDensityTransport
  rw [harg, hdeneq]
  field_simp [hu, hu', hyu, hyu']

/-- On every actual Xi copy, the abstract reciprocal mass shift is the existing shifted atom. -/
theorem reciprocalMassShift_xiZeroCopy
    (y : ℝ) (q : XiZeroCopy) :
    reciprocalMassShift y (xiZeroCopyReciprocalSquare q) =
      xiShiftedReciprocalSquare y q := rfl

/-- Actual Xi atoms never hit the moving pole at any nonnegative shift. -/
theorem one_sub_mul_xiShiftedReciprocalSquare
    {y : ℝ} (hy : 0 ≤ y) (q : XiZeroCopy) :
    1 - (y : ℂ) * xiShiftedReciprocalSquare y q =
      (1 + (y : ℂ) * xiZeroCopyReciprocalSquare q)⁻¹ := by
  rw [← reciprocalMassShift_xiZeroCopy]
  exact one_sub_mul_reciprocalMassShift
    (one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hy q)

/-- The rational square-half-density test obtained from a real polynomial square. -/
def xiShiftedSquareHalfDensityTest
    (y : ℝ) (p : Polynomial ℝ) (w : ℂ) : ℂ :=
  mobiusSquareHalfDensityTransport y
    (fun z => evalRealPolynomial p z ^ 2) w

/-- Multiplicity-labelled shifted trace term on the rational square-half-density carrier. -/
def xiShiftedSquareHalfDensityTraceTerm
    (y : ℝ) (p : Polynomial ℝ) (q : XiZeroCopy) : ℂ :=
  xiShiftedReciprocalSquare y q *
    xiShiftedSquareHalfDensityTest y p (xiShiftedReciprocalSquare y q)

/-- Every multiplicity-labelled trace term is invariant under square-half-density transport. -/
theorem xiShiftedSquareHalfDensityTraceTerm_eq_zeroShift
    {y : ℝ} (hy : 0 ≤ y) (p : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedSquareHalfDensityTraceTerm y p q =
      xiShiftedReciprocalTraceHankelTerm 0 p q := by
  rw [xiShiftedSquareHalfDensityTraceTerm, xiShiftedSquareHalfDensityTest,
    ← reciprocalMassShift_xiZeroCopy]
  rw [reciprocalMassShift_mul_squareHalfDensityTransport
    (one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hy q)]
  simp [xiShiftedReciprocalTraceHankelTerm, xiShiftedReciprocalSquare]

/-- Full multiplicity-exact trace on the transported square-half-density carrier. -/
def xiShiftedSquareHalfDensityTraceHankel
    (y : ℝ) (p : Polynomial ℝ) : ℂ :=
  ∑' q : XiZeroCopy, xiShiftedSquareHalfDensityTraceTerm y p q

/-- The full transported trace is exactly the unshifted polynomial trace. -/
theorem xiShiftedSquareHalfDensityTraceHankel_eq_zeroShift
    {y : ℝ} (hy : 0 ≤ y) (p : Polynomial ℝ) :
    xiShiftedSquareHalfDensityTraceHankel y p =
      xiShiftedReciprocalTraceHankel 0 p := by
  rw [xiShiftedSquareHalfDensityTraceHankel,
    xiShiftedReciprocalTraceHankel]
  apply tsum_congr
  exact xiShiftedSquareHalfDensityTraceTerm_eq_zeroShift hy p

/-- Denominator-cleared polynomial pullback.  Unlike the square-half-density carrier, this stays
at finite polynomial degree but pays an odd trace cocycle. -/
def mobiusDenominatorClearedPolynomialTest
    (y : ℝ) (d : ℕ) (p : Polynomial ℝ) (w : ℂ) : ℂ :=
  (1 - (y : ℂ) * w) ^ d *
    evalRealPolynomial p (w / (1 - (y : ℂ) * w))

/-- **Exact polynomial-transport obstruction.**  At a shifted Xi atom, clearing degree `d`
rotates the central trace term by the odd complex cocycle `(1 + y z)^(-(2d+1))`. -/
theorem xiShifted_denominatorClearedPolynomialTrace_eq_oddCocycle
    {y : ℝ} (hy : 0 ≤ y) (d : ℕ) (p : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedReciprocalSquare y q *
        mobiusDenominatorClearedPolynomialTest y d p
          (xiShiftedReciprocalSquare y q) ^ 2 =
      xiZeroCopyReciprocalSquare q *
          evalRealPolynomial p (xiZeroCopyReciprocalSquare q) ^ 2 /
        (1 + (y : ℂ) * xiZeroCopyReciprocalSquare q) ^ (2 * d + 1) := by
  let z := xiZeroCopyReciprocalSquare q
  have hden : 1 + (y : ℂ) * z ≠ 0 :=
    one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hy q
  rw [← reciprocalMassShift_xiZeroCopy]
  rw [mobiusDenominatorClearedPolynomialTest,
    reciprocalMassShift_div_one_sub hden,
    one_sub_mul_reciprocalMassShift hden, reciprocalMassShift]
  change z / (1 + (y : ℂ) * z) *
      (((1 + (y : ℂ) * z)⁻¹) ^ d * evalRealPolynomial p z) ^ 2 =
    z * evalRealPolynomial p z ^ 2 /
      (1 + (y : ℂ) * z) ^ (2 * d + 1)
  let D := 1 + (y : ℂ) * z
  let e := evalRealPolynomial p z
  have hsquare : ((D⁻¹) ^ d * e) ^ 2 = e ^ 2 / D ^ (2 * d) := by
    rw [mul_pow, ← pow_mul, inv_pow]
    simp only [Nat.mul_comm d 2, div_eq_mul_inv]
    ring
  change z / D * ((D⁻¹) ^ d * e) ^ 2 = z * e ^ 2 / D ^ (2 * d + 1)
  rw [hsquare, div_mul_div_comm]
  congr 1
  rw [pow_succ]
  ring

/-- Monomial squares display the unavoidable odd boundary pole explicitly. -/
theorem mobiusSquareHalfDensityTransport_evenMonomial
    (y : ℝ) (d : ℕ) (w : ℂ) :
    mobiusSquareHalfDensityTransport y (fun z => z ^ (2 * d)) w =
      w ^ (2 * d) / (1 - (y : ℂ) * w) ^ (2 * d + 1) := by
  rw [mobiusSquareHalfDensityTransport, div_pow]
  simp only [div_eq_mul_inv, pow_succ, mul_inv]
  ring

end

end RHTower

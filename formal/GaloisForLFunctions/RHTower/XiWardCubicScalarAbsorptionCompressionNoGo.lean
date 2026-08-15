import GaloisForLFunctions.RHTower.XiWardInteriorReflectionAbsorption

/-!
# Scalar Ward absorption does not control cubic mixed compression

Functional-equation absorption supplies a pointwise scalar upper bound for the continued Ward
response.  The cubic Euler collision kernel instead uses a signed four-point mixed difference.
This file proves, unconditionally, that this difference is positive on every positive exponential
Euler atom, negative after the von-Mangoldt sign occurring in the scalar Ward source, and is not
monotone for pointwise order even on the nonnegative source half-line.

Consequently the scalar pole--Gamma--von-Mangoldt Ward inequality cannot be passed through cubic
compression.  Any completed source-trace landing must retain a matrix-valued or graded source
identity before real-part scalarization.
-/

namespace RHTower

noncomputable section

/-- Signed four-point mixed difference used by the dyadic cubic Euler covariance. -/
def wardCubicFourPointDifference (F : ℝ → ℝ) (u r s : ℝ) : ℝ :=
  F (u + r + s) - F (u + r + 2 * s) -
    F (u + 2 * r + s) + F (u + 2 * r + 2 * s)

/-- One positive Dirichlet/Laplace atom. -/
def wardEulerExponentialAtom (lambda t : ℝ) : ℝ :=
  Real.exp (-lambda * t)

theorem wardEulerExponentialAtom_add (lambda x y : ℝ) :
    wardEulerExponentialAtom lambda (x + y) =
      wardEulerExponentialAtom lambda x * wardEulerExponentialAtom lambda y := by
  rw [wardEulerExponentialAtom, wardEulerExponentialAtom,
    wardEulerExponentialAtom, ← Real.exp_add]
  congr 1
  ring

theorem wardEulerExponentialAtom_two_mul (lambda x : ℝ) :
    wardEulerExponentialAtom lambda (2 * x) =
      wardEulerExponentialAtom lambda x ^ 2 := by
  rw [show 2 * x = x + x by ring, wardEulerExponentialAtom_add, pow_two]

/-- Exact atomwise factorization of the cubic mixed difference.  This is the source of positivity
for the Euler covariance built from `+LSeries(vonMangoldt, ·)`. -/
theorem wardCubicFourPointDifference_exponentialAtom
    (lambda u r s : ℝ) :
    wardCubicFourPointDifference (wardEulerExponentialAtom lambda) u r s =
      wardEulerExponentialAtom lambda u *
        (wardEulerExponentialAtom lambda r -
          wardEulerExponentialAtom lambda (2 * r)) *
        (wardEulerExponentialAtom lambda s -
          wardEulerExponentialAtom lambda (2 * s)) := by
  rw [wardCubicFourPointDifference]
  rw [show u + r + s = u + (r + s) by ring,
    show u + r + 2 * s = u + (r + 2 * s) by ring,
    show u + 2 * r + s = u + (2 * r + s) by ring,
    show u + 2 * r + 2 * s = u + (2 * r + 2 * s) by ring]
  rw [wardEulerExponentialAtom_add, wardEulerExponentialAtom_add,
    wardEulerExponentialAtom_add, wardEulerExponentialAtom_add,
    wardEulerExponentialAtom_add, wardEulerExponentialAtom_add,
    wardEulerExponentialAtom_add, wardEulerExponentialAtom_add]
  ring

/-- Every positive Laplace frequency and two positive dyadic scales give a strictly positive Euler
mixed atom. -/
theorem wardCubicFourPointDifference_exponentialAtom_pos
    {lambda r s : ℝ} (hlambda : 0 < lambda) (hr : 0 < r) (hs : 0 < s)
    (u : ℝ) :
    0 < wardCubicFourPointDifference
      (wardEulerExponentialAtom lambda) u r s := by
  rw [wardCubicFourPointDifference_exponentialAtom]
  have hr' : 0 < wardEulerExponentialAtom lambda r -
      wardEulerExponentialAtom lambda (2 * r) := by
    rw [sub_pos, wardEulerExponentialAtom, wardEulerExponentialAtom]
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hs' : 0 < wardEulerExponentialAtom lambda s -
      wardEulerExponentialAtom lambda (2 * s) := by
    rw [sub_pos, wardEulerExponentialAtom, wardEulerExponentialAtom]
    apply Real.exp_lt_exp.mpr
    nlinarith
  exact mul_pos (mul_pos (Real.exp_pos _) hr') hs'

/-- Negating the prime atom negates its mixed difference.  In particular the `-LSeries` prime
component in the scalar Ward source has the opposite mixed sign from the positive Euler
covariance. -/
theorem wardCubicFourPointDifference_neg_exponentialAtom
    (lambda u r s : ℝ) :
    wardCubicFourPointDifference
      (fun t => -wardEulerExponentialAtom lambda t) u r s =
      -wardCubicFourPointDifference
        (wardEulerExponentialAtom lambda) u r s := by
  rw [wardCubicFourPointDifference, wardCubicFourPointDifference]
  ring

/-- Explicit order counterexample: this function is nonnegative on the entire source half-line,
but its cubic mixed difference is strictly negative. -/
def wardScalarOrderCounterexample (t : ℝ) : ℝ :=
  1 - wardEulerExponentialAtom 1 t

theorem wardScalarOrderCounterexample_nonneg :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ wardScalarOrderCounterexample t := by
  intro t ht
  rw [wardScalarOrderCounterexample, sub_nonneg,
    wardEulerExponentialAtom]
  calc
    Real.exp (-(1 : ℝ) * t) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

/-- Pointwise scalar order on the whole nonnegative source ray is reversed by one concrete cubic
four-point compression.  Hence no theorem can push the scalar Ward absorption inequality through
this compression using order alone. -/
theorem wardCubicFourPointDifference_scalarOrderCounterexample :
    (∀ t : ℝ, 0 ≤ t → (0 : ℝ) ≤ wardScalarOrderCounterexample t) ∧
      wardCubicFourPointDifference (fun _ => 0) 0 1 1 >
        wardCubicFourPointDifference wardScalarOrderCounterexample 0 1 1 := by
  constructor
  · exact wardScalarOrderCounterexample_nonneg
  · have hpos := wardCubicFourPointDifference_exponentialAtom_pos
      (lambda := (1 : ℝ)) (r := (1 : ℝ)) (s := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) 0
    have hcounter :
        wardCubicFourPointDifference wardScalarOrderCounterexample 0 1 1 =
          -wardCubicFourPointDifference
            (wardEulerExponentialAtom 1) 0 1 1 := by
      rw [wardCubicFourPointDifference, wardCubicFourPointDifference,
        wardScalarOrderCounterexample,
        wardScalarOrderCounterexample, wardScalarOrderCounterexample,
        wardScalarOrderCounterexample]
      ring
    have hzero :
        wardCubicFourPointDifference (fun _ => 0) 0 1 1 = 0 := by
      simp [wardCubicFourPointDifference]
    rw [hzero, hcounter]
    linarith

end


end RHTower

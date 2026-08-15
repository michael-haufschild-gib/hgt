import GaloisForLFunctions.RHTower.BakerGeneralProof.AuxiliaryChainRule

/-!
# Differential transport through Baker component operators

This file gives the first-order analytic transport formula for a number-field auxiliary
polynomial and proves the exact effect of the common integer scale on each component derivation
and its iterates.  The latter identity preserves the integral algebraic data required by the
Siegel and extrapolation stages.
-/

open scoped Classical

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- Analytic function obtained by evaluating a number-field auxiliary polynomial on the curve. -/
noncomputable def SolvedRelation.auxiliaryFunction
    (R : SolvedRelation) (P : MvPolynomial R.Variable R.CoefficientField) (z : ℂ) : ℂ :=
  MvPolynomial.eval (R.auxiliaryPoint z) (R.complexify P)

/-- First-order differential transport from the analytic curve to the component operators. -/
theorem SolvedRelation.deriv_auxiliaryFunction
    (R : SolvedRelation) (P : MvPolynomial R.Variable R.CoefficientField) (z : ℂ) :
    deriv (R.auxiliaryFunction P) z =
      R.auxiliaryFunction (R.componentDerivation 1 none P) z +
        ∑ i : R.NonPivot,
          R.lambda i * R.auxiliaryFunction (R.componentDerivation 1 (some i) P) z := by
  unfold SolvedRelation.auxiliaryFunction
  rw [R.deriv_eval_auxiliaryPoint, R.analyticDerivation_complexify_eq_componentSum]
  simp [SolvedRelation.componentSum]

/-- Scaling a component vector field by an integer is multiplication by its constant polynomial. -/
theorem SolvedRelation.componentVector_scale
    (R : SolvedRelation) (c : ℤ) (d : R.Direction) (v : R.Variable) :
    R.componentVector c d v =
      MvPolynomial.C (R.integerScalar c) * R.componentVector 1 d v := by
  cases d <;> cases v <;>
    simp [SolvedRelation.componentVector, SolvedRelation.integerScalar,
      SolvedRelation.scaledComponentCoeff, zsmul_eq_mul] <;>
    split_ifs <;>
    simp [mul_comm, mul_left_comm, mul_add]

/-- The scaled component derivation is the corresponding scalar multiple of the unit-scale one. -/
theorem SolvedRelation.componentDerivation_scale
    (R : SolvedRelation) (c : ℤ) (d : R.Direction)
    (P : MvPolynomial R.Variable R.CoefficientField) :
    R.componentDerivation c d P =
      MvPolynomial.C (R.integerScalar c) * R.componentDerivation 1 d P := by
  have hderiv : R.componentDerivation c d =
      R.integerScalar c • R.componentDerivation 1 d := by
    apply MvPolynomial.derivation_ext
    intro v
    rw [Derivation.smul_apply, R.componentDerivation_X, R.componentDerivation_X]
    rw [R.componentVector_scale]
    exact MvPolynomial.C_mul'
  simpa only [Derivation.smul_apply, ← MvPolynomial.C_mul'] using
    congrArg (fun D : Derivation R.CoefficientField
      (MvPolynomial R.Variable R.CoefficientField)
      (MvPolynomial R.Variable R.CoefficientField) => D P) hderiv

private theorem SolvedRelation.componentDerivation_one_C_mul
    (R : SolvedRelation) (d : R.Direction) (a : R.CoefficientField)
    (P : MvPolynomial R.Variable R.CoefficientField) :
    R.componentDerivation 1 d (MvPolynomial.C a * P) =
      MvPolynomial.C a * R.componentDerivation 1 d P := by
  rw [Derivation.leibniz, MvPolynomial.derivation_C]
  simp

/-- Iterating a scaled component contributes exactly the corresponding power of its scale. -/
theorem SolvedRelation.componentDerivation_iterate_scale
    (R : SolvedRelation) (c : ℤ) (d : R.Direction) (k : ℕ)
    (P : MvPolynomial R.Variable R.CoefficientField) :
    (R.componentDerivation c d)^[k] P =
      (MvPolynomial.C (R.integerScalar c)) ^ k *
        (R.componentDerivation 1 d)^[k] P := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, R.componentDerivation_scale]
      rw [← MvPolynomial.C_pow, R.componentDerivation_one_C_mul]
      rw [MvPolynomial.C_pow, ← mul_assoc, ← pow_succ']
      congr 1
      exact (Function.iterate_succ_apply' (R.componentDerivation 1 d) k P).symm

end GaloisForLFunctions.RHTower.BakerGeneralProof

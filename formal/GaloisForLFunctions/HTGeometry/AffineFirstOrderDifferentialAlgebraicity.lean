import GaloisForLFunctions.HTGeometry.FormalMahlerIntegerNormalization

/-!
# Affine first-order differential algebraicity

A first-order affine differential constraint with coefficients in the base field is itself a
nonzero finite-jet relation.  This module exposes that reusable Prop interface directly, covering
both primitives (`y' = b`) and exponential gauges (`y' = a y`) without auxiliary closure
hypotheses.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Affine first-order DA law.**  Any element satisfying `y' = a y + b` with base-field
coefficients is differentially algebraic over that base. -/
theorem differentialAlgebraicOver_of_deriv_eq_base_mul_add
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {y : E} (a b : F)
    (hrel : y′ = algebraMap F E a * y + algebraMap F E b) :
    DifferentialAlgebraicOver F y := by
  let Q : MvPolynomial (Fin 2) F :=
    MvPolynomial.X 1 -
      (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b)
  have hQ : Q ≠ 0 := by
    intro hzero
    have hev := congrArg
      (MvPolynomial.eval (fun i : Fin 2 ↦ if i = 1 then b + 1 else 0)) hzero
    simp [Q] at hev
  apply differentialAlgebraicOver_of_finiteJetRelation hQ
  simpa [Q] using sub_eq_zero.mpr hrel

/-- A primitive of a base-field element is differentially algebraic over the base. -/
theorem differentialAlgebraicOver_of_deriv_eq_base
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {y : E} (b : F) (hrel : y′ = algebraMap F E b) :
    DifferentialAlgebraicOver F y := by
  apply differentialAlgebraicOver_of_deriv_eq_base_mul_add 0 b
  simpa using hrel

/-- A homogeneous first-order linear differential constraint is the zero-intercept specialization
of the affine law. -/
theorem differentialAlgebraicOver_of_deriv_eq_base_mul
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {y : E} (a : F) (hrel : y′ = algebraMap F E a * y) :
    DifferentialAlgebraicOver F y := by
  apply differentialAlgebraicOver_of_deriv_eq_base_mul_add a 0
  simpa using hrel

end


end GaloisForLFunctions.HTGeometry

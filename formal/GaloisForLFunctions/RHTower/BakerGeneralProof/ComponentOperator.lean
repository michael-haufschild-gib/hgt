import GaloisForLFunctions.RHTower.BakerGeneralProof.SolvedRelationConstruction
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie

/-!
# Commuting component operators for Baker's theorem

A solved inhomogeneous relation separates ordinary differentiation into algebraic polynomial
vector fields.  The constant component differentiates the additive variable; each remaining
component differentiates one exponential variable; all components also act diagonally on the
pivot exponential variable with the corresponding solved coefficient.  A common integer scale
makes their coefficients integral for the later auxiliary-polynomial argument.

This file constructs these vector fields as genuine derivations of the multivariate polynomial
ring and proves that every pair commutes.  No choice of logarithm branch is made here: the input
is the arbitrary-branch `SolvedRelation`.
-/

open scoped Classical

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- Auxiliary-polynomial variables: one additive variable and one variable per logarithm. -/
abbrev SolvedRelation.Variable (R : SolvedRelation) := Option (Fin R.n)

/-- Component directions: the constant term and all non-pivot logarithms. -/
abbrev SolvedRelation.Direction (R : SolvedRelation) := Option R.NonPivot

/-- The integer scaling factor regarded as an element of the coefficient number field. -/
noncomputable def SolvedRelation.integerScalar
    (R : SolvedRelation) (c : ℤ) : R.CoefficientField :=
  c • 1

/-- A solved coefficient multiplied by the common integer scaling factor. -/
noncomputable def SolvedRelation.scaledComponentCoeff
    (R : SolvedRelation) (c : ℤ) (d : R.Direction) : R.CoefficientField :=
  c • R.componentCoeffLift d

/-- Polynomial vector field underlying one scaled component operator. -/
noncomputable def SolvedRelation.componentVector
    (R : SolvedRelation) (c : ℤ) (d : R.Direction) (v : R.Variable) :
    MvPolynomial R.Variable R.CoefficientField :=
  match d, v with
  | none, none => MvPolynomial.C (R.integerScalar c)
  | none, some j =>
      if j = R.pivot then
        MvPolynomial.C (R.scaledComponentCoeff c none) * MvPolynomial.X (some j)
      else 0
  | some _, none => 0
  | some i, some j =>
      (if j = i then
          MvPolynomial.C (R.integerScalar c) * MvPolynomial.X (some j)
        else 0) +
      (if j = R.pivot then
          MvPolynomial.C (R.scaledComponentCoeff c (some i)) * MvPolynomial.X (some j)
        else 0)

/-- Scaled algebraic component operator as a derivation of the auxiliary polynomial ring. -/
noncomputable def SolvedRelation.componentDerivation
    (R : SolvedRelation) (c : ℤ) (d : R.Direction) :
    Derivation R.CoefficientField
      (MvPolynomial R.Variable R.CoefficientField)
      (MvPolynomial R.Variable R.CoefficientField) :=
  MvPolynomial.mkDerivation R.CoefficientField (R.componentVector c d)

@[simp] theorem SolvedRelation.componentDerivation_X
    (R : SolvedRelation) (c : ℤ) (d : R.Direction) (v : R.Variable) :
    R.componentDerivation c d (MvPolynomial.X v) = R.componentVector c d v := by
  exact MvPolynomial.mkDerivation_X
    (R := R.CoefficientField) (R.componentVector c d) v

/-- All scaled component operators commute on every auxiliary polynomial. -/
theorem SolvedRelation.componentDerivation_comm
    (R : SolvedRelation) (c : ℤ) (d e : R.Direction)
    (P : MvPolynomial R.Variable R.CoefficientField) :
    R.componentDerivation c d (R.componentDerivation c e P) =
      R.componentDerivation c e (R.componentDerivation c d P) := by
  let D := R.componentDerivation c d
  let E := R.componentDerivation c e
  have hbracket : ⁅D, E⁆ = (0 : Derivation R.CoefficientField
      (MvPolynomial R.Variable R.CoefficientField)
      (MvPolynomial R.Variable R.CoefficientField)) := by
    apply MvPolynomial.derivation_ext
    intro v
    rw [Derivation.commutator_apply]
    dsimp [D, E]
    rw [R.componentDerivation_X, R.componentDerivation_X]
    cases d <;> cases e <;> cases v <;>
      simp [SolvedRelation.componentVector] <;>
      split_ifs <;>
      simp_all [SolvedRelation.componentVector, Derivation.leibniz] <;>
      ring
  have happ := congrArg
    (fun A : Derivation R.CoefficientField
      (MvPolynomial R.Variable R.CoefficientField)
      (MvPolynomial R.Variable R.CoefficientField) => A P) hbracket
  rw [Derivation.commutator_apply] at happ
  exact sub_eq_zero.mp happ

end GaloisForLFunctions.RHTower.BakerGeneralProof

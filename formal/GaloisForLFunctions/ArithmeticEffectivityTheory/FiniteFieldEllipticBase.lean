import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# An elliptic function field over the three-element field

The projective Weierstrass cubic `Y²Z = X³ − XZ²` has discriminant one over `𝔽₃`.
Its affine coordinate ring is the actual quotient by the Weierstrass equation, and its
function field is the fraction field of that domain. The basis `{1,y}` over `𝔽₃[x]`
gives transcendence degree one. The point equivalence includes the point at infinity
and identifies every scalar extension with the hyperelliptic equation `y²=x³−x`.
-/

open Polynomial
open scoped nonZeroDivisors

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

attribute [local instance] Classical.propDecidable

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The finite constant field. -/
abbrev Constants := ZMod 3

/-- The Weierstrass model whose projective equation is `Y²Z=X³−XZ²`. -/
def curve : WeierstrassCurve Constants := ⟨0, 0, 0, -1, 0⟩

instance : curve.IsShortNF := ⟨rfl, rfl, rfl⟩

/-- In characteristic three the short-form discriminant is `−a₄³`. -/
theorem discriminant_eq_one : curve.Δ = 1 := by
  rw [WeierstrassCurve.Δ_of_isShortNF_of_char_three]
  norm_num [curve]

instance : curve.IsElliptic := ⟨discriminant_eq_one.symm ▸ isUnit_one⟩

/-- The affine coordinate domain `𝔽₃[x,y]/(y²−x³+x)`. -/
abbrev CoordinateRing := curve.toAffine.CoordinateRing

/-- The function field of the nonsingular projective cubic. -/
abbrev FunctionField := curve.toAffine.FunctionField

noncomputable instance : Module.Free Constants[X] CoordinateRing :=
  Module.Free.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis _)

instance : Module.Finite Constants[X] CoordinateRing :=
  Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis _)

instance : Algebra.IsAlgebraic CoordinateRing FunctionField :=
  IsLocalization.isAlgebraic FunctionField CoordinateRing⁰

instance : Algebra.IsAlgebraic Constants[X] FunctionField :=
  Algebra.IsAlgebraic.trans Constants[X] CoordinateRing FunctionField

/-- Passing from the finite coordinate algebra to its fraction field preserves dimension. -/
theorem functionField_trdeg_eq_one : Algebra.trdeg Constants FunctionField = 1 := by
  have h := trdeg_add_eq Constants Constants[X] (A := FunctionField)
  rw [Polynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero] at h
  exact h.symm

/-- The polynomial defining the degree-two map to the `x`-line. -/
noncomputable def cubic : Constants[X] := X ^ 3 - X

theorem cubic_natDegree : cubic.natDegree = 3 := by
  rw [cubic, natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
  simp only [natDegree_X, natDegree_X_pow]
  norm_num

/-- The derivative is a unit, so no geometric branch root is repeated. -/
theorem cubic_derivative : cubic.derivative = -1 := by
  simp only [cubic, derivative_sub, derivative_X_pow, derivative_X,
    CharP.cast_eq_zero Constants 3, C_0, zero_mul, zero_sub]

theorem cubic_squarefree : Squarefree cubic := by
  apply Polynomial.Separable.squarefree
  change IsCoprime cubic cubic.derivative
  rw [cubic_derivative]
  exact ⟨0, -1, by ring⟩

theorem cubic_odd : Odd cubic.natDegree := by
  rw [cubic_natDegree]
  exact ⟨1, rfl⟩

section Points

variable (E : Type*) [Field E] [Algebra Constants E]

/-- Projective points, represented by nonsingular affine points and infinity. -/
abbrev Points := (curve.map (algebraMap Constants E)).toAffine.Point

theorem equation_iff (x y : E) :
    (curve.map (algebraMap Constants E)).toAffine.Equation x y ↔
      y ^ 2 = aeval x cubic := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [curve, cubic, sub_eq_add_neg]

/-- The affine equation and the added point are the same projective curve over every extension. -/
noncomputable def pointsEquiv :
    Points E ≃ Option {xy : E × E // xy.2 ^ 2 = aeval xy.1 cubic} :=
  (curve.map (algebraMap Constants E)).toAffine.pointEquiv.trans
    (Equiv.optionCongr (Equiv.subtypeEquivRight fun xy => equation_iff E xy.1 xy.2))

variable [Fintype E]

noncomputable instance : Fintype (Points E) :=
  Fintype.ofEquiv _ (pointsEquiv E).symm

/-- The cardinality counts the point at infinity exactly once. -/
theorem card_points : Nat.card (Points E) =
    (Finset.univ.filter fun xy : E × E => xy.2 ^ 2 = aeval xy.1 cubic).card + 1 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (pointsEquiv E),
    Fintype.card_option, Fintype.card_subtype]

end Points

end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

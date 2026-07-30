import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Quantum possibility/composition orientation fracture

Reversing a product preserves its square and symmetric Jordan part, negates its antisymmetric Lie
part, and preserves associativity. Thus symmetric possibility data cannot distinguish a product
from its opposite orientation.

The final theorem records the topological obstruction relevant after the operator-algebra
classification of factor orientations: a continuous two-valued orientation on a preconnected
space is constant.

These are unconditional algebra and topology theorems. They do not formalize the Alfsen--Shultz
classification, physical time, spacetime, or gravity.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

variable {A : Type u}

/-- Product with reversed order. -/
def reverseProduct (mul : A → A → A) (x y : A) : A :=
  mul y x

/-- Unnormalized symmetric, or Jordan, part of a product. -/
def productSymmetricPart [AddCommSemigroup A] (mul : A → A → A) (x y : A) : A :=
  mul x y + mul y x

/-- Unnormalized antisymmetric, or Lie, part of a product. -/
def productAntisymmetricPart [AddGroup A] (mul : A → A → A) (x y : A) : A :=
  mul x y - mul y x

/-- Associativity stated for a bare binary product. -/
def IsAssociativeProduct (mul : A → A → A) : Prop :=
  ∀ x y z, mul (mul x y) z = mul x (mul y z)

/-- Reversing a product does not change its square. -/
theorem reverseProduct_square (mul : A → A → A) (x : A) :
    reverseProduct mul x x = mul x x := by
  rfl

/-- **Possibility-orientation blindness.** Reversing multiplication preserves its symmetric
Jordan part exactly. -/
theorem productSymmetricPart_reverse [AddCommSemigroup A]
    (mul : A → A → A) (x y : A) :
    productSymmetricPart (reverseProduct mul) x y =
      productSymmetricPart mul x y := by
  simp [productSymmetricPart, reverseProduct, add_comm]

/-- **Composition-orientation reversal.** Reversing multiplication negates its antisymmetric Lie
part exactly. -/
theorem productAntisymmetricPart_reverse [AddGroup A]
    (mul : A → A → A) (x y : A) :
    productAntisymmetricPart (reverseProduct mul) x y =
      -productAntisymmetricPart mul x y := by
  simp [productAntisymmetricPart, reverseProduct]

/-- The opposite of an associative product is associative. -/
theorem isAssociativeProduct_reverse (mul : A → A → A)
    (h : IsAssociativeProduct mul) :
    IsAssociativeProduct (reverseProduct mul) := by
  intro x y z
  exact (h z y x).symm

/-- **Two-orientation rigidity.** A continuous two-valued orientation field on a preconnected
space is constant. In the physical application, the separate operator-algebra classification is
needed to identify factor orientations with these two values. -/
theorem continuous_quantumOrientation_constant
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (orientation : X → Bool) (horientation : Continuous orientation)
    (x y : X) :
    orientation x = orientation y :=
  PreconnectedSpace.constant ‹PreconnectedSpace X› horientation

end GaloisForLFunctions.HTGeometry


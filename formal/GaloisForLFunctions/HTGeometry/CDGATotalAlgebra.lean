import GaloisForLFunctions.HTGeometry.CDGAUnital
import Mathlib.Algebra.DirectSum.Algebra

/-!
# The total algebra of a unital commutative differential graded algebra

Summing the degrees of a unital commutative differential graded algebra gives an associative unital
`R`-algebra: the graded product is bilinear, associative and unital, so the family is a graded ring
in the sense of direct sums.  It is not a commutative ring — the product is commutative only up to
the Koszul sign — but that is irrelevant for its use as a receptacle for universal properties of
algebras.

The family is carried by a type synonym so that the algebra and its unit are visible to instance
resolution.

* `CDGATotalCarrier` : the degrees of a unital algebra, as a family instance resolution can see.
* `CDGATotal` : the direct sum of the degrees, a ring and an `R`-algebra.
* `cdgaTotalOf` : the inclusion of a degree.
-/

universe u v

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)]

/-- The product does not depend on the proof identifying the target degree: transporting along the
identification is the same as using it in the product. -/
theorem CDGAStructure.mul_eq_rec (A : CDGAStructure R X) {a b n : ℕ} (h : a + b = n) (x : X a)
    (y : X b) : A.mul h x y = h ▸ A.mul rfl x y := by
  cases h
  rfl

/-- The degrees of a unital commutative differential graded algebra, as a family that instance
resolution can see the algebra and the unit in. -/
def CDGATotalCarrier (A : CDGAStructure R X) (_u : CDGAUnit A) (n : ℕ) : Type v := X n

namespace CDGATotalCarrier

variable {A : CDGAStructure R X} {u : CDGAUnit A}

instance (n : ℕ) : AddCommGroup (CDGATotalCarrier A u n) := inferInstanceAs (AddCommGroup (X n))

instance (n : ℕ) : Module R (CDGATotalCarrier A u n) := inferInstanceAs (Module R (X n))

instance : GradedMonoid.GOne (CDGATotalCarrier A u) where
  one := u.one

instance : GradedMonoid.GMul (CDGATotalCarrier A u) where
  mul {_ _} x y := A.mul rfl x y

theorem gMul_def {i j : ℕ} (x : CDGATotalCarrier A u i) (y : CDGATotalCarrier A u j) :
    GradedMonoid.GMul.mul x y = A.mul rfl x y := rfl

theorem gOne_def : (GradedMonoid.GOne.one : CDGATotalCarrier A u 0) = u.one := rfl

instance : DirectSum.GNonUnitalNonAssocSemiring (CDGATotalCarrier A u) where
  mul_zero {i j} x := by
    show A.mul rfl (x : X i) (0 : X j) = 0
    have h0 : (0 : X j) = (0 : R) • (0 : X j) := (zero_smul R _).symm
    rw [h0, A.mul_smul_right, zero_smul]
  zero_mul {i j} y := by
    show A.mul rfl (0 : X i) (y : X j) = 0
    have h0 : (0 : X i) = (0 : R) • (0 : X i) := (zero_smul R _).symm
    rw [h0, A.mul_smul_left, zero_smul]
  mul_add {i j} x y z := A.mul_add_right rfl (x : X i) (y : X j) z
  add_mul {i j} x y z := A.mul_add_left rfl (x : X i) (y : X i) (z : X j)

end CDGATotalCarrier

end GaloisForLFunctions.HTGeometry

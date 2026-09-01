import Mathlib.Algebra.Group.Basic

/-!
# Group structure from internal right inverses

A monoid in which every element admits a right inverse has a canonical noncomputable group
structure.  This packages set- and submonoid-level Galois constructions as honest groups.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A chosen right inverse in a monoid where all right inverses exist. -/
def chosenRightInverse {M : Type*} [Monoid M]
    (h : ∀ x : M, ∃ y : M, x * y = 1) (x : M) : M :=
  Classical.choose (h x)

theorem mul_chosenRightInverse {M : Type*} [Monoid M]
    (h : ∀ x : M, ∃ y : M, x * y = 1) (x : M) :
    x * chosenRightInverse h x = 1 :=
  Classical.choose_spec (h x)

theorem chosenRightInverse_mul {M : Type*} [Monoid M]
    (h : ∀ x : M, ∃ y : M, x * y = 1) (x : M) :
    chosenRightInverse h x * x = 1 := by
  let y := chosenRightInverse h x
  let z := chosenRightInverse h y
  have hxy : x * y = 1 := mul_chosenRightInverse h x
  have hyz : y * z = 1 := mul_chosenRightInverse h y
  have hxz : x = z := by
    calc
      x = x * 1 := (mul_one x).symm
      _ = x * (y * z) := by rw [hyz]
      _ = (x * y) * z := (mul_assoc x y z).symm
      _ = z := by rw [hxy, one_mul]
  rw [show chosenRightInverse h x = y by rfl, hxz]
  exact hyz

/-- Group structure forced by the existence of a right inverse for every monoid element. -/
@[reducible] noncomputable def groupOfRightInverses {M : Type*} [Monoid M]
    (h : ∀ x : M, ∃ y : M, x * y = 1) : Group M where
  inv := chosenRightInverse h
  inv_mul_cancel := chosenRightInverse_mul h

end

end GaloisForLFunctions.HTGeometry

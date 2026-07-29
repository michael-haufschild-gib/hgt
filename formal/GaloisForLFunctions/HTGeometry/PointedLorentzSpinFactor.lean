import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

/-!
# A pointed Euclidean carrier canonically defines a Lorentz spin factor

A unit direction `u` in a real inner-product space splits every vector into its scalar component
along `u` and its orthogonal spatial component. This file proves:

* the exact scalar-plus-spatial reconstruction;
* in dimension four, the spatial complement has dimension three;
* the resulting quadratic form is one positive scalar square minus the Euclidean spatial square;
* the associated product on `ℝ × E` is unital, commutative, and satisfies the Jordan identity.

These are unconditional algebraic facts. No event, clock, spacetime, causal signalling, or
gravitational interpretation is assumed.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scalar coordinate selected by a pointed Euclidean direction. -/
def pointedTime (u x : E) : ℝ :=
  inner ℝ u x

/-- Component orthogonal to a pointed Euclidean direction. -/
def pointedSpace (u x : E) : E :=
  x - pointedTime u x • u

/-- Lorentz quadratic form reconstructed from a pointed Euclidean direction. -/
def pointedLorentzQuadratic (u x : E) : ℝ :=
  pointedTime u x ^ 2 - inner ℝ (pointedSpace u x) (pointedSpace u x)

/-- The spatial component is orthogonal to a unit pointing direction. -/
theorem inner_pointedSpace_eq_zero
    (u x : E) (hu : inner ℝ u u = 1) :
    inner ℝ u (pointedSpace u x) = 0 := by
  simp only [pointedSpace, pointedTime, inner_sub_right, inner_smul_right, hu, mul_one]
  ring

/-- Scalar and spatial components reconstruct the original vector. -/
theorem pointedTime_smul_add_pointedSpace (u x : E) :
    pointedTime u x • u + pointedSpace u x = x := by
  simp [pointedSpace]

/-- A unit pointing direction is nonzero. -/
theorem ne_zero_of_inner_self_eq_one
    (u : E) (hu : inner ℝ u u = 1) :
    u ≠ 0 := by
  intro h
  subst u
  simp at hu

/-- In a four-dimensional Euclidean carrier, the spatial complement of a unit point is
three-dimensional. -/
theorem finrank_pointedSpatial_eq_three
    [Fact (Module.finrank ℝ E = 4)]
    (u : E) (hu : inner ℝ u u = 1) :
    Module.finrank ℝ (ℝ ∙ u)ᗮ = 3 := by
  exact Submodule.finrank_orthogonal_span_singleton
    (ne_zero_of_inner_self_eq_one u hu)

/-- Coordinates adapted to the pointing direction have the expected scalar component. -/
theorem pointedTime_smul_add_of_orthogonal
    (u X : E) (a : ℝ)
    (hu : inner ℝ u u = 1)
    (hX : inner ℝ u X = 0) :
    pointedTime u (a • u + X) = a := by
  unfold pointedTime
  rw [inner_add_right, inner_smul_right, hu, hX]
  simp

/-- Coordinates adapted to the pointing direction have the expected spatial component. -/
theorem pointedSpace_smul_add_of_orthogonal
    (u X : E) (a : ℝ)
    (hu : inner ℝ u u = 1)
    (hX : inner ℝ u X = 0) :
    pointedSpace u (a • u + X) = X := by
  rw [pointedSpace, pointedTime_smul_add_of_orthogonal u X a hu hX]
  module

/-- The pointed quadratic is exactly one positive scalar square minus the Euclidean spatial
square. -/
theorem pointedLorentzQuadratic_smul_add_of_orthogonal
    (u X : E) (a : ℝ)
    (hu : inner ℝ u u = 1)
    (hX : inner ℝ u X = 0) :
    pointedLorentzQuadratic u (a • u + X) =
      a ^ 2 - inner ℝ X X := by
  simp [pointedLorentzQuadratic,
    pointedTime_smul_add_of_orthogonal u X a hu hX,
    pointedSpace_smul_add_of_orthogonal u X a hu hX]

/-- The distinguished axis is positive for the pointed Lorentz quadratic. -/
theorem pointedLorentzQuadratic_smul_axis
    (u : E) (a : ℝ) (hu : inner ℝ u u = 1) :
    pointedLorentzQuadratic u (a • u) = a ^ 2 := by
  simpa using pointedLorentzQuadratic_smul_add_of_orthogonal
    u (0 : E) a hu (by simp)

/-- Every vector orthogonal to the pointing direction is nonpositive for the pointed Lorentz
quadratic. -/
theorem pointedLorentzQuadratic_spatial_nonpos
    (u X : E) (hX : inner ℝ u X = 0) :
    pointedLorentzQuadratic u X ≤ 0 := by
  change
    (inner ℝ u X) ^ 2 -
      inner ℝ (X - inner ℝ u X • u) (X - inner ℝ u X • u) ≤ 0
  rw [hX]
  simp only [zero_smul, sub_zero, zero_pow (by norm_num : 2 ≠ 0), zero_sub]
  exact neg_nonpos.mpr (real_inner_self_nonneg : 0 ≤ inner ℝ X X)

/-- Abstract carrier of a real spin factor. -/
abbrev RealSpinFactor (E : Type*) := ℝ × E

/-- Spin-factor Jordan product. -/
def realSpinFactorMul
    (x y : RealSpinFactor E) : RealSpinFactor E :=
  (x.1 * y.1 + inner ℝ x.2 y.2,
    x.1 • y.2 + y.1 • x.2)

/-- Unit of the spin-factor product. -/
def realSpinFactorOne : RealSpinFactor E :=
  (1, 0)

/-- Determinant of a real spin factor. -/
def realSpinFactorDet (x : RealSpinFactor E) : ℝ :=
  x.1 ^ 2 - inner ℝ x.2 x.2

/-- The spin-factor product is commutative. -/
theorem realSpinFactorMul_comm (x y : RealSpinFactor E) :
    realSpinFactorMul x y = realSpinFactorMul y x := by
  ext
  · simp [realSpinFactorMul, real_inner_comm, mul_comm]
  · simp [realSpinFactorMul, add_comm]

/-- The pointed element `(1,0)` is a left unit. -/
theorem realSpinFactorOne_mul (x : RealSpinFactor E) :
    realSpinFactorMul (realSpinFactorOne (E := E)) x = x := by
  ext <;> simp [realSpinFactorMul, realSpinFactorOne]

/-- The pointed element `(1,0)` is a right unit. -/
theorem realSpinFactorMul_one (x : RealSpinFactor E) :
    realSpinFactorMul x (realSpinFactorOne (E := E)) = x := by
  rw [realSpinFactorMul_comm, realSpinFactorOne_mul]

/-- The spin-factor product obeys the Jordan identity. -/
theorem realSpinFactorMul_jordan
    (x y : RealSpinFactor E) :
    realSpinFactorMul (realSpinFactorMul x x) (realSpinFactorMul x y) =
      realSpinFactorMul x (realSpinFactorMul (realSpinFactorMul x x) y) := by
  rcases x with ⟨a, u⟩
  rcases y with ⟨b, v⟩
  apply Prod.ext
  · simp only [realSpinFactorMul, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    rw [real_inner_comm v u]
    ring
  · simp only [realSpinFactorMul, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    rw [real_inner_comm v u]
    module

end GaloisForLFunctions.HTGeometry

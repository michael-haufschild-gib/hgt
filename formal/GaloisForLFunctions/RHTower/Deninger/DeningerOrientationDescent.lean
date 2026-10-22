import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Group.Invertible.Basic

/-!
# Orientation descent along an involution

The invariant and anti-invariant summands of an involution are complementary once `2` is
invertible: their intersection is zero because a vector fixed and negated by the involution is
its own negative, and they span because `v = (v + Cv)/2 + (v - Cv)/2`.

This is what makes descent along the oriented double cover faithful: a class whose invariant and
anti-invariant parts both vanish is zero.

* `deningerOrientationInvariant`, `deningerOrientationAntiInvariant` : the two summands.
* `deningerOrientation_isCompl` : the decomposition is direct.
* `deningerOrientation_eq_zero_of_parts` : faithfulness of the descent.
-/

namespace RHTower

section OrientationDescent

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Invertible (2 : R)]

/-- The orientation-invariant summand. -/
def deningerOrientationInvariant (C : V →ₗ[R] V) : Submodule R V :=
  LinearMap.ker (C - LinearMap.id)

/-- The orientation-anti-invariant summand. -/
def deningerOrientationAntiInvariant (C : V →ₗ[R] V) : Submodule R V :=
  LinearMap.ker (C + LinearMap.id)

omit [Invertible (2 : R)] in
theorem mem_deningerOrientationInvariant {C : V →ₗ[R] V} {v : V} :
    v ∈ deningerOrientationInvariant C ↔ C v = v := by
  rw [deningerOrientationInvariant, LinearMap.mem_ker]
  constructor
  · intro h
    have hz : C v - v = 0 := by simpa using h
    exact sub_eq_zero.mp hz
  · intro h
    simp [h]

omit [Invertible (2 : R)] in
theorem mem_deningerOrientationAntiInvariant {C : V →ₗ[R] V} {v : V} :
    v ∈ deningerOrientationAntiInvariant C ↔ C v = -v := by
  rw [deningerOrientationAntiInvariant, LinearMap.mem_ker]
  constructor
  · intro h
    have hz : C v + v = 0 := by simpa using h
    exact eq_neg_of_add_eq_zero_left hz
  · intro h
    simp [h]

/-- **Faithfulness of the descent.**  A vector whose invariant and anti-invariant parts both
vanish is zero. -/
theorem deningerOrientation_eq_zero_of_parts (C : V →ₗ[R] V) {v : V}
    (hinv : v + C v = 0) (hanti : v - C v = 0) : v = 0 := by
  have hsum : (2 : R) • v = 0 := by
    have h : (v + C v) + (v - C v) = 0 := by rw [hinv, hanti, add_zero]
    have h2 : (v + C v) + (v - C v) = (2 : R) • v := by
      rw [two_smul]
      abel
    rw [h2] at h
    exact h
  have := congrArg (fun w => (⅟(2 : R)) • w) hsum
  simpa [smul_smul, invOf_mul_self] using this

/-- **The decomposition is direct.** -/
theorem deningerOrientation_isCompl (C : V →ₗ[R] V) (hC : ∀ v, C (C v) = v) :
    IsCompl (deningerOrientationInvariant C) (deningerOrientationAntiInvariant C) := by
  constructor
  · rw [disjoint_iff_inf_le]
    intro v hv
    have h1 : C v = v := mem_deningerOrientationInvariant.mp hv.1
    have h2 : C v = -v := mem_deningerOrientationAntiInvariant.mp hv.2
    refine deningerOrientation_eq_zero_of_parts C ?_ ?_
    · rw [h2]
      abel
    · rw [h1]
      abel
  · rw [codisjoint_iff_le_sup]
    intro v _
    have hplus : (⅟(2 : R)) • (v + C v) ∈ deningerOrientationInvariant C := by
      rw [mem_deningerOrientationInvariant, map_smul, map_add, hC]
      rw [add_comm]
    have hminus : (⅟(2 : R)) • (v - C v) ∈ deningerOrientationAntiInvariant C := by
      rw [mem_deningerOrientationAntiInvariant, map_smul, map_sub, hC, ← smul_neg]
      congr 1
      abel
    have hsplit : v = (⅟(2 : R)) • (v + C v) + (⅟(2 : R)) • (v - C v) := by
      rw [← smul_add]
      have hadd : (v + C v) + (v - C v) = (2 : R) • v := by
        rw [two_smul]
        abel
      rw [hadd, smul_smul, invOf_mul_self, one_smul]
    rw [hsplit]
    exact Submodule.add_mem_sup hplus hminus

end OrientationDescent

end RHTower

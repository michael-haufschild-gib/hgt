/-
# Signed permutations of coordinates are linear isometries

A signed permutation `x ↦ (i ↦ ε i · x_{π i})` with `ε i = ±1` is an orthogonal map of Euclidean
space: it is linear, its explicit inverse is the signed permutation of the inverse permutation, and
it preserves the norm because squaring kills the signs and the permutation only reindexes the sum.
This is the group under which the fixed-shell Pauli ensemble is invariant.

Main results:
* `signedPermLinearEquiv` — the signed permutation as a linear equivalence.
* `signedPermIsometry` — **the signed permutation as a linear isometry**.
-/
import Mathlib

open Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The signed permutation of coordinates, as a linear equivalence of Euclidean space. -/
def signedPermLinearEquiv (π : Equiv.Perm ι) {ε : ι → ℝ} (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun x := (WithLp.toLp 2 fun i => ε i * (WithLp.ofLp x) (π i))
  map_add' x y := by
    ext i
    simp [mul_add]
  map_smul' c x := by
    ext i
    simp [mul_left_comm]
  invFun y := (WithLp.toLp 2 fun j => ε (π.symm j) * (WithLp.ofLp y) (π.symm j))
  left_inv x := by
    ext j
    have hsq : ε (π.symm j) * ε (π.symm j) = 1 := by
      rcases hε (π.symm j) with h | h <;> rw [h] <;> norm_num
    show ε (π.symm j) * (ε (π.symm j) * (WithLp.ofLp x) (π (π.symm j))) = (WithLp.ofLp x) j
    rw [← mul_assoc, hsq, one_mul, Equiv.apply_symm_apply]
  right_inv y := by
    ext i
    have hsq : ε i * ε i = 1 := by
      rcases hε i with h | h <;> rw [h] <;> norm_num
    show ε i * (ε (π.symm (π i)) * (WithLp.ofLp y) (π.symm (π i))) = (WithLp.ofLp y) i
    rw [Equiv.symm_apply_apply, ← mul_assoc, hsq, one_mul]

omit [Fintype ι] in
theorem coe_signedPermLinearEquiv (π : Equiv.Perm ι) {ε : ι → ℝ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (x : EuclideanSpace ℝ ι) (i : ι) :
    (WithLp.ofLp (signedPermLinearEquiv π hε x)) i = ε i * (WithLp.ofLp x) (π i) := rfl

/-- **The signed permutation is a linear isometry of Euclidean space.** -/
def signedPermIsometry (π : Equiv.Perm ι) {ε : ι → ℝ} (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι where
  toLinearEquiv := signedPermLinearEquiv π hε
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    have hterm : ∀ i : ι,
        ‖(WithLp.ofLp (signedPermLinearEquiv π hε x)) i‖ ^ (2 : ℕ)
          = ‖(WithLp.ofLp x) (π i)‖ ^ (2 : ℕ) := by
      intro i
      rw [coe_signedPermLinearEquiv, norm_mul]
      have hone : ‖ε i‖ = 1 := by
        rcases hε i with h | h <;> rw [h] <;> norm_num
      rw [hone, one_mul]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    exact Equiv.sum_comp π fun j => ‖(WithLp.ofLp x) j‖ ^ (2 : ℕ)

theorem coe_signedPermIsometry (π : Equiv.Perm ι) {ε : ι → ℝ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (x : EuclideanSpace ℝ ι) (i : ι) :
    (WithLp.ofLp (signedPermIsometry π hε x)) i = ε i * (WithLp.ofLp x) (π i) := rfl

end

end GaloisForLFunctions.HTGeometry

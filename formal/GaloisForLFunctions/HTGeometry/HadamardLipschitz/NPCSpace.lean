/-
# Metric spaces of non-positive curvature (Hadamard / NPC spaces)

This module introduces the metric backbone used by the `HadamardLipschitz` family of modules:
a geodesic metric space satisfying the Bruhat–Tits / Alexandrov *NPC inequality*

```
d(x #_t y, z)^2 ≤ (1-t) d(x,z)^2 + t d(y,z)^2 - t(1-t) d(x,y)^2 .
```

Complete spaces with this property are exactly the *Hadamard spaces* (CAT(0) spaces); every
Hadamard manifold is one.  Working at this level of generality means that all the
1-Lipschitz-network results proved downstream hold for Hadamard manifolds, but also for trees,
Hilbert spaces and Hadamard spaces with singularities.

The two facts proved here beyond the axioms are

* `NPCSpace.eq_gd_of_dist` — geodesics are unique: a point at the right pair of distances from
  the endpoints *is* the interpolation point;
* `NPCSpace.dist_sq_le_of_between` — consequently the NPC inequality can be applied to any
  point known only through its distances to the endpoints.

Non-vacuity: every real inner-product space is an `NPCSpace` (`InnerProductSpace.toNPCSpace`),
with the NPC inequality holding as an identity.
-/
import Mathlib.Analysis.InnerProductSpace.Basic

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

open scoped RealInnerProductSpace

/-- A metric space of non-positive curvature in the sense of Bruhat–Tits.

`gd x y t` is the point at proportion `t` along the geodesic from `x` to `y`, written `x #_t y`
in the literature.  The three axioms say that `gd x y ·` parametrises a geodesic from `x` to `y`
proportionally to arclength, and that the squared distance to any point is *uniformly* convex
along it. -/
class NPCSpace (X : Type*) [MetricSpace X] where
  /-- The point at proportion `t` along the geodesic from `x` to `y`. -/
  gd : X → X → ℝ → X
  /-- `gd x y t` is at distance `t * d(x,y)` from `x`. -/
  dist_gd_left (x y : X) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    dist x (gd x y t) = t * dist x y
  /-- `gd x y t` is at distance `(1-t) * d(x,y)` from `y`. -/
  dist_gd_right (x y : X) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    dist (gd x y t) y = (1 - t) * dist x y
  /-- The NPC (Bruhat–Tits) inequality. -/
  dist_gd_sq_le (x y z : X) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    dist (gd x y t) z ^ 2 ≤
      (1 - t) * dist x z ^ 2 + t * dist y z ^ 2 - t * (1 - t) * dist x y ^ 2

namespace NPCSpace

variable {X : Type*} [MetricSpace X] [NPCSpace X]

@[simp] theorem gd_zero (x y : X) : gd x y 0 = x := by
  have h := dist_gd_left x y 0 le_rfl zero_le_one
  simp only [zero_mul] at h
  exact (dist_eq_zero.mp h).symm

@[simp] theorem gd_one (x y : X) : gd x y 1 = y := by
  have h := dist_gd_right x y 1 zero_le_one le_rfl
  simp only [sub_self, zero_mul] at h
  exact dist_eq_zero.mp h

/-- **Uniqueness of geodesics.**  A point at distance `t·d(x,q)` from `x` and `(1-t)·d(x,q)`
from `q` is the geodesic interpolation point. -/
theorem eq_gd_of_dist (x q p : X) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (h1 : dist x p = t * dist x q) (h2 : dist p q = (1 - t) * dist x q) :
    p = gd x q t := by
  have h := dist_gd_sq_le x q p t ht₀ ht₁
  have hqp : dist q p = (1 - t) * dist x q := by rw [dist_comm]; exact h2
  rw [h1, hqp] at h
  have hzero : (1 - t) * (t * dist x q) ^ 2 + t * ((1 - t) * dist x q) ^ 2
      - t * (1 - t) * dist x q ^ 2 = 0 := by ring
  rw [hzero] at h
  have : dist (gd x q t) p = 0 := by
    have hnn : 0 ≤ dist (gd x q t) p := dist_nonneg
    nlinarith [h, hnn]
  exact (dist_eq_zero.mp this).symm

/-- The NPC inequality, stated for a point `p` specified only by its distances to the two
endpoints of the geodesic. -/
theorem dist_sq_le_of_between (x q p z : X) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (h1 : dist x p = t * dist x q) (h2 : dist p q = (1 - t) * dist x q) :
    dist p z ^ 2 ≤ (1 - t) * dist x z ^ 2 + t * dist q z ^ 2 - t * (1 - t) * dist x q ^ 2 := by
  rw [eq_gd_of_dist x q p t ht₀ ht₁ h1 h2]
  exact dist_gd_sq_le x q z t ht₀ ht₁

end NPCSpace

/-- **Non-vacuity.** Every real inner-product space is an NPC space; there the NPC inequality
is an identity (the parallelogram law in disguise). -/
instance (priority := 100) InnerProductSpace.toNPCSpace
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : NPCSpace E where
  gd x y t := (1 - t) • x + t • y
  dist_gd_left x y t ht₀ _ := by
    have hx : x - ((1 - t) • x + t • y) = t • (x - y) := by module
    rw [dist_eq_norm, dist_eq_norm, hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht₀]
  dist_gd_right x y t _ ht₁ := by
    have hx : (1 - t) • x + t • y - y = (1 - t) • (x - y) := by module
    rw [dist_eq_norm, dist_eq_norm, hx, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)]
  dist_gd_sq_le x y z t _ _ := by
    have key : ∀ a b : E, ‖(1 - t) • a + t • b‖ ^ 2
        = (1 - t) * ‖a‖ ^ 2 + t * ‖b‖ ^ 2 - t * (1 - t) * ‖a - b‖ ^ 2 := by
      intro a b
      rw [norm_add_sq_real, norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right,
        norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    have hx : (1 - t) • x + t • y - z = (1 - t) • (x - z) + t • (y - z) := by module
    have hxy : (x - z) - (y - z) = x - y := by abel
    simp only [dist_eq_norm, hx]
    rw [key (x - z) (y - z), hxy]

end GaloisForLFunctions.HTGeometry.HadamardLipschitz

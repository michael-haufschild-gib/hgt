import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# The inner product induced by a positive symmetric operator

A positive symmetric operator `T` on a real inner product space induces the bilinear form
`⟪u, v⟫_T = ⟪T u, v⟫`.  It is symmetric, bilinear and positive semidefinite, so it satisfies the
Cauchy–Schwarz inequality — proved here from the discriminant of the nonnegative quadratic
`t ↦ ⟪u + t v, u + t v⟫_T`, which needs no completeness or definiteness.

The identity that makes such a form useful against a resolvent is that solving `T v = e` collapses
the `T`-pairing of `v` to the plain pairing of `e`: the operator disappears from the left slot.  In
particular the `T`-pairings of solutions of `T v_z = e_z` are computed by the plain pairings of the
right-hand sides, with no reference to `T` at all.
-/

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The bilinear form induced by an operator: `⟪u, v⟫_T = ⟪T u, v⟫`. -/
def tInner (T : E →ₗ[ℝ] E) (u v : E) : ℝ := inner ℝ (T u) v

theorem tInner_def (T : E →ₗ[ℝ] E) (u v : E) : tInner T u v = inner ℝ (T u) v := rfl

/-- **The boundary-form identity.**  Solving `T v = e` removes the operator from the pairing: the
`T`-inner product of `v` against anything is the plain inner product of `e` against it. -/
theorem tInner_eq_inner_of_apply {T : E →ₗ[ℝ] E} {v e : E} (h : T v = e) (w : E) :
    tInner T v w = inner ℝ e w := by
  rw [tInner_def, h]

/-- A symmetric operator induces a symmetric form. -/
theorem tInner_comm {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (u v : E) :
    tInner T u v = tInner T v u := by
  rw [tInner_def, tInner_def, hT u v, real_inner_comm]

theorem tInner_add_left (T : E →ₗ[ℝ] E) (u v w : E) :
    tInner T (u + v) w = tInner T u w + tInner T v w := by
  rw [tInner_def, tInner_def, tInner_def, map_add, inner_add_left]

theorem tInner_smul_left (T : E →ₗ[ℝ] E) (c : ℝ) (u v : E) :
    tInner T (c • u) v = c * tInner T u v := by
  rw [tInner_def, tInner_def, map_smul, real_inner_smul_left]

theorem tInner_add_right {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (u v w : E) :
    tInner T u (v + w) = tInner T u v + tInner T u w := by
  rw [tInner_comm hT u (v + w), tInner_add_left, tInner_comm hT v u, tInner_comm hT w u]

theorem tInner_smul_right {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (c : ℝ) (u v : E) :
    tInner T u (c • v) = c * tInner T u v := by
  rw [tInner_comm hT u (c • v), tInner_smul_left, tInner_comm hT v u]

/-- The quadratic expansion along a line, the input of the Cauchy–Schwarz argument. -/
theorem tInner_self_add_smul {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (u v : E) (t : ℝ) :
    tInner T (u + t • v) (u + t • v)
      = tInner T v v * t ^ 2 + 2 * tInner T u v * t + tInner T u u := by
  rw [tInner_add_left, tInner_add_right hT, tInner_add_right hT, tInner_smul_left,
    tInner_smul_right hT, tInner_smul_right hT, tInner_comm hT v u]
  ring

/-- **Cauchy–Schwarz for the induced form.**  Positivity of the quadratic along every line forces its
discriminant to be nonpositive.  No definiteness or completeness is used. -/
theorem tInner_sq_le_of_nonneg {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hpos : ∀ w : E, 0 ≤ tInner T w w) (u v : E) :
    (tInner T u v) ^ 2 ≤ tInner T u u * tInner T v v := by
  have hquad : ∀ t : ℝ,
      0 ≤ tInner T v v * t ^ 2 + 2 * tInner T u v * t + tInner T u u := by
    intro t
    rw [← tInner_self_add_smul hT u v t]
    exact hpos _
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- The induced form vanishes on the kernel of the operator. -/
theorem tInner_eq_zero_of_apply_eq_zero {T : E →ₗ[ℝ] E} {v : E} (h : T v = 0) (w : E) :
    tInner T v w = 0 := by
  rw [tInner_eq_inner_of_apply h, inner_zero_left]

end GaloisForLFunctions.HTGeometry

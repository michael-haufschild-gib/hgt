import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The unit normal to a subspace through a point outside it

For a submodule `K` of an inner product space that admits an orthogonal projection and a vector
`v ∉ K`, the normalized residual

  `ψ = ‖v - P v‖⁻¹ • (v - P v)`

is a unit vector orthogonal to `K` with `⟪ψ, v⟫ = ‖v - P v‖ = dist(v, K) > 0`.

This is the invariant `d` of the fixed-tail obstruction: the component of the critical arithmetic
profile that the fixed tail space cannot absorb. It is packaged here abstractly because the
statement is independent of the function space used.
-/

noncomputable section
open Submodule

namespace RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The distance from `v` to `K`, realised as the norm of the orthogonal residual. -/
def orthoDefect (K : Submodule ℂ E) [K.HasOrthogonalProjection] (v : E) : ℝ :=
  ‖v - K.starProjection v‖

theorem orthoDefect_pos {K : Submodule ℂ E} [K.HasOrthogonalProjection] {v : E}
    (hv : v ∉ K) : 0 < orthoDefect K v := by
  rw [orthoDefect, norm_pos_iff, sub_ne_zero]
  intro h
  exact hv (K.starProjection_eq_self_iff.mp h.symm)

/-- The unit normal: the normalized orthogonal residual of `v` against `K`. -/
def unitNormal (K : Submodule ℂ E) [K.HasOrthogonalProjection] (v : E) : E :=
  ((orthoDefect K v : ℂ)⁻¹) • (v - K.starProjection v)

theorem norm_unitNormal {K : Submodule ℂ E} [K.HasOrthogonalProjection] {v : E}
    (hv : v ∉ K) : ‖unitNormal K v‖ = 1 := by
  have hd : 0 < orthoDefect K v := orthoDefect_pos hv
  rw [unitNormal, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hd]
  rw [← orthoDefect]
  exact inv_mul_cancel₀ (ne_of_gt hd)

theorem unitNormal_inner_eq_zero {K : Submodule ℂ E} [K.HasOrthogonalProjection] (v : E)
    {w : E} (hw : w ∈ K) : (inner ℂ (unitNormal K v) w : ℂ) = 0 := by
  rw [unitNormal, inner_smul_left, K.starProjection_inner_eq_zero v w hw, mul_zero]

theorem inner_unitNormal_self {K : Submodule ℂ E} [K.HasOrthogonalProjection] {v : E}
    (hv : v ∉ K) : (inner ℂ (unitNormal K v) v : ℂ) = ((orthoDefect K v : ℝ) : ℂ) := by
  have hd : 0 < orthoDefect K v := orthoDefect_pos hv
  have hdne : ((orthoDefect K v : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hd)
  have hperp : (inner ℂ (v - K.starProjection v) (K.starProjection v) : ℂ) = 0 :=
    K.starProjection_inner_eq_zero v _ (K.starProjection_apply_mem v)
  have hself : (inner ℂ (v - K.starProjection v) (v - K.starProjection v) : ℂ)
      = ((orthoDefect K v : ℝ) : ℂ) ^ (2 : ℕ) := by
    rw [inner_self_eq_norm_sq_to_K, orthoDefect]
    rfl
  have hkey : (inner ℂ (v - K.starProjection v) v : ℂ)
      = ((orthoDefect K v : ℝ) : ℂ) ^ (2 : ℕ) := by
    have h1 : (inner ℂ (v - K.starProjection v) v : ℂ)
        = (inner ℂ (v - K.starProjection v) (v - K.starProjection v) : ℂ)
          + (inner ℂ (v - K.starProjection v) (K.starProjection v) : ℂ) := by
      rw [← inner_add_right]
      congr 1
      abel
    rw [h1, hperp, add_zero, hself]
  rw [unitNormal, inner_smul_left, map_inv₀, Complex.conj_ofReal, hkey, pow_two,
    ← mul_assoc, inv_mul_cancel₀ hdne, one_mul]

/-- **The unit normal package.** -/
theorem exists_unitNormal {K : Submodule ℂ E} [K.HasOrthogonalProjection] {v : E}
    (hv : v ∉ K) :
    ∃ ψ : E, ‖ψ‖ = 1 ∧ (∀ w ∈ K, (inner ℂ ψ w : ℂ) = 0) ∧
      (inner ℂ ψ v : ℂ) = ((orthoDefect K v : ℝ) : ℂ) ∧ 0 < orthoDefect K v :=
  ⟨unitNormal K v, norm_unitNormal hv, fun _w hw => unitNormal_inner_eq_zero v hw,
    inner_unitNormal_self hv, orthoDefect_pos hv⟩

end RHTower

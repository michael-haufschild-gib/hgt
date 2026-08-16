import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Differentiating a self-adjoint quadratic form along a path

For a self-adjoint operator the two cross terms in the derivative of `t ↦ ⟪v t, R (v t)⟫` coincide,
so the derivative is twice a single pairing:

`d/dt ⟪v t, R (v t)⟫ = 2 ⟪v'(t), R (v t)⟫`.

That is the differentiation step behind a torque identity: once the velocity of the path is
expressed through an operator acting on the path itself, the derivative of the norm becomes a
matrix element of a commutator, and the algebraic half of that passage is the conjugation identity
`X R − R X = R (X T − T X) R` for `R` inverting `T`.
-/

namespace GaloisForLFunctions.HTGeometry

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A self-adjoint operator moves between the two slots of a real inner product. -/
theorem inner_selfAdjoint_swap {R : H →L[ℝ] H} (hR : ContinuousLinearMap.adjoint R = R) (x y : H) :
    inner ℝ x (R y) = inner ℝ y (R x) := by
  have h : inner ℝ x (R y) = inner ℝ (R x) y := by
    rw [← hR, ContinuousLinearMap.adjoint_inner_right, hR]
  rw [h, real_inner_comm]

/-- **The derivative of a self-adjoint quadratic form.**  Both cross terms agree, so the derivative
is twice the pairing of the velocity against the transformed position. -/
theorem hasDerivAt_selfAdjoint_quadratic {v : ℝ → H} {v' : H} {x : ℝ}
    (hv : HasDerivAt v v' x) {R : H →L[ℝ] H} (hR : ContinuousLinearMap.adjoint R = R) :
    HasDerivAt (fun t : ℝ => inner ℝ (v t) (R (v t))) (2 * inner ℝ v' (R (v x))) x := by
  have hRv : HasDerivAt (fun t : ℝ => R (v t)) (R v') x :=
    R.hasFDerivAt.comp_hasDerivAt x hv
  have h := HasDerivAt.inner (𝕜 := ℝ) hv hRv
  have hswap : inner ℝ (v x) (R v') = inner ℝ v' (R (v x)) := inner_selfAdjoint_swap hR _ _
  rw [hswap] at h
  have hval : inner ℝ v' (R (v x)) + inner ℝ v' (R (v x))
      = 2 * inner ℝ v' (R (v x)) := by ring
  rwa [hval] at h

/-- The derivative of the squared norm along a path is twice the pairing with the velocity: the
case `R = 1`. -/
theorem hasDerivAt_norm_sq_along {v : ℝ → H} {v' : H} {x : ℝ} (hv : HasDerivAt v v' x) :
    HasDerivAt (fun t : ℝ => ‖v t‖ ^ 2) (2 * inner ℝ v' (v x)) x := by
  have hone : ContinuousLinearMap.adjoint (1 : H →L[ℝ] H) = 1 := by
    simp
  have h := hasDerivAt_selfAdjoint_quadratic hv hone
  simpa [real_inner_self_eq_norm_sq] using h

end GaloisForLFunctions.HTGeometry

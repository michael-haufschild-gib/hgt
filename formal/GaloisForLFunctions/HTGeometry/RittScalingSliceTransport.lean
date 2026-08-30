import GaloisForLFunctions.HTGeometry.RittScalingCoboundaryDescent
import GaloisForLFunctions.HTGeometry.RittShiftRigidity

/-!
# The inhomogeneous descent, read inside an ambient field

A shift `σ` of an ambient field which restricts to `φ` on a coefficient field and scales a
transcendental generator, `σ t = μ · t`, evaluates the twisted scaling substitution: for every
polynomial `p` over the coefficients,

`σ (p(t)) = (twistComp φ (μ·X) p)(t)`.

Transcendence of `t` makes evaluation injective, so an inhomogeneous shift relation for a fraction
`P(t)/Q(t)` with `P`, `Q` coprime and `Q` monic is exactly the polynomial cross identity of
`RittScalingCoboundaryDescent`, and the descent applies verbatim.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {E L : Type*} [Field E] [Field L] [Algebra E L]

/-- Evaluation intertwines the shift with the twisted scaling substitution. -/
theorem aeval_twistComp_scale (σ : L →+* L) (φ : E →+* E)
    (hcomp : ∀ a : E, σ (algebraMap E L a) = algebraMap E L (φ a))
    {t : L} {μ : E} (hσt : σ t = algebraMap E L μ * t) (p : E[X]) :
    aeval t (twistComp φ (C μ * X) p) = σ (aeval t p) := by
  rw [twistComp, aeval_comp]
  have hval : aeval t (C μ * X : E[X]) = σ t := by
    rw [hσt]; simp
  rw [hval, aeval_shift_map σ φ hcomp t p]

/-- **The inhomogeneous descent inside an ambient field.**  A coprime fraction of a transcendental
generator solving `σ W = W + β·t` produces a solution of `φ(a)·μ = a + β` in the coefficient
field. -/
theorem exists_shift_solution_of_transcendental (σ : L →+* L) (φ : E →+* E)
    (hcomp : ∀ a : E, σ (algebraMap E L a) = algebraMap E L (φ a))
    {t : L} (ht : Transcendental E t) {μ β : E} (hμ : μ ≠ 0)
    (hσt : σ t = algebraMap E L μ * t)
    {P Q : E[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hrel : σ (aeval t P / aeval t Q)
      = aeval t P / aeval t Q + algebraMap E L β * t) :
    ∃ a : E, φ a * μ = a + β := by
  classical
  have hinj : Function.Injective (aeval t : E[X] →ₐ[E] L) :=
    (transcendental_iff_injective).mp ht
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hQt : aeval t Q ≠ 0 := by
    intro h
    exact hQ0 (hinj (by simpa using h))
  have htw : aeval t (twistComp φ (C μ * X) Q) ≠ 0 := by
    intro h
    exact (twistComp_ne_zero φ (natDegree_scaleSubst hμ) hQ0) (hinj (by simpa using h))
  refine exists_shift_solution_of_scaling_cross φ hμ hQ hcop (hinj ?_)
  have hσP := aeval_twistComp_scale σ φ hcomp hσt P
  have hσQ := aeval_twistComp_scale σ φ hcomp hσt Q
  rw [map_div₀, ← hσP, ← hσQ] at hrel
  rw [map_mul, map_mul, map_add, map_mul, map_mul, aeval_C, aeval_X]
  rw [div_add' _ _ _ hQt, div_eq_div_iff htw hQt] at hrel
  linear_combination hrel

end GaloisForLFunctions.HTGeometry

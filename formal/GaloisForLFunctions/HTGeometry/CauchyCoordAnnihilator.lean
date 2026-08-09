import GaloisForLFunctions.HTGeometry.HalfPlaneRungeClosure

/-!
# A functional killing every power of the Cauchy coordinate kills every holomorphic function

The consumer form of Runge on the half-plane.  A continuous functional annihilating all powers of
`z ↦ (z + a)⁻¹` annihilates the whole algebra they generate, hence — its kernel being closed — the
compact-open closure of that algebra, which by Runge contains every holomorphic function.

Linearity alone suffices for the first step, because every element of the generated algebra is a
polynomial in the generator, i.e. a finite linear combination of its powers; the functional is not
assumed multiplicative.

* `HTGeometry.eq_zero_of_forall_pow_cauchyCoord`.
-/

namespace HTGeometry

/-- **A functional vanishing on all powers of the Cauchy coordinate vanishes on all holomorphic
functions.** -/
theorem eq_zero_of_forall_pow_cauchyCoord {a : ℝ} (ha : 0 < a)
    (L : C((rightHalfPlane : Set ℂ), ℂ) →L[ℂ] ℂ)
    (hL : ∀ n : ℕ, L ((cauchyCoord a ha) ^ n) = 0) :
    ∀ f ∈ holoAlgebra, L f = 0 := by
  classical
  set r : C((rightHalfPlane : Set ℂ), ℂ) := cauchyCoord a ha with hr
  set S : Subalgebra ℂ C((rightHalfPlane : Set ℂ), ℂ) :=
    Algebra.adjoin ℂ ({r} : Set C((rightHalfPlane : Set ℂ), ℂ)) with hS
  -- the functional kills the generated algebra, by linearity through polynomials
  have hgen : ∀ x ∈ S, L x = 0 := by
    intro x hx
    rw [hS, Algebra.adjoin_singleton_eq_range_aeval] at hx
    obtain ⟨p, hp⟩ := hx
    have hexp : (Polynomial.aeval r) p
        = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • r ^ i :=
      Polynomial.aeval_eq_sum_range (x := r) (p := p)
    have hval : L ((Polynomial.aeval r) p) = 0 := by
      rw [hexp, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, hL i, smul_zero]
    rw [← hp]
    exact hval
  -- the kernel is closed, so it contains the closure
  have hker : IsClosed {x : C((rightHalfPlane : Set ℂ), ℂ) | L x = 0} := by
    have hpre : IsClosed ((L : C((rightHalfPlane : Set ℂ), ℂ) → ℂ) ⁻¹' {0}) :=
      (isClosed_singleton (x := (0 : ℂ))).preimage L.continuous
    exact hpre
  have hclos : closure (S : Set C((rightHalfPlane : Set ℂ), ℂ))
      ⊆ {x : C((rightHalfPlane : Set ℂ), ℂ) | L x = 0} :=
    closure_minimal hgen hker
  intro f hf
  have hmem := holo_mem_topologicalClosure_adjoin_cauchyCoord ha f hf
  rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe] at hmem
  exact hclos hmem

end HTGeometry

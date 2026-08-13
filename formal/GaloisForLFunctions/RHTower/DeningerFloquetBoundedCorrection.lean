import GaloisForLFunctions.RHTower.DeningerFloquetPoissonCompleteness

/-!
# The bounded-correction no-go

A bounded operator on the Floquet completion that annihilates every Poisson boundary annihilates
the whole closed boundary space, which is the annihilator of the resonant nodes.  Hence it is its
own composition with the orthogonal projection onto the resonance subspace, and it is determined by
its values on the resonant node indicators.  No bounded correction can see a nonresonant mode.

* `deningerFloquetBoundedCorrection_vanishing` : it kills the whole annihilator.
* `deningerFloquetBoundedCorrection_factors` : **it factors through the resonance projection.**
* `deningerFloquetBoundedCorrection_unique` : **the factorization is unique.**
-/

namespace RHTower

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace

noncomputable section

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- **A bounded operator killing every Poisson boundary vanishes on the whole annihilator of the
resonant nodes.** -/
theorem deningerFloquetBoundedCorrection_vanishing
    (A : Lp ℂ 2 deningerFloquetMeasure →L[ℂ] Y)
    (hA : ∀ f : DeningerMeyerCap, A (deningerFloquetLp (deningerPoissonSource f)) = 0)
    {x : Lp ℂ 2 deningerFloquetMeasure} (hx : x ∈ deningerFloquetResonanceSpanᗮ) : A x = 0 := by
  have hker : deningerFloquetBoundary
      ≤ LinearMap.ker (A : Lp ℂ 2 deningerFloquetMeasure →ₗ[ℂ] Y) := by
    refine Submodule.span_le.2 ?_
    rintro u ⟨f, rfl⟩
    exact hA f
  have hclosed : deningerFloquetBoundary.topologicalClosure
      ≤ LinearMap.ker (A : Lp ℂ 2 deningerFloquetMeasure →ₗ[ℂ] Y) :=
    Submodule.topologicalClosure_minimal _ hker A.isClosed_ker
  rw [deningerFloquetBoundary_topologicalClosure] at hclosed
  exact hclosed hx

/-- **The bounded-correction no-go.**  Every bounded operator annihilating the Poisson boundaries
equals its composition with the orthogonal projection onto the resonance subspace: it factors
through the resonance-only quotient. -/
theorem deningerFloquetBoundedCorrection_factors
    (A : Lp ℂ 2 deningerFloquetMeasure →L[ℂ] Y)
    (hA : ∀ f : DeningerMeyerCap, A (deningerFloquetLp (deningerPoissonSource f)) = 0)
    (x : Lp ℂ 2 deningerFloquetMeasure) :
    A x = A (deningerFloquetResonanceSpan.topologicalClosure.starProjection x) := by
  have hsub : x - deningerFloquetResonanceSpan.topologicalClosure.starProjection x
      ∈ deningerFloquetResonanceSpanᗮ :=
    Submodule.orthogonal_le deningerFloquetResonanceSpan.le_topologicalClosure
      (Submodule.sub_starProjection_mem_orthogonal x)
  have hzero := deningerFloquetBoundedCorrection_vanishing A hA hsub
  rw [map_sub] at hzero
  exact sub_eq_zero.1 hzero

/-- **The factorization is unique.**  A bounded operator annihilating the Poisson boundaries is
determined by its values on the resonant node indicators. -/
theorem deningerFloquetBoundedCorrection_unique
    (A B : Lp ℂ 2 deningerFloquetMeasure →L[ℂ] Y)
    (hA : ∀ f : DeningerMeyerCap, A (deningerFloquetLp (deningerPoissonSource f)) = 0)
    (hB : ∀ f : DeningerMeyerCap, B (deningerFloquetLp (deningerPoissonSource f)) = 0)
    (hAB : ∀ ξ ∈ deningerFloquetResonance,
      A (deningerFloquetAtomLp ξ) = B (deningerFloquetAtomLp ξ)) :
    A = B := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hker : deningerFloquetResonanceSpan
      ≤ LinearMap.ker ((A - B : Lp ℂ 2 deningerFloquetMeasure →L[ℂ] Y) :
        Lp ℂ 2 deningerFloquetMeasure →ₗ[ℂ] Y) := by
    refine Submodule.span_le.2 ?_
    rintro u ⟨ξ, hξ, rfl⟩
    show (A - B) (deningerFloquetAtomLp ξ) = 0
    rw [sub_apply, hAB ξ hξ, sub_self]
  have hclosure : deningerFloquetResonanceSpan.topologicalClosure
      ≤ LinearMap.ker ((A - B : Lp ℂ 2 deningerFloquetMeasure →L[ℂ] Y) :
        Lp ℂ 2 deningerFloquetMeasure →ₗ[ℂ] Y) :=
    Submodule.topologicalClosure_minimal _ hker (A - B).isClosed_ker
  have hsup : deningerFloquetResonanceSpan.topologicalClosure
      ⊔ deningerFloquetResonanceSpan.topologicalClosureᗮ = ⊤ :=
    Submodule.sup_orthogonal_of_hasOrthogonalProjection
  have hmem : x ∈ deningerFloquetResonanceSpan.topologicalClosure
      ⊔ deningerFloquetResonanceSpan.topologicalClosureᗮ := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hmem
  have hqperp : q ∈ deningerFloquetResonanceSpanᗮ :=
    Submodule.orthogonal_le deningerFloquetResonanceSpan.le_topologicalClosure hq
  have hCp : (A - B) p = 0 := hclosure hp
  have hCq : (A - B) q = 0 := by
    rw [sub_apply, deningerFloquetBoundedCorrection_vanishing A hA hqperp,
      deningerFloquetBoundedCorrection_vanishing B hB hqperp, sub_zero]
  have hCx : (A - B) x = 0 := by
    rw [← hpq, map_add, hCp, hCq, add_zero]
  rw [sub_apply, sub_eq_zero] at hCx
  exact hCx

end

end RHTower

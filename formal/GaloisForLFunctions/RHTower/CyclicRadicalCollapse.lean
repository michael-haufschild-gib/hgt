import Mathlib

/-!
# Cyclic radical collapse

A cyclic source vector cannot lie in a closed invariant radical unless that
radical is the whole ambient space.  This elementary topological theorem is
the abstract Hilbert-space mechanism behind the singular-rigging obligation
for the Hedenmalm theta pair.

The theorem is independent of zeta, theta functions, positivity, and spectral
assumptions.  A later source-specific module may discharge cyclicity for the
theta-cusp vector in ordinary `L²`.
-/

open Set

namespace RHTower

noncomputable section

/-- A family is cyclic when its algebraic linear span is dense. -/
def IsCyclicFamily (v : ι → E) [Semiring 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] [TopologicalSpace E] : Prop :=
  Dense (Submodule.span 𝕜 (Set.range v) : Set E)

/-- A closed submodule containing a cyclic family is the whole space. -/
theorem closedSubmodule_eq_top_of_isCyclicFamily
    [Semiring 𝕜] [TopologicalSpace 𝕜] [AddCommMonoid E]
    [TopologicalSpace E] [Module 𝕜 E] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]
    {v : ι → E} (hcyclic : IsCyclicFamily (𝕜 := 𝕜) v)
    (N : Submodule 𝕜 E) (hNclosed : IsClosed (N : Set E))
    (horbit : ∀ i, v i ∈ N) :
    N = ⊤ := by
  have hspan : Submodule.span 𝕜 (Set.range v) ≤ N := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact horbit i
  have hclosure :
      (Submodule.span 𝕜 (Set.range v)).topologicalClosure ≤ N :=
    Submodule.topologicalClosure_minimal _ hspan hNclosed
  have htop :
      (Submodule.span 𝕜 (Set.range v)).topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hcyclic
  rw [htop] at hclosure
  exact top_unique hclosure

/-- Positive formulation: a proper invariant radical containing a cyclic
orbit is forced to be nonclosed in the ambient topology. -/
theorem not_isClosed_of_isCyclicFamily_of_le_properSubmodule
    [Semiring 𝕜] [TopologicalSpace 𝕜] [AddCommMonoid E]
    [TopologicalSpace E] [Module 𝕜 E] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]
    {v : ι → E} (hcyclic : IsCyclicFamily (𝕜 := 𝕜) v)
    (N : Submodule 𝕜 E) (hNproper : N ≠ ⊤)
    (horbit : ∀ i, v i ∈ N) :
    ¬ IsClosed (N : Set E) := by
  intro hclosed
  exact hNproper (closedSubmodule_eq_top_of_isCyclicFamily hcyclic N hclosed horbit)

/-- Orbit form of cyclicity for a family of linear source transforms. -/
def IsCyclicOrbit [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    [TopologicalSpace E] (U : ι → E →ₗ[𝕜] E) (k : E) : Prop :=
  IsCyclicFamily (𝕜 := 𝕜) (fun i ↦ U i k)

/-- A closed submodule containing the complete orbit of a cyclic vector is
the whole ambient space. -/
theorem closedSubmodule_eq_top_of_isCyclicOrbit
    [Semiring 𝕜] [TopologicalSpace 𝕜] [AddCommMonoid E]
    [TopologicalSpace E] [Module 𝕜 E] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]
    {U : ι → E →ₗ[𝕜] E} {k : E} (hcyclic : IsCyclicOrbit (𝕜 := 𝕜) U k)
    (N : Submodule 𝕜 E) (hNclosed : IsClosed (N : Set E))
    (horbit : ∀ i, U i k ∈ N) :
    N = ⊤ :=
  closedSubmodule_eq_top_of_isCyclicFamily hcyclic N hNclosed horbit

/-- Hence every proper submodule containing a cyclic source orbit must be
topologically singular: it is not closed in the ambient topology. -/
theorem cyclicOrbit_forces_nonclosed_properSubmodule
    [Semiring 𝕜] [TopologicalSpace 𝕜] [AddCommMonoid E]
    [TopologicalSpace E] [Module 𝕜 E] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]
    {U : ι → E →ₗ[𝕜] E} {k : E} (hcyclic : IsCyclicOrbit (𝕜 := 𝕜) U k)
    (N : Submodule 𝕜 E) (hNproper : N ≠ ⊤)
    (horbit : ∀ i, U i k ∈ N) :
    ¬ IsClosed (N : Set E) :=
  not_isClosed_of_isCyclicFamily_of_le_properSubmodule hcyclic N hNproper horbit

/-- A continuous complex functional vanishing on a cyclic family is zero. -/
theorem continuousLinearFunctional_eq_zero_of_isCyclicFamily
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {v : ι → E} (hcyclic : IsCyclicFamily (𝕜 := ℂ) v)
    (L : E →L[ℂ] ℂ) (hL : ∀ i, L (v i) = 0) :
    L = 0 := by
  refine ContinuousLinearMap.ext_on hcyclic ?_
  rintro _ ⟨i, rfl⟩
  exact hL i

/-- A continuous reporter on a dense completion vanishes if its pullback
annihilates a cyclic source family.  This is the two-stage density mechanism:
first through the cyclic span in the source, then through the completion map. -/
theorem continuousBoundaryReporter_eq_zero_of_cyclic_denseRange
    {H B Y ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (v : ι → H) (hcyclic : IsCyclicFamily (𝕜 := ℂ) v)
    (j : H →L[ℂ] B) (hj : DenseRange j)
    (q : B →L[ℂ] Y) (hkill : ∀ i, q (j (v i)) = 0) :
    q = 0 := by
  have hqj : q.comp j = 0 := by
    refine ContinuousLinearMap.ext_on hcyclic ?_
    rintro _ ⟨i, rfl⟩
    simpa using hkill i
  have hcomp :
      (q : B → Y) ∘ (j : H → B) =
        ((0 : B →L[ℂ] Y) : B → Y) ∘ (j : H → B) := by
    funext x
    have hx := DFunLike.congr_fun hqj x
    simpa using hx
  have hfun := hj.equalizer q.continuous
    (0 : B →L[ℂ] Y).continuous hcomp
  ext b
  exact congrFun hfun b

end

end RHTower

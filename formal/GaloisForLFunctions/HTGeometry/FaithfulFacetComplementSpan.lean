import Mathlib

/-!
# The faithful-separation complement-span obstruction

The load-bearing mechanism behind every lower bound on faithful facet-separation dimension.
A faithful facet separation assigns to each facet `A` a complex-linear form `ℓ_A` whose zero set
on the assigned vectors is exactly the facet complement: `ℓ_A (a v) = 0 ↔ v ∉ A`.

The `⇐` direction says `ℓ_A` annihilates every complement vector `a v` (`v ∉ A`), hence — being
linear — annihilates the entire subspace they span.  The `⇒` direction says `ℓ_A (a u) ≠ 0` for a
facet vertex `u ∈ A`.  Combining them: **no facet vertex can lie in the span of the complement
vectors** (`facetVertex_notMem_complementSpan`).  Equivalently, membership yields a contradiction
(`no_facetVertex_in_complementSpan`).

This is the incidence obstruction that forces a faithful separation to occupy a large ambient
dimension: whenever the geometry of a complex would push a facet vertex into the linear span of a
facet complement, no faithful separation of that dimension exists.  It holds over an arbitrary
`ℂ`-module, with no finiteness hypothesis, and is the reusable engine for `ffsDim` lower bounds.
-/

open Finset

namespace GaloisForLFunctions

/-- **Complement-span obstruction (positive form).**  Given the exact facet-complement zero
pattern `ℓ_i (a v) = 0 ↔ v ∉ fac i`, a facet vertex `u ∈ fac i` never lies in the `ℂ`-linear span
of the complement vectors `{a v : v ∉ fac i}`.  If it did, linearity of `ℓ_i` would force
`ℓ_i (a u) = 0`, contradicting `u ∈ fac i`. -/
theorem facetVertex_notMem_complementSpan
    {V : Type*} {E : Type*} [AddCommGroup E] [Module ℂ E]
    {m : ℕ} (fac : Fin m → Finset V)
    (a : V → E) (ℓ : Fin m → (E →ₗ[ℂ] ℂ))
    (hzero : ∀ (i : Fin m) (v : V), ℓ i (a v) = 0 ↔ v ∉ fac i)
    (i : Fin m) (u : V) (hu : u ∈ fac i) :
    a u ∉ Submodule.span ℂ (a '' {v | v ∉ fac i}) := by
  intro hmem
  have hker : Submodule.span ℂ (a '' {v | v ∉ fac i}) ≤ LinearMap.ker (ℓ i) := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact (hzero i v).mpr hv
  have hz : ℓ i (a u) = 0 := by
    have := hker hmem
    rwa [LinearMap.mem_ker] at this
  exact (hzero i u).mp hz hu

/-- **Complement-span obstruction (contradiction form).**  If a facet vertex `u ∈ fac i` lies in
the span of its facet complement, the faithful zero pattern is impossible. -/
theorem no_facetVertex_in_complementSpan
    {V : Type*} {E : Type*} [AddCommGroup E] [Module ℂ E]
    {m : ℕ} (fac : Fin m → Finset V)
    (a : V → E) (ℓ : Fin m → (E →ₗ[ℂ] ℂ))
    (hzero : ∀ (i : Fin m) (v : V), ℓ i (a v) = 0 ↔ v ∉ fac i)
    (i : Fin m) (u : V) (hu : u ∈ fac i)
    (hmem : a u ∈ Submodule.span ℂ (a '' {v | v ∉ fac i})) : False :=
  facetVertex_notMem_complementSpan fac a ℓ hzero i u hu hmem

/-- **Strict enlargement.**  Adjoining a facet vertex `a u` (`u ∈ fac i`) to the complement span
strictly enlarges it: the complement span is a proper subspace of the span of the complement
together with `a u`.  This is the strict-inclusion step that converts the incidence obstruction
into a dimension increment for `ffsDim` lower bounds. -/
theorem complementSpan_lt_insert_facetVertex
    {V : Type*} {E : Type*} [AddCommGroup E] [Module ℂ E]
    {m : ℕ} (fac : Fin m → Finset V)
    (a : V → E) (ℓ : Fin m → (E →ₗ[ℂ] ℂ))
    (hzero : ∀ (i : Fin m) (v : V), ℓ i (a v) = 0 ↔ v ∉ fac i)
    (i : Fin m) (u : V) (hu : u ∈ fac i) :
    Submodule.span ℂ (a '' {v | v ∉ fac i})
      < Submodule.span ℂ (insert (a u) (a '' {v | v ∉ fac i})) := by
  have hnot : a u ∉ Submodule.span ℂ (a '' {v | v ∉ fac i}) :=
    facetVertex_notMem_complementSpan fac a ℓ hzero i u hu
  refine lt_of_le_of_ne (Submodule.span_mono (Set.subset_insert _ _)) ?_
  intro heq
  apply hnot
  rw [heq]
  exact Submodule.subset_span (Set.mem_insert _ _)

end GaloisForLFunctions

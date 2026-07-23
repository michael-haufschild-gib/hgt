import GaloisForLFunctions.HTGeometry.FaithfulFacetDimension
import GaloisForLFunctions.HTGeometry.FaithfulFacetVertexDimension

/-!
# Minimum-dimension faithful facet separation

The corpus constructs faithful facet separations separately in facet-coordinate dimension and in
vertex-coordinate dimension.  This file transports the smaller construction to one canonical
finite coordinate space and realizes the advertised minimum bound exactly.
-/

open Finset

namespace GaloisForLFunctions

noncomputable section

/-- Faithful separation of a finite covered facet family in the canonical coordinate space whose
dimension is the smaller of the facet and vertex counts. -/
def FaithfulFacetMinDimensionSeparation
    {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} (fac : Fin m → Finset V) : Prop :=
  ∃ (a : V → (Fin (min m (Fintype.card V)) → ℂ))
      (ℓ : Fin m → ((Fin (min m (Fintype.card V)) → ℂ) →ₗ[ℂ] ℂ)),
    LinearIndependent ℚ a ∧
    (∀ (i : Fin m) (v : V), ℓ i (a v) = 0 ↔ v ∉ fac i) ∧
    ∀ i : Fin m, LinearIndependent ℚ (fun v : fac i => ℓ i (a v))

/-- **Faithful-facet minimum-dimension universality law.**  Every finite vertex set covered by a
finite facet family admits a faithful separation in complex coordinate dimension exactly
`min(#facets,#vertices)`.  The vectors are rationally independent, every facet form has precisely
the facet complement as its zero pattern, and its nonzero facet values remain rationally
independent. -/
theorem exists_faithfulFacetMinDimensionSeparation
    {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} (fac : Fin m → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ fac i) :
    FaithfulFacetMinDimensionSeparation fac := by
  classical
  obtain ⟨τ, hτ⟩ := exists_transcendental_complex
  by_cases hm : m ≤ Fintype.card V
  · rw [FaithfulFacetMinDimensionSeparation, Nat.min_eq_left hm]
    obtain ⟨a, ha, hzero, hvalues⟩ :=
      exists_faithfulFacetSeparation hτ fac hcover
    let ℓ : Fin m → ((Fin m → ℂ) →ₗ[ℂ] ℂ) := fun i => LinearMap.proj i
    refine ⟨a, ℓ, ha, ?_, ?_⟩
    · intro i v
      simpa [ℓ] using hzero i v
    · intro i
      simpa [ℓ] using hvalues i
  · have hcard : Fintype.card V ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hm)
    rw [FaithfulFacetMinDimensionSeparation, Nat.min_eq_right hcard]
    obtain ⟨a, ℓ, ha, hzero, hvalues⟩ :=
      exists_faithfulFacetSeparation_vertexDim hτ fac
    let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
    let E : (V → ℂ) ≃ₗ[ℂ] (Fin (Fintype.card V) → ℂ) :=
      LinearEquiv.piCongrLeft ℂ (fun _ : Fin (Fintype.card V) => ℂ) e
    let a' : V → (Fin (Fintype.card V) → ℂ) := fun v => E (a v)
    let ℓ' : Fin m → ((Fin (Fintype.card V) → ℂ) →ₗ[ℂ] ℂ) :=
      fun i => (ℓ i).comp E.symm.toLinearMap
    have ha' : LinearIndependent ℚ a' := by
      apply ha.map'
        (E.toLinearMap.restrictScalars ℚ)
      exact LinearMap.ker_eq_bot.mpr E.injective
    refine ⟨a', ℓ', ha', ?_, ?_⟩
    · intro i v
      simpa [a', ℓ'] using hzero i v
    · intro i
      simpa [a', ℓ'] using hvalues i

end

end GaloisForLFunctions

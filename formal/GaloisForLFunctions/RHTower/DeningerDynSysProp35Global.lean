import GaloisForLFunctions.RHTower.DeningerDynSysProp35Affine
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Proposition 3.5 for a general base

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 3.5, the
covering step.

A `C`-valued point of a scheme has a single point as image, so it factors through any affine open
containing that point.  Hence the affine case of Proposition 3.5 globalises: if every point of the
base has an affine open neighbourhood over which the ring homomorphism is surjective on
homomorphisms into `C`, then every `C`-point of the base lifts.
-/

namespace RHTower

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

variable {X X₀ : Scheme.{u}} (π : X ⟶ X₀) {C : Type u} [Field C]

/-- A `C`-point of a scheme factors through any affine open containing its image. -/
theorem deningerPoint_range_subset {U₀ : X₀.Opens} (hU₀ : IsAffineOpen U₀)
    (g : Spec (CommRingCat.of C) ⟶ X₀)
    (hmem : ∀ p : (Spec (CommRingCat.of C) : Scheme.{u}), g.base p ∈ U₀) :
    Set.range (g.base) ⊆ Set.range (hU₀.fromSpec.base) := by
  rw [hU₀.range_fromSpec]
  rintro _ ⟨p, rfl⟩
  exact hmem p

/-- **Deninger, Proposition 3.5, surjectivity.**  If every point of the base has an affine open
neighbourhood over which the ring homomorphism is surjective on homomorphisms into `C`, then every
`C`-point of the base lifts to a `C`-point of the total space. -/
theorem deningerSchemePoint_surjective
    (hloc : ∀ x₀ : X₀, ∃ (U₀ : X₀.Opens) (_ : IsAffineOpen U₀), x₀ ∈ U₀ ∧
      ∃ _ : IsAffineOpen (π ⁻¹ᵁ U₀),
        Function.Surjective (fun ψ : Γ(X, π ⁻¹ᵁ U₀) ⟶ CommRingCat.of C => π.app U₀ ≫ ψ)) :
    Function.Surjective (fun h : Spec (CommRingCat.of C) ⟶ X => h ≫ π) := by
  intro g
  obtain ⟨U₀, hU₀, hmem, hV, hsurj⟩ := hloc (g.base default)
  have hsub : Set.range (g.base) ⊆ Set.range (hU₀.fromSpec.base) := by
    refine deningerPoint_range_subset hU₀ g fun p => ?_
    have hp : p = default := Subsingleton.elim _ _
    rw [hp]
    exact hmem
  have hg' : IsOpenImmersion.lift hU₀.fromSpec g hsub ≫ hU₀.fromSpec = g :=
    IsOpenImmersion.lift_fac _ _ _
  obtain ⟨ψ, hψ⟩ := hsurj (Spec.preimage (IsOpenImmersion.lift hU₀.fromSpec g hsub))
  have hψ' : π.app U₀ ≫ ψ = Spec.preimage (IsOpenImmersion.lift hU₀.fromSpec g hsub) := hψ
  refine ⟨Spec.map ψ ≫ hV.fromSpec, ?_⟩
  dsimp only
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec π hU₀ hV (le_refl (π ⁻¹ᵁ U₀)),
    ← Spec.map_comp_assoc, ← Scheme.Hom.app_eq_appLE, hψ', Spec.map_preimage, hg']

/-- **Deninger, Proposition 3.5, the fibres.**  If two `C`-points of the total space lying over a
common affine open of the base and inducing the same point of the base are `G`-conjugate, then
this holds globally: two `C`-points over the same point of the base already lie over a common
affine open. -/
theorem deningerSchemePoint_conjugate {G : Type*} (σ : G → (X ⟶ X))
    (hloc : ∀ x₀ : X₀, ∃ (U₀ : X₀.Opens) (_ : IsAffineOpen U₀), x₀ ∈ U₀ ∧
      ∀ k₁ k₂ : Spec (CommRingCat.of C) ⟶ X,
        (∀ p : (Spec (CommRingCat.of C) : Scheme.{u}), (k₁ ≫ π).base p ∈ U₀) →
        (∀ p : (Spec (CommRingCat.of C) : Scheme.{u}), (k₂ ≫ π).base p ∈ U₀) →
        k₁ ≫ π = k₂ ≫ π → ∃ g : G, k₂ = k₁ ≫ σ g)
    (h₁ h₂ : Spec (CommRingCat.of C) ⟶ X) (h : h₁ ≫ π = h₂ ≫ π) :
    ∃ g : G, h₂ = h₁ ≫ σ g := by
  obtain ⟨U₀, _, hmem, hcase⟩ := hloc ((h₁ ≫ π).base default)
  refine hcase h₁ h₂ ?_ ?_ h
  · intro p
    rw [Subsingleton.elim p default]
    exact hmem
  · intro p
    rw [Subsingleton.elim p default, ← h]
    exact hmem

end

end RHTower

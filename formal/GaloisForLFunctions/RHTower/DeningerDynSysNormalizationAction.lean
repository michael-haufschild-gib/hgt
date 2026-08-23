import Mathlib.AlgebraicGeometry.Normalization

/-!
# The Galois action on a relative normalization

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §3: for `X₀` an
integral normal scheme with function field `K₀` and `K` a normal extension of `K₀`, the group
`G = Aut_{K₀}(K)` acts on the normalization `X` of `X₀` in `K`.

The construction is the universal property of the relative normalization.  An endomorphism `σ` of
the source over the base induces `X ⟶ X` as the unique factorization of `σ ≫ toNormalization`
through the integral morphism `fromNormalization`; uniqueness gives the two functoriality laws,
and the factorization gives that the induced map lies over the base.
-/

namespace RHTower

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- The endomorphism of the relative normalization induced by an endomorphism of the source over
the base. -/
def deningerNormalizationMap (σ : X ⟶ X) (hσ : σ ≫ f = f) :
    f.normalization ⟶ f.normalization :=
  f.normalizationDesc (σ ≫ f.toNormalization) f.fromNormalization
    (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hσ])

/-- The induced endomorphism lies over the base. -/
@[reassoc (attr := simp)]
theorem deningerNormalizationMap_comp (σ : X ⟶ X) (hσ : σ ≫ f = f) :
    deningerNormalizationMap f σ hσ ≫ f.fromNormalization = f.fromNormalization :=
  f.normalizationDesc_comp _ _ _

/-- The induced endomorphism is compatible with the map into the normalization. -/
@[reassoc]
theorem deningerToNormalization_normalizationMap (σ : X ⟶ X) (hσ : σ ≫ f = f) :
    f.toNormalization ≫ deningerNormalizationMap f σ hσ = σ ≫ f.toNormalization :=
  f.toNormalization_normalizationDesc _ _ _

theorem deningerNormalizationMap_congr (σ τ : X ⟶ X) (hσ : σ ≫ f = f) (hτ : τ ≫ f = f)
    (h : σ = τ) :
    deningerNormalizationMap f σ hσ = deningerNormalizationMap f τ hτ := by
  subst h; rfl

@[simp]
theorem deningerNormalizationMap_id :
    deningerNormalizationMap f (𝟙 X) (Category.id_comp f) = 𝟙 _ := by
  refine Scheme.Hom.normalization.hom_ext f _ _ f.fromNormalization ?_ ?_ ?_
  · rw [deningerToNormalization_normalizationMap, Category.comp_id, Category.id_comp]
  · exact deningerNormalizationMap_comp f _ _
  · rw [Category.id_comp]

theorem deningerNormalizationMap_map (σ τ : X ⟶ X) (hσ : σ ≫ f = f) (hτ : τ ≫ f = f) :
    deningerNormalizationMap f σ hσ ≫ deningerNormalizationMap f τ hτ
      = deningerNormalizationMap f (σ ≫ τ) (by rw [Category.assoc, hτ, hσ]) := by
  refine Scheme.Hom.normalization.hom_ext f _ _ f.fromNormalization ?_ ?_ ?_
  · rw [← Category.assoc, deningerToNormalization_normalizationMap, Category.assoc,
      deningerToNormalization_normalizationMap, ← Category.assoc,
      deningerToNormalization_normalizationMap]
  · rw [Category.assoc, deningerNormalizationMap_comp, deningerNormalizationMap_comp]
  · exact deningerNormalizationMap_comp f _ _

/-- An automorphism of the source over the base induces an automorphism of the relative
normalization. -/
def deningerNormalizationIso (σ : X ≅ X) (hσ : σ.hom ≫ f = f) :
    f.normalization ≅ f.normalization where
  hom := deningerNormalizationMap f σ.hom hσ
  inv := deningerNormalizationMap f σ.inv
    (by simpa using (congrArg (fun k => σ.inv ≫ k) hσ).symm)
  hom_inv_id := by
    rw [deningerNormalizationMap_map]
    exact (deningerNormalizationMap_congr f _ (𝟙 X) _ (Category.id_comp f)
      σ.hom_inv_id).trans (deningerNormalizationMap_id f)
  inv_hom_id := by
    rw [deningerNormalizationMap_map]
    exact (deningerNormalizationMap_congr f _ (𝟙 X) _ (Category.id_comp f)
      σ.inv_hom_id).trans (deningerNormalizationMap_id f)

/-- A family of endomorphisms of the source over the base — Deninger's action of `Aut_{K₀}(K)` —
transported to the relative normalization. -/
def deningerNormalizationAction {G : Type*} (ρ : G → (X ⟶ X)) (hρ : ∀ g, ρ g ≫ f = f) :
    G → (f.normalization ⟶ f.normalization) :=
  fun g => deningerNormalizationMap f (ρ g) (hρ g)

@[simp]
theorem deningerNormalizationAction_comp {G : Type*} (ρ : G → (X ⟶ X)) (hρ : ∀ g, ρ g ≫ f = f)
    (g : G) :
    deningerNormalizationAction f ρ hρ g ≫ f.fromNormalization = f.fromNormalization :=
  deningerNormalizationMap_comp f _ _

end

end RHTower

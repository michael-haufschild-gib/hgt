import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.ArtinCharacterOnRefinedRay

/-! Agreement on coprime ideals extends to ideles by ray normalization. -/

noncomputable section

open NumberField IsDedekindDomain GaloisForLFunctions GaloisForLFunctions.HeckeLFunctions

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

universe u

variable {K L G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  {A : Type*} [Group A]

theorem artin_factor_of_agreement_on_ideals (q m : Modulus K)
    (hfin : q.fin ≤ m.fin) (hinf : m.inf ⊆ q.inf) (f : IdeleGroup K →* G)
    (hd : ∀ a : Kˣ, f (diagonal K a) = 1)
    (hf : ∀ y : idelesOneMod m, f y.val = artinMap K L G (toFractionalIdeal y.val))
    (g : G →* A) (χ : RayClassGroup q →* A)
    (hχ : ∀ I : idealGroup q, g (artinMap K L G I.val) = χ (rayClass q I)) :
    g.comp f = χ.comp (toRayClass q) := by
  ext x
  obtain ⟨a, ha⟩ := exists_diagonal_mul_mem_idelesOneMod q x
  let y : idelesOneMod q := ⟨diagonal K a * x, ha⟩
  have he : f y.val = f x := by
    change f (diagonal K a * x) = f x
    rw [map_mul, hd, _root_.one_mul]
  have hr := toRayClass_normalized q a⁻¹ y
  change toRayClass q (diagonal K a⁻¹ * (diagonal K a * x)) = _ at hr
  rw [map_inv, inv_mul_cancel_left] at hr
  change g (f x) = χ (toRayClass q x)
  rw [← he, hf ⟨y.val, idelesOneMod_le_of_refinement hfin hinf y.2⟩, hr]
  exact hχ (toCoprimeIdeals q y)

end GlobalTheory.Reciprocity

import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdelicRayRefinement
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.FiniteIdelicArtin

/-! A finite idelic Artin factor determines the character on ideals
prime to a common refinement of its two moduli. -/

noncomputable section

open NumberField IsDedekindDomain GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

universe u

variable {K L G : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  {A : Type*} [Group A]

/-- Factor identities on ideles may be evaluated on coprime fractional
ideals after refining the ray and Artin moduli. -/
theorem artin_factor_on_ray_refinement (q r m : Modulus K)
    (hqr : q.fin ≤ r.fin) (hqm : q.fin ≤ m.fin)
    (hir : r.inf ⊆ q.inf) (him : m.inf ⊆ q.inf)
    (f : IdeleGroup K →* G) (g : G →* A) (χ : RayClassGroup m →* A)
    (hf : ∀ x : idelesOneMod r, f x.val = artinMap K L G (toFractionalIdeal x.val))
    (hχ : g.comp f = χ.comp (toRayClass m))
    (I : idealGroup q) :
    g (artinMap K L G I.val) =
      χ (rayClass m ⟨I.val, fun v hv => I.2 v (hv.trans (Ideal.dvd_iff_le.mpr hqm))⟩) := by
  obtain ⟨x, hx⟩ := toCoprimeIdeals_surjective q I
  have hI : toFractionalIdeal x.val = I.val := congrArg Subtype.val hx
  let y : idelesOneMod m := ⟨x.val, idelesOneMod_le_of_refinement hqm him x.2⟩
  have he : toRayClass m x.val = rayClass m (toCoprimeIdeals m y) := by
    simpa only [map_one, one_mul] using toRayClass_normalized m 1 y
  have h := DFunLike.congr_fun hχ x.val
  change g (f x.val) = χ (toRayClass m x.val) at h
  rw [hf ⟨x.val, idelesOneMod_le_of_refinement hqr hir x.2⟩, hI, he] at h
  exact h.trans (congrArg (fun z : idealGroup m => χ (rayClass m z)) (Subtype.ext hI))

end GlobalTheory.Reciprocity

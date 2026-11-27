import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.RayNormRefinement
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.ArtinCharacterOnRefinedRay

/-! A norm pullback identity on ideles determines the relative Artin
values on ideals prime to a common rational refinement. -/

noncomputable section

open NumberField IsDedekindDomain GaloisForLFunctions GaloisForLFunctions.HeckeLFunctions

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

variable {K E M H : Type} [Field K] [NumberField K] [Field E] [NumberField E]
  [Field M] [NumberField M] [Algebra K E] [Algebra E M] [CommGroup H] [Fintype H]
  [MulSemiringAction H M] [IsGaloisGroup H E M] {A : Type*} [Group A]

theorem artin_factor_on_norm_refinement {c d : ℕ} [NeZero c] [NeZero d]
    (hcd : c ∣ d) (m : Modulus E) (hd : (normModulus E d).fin ≤ m.fin)
    (f : IdeleGroup E →* H) (ψ : H →* A) (χ : RayClassGroup (normModulus K c) →* A)
    (hp : ∀ y : idelesOneMod m, f y.val = artinMap E M H (toFractionalIdeal y.val))
    (hχ : ψ.comp f = (χ.comp (rayClassNorm K E c)).comp (toRayClass (normModulus E c)))
    (J : idealGroup (normModulus E d)) :
    ψ (artinMap E M H J.val) =
      (χ.comp (rationalRayReduction K hcd)) (rayClassNorm K E d (rayClass (normModulus E d) J)) := by
  have h := artin_factor_on_ray_refinement (normModulus E d) m (normModulus E c)
    hd (normModulus_fin_le_of_dvd E hcd) (Set.subset_univ _) (by rfl)
    f ψ (χ.comp (rayClassNorm K E c)) hp hχ J
  have hn := DFunLike.congr_fun (rationalRayReduction_comp_rayClassNorm K E hcd)
    (rayClass (normModulus E d) J)
  exact h.trans (congrArg χ hn.symm)

end GlobalTheory.Reciprocity

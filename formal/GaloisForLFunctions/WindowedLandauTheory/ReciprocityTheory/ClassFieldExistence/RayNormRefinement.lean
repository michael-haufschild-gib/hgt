import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.RayClassNorm
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.RationalRayRefinement

/-! Norms on ray class groups are compatible with rational modulus reduction. -/

noncomputable section

open NumberField GaloisForLFunctions GaloisForLFunctions.HeckeLFunctions

namespace GlobalTheory.Reciprocity

open IdeleRay

universe u

variable (K E : Type u) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

theorem rationalRayReduction_comp_rayClassNorm {c d : ℕ} [NeZero c] [NeZero d]
    (h : c ∣ d) :
    (rationalRayReduction K h).comp (rayClassNorm K E d) =
      (rayClassNorm K E c).comp (rationalRayReduction E h) := by
  apply MonoidHom.ext
  intro I
  obtain ⟨J, rfl⟩ := (QuotientGroup.mk'_surjective _) I
  rfl

end GlobalTheory.Reciprocity

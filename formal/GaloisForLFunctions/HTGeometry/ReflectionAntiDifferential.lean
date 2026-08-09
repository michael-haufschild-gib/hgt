import GaloisForLFunctions.HTGeometry.AntiDifferentialAlgEquiv
import GaloisForLFunctions.HTGeometry.MeromorphicReflection
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# The rapidity reflection as an orientation-reversing differential automorphism

The reflection `z ↦ c − z` fixes the constant field pointwise and negates the derivation, so it is
a term of `AntiDifferentialAlgEquiv ℂ (meroField Set.univ)`.  Consequently it preserves
differential algebraicity over `ℂ` exactly, and the Kolchin exchange obstruction transports to the
automorphism it was written about.
-/

namespace GaloisForLFunctions.HTGeometry

open Bottcher
open scoped Differential UnivMeroFieldInstances

noncomputable section

theorem complexReflectionAnalyticEquiv_constToAnalytic (c a : ℂ) :
    complexReflectionAnalyticEquiv c (constToAnalytic (Set.univ : Set ℂ) a)
      = constToAnalytic (Set.univ : Set ℂ) a :=
  precompAnalytic_constToAnalytic (analyticOnNhd_complexReflection c _)
    (Set.mapsTo_univ _ _) a

theorem complexReflectionMeroEquiv_algebraMap_complex (c a : ℂ) :
    complexReflectionMeroEquiv c (algebraMap ℂ (meroField (Set.univ : Set ℂ)) a)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) a := by
  have hmap : algebraMap ℂ (meroField (Set.univ : Set ℂ)) a
      = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ))
        (constToAnalytic (Set.univ : Set ℂ) a) := rfl
  rw [hmap, complexReflectionMeroEquiv_algebraMap,
    complexReflectionAnalyticEquiv_constToAnalytic]

/-- **The reflection is an orientation-reversing differential automorphism.** -/
def reflectionAntiDifferentialAlgEquiv (c : ℂ) :
    AntiDifferentialAlgEquiv ℂ (meroField (Set.univ : Set ℂ)) where
  toAlgEquiv :=
    AlgEquiv.ofRingEquiv (f := complexReflectionMeroEquiv c)
      (complexReflectionMeroEquiv_algebraMap_complex c)
  map_deriv_neg' := complexReflectionMeroEquiv_deriv c

@[simp]
theorem reflectionAntiDifferentialAlgEquiv_apply (c : ℂ)
    (z : meroField (Set.univ : Set ℂ)) :
    (reflectionAntiDifferentialAlgEquiv c).toAlgEquiv z = complexReflectionMeroEquiv c z := rfl

/-- **Reflection preserves differential algebraicity over the constants exactly.**  This is the
transport law the Kolchin exchange obstruction needs for the physical rapidity reflection. -/
theorem differentialAlgebraicOver_complexReflectionMeroEquiv_iff (c : ℂ)
    (z : meroField (Set.univ : Set ℂ)) :
    DifferentialAlgebraicOver ℂ (complexReflectionMeroEquiv c z)
      ↔ DifferentialAlgebraicOver ℂ z :=
  (reflectionAntiDifferentialAlgEquiv c).differentialAlgebraicOver_map_iff z

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.RHTower.CompletedFluxGermRigidity

/-!
# Hasse principle for completed-flux Taylor data

The complete Taylor profile of the residue-filled completed local flux separates arbitrary complex
base points.  Thus distinct points are detected at one finite derivative order, including points
where `xi` vanishes.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Completed-flux Taylor coefficients form a Hasse family for complex base points. -/
noncomputable def completedFluxTaylorHasseFamily : HasseFamily ℂ ℕ where
  Local _ := ℂ
  profile := completedFluxTaylorCoeff
  profile_injective := by
    intro a b h
    apply completedFluxGermAt_germ_injective
    apply (completedFluxTaylorCoeff_all_eq_iff_germ_eq a b).mp
    exact congrFun h

/-- Complex points are equivalent to the completed-flux Taylor profiles that occur. -/
noncomputable def completedFluxTaylorHasseEquivRealizedProfile :
    ℂ ≃ Set.range completedFluxTaylorCoeff :=
  completedFluxTaylorHasseFamily.equivRealizedProfiles

/-- Two base points agree exactly when all completed-flux Taylor coefficients agree. -/
theorem completedFluxTaylorCoeff_congr_hasse_iff (a b : ℂ) :
    (∀ n : ℕ, completedFluxTaylorCoeff a n = completedFluxTaylorCoeff b n) ↔ a = b :=
  completedFluxTaylorHasseFamily.pointwise_eq_iff a b

/-- Unequal base points differ at one finite completed-flux derivative order. -/
theorem completedFluxTaylorCoeff_ne_iff_exists_order_ne (a b : ℂ) :
    a ≠ b ↔ ∃ n : ℕ, completedFluxTaylorCoeff a n ≠ completedFluxTaylorCoeff b n :=
  completedFluxTaylorHasseFamily.ne_iff_exists_local_ne a b

end


end RHTower

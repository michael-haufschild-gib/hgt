import GaloisForLFunctions.RHTower.XiContinuousCappedLift
import GaloisForLFunctions.HTGeometry.CappedSimplyConnectedFactorization

open Topology Set Function
open scoped UpperHalfPlane

namespace RHTower.XiMarkedMonodromy
open GaloisForLFunctions.HTGeometry

/-- Actual Xi factors continuously through a simply connected capped image cover.
No hypothesis on Xi or on the existence or topology of its completion is assumed. -/
theorem xi_simplyConnected_capped_factorization :
    ∃ H : Subgroup (coveringDeckGroup markedUniversalCover),
      SimplyConnectedSpace (CappedMarkedCover H) ∧
      ∃ G : C(ℂ, CappedMarkedCover H), ∀ z, cappedMarkedProjection H (G z) = xi z := by
  obtain ⟨H, F, hF, G, hGp, hG, hsurj⟩ := xi_continuous_capped_image_factorization
  let j : C(Source ({0} : Finset ℝ), ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  let i : C(MarkedImageCover H, CappedMarkedCover H) :=
    ⟨(finitePeripheralCapData H).old, (finitePeripheralCapData H).continuous_old⟩
  have hcomm : G.comp j = i.comp F := by
    ext s
    exact hG s
  have hs : SimplyConnectedSpace (CappedMarkedCover H) :=
    simplyConnectedSpace_of_commuting_surjective_fundamentalGroups F i j G (sourceZero {0})
      (fundamentalGroup_map_surjective_of_mapOfEq F hF hsurj)
      ((finitePeripheralCapData H).fundamentalGroup_old_surjective (F (sourceZero {0}))) hcomm
  exact ⟨H, hs, G, hGp⟩

end RHTower.XiMarkedMonodromy

import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.HTGeometry.TwoProjectionSupersymmetry
import GaloisForLFunctions.RHTower.SoninEvenCarrier

noncomputable section

namespace RHTower

/-- Closed two-projection `D = 1`, `N = 2` split from even parity and a central Sonin carrier. -/
def soninEvenCentralD1N2Split (a : ℝ) :
    SuperPoincare.D1N2Split (Module.End ℂ SoninL2) :=
  SuperPoincare.D1N2Split.ofEqNeg
    (evenProjection.toLinearMap - (centralSoninProjection a).toLinearMap)
    (1 - evenProjection.toLinearMap - (centralSoninProjection a).toLinearMap)
    (eq_neg_iff_add_eq_zero.mpr
      (HTGeometry.twoProjection_difference_anticommutes_complement
        (ContinuousLinearMap.IsIdempotentElem.toLinearMap evenProjection_idempotent)
        (ContinuousLinearMap.IsIdempotentElem.toLinearMap
          (centralSoninCarrier a).isIdempotentElem_starProjection)))

/-- The two momenta partition the identity for every concrete central Sonin carrier. -/
theorem soninEvenCentral_momentum_partition (a : ℝ) :
    (soninEvenCentralD1N2Split a).momentum0 +
      (soninEvenCentralD1N2Split a).momentum1 = 1 := by
  change
    (evenProjection.toLinearMap - (centralSoninProjection a).toLinearMap) *
        (evenProjection.toLinearMap - (centralSoninProjection a).toLinearMap) +
      (1 - evenProjection.toLinearMap - (centralSoninProjection a).toLinearMap) *
        (1 - evenProjection.toLinearMap - (centralSoninProjection a).toLinearMap) = 1
  exact HTGeometry.twoProjection_difference_sq_add_complement_sq
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap evenProjection_idempotent)
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap
      (centralSoninCarrier a).isIdempotentElem_starProjection)

end RHTower

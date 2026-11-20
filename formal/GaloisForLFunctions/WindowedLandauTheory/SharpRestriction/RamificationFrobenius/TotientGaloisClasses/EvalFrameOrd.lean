import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection

/-! # A `positivity` extension: the order of a frame is positive. -/

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- `positivity` proves `0 < Frame.ord a`. -/
@[positivity WindowedLandauTheory.HC.Frame.ord _]
def evalFrameOrd : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with
  | none => throwError "no order"
  | some _pα => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(WindowedLandauTheory.HC.Frame.ord $a) =>
    assertInstancesCommute
    return .positive q(WindowedLandauTheory.HC.Frame.ord_pos $a)
  | _, _, _ => throwError "not the order of a frame"

end Mathlib.Meta.Positivity

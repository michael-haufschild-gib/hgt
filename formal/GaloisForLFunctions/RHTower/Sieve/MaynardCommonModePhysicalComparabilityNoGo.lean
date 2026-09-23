import GaloisForLFunctions.RHTower.Sieve.MaynardCommonModePairedAnnulus

/-!
# Common-mode physical comparability obstruction

The frozen common reference is deliberately wider than every physical target.
This proves that the separation is polynomial, not a removable constant loss:
the existing physical-slice outer receiver, whose two endpoint estimates require
`R ≤ 2H`, cannot be applied to the common-mode pair on any sufficiently high
physical block.  Thus a width telescope only becomes a viable Route-T weld if it
also supplies a new treatment of its wide transition rungs.
-/

noncomputable section

namespace RHTower.Sieve

open Filter Set

/-- The common reference eventually exceeds twice every target relative width in its physical
block.  Its exact exponent gap is `29/80 - d/2`, where `d` is the fixed global amplitude
deficit.  Consequently the `R ≤ 2H` premise in the existing physical outer receiver fails
uniformly for the Route-T common-mode pair. -/
theorem eventually_routeT_commonMode_reference_exceeds_two_targetWidths :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ lambda ∈ Set.Icc x (2 * x),
      2 * routeTPrimeGapPacketWidth lambda <
        routeTCommonModeReferenceRelativeWidth x := by
  let theta : ℝ := routeTPhysicalSliceHandoffTheta
  let e : ℝ := theta - 1 + 49 / 80
  have he : 0 < e := by
    dsimp only [e, theta, routeTPhysicalSliceHandoffTheta]
    linarith [maynardLongGlobalAmplitudeDeficit_lt_one_hundredth]
  have hpowTop : Tendsto (fun x : ℝ => x ^ e) atTop atTop :=
    tendsto_rpow_atTop he
  have hlarge : ∀ᶠ x : ℝ in atTop, 1 < x ^ e :=
    hpowTop.eventually_gt_atTop 1
  filter_upwards [hlarge, Filter.eventually_ge_atTop (1 : ℝ)] with x hxe hx
  intro lambda hlambda
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hanti : lambda ^ (-(49 / 80 : ℝ)) ≤ x ^ (-(49 / 80 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hx0 hlambda.1 (by norm_num)
  have htheta0 : 0 ≤ theta := by
    dsimp only [theta]
    exact routeTPhysicalSliceHandoffTheta_pos.le
  have htwo : 1 ≤ (2 : ℝ) ^ theta :=
    Real.one_le_rpow (by norm_num) htheta0
  have hcoeff : 4 ≤ (4 : ℝ) * 2 ^ theta := by nlinarith
  have hfactor : x ^ (theta - 1) =
      x ^ (-(49 / 80 : ℝ)) * x ^ e := by
    rw [← Real.rpow_add hx0]
    congr 1
    dsimp only [e]
    ring
  have hfactorBig : 2 < (4 : ℝ) * 2 ^ theta * x ^ e := by
    nlinarith
  have hnegpos : 0 < x ^ (-(49 / 80 : ℝ)) :=
    Real.rpow_pos_of_pos hx0 _
  have hmain : 2 * x ^ (-(49 / 80 : ℝ)) <
      (4 : ℝ) * 2 ^ theta * x ^ (theta - 1) := by
    calc
      2 * x ^ (-(49 / 80 : ℝ)) = x ^ (-(49 / 80 : ℝ)) * 2 := by ring
      _ < x ^ (-(49 / 80 : ℝ)) * ((4 : ℝ) * 2 ^ theta * x ^ e) :=
        mul_lt_mul_of_pos_left hfactorBig hnegpos
      _ = (4 : ℝ) * 2 ^ theta * x ^ (theta - 1) := by rw [hfactor]; ring
  have hrefEq : routeTCommonModeReferenceRelativeWidth x =
      ((4 : ℝ) * 2 ^ theta) * x ^ (theta - 1) := by
    dsimp only [routeTCommonModeReferenceRelativeWidth]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx0.le,
      Real.rpow_sub hx0, Real.rpow_one]
    ring
  unfold routeTPrimeGapPacketWidth
  calc
    2 * lambda ^ (-(49 / 80 : ℝ)) ≤ 2 * x ^ (-(49 / 80 : ℝ)) :=
      mul_le_mul_of_nonneg_left hanti (by norm_num)
    _ < (4 : ℝ) * 2 ^ theta * x ^ (theta - 1) := hmain
    _ = routeTCommonModeReferenceRelativeWidth x := hrefEq.symm

end RHTower.Sieve

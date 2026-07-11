import GaloisForLFunctions.RHTower.XiThetaSquareRateCausalSource
import GaloisForLFunctions.RHTower.XiThetaHeatReparametrization

/-!
# Reflected completed-theta action of the causal square-rate reader

The completed theta source splits into a positive logarithmic half and its reflection.  Under the
same shifted heat coordinate `y = exp(u) - 1`, the reflected half occupies `-1 < y < 0`.  The
square-rate source reader is causal: it vanishes almost everywhere on `y < 0`.  Their direct
pairing is therefore exactly zero.

Reorienting the reflected half before applying the heat coordinate does not create a second
charge: by definition it recovers the positive half itself.  Thus reflection is either annihilated
by the one-coordinate causal reader or duplicates the positive datum after reorientation; it is
never an independent source variable.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate

noncomputable section

namespace RHTower

/-- The reflected theta half in the global shifted heat coordinate `y = exp(u) - 1`.
The indicator records the natural domain `y > -1`; the reflected source itself forces vanishing
for `y ≥ 0`. -/
def xiThetaReflectedShiftedHeatProfile (y : ℝ) : ℂ :=
  Complex.ofReal <|
    (Ioi (-1 : ℝ)).indicator
      (thetaLogToShiftedHeat (fun u => (xiThetaReflectedSource u).re)) y

/-- The reflected shifted-heat profile vanishes on the causal half-line. -/
theorem xiThetaReflectedShiftedHeatProfile_eq_zero_of_nonneg
    {y : ℝ} (hy : 0 ≤ y) :
    xiThetaReflectedShiftedHeatProfile y = 0 := by
  have hdomain : y ∈ Ioi (-1 : ℝ) := by
    simpa only [mem_Ioi] using (by linarith : -1 < y)
  have hlog : 0 ≤ Real.log (1 + y) := Real.log_nonneg (by linarith)
  have hsource : xiThetaReflectedSource (Real.log (1 + y)) = 0 := by
    rw [xiThetaReflectedSource, xiThetaPositiveSource, indicator_of_notMem]
    simpa only [mem_Ioi, not_lt] using neg_nonpos.mpr hlog
  simp [xiThetaReflectedShiftedHeatProfile, hdomain, thetaLogToShiftedHeat, hsource]

/-- The reflected shifted-heat profile also vanishes outside the coordinate domain. -/
theorem xiThetaReflectedShiftedHeatProfile_eq_zero_of_le_neg_one
    {y : ℝ} (hy : y ≤ -1) :
    xiThetaReflectedShiftedHeatProfile y = 0 := by
  have hnot : y ∉ Ioi (-1 : ℝ) := by
    simpa only [mem_Ioi, not_lt] using hy
  simp [xiThetaReflectedShiftedHeatProfile, hnot]

/-- If one first reorients the reflected logarithmic half, it is literally the positive half.
This is the alternative to the zero direct action, not a second source datum. -/
theorem xiThetaReflectedSource_reoriented (u : ℝ) :
    xiThetaReflectedSource (-u) = xiThetaPositiveSource u := by
  simp [xiThetaReflectedSource]

/-- Direct reflected-theta action of an `L²` reader in the global shifted heat coordinate. -/
def causalReaderReflectedThetaAction (r : Lp ℂ 2 (volume : Measure ℝ)) : ℂ :=
  ∫ y : ℝ, conj (r y) * xiThetaReflectedShiftedHeatProfile y

/-- Every causal `L²` reader has exactly zero direct action on the reflected theta half. -/
theorem causalReaderReflectedThetaAction_eq_zero
    (r : Lp ℂ 2 (volume : Measure ℝ))
    (hsupp : HasAELowerSupport (fun y : ℝ => r y) 0) :
    causalReaderReflectedThetaAction r = 0 := by
  rw [causalReaderReflectedThetaAction]
  calc
    (∫ y : ℝ, conj (r y) * xiThetaReflectedShiftedHeatProfile y) =
        ∫ _y : ℝ, (0 : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hsupp] with y hreader
      by_cases hy : y < 0
      · rw [hreader hy]
        simp
      · have hy0 : 0 ≤ y := le_of_not_gt hy
        rw [xiThetaReflectedShiftedHeatProfile_eq_zero_of_nonneg hy0, mul_zero]
    _ = 0 := by simp

/-- The canonical square-rate source reader has zero reflected completed-theta action. -/
theorem thetaHeatRateSourceReaderL2_reflectedThetaAction_eq_zero
    {n : ℕ} (hn : 1 ≤ n) :
    causalReaderReflectedThetaAction (thetaHeatRateSourceReaderL2 n hn) = 0 :=
  causalReaderReflectedThetaAction_eq_zero _
    (thetaHeatRateSourceReaderL2_hasAELowerSupport hn)

end RHTower

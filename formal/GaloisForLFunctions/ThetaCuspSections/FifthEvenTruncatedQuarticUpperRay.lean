import GaloisForLFunctions.ThetaCuspSections.FifthEvenQuarticRay
import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossCompactEnvelope
import GaloisForLFunctions.ThetaCuspSections.FifthEvenTruncatedQuarticFlux

/-!
# Positivity of the truncated quartic source from theta scale seven

Before the profile's double zero, the scalar compensation exceeds the
quartic load paid by the native fifth section. Beyond the double zero,
the truncated source is native and positive. The literal weighted source
is therefore positive for every positive aperture from scale seven onward.
-/

noncomputable section
open Matrix

namespace GaloisForLFunctions.ThetaCuspSections.FifthPolynomialCross
open _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit
open EvenFiveEndpoint FifthRemainder FifthNativeRay

/-- The quartic profile pays the complete source from scale seven to its double zero. -/
theorem repair_compact_from_seven_posDef {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) (hx2 : x^2 ≤ 1/2) :
    (repair x).PosDef := by
  have hp := QuarticRayCertificate.native_quartic_reserve_from_seven_posDef hq
  have hs := compensation_compact_quartic_lower_seven (by linarith only [hq]) hx2
  have hB : (crossLoad paidSevenSchur).PosSemidef :=
    crossCoefficient_posDef.posSemidef.conjTranspose_mul_mul_same loadMap
  have he : repair x =
      (nativeShiftedMatrix 5 0 x-
        ((3/20)*sourceUnit x*(thetaCuspSingleAtomReflectionScale 1 x)^4) •
          crossLoad paidSevenSchur)+
      (compensation x+(3/20)*sourceUnit x*(thetaCuspSingleAtomReflectionScale 1 x)^4) •
        crossLoad paidSevenSchur := by
    ext i j
    simp only [repair,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact hp.add_posSemidef (hB.smul (by linarith only [hs]))

/-- The literal weighted quartic source has the same positive compact upper interval. -/
theorem weightedRepair_compact_from_seven_posDef {a r : ℝ} (ha : 0 < a)
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 (r/2)) (hr2 : (r/2)^2 ≤ 1/2) :
    (weightedRepair a r).PosDef := by
  have hx := regimeOne_pos_of_six_le (x := r/2) (by linarith only [hq])
  have hr : 0 < r := by linarith only [hx]
  have hw := mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha hr))
  have hl := deriv_flux_lower ha.le hr.le
  have hB : (crossLoad paidSevenSchur).PosSemidef :=
    crossCoefficient_posDef.posSemidef.conjTranspose_mul_mul_same loadMap
  rw [weightedRepair_decomposition]
  exact ((repair_compact_from_seven_posDef hq hr2).smul hw).add_posSemidef
    (hB.smul (sub_nonneg.mpr hl))

/-- The quartic profile is positive from scale eight to its double zero. -/
theorem repair_compact_upper_posDef {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) (hx2 : x^2 ≤ 1/2) :
    (repair x).PosDef :=
  repair_compact_from_seven_posDef (by linarith only [hq]) hx2

/-- The literal weighted quartic source is positive on the compact scale-eight interval. -/
theorem weightedRepair_compact_upper_posDef {a r : ℝ} (ha : 0 < a)
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 (r/2)) (hr2 : (r/2)^2 ≤ 1/2) :
    (weightedRepair a r).PosDef :=
  weightedRepair_compact_from_seven_posDef ha (by linarith only [hq]) hr2

end GaloisForLFunctions.ThetaCuspSections.FifthPolynomialCross

namespace GaloisForLFunctions.ThetaCuspSections.FifthTruncatedCross
open _root_.RHTower

/-- The complete truncated source is positive from theta scale seven onward. -/
theorem weightedRepair_from_seven_posDef {a r : ℝ} (ha : 0 < a)
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 (r/2)) :
    (weightedRepair a r).PosDef := by
  by_cases hr : r ≤ cutoff
  · have hx := regimeOne_pos_of_six_le (x := r/2) (by linarith only [hq])
    have hr0 : 0 ≤ r := by linarith only [hx]
    have hs := mul_self_le_mul_self hr0 hr
    have hr2 : (r/2)^2 ≤ 1/2 := by nlinarith only [hs,cutoff_sq]
    rw [weightedRepair_eq_inner a hr]
    exact FifthPolynomialCross.weightedRepair_compact_from_seven_posDef ha hq hr2
  · exact weightedRepair_outer_posDef ha (not_le.mp hr).le

/-- The complete truncated source is positive from theta scale eight onward. -/
theorem weightedRepair_from_eight_posDef {a r : ℝ} (ha : 0 < a)
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 (r/2)) :
    (weightedRepair a r).PosDef :=
  weightedRepair_from_seven_posDef ha (by linarith only [hq])

end GaloisForLFunctions.ThetaCuspSections.FifthTruncatedCross

import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaTurningPoints
import Mathlib.Tactic

/-!
# Curvature classification at Jacobi turning points

Exact second derivatives distinguish crests from troughs.  Positive-modulus Region I has a strict
center crest and Jacobi-endpoint trough; negative-modulus Region I reverses them.  Region II has a
strict center trough and endpoint crest.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

abbrev PhysicalRegionIPositiveModulus :=
  {P : PhysicalRegionI // 0 < P.val.modulus}

theorem jacobiSquaredCurvatureVelocity_at_peak
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus)
    (x : JacobiSnPeakPoint J) : jacobiSquaredCurvatureVelocity P.val J x.val = 0 := by
  rw [jacobiSquaredCurvatureVelocity, jacobiSnPeak_cn_zero J x]
  ring

theorem jacobiSquaredCurvatureAcceleration_at_peak
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus)
    (x : JacobiSnPeakPoint J) :
    jacobiSquaredCurvatureAcceleration P.val J x.val =
      2 * P.val.modulus * (1 - P.val.modulus) := by
  have hdn : J.dn x.val ^ (2 : ℕ) = 1 - P.val.modulus := by
    nlinarith [J.dn_sq_add_m_sn_sq x.val, x.sn_sq]
  rw [jacobiSquaredCurvatureAcceleration, jacobiSnPeak_cn_zero J x]
  rw [show (J.sn x.val * J.dn x.val) ^ (2 : ℕ) = J.sn x.val ^ (2 : ℕ) * J.dn x.val ^ (2 : ℕ) by ring,
    x.sn_sq, hdn]
  ring

theorem correctedJacobiAmplitudeAcceleration_at_peak
    (P : PhysicalRegionI) (J : JacobiEllipticSystem P.val.modulus)
    (x : JacobiSnPeakPoint J) :
    correctedJacobiAmplitudeAcceleration P J x.val =
      P.val.modulus * (1 - P.val.modulus) /
        ((P.val.q₀ : ℝ) * correctedJacobiAmplitude P J x.val) := by
  rw [correctedJacobiAmplitudeAcceleration,
    jacobiSquaredCurvatureAcceleration_at_peak,
    jacobiSquaredCurvatureVelocity_at_peak]
  ring

theorem regionIPositiveAmplitudeAcceleration_center_neg
    (P : PhysicalRegionIPositiveModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) :
    correctedJacobiAmplitudeAcceleration P.val J 0 < 0 := by
  rw [correctedJacobiAmplitudeAcceleration_zero]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr P.property) P.val.property.1

theorem regionIPositiveAmplitudeAcceleration_peak_pos
    (P : PhysicalRegionIPositiveModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (x : JacobiSnPeakPoint J) :
    0 < correctedJacobiAmplitudeAcceleration P.val J x.val := by
  rw [correctedJacobiAmplitudeAcceleration_at_peak]
  have hm1 : 0 < 1 - P.val.val.modulus := by
    linarith [(physicalRegionI_bounds P.val).2.1]
  exact div_pos (mul_pos P.property hm1)
    (mul_pos P.val.property.1 (correctedJacobiAmplitude_pos P.val J x.val))

theorem regionINegativeAmplitudeAcceleration_center_pos
    (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) :
    0 < correctedJacobiAmplitudeAcceleration P.val J 0 := by
  rw [correctedJacobiAmplitudeAcceleration_zero]
  exact div_pos (neg_pos.mpr P.property) P.val.property.1

theorem regionINegativeAmplitudeAcceleration_peak_neg
    (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (x : JacobiSnPeakPoint J) :
    correctedJacobiAmplitudeAcceleration P.val J x.val < 0 := by
  rw [correctedJacobiAmplitudeAcceleration_at_peak]
  have hm1 : 0 < 1 - P.val.val.modulus := by linarith [P.property]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos P.property hm1)
    (mul_pos P.val.property.1 (correctedJacobiAmplitude_pos P.val J x.val))

theorem jacobiSdVelocity_at_peak
    (m : ClassicalModulus) (J : JacobiEllipticSystem (m : ℝ))
    (x : JacobiSnPeakPoint J) : jacobiSdVelocity J x.val = 0 := by
  rw [jacobiSdVelocity, jacobiSnPeak_cn_zero J x]
  ring

theorem regionIIJacobiSquaredCurvatureAcceleration_at_peak
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) :
    regionIIJacobiSquaredCurvatureAcceleration P J x.val =
      -2 * (regionIIComplementModulus P : ℝ) := by
  rw [regionIIJacobiSquaredCurvatureAcceleration,
    jacobiSdVelocity_at_peak (regionIIComplementModulus P) J x,
    jacobiSdAcceleration]
  have hsd := jacobiSd_sq_at_peak (regionIIComplementModulus P) J x
  have hgap : 1 - (regionIIComplementModulus P : ℝ) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (regionIIComplementModulus P).property.2)
  have hprod : (1 - (regionIIComplementModulus P : ℝ)) *
      jacobiSd J x.val ^ (2 : ℕ) = 1 := by
    rw [hsd]
    field_simp [hgap]
  calc
    2 * (regionIIComplementModulus P : ℝ) *
        (1 - (regionIIComplementModulus P : ℝ)) *
        (0 ^ (2 : ℕ) + jacobiSd J x.val *
          ((2 * (regionIIComplementModulus P : ℝ) - 1) * jacobiSd J x.val -
            2 * (regionIIComplementModulus P : ℝ) *
              (1 - (regionIIComplementModulus P : ℝ)) * jacobiSd J x.val ^ (3 : ℕ))) =
      2 * (regionIIComplementModulus P : ℝ) *
        ((1 - (regionIIComplementModulus P : ℝ)) * jacobiSd J x.val ^ (2 : ℕ)) *
        ((2 * (regionIIComplementModulus P : ℝ) - 1) -
          2 * (regionIIComplementModulus P : ℝ) *
            ((1 - (regionIIComplementModulus P : ℝ)) * jacobiSd J x.val ^ (2 : ℕ))) := by ring
    _ = -2 * (regionIIComplementModulus P : ℝ) := by rw [hprod]; ring

theorem regionIIJacobiAmplitudeAcceleration_at_peak
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) :
    regionIIJacobiAmplitudeAcceleration P J x.val =
      -(regionIIComplementModulus P : ℝ) /
        (regionIIRealScale P * regionIIJacobiAmplitude P J x.val) := by
  rw [regionIIJacobiAmplitudeAcceleration,
    regionIIJacobiSquaredCurvatureAcceleration_at_peak,
    regionIIJacobiSquaredCurvatureVelocity]
  rw [sdSquaredCurvatureVelocity,
    jacobiSdVelocity_at_peak (regionIIComplementModulus P) J x]
  ring

theorem regionIIJacobiAmplitudeAcceleration_peak_neg
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) :
    regionIIJacobiAmplitudeAcceleration P J x.val < 0 := by
  rw [regionIIJacobiAmplitudeAcceleration_at_peak]
  exact div_neg_of_neg_of_pos
    (neg_lt_zero.mpr (regionIIComplementModulus P).property.1)
    (mul_pos (regionIIRealScale_pos P) (regionIIJacobiAmplitude_pos P J x.val))

theorem regionIPositivePhysicalCurvature_center_acceleration_neg
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionIPositiveModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) :
    physicalJacobiCurvatureAcceleration k₀ P.val J 0 < 0 := by
  rw [physicalJacobiCurvatureAcceleration, physicalJacobiArgument, mul_zero]
  exact mul_neg_of_pos_of_neg
    (mul_pos k₀.property (sq_pos_of_pos (jacobiArclengthScale_pos k₀ P.val)))
    (regionIPositiveAmplitudeAcceleration_center_neg P J)

theorem regionIPositivePhysicalCurvature_peak_acceleration_pos
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionIPositiveModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (x : JacobiSnPeakPoint J) :
    0 < physicalJacobiCurvatureAcceleration k₀ P.val J
      (regionIPhysicalPeakLocation k₀ P.val J x) := by
  rw [physicalJacobiCurvatureAcceleration, regionIPhysicalPeak_argument]
  exact mul_pos
    (mul_pos k₀.property (sq_pos_of_pos (jacobiArclengthScale_pos k₀ P.val)))
    (regionIPositiveAmplitudeAcceleration_peak_pos P J x)

theorem regionINegativePhysicalCurvature_center_acceleration_pos
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) :
    0 < physicalJacobiCurvatureAcceleration k₀ P.val J 0 := by
  rw [physicalJacobiCurvatureAcceleration, physicalJacobiArgument, mul_zero]
  exact mul_pos
    (mul_pos k₀.property (sq_pos_of_pos (jacobiArclengthScale_pos k₀ P.val)))
    (regionINegativeAmplitudeAcceleration_center_pos P J)

theorem regionINegativePhysicalCurvature_peak_acceleration_neg
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) (x : JacobiSnPeakPoint J) :
    physicalJacobiCurvatureAcceleration k₀ P.val J
      (regionIPhysicalPeakLocation k₀ P.val J x) < 0 := by
  rw [physicalJacobiCurvatureAcceleration, regionIPhysicalPeak_argument]
  exact mul_neg_of_pos_of_neg
    (mul_pos k₀.property (sq_pos_of_pos (jacobiArclengthScale_pos k₀ P.val)))
    (regionINegativeAmplitudeAcceleration_peak_neg P J x)

theorem regionIIPhysicalCurvature_peak_acceleration_neg
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) :
    regionIIPhysicalCurvatureAcceleration k₀ P J
      (regionIIPhysicalPeakLocation k₀ P J x) < 0 := by
  rw [regionIIPhysicalCurvatureAcceleration, compiledCurvatureAcceleration,
    regionIIPhysicalPeak_argument]
  exact mul_neg_of_pos_of_neg
    (mul_pos k₀.property
      (sq_pos_of_pos (compiledArclengthScale_pos k₀ (regionIIAmplitudeOscillator P J))))
    (regionIIJacobiAmplitudeAcceleration_peak_neg P J x)

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaRegionIIHydrodynamics
import Mathlib.Tactic

/-!
# Sharp bounds for the Region II `sd` curvature

The Jacobi identities alone imply `sd² ≤ 1/(1-m)` in the classical chamber.  Applied to the
paper's Region II transform, this proves its exact global curvature range and identifies peak
points without requiring a separate analytic construction of the period lattice.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

theorem classicalJacobiSd_sq_le
    (m : ClassicalModulus) (J : JacobiEllipticSystem (m : ℝ)) (x : ℝ) :
    jacobiSd J x ^ 2 ≤ 1 / (1 - (m : ℝ)) := by
  have hdn := classicalJacobiDn_sq_pos m J x
  have hgap : 0 < 1 - (m : ℝ) := sub_pos.mpr m.property.2
  have haux :
      (1 - (m : ℝ)) * J.sn x ^ 2 ≤ J.dn x ^ 2 := by
    have hquad := J.dn_sq_add_m_sn_sq x
    have hsn := J.sn_sq_le_one x
    nlinarith
  rw [jacobiSd, div_pow]
  apply (div_le_iff₀ hdn).2
  rw [show 1 / (1 - (m : ℝ)) * J.dn x ^ 2 =
      J.dn x ^ 2 / (1 - (m : ℝ)) by ring]
  exact (le_div_iff₀ hgap).2 (by simpa [mul_comm] using haux)

theorem classicalJacobiSd_sq_eq_upper_iff
    (m : ClassicalModulus) (J : JacobiEllipticSystem (m : ℝ)) (x : ℝ) :
    jacobiSd J x ^ 2 = 1 / (1 - (m : ℝ)) ↔ J.sn x ^ 2 = 1 := by
  have hdn := classicalJacobiDn_sq_pos m J x
  have hgap : 0 < 1 - (m : ℝ) := sub_pos.mpr m.property.2
  rw [jacobiSd, div_pow]
  constructor
  · intro h
    have hquad := J.dn_sq_add_m_sn_sq x
    have hcross := (div_eq_div_iff (ne_of_gt hdn) (ne_of_gt hgap)).1 h
    norm_num at hcross
    nlinarith
  · intro hsn
    have hquad := J.dn_sq_add_m_sn_sq x
    apply (div_eq_div_iff (ne_of_gt hdn) (ne_of_gt hgap)).2
    norm_num
    nlinarith

theorem regionIIJacobiAmplitude_sq_lower
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    1 ≤ regionIIJacobiAmplitude P J x ^ 2 := by
  rw [regionIIJacobiAmplitude_sq]
  have hn := regionIITransformedModulus_pos P
  have hq := neg_pos.mpr P.property.1
  have hsd := sq_nonneg (jacobiSd J x)
  have hcoef : 0 ≤ regionIITransformedModulus P / (-(P.val.q₀ : ℝ)) :=
    (div_pos hn hq).le
  nlinarith [mul_nonneg hcoef hsd]

theorem regionIIJacobiAmplitude_sq_upper
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    regionIIJacobiAmplitude P J x ^ 2 ≤
      1 + 1 / (-(P.val.q₀ : ℝ)) := by
  rw [regionIIJacobiAmplitude_sq]
  have hn := regionIITransformedModulus_pos P
  have hq := neg_pos.mpr P.property.1
  have hsd := classicalJacobiSd_sq_le (regionIIComplementModulus P) J x
  have hcomp :
      1 - (regionIIComplementModulus P : ℝ) =
        regionIITransformedModulus P := rfl
  rw [hcomp] at hsd
  have hcoef : 0 ≤ regionIITransformedModulus P / (-(P.val.q₀ : ℝ)) :=
    (div_pos hn hq).le
  have hmul := mul_le_mul_of_nonneg_left hsd hcoef
  have hcollapse :
      regionIITransformedModulus P / (-(P.val.q₀ : ℝ)) *
          (1 / regionIITransformedModulus P) =
        1 / (-(P.val.q₀ : ℝ)) := by
    field_simp [ne_of_gt hn, ne_of_gt hq]
  rw [hcollapse] at hmul
  linarith

/-- Paper's Region II origin is a global curvature minimum. -/
theorem regionIIPhysicalCurvature_sq_lower
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (s : ℝ) :
    (k₀ : ℝ) ^ 2 ≤ regionIIPhysicalCurvature k₀ P J s ^ 2 := by
  rw [regionIIPhysicalCurvature, compiledCurvature, mul_pow]
  change (k₀ : ℝ) ^ 2 ≤ (k₀ : ℝ) ^ 2 *
    regionIIJacobiAmplitude P J
      (compiledArgument k₀ (regionIIAmplitudeOscillator P J) s) ^ 2
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (regionIIJacobiAmplitude_sq_lower P J
      (compiledArgument k₀ (regionIIAmplitudeOscillator P J) s))
    (sq_nonneg (k₀ : ℝ))

/-- Paper's exact Region II upper curvature bound. -/
theorem regionIIPhysicalCurvature_sq_upper
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (s : ℝ) :
    regionIIPhysicalCurvature k₀ P J s ^ 2 ≤
      (k₀ : ℝ) ^ 2 * (1 + 1 / (-(P.val.q₀ : ℝ))) := by
  rw [regionIIPhysicalCurvature, compiledCurvature, mul_pow]
  change (k₀ : ℝ) ^ 2 *
      regionIIJacobiAmplitude P J
        (compiledArgument k₀ (regionIIAmplitudeOscillator P J) s) ^ 2 ≤ _
  exact mul_le_mul_of_nonneg_left
    (regionIIJacobiAmplitude_sq_upper P J
      (compiledArgument k₀ (regionIIAmplitudeOscillator P J) s))
    (sq_nonneg (k₀ : ℝ))

theorem regionIIPhysicalDensity_lower
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    (k₀ : ℝ) ^ 2 ≤ regionIIPhysicalDensity D k₀ P J t s := by
  rw [regionIIPhysicalDensity, compiledTravelingDensity_eq_curvature_sq]
  exact regionIIPhysicalCurvature_sq_lower k₀ P J _

theorem regionIIPhysicalDensity_upper
    (D : ℝˣ) (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (t s : ℝ) :
    regionIIPhysicalDensity D k₀ P J t s ≤
      (k₀ : ℝ) ^ 2 * (1 + 1 / (-(P.val.q₀ : ℝ))) := by
  rw [regionIIPhysicalDensity, compiledTravelingDensity_eq_curvature_sq]
  exact regionIIPhysicalCurvature_sq_upper k₀ P J _

/-- A certified Jacobi half-period peak, packaged as data instead of a theorem premise. -/
structure JacobiSnPeakPoint {m : ℝ} (J : JacobiEllipticSystem m) where
  val : ℝ
  sn_sq : J.sn val ^ 2 = 1

theorem jacobiSd_sq_at_peak
    (m : ClassicalModulus) (J : JacobiEllipticSystem (m : ℝ))
    (x : JacobiSnPeakPoint J) :
    jacobiSd J x.val ^ 2 = 1 / (1 - (m : ℝ)) :=
  (classicalJacobiSd_sq_eq_upper_iff m J x.val).2 x.sn_sq

theorem regionIIJacobiAmplitude_sq_at_peak
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) :
    regionIIJacobiAmplitude P J x.val ^ 2 =
      1 + 1 / (-(P.val.q₀ : ℝ)) := by
  rw [regionIIJacobiAmplitude_sq, jacobiSd_sq_at_peak]
  have hn := regionIITransformedModulus_pos P
  have hq := neg_pos.mpr P.property.1
  change 1 + regionIITransformedModulus P / (-(P.val.q₀ : ℝ)) *
      (1 / regionIITransformedModulus P) = _
  field_simp [ne_of_gt hn, ne_of_gt hq]

noncomputable def regionIIPhysicalPeakLocation
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) : ℝ :=
  x.val / compiledArclengthScale k₀ (regionIIAmplitudeOscillator P J)

theorem regionIIPhysicalPeak_argument
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) :
    compiledArgument k₀ (regionIIAmplitudeOscillator P J)
      (regionIIPhysicalPeakLocation k₀ P J x) = x.val := by
  rw [compiledArgument, regionIIPhysicalPeakLocation]
  field_simp [ne_of_gt
    (compiledArclengthScale_pos k₀ (regionIIAmplitudeOscillator P J))]

theorem regionIIPhysicalCurvature_sq_at_peak
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ))
    (x : JacobiSnPeakPoint J) :
    regionIIPhysicalCurvature k₀ P J
        (regionIIPhysicalPeakLocation k₀ P J x) ^ 2 =
      (k₀ : ℝ) ^ 2 * (1 + 1 / (-(P.val.q₀ : ℝ))) := by
  rw [regionIIPhysicalCurvature_sq, regionIIPhysicalPeak_argument,
    jacobiSd_sq_at_peak]
  have hn := regionIITransformedModulus_pos P
  have hq := neg_pos.mpr P.property.1
  change (k₀ : ℝ) ^ 2 *
      (1 + regionIITransformedModulus P / (-(P.val.q₀ : ℝ)) *
        (1 / regionIITransformedModulus P)) = _
  field_simp [ne_of_gt hn, ne_of_gt hq]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

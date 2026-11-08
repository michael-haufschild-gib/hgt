import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePolarSourceIsContinuousInTheWeightedNorm

/-!
# Physical window weights recover their profiles

Inverse half-weighting identifies smooth coefficient windows with physical profiles.
The weighted coefficient mass and signed polar source retain their exact constants.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis
  CriticalArithmeticCorrelationTheory WindowTowerOfSpecZ

/-- The coefficient window whose physical half-weight is the prescribed profile. -/
def physicalWindowWeights (F : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.exp (-u / 2) * F u / (∫ v, tiltedUnitSpline v)

lemma contDiff_physicalWindowWeights {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 2 (physicalWindowWeights F) :=
  ((Real.contDiff_exp.comp (contDiff_id.neg.div_const 2)).mul hF).div_const _

lemma physicalWindowWeights_vanish {F : ℝ → ℝ} {A : ℝ}
    (hs : ∀ u, u ∉ Set.Icc (-A) 0 → F u = 0) :
    ∀ u, u ∉ Set.Icc (-A) 0 → physicalWindowWeights F u = 0 := by
  intro u hu
  simp only [physicalWindowWeights, hs u hu, mul_zero, zero_div]

lemma physicalWindowWeights_halfWeight (F : ℝ → ℝ) (u : ℝ) :
    (∫ v, tiltedUnitSpline v) * halfWeight (physicalWindowWeights F) u = F u := by
  unfold halfWeight physicalWindowWeights
  have he : Real.exp (u / 2) * Real.exp (-u / 2) = 1 := by
    rw [← Real.exp_add, show u / 2 + -u / 2 = 0 by ring, Real.exp_zero]
  calc
    _ = (Real.exp (u / 2) * Real.exp (-u / 2)) * F u := by
      field_simp [integral_tiltedUnitSpline_ne_zero]
    _ = _ := by rw [he, one_mul]

/-- The coefficient seventh mass is the physical eighth mass divided by the squared atom mass. -/
theorem integral_weighted_physicalWindowWeights_sq (F : ℝ → ℝ) :
    (∫ u, Real.exp (-(7 * u)) * physicalWindowWeights F u ^ 2) =
      exponentialMass 8 F / (∫ v, tiltedUnitSpline v) ^ 2 := by
  have he (u : ℝ) : Real.exp (-(7 * u)) * physicalWindowWeights F u ^ 2 =
      (Real.exp (-(8 * u)) * F u ^ 2) / (∫ v, tiltedUnitSpline v) ^ 2 := by
    unfold physicalWindowWeights
    rw [div_pow, mul_pow, pow_two (Real.exp _)]
    have hx : Real.exp (-(7 * u)) * (Real.exp (-u / 2) * Real.exp (-u / 2)) =
        Real.exp (-(8 * u)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.exp (-(7 * u)) * (Real.exp (-u / 2) * Real.exp (-u / 2))) * F u ^ 2 /
          (∫ v, tiltedUnitSpline v) ^ 2 := by ring
      _ = _ := by rw [hx]
  simp only [he, integral_div, exponentialMass]

/-- The exact signed polar source in physical coordinates. -/
theorem generalTerminalPolarSource_physicalWindowWeights {F : ℝ → ℝ} {A : ℝ}
    (hF : ContDiff ℝ 2 F) (hA : 0 ≤ A)
    (hs : ∀ u, u ∉ Set.Icc (-A) 0 → F u = 0) :
    generalTerminalPolarSource A (physicalWindowWeights F) =
      ((∫ v, tiltedUnitSpline v) / (∫ v, tiltedUnitSpline v ^ 2)) *
        ∫ u, F u * polarSourceProfile u := by
  rw [generalTerminalPolarSource_eq_integral_polarSourceProfile
    (contDiff_physicalWindowWeights hF) hA (physicalWindowWeights_vanish hs)]
  have he (u : ℝ) : halfWeight (physicalWindowWeights F) u =
      F u / (∫ v, tiltedUnitSpline v) := by
    have hh := physicalWindowWeights_halfWeight F u
    apply (eq_div_iff integral_tiltedUnitSpline_ne_zero).mpr
    simpa only [mul_comm] using hh
  simp only [he, div_mul_eq_mul_div, integral_div]
  unfold splineAtom
  field_simp [integral_tiltedUnitSpline_ne_zero, integral_tiltedUnitSpline_sq_pos.ne']

#print axioms integral_weighted_physicalWindowWeights_sq
#print axioms generalTerminalPolarSource_physicalWindowWeights
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

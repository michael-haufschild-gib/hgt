import GaloisForLFunctions.HTGeometry.Thermodynamics.AdSGaussBonnetBoundary

/-!
# The full charged critical curve and its global minimum

The critical edge of arXiv:2611.16364 has squared radius between `1/6`
and `1/3`. An angular coordinate includes both endpoints. At every point
of this curve the entire potential gap factors into a fourth power and
a positive quadratic, proving global uniqueness among positive radii.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.AdSGaussBonnet

def criticalCurveRadius (θ : ℝ) : ℝ := Real.sqrt ((1 + Real.sin θ ^ 2) / 6)
def criticalCurveCoupling (θ : ℝ) : ℝ :=
  5 * criticalCurveRadius θ ^ 2 * (1 - 3 * criticalCurveRadius θ ^ 2) /
    (6 * (9 * criticalCurveRadius θ ^ 2 + 1))
def criticalCurveCharge (θ : ℝ) : ℝ :=
  Real.sqrt (criticalCurveRadius θ ^ 4 * (6 * criticalCurveRadius θ ^ 2 - 1) / 5)
def criticalCurveTemperature (θ : ℝ) : ℝ :=
  (9 * criticalCurveRadius θ ^ 2 + 1) / (5 * Real.pi * criticalCurveRadius θ)
def criticalCurveMinimum (θ : ℝ) : ℝ :=
  3 * criticalCurveCoupling θ + 9 * criticalCurveRadius θ ^ 4 - 2 * criticalCurveRadius θ ^ 2

theorem criticalCurveRadius_pos (θ : ℝ) : 0 < criticalCurveRadius θ := by
  unfold criticalCurveRadius
  exact Real.sqrt_pos.mpr (by positivity)

theorem criticalCurveRadius_sq (θ : ℝ) :
    criticalCurveRadius θ ^ 2 = (1 + Real.sin θ ^ 2) / 6 := by
  unfold criticalCurveRadius
  exact Real.sq_sqrt (by positivity)

theorem criticalCurveRadius_bounds (θ : ℝ) :
    1 / 6 ≤ criticalCurveRadius θ ^ 2 ∧ criticalCurveRadius θ ^ 2 ≤ 1 / 3 := by
  rw [criticalCurveRadius_sq]
  constructor
  · nlinarith only [sq_nonneg (Real.sin θ)]
  · nlinarith only [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]

theorem criticalCurveCoupling_bounds (θ : ℝ) :
    0 ≤ criticalCurveCoupling θ ∧ criticalCurveCoupling θ ≤ 1 / 36 := by
  have hs := criticalCurveRadius_bounds θ
  have hden : 0 < 6 * (9 * criticalCurveRadius θ ^ 2 + 1) := by positivity
  unfold criticalCurveCoupling
  constructor
  · exact div_nonneg (mul_nonneg (by positivity) (by linarith only [hs.2])) hden.le
  · apply (div_le_iff₀ hden).mpr
    have h₁ : 0 ≤ 6 * criticalCurveRadius θ ^ 2 - 1 := by linarith only [hs.1]
    have h₂ : 0 ≤ 15 * criticalCurveRadius θ ^ 2 - 1 := by linarith only [hs.1]
    nlinarith only [mul_nonneg h₁ h₂]

theorem criticalCurveCharge_sq (θ : ℝ) :
    criticalCurveCharge θ ^ 2 =
      criticalCurveRadius θ ^ 4 * (6 * criticalCurveRadius θ ^ 2 - 1) / 5 := by
  unfold criticalCurveCharge
  apply Real.sq_sqrt
  have hs : 0 ≤ 6 * criticalCurveRadius θ ^ 2 - 1 := by
    linarith only [(criticalCurveRadius_bounds θ).1]
  positivity

theorem criticalCurveTemperature_pos (θ : ℝ) : 0 < criticalCurveTemperature θ := by
  unfold criticalCurveTemperature
  have hr := criticalCurveRadius_pos θ
  positivity

theorem criticalCurve_temperature_value (θ : ℝ) :
    temperature (criticalCurveCoupling θ) (criticalCurveCharge θ) (criticalCurveRadius θ) =
      criticalCurveTemperature θ := by
  have hden : criticalCurveRadius θ ^ 2 + 2 * criticalCurveCoupling θ ≠ 0 := by
    have hr := criticalCurveRadius_pos θ
    have hl := (criticalCurveCoupling_bounds θ).1
    positivity
  unfold temperature
  rw [criticalCurveCharge_sq]
  unfold criticalCurveTemperature
  field_simp [hden, (criticalCurveRadius_pos θ).ne']
  unfold criticalCurveCoupling
  have hd : 9 * criticalCurveRadius θ ^ 2 + 1 ≠ 0 := by positivity
  field_simp [hd]
  ring

def criticalQuarticFactor (θ x : ℝ) : ℝ :=
  x ^ 2 + 4 * (6 * criticalCurveRadius θ ^ 2 - 1) / (15 * criticalCurveRadius θ) * x +
    (6 * criticalCurveRadius θ ^ 2 - 1) / 15

theorem criticalQuarticFactor_pos (θ u : ℝ) : 0 < criticalQuarticFactor θ (Real.exp u) := by
  have hs : 0 ≤ 6 * criticalCurveRadius θ ^ 2 - 1 := by
    linarith only [(criticalCurveRadius_bounds θ).1]
  have hr := criticalCurveRadius_pos θ
  unfold criticalQuarticFactor
  positivity

/-- The quartic normal form is an exact global factorization along the whole critical edge. -/
theorem criticalCurve_potential_gap (θ u : ℝ) :
    potential (criticalCurveTemperature θ) 0 (criticalCurveCoupling θ)
        (criticalCurveCharge θ) (Real.exp u) - criticalCurveMinimum θ =
      3 * (Real.exp u - criticalCurveRadius θ) ^ 4 * criticalQuarticFactor θ (Real.exp u) /
        Real.exp u ^ 2 := by
  unfold potential energy entropy criticalCurveMinimum
  rw [criticalCurveCharge_sq]
  unfold criticalCurveTemperature criticalCurveCoupling criticalQuarticFactor
  have hd : 9 * criticalCurveRadius θ ^ 2 + 1 ≠ 0 := by positivity
  field_simp [(criticalCurveRadius_pos θ).ne', hd]
  ring

theorem criticalCurve_global_lower_bound (θ u : ℝ) :
    criticalCurveMinimum θ ≤ potential (criticalCurveTemperature θ) 0
      (criticalCurveCoupling θ) (criticalCurveCharge θ) (Real.exp u) := by
  apply sub_nonneg.mp
  rw [criticalCurve_potential_gap]
  have h := criticalQuarticFactor_pos θ u
  positivity

/-- No additional positive-radius minimum occurs anywhere on the critical curve. -/
theorem criticalCurve_unique_minimizer (θ u : ℝ) :
    potential (criticalCurveTemperature θ) 0 (criticalCurveCoupling θ)
        (criticalCurveCharge θ) (Real.exp u) = criticalCurveMinimum θ ↔
      Real.exp u = criticalCurveRadius θ := by
  rw [← sub_eq_zero, criticalCurve_potential_gap, div_eq_zero_iff]
  simp only [pow_ne_zero 2 (Real.exp_ne_zero u), or_false,
    mul_eq_zero, (criticalQuarticFactor_pos θ u).ne',
    show (3 : ℝ) ≠ 0 by norm_num, false_or,
    pow_eq_zero_iff (by norm_num : 4 ≠ 0), sub_eq_zero]

theorem criticalCurve_minimum_attained (θ : ℝ) :
    potential (criticalCurveTemperature θ) 0 (criticalCurveCoupling θ)
      (criticalCurveCharge θ) (criticalCurveRadius θ) = criticalCurveMinimum θ := by
  unfold potential energy entropy criticalCurveMinimum
  rw [criticalCurveCharge_sq]
  unfold criticalCurveTemperature criticalCurveCoupling
  have hd : 9 * criticalCurveRadius θ ^ 2 + 1 ≠ 0 := by positivity
  field_simp [(criticalCurveRadius_pos θ).ne', hd]
  ring

#print axioms criticalCurveCoupling_bounds
#print axioms criticalCurve_potential_gap
#print axioms criticalCurve_unique_minimizer
#print axioms criticalCurve_minimum_attained

end GaloisForLFunctions.HTGeometry.AdSGaussBonnet

import GaloisForLFunctions.HTGeometry.EinastoRadialGravity

/-!
# Einasto anisotropic pressures and sharp energy-condition radii

Applies equation (12) of arXiv:2608.23600v1 to the density and its proved
derivative. The radial conservation identity, null-energy inequalities, and
central `w=-1` limit follow exactly. Dominant and strong energy inequalities
have explicit radius thresholds for every positive shape and length scale.

A further consequence identifies the tangential dominant-energy region with
the nonpositive-Ricci region in the paper's sign convention. This is an algebraic
classification of the stated fluid components, not a spacetime tensor theorem.
-/

noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

def einastoRadialPressure (d l a r : ℝ) : ℝ := -einastoDensity d l a r

def einastoTangentialPressure (d l a r : ℝ) : ℝ :=
  -einastoDensity d l a r + einastoSlope d l a r / 2

def einastoPressureThreshold (l a c : ℝ) : ℝ := l + exp a * (c + a)

theorem einastoSlope_exponential (d l a t : ℝ) :
    einastoSlope d l a (exp t) =
      exp (-a + (t - l) * exp (-a)) * einastoDensity d l a (exp t) := by
  unfold einastoSlope
  rw [← exp_sub, ← exp_mul, ← exp_add]

theorem einastoSlope_pos (d l a t : ℝ) : 0 < einastoSlope d l a (exp t) := by
  rw [einastoSlope_exponential]
  exact mul_pos (exp_pos _) (einastoDensity_pos d l a (exp t))

theorem einastoPressureThreshold_scaled (l a c t : ℝ) :
    -a + (t - l) * exp (-a) ≤ c ↔ t ≤ einastoPressureThreshold l a c := by
  rw [einastoPressureThreshold, exp_neg]
  have hp := exp_pos a
  constructor <;> intro h
  · have h' := (mul_le_mul_iff_right₀ hp).mpr h
    field_simp at h'
    nlinarith
  · apply (mul_le_mul_iff_right₀ hp).mp
    field_simp
    nlinarith

theorem einastoSlope_le_density_iff (d l a c t : ℝ) :
    einastoSlope d l a (exp t) ≤ exp c * einastoDensity d l a (exp t) ↔
      t ≤ einastoPressureThreshold l a c := by
  rw [einastoSlope_exponential, mul_le_mul_iff_left₀ (einastoDensity_pos d l a (exp t)),
    exp_le_exp]
  exact einastoPressureThreshold_scaled l a c t

theorem einastoRadialPressure_derivative (d l a t : ℝ) :
    HasDerivAt (einastoRadialPressure d l a)
      (einastoSlope d l a (exp t) / exp t) (exp t) := by
  change HasDerivAt (fun r => -einastoDensity d l a r) _ _
  have h := (einastoDensity_derivative d l a t).neg
  exact h.congr_deriv (by ring)

theorem einastoPressure_conservation (d l a t : ℝ) :
    deriv (einastoRadialPressure d l a) (exp t) =
      -2 / exp t * (einastoRadialPressure d l a (exp t) - einastoTangentialPressure d l a (exp t)) := by
  rw [(einastoRadialPressure_derivative d l a t).deriv]
  unfold einastoRadialPressure einastoTangentialPressure
  ring

theorem einastoRadial_null_energy (d l a r : ℝ) :
    einastoDensity d l a r + einastoRadialPressure d l a r = 0 := by
  simp [einastoRadialPressure]

theorem einastoTangential_null_energy (d l a t : ℝ) :
    0 < einastoDensity d l a (exp t) + einastoTangentialPressure d l a (exp t) := by
  unfold einastoTangentialPressure
  linarith [einastoSlope_pos d l a t]

theorem einastoRadial_dominant_energy (d l a r : ℝ) :
    |einastoRadialPressure d l a r| = einastoDensity d l a r := by
  rw [einastoRadialPressure, abs_neg, abs_of_pos (einastoDensity_pos d l a r)]

/-- A sharp outer radius for the tangential dominant-energy inequality. -/
theorem einastoTangential_dominant_energy_iff (d l a t : ℝ) :
    |einastoTangentialPressure d l a (exp t)| ≤ einastoDensity d l a (exp t) ↔
      t ≤ einastoPressureThreshold l a (log 4) := by
  have hs := einastoSlope_pos d l a t
  have h := einastoSlope_le_density_iff d l a (log 4) t
  rw [exp_log (by norm_num : (0 : ℝ) < 4)] at h
  rw [← h, abs_le]
  unfold einastoTangentialPressure
  constructor
  · intro h
    linarith [h.2]
  · intro h
    constructor <;> linarith

/-- Outside the sharp radius, the tangential pressure exceeds the density. -/
theorem einastoTangential_dominant_energy_failure (d l a u : ℝ) :
    einastoDensity d l a (exp (einastoPressureThreshold l a (log 4) + exp u)) <
      |einastoTangentialPressure d l a (exp (einastoPressureThreshold l a (log 4) + exp u))| := by
  apply lt_of_not_ge
  rw [einastoTangential_dominant_energy_iff]
  linarith [exp_pos u]

/-- The central pressure becomes isotropic with equation of state `w=-1`. -/
theorem einastoPressure_core_limit (d l a : ℝ) :
    Filter.Tendsto (einastoTangentialPressure d l a) (nhds 0) (nhds (-exp d)) := by
  have hd := (einastoDensity_continuous d l a).continuousAt.tendsto (x := 0)
  have hs := (einastoSlope_continuous d l a).continuousAt.tendsto (x := 0)
  rw [einastoDensity_zero] at hd
  rw [einastoSlope_zero] at hs
  change Filter.Tendsto (fun r => -einastoDensity d l a r + einastoSlope d l a r / 2) _ _
  simpa only [zero_div, add_zero] using hd.neg.add (hs.div_const 2)

theorem einastoPressureThreshold_lower_scaled (l a c t : ℝ) :
    c ≤ -a + (t - l) * exp (-a) ↔ einastoPressureThreshold l a c ≤ t := by
  rw [einastoPressureThreshold, exp_neg]
  have hp := exp_pos a
  constructor <;> intro h
  · have h' := (mul_le_mul_iff_right₀ hp).mpr h
    field_simp at h'
    nlinarith
  · apply (mul_le_mul_iff_right₀ hp).mp
    field_simp
    nlinarith

/-- The strong-energy inequality has a sharp inner radius. -/
theorem einasto_strong_energy_iff (d l a t : ℝ) :
    0 ≤ einastoDensity d l a (exp t) + einastoRadialPressure d l a (exp t) +
      2 * einastoTangentialPressure d l a (exp t) ↔
      einastoPressureThreshold l a (log 2) ≤ t := by
  have hd := einastoDensity_pos d l a (exp t)
  have he : (2 : ℝ) ≤ exp (-a + (t - l) * exp (-a)) ↔
      einastoPressureThreshold l a (log 2) ≤ t := by
    rw [← exp_log (by norm_num : (0 : ℝ) < 2), exp_le_exp]
    simpa only [log_exp] using einastoPressureThreshold_lower_scaled l a (log 2) t
  rw [← he]
  unfold einastoRadialPressure einastoTangentialPressure
  rw [einastoSlope_exponential]
  constructor <;> intro h
  · nlinarith
  · nlinarith

/-- In the paper's convention, nonpositive Ricci is exactly the dominant-energy region. -/
theorem einasto_dominant_energy_iff_Ricci_nonpos (d l a t : ℝ) :
    |einastoTangentialPressure d l a (exp t)| ≤ einastoDensity d l a (exp t) ↔
      einastoRadialRicci d l a (exp t) ≤ 0 := by
  have hs := einastoSlope_pos d l a t
  rw [abs_le, einastoRadialRicci_eq]
  unfold einastoTangentialPressure
  have hp := Real.pi_pos
  constructor
  · intro h
    have h' : einastoSlope d l a (exp t) - 4 * einastoDensity d l a (exp t) ≤ 0 := by
      linarith [h.2]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h'
  · intro h
    have h' : einastoSlope d l a (exp t) - 4 * einastoDensity d l a (exp t) ≤ 0 :=
      nonpos_of_mul_nonpos_right h (by positivity)
    constructor <;> linarith

end GaloisForLFunctions.HTGeometry

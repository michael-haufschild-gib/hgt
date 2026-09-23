import GaloisForLFunctions.RHTower.ThetaCuspHawkingSchwarzschildMatsubaraCutoffEndpoint
import GaloisForLFunctions.HTGeometry.CPVSchwarzschildLimit
import GaloisForLFunctions.RHTower.ThetaCuspHawkingSchwarzschildRecoilCompletionEndpoint

/-!
# Information scaling extracted from the Schwarzschild metric

Applies equations (7), (8), and (12) of arXiv:2608.06941v1 to the actual
Schwarzschild time-time metric entry, the CPV horizon potential derivative,
and existing Hawking entropy, inverse temperature, and Matsubara rates.
The expression `(1 + g₀₀)/r²` gives the spherical-lapse inverse-cube quantity;
this module does not construct a Riemann tensor or identify it with Ricci.

A mass-independent calibration matches all positive masses exactly when
information scales linearly with mass. Quadratic area entropy instead needs
a mass-dependent calibration. An imposed curvature ceiling gives an exact
radius boundary and a sharp condition for that boundary to fit inside the
horizon. These algebraic consequences do not establish the paper's physical
information ansatz.
-/

noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

/-- The spherical-lapse expression extracted from the actual time-time metric entry. -/
def schwarzschildInformationCurvature (M r polar : ℝ) : ℝ :=
  (1 + schwarzschildBoyerLindquistMetric M r polar 0 0) / r ^ (2 : ℕ)

def massPowerInformation (c p m : ℝ) : ℝ := exp (c + p * m)

def calibratedInformationCurvature (c p m t : ℝ) : ℝ :=
  2 * exp (-c) * massPowerInformation c p m / exp t ^ (3 : ℕ)

theorem schwarzschildInformationCurvature_eq (M t polar : ℝ) :
    schwarzschildInformationCurvature M (exp t) polar = 2 * M / exp t ^ (3 : ℕ) := by
  rw [schwarzschildInformationCurvature, schwarzschildBoyerLindquistMetric_explicit]
  change (1 + -(exp t ^ (2 : ℕ) - 2 * M * exp t) / exp t ^ (2 : ℕ)) / exp t ^ (2 : ℕ) = _
  field_simp
  ring

theorem schwarzschildInformationCurvature_pos (m t polar : ℝ) :
    0 < schwarzschildInformationCurvature (exp m) (exp t) polar := by
  rw [schwarzschildInformationCurvature_eq]
  positivity

theorem schwarzschildInformationCurvature_angle_independent (M t polar other : ℝ) :
    schwarzschildInformationCurvature M (exp t) polar =
      schwarzschildInformationCurvature M (exp t) other := by
  simp only [schwarzschildInformationCurvature_eq]

theorem schwarzschildInformationCurvature_horizon (m polar : ℝ) :
    schwarzschildInformationCurvature (exp m) (2 * exp m) polar = 1 / (4 * exp m ^ (2 : ℕ)) := by
  have h := schwarzschildInformationCurvature_eq (exp m) (log 2 + m) polar
  rw [exp_add, exp_log (by norm_num : (0 : ℝ) < 2)] at h
  rw [h]
  field_simp
  ring

theorem schwarzschildInformationCurvature_entropy_product (m polar : ℝ) :
    RHTower.schwarzschildBekensteinHawkingEntropy (exp m) *
      schwarzschildInformationCurvature (exp m) (2 * exp m) polar = Real.pi := by
  rw [schwarzschildInformationCurvature_horizon, RHTower.schwarzschildBekensteinHawkingEntropy]
  field_simp

theorem schwarzschildInformationCurvature_horizon_slope (m polar : ℝ) :
    schwarzschildInformationCurvature (exp m) (2 * exp m) polar =
      4 * (deriv (CPV.schwarzschildPotential 0 m) 0) ^ (2 : ℕ) := by
  rw [schwarzschildInformationCurvature_horizon, (CPV.schwarzschildPotential_hasDerivAt_zero 0 m).deriv,
    exp_zero]
  field_simp

theorem calibratedInformationCurvature_eq (c p m t : ℝ) :
    calibratedInformationCurvature c p m t = 2 * exp (p * m) / exp t ^ (3 : ℕ) := by
  unfold calibratedInformationCurvature massPowerInformation
  rw [exp_add, exp_neg]
  field_simp

/-- The fixed inverse-cube calibration detects the mass exponent exactly. -/
theorem calibratedInformationCurvature_matches_iff (c p m t polar : ℝ) :
    calibratedInformationCurvature c p m t =
      schwarzschildInformationCurvature (exp m) (exp t) polar ↔ p = 1 ∨ m = 0 := by
  rw [calibratedInformationCurvature_eq, schwarzschildInformationCurvature_eq,
    div_left_inj' (by positivity : exp t ^ (3 : ℕ) ≠ 0), mul_right_inj' (by norm_num : (2 : ℝ) ≠ 0),
    exp_eq_exp]
  constructor
  · intro h
    have he : (p - 1) * m = 0 := by nlinarith
    simpa only [mul_eq_zero, sub_eq_zero] using he
  · rintro (rfl | rfl) <;> ring

/-- Universal agreement forces linear information-mass scaling. -/
theorem calibratedInformationCurvature_rigidity (c p t polar : ℝ) :
    (∀ m, calibratedInformationCurvature c p m t =
      schwarzschildInformationCurvature (exp m) (exp t) polar) ↔ p = 1 := by
  constructor
  · intro h
    have hh := (calibratedInformationCurvature_matches_iff c p 1 t polar).mp (h 1)
    exact hh.resolve_right one_ne_zero
  · rintro rfl m
    exact (calibratedInformationCurvature_matches_iff c 1 m t polar).mpr (Or.inl rfl)

/-- At every mass different from the reference mass, quadratic area scaling is distinguishable. -/
theorem quadraticInformationCurvature_mismatch (c t polar u : ℝ) :
    calibratedInformationCurvature c 2 (exp u) t ≠
      schwarzschildInformationCurvature (exp (exp u)) (exp t) polar := by
  rw [ne_eq, calibratedInformationCurvature_matches_iff]
  simp only [OfNat.ofNat_ne_one, exp_ne_zero, or_self, not_false_eq_true]

theorem schwarzschildInformationCurvature_inverseTemperature (m polar : ℝ) :
    RHTower.schwarzschildHawkingInverseTemperature (2 * exp m) ^ (2 : ℕ) *
      schwarzschildInformationCurvature (exp m) (2 * exp m) polar = 16 * Real.pi ^ (2 : ℕ) := by
  rw [schwarzschildInformationCurvature_horizon, RHTower.schwarzschildHawkingInverseTemperature]
  field_simp
  ring

theorem schwarzschildInformationCurvature_matsubara (m polar : ℝ) (n : ℕ) :
    RHTower.schwarzschildHawkingMatsubaraRate (2 * exp m) n ^ (2 : ℕ) =
      (n : ℝ) ^ (2 : ℕ) / 4 * schwarzschildInformationCurvature (exp m) (2 * exp m) polar := by
  rw [schwarzschildInformationCurvature_horizon, RHTower.schwarzschildHawkingMatsubaraRate,
    RHTower.schwarzschildHawkingInverseTemperature]
  field_simp

/-- The area entropy determines a mass-dependent inverse-cube coefficient. -/
theorem schwarzschildInformationCurvature_areaEntropy (m t polar : ℝ) :
    schwarzschildInformationCurvature (exp m) (exp t) polar =
      RHTower.schwarzschildBekensteinHawkingEntropy (exp m) /
        (2 * Real.pi * exp m * exp t ^ (3 : ℕ)) := by
  rw [schwarzschildInformationCurvature_eq, RHTower.schwarzschildBekensteinHawkingEntropy]
  field_simp
  ring

theorem schwarzschildInformationCurvature_exponential (m t polar : ℝ) :
    schwarzschildInformationCurvature (exp m) (exp t) polar = exp (log 2 + m - 3 * t) := by
  rw [schwarzschildInformationCurvature_eq, exp_sub, exp_add,
    exp_log (by norm_num : (0 : ℝ) < 2)]
  have he : exp (3 * t) = exp t ^ (3 : ℕ) := exp_nat_mul t 3
  rw [he]

/-- The exact radius boundary exposed by an imposed positive curvature ceiling. -/
theorem schwarzschildInformationCurvature_cap_iff (m l t polar : ℝ) :
    schwarzschildInformationCurvature (exp m) (exp t) polar ≤ exp (-2 * l) ↔
      (log 2 + m + 2 * l) / 3 ≤ t := by
  rw [schwarzschildInformationCurvature_exponential, exp_le_exp]
  constructor <;> intro h <;> linarith

def informationCurvatureCapRadius (m l : ℝ) : ℝ := exp ((log 2 + m + 2 * l) / 3)

theorem informationCurvatureCapRadius_attains (m l polar : ℝ) :
    schwarzschildInformationCurvature (exp m) (informationCurvatureCapRadius m l) polar = exp (-2 * l) := by
  rw [informationCurvatureCapRadius, schwarzschildInformationCurvature_exponential]
  congr 1
  ring

/-- A capped surface fits within the horizon exactly above the corresponding mass threshold. -/
theorem informationCurvatureCapRadius_inside_horizon (m l : ℝ) :
    informationCurvatureCapRadius m l ≤ 2 * exp m ↔ l ≤ log 2 + m := by
  rw [show 2 * exp m = exp (log 2 + m) by
    rw [exp_add, exp_log (by norm_num : (0 : ℝ) < 2)],
    informationCurvatureCapRadius, exp_le_exp]
  constructor <;> intro h <;> linarith

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingEvaporationSingularityOrderSelectionEndpoint
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingSchwarzschildRecoilCompletionEndpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Hawking mass-loss law and two distinct transition clocks

Equations (36)--(40) of arXiv:2608.06941v1 applied to the corpus's exact
Schwarzschild remaining lifetime and Bekenstein--Hawking entropy. A real
cube-root curve inverts the clock, satisfies the actual mass-loss differential
equation at every strictly preterminal time, and tends continuously to zero.

The paper's half-mass transition consumes `7/8` of the lifetime and leaves
`1/4` of the initial area entropy. Halving area entropy gives a strictly earlier
clock. These statements distinguish mathematical thresholds; no entanglement
Page curve or physical remnant claim is inferred from them. Derivative claims
are only on the strictly preterminal branch of the real-power formula.
-/

noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

/-- Positive real cube-root branch of the exact remaining-time equation. -/
def hawkingEvaporationMass (a T t : ℝ) : ℝ := (3 * exp a * (T - t)) ^ (1 / 3 : ℝ)

def hawkingTimeToMassFraction (a m q : ℝ) : ℝ :=
  RHTower.schwarzschildEvaporationRemainingTime (exp a) (exp m) -
    RHTower.schwarzschildEvaporationRemainingTime (exp a) (q * exp m)

theorem hawkingEvaporationMass_pos (a T v : ℝ) :
    0 < hawkingEvaporationMass a T (T - exp v) := by
  unfold hawkingEvaporationMass
  apply rpow_pos_of_pos
  simp only [sub_sub_cancel]
  positivity

theorem hawkingEvaporationMass_cube (a T v : ℝ) :
    hawkingEvaporationMass a T (T - exp v) ^ 3 = 3 * exp a * exp v := by
  unfold hawkingEvaporationMass
  simp only [sub_sub_cancel]
  rw [← rpow_natCast _ 3, ← rpow_mul (by positivity : 0 ≤ 3 * exp a * exp v)]
  norm_num

/-- The constructed curve exactly inverts the existing evaporation clock. -/
theorem hawkingEvaporationMass_clock (a T v : ℝ) :
    RHTower.schwarzschildEvaporationRemainingTime (exp a)
      (hawkingEvaporationMass a T (T - exp v)) = exp v := by
  rw [RHTower.schwarzschildEvaporationRemainingTime, hawkingEvaporationMass_cube]
  field_simp

/-- The mass-loss differential law is proved for every strictly preterminal time. -/
theorem hawkingEvaporationMass_derivative (a T v : ℝ) :
    HasDerivAt (hawkingEvaporationMass a T)
      (-exp a / hawkingEvaporationMass a T (T - exp v) ^ 2) (T - exp v) := by
  have hp : 0 < 3 * exp a * (T - (T - exp v)) := by simp only [sub_sub_cancel]; positivity
  have h := (hasDerivAt_rpow_const (p := (1 / 3 : ℝ)) (Or.inl hp.ne')).comp (T - exp v)
    (((hasDerivAt_id (T - exp v)).const_sub T).const_mul (3 * exp a))
  apply h.congr_deriv
  rw [rpow_sub hp, rpow_one]
  have hm := hawkingEvaporationMass_cube a T v
  have hn := (hawkingEvaporationMass_pos a T v).ne'
  change (1 / 3 : ℝ) * (hawkingEvaporationMass a T (T - exp v) /
      (3 * exp a * (T - (T - exp v)))) * (3 * exp a * -1) = _
  simp only [sub_sub_cancel]
  field_simp
  nlinarith [hm]

theorem hawkingEvaporationMass_rate_neg (a T v : ℝ) :
    deriv (hawkingEvaporationMass a T) (T - exp v) < 0 := by
  rw [(hawkingEvaporationMass_derivative a T v).deriv]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (exp_pos a))
    (sq_pos_of_pos (hawkingEvaporationMass_pos a T v))

theorem hawkingEvaporationEntropy_derivative (a T v : ℝ) :
    HasDerivAt (fun t => RHTower.schwarzschildBekensteinHawkingEntropy (hawkingEvaporationMass a T t))
      (-8 * Real.pi * exp a / hawkingEvaporationMass a T (T - exp v)) (T - exp v) := by
  have h := ((hawkingEvaporationMass_derivative a T v).pow 2).const_mul (4 * Real.pi)
  apply h.congr_deriv
  dsimp
  have hn := (hawkingEvaporationMass_pos a T v).ne'
  field_simp
  ring

/-- Every mass fraction has an exact elapsed lifetime fraction. -/
theorem hawkingTimeToMassFraction_ratio (a m q : ℝ) :
    hawkingTimeToMassFraction a m q /
      RHTower.schwarzschildEvaporationRemainingTime (exp a) (exp m) = 1 - q ^ 3 := by
  unfold hawkingTimeToMassFraction RHTower.schwarzschildEvaporationRemainingTime
  field_simp

theorem hawkingTimeToMassFraction_entropy_ratio (m q : ℝ) :
    RHTower.schwarzschildBekensteinHawkingEntropy (q * exp m) /
      RHTower.schwarzschildBekensteinHawkingEntropy (exp m) = q ^ 2 := by
  unfold RHTower.schwarzschildBekensteinHawkingEntropy
  field_simp

/-- Equation (40): the half-mass clock consumes exactly seven eighths of the lifetime. -/
theorem hawking_half_mass_time (a m : ℝ) :
    hawkingTimeToMassFraction a m (1 / 2) =
      (7 / 8) * RHTower.schwarzschildEvaporationRemainingTime (exp a) (exp m) := by
  unfold hawkingTimeToMassFraction RHTower.schwarzschildEvaporationRemainingTime
  ring

/-- The same half-mass event leaves one quarter of area entropy. -/
theorem hawking_half_mass_entropy (m : ℝ) :
    RHTower.schwarzschildBekensteinHawkingEntropy (exp m / 2) =
      RHTower.schwarzschildBekensteinHawkingEntropy (exp m) / 4 := by
  unfold RHTower.schwarzschildBekensteinHawkingEntropy
  ring

theorem hawking_half_entropy_mass (m : ℝ) :
    RHTower.schwarzschildBekensteinHawkingEntropy (exp m / sqrt 2) =
      RHTower.schwarzschildBekensteinHawkingEntropy (exp m) / 2 := by
  unfold RHTower.schwarzschildBekensteinHawkingEntropy
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Half area entropy and half mass define different transition clocks. -/
theorem hawking_half_entropy_time (a m : ℝ) :
    hawkingTimeToMassFraction a m (1 / sqrt 2) =
      (1 - 1 / (2 * sqrt 2)) * RHTower.schwarzschildEvaporationRemainingTime (exp a) (exp m) := by
  have hs : sqrt 2 ≠ 0 := by positivity
  have hsq := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  unfold hawkingTimeToMassFraction RHTower.schwarzschildEvaporationRemainingTime
  field_simp
  nlinarith [hsq]

theorem hawking_half_entropy_before_half_mass (a m : ℝ) :
    hawkingTimeToMassFraction a m (1 / sqrt 2) < hawkingTimeToMassFraction a m (1 / 2) := by
  rw [hawking_half_entropy_time, hawking_half_mass_time]
  apply mul_lt_mul_of_pos_right
  · have hs : 0 < sqrt 2 := by positivity
    have hsq := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hb : sqrt 2 < 4 := by nlinarith
    have hi : 1 / 8 < 1 / (2 * sqrt 2) := by
      apply one_div_lt_one_div_of_lt (by positivity : 0 < 2 * sqrt 2)
      nlinarith
    linarith
  · unfold RHTower.schwarzschildEvaporationRemainingTime
    positivity

theorem hawkingEvaporationMass_terminal (a T : ℝ) : hawkingEvaporationMass a T T = 0 := by
  simp [hawkingEvaporationMass]

theorem hawkingEvaporationMass_terminal_limit (a T : ℝ) :
    Filter.Tendsto (hawkingEvaporationMass a T) (nhds T) (nhds 0) := by
  have hc : Continuous (hawkingEvaporationMass a T) :=
    (continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 3)).comp
      (continuous_const.mul (continuous_const.sub continuous_id))
  simpa only [hawkingEvaporationMass_terminal] using hc.continuousAt.tendsto (x := T)

end GaloisForLFunctions.HTGeometry

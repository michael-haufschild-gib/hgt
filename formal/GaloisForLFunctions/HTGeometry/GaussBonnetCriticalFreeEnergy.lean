import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistence
import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalUniversality

/-!
# Quartic critical Gibbs minimum and exact derivatives of every order

At the Model B critical point of arXiv:2609.00025, equations (19)--(25)
and the phase structure of section 5, the actual off-shell free-energy gap
is a positive quartic divided by radius. Its unique global minimizer has
vanishing first three derivatives and strictly positive fourth derivative.
Logarithmic radius gives unrestricted real coordinates. An explicit jet
formula computes actual derivatives of every order by symbolic induction.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Actual critical Gibbs free energy in logarithmic radius. -/
def egbCriticalLogGibbs (x theta u : ℝ) : ℝ :=
  egbOffShellGibbs (egbCriticalPressure x) (egbCriticalTemperature x)
    (egbCriticalCharge x theta) (egbCriticalCouplingRoot x theta) (Real.exp u)

/-- Candidate logarithmic-radius derivative of order n. -/
def egbCriticalGibbsJet (x : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp u / 2 + (-1 : ℝ)^n * Real.exp x ^ (2 : ℕ) / (12 * Real.exp u) +
    (3 : ℝ)^n * Real.exp u ^ (3 : ℕ) / (12 * Real.exp x ^ (2 : ℕ)) -
      (2 : ℝ)^n * Real.exp u ^ (2 : ℕ) / (3 * Real.exp x)

theorem egbCriticalLogGibbs_formula (x theta u : ℝ) :
    egbCriticalLogGibbs x theta u = Real.exp u / 2 + Real.exp x ^ (2 : ℕ) / (12 * Real.exp u) +
      Real.exp u ^ (3 : ℕ) / (12 * Real.exp x ^ (2 : ℕ)) - Real.exp u ^ (2 : ℕ) / (3 * Real.exp x) := by
  unfold egbCriticalLogGibbs egbOffShellGibbs egbMass egbEntropyB
  rw [egbCritical_effective_charge]
  unfold egbCriticalPressure egbCriticalTemperature
  field_simp [Real.pi_ne_zero]
  ring

/-- An exact quartic minimum, not merely a truncated local expansion. -/
theorem egbCriticalLogGibbs_gap (x theta u : ℝ) :
    egbCriticalLogGibbs x theta u - Real.exp x / 3 =
      (Real.exp u - Real.exp x)^(4 : ℕ) / (12 * Real.exp u * Real.exp x ^ (2 : ℕ)) := by
  rw [egbCriticalLogGibbs_formula]
  field_simp
  ring

theorem egbCriticalLogGibbs_value (x theta : ℝ) : egbCriticalLogGibbs x theta x = Real.exp x / 3 := by
  have h := egbCriticalLogGibbs_gap x theta x
  simp only [sub_self, zero_pow (by norm_num : 4 ≠ 0), zero_div] at h
  linarith

theorem egbCriticalLogGibbs_lower_bound (x theta u : ℝ) :
    Real.exp x / 3 ≤ egbCriticalLogGibbs x theta u := by
  have h := egbCriticalLogGibbs_gap x theta u
  have hp : 0 ≤ (Real.exp u - Real.exp x)^(4 : ℕ) / (12 * Real.exp u * Real.exp x ^ (2 : ℕ)) := by positivity
  linarith

/-- The critical point has exactly one global minimum in the entire positive-radius domain. -/
theorem egbCriticalLogGibbs_unique_minimum (x theta u : ℝ) :
    egbCriticalLogGibbs x theta u = Real.exp x / 3 ↔ u = x := by
  rw [← sub_eq_zero, egbCriticalLogGibbs_gap]
  have hd : 12 * Real.exp u * Real.exp x ^ (2 : ℕ) ≠ 0 := by positivity
  simp only [div_eq_zero_iff, hd, or_false, pow_eq_zero_iff (by norm_num : 4 ≠ 0),
    sub_eq_zero]
  exact Real.exp_injective.eq_iff

/-- Every other positive radius has strictly larger Gibbs free energy. -/
theorem egbCriticalLogGibbs_strict_gap (x theta u : ℝ) :
    Real.exp x / 3 < egbCriticalLogGibbs x theta u ↔ u ≠ x := by
  constructor
  · intro h he
    subst u
    rw [egbCriticalLogGibbs_value] at h
    exact lt_irrefl _ h
  · intro h
    exact lt_of_le_of_ne (egbCriticalLogGibbs_lower_bound x theta u)
      (Ne.symm (mt (egbCriticalLogGibbs_unique_minimum x theta u).mp h))

/-- Charge/coupling angular decomposition does not change the critical Gibbs landscape. -/
theorem egbCriticalLogGibbs_angle_independent (x theta phi u : ℝ) :
    egbCriticalLogGibbs x theta u = egbCriticalLogGibbs x phi u := by
  rw [egbCriticalLogGibbs_formula, egbCriticalLogGibbs_formula]

/-- The full critical gap has a universal dimensionless shape at every scale. -/
theorem egbCriticalLogGibbs_universal_gap (x theta v : ℝ) :
    (egbCriticalLogGibbs x theta (x + v) - Real.exp x / 3) / Real.exp x =
      (Real.exp v - 1)^(4 : ℕ) / (12 * Real.exp v) := by
  rw [egbCriticalLogGibbs_gap, Real.exp_add]
  field_simp

/-- Every candidate jet has the next jet as its actual derivative. -/
theorem egbCriticalGibbsJet_hasDerivAt (x u : ℝ) (n : ℕ) :
    HasDerivAt (egbCriticalGibbsJet x n) (egbCriticalGibbsJet x (n + 1) u) u := by
  have he := Real.hasDerivAt_exp u
  have hq : HasDerivAt (fun v => (-1 : ℝ)^n * Real.exp x ^ (2 : ℕ) / (12 * Real.exp v))
      ((0 * (12 * Real.exp u) - ((-1 : ℝ)^n * Real.exp x ^ (2 : ℕ)) * (12 * Real.exp u)) /
        (12 * Real.exp u)^(2 : ℕ)) u :=
    (hasDerivAt_const u ((-1 : ℝ)^n * Real.exp x ^ (2 : ℕ))).div (he.const_mul 12) (by positivity)
  have h : HasDerivAt (egbCriticalGibbsJet x n)
      (Real.exp u / 2 +
        (0 * (12 * Real.exp u) - ((-1 : ℝ)^n * Real.exp x ^ (2 : ℕ)) * (12 * Real.exp u)) /
          (12 * Real.exp u)^(2 : ℕ) +
        (3 : ℝ)^n * (3 * Real.exp u ^ (2 : ℕ) * Real.exp u) / (12 * Real.exp x ^ (2 : ℕ)) -
          (2 : ℝ)^n * (2 * Real.exp u ^ (1 : ℕ) * Real.exp u) / (3 * Real.exp x)) u :=
    (((he.div_const 2).add hq).add (((he.pow 3).const_mul ((3 : ℝ)^n)).div_const (12 * Real.exp x ^ (2 : ℕ)))).sub
      (((he.pow 2).const_mul ((2 : ℝ)^n)).div_const (3 * Real.exp x))
  apply h.congr_deriv
  unfold egbCriticalGibbsJet
  simp only [pow_succ]
  field_simp
  ring

/-- Closed formula for actual derivatives of arbitrary order. -/
theorem egbCriticalLogGibbs_iteratedDeriv (x theta : ℝ) (n : ℕ) :
    iteratedDeriv n (egbCriticalLogGibbs x theta) = egbCriticalGibbsJet x n := by
  induction n with
  | zero =>
    rw [iteratedDeriv_zero]
    funext u
    simp only [egbCriticalLogGibbs_formula, egbCriticalGibbsJet, pow_zero, one_mul]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext fun u => (egbCriticalGibbsJet_hasDerivAt x u n).deriv

/-- Exact critical value of the n-th derivative; no finite-difference approximation. -/
theorem egbCriticalLogGibbs_iteratedDeriv_at_critical (x theta : ℝ) (n : ℕ) :
    iteratedDeriv n (egbCriticalLogGibbs x theta) x =
      Real.exp x * (6 + (-1 : ℝ)^n + (3 : ℝ)^n - 4 * (2 : ℝ)^n) / 12 := by
  rw [egbCriticalLogGibbs_iteratedDeriv, egbCriticalGibbsJet]
  field_simp
  ring

theorem egbCriticalLogGibbs_first_derivative_zero (x theta : ℝ) :
    deriv (egbCriticalLogGibbs x theta) x = 0 := by
  rw [← iteratedDeriv_one, egbCriticalLogGibbs_iteratedDeriv_at_critical]
  ring

theorem egbCriticalLogGibbs_second_derivative_zero (x theta : ℝ) :
    iteratedDeriv 2 (egbCriticalLogGibbs x theta) x = 0 := by
  rw [egbCriticalLogGibbs_iteratedDeriv_at_critical]
  ring

theorem egbCriticalLogGibbs_third_derivative_zero (x theta : ℝ) :
    iteratedDeriv 3 (egbCriticalLogGibbs x theta) x = 0 := by
  rw [egbCriticalLogGibbs_iteratedDeriv_at_critical]
  ring

theorem egbCriticalLogGibbs_fourth_derivative (x theta : ℝ) :
    iteratedDeriv 4 (egbCriticalLogGibbs x theta) x = 2 * Real.exp x := by
  rw [egbCriticalLogGibbs_iteratedDeriv_at_critical]
  ring

theorem egbCriticalLogGibbs_fourth_derivative_pos (x theta : ℝ) :
    0 < iteratedDeriv 4 (egbCriticalLogGibbs x theta) x := by
  rw [egbCriticalLogGibbs_fourth_derivative]
  exact mul_pos (by norm_num) (Real.exp_pos x)

end GaloisForLFunctions.HTGeometry

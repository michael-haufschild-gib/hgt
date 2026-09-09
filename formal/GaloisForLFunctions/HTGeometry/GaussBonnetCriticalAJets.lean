import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalAGibbs

/-!
# Model-A critical derivatives of arbitrary order

The logarithmic entropy contributes an affine term in logarithmic radius.
After two actual derivatives this term disappears. Symbolic induction
therefore supplies all higher derivatives of the genuine critical Gibbs
function. The first three vanish at criticality, the fourth is strictly
positive, and its normalized coefficient varies with the physical coupling.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

theorem egbCriticalALogGibbs_derivative_function (x θ l : ℝ) :
    deriv (egbCriticalALogGibbs x θ l) =
      (fun u => egbCriticalAGibbsJet x θ 1 u - egbCriticalAEntropySlope x θ) :=
  funext fun u => (egbCriticalALogGibbs_hasDerivAt x θ l u).deriv

theorem egbCriticalALogGibbs_second_hasDerivAt (x θ l u : ℝ) :
    HasDerivAt (deriv (egbCriticalALogGibbs x θ l)) (egbCriticalAGibbsJet x θ 2 u) u := by
  rw [egbCriticalALogGibbs_derivative_function]
  exact (egbCriticalAGibbsJet_hasDerivAt x θ u 1).sub_const _

/-- Formula for every actual derivative of order two or higher. -/
theorem egbCriticalALogGibbs_iteratedDeriv (x θ l : ℝ) (n : ℕ) :
    iteratedDeriv (n + 2) (egbCriticalALogGibbs x θ l) = egbCriticalAGibbsJet x θ (n + 2) := by
  induction n with
  | zero =>
    funext u
    rw [show 0 + 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact (egbCriticalALogGibbs_second_hasDerivAt x θ l u).deriv
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 from Nat.add_right_comm n 1 2, iteratedDeriv_succ, ih]
    exact funext fun u => (egbCriticalAGibbsJet_hasDerivAt x θ u (n + 2)).deriv

theorem egbCriticalALogGibbs_iteratedDeriv_at_critical (x θ l : ℝ) (n : ℕ) :
    iteratedDeriv (n + 2) (egbCriticalALogGibbs x θ l) x =
      exp x * (18 * (1 + 2 * egbCriticalAShape θ) + 3 * (-1 : ℝ) ^ (n + 2) * (1 - 6 * egbCriticalAShape θ) +
        (3 : ℝ) ^ (n + 2) * (3 - 2 * egbCriticalAShape θ) - 12 * (2 : ℝ) ^ (n + 2)) /
          (36 * (1 + 2 * egbCriticalAShape θ)) := by
  rw [egbCriticalALogGibbs_iteratedDeriv]
  unfold egbCriticalAGibbsJet
  have hb := (egbCriticalAShape_bounds θ).1
  field_simp
  ring

theorem egbCriticalALogGibbs_first_derivative_zero (x θ l : ℝ) :
    deriv (egbCriticalALogGibbs x θ l) x = 0 := by
  rw [egbCriticalALogGibbs_derivative_factorization]
  ring

theorem egbCriticalALogGibbs_second_derivative_zero (x θ l : ℝ) :
    iteratedDeriv 2 (egbCriticalALogGibbs x θ l) x = 0 := by
  rw [show 2 = 0 + 2 from rfl, egbCriticalALogGibbs_iteratedDeriv_at_critical]
  ring

theorem egbCriticalALogGibbs_third_derivative_zero (x θ l : ℝ) :
    iteratedDeriv 3 (egbCriticalALogGibbs x θ l) x = 0 := by
  rw [show 3 = 1 + 2 from rfl, egbCriticalALogGibbs_iteratedDeriv_at_critical]
  ring

/-- Exact quartic coefficient, including its dependence on the dimensionless Gauss--Bonnet coupling. -/
theorem egbCriticalALogGibbs_fourth_derivative (x θ l : ℝ) :
    iteratedDeriv 4 (egbCriticalALogGibbs x θ l) x =
      2 * exp x * (1 - 2 * egbCriticalAShape θ) / (1 + 2 * egbCriticalAShape θ) := by
  rw [show 4 = 2 + 2 from rfl, egbCriticalALogGibbs_iteratedDeriv_at_critical]
  have hb := (egbCriticalAShape_bounds θ).1
  field_simp
  ring

theorem egbCriticalALogGibbs_fourth_derivative_pos (x θ l : ℝ) :
    0 < iteratedDeriv 4 (egbCriticalALogGibbs x θ l) x := by
  rw [egbCriticalALogGibbs_fourth_derivative]
  have hb := (egbCriticalAShape_bounds θ).1
  have hp : 0 < 1 - 2 * egbCriticalAShape θ := by linarith [egbCriticalAShape_lt_sixth θ]
  positivity

/-- All higher derivatives are independent of the arbitrary entropy reference. -/
theorem egbCriticalALogGibbs_higher_derivatives_reference_invariant (x θ l c : ℝ) (n : ℕ) :
    iteratedDeriv (n + 2) (egbCriticalALogGibbs x θ (l + c)) =
      iteratedDeriv (n + 2) (egbCriticalALogGibbs x θ l) := by
  rw [egbCriticalALogGibbs_iteratedDeriv, egbCriticalALogGibbs_iteratedDeriv]

/-- The quartic stiffness decreases strictly as the dimensionless coupling increases. -/
theorem egbCriticalALogGibbs_quartic_comparison (x θ φ l : ℝ) :
    iteratedDeriv 4 (egbCriticalALogGibbs x θ l) x < iteratedDeriv 4 (egbCriticalALogGibbs x φ l) x ↔
      egbCriticalAShape φ < egbCriticalAShape θ := by
  rw [egbCriticalALogGibbs_fourth_derivative, egbCriticalALogGibbs_fourth_derivative]
  have hθ : 0 < 1 + 2 * egbCriticalAShape θ := by
    have h := (egbCriticalAShape_bounds θ).1
    positivity
  have hφ : 0 < 1 + 2 * egbCriticalAShape φ := by
    have h := (egbCriticalAShape_bounds φ).1
    positivity
  rw [div_lt_div_iff₀ hθ hφ]
  have hx := exp_pos x
  constructor <;> intro h <;> nlinarith

end GaloisForLFunctions.HTGeometry

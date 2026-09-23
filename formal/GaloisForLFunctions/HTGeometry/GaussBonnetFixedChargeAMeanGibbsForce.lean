import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAInteriorGibbsForce
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeABarrierCriticalLimit

/-!
# The next-order Gibbs force at the arithmetic phase mean

The leading cubic force vanishes at the mean coordinate. Its next term
is quartic and strictly negative, resolving the asymmetry hidden by the
leading quartic energy profile.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAMeanGibbsForceCoefficient (φ : ℝ) : ℝ :=
  -(5 - 14 * egbFixedChargeACriticalCouplingWeight φ) /
    (60 * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ))

theorem egbFixedChargeAMeanGibbsForceCoefficient_neg (φ : ℝ) : egbFixedChargeAMeanGibbsForceCoefficient φ < 0 := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have hn : 0 < 5 - 14 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  unfold egbFixedChargeAMeanGibbsForceCoefficient
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hn) (by positivity)

theorem egbFixedChargeAMeanGibbs_force_formula (w φ τ l : ℝ) :
    deriv (egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
      (exp w * cos φ) (exp w * sin φ) l) (egbFixedChargeAMeanRadius w φ τ) /
      egbCoexistenceASymmetricRatio τ ^ (4 : ℕ) =
      -((egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ +
        egbFixedChargeAMiddleMeanConstant τ φ) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) /
        (2 * egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))) := by
  have h := (egbFixedChargeA_mean_gibbs_derivative w φ τ l 0).deriv
  simp only [exp_zero, mul_one, one_pow] at h
  rw [h, egbFixedChargeAMeanStationaryPolynomial_factorization]
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hD := egbFixedChargeAMeanDenominator_pos τ φ
  have hx : 0 < 1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) := by positivity
  field_simp <;> ring

theorem egbFixedChargeAMeanGibbs_quartic_force_limit (w φ l : ℝ) :
    Tendsto (fun τ => deriv (egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
      (exp w * cos φ) (exp w * sin φ) l) (egbFixedChargeAMeanRadius w φ τ) /
      egbCoexistenceASymmetricRatio τ ^ (4 : ℕ)) atBot (𝓝 (egbFixedChargeAMeanGibbsForceCoefficient φ)) := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have h2 : Tendsto (fun τ => 1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) atBot (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (egbCoexistenceASymmetricRatio_critical_limit.pow 2)
  have hd := ((tendsto_const_nhds (x := (2 : ℝ))).mul (egbFixedChargeAMeanDenominator_critical_limit φ)).mul h2
  have h := (egbFixedChargeAMiddleMeanResidual_critical_limit φ).neg.div hd (by positivity)
  have he : -(1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5) /
      (2 * (6 + 12 * egbFixedChargeACriticalCouplingWeight φ) * 1) = egbFixedChargeAMeanGibbsForceCoefficient φ := by
    unfold egbFixedChargeAMeanGibbsForceCoefficient
    field_simp <;> ring
  rw [he] at h
  simp only [egbFixedChargeAMeanGibbs_force_formula]
  simpa only [Pi.div_def] using h

theorem egbFixedChargeAMeanGibbs_force_eventually_neg (w φ l : ℝ) :
    ∀ᶠ τ in atBot, deriv (egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
      (exp w * cos φ) (exp w * sin φ) l) (egbFixedChargeAMeanRadius w φ τ) < 0 := by
  have h := (egbFixedChargeAMeanGibbs_quartic_force_limit w φ l).eventually_lt_const
    (egbFixedChargeAMeanGibbsForceCoefficient_neg φ)
  filter_upwards [h] with τ hτ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hd4 : 0 < egbCoexistenceASymmetricRatio τ ^ (4 : ℕ) := by positivity
  have hcross := (div_lt_iff₀ hd4).1 hτ
  linarith

theorem egbFixedChargeAMeanGibbs_force_barrier_ratio_limit (w φ l₁ l₂ : ℝ) :
    Tendsto (fun τ => deriv (egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
      (exp w * cos φ) (exp w * sin φ) l₁) (egbFixedChargeAMeanRadius w φ τ) /
      egbFixedChargeAGibbsBarrier w φ τ l₂)
      atBot (𝓝 (egbFixedChargeAMeanGibbsForceCoefficient φ / egbFixedChargeAGibbsBarrierCoefficient w φ)) := by
  have h := (egbFixedChargeAMeanGibbs_quartic_force_limit w φ l₁).div
    (egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l₂) (egbFixedChargeAGibbsBarrierCoefficient_pos w φ).ne'
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

end GaloisForLFunctions.HTGeometry

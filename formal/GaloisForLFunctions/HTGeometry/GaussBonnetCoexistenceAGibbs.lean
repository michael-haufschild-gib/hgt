import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAStates
import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAGlobalMinima
import GaloisForLFunctions.HTGeometry.GaussBonnetGibbsAGauge

/-!
# Global coexistence in the actual model-A Gibbs functional

Transfer the analytic reduced landscape to the corpus's physical mass and
logarithmic entropy. For every reference length, the constructed small and
large radii are precisely the global minimizers among all positive radii.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

/-- Exact dimensional scaling, including the radius-independent entropy reference term. -/
theorem egbCoexistenceA_gibbs_scaling (k τ θ l u : ℝ) :
    egbOffShellGibbsA (egbCoexistenceAPressure k τ θ) (egbCoexistenceATemperature k τ θ)
      (egbCoexistenceACharge k τ θ) (egbCoexistenceACouplingRoot k τ θ) l (exp k * exp u) =
    exp k * (egbCoexistenceAReducedLogGibbs τ θ u -
      egbCoexistenceACouplingWeight τ θ * egbCoexistenceATemperatureWeight τ θ * (k - l)) := by
  have hlog : log (exp k * exp u / exp l) = k + u - l := by
    rw [← exp_add, ← exp_sub, log_exp]
  unfold egbOffShellGibbsA egbMass egbEntropyA
  rw [egbCoexistenceA_effective_charge, egbCoexistenceACouplingRoot_sq, hlog]
  unfold egbCoexistenceAPressure egbCoexistenceATemperature
    egbCoexistenceAReducedLogGibbs egbCoexistenceAReducedGibbs
  rw [log_exp]
  field_simp
  ring

/-- The actual Gibbs gap is a positive scale times the reduced gap. -/
theorem egbCoexistenceA_gibbs_gap (k τ θ l u : ℝ) :
    egbOffShellGibbsA (egbCoexistenceAPressure k τ θ) (egbCoexistenceATemperature k τ θ)
      (egbCoexistenceACharge k τ θ) (egbCoexistenceACouplingRoot k τ θ) l (exp k * exp u) -
    egbOffShellGibbsA (egbCoexistenceAPressure k τ θ) (egbCoexistenceATemperature k τ θ)
      (egbCoexistenceACharge k τ θ) (egbCoexistenceACouplingRoot k τ θ) l (exp k) =
    exp k * (egbCoexistenceAReducedLogGibbs τ θ u - egbCoexistenceAReducedLogGibbs τ θ 0) := by
  have h0 := egbCoexistenceA_gibbs_scaling k τ θ l 0
  simp only [exp_zero, mul_one] at h0
  rw [egbCoexistenceA_gibbs_scaling, h0]
  ring

theorem egbCoexistenceA_equal_gibbs (k τ θ l : ℝ) :
    egbOffShellGibbsA (egbCoexistenceAPressure k τ θ) (egbCoexistenceATemperature k τ θ)
      (egbCoexistenceACharge k τ θ) (egbCoexistenceACouplingRoot k τ θ) l (egbCoexistenceSmallRadius k τ) =
    egbOffShellGibbsA (egbCoexistenceAPressure k τ θ) (egbCoexistenceATemperature k τ θ)
      (egbCoexistenceACharge k τ θ) (egbCoexistenceACouplingRoot k τ θ) l (egbCoexistenceLargeRadius k) := by
  have h := egbCoexistenceA_gibbs_gap k τ θ l (log (thermalRatio τ))
  rw [egbCoexistenceAReducedLogGibbs_balance, sub_self, mul_zero, exp_log (thermalRatio_pos τ)] at h
  simpa only [egbCoexistenceSmallRadius, egbCoexistenceLargeRadius, mul_comm (exp k)] using sub_eq_zero.mp h

/-- Global minimum over every positive physical radius, parameterized by its logarithm. -/
theorem egbCoexistenceA_global_minimum (k τ θ l x : ℝ) :
    egbOffShellGibbsA (egbCoexistenceAPressure k τ θ) (egbCoexistenceATemperature k τ θ)
      (egbCoexistenceACharge k τ θ) (egbCoexistenceACouplingRoot k τ θ) l (egbCoexistenceLargeRadius k) ≤
    egbOffShellGibbsA (egbCoexistenceAPressure k τ θ) (egbCoexistenceATemperature k τ θ)
      (egbCoexistenceACharge k τ θ) (egbCoexistenceACouplingRoot k τ θ) l (exp x) := by
  have h := egbCoexistenceA_gibbs_gap k τ θ l (x - k)
  have hr : exp k * exp (x - k) = exp x := by rw [← exp_add]; congr 1; ring
  rw [hr] at h
  have hgap := sub_nonneg.mpr (egbCoexistenceAReducedLogGibbs_global_minimum τ θ (x - k))
  exact sub_nonneg.mp (h.symm ▸ mul_nonneg (le_of_lt (exp_pos k)) hgap)

/-- Precisely the two physical phase radii minimize Gibbs energy; no extra minima are hidden. -/
theorem egbCoexistenceA_global_minimizers_iff (k τ θ l x : ℝ) :
    egbOffShellGibbsA (egbCoexistenceAPressure k τ θ) (egbCoexistenceATemperature k τ θ)
      (egbCoexistenceACharge k τ θ) (egbCoexistenceACouplingRoot k τ θ) l (exp x) =
    egbOffShellGibbsA (egbCoexistenceAPressure k τ θ) (egbCoexistenceATemperature k τ θ)
      (egbCoexistenceACharge k τ θ) (egbCoexistenceACouplingRoot k τ θ) l (egbCoexistenceLargeRadius k) ↔
    exp x = egbCoexistenceSmallRadius k τ ∨ exp x = egbCoexistenceLargeRadius k := by
  have h := egbCoexistenceA_gibbs_gap k τ θ l (x - k)
  have hr : exp k * exp (x - k) = exp x := by rw [← exp_add]; congr 1; ring
  rw [hr] at h
  have hz : x - k = log (thermalRatio τ) ↔ exp x = egbCoexistenceSmallRadius k τ := by
    constructor
    · intro he
      have hx : x = k + log (thermalRatio τ) := by linarith
      rw [hx, exp_add, exp_log (thermalRatio_pos τ), egbCoexistenceSmallRadius, mul_comm]
    · intro he
      have he' : exp (x - k) = thermalRatio τ := by
        apply (mul_left_cancel₀ (exp_ne_zero k))
        rw [hr, he, egbCoexistenceSmallRadius, mul_comm]
      rw [← log_exp (x - k), he']
  have h0 : x - k = 0 ↔ exp x = egbCoexistenceLargeRadius k := by
    change x - k = 0 ↔ exp x = exp k
    rw [sub_eq_zero, exp_eq_exp]
  dsimp only [egbCoexistenceLargeRadius] at h0 ⊢
  rw [← sub_eq_zero, h]
  simp only [mul_eq_zero, exp_ne_zero, false_or, sub_eq_zero,
    egbCoexistenceAReducedLogGibbs_minimizers_iff, hz, h0]

/-- The intervening stationary radius carries a strictly positive physical energy barrier. -/
theorem egbCoexistenceA_gibbs_barrier_pos (k τ θ l : ℝ) :
    0 < egbOffShellGibbsA (egbCoexistenceAPressure k τ θ) (egbCoexistenceATemperature k τ θ)
      (egbCoexistenceACharge k τ θ) (egbCoexistenceACouplingRoot k τ θ) l (exp k * egbCoexistenceAMiddleRadius τ θ) -
    egbOffShellGibbsA (egbCoexistenceAPressure k τ θ) (egbCoexistenceATemperature k τ θ)
      (egbCoexistenceACharge k τ θ) (egbCoexistenceACouplingRoot k τ θ) l (egbCoexistenceLargeRadius k) := by
  have h := egbCoexistenceA_gibbs_gap k τ θ l (log (egbCoexistenceAMiddleRadius τ θ))
  rw [exp_log (egbCoexistenceAMiddleRadius_pos τ θ)] at h
  exact h.symm ▸ mul_pos (exp_pos k) (egbCoexistenceAReducedLogGibbs_barrier_pos τ θ)

/-- Exactly three physical positive radii have the coexistence temperature. -/
theorem egbCoexistenceA_stationary_temperature_iff (k τ θ u : ℝ) :
    egbTemperatureA (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ) (exp k * exp u) = egbCoexistenceATemperature k τ θ ↔
    exp u = thermalRatio τ ∨ exp u = egbCoexistenceAMiddleRadius τ θ ∨ exp u = 1 := by
  have hEOS : egbTemperatureA (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ) (exp k * exp u) = egbCoexistenceATemperature k τ θ ↔
    egbPressureA (egbCoexistenceATemperature k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ) (exp k * exp u) = egbCoexistenceAPressure k τ θ := by
    rw [← exp_add]
    constructor
    · intro h
      rw [← h, egbPressureA_temperature]
    · intro h
      rw [← h, egbTemperatureA_pressure]
  rw [hEOS, ← sub_eq_zero, egbCoexistenceA_pressure_residual]
  have hden : 8 * Real.pi * exp k ^ 2 * exp u ^ 4 ≠ 0 := by positivity
  have hsmall : 2 * exp u ≠ 0 := by positivity
  have hs := egbCoexistenceA_stationary_radii_iff τ θ u
  rw [(egbCoexistenceAReducedLogGibbs_hasDerivAt τ θ u).deriv] at hs
  simp only [div_eq_zero_iff, hsmall, or_false] at hs
  simpa only [div_eq_zero_iff, hden, or_false, neg_eq_zero] using hs

theorem egbCoexistenceA_middle_temperature (k τ θ : ℝ) :
    egbTemperatureA (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ) (exp k * egbCoexistenceAMiddleRadius τ θ) =
    egbCoexistenceATemperature k τ θ := by
  have h := (egbCoexistenceA_stationary_temperature_iff k τ θ (log (egbCoexistenceAMiddleRadius τ θ))).2
    (Or.inr (Or.inl (exp_log (egbCoexistenceAMiddleRadius_pos τ θ))))
  simpa only [exp_log (egbCoexistenceAMiddleRadius_pos τ θ)] using h

end GaloisForLFunctions.HTGeometry

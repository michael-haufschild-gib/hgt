import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanDeficitDomination

/-!
# The sixth-order deficit integrand and its positive amplitude

The limiting integrand is a line. Its integral is the positive product
of the middle displacement and the mean force, divided by two. Equivalent
formulas connect it to the previously proved barrier amplitude.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAMeanDeficitIntegrand (w φ τ u : ℝ) : ℝ :=
  egbFixedChargeAMeanRadius w φ τ * egbFixedChargeAMiddleQuadraticShift τ φ * egbFixedChargeAMeanDeficitForce τ φ u

def egbFixedChargeAMeanDeficitCoefficient (w φ : ℝ) : ℝ :=
  egbFixedChargeACriticalRadius w φ * (5 - 14 * egbFixedChargeACriticalCouplingWeight φ) ^ 2 /
    (2400 * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ))

def egbFixedChargeAMeanDeficitLimitIntegrand (w φ u : ℝ) : ℝ := 2 * egbFixedChargeAMeanDeficitCoefficient w φ * (1 - u)

theorem egbFixedChargeAMeanDeficitCoefficient_pos (w φ : ℝ) : 0 < egbFixedChargeAMeanDeficitCoefficient w φ := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have h5 : 0 < 5 - 14 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  unfold egbFixedChargeAMeanDeficitCoefficient
  positivity

theorem egbFixedChargeAMeanDeficitCoefficient_force_product (w φ : ℝ) :
    egbFixedChargeACriticalRadius w φ * egbFixedChargeAMiddleMeanCorrection φ * egbFixedChargeAMeanGibbsForceCoefficient φ =
      2 * egbFixedChargeAMeanDeficitCoefficient w φ := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  unfold egbFixedChargeAMiddleMeanCorrection egbFixedChargeAMeanGibbsForceCoefficient egbFixedChargeAMeanDeficitCoefficient
  field_simp <;> ring

theorem egbFixedChargeAMeanDeficitCoefficient_barrier_product (w φ : ℝ) :
    egbFixedChargeAMeanDeficitCoefficient w φ =
      2 * egbFixedChargeAGibbsBarrierCoefficient w φ * egbFixedChargeAMiddleMeanCorrection φ ^ 2 := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  unfold egbFixedChargeAMeanDeficitCoefficient egbFixedChargeAGibbsBarrierCoefficient egbFixedChargeAMiddleMeanCorrection
  field_simp <;> ring

theorem egbFixedChargeAMeanDeficitCoefficient_barrier_ratio (w φ : ℝ) :
    egbFixedChargeAMeanDeficitCoefficient w φ / egbFixedChargeAGibbsBarrierCoefficient w φ =
      2 * egbFixedChargeAMiddleMeanCorrection φ ^ 2 := by
  have hB := egbFixedChargeAGibbsBarrierCoefficient_pos w φ
  rw [egbFixedChargeAMeanDeficitCoefficient_barrier_product]
  field_simp

theorem egbFixedChargeAMeanDeficitIntegrand_critical_limit (w φ u : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanDeficitIntegrand w φ τ u) atBot
      (𝓝 (egbFixedChargeAMeanDeficitLimitIntegrand w φ u)) := by
  have h := ((egbFixedChargeAMeanRadius_critical_limit w φ).mul
    (egbFixedChargeAMiddleQuadraticShift_critical_limit φ)).mul (egbFixedChargeAMeanDeficitForce_critical_limit φ u)
  have he : egbFixedChargeACriticalRadius w φ * egbFixedChargeAMiddleMeanCorrection φ *
      (egbFixedChargeAMeanGibbsForceCoefficient φ * (1 - u)) = egbFixedChargeAMeanDeficitLimitIntegrand w φ u := by
    calc
      _ = (egbFixedChargeACriticalRadius w φ * egbFixedChargeAMiddleMeanCorrection φ *
        egbFixedChargeAMeanGibbsForceCoefficient φ) * (1 - u) := by ring
      _ = _ := by rw [egbFixedChargeAMeanDeficitCoefficient_force_product]; rfl
  rw [he] at h
  exact h

theorem egbFixedChargeAMeanDeficitIntegrand_measurable (w φ τ : ℝ) : Measurable (egbFixedChargeAMeanDeficitIntegrand w φ τ) := by
  unfold egbFixedChargeAMeanDeficitIntegrand egbFixedChargeAMeanDeficitForce egbFixedChargeAMeanDeficitPolynomial
  fun_prop

theorem egbFixedChargeAMeanDeficitIntegrand_continuousOn (w φ τ : ℝ) :
    ContinuousOn (egbFixedChargeAMeanDeficitIntegrand w φ τ) (Icc (0 : ℝ) 1) := by
  unfold egbFixedChargeAMeanDeficitIntegrand
  exact continuousOn_const.mul (egbFixedChargeAMeanDeficitForce_continuousOn τ φ)

theorem egbFixedChargeAMeanDeficitIntegrand_intervalIntegrable (w φ τ : ℝ) :
    IntervalIntegrable (egbFixedChargeAMeanDeficitIntegrand w φ τ) volume 0 1 :=
  ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (egbFixedChargeAMeanDeficitIntegrand_continuousOn w φ τ)

theorem egbFixedChargeAMeanDeficitIntegrand_dominated (w φ : ℝ) :
    ∀ᶠ τ in atBot, ∀ u ∈ Icc (0 : ℝ) 1,
      |egbFixedChargeAMeanDeficitIntegrand w φ τ u| ≤ 11 * (egbFixedChargeACriticalRadius w φ + 1) := by
  have hmhi := (egbFixedChargeAMeanRadius_critical_limit w φ).eventually_lt_const
    (show egbFixedChargeACriticalRadius w φ < egbFixedChargeACriticalRadius w φ + 1 by linarith)
  filter_upwards [hmhi, egbFixedChargeAMiddleQuadraticShift_eventually_bounds φ,
    egbFixedChargeAMeanDeficitForce_dominated φ] with τ hmhi hc hforce
  intro u hu
  have hm := egbFixedChargeAMeanRadius_pos w φ τ
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hmabs : |egbFixedChargeAMeanRadius w φ τ| ≤ egbFixedChargeACriticalRadius w φ + 1 := by
    rw [abs_of_pos hm]; exact hmhi.le
  have hcabs : |egbFixedChargeAMiddleQuadraticShift τ φ| ≤ 1 := abs_le.mpr ⟨hc.1.le, by linarith [hc.2]⟩
  unfold egbFixedChargeAMeanDeficitIntegrand
  simp only [abs_mul]
  calc
    _ ≤ ((egbFixedChargeACriticalRadius w φ + 1) * 1) * 11 :=
      mul_le_mul (mul_le_mul hmabs hcabs (abs_nonneg _) (by positivity)) (hforce u hu) (abs_nonneg _) (by positivity)
    _ = _ := by ring

end GaloisForLFunctions.HTGeometry

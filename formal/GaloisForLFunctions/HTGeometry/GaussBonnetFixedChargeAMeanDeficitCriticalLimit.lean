import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanDeficitIntegral

/-!
# The actual mean energy deficit closes at sixth order

A dominated convergence proof yields the positive coefficient for the
true energy difference between the intermediate equilibrium and the
arithmetic phase mean. Its ratio to the main barrier closes quadratically.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAMeanDeficitIntegrand_integral_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => ∫ u in (0 : ℝ)..1, egbFixedChargeAMeanDeficitIntegrand w φ τ u)
      atBot (𝓝 (egbFixedChargeAMeanDeficitCoefficient w φ)) := by
  have hmeas : ∀ᶠ τ in (atBot : Filter ℝ), AEStronglyMeasurable
      (egbFixedChargeAMeanDeficitIntegrand w φ τ) (volume.restrict (uIoc (0 : ℝ) 1)) :=
    .of_forall (fun τ => (egbFixedChargeAMeanDeficitIntegrand_measurable w φ τ).aestronglyMeasurable)
  have hbound : ∀ᶠ τ in (atBot : Filter ℝ), ∀ᵐ u ∂volume,
      u ∈ uIoc (0 : ℝ) 1 → ‖egbFixedChargeAMeanDeficitIntegrand w φ τ u‖ ≤
        11 * (egbFixedChargeACriticalRadius w φ + 1) := by
    filter_upwards [egbFixedChargeAMeanDeficitIntegrand_dominated w φ] with τ hτ
    apply Filter.Eventually.of_forall
    intro u hu
    have hu' : u ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    simpa only [Real.norm_eq_abs] using hτ u ⟨hu'.1.le, hu'.2⟩
  have hint : IntervalIntegrable (fun _ : ℝ => 11 * (egbFixedChargeACriticalRadius w φ + 1)) volume 0 1 :=
    (continuous_const : Continuous (fun _ : ℝ => 11 * (egbFixedChargeACriticalRadius w φ + 1))).intervalIntegrable 0 1
  have hlim : ∀ᵐ u ∂volume, u ∈ uIoc (0 : ℝ) 1 →
      Tendsto (fun τ => egbFixedChargeAMeanDeficitIntegrand w φ τ u) atBot
        (𝓝 (egbFixedChargeAMeanDeficitLimitIntegrand w φ u)) :=
    .of_forall (fun u _ => egbFixedChargeAMeanDeficitIntegrand_critical_limit w φ u)
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => 11 * (egbFixedChargeACriticalRadius w φ + 1)) hmeas hbound hint hlim
  rwa [egbFixedChargeAMeanDeficitLimitIntegrand_integral] at h

theorem egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanGibbsDeficit w φ τ l / egbCoexistenceASymmetricRatio τ ^ 6)
      atBot (𝓝 (egbFixedChargeAMeanDeficitCoefficient w φ)) := by
  simp only [egbFixedChargeAMeanGibbsDeficit_integral]
  exact egbFixedChargeAMeanDeficitIntegrand_integral_critical_limit w φ

theorem egbFixedChargeAMeanGibbsDeficit_critical_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanGibbsDeficit w φ τ l) atBot (𝓝 (0 : ℝ)) := by
  have h := (egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit w φ l).mul
    (egbCoexistenceASymmetricRatio_critical_limit.pow 6)
  simp only [zero_pow (by norm_num : (6 : ℕ) ≠ 0), mul_zero] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMeanGibbsDeficit_eventually_pos (w φ l : ℝ) :
    ∀ᶠ τ in atBot, 0 < egbFixedChargeAMeanGibbsDeficit w φ τ l := by
  have h := (egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit w φ l).eventually_const_lt
    (egbFixedChargeAMeanDeficitCoefficient_pos w φ)
  filter_upwards [h] with τ hτ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hd6 : 0 < egbCoexistenceASymmetricRatio τ ^ 6 := by positivity
  have hcross := (lt_div_iff₀ hd6).1 hτ
  linarith

theorem egbFixedChargeAMeanGibbsDeficit_barrier_quadratic_limit (w φ l₁ l₂ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMeanGibbsDeficit w φ τ l₁ / egbFixedChargeAGibbsBarrier w φ τ l₂) /
      egbCoexistenceASymmetricRatio τ ^ 2) atBot (𝓝 (2 * egbFixedChargeAMiddleMeanCorrection φ ^ 2)) := by
  have h := (egbFixedChargeAMeanGibbsDeficit_sixth_critical_limit w φ l₁).div
    (egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l₂) (egbFixedChargeAGibbsBarrierCoefficient_pos w φ).ne'
  rw [egbFixedChargeAMeanDeficitCoefficient_barrier_ratio] at h
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMeanGibbsDeficit_barrier_ratio_limit (w φ l₁ l₂ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanGibbsDeficit w φ τ l₁ / egbFixedChargeAGibbsBarrier w φ τ l₂)
      atBot (𝓝 (0 : ℝ)) := by
  have h := (egbFixedChargeAMeanGibbsDeficit_barrier_quadratic_limit w φ l₁ l₂).mul
    (egbCoexistenceASymmetricRatio_critical_limit.pow 2)
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeABarrierIntegral
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeABarrierDomination
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalStates

/-!
# Quartic closing of the physical coexistence Gibbs barrier

Dominated convergence applies to the actual Gibbs derivative on the
constructed path from the large phase to the intermediate equilibrium.
The coefficient is the critical radial quartic coefficient times r_c⁴.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeABarrierIntegrand_integral_critical_limit (w φ : ℝ) :
    Tendsto (fun τ => ∫ u in (0 : ℝ)..1, egbFixedChargeABarrierIntegrand w φ τ u)
      atBot (𝓝 (egbFixedChargeAGibbsBarrierCoefficient w φ)) := by
  have hmeas : ∀ᶠ τ in (atBot : Filter ℝ), AEStronglyMeasurable
      (egbFixedChargeABarrierIntegrand w φ τ) (volume.restrict (uIoc (0 : ℝ) 1)) :=
    .of_forall (fun τ => (egbFixedChargeABarrierIntegrand_measurable w φ τ).aestronglyMeasurable)
  have hbound : ∀ᶠ τ in (atBot : Filter ℝ), ∀ᵐ u ∂volume,
      u ∈ uIoc (0 : ℝ) 1 → ‖egbFixedChargeABarrierIntegrand w φ τ u‖ ≤
        20 * (egbFixedChargeACriticalRadius w φ + 1) := by
    filter_upwards [egbFixedChargeABarrierIntegrand_dominated w φ] with τ hτ
    apply Filter.Eventually.of_forall
    intro u hu
    have hu' : u ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    simpa only [Real.norm_eq_abs] using hτ u ⟨hu'.1.le, hu'.2⟩
  have hint : IntervalIntegrable (fun _ : ℝ => 20 * (egbFixedChargeACriticalRadius w φ + 1)) volume 0 1 :=
    (continuous_const : Continuous (fun _ : ℝ => 20 * (egbFixedChargeACriticalRadius w φ + 1))).intervalIntegrable 0 1
  have hlim : ∀ᵐ u ∂volume, u ∈ uIoc (0 : ℝ) 1 →
      Tendsto (fun τ => egbFixedChargeABarrierIntegrand w φ τ u) atBot
        (𝓝 (egbFixedChargeABarrierLimitIntegrand w φ u)) :=
    .of_forall (fun u _ => egbFixedChargeABarrierIntegrand_critical_limit w φ u)
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => 20 * (egbFixedChargeACriticalRadius w φ + 1)) hmeas hbound hint hlim
  rwa [egbFixedChargeABarrierLimitIntegrand_integral] at h

theorem egbFixedChargeAGibbsBarrier_quartic_critical_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsBarrier w φ τ l / egbCoexistenceASymmetricRatio τ ^ (4 : ℕ))
      atBot (𝓝 (egbFixedChargeAGibbsBarrierCoefficient w φ)) := by
  simp only [egbFixedChargeAGibbsBarrier_integral]
  exact egbFixedChargeABarrierIntegrand_integral_critical_limit w φ

theorem egbFixedChargeAGibbsBarrier_critical_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsBarrier w φ τ l) atBot (𝓝 (0 : ℝ)) := by
  have h := (egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l).mul
    (egbCoexistenceASymmetricRatio_critical_limit.pow 4)
  simp only [zero_pow (by norm_num : (4 : ℕ) ≠ 0), mul_zero] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAGibbsBarrierCoefficient_critical_quartic (w φ : ℝ) :
    egbFixedChargeAGibbsBarrierCoefficient w φ =
      egbFixedChargeACriticalQuarticCoefficient w φ * egbFixedChargeACriticalRadius w φ ^ (4 : ℕ) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  unfold egbFixedChargeAGibbsBarrierCoefficient egbFixedChargeACriticalQuarticCoefficient
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry

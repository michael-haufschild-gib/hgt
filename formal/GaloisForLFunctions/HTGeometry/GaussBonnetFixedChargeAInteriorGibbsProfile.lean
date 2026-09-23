import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAInteriorGibbsIntegral
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeABarrierCriticalLimit

/-!
# The complete critical interior Gibbs profile

At radius m(1+d sin ψ), the actual Gibbs gap divided by d⁴ tends to
B cos⁴ψ. Dividing instead by the actual moving-middle barrier eliminates
B entirely, giving the same quartic profile for every conserved mixture.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAInteriorGibbsIntegrand_integral_critical_limit (w φ ψ : ℝ) :
    Tendsto (fun τ => ∫ u in (0 : ℝ)..1, egbFixedChargeAInteriorGibbsIntegrand w φ τ ψ u)
      atBot (𝓝 (egbFixedChargeAGibbsBarrierCoefficient w φ * cos ψ ^ (4 : ℕ))) := by
  have hmeas : ∀ᶠ τ in (atBot : Filter ℝ), AEStronglyMeasurable
      (egbFixedChargeAInteriorGibbsIntegrand w φ τ ψ) (volume.restrict (uIoc (0 : ℝ) 1)) :=
    .of_forall (fun τ => (egbFixedChargeAInteriorGibbsIntegrand_measurable w φ τ ψ).aestronglyMeasurable)
  have hbound : ∀ᶠ τ in (atBot : Filter ℝ), ∀ᵐ u ∂volume,
      u ∈ uIoc (0 : ℝ) 1 → ‖egbFixedChargeAInteriorGibbsIntegrand w φ τ ψ u‖ ≤
        20 * (egbFixedChargeACriticalRadius w φ + 1) := by
    filter_upwards [egbFixedChargeAInteriorGibbsIntegrand_dominated w φ] with τ hτ
    apply Filter.Eventually.of_forall
    intro u hu
    have hu' : u ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    simpa only [Real.norm_eq_abs] using hτ ψ u ⟨hu'.1.le, hu'.2⟩
  have hint : IntervalIntegrable (fun _ : ℝ => 20 * (egbFixedChargeACriticalRadius w φ + 1)) volume 0 1 :=
    (continuous_const : Continuous (fun _ : ℝ => 20 * (egbFixedChargeACriticalRadius w φ + 1))).intervalIntegrable 0 1
  have hlim : ∀ᵐ u ∂volume, u ∈ uIoc (0 : ℝ) 1 →
      Tendsto (fun τ => egbFixedChargeAInteriorGibbsIntegrand w φ τ ψ u) atBot
        (𝓝 (egbFixedChargeAInteriorGibbsLimitIntegrand w φ ψ u)) :=
    .of_forall (fun u _ => egbFixedChargeAInteriorGibbsIntegrand_critical_limit w φ ψ u)
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => 20 * (egbFixedChargeACriticalRadius w φ + 1)) hmeas hbound hint hlim
  rwa [egbFixedChargeAInteriorGibbsLimitIntegrand_integral] at h

theorem egbFixedChargeAInteriorGibbsGap_quartic_critical_limit (w φ l ψ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAInteriorGibbsGap w φ τ l ψ / egbCoexistenceASymmetricRatio τ ^ (4 : ℕ))
      atBot (𝓝 (egbFixedChargeAGibbsBarrierCoefficient w φ * cos ψ ^ (4 : ℕ))) := by
  simp only [egbFixedChargeAInteriorGibbsGap_integral]
  exact egbFixedChargeAInteriorGibbsIntegrand_integral_critical_limit w φ ψ

theorem egbFixedChargeAInteriorGibbsGap_barrier_ratio_limit (w φ l₁ l₂ ψ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAInteriorGibbsGap w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂)
      atBot (𝓝 (cos ψ ^ (4 : ℕ))) := by
  have hB := egbFixedChargeAGibbsBarrierCoefficient_pos w φ
  have h := (egbFixedChargeAInteriorGibbsGap_quartic_critical_limit w φ l₁ ψ).div
    (egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l₂) hB.ne'
  have he : egbFixedChargeAGibbsBarrierCoefficient w φ * cos ψ ^ (4 : ℕ) / egbFixedChargeAGibbsBarrierCoefficient w φ =
      cos ψ ^ (4 : ℕ) := by field_simp
  rw [he] at h
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAInteriorGibbsGap_critical_limit (w φ l ψ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAInteriorGibbsGap w φ τ l ψ) atBot (𝓝 (0 : ℝ)) := by
  have h := (egbFixedChargeAInteriorGibbsGap_quartic_critical_limit w φ l ψ).mul
    (egbCoexistenceASymmetricRatio_critical_limit.pow 4)
  simp only [zero_pow (by norm_num : (4 : ℕ) ≠ 0), mul_zero] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMeanGibbsGap_quartic_critical_limit (w φ l : ℝ) :
    Tendsto (fun τ => (egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
      (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAMeanRadius w φ τ) -
      egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
        (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ)) / egbCoexistenceASymmetricRatio τ ^ (4 : ℕ))
      atBot (𝓝 (egbFixedChargeAGibbsBarrierCoefficient w φ)) := by
  simpa only [egbFixedChargeAInteriorGibbsGap, egbFixedChargeAInteriorRadius_mean, cos_zero, one_pow, mul_one] using
    egbFixedChargeAInteriorGibbsGap_quartic_critical_limit w φ l 0

theorem egbFixedChargeAMeanGibbsGap_barrier_ratio_limit (w φ l₁ l₂ : ℝ) :
    Tendsto (fun τ => (egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
      (exp w * cos φ) (exp w * sin φ) l₁ (egbFixedChargeAMeanRadius w φ τ) -
      egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
        (exp w * cos φ) (exp w * sin φ) l₁ (egbFixedChargeALargeRadius w φ τ)) / egbFixedChargeAGibbsBarrier w φ τ l₂)
      atBot (𝓝 (1 : ℝ)) := by
  simpa only [egbFixedChargeAInteriorGibbsGap, egbFixedChargeAInteriorRadius_mean, cos_zero, one_pow] using
    egbFixedChargeAInteriorGibbsGap_barrier_ratio_limit w φ l₁ l₂ 0

end GaloisForLFunctions.HTGeometry

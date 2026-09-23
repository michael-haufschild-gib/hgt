import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsOddIntegral

/-!
# First asymmetric correction to the actual Gibbs energy profile

For every fixed interior coordinate t = sin ψ, the normalized quartic
profile has first correction C₁ t (1 - t²)². This follows from the exact
energy integral and dominated convergence, with no assumed expansion of
Gibbs energy or interchange of unproved asymptotic series.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAGibbsOddIntegrand_integral_critical_limit (w φ ψ : ℝ) :
    Tendsto (fun τ => ∫ u in (0 : ℝ)..1, egbFixedChargeAGibbsOddIntegrand w φ τ ψ u)
      atBot (𝓝 (egbFixedChargeAGibbsOddCoefficient w φ * sin ψ * cos ψ ^ (4 : ℕ))) := by
  have hmeas : ∀ᶠ τ in (atBot : Filter ℝ), AEStronglyMeasurable
      (egbFixedChargeAGibbsOddIntegrand w φ τ ψ) (volume.restrict (uIoc (0 : ℝ) 1)) :=
    .of_forall (fun τ => (egbFixedChargeAGibbsOddIntegrand_measurable w φ τ ψ).aestronglyMeasurable)
  have hbound : ∀ᶠ τ in (atBot : Filter ℝ), ∀ᵐ u ∂volume,
      u ∈ uIoc (0 : ℝ) 1 → ‖egbFixedChargeAGibbsOddIntegrand w φ τ ψ u‖ ≤
        160 * (egbFixedChargeAGibbsCriticalPrefactor w φ + 1) := by
    filter_upwards [egbFixedChargeAGibbsOddIntegrand_dominated w φ] with τ hτ
    apply Filter.Eventually.of_forall
    intro u hu
    have hu' : u ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    simpa only [Real.norm_eq_abs] using hτ ψ u ⟨hu'.1.le, hu'.2⟩
  have hint : IntervalIntegrable (fun _ : ℝ => 160 * (egbFixedChargeAGibbsCriticalPrefactor w φ + 1)) volume 0 1 :=
    (continuous_const : Continuous (fun _ : ℝ => 160 * (egbFixedChargeAGibbsCriticalPrefactor w φ + 1))).intervalIntegrable 0 1
  have hlim : ∀ᵐ u ∂volume, u ∈ uIoc (0 : ℝ) 1 →
      Tendsto (fun τ => egbFixedChargeAGibbsOddIntegrand w φ τ ψ u) atBot
        (𝓝 (egbFixedChargeAGibbsOddLimitIntegrand w φ ψ u)) :=
    .of_forall (fun u _ => egbFixedChargeAGibbsOddIntegrand_critical_limit w φ ψ u)
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => 160 * (egbFixedChargeAGibbsCriticalPrefactor w φ + 1)) hmeas hbound hint hlim
  rwa [egbFixedChargeAGibbsOddLimitIntegrand_integral] at h

theorem egbFixedChargeAInteriorGibbsGap_first_correction_limit (w φ l ψ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAInteriorGibbsGap w φ τ l ψ / egbCoexistenceASymmetricRatio τ ^ (4 : ℕ) -
      egbFixedChargeAGibbsBarrierCoefficient w φ * cos ψ ^ (4 : ℕ)) / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (egbFixedChargeAGibbsOddCoefficient w φ * sin ψ * cos ψ ^ (4 : ℕ))) := by
  simp only [egbFixedChargeAGibbsOddGap_integral]
  exact egbFixedChargeAGibbsOddIntegrand_integral_critical_limit w φ ψ

theorem egbFixedChargeAInteriorGibbsGap_fifth_order_limit (w φ l ψ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAInteriorGibbsGap w φ τ l ψ -
      egbFixedChargeAGibbsBarrierCoefficient w φ * cos ψ ^ (4 : ℕ) * egbCoexistenceASymmetricRatio τ ^ (4 : ℕ)) /
      egbCoexistenceASymmetricRatio τ ^ (5 : ℕ))
      atBot (𝓝 (egbFixedChargeAGibbsOddCoefficient w φ * sin ψ * cos ψ ^ (4 : ℕ))) := by
  convert egbFixedChargeAInteriorGibbsGap_first_correction_limit w φ l ψ using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp
  <;> ring

theorem egbFixedChargeAMeanGibbsGap_first_correction_limit (w φ l : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAInteriorGibbsGap w φ τ l 0 / egbCoexistenceASymmetricRatio τ ^ (4 : ℕ) -
      egbFixedChargeAGibbsBarrierCoefficient w φ) / egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  simpa only [sin_zero, cos_zero, one_pow, mul_one, mul_zero, zero_mul] using
    egbFixedChargeAInteriorGibbsGap_first_correction_limit w φ l 0

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsOddUniformIntegrand

/-!
# Uniform first correction of the actual Gibbs energy

The exact integral identity and a uniform integral error estimate prove
the first Gibbs correction simultaneously across the entire phase
interval, including its endpoints. No convergence of the chosen radius
coordinate is required.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAInteriorGibbsGap_uniform_first_correction_limit (w φ l : ℝ) :
    TendstoUniformly (fun τ ψ => (egbFixedChargeAInteriorGibbsGap w φ τ l ψ / egbCoexistenceASymmetricRatio τ ^ (4 : ℕ) -
      egbFixedChargeAGibbsBarrierCoefficient w φ * cos ψ ^ (4 : ℕ)) / egbCoexistenceASymmetricRatio τ)
      (fun ψ => egbFixedChargeAGibbsOddCoefficient w φ * sin ψ * cos ψ ^ (4 : ℕ)) atBot := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have h := (Metric.tendstoUniformlyOn_iff.mp (egbFixedChargeAGibbsOddIntegrand_uniform_critical_limit w φ))
    (ε / 2) (by positivity)
  filter_upwards [h] with τ hτ
  intro ψ
  have hbound : ∀ u ∈ uIoc (0 : ℝ) 1,
      ‖egbFixedChargeAGibbsOddLimitIntegrand w φ ψ u - egbFixedChargeAGibbsOddIntegrand w φ τ ψ u‖ ≤ ε / 2 := by
    intro u hu
    have hu' : u ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    have he := hτ (ψ, u) ⟨mem_univ _, ⟨hu'.1.le, hu'.2⟩⟩
    simpa only [Real.norm_eq_abs, Real.dist_eq] using he.le
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  norm_num only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at hi
  rw [Real.dist_eq, egbFixedChargeAGibbsOddGap_integral, ← egbFixedChargeAGibbsOddLimitIntegrand_integral]
  rw [← intervalIntegral.integral_sub ((egbFixedChargeAGibbsOddLimitIntegrand_continuous w φ ψ).intervalIntegrable 0 1)
    (egbFixedChargeAGibbsOddIntegrand_intervalIntegrable w φ τ ψ)]
  exact hi.trans_lt (by linarith)

theorem egbFixedChargeAInteriorGibbsGap_uniform_fifth_order_limit (w φ l : ℝ) :
    TendstoUniformly (fun τ ψ => (egbFixedChargeAInteriorGibbsGap w φ τ l ψ -
      egbFixedChargeAGibbsBarrierCoefficient w φ * cos ψ ^ (4 : ℕ) * egbCoexistenceASymmetricRatio τ ^ (4 : ℕ)) /
      egbCoexistenceASymmetricRatio τ ^ (5 : ℕ))
      (fun ψ => egbFixedChargeAGibbsOddCoefficient w φ * sin ψ * cos ψ ^ (4 : ℕ)) atBot := by
  convert egbFixedChargeAInteriorGibbsGap_uniform_first_correction_limit w φ l using 1
  funext τ ψ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.AnalyticPolynomialHardyFactorization
import GaloisForLFunctions.HTGeometry.HardyCoefficientBound

/-!
# Square-summable coefficient factors for analytic polynomials

This module upgrades finite polynomial inner--outer factorization to the coefficient form used in
the F. and M. Riesz compactness argument.
-/

open MeasureTheory Complex Filter Topology Set Polynomial
open scoped Real ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The normalized boundary `L¹` norm of a complex polynomial. -/
noncomputable def polynomialBoundaryL1 (p : ℂ[X]) : ℝ :=
  (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖p.eval (circleMap 0 1 θ)‖

private theorem continuousOn_multiset_prod_coeff {ι : Type*} (s : Multiset ι)
    (f : ι → ℂ → ℂ) (t : Set ℂ)
    (hf : ∀ a ∈ s, ContinuousOn (f a) t) :
    ContinuousOn (fun z => (s.map fun a => f a z).prod) t := by
  induction s using Multiset.induction_on with
  | empty => simpa using (continuousOn_const : ContinuousOn (fun _ : ℂ => (1 : ℂ)) t)
  | @cons a s ih =>
      simpa using! (hf a (by simp)).mul
        (ih (fun x hx => hf x (by simp [hx])))

/-- The finite Blaschke product is continuous on the closed unit disk. -/
theorem continuousOn_polynomialBlaschke_closedBall (p : ℂ[X]) :
    ContinuousOn (polynomialBlaschke p) (Metric.closedBall 0 1) := by
  unfold polynomialBlaschke
  apply continuousOn_multiset_prod_coeff
  intro a ha
  have haI : ‖a‖ < 1 := (Multiset.mem_filter.mp ha).2
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro z hz
  apply blaschkeFactor_den_ne_zero haI
  simpa [Metric.mem_closedBall, dist_zero_right] using hz

/-- The two Hardy factors of an analytic polynomial have square-summable Taylor coefficients, and
both squared coefficient norms are bounded by the boundary `L¹` norm of the polynomial. -/
theorem exists_polynomial_hardy_coefficients {p : ℂ[X]} (hp : p ≠ 0) :
    ∃ g h : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.ball 0 1) ∧
      AnalyticOnNhd ℂ h (Metric.ball 0 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, g z * h z = p.eval z) ∧
      Memℓp (fun k => (cauchyPowerSeries g 0 (1 / 2 : NNReal)).coeff k) 2 ∧
      Memℓp (fun k => (cauchyPowerSeries h 0 (1 / 2 : NNReal)).coeff k) 2 ∧
      (∑' k, ‖(cauchyPowerSeries g 0 (1 / 2 : NNReal)).coeff k‖ ^ 2)
        ≤ polynomialBoundaryL1 p ∧
      (∑' k, ‖(cauchyPowerSeries h 0 (1 / 2 : NNReal)).coeff k‖ ^ 2)
        ≤ polynomialBoundaryL1 p := by
  obtain ⟨g, h, hg, hh, hprod, hhmod, hgmod⟩ :=
    exists_polynomial_hardy_factorization_open hp
  have hga : AnalyticOnNhd ℂ g (Metric.ball 0 1) := hg.analyticOnNhd Metric.isOpen_ball
  have hha : AnalyticOnNhd ℂ h (Metric.ball 0 1) := hh.analyticOnNhd Metric.isOpen_ball
  have hIoo : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := by
    rw [← Set.Ioi_inter_Iio]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos)) self_mem_nhdsWithin
  have hlimhInt := tendsto_intervalIntegral_circleMap_radius_of_continuousOn
    (F := fun z => ‖polynomialOuterization p z‖)
    (differentiable_polynomialOuterization p).continuous.norm.continuousOn
  have hlimhRaw := hlimhInt.const_mul ((2 * π)⁻¹)
  have hlimhEq : (fun r : ℝ => (2 * π)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * π), ‖polynomialOuterization p (circleMap 0 r θ)‖)
      =ᶠ[𝓝[<] (1 : ℝ)] circleMeanSq h := by
    filter_upwards [hIoo] with r hr
    rw [circleMeanSq]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    symm
    exact hhmod (circleMap 0 r θ) (by
      rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero,
        abs_of_nonneg hr.1.le]
      exact hr.2)
  have hboundaryOuter :
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
          ‖polynomialOuterization p (circleMap 0 1 θ)‖ = polynomialBoundaryL1 p := by
    rw [polynomialBoundaryL1]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    apply norm_polynomialOuterization_eq
    rw [norm_circleMap_zero]
    norm_num
  rw [hboundaryOuter] at hlimhRaw
  have hlimh : Tendsto (circleMeanSq h) (𝓝[<] (1 : ℝ)) (𝓝 (polynomialBoundaryL1 p)) :=
    Filter.Tendsto.congr' hlimhEq hlimhRaw
  let FG : ℂ → ℝ := fun z => ‖polynomialBlaschke p z‖ ^ 2 *
    ‖polynomialOuterization p z‖
  have hFG : ContinuousOn FG (Metric.closedBall 0 1) :=
    ((continuousOn_polynomialBlaschke_closedBall p).norm.pow 2).mul
      ((differentiable_polynomialOuterization p).continuous.norm.continuousOn)
  have hlimgInt := tendsto_intervalIntegral_circleMap_radius_of_continuousOn hFG
  have hlimgRaw := hlimgInt.const_mul ((2 * π)⁻¹)
  have hlimgEq : (fun r : ℝ => (2 * π)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * π), FG (circleMap 0 r θ))
      =ᶠ[𝓝[<] (1 : ℝ)] circleMeanSq g := by
    filter_upwards [hIoo] with r hr
    rw [circleMeanSq]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    symm
    exact hgmod (circleMap 0 r θ) (by
      rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero,
        abs_of_nonneg hr.1.le]
      exact hr.2)
  have hboundaryG :
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), FG (circleMap 0 1 θ) =
        polynomialBoundaryL1 p := by
    rw [polynomialBoundaryL1]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    change ‖polynomialBlaschke p (circleMap 0 1 θ)‖ ^ 2 *
      ‖polynomialOuterization p (circleMap 0 1 θ)‖ = _
    rw [norm_polynomialBlaschke_eq_one p (by
      rw [norm_circleMap_zero]
      norm_num), one_pow, one_mul]
    exact norm_polynomialOuterization_eq p (by
      rw [norm_circleMap_zero]
      norm_num)
  rw [hboundaryG] at hlimgRaw
  have hlimg : Tendsto (circleMeanSq g) (𝓝[<] (1 : ℝ)) (𝓝 (polynomialBoundaryL1 p)) :=
    Filter.Tendsto.congr' hlimgEq hlimgRaw
  have hgcoeff := cauchyPowerSeries_coeff_memℓp_two_of_circleMeanSq_tendsto hga hlimg
  have hhcoeff := cauchyPowerSeries_coeff_memℓp_two_of_circleMeanSq_tendsto hha hlimh
  exact ⟨g, h, hga, hha, hprod, hgcoeff.1, hhcoeff.1, hgcoeff.2, hhcoeff.2⟩

end
end GaloisForLFunctions.HTGeometry

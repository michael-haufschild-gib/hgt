import GaloisForLFunctions.HTGeometry.PoissonKernelIntegrals
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# The `L²` mass of the Cauchy kernel on a vertical line

`∫_ℝ dt/(a² + (t−c)²) = π/a` is the total mass of the Poisson kernel; on the vertical line
`Re s = σ` it says that `s ↦ (Z − s)^{-1}` has square-integral `π/(σ − Re Z)`, which tends to zero
as the line moves right.  This is the estimate that kills the right-hand vertical edge of Burnol's
rectangle when its half-width tends to infinity.

## Main results

* `integral_inv_sq_add_sq`
* `integral_norm_sq_cauchyKernel_line`
-/

open MeasureTheory Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem integral_inv_sq_add_sq_shift {a c : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, (a ^ (2 : ℕ) + (t - c) ^ (2 : ℕ))⁻¹) = Real.pi / a := by
  have hshift : (∫ t : ℝ, (a ^ (2 : ℕ) + (t - c) ^ (2 : ℕ))⁻¹) = ∫ t : ℝ, (a ^ (2 : ℕ) + t ^ (2 : ℕ))⁻¹ := by
    have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun t : ℝ => (a ^ (2 : ℕ) + t ^ (2 : ℕ))⁻¹) (-c)
    simpa [sub_eq_add_neg] using h
  rw [hshift]
  exact integral_inv_sq_add_sq ha

/-- The Cauchy kernel has finite `L²` mass on every vertical line strictly right of its pole. -/
theorem integral_norm_sq_cauchyKernel_line {Z : ℂ} {σ : ℝ} (h : Z.re < σ) :
    (∫ t : ℝ, ‖(Z - ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ^ (2 : ℕ)) = Real.pi / (σ - Z.re) := by
  have ha : 0 < σ - Z.re := by linarith
  have hval : ∀ t : ℝ, ‖(Z - ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ^ (2 : ℕ)
      = ((σ - Z.re) ^ (2 : ℕ) + (t - Z.im) ^ (2 : ℕ))⁻¹ := by
    intro t
    have hre : (Z - ((σ : ℂ) + (t : ℂ) * I)).re = Z.re - σ := by simp
    have him : (Z - ((σ : ℂ) + (t : ℂ) * I)).im = Z.im - t := by simp
    have hne : Z - ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro hzero
      have := congrArg Complex.re hzero
      rw [hre] at this
      simp at this
      linarith
    rw [norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply, hre, him]
    congr 1
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hval)]
  exact integral_inv_sq_add_sq_shift ha

theorem integrable_norm_sq_cauchyKernel_line {Z : ℂ} {σ : ℝ} (h : Z.re < σ) :
    Integrable (fun t : ℝ => ‖(Z - ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ^ (2 : ℕ)) volume := by
  have ha : 0 < σ - Z.re := by linarith
  have hbase : Integrable (fun t : ℝ => ((σ - Z.re) ^ (2 : ℕ) + t ^ (2 : ℕ))⁻¹) volume :=
    integrable_inv_sq_add_sq ha
  have hshift : Integrable (fun t : ℝ => ((σ - Z.re) ^ (2 : ℕ) + (t - Z.im) ^ (2 : ℕ))⁻¹) volume := by
    have h2 := hbase.comp_sub_right Z.im
    exact h2
  refine hshift.congr ?_
  filter_upwards with t
  rw [norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply]
  have hre : (Z - ((σ : ℂ) + (t : ℂ) * I)).re = Z.re - σ := by simp
  have him : (Z - ((σ : ℂ) + (t : ℂ) * I)).im = Z.im - t := by simp
  rw [hre, him]
  congr 1
  ring

/-- **The vertical edge estimate.**  An `L²` datum on a vertical line paired against the Cauchy
kernel of a point strictly left of it is controlled by the two `L²` masses; the kernel mass
`π/(σ − Re Z)` tends to zero as the line moves right. -/
theorem norm_integral_mul_cauchyKernel_le {F : ℝ → ℂ} {σ : ℝ} {Z : ℂ} (hZ : Z.re < σ)
    (hFm : AEStronglyMeasurable F volume)
    (hF2 : Integrable (fun t : ℝ => ‖F t‖ ^ (2 : ℕ)) volume)
    {M : ℝ} (hM : (∫ t : ℝ, ‖F t‖ ^ (2 : ℕ)) ≤ M) :
    ‖∫ t : ℝ, F t * (Z - ((σ : ℂ) + (t : ℂ) * I))⁻¹‖
      ≤ Real.sqrt M * Real.sqrt (Real.pi / (σ - Z.re)) := by
  have ha : 0 < σ - Z.re := by linarith
  set K : ℝ → ℝ := fun t : ℝ => ‖(Z - ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ with hKdef
  have hne : ∀ t : ℝ, Z - ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hKm : AEStronglyMeasurable K volume := by
    refine Continuous.aestronglyMeasurable ?_
    refine continuous_norm.comp ?_
    exact Continuous.inv₀ (by fun_prop) hne
  have hK2 : Integrable (fun t : ℝ => K t ^ (2 : ℕ)) volume := integrable_norm_sq_cauchyKernel_line hZ
  have hKval : (∫ t : ℝ, K t ^ (2 : ℕ)) = Real.pi / (σ - Z.re) :=
    integral_norm_sq_cauchyKernel_line hZ
  have hFnorm : AEStronglyMeasurable (fun t : ℝ => ‖F t‖) volume := hFm.norm
  have hcs := sq_integral_mul_le (μ := (volume : Measure ℝ)) hFnorm hKm hF2 hK2
  have hnn : 0 ≤ ∫ t : ℝ, ‖F t‖ * K t := by
    refine integral_nonneg fun t => ?_
    positivity
  have hM0 : 0 ≤ M := le_trans (integral_nonneg fun t => by positivity) hM
  have hstep1 : ‖∫ t : ℝ, F t * (Z - ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ ∫ t : ℝ, ‖F t‖ * K t := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_))
    show ‖F t * (Z - ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ = ‖F t‖ * K t
    rw [norm_mul]
  have hpik : (0 : ℝ) ≤ Real.pi / (σ - Z.re) := by positivity
  have hsq : (∫ t : ℝ, ‖F t‖ * K t) ^ (2 : ℕ) ≤ M * (Real.pi / (σ - Z.re)) := by
    refine le_trans hcs ?_
    rw [hKval]
    exact mul_le_mul_of_nonneg_right hM hpik
  have hfinal : (∫ t : ℝ, ‖F t‖ * K t) ≤ Real.sqrt (M * (Real.pi / (σ - Z.re))) :=
    (Real.le_sqrt hnn (by positivity)).mpr hsq
  rw [Real.sqrt_mul hM0] at hfinal
  linarith [hstep1, hfinal]

end

end GaloisForLFunctions.HTGeometry


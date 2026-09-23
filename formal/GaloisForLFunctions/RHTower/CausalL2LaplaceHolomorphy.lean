import GaloisForLFunctions.RHTower.ComplexLaplaceHolomorphy
import Mathlib

/-!
# The causal Laplace transform of a square-integrable boundary function

If `g` is square integrable on the positive ray then `∫_0^∞ e^{-zt} g(t) dt` converges absolutely
for every `Re z > 0`, because the kernel is itself square integrable there, and the transform is
holomorphic on the open right half plane: the derivative kernel `t e^{-zt}` is dominated on every
ball strictly inside the half plane by a fixed square-integrable multiple of `g`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RHTower

noncomputable section

/-- The causal Laplace transform of a boundary function. -/
def causalTransform (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), Complex.exp (-z * (t : ℂ)) * g t

theorem norm_cexp_neg_mul_ofReal (z : ℂ) (t : ℝ) :
    ‖Complex.exp (-z * (t : ℂ))‖ = Real.exp (-z.re * t) := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

/-- The exponential kernel is square integrable on the positive ray. -/
theorem memLp_cexp_kernel {z : ℂ} (hz : 0 < z.re) :
    MemLp (fun t : ℝ => Complex.exp (-z * (t : ℂ))) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Complex.exp (-z * (t : ℂ)))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(2 * z.re) * t)) (Ioi (0 : ℝ)) volume :=
    exp_neg_integrableOn_Ioi 0 (by linarith)
  refine hint.congr_fun (fun t _ => ?_) measurableSet_Ioi
  rw [norm_cexp_neg_mul_ofReal, pow_two, ← Real.exp_add]
  ring_nf

/-- The transform converges absolutely on the open right half plane. -/
theorem integrableOn_causalKernel {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi (0 : ℝ)))) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * g t) (Ioi (0 : ℝ)) volume := by
  have h := (memLp_cexp_kernel hz).integrable_mul hg
  exact h.congr (Filter.Eventually.of_forall fun t => rfl)

/-- The elementary majorant `t ≤ e^{at}/a`. -/
theorem le_exp_div {a t : ℝ} (ha : 0 < a) (_ht : 0 ≤ t) : t ≤ Real.exp (a * t) / a := by
  have h := Real.add_one_le_exp (a * t)
  have h2 : a * t ≤ Real.exp (a * t) := by linarith
  rw [le_div_iff₀ ha]
  linarith [h2]

/-- The derivative kernel is dominated by a square-integrable multiple of the boundary function. -/
theorem norm_deriv_kernel_le {σ : ℝ} (hσ : 0 < σ) {x : ℂ} (hx : σ ≤ x.re) {t : ℝ} (ht : 0 ≤ t)
    (w : ℂ) :
    ‖-((t : ℂ) * Complex.exp (-x * (t : ℂ)) * w)‖
      ≤ (2 / σ) * Real.exp (-(σ / 2) * t) * ‖w‖ := by
  have hbound : t ≤ Real.exp ((σ / 2) * t) / (σ / 2) := le_exp_div (by linarith) ht
  have hexp : Real.exp (-x.re * t) ≤ Real.exp (-σ * t) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [ht, hx]
  rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht,
    norm_cexp_neg_mul_ofReal]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg w)
  calc t * Real.exp (-x.re * t)
      ≤ (Real.exp ((σ / 2) * t) / (σ / 2)) * Real.exp (-σ * t) := by
        exact mul_le_mul hbound hexp (Real.exp_pos _).le (by positivity)
    _ = (2 / σ) * Real.exp (-(σ / 2) * t) := by
        have hexp2 : Real.exp (σ / 2 * t) * Real.exp (-σ * t) = Real.exp (-(σ / 2) * t) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [div_div_eq_mul_div]
        calc Real.exp (σ / 2 * t) * 2 / σ * Real.exp (-σ * t)
            = 2 / σ * (Real.exp (σ / 2 * t) * Real.exp (-σ * t)) := by ring
          _ = 2 / σ * Real.exp (-(σ / 2) * t) := by rw [hexp2]


theorem memLp_expDecay {σ : ℝ} (hσ : 0 < σ) :
    MemLp (fun t : ℝ => ((2 / σ) * Real.exp (-(σ / 2) * t) : ℝ)) 2
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ((2 / σ) * Real.exp (-(σ / 2) * t) : ℝ))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
      ).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-σ * t)) (Ioi (0 : ℝ)) volume :=
    exp_neg_integrableOn_Ioi 0 hσ
  have hscaled : IntegrableOn (fun t : ℝ => ((2 / σ) ^ (2 : ℕ)) * Real.exp (-σ * t))
      (Ioi (0 : ℝ)) volume := hint.const_mul _
  refine hscaled.congr_fun (fun t _ => ?_) measurableSet_Ioi
  have hexp2 : Real.exp (-(σ / 2) * t) ^ (2 : ℕ) = Real.exp (-σ * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow, hexp2]

/-! ## Holomorphy -/

set_option maxHeartbeats 1000000 in
/-- **The causal transform of a square-integrable boundary function is complex differentiable on
the open right half plane.** -/
theorem hasDerivAt_causalTransform {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi (0 : ℝ)))) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (causalTransform g)
      (∫ t in Ioi (0 : ℝ), -((t : ℂ) * Complex.exp (-z * (t : ℂ)) * g t)) z := by
  set σ : ℝ := z.re / 2 with hσdef
  have hσ : 0 < σ := by rw [hσdef]; linarith
  have hgnorm : MemLp (fun t : ℝ => ‖g t‖) 2 (volume.restrict (Ioi (0 : ℝ))) := hg.norm
  have hboundInt : Integrable
      (fun t : ℝ => (2 / σ) * Real.exp (-(σ / 2) * t) * ‖g t‖)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have h := (memLp_expDecay hσ).integrable_mul hgnorm
    exact h.congr (Filter.Eventually.of_forall fun t => rfl)
  have hmeasF : ∀ᶠ x : ℂ in nhds z,
      AEStronglyMeasurable (fun t : ℝ => Complex.exp (-x * (t : ℂ)) * g t)
        (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards with x
    exact ((Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable).mul hg.1
  have hInt := integrableOn_causalKernel hg hz
  have hmeasF' : AEStronglyMeasurable
      (fun t : ℝ => -((t : ℂ) * Complex.exp (-z * (t : ℂ)) * g t))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine AEStronglyMeasurable.neg ?_
    exact ((Complex.continuous_ofReal.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable).mul hg.1
  have hdom : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))), ∀ x ∈ Metric.ball z σ,
      ‖-((t : ℂ) * Complex.exp (-x * (t : ℂ)) * g t)‖
        ≤ (2 / σ) * Real.exp (-(σ / 2) * t) * ‖g t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x hx
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have hxre : σ ≤ x.re := by
      have h1 : |x.re - z.re| ≤ ‖x - z‖ := by
        have := Complex.abs_re_le_norm (x - z)
        simpa using this
      have h2 : ‖x - z‖ < σ := by
        rw [← Complex.dist_eq]
        exact Metric.mem_ball.mp hx
      have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
      have h4 := h3.1
      rw [hσdef] at h4 ⊢
      linarith
    exact norm_deriv_kernel_le hσ hxre ht0 (g t)
  have hderiv : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))), ∀ x ∈ Metric.ball z σ,
      HasDerivAt (fun y : ℂ => Complex.exp (-y * (t : ℂ)) * g t)
        (-((t : ℂ) * Complex.exp (-x * (t : ℂ)) * g t)) x := by
    filter_upwards with t x _
    have h1 : HasDerivAt (fun y : ℂ => -y * (t : ℂ)) (-(t : ℂ)) x := by
      have h0 : HasDerivAt (fun y : ℂ => (-(t : ℂ)) * y) ((-(t : ℂ)) * 1) x :=
        (hasDerivAt_id x).const_mul (-(t : ℂ))
      refine (h0.congr_deriv (by ring)).congr_of_eventuallyEq ?_
      filter_upwards with y
      ring
    have h2 := h1.cexp
    have h3 : HasDerivAt (fun y : ℂ => Complex.exp (-y * (t : ℂ)))
        (-((t : ℂ) * Complex.exp (-x * (t : ℂ)))) x := h2.congr_deriv (by ring)
    have h4 := h3.mul_const (g t)
    exact h4.congr_deriv (by ring)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (x : ℂ) (t : ℝ) => Complex.exp (-x * (t : ℂ)) * g t)
    (F' := fun (x : ℂ) (t : ℝ) => -((t : ℂ) * Complex.exp (-x * (t : ℂ)) * g t))
    (bound := fun t : ℝ => (2 / σ) * Real.exp (-(σ / 2) * t) * ‖g t‖)
    (Metric.ball_mem_nhds z hσ) hmeasF hInt hmeasF' hdom hboundInt hderiv
  exact hmain.2

/-- **The causal transform is holomorphic on the open right half plane.** -/
theorem differentiableOn_causalTransform {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioi (0 : ℝ)))) :
    DifferentiableOn ℂ (causalTransform g) {z : ℂ | 0 < z.re} := fun _z hz =>
  ((hasDerivAt_causalTransform hg hz).differentiableAt).differentiableWithinAt

end

end RHTower

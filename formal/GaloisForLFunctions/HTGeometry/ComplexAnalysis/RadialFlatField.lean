import GaloisForLFunctions.HTGeometry.ComplexAnalysis.RadialAntiholomorphicDerivative
import GaloisForLFunctions.HTGeometry.ComplexAnalysis.HolomorphicL2Flatness
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# A smooth, infinitely flat radial field with an explicit antiholomorphic defect

The radial field `exp(-1/‖x‖²)`, extended by zero at the origin, is smooth on every complex
Hilbert space. Its antiholomorphic norm is exactly `‖x‖⁻³` times its modulus. On the complex
line its local squared mass vanishes faster than every power, despite positivity off the origin.
-/

open MeasureTheory Filter Topology Set Metric

noncomputable section
namespace GaloisForLFunctions.HTGeometry

section Hilbert

variable {E : Type*} [NormedAddCommGroup E]

/-- Exponential radial flatness, with its smooth value zero at the origin. -/
def radialFlatField (x : E) : ℂ := (expNegInvGlue (‖x‖ ^ 2) : ℂ)

theorem radialFlatField_zero : radialFlatField (0 : E) = 0 := by
  simp only [radialFlatField, norm_zero, zero_pow two_ne_zero, expNegInvGlue.zero,
    Complex.ofReal_zero]

/-- The exponential profile is positive away from the centre. -/
theorem radialFlatField_ne_zero {x : E} (hx : x ≠ 0) : radialFlatField x ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr
    (expNegInvGlue.pos_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hx))).ne'

theorem norm_radialFlatField (x : E) : ‖radialFlatField x‖ = expNegInvGlue (‖x‖ ^ 2) := by
  rw [radialFlatField, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (expNegInvGlue.nonneg _)]

/-- Every inverse even power is dominated by the exponential flatness at the origin. -/
theorem tendsto_norm_radialFlatField_div_pow (k : ℕ) :
    Tendsto (fun x : E => ‖radialFlatField x‖ / ‖x‖ ^ (2 * k)) (𝓝 0) (𝓝 0) := by
  have ht : Tendsto (fun x : E => ‖x‖ ^ 2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun x : E => ‖x‖ ^ (2 : ℕ)) := continuous_norm.pow 2
    have h := hc.tendsto (0 : E)
    change Tendsto (fun x : E => ‖x‖ ^ 2) (𝓝 0) (𝓝 (‖(0 : E)‖ ^ 2)) at h
    simpa only [norm_zero, zero_pow two_ne_zero] using h
  have h := (expNegInvGlue.tendsto_polynomial_inv_mul_zero
    (Polynomial.X ^ k : Polynomial ℝ)).comp ht
  change Tendsto (fun x : E =>
    (Polynomial.X ^ k : Polynomial ℝ).eval ((‖x‖ ^ 2)⁻¹) * expNegInvGlue (‖x‖ ^ 2))
      (𝓝 0) (𝓝 0) at h
  simpa only [Function.comp_apply, Polynomial.eval_pow, Polynomial.eval_X, inv_pow,
    ← pow_mul, div_eq_mul_inv, mul_comm, norm_radialFlatField] using h

variable [InnerProductSpace ℂ E]

local instance (priority := 50) : InnerProductSpace ℝ E :=
  InnerProductSpace.rclikeToReal ℂ E

/-- Smoothness at the centre follows by composing the smooth glued exponential with squared norm. -/
theorem contDiff_radialFlatField : ContDiff ℝ (⊤ : ℕ∞) (radialFlatField : E → ℂ) := by
  exact Complex.ofRealCLM.contDiff.comp
    (expNegInvGlue.contDiff.comp (contDiff_norm_sq ℂ))

private theorem hasDerivAt_expNegInvGlue (t : ℝ) :
    HasDerivAt expNegInvGlue ((t⁻¹) ^ 2 * expNegInvGlue t) t := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) t

/-- The exact radial defect is the inverse cube of the radius times the field modulus.
The identity includes the origin, where both sides vanish. -/
theorem norm_dbarDifferential_radialFlatField (x : E) :
    ‖_root_.HTGeometry.dbarDifferential (radialFlatField : E → ℂ) x‖ =
      (1 / ‖x‖ ^ 3) * ‖radialFlatField x‖ := by
  change ‖_root_.HTGeometry.dbarDifferential
    (fun y : E => (expNegInvGlue (‖y‖ ^ 2) : ℂ)) x‖ = _
  rw [_root_.HTGeometry.norm_dbarDifferential_radial_sq
    (hasDerivAt_expNegInvGlue (‖x‖ ^ 2)),
    abs_of_nonneg (mul_nonneg (sq_nonneg _) (expNegInvGlue.nonneg _)), norm_radialFlatField]
  by_cases hx : ‖x‖ = 0
  · simp only [hx, zero_pow two_ne_zero, inv_zero, zero_mul, zero_pow (by omega : 3 ≠ 0),
      div_zero]
  · field_simp

/-- Every power below the inverse-cube potential's dimensional threshold is locally integrable. -/
theorem integrableOn_radialFlatPotential_rpow
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {p : ℝ} (hp : 3 * p < (Module.finrank ℝ E : ℝ)) (R : ℝ) :
    IntegrableOn (fun x : E => (1 / ‖x‖ ^ 3) ^ p) (ball 0 R) := by
  have he (x : E) : (1 / ‖x‖ ^ 3) ^ p = ‖x‖ ^ (-(3 * p)) := by
    have hb : 1 / ‖x‖ ^ 3 = ‖x‖ ^ (-3 : ℝ) := by
      rw [Real.rpow_neg (norm_nonneg x)]
      norm_num
    rw [hb, ← Real.rpow_mul (norm_nonneg x)]
    congr 1
    ring
  simp_rw [he]
  apply integrableOn_ball_of_norm_le_rpow (μ := volume) Module.finrank_pos hp (C := 1)
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _), one_mul]
  · have hm : Measurable (fun x : E => ‖x‖ ^ (-(3 * p))) := by fun_prop
    exact hm.aestronglyMeasurable

end Hilbert

/-- The nonzero smooth radial field has infinite-order local squared-mass vanishing. -/
theorem l2FlatAt_radialFlatField : L2FlatAt (radialFlatField : ℂ → ℂ) 0 := by
  intro k
  simp only [zero_add]
  have hnear : ∀ᶠ z : ℂ in 𝓝 0,
      ‖radialFlatField z‖ / ‖z‖ ^ (2 * k) < 1 :=
    (tendsto_norm_radialFlatField_div_pow (E := ℂ) k).eventually_lt_const zero_lt_one
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hbound (r : ℝ) (hr : 0 < r) (hrδ : r < δ) :
      (∫ z in ball (0 : ℂ) r, ‖radialFlatField z‖ ^ 2) / r ^ k ≤
        (Real.pi / (2 * (k : ℝ) + 1)) * r ^ (3 * k + 2) := by
    have hintf : IntegrableOn (fun z : ℂ => ‖radialFlatField z‖ ^ 2) (ball 0 r) :=
      ((contDiff_radialFlatField.continuous.norm.pow 2).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : ℂ) r)).mono_set ball_subset_closedBall
    have hintp : IntegrableOn (fun z : ℂ => ‖z‖ ^ (2 * (2 * k))) (ball 0 r) :=
      ((continuous_norm.pow _).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : ℂ) r)).mono_set ball_subset_closedBall
    have hi : (∫ z in ball (0 : ℂ) r, ‖radialFlatField z‖ ^ 2) ≤
        ∫ z in ball (0 : ℂ) r, ‖z‖ ^ (2 * (2 * k)) := by
      apply integral_mono_ae hintf hintp
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      have hzbound : ‖radialFlatField z‖ ≤ ‖z‖ ^ (2 * k) := by
        by_cases hz0 : z = 0
        · subst z
          rw [radialFlatField_zero, norm_zero]
          positivity
        · have hratio := hsub (ball_subset_ball hrδ.le hz)
          exact ((div_lt_one (pow_pos (norm_pos_iff.mpr hz0) _)).mp hratio).le
      calc
        ‖radialFlatField z‖ ^ 2 ≤ (‖z‖ ^ (2 * k)) ^ 2 := by gcongr
        _ = _ := by rw [← pow_mul, Nat.mul_comm (2 * k) 2]
    have hp := integral_ball_norm_even_pow (2 * k) ⟨r, hr.le⟩
    change (∫ z in ball (0 : ℂ) r, ‖z‖ ^ (2 * (2 * k))) =
      Real.pi * r ^ (2 * (2 * k) + 2) / (((2 * k : ℕ) : ℝ) + 1) at hp
    rw [hp] at hi
    calc
      _ ≤ (Real.pi * r ^ (2 * (2 * k) + 2) / (((2 * k : ℕ) : ℝ) + 1)) / r ^ k :=
        div_le_div_of_nonneg_right hi (pow_nonneg hr.le _)
      _ = _ := by
        rw [show 2 * (2 * k) + 2 = (3 * k + 2) + k by omega, pow_add]
        push_cast
        field_simp
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < δ :=
    nhdsWithin_le_nhds (eventually_lt_nhds hδ)
  have hle : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      (∫ z in ball (0 : ℂ) r, ‖radialFlatField z‖ ^ 2) / r ^ k ≤
        (Real.pi / (2 * (k : ℝ) + 1)) * r ^ (3 * k + 2) := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrδ
    exact hbound r hr hrδ
  have hnonneg : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ (∫ z in ball (0 : ℂ) r, ‖radialFlatField z‖ ^ 2) / r ^ k := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_nonneg (integral_nonneg fun z => sq_nonneg _) (pow_nonneg hr.le _)
  have hlim : Tendsto (fun r : ℝ =>
      (Real.pi / (2 * (k : ℝ) + 1)) * r ^ (3 * k + 2)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => (Real.pi / (2 * (k : ℝ) + 1)) * r ^ (3 * k + 2)) :=
      continuous_const.mul (continuous_id.pow _)
    simpa only [zero_pow (by omega : 3 * k + 2 ≠ 0), mul_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact squeeze_zero' hnonneg hle hlim

/-- Smoothness and infinite-order local L² vanishing do not imply holomorphicity. -/
theorem not_entire_radialFlatField : ¬ AnalyticOnNhd ℂ (radialFlatField : ℂ → ℂ) univ := by
  intro h
  have hz := eq_zero_of_entire_l2FlatAt h l2FlatAt_radialFlatField
  have h1 := congr_fun hz (1 : ℂ)
  exact radialFlatField_ne_zero one_ne_zero h1

end GaloisForLFunctions.HTGeometry

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex

/-!
# The Euler integral behind the Mellin representation of the Barnes zeta

The meromorphic continuation of the Barnes double zeta past its abscissa of convergence goes
through the Mellin representation

```text
Γ(s) ζ₂(s, z) = ∫_0^∞ t^(s-1) e^(-z t) / ((1 - e^(-ω₁ t))(1 - e^(-ω₂ t))) dt,     Re s > 2,
```

which is obtained by summing the Euler integral of each cone term over the cone.  The term-by-term
input is the scaled Euler integral

```text
∫_0^∞ t^(s-1) e^(-w t) dt = Γ(s) w^(-s).
```

This module proves it for a positive real rate `w`, which is the case where the substitution
`t ↦ w t` is a genuine change of variables on the half-line; the complex-rate version is obtained
from it by analytic continuation in `w` over the right half-plane, where both sides are analytic and
agree on the positive reals.

Convergence itself is proved for a **complex** rate: `integrableOn_cpow_mul_exp_neg_mul_Ioi` shows
`t^(s-1) e^(-w t)` is integrable on the half-line whenever `Re s > 0` and `Re w > 0`, dominated by
the real integrand `t^(Re s - 1) e^(-(Re w) t)` of `integrableOn_rpow_mul_exp_neg_mul_Ioi`.  This is
what both the analytic continuation in the rate and the term-by-term summation over the cone need.

The continuation itself is `integral_cpow_mul_exp_neg_mul_Ioi`: differentiating under the integral
sign (`hasDerivAt_integral_cpow_mul_exp`, dominated on a ball by `t^(Re s) e^(-a t)`) makes the
integral holomorphic in the rate on the right half-plane, where it agrees with `Γ(s) w^(-s)` on the
positive reals; the identity theorem on that convex, hence preconnected, set does the rest.
-/

open Complex Real MeasureTheory Set Filter
open scoped Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The scaled Euler integral for a positive real rate.**  For `w > 0` real and `Re s > 0`,

```text
∫_0^∞ t^(s-1) e^(-w t) dt = Γ(s) w^(-s).
```

This is the base case of the Mellin representation of the Barnes zeta functions; the complex-rate
version follows from it by analytic continuation in the rate. -/
theorem integral_cpow_mul_exp_neg_real_mul_Ioi {s : ℂ} (hs : 0 < s.re) {w : ℝ} (hw : 0 < w) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * Complex.exp (-((w : ℂ) * t)))
      = Complex.Gamma s * (w : ℂ) ^ (-s) := by
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hw]
  have harg : ((w : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hw.le]
    exact (Real.pi_ne_zero).symm
  rw [one_div, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  ring

/-! ## Convergence of the Euler integral -/

/-- The Euler integrand with a positive real rate is integrable on the half-line. -/
theorem integrableOn_rpow_mul_exp_neg_mul_Ioi {σ a : ℝ} (hσ : -1 < σ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ σ * Real.exp (-(a * t))) (Ioi 0) := by
  have hbase : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((σ + 1) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by linarith)
  have hbase' : IntegrableOn (fun x : ℝ => x ^ σ * Real.exp (-x)) (Ioi 0) := by
    refine hbase.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [add_sub_cancel_right]
    ring
  have hscale := (integrableOn_Ioi_comp_mul_left_iff
    (fun x : ℝ => x ^ σ * Real.exp (-x)) 0 ha).mpr (by simpa using hbase')
  have hconst : IntegrableOn
      (fun t : ℝ => (a ^ σ)⁻¹ * ((a * t) ^ σ * Real.exp (-(a * t)))) (Ioi 0) :=
    hscale.const_mul _
  refine hconst.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (0 : ℝ) < t := ht
  show (a ^ σ)⁻¹ * ((a * t) ^ σ * Real.exp (-(a * t))) = t ^ σ * Real.exp (-(a * t))
  rw [Real.mul_rpow ha.le ht0.le]
  field_simp

/-- **Convergence of the complex-rate Euler integral.**  For `Re s > 0` and `Re w > 0` the
integrand `t^(s-1) e^(-w t)` is integrable on the half-line. -/
theorem integrableOn_cpow_mul_exp_neg_mul_Ioi {s w : ℂ} (hs : 0 < s.re) (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * Complex.exp (-(w * t))) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * Complex.exp (-(w * t))) (volume.restrict (Ioi 0)) := by
    refine ((continuousOn_of_forall_continuousAt fun t ht => ?_).aestronglyMeasurable
      measurableSet_Ioi)
    have ht0 : (0 : ℝ) < t := ht
    exact (Complex.continuousAt_ofReal_cpow_const t (s - 1) (Or.inr (ne_of_gt ht0))).mul
      ((Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal).neg).continuousAt)
  have hdom : IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * Real.exp (-(w.re * t))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) hw
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  have hexp : ‖Complex.exp (-(w * t))‖ = Real.exp (-(w.re * t)) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [hexp, Complex.sub_re, Complex.one_re]


/-! ## Holomorphy in the rate and the complex-rate Euler integral -/

theorem aestronglyMeasurable_cpow_mul_exp (s w : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (s - 1) * Complex.exp (-(w * t)))
      (volume.restrict (Ioi 0)) := by
  refine ((continuousOn_of_forall_continuousAt fun t ht => ?_).aestronglyMeasurable
    measurableSet_Ioi)
  have ht0 : (0 : ℝ) < t := ht
  exact (Complex.continuousAt_ofReal_cpow_const t (s - 1) (Or.inr (ne_of_gt ht0))).mul
    ((Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal).neg).continuousAt)

/-- The `w`-derivative of the Euler integrand. -/
theorem hasDerivAt_cpow_mul_exp (s w : ℂ) (t : ℝ) :
    HasDerivAt (fun v : ℂ => (t : ℂ) ^ (s - 1) * Complex.exp (-(v * t)))
      ((t : ℂ) ^ (s - 1) * (Complex.exp (-(w * t)) * -(t : ℂ))) w := by
  have h0 : HasDerivAt (fun v : ℂ => (-(t : ℂ)) * v) (-(t : ℂ)) w := by
    simpa using (hasDerivAt_id w).const_mul (-(t : ℂ))
  have hlin : HasDerivAt (fun v : ℂ => -(v * (t : ℂ))) (-(t : ℂ)) w := by
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards with v
    ring
  exact (hlin.cexp).const_mul ((t : ℂ) ^ (s - 1))

/-- **The Euler integral is holomorphic in the rate.**  On the open right half-plane the integral
`∫_0^∞ t^(s-1) e^(-w t) dt` is complex differentiable in `w`. -/
theorem hasDerivAt_integral_cpow_mul_exp {s w₀ : ℂ} (hs : 0 < s.re) (hw : 0 < w₀.re) :
    HasDerivAt (fun w : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * Complex.exp (-(w * t)))
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (Complex.exp (-(w₀ * t)) * -(t : ℂ))) w₀ := by
  set a : ℝ := w₀.re / 2 with ha
  have ha0 : 0 < a := by positivity
  set ε : ℝ := w₀.re / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hball : ∀ w ∈ Metric.ball w₀ ε, a ≤ w.re := by
    intro w hw'
    have hdist : ‖w - w₀‖ < ε := by
      rwa [Metric.mem_ball, dist_eq_norm] at hw'
    have hre : |(w - w₀).re| ≤ ‖w - w₀‖ := Complex.abs_re_le_norm _
    simp only [Complex.sub_re] at hre
    have : w₀.re - w.re ≤ ε := by
      have h1 : -(w - w₀).re ≤ |(w - w₀).re| := neg_le_abs _
      simp only [Complex.sub_re] at h1
      linarith
    simp only [ha, hε] at *
    linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound :=
      fun t : ℝ => t ^ s.re * Real.exp (-(a * t)))
    (F := fun w : ℂ => fun t : ℝ => (t : ℂ) ^ (s - 1) * Complex.exp (-(w * t)))
    (F' := fun w : ℂ => fun t : ℝ => (t : ℂ) ^ (s - 1) * (Complex.exp (-(w * t)) * -(t : ℂ)))
    (Metric.ball_mem_nhds w₀ hε0)
    (Eventually.of_forall fun w => aestronglyMeasurable_cpow_mul_exp s w)
    (integrableOn_cpow_mul_exp_neg_mul_Ioi hs hw) ?_ ?_ ?_ ?_).2
  · refine ((continuousOn_of_forall_continuousAt fun t ht => ?_).aestronglyMeasurable
      measurableSet_Ioi)
    have ht0 : (0 : ℝ) < t := ht
    exact (Complex.continuousAt_ofReal_cpow_const t (s - 1) (Or.inr (ne_of_gt ht0))).mul
      (((Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal).neg).mul
        (continuous_neg.comp Complex.continuous_ofReal)).continuousAt)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw'
    have ht0 : (0 : ℝ) < t := ht
    have hre : a ≤ w.re := hball w hw'
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, norm_mul, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, Complex.norm_exp]
    have hsim : (-(w * (t : ℂ))).re = -(w.re * t) := by simp
    rw [hsim, Complex.sub_re, Complex.one_re]
    rw [mul_comm (Real.exp (-(w.re * t))) t]
    have hexp : Real.exp (-(w.re * t)) ≤ Real.exp (-(a * t)) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have hsplit : t ^ (s.re - 1) * t = t ^ s.re := by
      have hone : t ^ (s.re - 1) * t ^ (1 : ℝ) = t ^ (s.re - 1 + 1) :=
        (Real.rpow_add ht0 _ _).symm
      rw [Real.rpow_one] at hone
      rw [hone]
      congr 1
      ring
    calc t ^ (s.re - 1) * (t * Real.exp (-(w.re * t)))
        = (t ^ (s.re - 1) * t) * Real.exp (-(w.re * t)) := by ring
      _ = t ^ s.re * Real.exp (-(w.re * t)) := by rw [hsplit]
      _ ≤ t ^ s.re * Real.exp (-(a * t)) := by
          exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg ht0.le _)
  · have := integrableOn_rpow_mul_exp_neg_mul_Ioi (σ := s.re) (a := a) (by linarith) ha0
    exact this
  · filter_upwards with t w _
    exact hasDerivAt_cpow_mul_exp s w t


/-- The Euler integral is holomorphic on the open right half-plane. -/
theorem differentiableOn_integral_cpow_mul_exp {s : ℂ} (hs : 0 < s.re) :
    DifferentiableOn ℂ
      (fun w : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * Complex.exp (-(w * t)))
      {w : ℂ | 0 < w.re} :=
  fun _ hw => ((hasDerivAt_integral_cpow_mul_exp hs hw).differentiableAt).differentiableWithinAt

/-- **The Euler integral for a complex rate.**  For `Re s > 0` and `Re w > 0`,

```text
∫_0^∞ t^(s-1) e^(-w t) dt = Γ(s) w^(-s).
```

Both sides are holomorphic on the right half-plane and agree on the positive reals, which
accumulate there, so the identity theorem propagates the real-rate case. -/
theorem integral_cpow_mul_exp_neg_mul_Ioi {s w : ℂ} (hs : 0 < s.re) (hw : 0 < w.re) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * Complex.exp (-(w * t)))
      = Complex.Gamma s * w ^ (-s) := by
  classical
  set U : Set ℂ := {v : ℂ | 0 < v.re} with hU
  have hUopen : IsOpen U := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hUconv : Convex ℝ U := convex_halfSpace_re_gt 0
  have hUconn : IsPreconnected U := hUconv.isPreconnected
  set F : ℂ → ℂ := fun v => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * Complex.exp (-(v * t)) with hF
  set G : ℂ → ℂ := fun v => Complex.Gamma s * v ^ (-s) with hG
  have hFa : AnalyticOnNhd ℂ F U :=
    (differentiableOn_integral_cpow_mul_exp hs).analyticOnNhd hUopen
  have hGa : AnalyticOnNhd ℂ G U := by
    refine DifferentiableOn.analyticOnNhd (fun v hv => ?_) hUopen
    have hslit : v ∈ Complex.slitPlane := Or.inl hv
    have hcp : DifferentiableAt ℂ (fun v : ℂ => v ^ (-s)) v :=
      (differentiableAt_id).cpow_const hslit
    exact (hcp.const_mul (Complex.Gamma s)).differentiableWithinAt
  have hone : (1 : ℂ) ∈ U := by
    simp [hU]
  have hreal : ∀ x : ℝ, 0 < x → F (x : ℂ) = G (x : ℂ) := by
    intro x hx
    rw [hF, hG]
    exact integral_cpow_mul_exp_neg_real_mul_Ioi hs hx
  have htend : Filter.Tendsto (fun n : ℕ => ((1 + 1 / (n + 1 : ℝ) : ℝ) : ℂ)) atTop
      (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hR : Filter.Tendsto (fun n : ℕ => (1 + 1 / (n + 1 : ℝ))) atTop (𝓝 ((1 : ℝ) + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at hR
      have hc := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hR
      simpa [Function.comp_def] using hc
    · filter_upwards with n
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcon
      have hcast : (1 : ℝ) + 1 / (n + 1 : ℝ) = 1 := by exact_mod_cast hcon
      have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      linarith
  have hfreq : ∃ᶠ v in 𝓝[≠] (1 : ℂ), F v = G v := by
    refine htend.frequently (Filter.Eventually.frequently ?_)
    filter_upwards with n
    refine hreal _ ?_
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith
  have heq := hFa.eqOn_of_preconnected_of_frequently_eq hGa hUconn hone hfreq
  exact heq hw

end

end GaloisForLFunctions.HTGeometry

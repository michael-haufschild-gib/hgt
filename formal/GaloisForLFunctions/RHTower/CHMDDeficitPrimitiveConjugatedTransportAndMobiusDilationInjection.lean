import GaloisForLFunctions.RHTower.CHMDPrimeKernelDerivativeUniformBound
import GaloisForLFunctions.RHTower.CCMPrimeDeficitMobiusTailLocalization

/-!
# Conjugated second-derivative transport of the integrated Chebyshev deficit

Let `K_y` be the Klein–Gordon prime kernel, let `D(s) = ∫_0^s (e^t − ψ(e^t)) dt` be the
integrated Chebyshev deficit, and let `f_y(s) = e^{−s/2} K_y(s)` be the conjugated kernel.
The space derivative of `K_y` paired with the `√`-weighted Chebyshev discrepancy
`Δ(s) = Σ_{log n < s} Λ(n)/√n − 2e^{s/2}` satisfies the exact identity
`∫_0^∞ ∂_sK_y(s) Δ(s) ds = K_y(0) + ∫_0^∞ D(s) f_y''(s) ds`,
where `f_y'' = e^{−s/2} (∂_s − ½)² K_y`.  The proof is termwise over the prime powers: the
tent `(s − log n)_+` integrates against `f_y''` to `f_y(log n) = K_y(log n)/√n`, and the
pole density `e^s − 1` integrates to `K_y(0) + ∫_0^∞ e^{s/2} K_y`.

The conjugated Laplacian `f_y''` is bounded by a constant times `e^{−s/2}` uniformly in the
Klein–Gordon time `y`, through the Fourier form `−(1/π)∫ cos(y√(r²+2)) sech²(r/2) r² cos(rs) dr`
of the second space derivative.

Substituting the Möbius-dilation decomposition of `D` (explicit work, Mertens channel,
small-divisor head, large-divisor tail), the head pairs to a quantity bounded uniformly in `y`,
so the Riemann hypothesis is equivalent to a one-sided bound on the pairing of the Λ-free
Möbius part with `f_y''`.  No one-sided bound is produced.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace RHTower.CHMDChebyshevTransport

open RHTower.CHMDLightCone RHTower.CHMDStage22 GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Section 1: the second derivative of the d'Alembert kernel -/

/-- The second derivative `D''` of the d'Alembert kernel on the real line. -/
def dAlembertDeriv2 (v : ℝ) : ℝ := (deriv (deriv dAlembertKernel) (v : ℂ)).re

theorem analyticOnNhd_dAlembertKernel :
    AnalyticOnNhd ℂ dAlembertKernel {w | sinhSlope w ≠ 0} :=
  differentiableOn_dAlembertKernel.analyticOnNhd isOpen_sinhSlope_ne_zero

theorem hasDerivAt_dAlembertDeriv (v : ℝ) : HasDerivAt dAlembertDeriv (dAlembertDeriv2 v) v :=
  (analyticOnNhd_dAlembertKernel.deriv (v : ℂ)
    (sinhSlope_ofReal_ne_zero v)).differentiableAt.hasDerivAt.real_of_complex

theorem continuous_dAlembertDeriv2 : Continuous dAlembertDeriv2 := by
  have hc : ContinuousOn (deriv (deriv dAlembertKernel)) {w | sinhSlope w ≠ 0} :=
    analyticOnNhd_dAlembertKernel.deriv.deriv.continuousOn
  exact Complex.continuous_re.comp
    (hc.comp_continuous Complex.continuous_ofReal fun v => sinhSlope_ofReal_ne_zero v)

/-- Explicit formula for `D''` off the origin. -/
theorem dAlembertDeriv2_of_ne {v : ℝ} (hv : v ≠ 0) :
    dAlembertDeriv2 v =
      -(2 * π ^ 2 * v) / Real.sinh (π * v) - 4 * π * Real.cosh (π * v) / Real.sinh (π * v) ^ 2 +
        4 * π ^ 2 * v * Real.cosh (π * v) ^ 2 / Real.sinh (π * v) ^ 3 := by
  have hs : Real.sinh (π * v) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]
    exact mul_ne_zero Real.pi_ne_zero hv
  have hS : HasDerivAt (fun u : ℝ => Real.sinh (π * u)) (Real.cosh (π * v) * π) v := by
    have := ((hasDerivAt_id' v).const_mul π).sinh
    rwa [mul_one] at this
  have hC : HasDerivAt (fun u : ℝ => Real.cosh (π * u)) (Real.sinh (π * v) * π) v := by
    have := ((hasDerivAt_id' v).const_mul π).cosh
    rwa [mul_one] at this
  have hN := (hS.const_mul 2).sub (((hasDerivAt_id' v).const_mul 2).mul (hC.const_mul π))
  have hS2 := hS.pow 2
  have h3 := hN.div hS2 (pow_ne_zero 2 hs)
  have heq : (fun u : ℝ => (2 * Real.sinh (π * u) - 2 * u * (π * Real.cosh (π * u))) /
      Real.sinh (π * u) ^ 2) =ᶠ[𝓝 v] dAlembertDeriv := by
    filter_upwards [isOpen_ne.mem_nhds hv] with u hu
    exact (dAlembertDeriv_of_ne hu).symm
  have h4 := h3.congr_of_eventuallyEq heq.symm
  have h5 := (hasDerivAt_dAlembertDeriv v).unique h4
  simp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply, Nat.cast_ofNat,
    show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h5
  rw [h5]
  field_simp
  ring

/-- Exponential decay of `D''` away from the origin. -/
theorem abs_dAlembertDeriv2_le_of_one_le {v : ℝ} (hv : 1 ≤ |v|) :
    |dAlembertDeriv2 v| ≤ (64 * π + 264 * π ^ 2) * (1 + |v|) * Real.exp (-(π * |v|)) := by
  have hv0 : v ≠ 0 := by
    intro h; rw [h, abs_zero] at hv; linarith
  have hpi := Real.pi_pos
  rw [dAlembertDeriv2_of_ne hv0]
  have hπv : 1 ≤ π * |v| := by nlinarith [Real.pi_gt_three]
  have hS := exp_div_four_le_sinh hπv
  set E := Real.exp (π * |v|) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  set S := Real.sinh (π * |v|) with hSdef
  have hSpos : 0 < S := by linarith [div_pos hEpos four_pos]
  have hES : E ≤ 4 * S := by linarith
  have habsS : |Real.sinh (π * v)| = S := by
    rw [hSdef, Real.abs_sinh, abs_mul, abs_of_pos hpi]
  have hcosh : |Real.cosh (π * v)| ≤ E := by
    rw [abs_of_pos (Real.cosh_pos _), ← Real.cosh_abs, abs_mul, abs_of_pos hpi]
    exact cosh_le_exp_of_nonneg (by positivity)
  have hcosh0 : 0 ≤ |Real.cosh (π * v)| := abs_nonneg _
  have habs4 : |(4 : ℝ)| = 4 := abs_of_pos (by norm_num)
  have habsπ : |π| = π := abs_of_pos hpi
  have hT1 : |-(2 * π ^ 2 * v) / Real.sinh (π * v)| ≤ 8 * π ^ 2 * |v| / E := by
    simp only [abs_div, abs_neg, abs_mul, abs_pow, abs_two, habsS, habsπ]
    rw [div_le_div_iff₀ hSpos hEpos]
    have := mul_le_mul_of_nonneg_left hES (by positivity : (0 : ℝ) ≤ 2 * π ^ 2 * |v|)
    nlinarith
  have hT2 : |4 * π * Real.cosh (π * v) / Real.sinh (π * v) ^ 2| ≤ 64 * π / E := by
    simp only [abs_div, abs_mul, abs_pow, habs4, habsS, habsπ]
    rw [div_le_div_iff₀ (by positivity) hEpos]
    have hsq : E ^ 2 ≤ (4 * S) ^ 2 := pow_le_pow_left₀ hEpos.le hES 2
    have h1 : 4 * π * |Real.cosh (π * v)| * E ≤ 4 * π * E * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcosh (by positivity)) hEpos.le
    nlinarith
  have hT3 : |4 * π ^ 2 * v * Real.cosh (π * v) ^ 2 / Real.sinh (π * v) ^ 3| ≤
      256 * π ^ 2 * |v| / E := by
    simp only [abs_div, abs_mul, abs_pow, habs4, habsS, habsπ]
    rw [div_le_div_iff₀ (by positivity) hEpos]
    have hcu : E ^ 3 ≤ (4 * S) ^ 3 := pow_le_pow_left₀ hEpos.le hES 3
    have hc2 : |Real.cosh (π * v)| ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ hcosh0 hcosh 2
    have h1 : 4 * π ^ 2 * |v| * |Real.cosh (π * v)| ^ 2 * E ≤ 4 * π ^ 2 * |v| * E ^ 2 * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc2 (by positivity)) hEpos.le
    have h2 := mul_le_mul_of_nonneg_left hcu (by positivity : (0 : ℝ) ≤ 4 * π ^ 2 * |v|)
    nlinarith [h1, h2]
  have hsum : |-(2 * π ^ 2 * v) / Real.sinh (π * v) - 4 * π * Real.cosh (π * v) /
      Real.sinh (π * v) ^ 2 + 4 * π ^ 2 * v * Real.cosh (π * v) ^ 2 / Real.sinh (π * v) ^ 3| ≤
      8 * π ^ 2 * |v| / E + 64 * π / E + 256 * π ^ 2 * |v| / E := by
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ((abs_sub _ _).trans (add_le_add hT1 hT2)) hT3
  refine hsum.trans ?_
  rw [Real.exp_neg, ← hE, ← div_eq_mul_inv, ← add_div, ← add_div,
    div_le_div_iff_of_pos_right hEpos]
  nlinarith [abs_nonneg v, Real.pi_gt_three]

/-- Global domination `|D''(v)| ≤ C (1+|v|) e^{−π|v|}` with some constant `C`. -/
theorem exists_abs_dAlembertDeriv2_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, |dAlembertDeriv2 v| ≤ C * (1 + |v|) * Real.exp (-(π * |v|)) := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    continuous_dAlembertDeriv2.continuousOn
  have hC₀0 : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ 0 ⟨by norm_num, by norm_num⟩)
  set C₁ : ℝ := 64 * π + 264 * π ^ 2 with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨max (C₀ * Real.exp π) C₁, le_max_of_le_right hC₁0, fun v => ?_⟩
  have hpos : 0 < (1 + |v|) * Real.exp (-(π * |v|)) := by positivity
  rcases le_or_gt |v| 1 with hv | hv
  · have h1 := hC₀ v (abs_le.mp hv)
    rw [Real.norm_eq_abs] at h1
    have h2 : 1 ≤ Real.exp π * Real.exp (-(π * |v|)) := by
      rw [← Real.exp_add]
      have : 0 ≤ π + -(π * |v|) := by nlinarith [Real.pi_pos]
      exact Real.one_le_exp_iff.mpr this
    have h3 : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
    calc |dAlembertDeriv2 v| ≤ C₀ := h1
      _ ≤ C₀ * (Real.exp π * Real.exp (-(π * |v|))) := by nlinarith
      _ ≤ C₀ * Real.exp π * ((1 + |v|) * Real.exp (-(π * |v|))) := by
          have hE := (Real.exp_pos (-(π * |v|))).le
          have hCE : 0 ≤ C₀ * Real.exp π := by positivity
          calc C₀ * (Real.exp π * Real.exp (-(π * |v|)))
              = C₀ * Real.exp π * (1 * Real.exp (-(π * |v|))) := by ring
            _ ≤ C₀ * Real.exp π * ((1 + |v|) * Real.exp (-(π * |v|))) := by gcongr
      _ ≤ max (C₀ * Real.exp π) C₁ * (1 + |v|) * Real.exp (-(π * |v|)) := by
          have := mul_le_mul_of_nonneg_right (le_max_left (C₀ * Real.exp π) C₁) hpos.le
          nlinarith
  · calc |dAlembertDeriv2 v| ≤ C₁ * (1 + |v|) * Real.exp (-(π * |v|)) :=
          abs_dAlembertDeriv2_le_of_one_le hv.le
      _ ≤ max (C₀ * Real.exp π) C₁ * (1 + |v|) * Real.exp (-(π * |v|)) := by
          have := mul_le_mul_of_nonneg_right (le_max_right (C₀ * Real.exp π) C₁) hpos.le
          nlinarith

theorem exists_abs_dAlembertDeriv2_le_const :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, |dAlembertDeriv2 v| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_dAlembertDeriv2_le
  refine ⟨C, hC0, fun v => (hC v).trans ?_⟩
  have h1 : (1 + |v|) * Real.exp (-(π * |v|)) ≤ 1 := by
    have h2 : 1 + |v| ≤ Real.exp (π * |v|) := by
      have := Real.add_one_le_exp (π * |v|)
      have : |v| ≤ π * |v| := by nlinarith [Real.pi_gt_three, abs_nonneg v]
      linarith
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    exact h2
  calc C * (1 + |v|) * Real.exp (-(π * |v|)) = C * ((1 + |v|) * Real.exp (-(π * |v|))) := by ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left h1 hC0
    _ = C := mul_one C

/-! ## Section 2: the second space derivative of the prime kernel -/

/-- The second space derivative `∂_s² K_y(s)` of the prime kernel, in light-cone form. -/
def kernelDeriv2 (y s : ℝ) : ℝ :=
  dAlembertDeriv2 (s + y) + dAlembertDeriv2 (s - y) -
    y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
      (dAlembertDeriv2 (s + y * t) + dAlembertDeriv2 (s - y * t))

/-- The `D'`-tail is differentiable in the space variable, with derivative the `D''`-tail. -/
theorem hasDerivAt_lightConeDerivTail (y s : ℝ) :
    HasDerivAt (fun s => ∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
        (dAlembertDeriv (s + y * t) + dAlembertDeriv (s - y * t)))
      (∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
        (dAlembertDeriv2 (s + y * t) + dAlembertDeriv2 (s - y * t))) s := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_dAlembertDeriv2_le_const
  set Bt : ℝ → ℝ := fun t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) with hBt
  have hBc : Continuous Bt := continuous_lightConeBesselReal.comp (by fun_prop)
  set F : ℝ → ℝ → ℝ := fun x t => Bt t * (dAlembertDeriv (x + y * t) + dAlembertDeriv (x - y * t))
    with hF
  set F' : ℝ → ℝ → ℝ := fun x t =>
    Bt t * (dAlembertDeriv2 (x + y * t) + dAlembertDeriv2 (x - y * t)) with hF'
  have hFc : ∀ x, Continuous (F x) := fun x =>
    hBc.mul ((continuous_dAlembertDeriv.comp (by fun_prop)).add
      (continuous_dAlembertDeriv.comp (by fun_prop)))
  have hF'c : ∀ x, Continuous (F' x) := fun x =>
    hBc.mul ((continuous_dAlembertDeriv2.comp (by fun_prop)).add
      (continuous_dAlembertDeriv2.comp (by fun_prop)))
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := volume) (a := (-1 : ℝ)) (b := 1) (F := F) (F' := F') (x₀ := s)
    (s := Metric.ball s 1) (bound := fun _ => Real.exp (y ^ 2 / 2) * (2 * C))
    (Metric.ball_mem_nhds s one_pos)
    (Eventually.of_forall fun x => (hFc x).aestronglyMeasurable)
    ((hFc s).intervalIntegrable _ _)
    (hF'c s).aestronglyMeasurable
    (Eventually.of_forall fun t ht x _ => ?_)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ x _ => ?_)
  · exact key.2
  · have hta := mem_uIoc_neg_one_one_abs_le ht
    have hB := abs_lightConeBesselReal_light_cone_le y hta
    simp only [hF', Real.norm_eq_abs, abs_mul]
    have h1 := hC (x + y * t)
    have h2 := hC (x - y * t)
    have h3 : |dAlembertDeriv2 (x + y * t) + dAlembertDeriv2 (x - y * t)| ≤ 2 * C := by
      calc |dAlembertDeriv2 (x + y * t) + dAlembertDeriv2 (x - y * t)|
          ≤ |dAlembertDeriv2 (x + y * t)| + |dAlembertDeriv2 (x - y * t)| := abs_add_le _ _
        _ ≤ 2 * C := by linarith
    exact mul_le_mul hB h3 (abs_nonneg _) (Real.exp_pos _).le
  · simp only [hF, hF']
    have h1 := (hasDerivAt_dAlembertDeriv (x + y * t)).comp x ((hasDerivAt_id' x).add_const (y * t))
    have h2 := (hasDerivAt_dAlembertDeriv (x - y * t)).comp x ((hasDerivAt_id' x).sub_const (y * t))
    have h := (h1.add h2).const_mul (Bt t)
    simp only [mul_one] at h
    exact h

theorem continuous_lightConeDeriv2Tail (y : ℝ) :
    Continuous fun s => ∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
      (dAlembertDeriv2 (s + y * t) + dAlembertDeriv2 (s - y * t)) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun s t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
      (dAlembertDeriv2 (s + y * t) + dAlembertDeriv2 (s - y * t)))
    ((continuous_lightConeBesselReal.comp (by fun_prop)).mul
      ((continuous_dAlembertDeriv2.comp (by fun_prop)).add
        (continuous_dAlembertDeriv2.comp (by fun_prop))))
    _ _

theorem continuous_kernelDeriv2 (y : ℝ) : Continuous (kernelDeriv2 y) := by
  unfold kernelDeriv2
  exact ((continuous_dAlembertDeriv2.comp (by fun_prop)).add
    (continuous_dAlembertDeriv2.comp (by fun_prop))).sub
    (continuous_const.mul (continuous_lightConeDeriv2Tail y))

/-- **The space derivative of the prime kernel is differentiable**, with derivative
`kernelDeriv2 y s`. -/
theorem hasDerivAt_kernelDeriv (y s : ℝ) : HasDerivAt (kernelDeriv y) (kernelDeriv2 y s) s := by
  have h1 := (hasDerivAt_dAlembertDeriv (s + y)).comp s ((hasDerivAt_id' s).add_const y)
  have h2 := (hasDerivAt_dAlembertDeriv (s - y)).comp s ((hasDerivAt_id' s).sub_const y)
  have h3 := (hasDerivAt_lightConeDerivTail y s).const_mul (y ^ 2 / 2)
  have h := (h1.add h2).sub h3
  simp only [mul_one] at h
  exact h

/-- Exponential decay of the second space derivative of the prime kernel. -/
theorem exists_abs_kernelDeriv2_le (y : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |kernelDeriv2 y s| ≤ C * Real.exp (-((π - 1) * |s|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_dAlembertDeriv2_le
  set K : ℝ := C * (1 + |y|) * Real.exp (π * |y|) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * K + y ^ 2 * (Real.exp (y ^ 2 / 2) * (2 * K)),
    add_nonneg (by linarith) (mul_nonneg (sq_nonneg y) (mul_nonneg (Real.exp_pos _).le (by linarith))),
    fun s => ?_⟩
  have hpair : |dAlembertDeriv2 (s + y) + dAlembertDeriv2 (s - y)| ≤
      2 * K * Real.exp (-((π - 1) * |s|)) := by
    have e1 := shift_decay_le hC0 hC y (a := y) le_rfl s
    have e2 := shift_decay_le hC0 hC y (a := -y) (by rw [abs_neg]) s
    rw [← sub_eq_add_neg] at e2
    calc |dAlembertDeriv2 (s + y) + dAlembertDeriv2 (s - y)|
        ≤ |dAlembertDeriv2 (s + y)| + |dAlembertDeriv2 (s - y)| := abs_add_le _ _
      _ ≤ 2 * K * Real.exp (-((π - 1) * |s|)) := by rw [hK]; linarith
  have htail : |∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
      (dAlembertDeriv2 (s + y * t) + dAlembertDeriv2 (s - y * t))| ≤
      Real.exp (y ^ 2 / 2) * (2 * K * Real.exp (-((π - 1) * |s|))) * 2 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
      (C := Real.exp (y ^ 2 / 2) * (2 * K * Real.exp (-((π - 1) * |s|))))
      (f := fun t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
        (dAlembertDeriv2 (s + y * t) + dAlembertDeriv2 (s - y * t))) fun t ht => by
        have hta := mem_uIoc_neg_one_one_abs_le ht
        have hB := abs_lightConeBesselReal_light_cone_le y hta
        have hyt : |y * t| ≤ |y| := by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg y) hta
        have hyt' : |-(y * t)| ≤ |y| := by rwa [abs_neg]
        have e1 := shift_decay_le hC0 hC y hyt s
        have e2 := shift_decay_le hC0 hC y hyt' s
        rw [← sub_eq_add_neg] at e2
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul hB ?_ (abs_nonneg _) (Real.exp_pos _).le
        calc |dAlembertDeriv2 (s + y * t) + dAlembertDeriv2 (s - y * t)|
            ≤ |dAlembertDeriv2 (s + y * t)| + |dAlembertDeriv2 (s - y * t)| := abs_add_le _ _
          _ ≤ 2 * K * Real.exp (-((π - 1) * |s|)) := by rw [hK]; linarith
    rw [Real.norm_eq_abs] at h
    simpa [abs_of_pos (by norm_num : (0 : ℝ) < 1 - -1), show (1 : ℝ) - -1 = 2 by norm_num] using h
  unfold kernelDeriv2
  have hy2 : 0 ≤ y ^ 2 / 2 := by positivity
  calc |dAlembertDeriv2 (s + y) + dAlembertDeriv2 (s - y) - y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1,
        lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
          (dAlembertDeriv2 (s + y * t) + dAlembertDeriv2 (s - y * t))|
      ≤ |dAlembertDeriv2 (s + y) + dAlembertDeriv2 (s - y)| + y ^ 2 / 2 * |∫ t in (-1 : ℝ)..1,
        lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
          (dAlembertDeriv2 (s + y * t) + dAlembertDeriv2 (s - y * t))| := by
        rw [sub_eq_add_neg]
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_mul, abs_of_nonneg hy2]
    _ ≤ 2 * K * Real.exp (-((π - 1) * |s|)) +
        y ^ 2 / 2 * (Real.exp (y ^ 2 / 2) * (2 * K * Real.exp (-((π - 1) * |s|))) * 2) := by
        gcongr
    _ = (2 * K + y ^ 2 * (Real.exp (y ^ 2 / 2) * (2 * K))) * Real.exp (-((π - 1) * |s|)) := by
        ring

/-! ## Section 3: the Fourier form of the second space derivative and its uniform bound -/

theorem integrable_sq_mul_sechSqHalf : Integrable fun r : ℝ => r ^ 2 * sechSqHalf r := by
  have h := (_root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 2 (r := 1) one_pos).const_mul 4
  refine h.mono' ((continuous_pow 2).mul continuous_sechSqHalf).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (sechSqHalf_pos s)]
  have := mul_le_mul_of_nonneg_left (sechSqHalf_le_exp_neg_abs s) (sq_nonneg |s|)
  simp only [neg_one_mul]
  linarith

/-- The second absolute moment `∫ r² sech²(r/2) dr` of the sech² weight. -/
def sechSecondMoment : ℝ := ∫ r : ℝ, r ^ 2 * sechSqHalf r

theorem sechSecondMoment_nonneg : 0 ≤ sechSecondMoment :=
  integral_nonneg fun r => mul_nonneg (sq_nonneg r) (sechSqHalf_pos r).le

/-- **Fourier form of the second space derivative of the prime kernel**:
`−(1/π) ∫ cos(y√(r²+2)) sech²(r/2) r² cos(rs) dr`. -/
def kernelDeriv2Fourier (y s : ℝ) : ℝ :=
  -(1 / π) * ∫ r : ℝ, kgSymbolWeight y r * (r ^ 2 * Real.cos (r * s))

/-- Differentiation of the Fourier form of the space derivative under the integral. -/
theorem hasDerivAt_kernelDerivFourier (y s : ℝ) :
    HasDerivAt (kernelDerivFourier y) (kernelDeriv2Fourier y s) s := by
  have hAc := continuous_kgSymbolWeight y
  set F : ℝ → ℝ → ℝ := fun x r => kgSymbolWeight y r * (r * Real.sin (r * x)) with hF
  set F' : ℝ → ℝ → ℝ := fun x r => kgSymbolWeight y r * (r ^ 2 * Real.cos (r * x)) with hF'
  have hFint : Integrable (F s) := by
    refine integrable_abs_mul_sechSqHalf.mono' (hAc.mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 := abs_kgSymbolWeight_le y r
    have h2 : |Real.sin (r * s)| ≤ 1 := Real.abs_sin_le_one _
    calc |kgSymbolWeight y r| * (|r| * |Real.sin (r * s)|) ≤ sechSqHalf r * (|r| * 1) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg r))
            (by positivity) (sechSqHalf_pos r).le
      _ = |r| * sechSqHalf r := by ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (𝕜 := ℝ)
    (F := F) (x₀ := s) (s := Metric.ball s 1) (bound := fun r => r ^ 2 * sechSqHalf r)
    (Metric.ball_mem_nhds s one_pos)
    (Eventually.of_forall fun x => (hAc.mul (by fun_prop)).aestronglyMeasurable)
    hFint (F' := F') (hAc.mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun r x _ => by
      simp only [hF', Real.norm_eq_abs, abs_mul, abs_pow]
      have h1 := abs_kgSymbolWeight_le y r
      have h2 : |Real.cos (r * x)| ≤ 1 := Real.abs_cos_le_one _
      calc |kgSymbolWeight y r| * (|r| ^ 2 * |Real.cos (r * x)|) ≤ sechSqHalf r * (|r| ^ 2 * 1) :=
            mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
              (by positivity) (sechSqHalf_pos r).le
        _ = r ^ 2 * sechSqHalf r := by rw [sq_abs]; ring)
    integrable_sq_mul_sechSqHalf
    (Eventually.of_forall fun r x _ => by
      simp only [hF, hF']
      have h := ((((hasDerivAt_id' x).const_mul r).sin).const_mul r).const_mul (kgSymbolWeight y r)
      refine h.congr_deriv ?_
      ring)
  have h := key.2.const_mul (-(1 / π))
  have hfun : kernelDerivFourier y = fun x => -(1 / π) * ∫ r, F x r := rfl
  rw [hfun]
  exact h

/-- The light-cone second space derivative coincides with the Fourier form. -/
theorem kernelDeriv2_eq_kernelDeriv2Fourier (y s : ℝ) :
    kernelDeriv2 y s = kernelDeriv2Fourier y s := by
  have hfun : kernelDeriv y = kernelDerivFourier y := funext fun s => kernelDeriv_eq_kernelDerivFourier y s
  have h2 := hasDerivAt_kernelDerivFourier y s
  rw [← hfun] at h2
  exact (hasDerivAt_kernelDeriv y s).unique h2

/-- **Uniform bound on the second space derivative of the prime kernel**:
`|∂_s² K_y(s)| ≤ (1/π) ∫ r² sech²(r/2) dr` for all `y`, `s`. -/
theorem abs_kernelDeriv2_le (y s : ℝ) : |kernelDeriv2 y s| ≤ 1 / π * sechSecondMoment := by
  rw [kernelDeriv2_eq_kernelDeriv2Fourier]
  unfold kernelDeriv2Fourier sechSecondMoment
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h := norm_integral_le_of_norm_le (μ := volume)
    (f := fun r => kgSymbolWeight y r * (r ^ 2 * Real.cos (r * s))) integrable_sq_mul_sechSqHalf
    (Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
      have h1 := abs_kgSymbolWeight_le y r
      have h2 : |Real.cos (r * s)| ≤ 1 := Real.abs_cos_le_one _
      calc |kgSymbolWeight y r| * (|r| ^ 2 * |Real.cos (r * s)|) ≤ sechSqHalf r * (|r| ^ 2 * 1) :=
            mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
              (by positivity) (sechSqHalf_pos r).le
        _ = r ^ 2 * sechSqHalf r := by rw [sq_abs]; ring)
  rwa [Real.norm_eq_abs] at h


/-! ## Section 4: the conjugated kernel `f_y(s) = e^{−s/2} K_y(s)` and its Laplacian -/

/-- The conjugated kernel `f_y(s) = e^{−s/2} K_y(s)`. -/
def conjugatedKernel (y s : ℝ) : ℝ := Real.exp (-(s / 2)) * chmdPrimeKernel y s

/-- The derivative `f_y'(s) = e^{−s/2} (∂_s − ½) K_y(s)`. -/
def conjugatedKernelDeriv (y s : ℝ) : ℝ :=
  Real.exp (-(s / 2)) * (kernelDeriv y s - chmdPrimeKernel y s / 2)

/-- The conjugated Laplacian `f_y''(s) = e^{−s/2} (∂_s − ½)² K_y(s)`. -/
def conjugatedLaplacian (y s : ℝ) : ℝ :=
  Real.exp (-(s / 2)) * (kernelDeriv2 y s - kernelDeriv y s + chmdPrimeKernel y s / 4)

theorem hasDerivAt_exp_neg_half (s : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-(s / 2))) (-(Real.exp (-(s / 2)) / 2)) s := by
  have h := (Real.hasDerivAt_exp (-(s / 2))).comp s (((hasDerivAt_id' s).div_const 2).neg)
  refine h.congr_deriv ?_
  show Real.exp (-(s / 2)) * -(1 / 2) = -(Real.exp (-(s / 2)) / 2)
  ring

theorem hasDerivAt_conjugatedKernel (y s : ℝ) :
    HasDerivAt (conjugatedKernel y) (conjugatedKernelDeriv y s) s := by
  have h := (hasDerivAt_exp_neg_half s).mul (hasDerivAt_chmdPrimeKernel_right y s)
  refine h.congr_deriv ?_
  unfold conjugatedKernelDeriv
  ring

theorem hasDerivAt_conjugatedKernelDeriv (y s : ℝ) :
    HasDerivAt (conjugatedKernelDeriv y) (conjugatedLaplacian y s) s := by
  have h := (hasDerivAt_exp_neg_half s).mul
    ((hasDerivAt_kernelDeriv y s).sub ((hasDerivAt_chmdPrimeKernel_right y s).div_const 2))
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply]
  unfold conjugatedLaplacian
  ring

theorem continuous_conjugatedKernel (y : ℝ) : Continuous (conjugatedKernel y) := by
  unfold conjugatedKernel
  exact (by fun_prop : Continuous fun s : ℝ => Real.exp (-(s / 2))).mul
    (continuous_chmdPrimeKernel_right y)

theorem continuous_conjugatedKernelDeriv (y : ℝ) : Continuous (conjugatedKernelDeriv y) := by
  unfold conjugatedKernelDeriv
  exact (by fun_prop : Continuous fun s : ℝ => Real.exp (-(s / 2))).mul
    ((continuous_kernelDeriv y).sub ((continuous_chmdPrimeKernel_right y).div_const 2))

theorem continuous_conjugatedLaplacian (y : ℝ) : Continuous (conjugatedLaplacian y) := by
  unfold conjugatedLaplacian
  exact (by fun_prop : Continuous fun s : ℝ => Real.exp (-(s / 2))).mul
    (((continuous_kernelDeriv2 y).sub (continuous_kernelDeriv y)).add
      ((continuous_chmdPrimeKernel_right y).div_const 4))

/-- The uniform constant bounding `(∂_s − ½)² K_y` for all `y`, `s`. -/
def laplacianBound : ℝ := 1 / π * sechSecondMoment + 8 * Real.log 2 / π + 1 / π

theorem laplacianBound_nonneg : 0 ≤ laplacianBound := by
  unfold laplacianBound
  have := sechSecondMoment_nonneg
  have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  positivity

/-- **Uniform bound on the conjugated Laplacian**: `|f_y''(s)| ≤ laplacianBound · e^{−s/2}`. -/
theorem abs_conjugatedLaplacian_le (y s : ℝ) :
    |conjugatedLaplacian y s| ≤ laplacianBound * Real.exp (-(s / 2)) := by
  unfold conjugatedLaplacian laplacianBound
  rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have h2 := abs_kernelDeriv2_le y s
  have h1 := abs_kernelDeriv_le y s
  have h0 := abs_chmdPrimeKernel_le y s
  calc |kernelDeriv2 y s - kernelDeriv y s + chmdPrimeKernel y s / 4|
      ≤ |kernelDeriv2 y s| + |kernelDeriv y s| + |chmdPrimeKernel y s| / 4 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
        linarith [abs_sub (kernelDeriv2 y s) (kernelDeriv y s)]
    _ ≤ 1 / π * sechSecondMoment + 8 * Real.log 2 / π + 4 / π / 4 := by gcongr
    _ = _ := by ring

/-- Exponential decay of the conjugated Laplacian on the forward half-line. -/
theorem exists_abs_conjugatedLaplacian_le (y : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
      |conjugatedLaplacian y s| ≤ C * Real.exp (-((π - 1 / 2) * s)) := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_abs_kernelDeriv2_le y
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_abs_kernelDeriv_le y
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_abs_chmdPrimeKernel_le y
  refine ⟨C₂ + C₁ + C₀ / 4, by positivity, fun s hs => ?_⟩
  unfold conjugatedLaplacian
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have e2 := hC₂ s
  have e1 := hC₁ s
  have e0 := hC₀ s
  rw [abs_of_nonneg hs] at e2 e1 e0
  have hexp : Real.exp (-((π - 1 / 2) * s)) = Real.exp (-(s / 2)) * Real.exp (-((π - 1) * s)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  calc Real.exp (-(s / 2)) * |kernelDeriv2 y s - kernelDeriv y s + chmdPrimeKernel y s / 4|
      ≤ Real.exp (-(s / 2)) * (|kernelDeriv2 y s| + |kernelDeriv y s| + |chmdPrimeKernel y s| / 4) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        refine (abs_add_le _ _).trans ?_
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
        linarith [abs_sub (kernelDeriv2 y s) (kernelDeriv y s)]
    _ ≤ Real.exp (-(s / 2)) * ((C₂ + C₁ + C₀ / 4) * Real.exp (-((π - 1) * s))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have : |chmdPrimeKernel y s| / 4 ≤ C₀ / 4 * Real.exp (-((π - 1) * s)) := by
          rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by norm_num)]
          exact e0
        linarith
    _ = _ := by ring

/-- Exponential decay of `f_y'` on the forward half-line. -/
theorem exists_abs_conjugatedKernelDeriv_le (y : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
      |conjugatedKernelDeriv y s| ≤ C * Real.exp (-((π - 1 / 2) * s)) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_abs_kernelDeriv_le y
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_abs_chmdPrimeKernel_le y
  refine ⟨C₁ + C₀ / 2, by positivity, fun s hs => ?_⟩
  unfold conjugatedKernelDeriv
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have e1 := hC₁ s
  have e0 := hC₀ s
  rw [abs_of_nonneg hs] at e1 e0
  have hexp : Real.exp (-((π - 1 / 2) * s)) = Real.exp (-(s / 2)) * Real.exp (-((π - 1) * s)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  calc Real.exp (-(s / 2)) * |kernelDeriv y s - chmdPrimeKernel y s / 2|
      ≤ Real.exp (-(s / 2)) * (|kernelDeriv y s| + |chmdPrimeKernel y s| / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        refine (abs_sub _ _).trans ?_
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (-(s / 2)) * ((C₁ + C₀ / 2) * Real.exp (-((π - 1) * s))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have : |chmdPrimeKernel y s| / 2 ≤ C₀ / 2 * Real.exp (-((π - 1) * s)) := by
          rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by norm_num)]
          exact e0
        linarith
    _ = _ := by ring

/-- Exponential decay of `f_y` on the forward half-line. -/
theorem exists_abs_conjugatedKernel_le (y : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s →
      |conjugatedKernel y s| ≤ C * Real.exp (-((π - 1 / 2) * s)) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_abs_chmdPrimeKernel_le y
  refine ⟨C₀, hC₀0, fun s hs => ?_⟩
  unfold conjugatedKernel
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have e0 := hC₀ s
  rw [abs_of_nonneg hs] at e0
  have hexp : Real.exp (-((π - 1 / 2) * s)) = Real.exp (-(s / 2)) * Real.exp (-((π - 1) * s)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp, ← mul_assoc, mul_comm C₀, mul_assoc]
  exact mul_le_mul_of_nonneg_left e0 (Real.exp_pos _).le

/-! ## Section 5: elementary limits and integrability on the forward half-line -/

theorem tendsto_mul_exp_neg_mul_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun s : ℝ => s * Real.exp (-(c * s))) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.const_mul_atTop hc)
  have h' := h.const_mul c⁻¹
  rw [mul_zero] at h'
  refine h'.congr fun s => ?_
  simp only [Function.comp, pow_one, id]
  field_simp

/-- A function dominated by `C e^{−cs}` on the half-line, multiplied by `s − ℓ`, tends to zero. -/
theorem tendsto_sub_mul_of_abs_le {g : ℝ → ℝ} {C c : ℝ} (hc : 0 < c)
    (hg : ∀ s, 0 ≤ s → |g s| ≤ C * Real.exp (-(c * s))) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    Tendsto (fun s => (s - ℓ) * g s) atTop (𝓝 0) := by
  have h := (tendsto_mul_exp_neg_mul_atTop hc).const_mul C
  rw [mul_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop (max 0 ℓ)] with s hs
  have hs0 : 0 ≤ s := le_trans (le_max_left _ _) hs
  have hsl : ℓ ≤ s := le_trans (le_max_right _ _) hs
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hsl)]
  have hC : 0 ≤ C := by
    have := hg 0 le_rfl
    have hp := Real.exp_pos (-(c * 0))
    nlinarith [abs_nonneg (g 0)]
  calc (s - ℓ) * |g s| ≤ s * (C * Real.exp (-(c * s))) :=
        mul_le_mul (by linarith) (hg s hs0) (abs_nonneg _) hs0
    _ = C * (s * Real.exp (-(c * s))) := by ring

/-- A function dominated by `C e^{−cs}` on the half-line, multiplied by `e^{as}` with `a < c`,
tends to zero. -/
theorem tendsto_exp_mul_of_abs_le {g : ℝ → ℝ} {C c a : ℝ} (hac : a < c)
    (hg : ∀ s, 0 ≤ s → |g s| ≤ C * Real.exp (-(c * s))) :
    Tendsto (fun s => Real.exp (a * s) * g s) atTop (𝓝 0) := by
  have h := (tendsto_exp_neg_mul_abs_atTop (c := c - a) (by linarith)).const_mul C
  rw [mul_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop 0] with s hs
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hs]
  calc Real.exp (a * s) * |g s| ≤ Real.exp (a * s) * (C * Real.exp (-(c * s))) :=
        mul_le_mul_of_nonneg_left (hg s hs) (Real.exp_pos _).le
    _ = C * Real.exp (-((c - a) * s)) := by
        rw [show Real.exp (a * s) * (C * Real.exp (-(c * s))) =
          C * (Real.exp (a * s) * Real.exp (-(c * s))) by ring, ← Real.exp_add]
        congr 2
        ring

/-- `s ≤ 2 e^{s/2}`. -/
theorem le_two_mul_exp_half (s : ℝ) : s ≤ 2 * Real.exp (s / 2) := by
  have := Real.add_one_le_exp (s / 2)
  linarith

/-- `(s − ℓ) e^{−cs}` is integrable on `(ℓ, ∞)` whenever `c > 1/2` and `ℓ ≥ 0`, through the
domination by `2 e^{−(c − ½)s}`. -/
theorem integrableOn_sub_mul_of_abs_le {g : ℝ → ℝ} {C c : ℝ} (hc : 1 / 2 < c)
    (hmeas : Measurable g) (hg : ∀ s, 0 ≤ s → |g s| ≤ C * Real.exp (-(c * s))) {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) :
    IntegrableOn (fun s => (s - ℓ) * g s) (Ioi ℓ) := by
  have hC : 0 ≤ C := by
    have := hg 0 le_rfl
    have hp := Real.exp_pos (-(c * 0))
    nlinarith [abs_nonneg (g 0)]
  have hdom : IntegrableOn (fun s : ℝ => 2 * C * Real.exp (-(c - 1 / 2) * s)) (Ioi ℓ) :=
    (exp_neg_integrableOn_Ioi ℓ (by linarith)).const_mul (2 * C)
  refine hdom.mono' ((measurable_id.sub measurable_const).mul hmeas).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun s hs => ?_
  have hsl : ℓ < s := hs
  have hs0 : 0 ≤ s := hℓ.trans hsl.le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hsl.le)]
  calc (s - ℓ) * |g s| ≤ (2 * Real.exp (s / 2)) * (C * Real.exp (-(c * s))) :=
        mul_le_mul (by linarith [le_two_mul_exp_half s]) (hg s hs0) (abs_nonneg _)
          (by positivity)
    _ = 2 * C * Real.exp (-(c - 1 / 2) * s) := by
        rw [show 2 * Real.exp (s / 2) * (C * Real.exp (-(c * s))) =
          2 * C * (Real.exp (s / 2) * Real.exp (-(c * s))) by ring, ← Real.exp_add]
        congr 2
        ring

/-! ## Section 6: the two integrations by parts against the conjugated Laplacian -/

theorem integrableOn_sub_mul_conjugatedLaplacian (y : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    IntegrableOn (fun s => (s - ℓ) * conjugatedLaplacian y s) (Ioi ℓ) := by
  obtain ⟨C, _, hC⟩ := exists_abs_conjugatedLaplacian_le y
  exact integrableOn_sub_mul_of_abs_le (by linarith [Real.pi_gt_three])
    (continuous_conjugatedLaplacian y).measurable hC hℓ

/-- **Tent integration by parts**: `∫_ℓ^∞ (s − ℓ) f_y''(s) ds = f_y(ℓ)` for `ℓ ≥ 0`. -/
theorem integral_Ioi_sub_mul_conjugatedLaplacian (y : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ∫ s in Ioi ℓ, (s - ℓ) * conjugatedLaplacian y s = conjugatedKernel y ℓ := by
  set g : ℝ → ℝ := fun s => (s - ℓ) * conjugatedKernelDeriv y s - conjugatedKernel y s with hg
  have hgd : ∀ x, HasDerivAt g ((x - ℓ) * conjugatedLaplacian y x) x := fun x => by
    have h := (((hasDerivAt_id' x).sub_const ℓ).mul (hasDerivAt_conjugatedKernelDeriv y x)).sub
      (hasDerivAt_conjugatedKernel y x)
    refine h.congr_deriv ?_
    ring
  have hcont : Continuous g :=
    ((continuous_id.sub continuous_const).mul (continuous_conjugatedKernelDeriv y)).sub
      (continuous_conjugatedKernel y)
  have hpi : (0 : ℝ) < π - 1 / 2 := by linarith [Real.pi_gt_three]
  have htend : Tendsto g atTop (𝓝 0) := by
    obtain ⟨C₁, _, hC₁⟩ := exists_abs_conjugatedKernelDeriv_le y
    obtain ⟨C₀, _, hC₀⟩ := exists_abs_conjugatedKernel_le y
    have h1 := tendsto_sub_mul_of_abs_le hpi hC₁ hℓ
    have h0 : Tendsto (fun s => conjugatedKernel y s) atTop (𝓝 0) := by
      have := tendsto_exp_mul_of_abs_le (a := 0) hpi hC₀
      simpa using this
    simpa using h1.sub h0
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := ℓ) (m := 0) hcont.continuousWithinAt
    (fun x _ => hgd x) (integrableOn_sub_mul_conjugatedLaplacian y hℓ) htend
  rw [h]
  simp [hg]

theorem integrableOn_exp_sub_one_mul_conjugatedLaplacian (y : ℝ) :
    IntegrableOn (fun s => (Real.exp s - 1) * conjugatedLaplacian y s) (Ioi (0 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_conjugatedLaplacian_le y
  have hdom : IntegrableOn (fun s : ℝ => C * Real.exp (-(π - 3 / 2) * s)) (Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith [Real.pi_gt_three])).const_mul C
  refine hdom.mono' ((Real.continuous_exp.sub continuous_const).mul
    (continuous_conjugatedLaplacian y)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun s hs => ?_
  have hs0 : 0 ≤ s := le_of_lt hs
  have he : 0 ≤ Real.exp s - 1 := by linarith [Real.add_one_le_exp s, Real.one_le_exp_iff.mpr hs0]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg he]
  calc (Real.exp s - 1) * |conjugatedLaplacian y s|
      ≤ Real.exp s * (C * Real.exp (-((π - 1 / 2) * s))) :=
        mul_le_mul (by linarith) (hC s hs0) (abs_nonneg _) (Real.exp_pos _).le
    _ = C * Real.exp (-(π - 3 / 2) * s) := by
        rw [show Real.exp s * (C * Real.exp (-((π - 1 / 2) * s))) =
          C * (Real.exp s * Real.exp (-((π - 1 / 2) * s))) by ring, ← Real.exp_add]
        congr 2
        ring

theorem exp_mul_conjugatedKernel (y s : ℝ) :
    Real.exp s * conjugatedKernel y s = chmdPrimeKernel y s * Real.exp (s / 2) := by
  unfold conjugatedKernel
  rw [← mul_assoc, ← Real.exp_add, show s + -(s / 2) = s / 2 by ring, mul_comm]

/-- **Pole-density integration by parts**:
`∫_0^∞ (e^s − 1) f_y''(s) ds = K_y(0) + ∫_0^∞ K_y(s) e^{s/2} ds`. -/
theorem integral_Ioi_exp_sub_one_mul_conjugatedLaplacian (y : ℝ) :
    ∫ s in Ioi (0 : ℝ), (Real.exp s - 1) * conjugatedLaplacian y s =
      chmdPrimeKernel y 0 + ∫ s in Ioi (0 : ℝ), chmdPrimeKernel y s * Real.exp (s / 2) := by
  set g : ℝ → ℝ := fun s => (Real.exp s - 1) * conjugatedKernelDeriv y s -
    Real.exp s * conjugatedKernel y s with hg
  have hgd : ∀ x, HasDerivAt g
      ((Real.exp x - 1) * conjugatedLaplacian y x - Real.exp x * conjugatedKernel y x) x := by
    intro x
    have h := (((Real.hasDerivAt_exp x).sub_const 1).mul (hasDerivAt_conjugatedKernelDeriv y x)).sub
      ((Real.hasDerivAt_exp x).mul (hasDerivAt_conjugatedKernel y x))
    refine h.congr_deriv ?_
    unfold conjugatedKernelDeriv conjugatedKernel conjugatedLaplacian
    ring
  have hcont : Continuous g :=
    ((Real.continuous_exp.sub continuous_const).mul (continuous_conjugatedKernelDeriv y)).sub
      (Real.continuous_exp.mul (continuous_conjugatedKernel y))
  have hpi : (1 : ℝ) < π - 1 / 2 := by linarith [Real.pi_gt_three]
  have htend : Tendsto g atTop (𝓝 0) := by
    obtain ⟨C₁, _, hC₁⟩ := exists_abs_conjugatedKernelDeriv_le y
    obtain ⟨C₀, _, hC₀⟩ := exists_abs_conjugatedKernel_le y
    have h1 := tendsto_exp_mul_of_abs_le (a := 1) hpi hC₁
    have h1' := tendsto_exp_mul_of_abs_le (a := 0) (by linarith) hC₁
    have h0 := tendsto_exp_mul_of_abs_le (a := 1) hpi hC₀
    simp only [one_mul, zero_mul, Real.exp_zero] at h1 h1' h0
    have := (h1.sub h1').sub h0
    rw [sub_zero, sub_zero] at this
    refine this.congr fun s => ?_
    simp only [hg]
    ring
  have hint1 := integrableOn_exp_sub_one_mul_conjugatedLaplacian y
  have hint2 : IntegrableOn (fun s => Real.exp s * conjugatedKernel y s) (Ioi (0 : ℝ)) := by
    refine (integrable_chmdPrimeKernel_mul_exp_half y).integrableOn.congr_fun ?_ measurableSet_Ioi
    intro s _
    exact (exp_mul_conjugatedKernel y s).symm
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (m := 0) hcont.continuousWithinAt
    (fun x _ => hgd x) (hint1.sub hint2) htend
  rw [integral_sub hint1 hint2] at h
  have h0 : g 0 = -chmdPrimeKernel y 0 := by
    simp [hg, conjugatedKernel]
  rw [h0] at h
  have hK : ∫ s in Ioi (0 : ℝ), Real.exp s * conjugatedKernel y s =
      ∫ s in Ioi (0 : ℝ), chmdPrimeKernel y s * Real.exp (s / 2) :=
    setIntegral_congr_fun measurableSet_Ioi fun s _ => exp_mul_conjugatedKernel y s
  linarith

/-! ## Section 7: the integrated Chebyshev deficit as a tent series over the prime powers -/

theorem deficit_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp t - Chebyshev.psi (Real.exp t)) volume a b :=
  (Real.continuous_exp.intervalIntegrable a b).sub
    ((Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable)

theorem continuous_ccmLogChebyshevDeficitPrimitive : Continuous ccmLogChebyshevDeficitPrimitive :=
  intervalIntegral.continuous_primitive (fun a b => deficit_intervalIntegrable a b) 0

/-- Chebyshev's bound for the integrated deficit: `|D(s)| ≤ (log 4 + 5) e^s` for `s ≥ 0`. -/
theorem abs_ccmLogChebyshevDeficitPrimitive_le {s : ℝ} (hs : 0 ≤ s) :
    |ccmLogChebyshevDeficitPrimitive s| ≤ (Real.log 4 + 5) * Real.exp s := by
  unfold ccmLogChebyshevDeficitPrimitive
  have hi := deficit_intervalIntegrable 0 s
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc |∫ t in (0 : ℝ)..s, Real.exp t - Chebyshev.psi (Real.exp t)|
      ≤ ∫ t in (0 : ℝ)..s, |Real.exp t - Chebyshev.psi (Real.exp t)| :=
        intervalIntegral.abs_integral_le_integral_abs hs
    _ ≤ ∫ t in (0 : ℝ)..s, (Real.log 4 + 5) * Real.exp t := by
        refine intervalIntegral.integral_mono_on hs hi.abs
          ((Real.continuous_exp.const_mul _).intervalIntegrable 0 s) fun t _ => ?_
        have h1 := Chebyshev.psi_nonneg (Real.exp t)
        have h2 := Chebyshev.psi_le_const_mul_self (Real.exp_pos t).le
        have h3 := Real.exp_pos t
        rw [abs_le]
        constructor <;> nlinarith
    _ = (Real.log 4 + 5) * (Real.exp s - 1) := by
        rw [intervalIntegral.integral_const_mul, integral_exp, Real.exp_zero]
    _ ≤ (Real.log 4 + 5) * Real.exp s := by nlinarith

/-- The integrated deficit is the pole density `e^s − 1` minus the tent series over the prime
powers: `D(s) = e^s − 1 − Σ_n Λ(n) (s − log n)_+` for `s ≥ 0`. -/
theorem ccmLogChebyshevDeficitPrimitive_eq_tsum {s : ℝ} (hs : 0 ≤ s) :
    ccmLogChebyshevDeficitPrimitive s = Real.exp s - 1 -
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * max (s - Real.log n) 0 := by
  rw [ccmLogChebyshevDeficitPrimitive_eq_entry_prefix hs le_rfl, ccmPrimeEntryPrefix]
  simp only [ccmPrimeEntryTent]
  congr 1
  symm
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_Icc, not_and_or] at hn
  rcases hn with hn | hn
  · have h0 : n = 0 := by omega
    subst h0
    simp
  · have hn' : ⌊Real.exp s⌋₊ < n := by omega
    have hexp : Real.exp s < n := (Nat.floor_lt (Real.exp_pos s).le).mp hn'
    have hnpos : (0 : ℝ) < n := (Real.exp_pos s).trans hexp
    have hlog : s < Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr hexp
    rw [max_eq_right (by linarith), mul_zero]

/-- The tent series is dominated termwise by the prime weights:
`Λ(n) e^{−(π − ½) log n} = (Λ(n)/√n) e^{−(π − 1) log n}`. -/
theorem vonMangoldt_mul_exp_eq_chmdPrimeWeight_mul_exp (n : ℕ) :
    ArithmeticFunction.vonMangoldt n * Real.exp (-((π - 1 / 2) * Real.log n)) =
      chmdPrimeWeight n * Real.exp (-((π - 1) * Real.log n)) := by
  rcases lt_or_ge n 2 with hn | hn
  · rw [chmdPrimeWeight_eq_zero_of_lt_two hn, zero_mul]
    interval_cases n <;> simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    unfold chmdPrimeWeight
    rw [if_pos hn]
    have hsqrt : Real.sqrt n = Real.exp (Real.log n / 2) := by
      rw [Real.exp_half, Real.exp_log hn0]
    have hexp : Real.exp (-((π - 1 / 2) * Real.log n)) =
        (Real.exp (Real.log n / 2))⁻¹ * Real.exp (-((π - 1) * Real.log n)) := by
      rw [← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    rw [hsqrt, hexp]
    ring

/-- `Λ(n) f_y(log n) = (Λ(n)/√n) K_y(log n)`. -/
theorem vonMangoldt_mul_conjugatedKernel_log (y : ℝ) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n * conjugatedKernel y (Real.log n) =
      chmdPrimeWeight n * chmdPrimeKernel y (Real.log n) := by
  rcases lt_or_ge n 2 with hn | hn
  · rw [chmdPrimeWeight_eq_zero_of_lt_two hn, zero_mul]
    interval_cases n <;> simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    unfold chmdPrimeWeight conjugatedKernel
    rw [if_pos hn]
    have hsqrt : Real.sqrt n = Real.exp (Real.log n / 2) := by
      rw [Real.exp_half, Real.exp_log hn0]
    rw [hsqrt, Real.exp_neg]
    ring

/-! ## Section 8: the conjugated transport identity -/

theorem integrableOn_deficitPrimitive_mul_conjugatedLaplacian (y : ℝ) :
    IntegrableOn (fun s => ccmLogChebyshevDeficitPrimitive s * conjugatedLaplacian y s)
      (Ioi (0 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_conjugatedLaplacian_le y
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hdom : IntegrableOn (fun s : ℝ => (Real.log 4 + 5) * C * Real.exp (-(π - 3 / 2) * s))
      (Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith [Real.pi_gt_three])).const_mul _
  refine hdom.mono' (continuous_ccmLogChebyshevDeficitPrimitive.mul
    (continuous_conjugatedLaplacian y)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun s hs => ?_
  have hs0 : 0 ≤ s := le_of_lt hs
  rw [Real.norm_eq_abs, abs_mul]
  calc |ccmLogChebyshevDeficitPrimitive s| * |conjugatedLaplacian y s|
      ≤ (Real.log 4 + 5) * Real.exp s * (C * Real.exp (-((π - 1 / 2) * s))) :=
        mul_le_mul (abs_ccmLogChebyshevDeficitPrimitive_le hs0) (hC s hs0) (abs_nonneg _)
          (by positivity)
    _ = (Real.log 4 + 5) * C * Real.exp (-(π - 3 / 2) * s) := by
        rw [show (Real.log 4 + 5) * Real.exp s * (C * Real.exp (-((π - 1 / 2) * s))) =
          (Real.log 4 + 5) * C * (Real.exp s * Real.exp (-((π - 1 / 2) * s))) by ring,
          ← Real.exp_add]
        congr 2
        ring

/-- **Conjugated transport identity.**  The integrated Chebyshev deficit paired with the conjugated
Laplacian is `K_y(0)` minus the transported discrepancy measure:
`∫_0^∞ D(s) f_y''(s) ds = K_y(0) − T(y)`, where
`T(y) = Σ_n (Λ(n)/√n) K_y(log n) − ∫_0^∞ K_y(s) e^{s/2} ds`. -/
theorem integral_deficitPrimitive_mul_conjugatedLaplacian (y : ℝ) :
    ∫ s in Ioi (0 : ℝ), ccmLogChebyshevDeficitPrimitive s * conjugatedLaplacian y s =
      chmdPrimeKernel y 0 - chebyshevDiscrepancyTransport y := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_conjugatedLaplacian_le y
  set c : ℝ := π - 1 / 2 with hc
  have hcpos : 0 < c := by rw [hc]; linarith [Real.pi_gt_three]
  have hc2 : 0 < c / 2 := by positivity
  set F : ℕ → ℝ → ℝ := fun n s =>
    (Ioi (Real.log n)).indicator
      (fun s => -(ArithmeticFunction.vonMangoldt n * ((s - Real.log n) * conjugatedLaplacian y s))) s
    with hF
  have hFint : ∀ n, Integrable (F n) := by
    intro n
    have h : IntegrableOn
        (fun s => -(ArithmeticFunction.vonMangoldt n * ((s - Real.log n) * conjugatedLaplacian y s)))
        (Ioi (Real.log n)) :=
      ((integrableOn_sub_mul_conjugatedLaplacian y (Real.log_natCast_nonneg n)).const_mul
        (ArithmeticFunction.vonMangoldt n)).neg
    exact h.integrable_indicator measurableSet_Ioi
  -- each integral is the prime-weighted kernel value
  have hFval : ∀ n, ∫ s, F n s = -(chmdPrimeWeight n * chmdPrimeKernel y (Real.log n)) := by
    intro n
    simp only [hF]
    rw [integral_indicator measurableSet_Ioi, integral_neg, integral_const_mul,
      integral_Ioi_sub_mul_conjugatedLaplacian y (Real.log_natCast_nonneg n),
      vonMangoldt_mul_conjugatedKernel_log]
  -- summability of the norms
  have hFnorm : ∀ n, ∫ s, ‖F n s‖ ≤
      chmdPrimeWeight n * Real.exp (-((π - 1) * Real.log n)) * (C * (2 / c) * (c / 2)⁻¹) := by
    intro n
    have hln := Real.log_natCast_nonneg n
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    set ℓ := Real.log n with hℓ
    set B : ℝ := C * (2 / c) * Real.exp (-(c / 2 * ℓ)) with hB
    -- pointwise domination by an exponential
    have hbound : ∀ s, ‖F n s‖ ≤ (Ioi ℓ).indicator
        (fun s => ArithmeticFunction.vonMangoldt n * (B * Real.exp (-(c / 2 * s)))) s := by
      intro s
      simp only [hF]
      by_cases hs : s ∈ Ioi ℓ
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, Real.norm_eq_abs, abs_neg, abs_mul,
          abs_of_nonneg hΛ, abs_mul]
        have hsl : ℓ < s := hs
        have hs0 : 0 ≤ s := hln.trans hsl.le
        rw [abs_of_nonneg (sub_nonneg.mpr hsl.le)]
        refine mul_le_mul_of_nonneg_left ?_ hΛ
        -- (s − ℓ) e^{−cs} ≤ (2/c) e^{−(c/2)ℓ} e^{−(c/2)s}
        have hkey : (s - ℓ) * Real.exp (-(c * s)) ≤
            2 / c * Real.exp (-(c / 2 * ℓ)) * Real.exp (-(c / 2 * s)) := by
          have h1 : c / 2 * (s - ℓ) ≤ Real.exp (c / 2 * (s - ℓ)) := by
            linarith [Real.add_one_le_exp (c / 2 * (s - ℓ))]
          have h2 : s - ℓ ≤ 2 / c * Real.exp (c / 2 * (s - ℓ)) := by
            have h3 : 2 / c * (c / 2 * (s - ℓ)) ≤ 2 / c * Real.exp (c / 2 * (s - ℓ)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
            have h4 : 2 / c * (c / 2 * (s - ℓ)) = s - ℓ := by field_simp
            linarith
          calc (s - ℓ) * Real.exp (-(c * s))
              ≤ 2 / c * Real.exp (c / 2 * (s - ℓ)) * Real.exp (-(c * s)) :=
                mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
            _ = 2 / c * Real.exp (-(c / 2 * ℓ)) * Real.exp (-(c / 2 * s)) := by
                rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
                congr 2
                ring
        calc (s - ℓ) * |conjugatedLaplacian y s|
            ≤ (s - ℓ) * (C * Real.exp (-(c * s))) :=
              mul_le_mul_of_nonneg_left (hC s hs0) (sub_nonneg.mpr hsl.le)
          _ = C * ((s - ℓ) * Real.exp (-(c * s))) := by ring
          _ ≤ C * (2 / c * Real.exp (-(c / 2 * ℓ)) * Real.exp (-(c / 2 * s))) :=
              mul_le_mul_of_nonneg_left hkey hC0
          _ = B * Real.exp (-(c / 2 * s)) := by rw [hB]; ring
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, norm_zero]
    have hint : Integrable fun s => (Ioi ℓ).indicator
        (fun s => ArithmeticFunction.vonMangoldt n * (B * Real.exp (-(c / 2 * s)))) s := by
      refine IntegrableOn.integrable_indicator ?_ measurableSet_Ioi
      have h : IntegrableOn (fun x : ℝ => ArithmeticFunction.vonMangoldt n * B *
          Real.exp (-(c / 2) * x)) (Ioi ℓ) :=
        (exp_neg_integrableOn_Ioi ℓ hc2).const_mul _
      refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
      simp only [neg_mul]
      ring
    have hmono := integral_mono_of_nonneg (μ := volume) (f := fun s => ‖F n s‖)
      (g := fun s => (Ioi ℓ).indicator
        (fun s => ArithmeticFunction.vonMangoldt n * (B * Real.exp (-(c / 2 * s)))) s)
      (Eventually.of_forall fun s => norm_nonneg _) hint (Eventually.of_forall hbound)
    refine hmono.trans (le_of_eq ?_)
    rw [integral_indicator measurableSet_Ioi, integral_const_mul, integral_const_mul,
      integral_Ioi_exp_neg_mul' hc2]
    have hsplit : Real.exp (-(c / 2 * ℓ)) * Real.exp (-(c / 2 * ℓ)) = Real.exp (-(c * ℓ)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hw := vonMangoldt_mul_exp_eq_chmdPrimeWeight_mul_exp n
    rw [← hℓ, ← hc] at hw
    calc ArithmeticFunction.vonMangoldt n * (B * ((c / 2)⁻¹ * Real.exp (-(c / 2 * ℓ))))
        = ArithmeticFunction.vonMangoldt n * Real.exp (-(c * ℓ)) * (C * (2 / c) * (c / 2)⁻¹) := by
          rw [← hsplit, hB]; ring
      _ = _ := by rw [hw]
  have hFsum : Summable fun n => ∫ s, ‖F n s‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun s => norm_nonneg _)
      (fun n => hFnorm n) ?_
    exact summable_chmdPrimeWeight_mul_exp.mul_right _
  have hswap := integral_tsum_of_summable_integral_norm hFint hFsum
  simp_rw [hFval] at hswap
  rw [tsum_neg] at hswap
  -- identify the series pointwise on the forward half-line
  have hpt : ∀ s, (∑' n, F n s) =
      -(conjugatedLaplacian y s * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * max (s - Real.log n) 0) := by
    intro s
    rw [← tsum_mul_left, ← tsum_neg]
    refine tsum_congr fun n => ?_
    simp only [hF]
    by_cases hs : s ∈ Ioi (Real.log n)
    · rw [Set.indicator_of_mem hs, max_eq_left (sub_nonneg.mpr (le_of_lt hs))]
      ring
    · rw [Set.indicator_of_notMem hs, max_eq_right (by simpa [Set.mem_Ioi, not_lt] using hs)]
      ring
  have hpt' : ∀ s ∈ Ioi (0 : ℝ), (∑' n, F n s) =
      ccmLogChebyshevDeficitPrimitive s * conjugatedLaplacian y s -
        (Real.exp s - 1) * conjugatedLaplacian y s := by
    intro s hs
    rw [hpt s, ccmLogChebyshevDeficitPrimitive_eq_tsum (le_of_lt hs)]
    ring
  have hzero : ∀ s ∉ Ioi (0 : ℝ), (∑' n, F n s) = 0 := by
    intro s hs
    have hs0 : s ≤ 0 := by simpa [Set.mem_Ioi, not_lt] using hs
    rw [hpt s]
    have : (fun n : ℕ => ArithmeticFunction.vonMangoldt n * max (s - Real.log n) 0) =
        fun _ => 0 := by
      funext n
      rw [max_eq_right (by linarith [Real.log_natCast_nonneg n]), mul_zero]
    rw [this, tsum_zero, mul_zero, neg_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    setIntegral_congr_fun measurableSet_Ioi hpt',
    integral_sub (integrableOn_deficitPrimitive_mul_conjugatedLaplacian y)
      (integrableOn_exp_sub_one_mul_conjugatedLaplacian y),
    integral_Ioi_exp_sub_one_mul_conjugatedLaplacian] at hswap
  unfold chebyshevDiscrepancyTransport
  linarith

/-- **The derivative pairing with the discrepancy is the conjugated-Laplacian pairing with the
integrated deficit**: `∫_0^∞ ∂_sK_y(s) Δ(s) ds = K_y(0) + ∫_0^∞ D(s) f_y''(s) ds`. -/
theorem integral_kernelDeriv_mul_discrepancy_eq_conjugated (y : ℝ) :
    ∫ s in Ioi (0 : ℝ), kernelDeriv y s * chebyshevDiscrepancy s =
      chmdPrimeKernel y 0 +
        ∫ s in Ioi (0 : ℝ), ccmLogChebyshevDeficitPrimitive s * conjugatedLaplacian y s := by
  have h1 := chebyshevDiscrepancyTransport_eq y
  have h2 := integral_deficitPrimitive_mul_conjugatedLaplacian y
  linarith

/-- **Riemann hypothesis through the conjugated-Laplacian pairing (upper form).** -/
theorem riemannHypothesis_iff_integral_deficitPrimitive_mul_conjugatedLaplacian_bddAbove :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ y : ℝ, 0 ≤ y →
      (∫ s in Ioi (0 : ℝ), ccmLogChebyshevDeficitPrimitive s * conjugatedLaplacian y s) ≤ M := by
  rw [riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddBelow]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M + 4 / π, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_chmdPrimeKernel_le y 0
    have h3 := integral_deficitPrimitive_mul_conjugatedLaplacian y
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    linarith
  · rintro ⟨M, hM⟩
    refine ⟨M + 4 / π, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_chmdPrimeKernel_le y 0
    have h3 := integral_deficitPrimitive_mul_conjugatedLaplacian y
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    linarith

/-- **Riemann hypothesis through the conjugated-Laplacian pairing (lower form).** -/
theorem riemannHypothesis_iff_integral_deficitPrimitive_mul_conjugatedLaplacian_bddBelow :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ y : ℝ, 0 ≤ y →
      -M ≤ ∫ s in Ioi (0 : ℝ), ccmLogChebyshevDeficitPrimitive s * conjugatedLaplacian y s := by
  rw [riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddAbove]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M + 4 / π, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_chmdPrimeKernel_le y 0
    have h3 := integral_deficitPrimitive_mul_conjugatedLaplacian y
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    linarith
  · rintro ⟨M, hM⟩
    refine ⟨M + 4 / π, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_chmdPrimeKernel_le y 0
    have h3 := integral_deficitPrimitive_mul_conjugatedLaplacian y
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    linarith


/-! ## Section 9: injecting the Möbius-dilation decomposition of the integrated deficit -/

/-- The Λ-free Möbius part of the integrated Chebyshev deficit: the explicit work, the Mertens
channel and the large-divisor transient tail of the Möbius-dilation reconstruction. -/
def mobiusDeficitRest (T : ℝ) : ℝ :=
  ccmPrimeDeficitMobiusExplicitWork T +
    ccmPrimeDeficitDilationLimit * (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, moebiusCoeff n) +
      ccmPrimeDeficitMobiusTransientTail T

/-- `D = (Λ-free Möbius part) + (small-divisor head)` on the forward half-line. -/
theorem ccmLogChebyshevDeficitPrimitive_eq_mobiusDeficitRest_add_head {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T =
      mobiusDeficitRest T + ccmPrimeDeficitMobiusTransientHead T := by
  rw [ccmLogChebyshevDeficitPrimitive_eq_moebius_split hT]
  unfold mobiusDeficitRest
  ring

/-- A sum over `1 ≤ n ≤ ⌊φ s⌋₊` of measurable summands is measurable in `s`. -/
theorem measurable_sum_Icc_floor {g : ℕ → ℝ → ℝ} (hg : ∀ n, Measurable (g n)) {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    Measurable fun s => ∑ n ∈ Finset.Icc 1 ⌊φ s⌋₊, g n s := by
  have h : Measurable fun p : ℝ × ℕ => ∑ n ∈ Finset.Icc 1 p.2, g n p.1 :=
    measurable_from_prod_countable_left fun N =>
      Finset.measurable_sum (Finset.Icc 1 N) fun n _ => hg n
  exact h.comp (measurable_id.prodMk (Nat.measurable_floor.comp hφ))

theorem measurable_floor_exp_cast : Measurable fun T : ℝ => ((⌊Real.exp T⌋₊ : ℕ) : ℝ) :=
  measurable_from_nat.comp (Nat.measurable_floor.comp Real.measurable_exp)

theorem measurable_ccmPrimeDeficitDilationSource : Measurable ccmPrimeDeficitDilationSource := by
  unfold ccmPrimeDeficitDilationSource
  refine ((Real.measurable_exp.mul (measurable_sum_Icc_floor (fun n => measurable_const)
    Real.measurable_exp)).sub measurable_floor_exp_cast).sub
    (measurable_sum_Icc_floor (fun n => ?_) Real.measurable_exp)
  exact measurable_const.mul (measurable_id.sub measurable_const)

theorem measurable_ccmPrimeDeficitDilationRemainder :
    Measurable ccmPrimeDeficitDilationRemainder := by
  unfold ccmPrimeDeficitDilationRemainder
  exact (measurable_ccmPrimeDeficitDilationSource.sub
    (measurable_const.mul (Real.measurable_exp.sub measurable_const))).add
    (measurable_const.mul measurable_id)

theorem measurable_ccmPrimeDeficitMobiusTransientHead :
    Measurable ccmPrimeDeficitMobiusTransientHead := by
  unfold ccmPrimeDeficitMobiusTransientHead
  refine measurable_sum_Icc_floor (fun n => ?_) (Real.measurable_exp.comp (measurable_id.div_const 2))
  exact measurable_const.mul
    ((measurable_ccmPrimeDeficitDilationRemainder.comp (measurable_id.sub measurable_const)).sub
      measurable_const)

/-- The head budget `∫_0^∞ (s + 14)/4 · e^{−s/2} ds`. -/
def headBudget : ℝ := ∫ s in Ioi (0 : ℝ), (s + 14) / 4 * Real.exp (-(s / 2))

theorem integrableOn_headBudget :
    IntegrableOn (fun s : ℝ => (s + 14) / 4 * Real.exp (-(s / 2))) (Ioi (0 : ℝ)) := by
  have h1 := (_root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 1 (r := 1 / 2) (by norm_num)).const_mul
    (1 / 4)
  have h0 := (_root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 (r := 1 / 2) (by norm_num)).const_mul
    (7 / 2)
  refine (h1.add h0).integrableOn.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hs0 : 0 ≤ s := le_of_lt hs
  simp only [Pi.add_apply, pow_one, pow_zero, one_mul, abs_of_nonneg hs0]
  rw [show -(1 / 2 : ℝ) * s = -(s / 2) by ring]
  ring

theorem headBudget_nonneg : 0 ≤ headBudget :=
  setIntegral_nonneg measurableSet_Ioi fun s hs =>
    mul_nonneg (by linarith [le_of_lt (Set.mem_Ioi.mp hs)]) (Real.exp_pos _).le

theorem integrableOn_head_mul_conjugatedLaplacian (y : ℝ) :
    IntegrableOn (fun s => ccmPrimeDeficitMobiusTransientHead s * conjugatedLaplacian y s)
      (Ioi (0 : ℝ)) := by
  refine (integrableOn_headBudget.const_mul laplacianBound).mono'
    (measurable_ccmPrimeDeficitMobiusTransientHead.mul
      (continuous_conjugatedLaplacian y).measurable).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun s hs => ?_
  have hs0 : 0 ≤ s := le_of_lt hs
  rw [Real.norm_eq_abs, abs_mul]
  calc |ccmPrimeDeficitMobiusTransientHead s| * |conjugatedLaplacian y s|
      ≤ (s + 14) / 4 * (laplacianBound * Real.exp (-(s / 2))) :=
        mul_le_mul (abs_ccmPrimeDeficitMobiusTransientHead_le hs0) (abs_conjugatedLaplacian_le y s)
          (abs_nonneg _) (by linarith)
    _ = laplacianBound * ((s + 14) / 4 * Real.exp (-(s / 2))) := by ring

/-- **The small-divisor head pairs to a bounded quantity**, uniformly in the Klein–Gordon time. -/
theorem abs_integral_head_mul_conjugatedLaplacian_le (y : ℝ) :
    |∫ s in Ioi (0 : ℝ), ccmPrimeDeficitMobiusTransientHead s * conjugatedLaplacian y s| ≤
      laplacianBound * headBudget := by
  have hint : IntegrableOn (fun s : ℝ => laplacianBound * ((s + 14) / 4 * Real.exp (-(s / 2))))
      (Ioi (0 : ℝ)) :=
    integrableOn_headBudget.const_mul laplacianBound
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun s => ccmPrimeDeficitMobiusTransientHead s * conjugatedLaplacian y s) hint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => by
      have hs0 : 0 ≤ s := le_of_lt hs
      rw [Real.norm_eq_abs, abs_mul]
      calc |ccmPrimeDeficitMobiusTransientHead s| * |conjugatedLaplacian y s|
          ≤ (s + 14) / 4 * (laplacianBound * Real.exp (-(s / 2))) :=
            mul_le_mul (abs_ccmPrimeDeficitMobiusTransientHead_le hs0)
              (abs_conjugatedLaplacian_le y s) (abs_nonneg _) (by linarith)
        _ = laplacianBound * ((s + 14) / 4 * Real.exp (-(s / 2))) := by ring))
  rw [Real.norm_eq_abs, integral_const_mul] at h
  exact h

theorem integrableOn_mobiusDeficitRest_mul_conjugatedLaplacian (y : ℝ) :
    IntegrableOn (fun s => mobiusDeficitRest s * conjugatedLaplacian y s) (Ioi (0 : ℝ)) := by
  refine ((integrableOn_deficitPrimitive_mul_conjugatedLaplacian y).sub
    (integrableOn_head_mul_conjugatedLaplacian y)).congr_fun (fun s hs => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply]
  rw [ccmLogChebyshevDeficitPrimitive_eq_mobiusDeficitRest_add_head (le_of_lt hs)]
  ring

/-- The Λ-free Möbius pairing is the full deficit pairing minus the head pairing. -/
theorem integral_mobiusDeficitRest_mul_conjugatedLaplacian (y : ℝ) :
    ∫ s in Ioi (0 : ℝ), mobiusDeficitRest s * conjugatedLaplacian y s =
      (∫ s in Ioi (0 : ℝ), ccmLogChebyshevDeficitPrimitive s * conjugatedLaplacian y s) -
        ∫ s in Ioi (0 : ℝ), ccmPrimeDeficitMobiusTransientHead s * conjugatedLaplacian y s := by
  rw [← integral_sub (integrableOn_deficitPrimitive_mul_conjugatedLaplacian y)
    (integrableOn_head_mul_conjugatedLaplacian y)]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  rw [ccmLogChebyshevDeficitPrimitive_eq_mobiusDeficitRest_add_head (le_of_lt hs)]
  ring

/-- **Riemann hypothesis through the Λ-free Möbius pairing (upper form)**: the small-divisor head
is absorbed into a uniform constant. -/
theorem riemannHypothesis_iff_integral_mobiusDeficitRest_mul_conjugatedLaplacian_bddAbove :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ y : ℝ, 0 ≤ y →
      (∫ s in Ioi (0 : ℝ), mobiusDeficitRest s * conjugatedLaplacian y s) ≤ M := by
  rw [riemannHypothesis_iff_integral_deficitPrimitive_mul_conjugatedLaplacian_bddAbove]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M + laplacianBound * headBudget, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_le.mp (abs_integral_head_mul_conjugatedLaplacian_le y)
    have h3 := integral_mobiusDeficitRest_mul_conjugatedLaplacian y
    linarith [h2.1]
  · rintro ⟨M, hM⟩
    refine ⟨M + laplacianBound * headBudget, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_le.mp (abs_integral_head_mul_conjugatedLaplacian_le y)
    have h3 := integral_mobiusDeficitRest_mul_conjugatedLaplacian y
    linarith [h2.2]

/-- **Riemann hypothesis through the Λ-free Möbius pairing (lower form).** -/
theorem riemannHypothesis_iff_integral_mobiusDeficitRest_mul_conjugatedLaplacian_bddBelow :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ y : ℝ, 0 ≤ y →
      -M ≤ ∫ s in Ioi (0 : ℝ), mobiusDeficitRest s * conjugatedLaplacian y s := by
  rw [riemannHypothesis_iff_integral_deficitPrimitive_mul_conjugatedLaplacian_bddBelow]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M + laplacianBound * headBudget, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_le.mp (abs_integral_head_mul_conjugatedLaplacian_le y)
    have h3 := integral_mobiusDeficitRest_mul_conjugatedLaplacian y
    linarith [h2.2]
  · rintro ⟨M, hM⟩
    refine ⟨M + laplacianBound * headBudget, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_le.mp (abs_integral_head_mul_conjugatedLaplacian_le y)
    have h3 := integral_mobiusDeficitRest_mul_conjugatedLaplacian y
    linarith [h2.1]

end

end RHTower.CHMDChebyshevTransport

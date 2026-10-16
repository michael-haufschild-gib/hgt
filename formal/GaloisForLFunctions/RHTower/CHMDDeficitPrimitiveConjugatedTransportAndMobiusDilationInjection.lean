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

end

end RHTower.CHMDChebyshevTransport

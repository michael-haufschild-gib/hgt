import GaloisForLFunctions.RHTower.CHMDPoleDensityLawAndChebyshevDiscrepancyTransport

/-!
# CHMD: the derivative kernel and the function form of the Chebyshev-discrepancy transport law

The pole-density law expresses the Klein–Gordon prime wave as the pole wave plus the transport of the
`√`-weighted Chebyshev discrepancy *measure* `Σ_n (Λ(n)/√n) δ_{log n} − e^{s/2} ds`.  This module
integrates that transport by parts over the prime powers, producing the law in terms of the classical
discrepancy *function* `Δ(s) = Σ_{log n < s} Λ(n)/√n − 2 e^{s/2}` and the space derivative
`∂_s K_y(s)` of the prime kernel.

1. **The derivative of the d'Alembert kernel** (`dAlembertDeriv`, `hasDerivAt_dAlembertReal`): the
   real restriction of `D(w) = 2/S(w)`, `S(w) = sinh(πw)/w`, is differentiable with continuous
   derivative `D'`, given off the origin by `D'(v) = (2 sinh(πv) − 2πv cosh(πv)) / sinh²(πv)`, and
   dominated by `C (1+|v|) e^{−π|v|}` (`exists_abs_dAlembertDeriv_le`).  Inside the light cone the
   shifts obey `|G(s+a)| ≤ C(1+|y|) e^{π|y|} e^{−(π−1)|s|}` for `|a| ≤ |y|` (`shift_decay_le`).
2. **The space derivative of the prime kernel** (`kernelDeriv`, `hasDerivAt_chmdPrimeKernel_right`):
   `∂_s K_y(s) = D'(s+y) + D'(s−y) − (y²/2) ∫_{−1}^{1} B(2y²(1−t²)) (D'(s+yt) + D'(s−yt)) dt`,
   obtained by differentiating the light-cone tail under the integral sign; both `K_y` and
   `∂_s K_y` decay like `e^{−(π−1)|s|}` (`exists_abs_chmdPrimeKernel_le`, `exists_abs_kernelDeriv_le`),
   so `K_y(s) e^{s/2} → 0` and `∂_s K_y` is integrable against `e^{s/2}`.
3. **The Chebyshev step and discrepancy** (`chebyshevStep`, `chebyshevDiscrepancy`):
   `Ψ(s) = Σ_{log n < s} Λ(n)/√n` is a finite sum, nonnegative, monotone (hence measurable), vanishes
   for `s ≤ 0`, and obeys the Chebyshev bound `Ψ(s) ≤ (2 log 4 + 16) e^{s/2}` (`chebyshevStep_le`).
4. **Stieltjes integration by parts over the prime powers** (`tsum_chmdPrimeWeight_mul_kernel_eq`):
   `Σ_n (Λ(n)/√n) K_y(log n) = −∫_0^∞ ∂_sK_y(s) Ψ(s) ds`, from `K_y(ℓ) = −∫_ℓ^∞ ∂_sK_y` and Tonelli
   over the prime powers (the norms are summable because `∂_s K_y` decays like `e^{−(π−1)s}` and
   `Σ_n n · n^{−(π−1)} < ∞`).
5. **The pole counterterm integrated by parts** (`integral_Ioi_kernelDeriv_mul_two_exp_half`):
   `∫_0^∞ ∂_sK_y(s) · 2e^{s/2} ds = −2K_y(0) − ∫_0^∞ K_y(s) e^{s/2} ds`.
6. **Function form of the transport law** (`chmdPrimeWave_eq_pole_add_derivative_transport`):
   `chmdPrimeWave y = chmdPoleWave y + 2K_y(0) − poleShadow y − ∫_0^∞ ∂_sK_y(s) Δ(s) ds`,
   with `|2K_y(0) − poleShadow y| ≤ 16/π`; equivalently
   `chebyshevDiscrepancyTransport y = 2K_y(0) − ∫_0^∞ ∂_sK_y(s) Δ(s) ds`.  Consequently
   (`riemannHypothesis_iff_integral_kernelDeriv_mul_discrepancy_bddAbove`, `…_bddBelow`) the Riemann
   hypothesis holds iff the derivative pairing `∫_0^∞ ∂_sK_y(s) Δ(s) ds` is bounded above
   (equivalently below) for `y ≥ 0`: the entire one-sided content of the light-cone route is the
   pairing of the classical `√`-weighted Chebyshev discrepancy with the exponentially localized odd
   kernel `∂_s K_y`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace RHTower.CHMDChebyshevTransport

open RHTower.CHMDLightCone RHTower.CHMDStage22 GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Section 1: the derivative of the d'Alembert kernel -/

/-- The derivative `D'` of the d'Alembert kernel on the real line. -/
def dAlembertDeriv (v : ℝ) : ℝ := (deriv dAlembertKernel (v : ℂ)).re

theorem sinhSlope_ofReal_ne_zero (v : ℝ) : sinhSlope (v : ℂ) ≠ 0 :=
  sinhSlope_ne_zero_of_abs_im_lt (by simp)

theorem hasDerivAt_dAlembertReal (v : ℝ) : HasDerivAt dAlembertReal (dAlembertDeriv v) v :=
  (differentiableAt_dAlembertKernel (sinhSlope_ofReal_ne_zero v)).hasDerivAt.real_of_complex

theorem continuous_dAlembertDeriv : Continuous dAlembertDeriv := by
  have han : AnalyticOnNhd ℂ dAlembertKernel {w | sinhSlope w ≠ 0} :=
    differentiableOn_dAlembertKernel.analyticOnNhd isOpen_sinhSlope_ne_zero
  have hc : ContinuousOn (deriv dAlembertKernel) {w | sinhSlope w ≠ 0} := han.deriv.continuousOn
  exact Complex.continuous_re.comp
    (hc.comp_continuous Complex.continuous_ofReal fun v => sinhSlope_ofReal_ne_zero v)

/-- Explicit formula for `D'` off the origin. -/
theorem dAlembertDeriv_of_ne {v : ℝ} (hv : v ≠ 0) :
    dAlembertDeriv v =
      (2 * Real.sinh (π * v) - 2 * v * (π * Real.cosh (π * v))) / Real.sinh (π * v) ^ 2 := by
  have hs : Real.sinh (π * v) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]
    exact mul_ne_zero Real.pi_ne_zero hv
  have h1 : HasDerivAt (fun u : ℝ => 2 * u) 2 v := by
    simpa using (hasDerivAt_id v).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun u : ℝ => Real.sinh (π * u)) (Real.cosh (π * v) * π) v := by
    have := ((hasDerivAt_id' v).const_mul π).sinh
    rwa [mul_one] at this
  have h3 := h1.div h2 hs
  have heq : (fun u : ℝ => 2 * u / Real.sinh (π * u)) =ᶠ[𝓝 v] dAlembertReal := by
    filter_upwards [isOpen_ne.mem_nhds hv] with u hu
    exact (dAlembertReal_of_ne hu).symm
  have h4 := h3.congr_of_eventuallyEq heq.symm
  rw [(hasDerivAt_dAlembertReal v).unique h4]
  ring

theorem cosh_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- Exponential decay of `D'` away from the origin. -/
theorem abs_dAlembertDeriv_le_of_one_le {v : ℝ} (hv : 1 ≤ |v|) :
    |dAlembertDeriv v| ≤ 32 * π * (1 + |v|) * Real.exp (-(π * |v|)) := by
  have hv0 : v ≠ 0 := by
    intro h; rw [h, abs_zero] at hv; linarith
  have hpi := Real.pi_pos
  rw [dAlembertDeriv_of_ne hv0, abs_div, abs_pow, Real.abs_sinh, abs_mul, abs_of_pos hpi]
  have hπv : 1 ≤ π * |v| := by nlinarith [Real.pi_gt_three]
  have hS := exp_div_four_le_sinh hπv
  set E := Real.exp (π * |v|) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hSpos : 0 < Real.sinh (π * |v|) := by linarith
  have hcosh : Real.cosh (π * v) ≤ E := by
    rw [← Real.cosh_abs, abs_mul, abs_of_pos hpi]
    exact cosh_le_exp_of_nonneg (by positivity)
  have hcoshpos : 0 < Real.cosh (π * v) := Real.cosh_pos _
  have hnum : |2 * Real.sinh (π * v) - 2 * v * (π * Real.cosh (π * v))| ≤
      2 * Real.sinh (π * |v|) + 2 * |v| * (π * E) := by
    refine (abs_sub _ _).trans ?_
    simp only [abs_mul, abs_of_pos hpi, Real.abs_sinh, abs_of_pos hcoshpos, abs_two]
    have := mul_le_mul_of_nonneg_left hcosh (by positivity : (0 : ℝ) ≤ 2 * |v| * π)
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  have hE' : Real.exp (-(π * |v|)) = 1 / E := by rw [Real.exp_neg, hE, one_div]
  rw [hE']
  have hS2 : E ^ 2 / 16 ≤ Real.sinh (π * |v|) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hS 2
    rw [div_pow] at this
    linarith
  calc |2 * Real.sinh (π * v) - 2 * v * (π * Real.cosh (π * v))|
      ≤ 2 * Real.sinh (π * |v|) + 2 * |v| * (π * E) := hnum
    _ ≤ 32 * π * (1 + |v|) * (1 / E) * Real.sinh (π * |v|) ^ 2 := by
        have h1 : 2 * Real.sinh (π * |v|) ≤ 8 * (1 / E) * Real.sinh (π * |v|) ^ 2 := by
          have : 1 ≤ 4 * (1 / E) * Real.sinh (π * |v|) := by
            rw [show 4 * (1 / E) * Real.sinh (π * |v|) = (Real.sinh (π * |v|)) / (E / 4) by
              field_simp]
            rw [le_div_iff₀ (by positivity)]
            linarith
          nlinarith
        have h2 : 2 * |v| * (π * E) ≤ 32 * π * |v| * (1 / E) * Real.sinh (π * |v|) ^ 2 := by
          have : 2 * |v| * (π * E) = 32 * π * |v| * (1 / E) * (E ^ 2 / 16) := by
            field_simp; ring
          rw [this]
          gcongr
        have hpiv : 0 ≤ π * |v| := by positivity
        nlinarith [h1, h2, Real.pi_gt_three, abs_nonneg v]

/-- Global domination `|D'(v)| ≤ C (1+|v|) e^{−π|v|}` with some constant `C`. -/
theorem exists_abs_dAlembertDeriv_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, |dAlembertDeriv v| ≤ C * (1 + |v|) * Real.exp (-(π * |v|)) := by
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    continuous_dAlembertDeriv.continuousOn
  have hC₀0 : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ 0 ⟨by norm_num, by norm_num⟩)
  refine ⟨max (C₀ * Real.exp π) (32 * π), le_max_of_le_right (by positivity), fun v => ?_⟩
  have hpos : 0 < (1 + |v|) * Real.exp (-(π * |v|)) := by positivity
  rcases le_or_gt |v| 1 with hv | hv
  · have h1 := hC₀ v (abs_le.mp hv)
    rw [Real.norm_eq_abs] at h1
    have h2 : 1 ≤ Real.exp π * Real.exp (-(π * |v|)) := by
      rw [← Real.exp_add]
      have : 0 ≤ π + -(π * |v|) := by nlinarith [Real.pi_pos]
      exact Real.one_le_exp_iff.mpr this
    have h3 : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
    calc |dAlembertDeriv v| ≤ C₀ := h1
      _ ≤ C₀ * (Real.exp π * Real.exp (-(π * |v|))) := by nlinarith
      _ ≤ C₀ * Real.exp π * ((1 + |v|) * Real.exp (-(π * |v|))) := by
          have hE := (Real.exp_pos (-(π * |v|))).le
          have hCE : 0 ≤ C₀ * Real.exp π := by positivity
          calc C₀ * (Real.exp π * Real.exp (-(π * |v|)))
              = C₀ * Real.exp π * (1 * Real.exp (-(π * |v|))) := by ring
            _ ≤ C₀ * Real.exp π * ((1 + |v|) * Real.exp (-(π * |v|))) := by gcongr
      _ ≤ max (C₀ * Real.exp π) (32 * π) * (1 + |v|) * Real.exp (-(π * |v|)) := by
          have := mul_le_mul_of_nonneg_right (le_max_left (C₀ * Real.exp π) (32 * π)) hpos.le
          nlinarith
  · calc |dAlembertDeriv v| ≤ 32 * π * (1 + |v|) * Real.exp (-(π * |v|)) :=
          abs_dAlembertDeriv_le_of_one_le hv.le
      _ ≤ max (C₀ * Real.exp π) (32 * π) * (1 + |v|) * Real.exp (-(π * |v|)) := by
          have := mul_le_mul_of_nonneg_right (le_max_right (C₀ * Real.exp π) (32 * π)) hpos.le
          nlinarith

/-- Shifted exponential decay inside the light cone, for any kernel dominated by `C(1+|v|)e^{−π|v|}`. -/
theorem shift_decay_le {G : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hG : ∀ v, |G v| ≤ C * (1 + |v|) * Real.exp (-(π * |v|))) (y : ℝ) {a : ℝ} (ha : |a| ≤ |y|)
    (s : ℝ) :
    |G (s + a)| ≤ C * (1 + |y|) * Real.exp (π * |y|) * Real.exp (-((π - 1) * |s|)) := by
  have hD := hG (s + a)
  have h1 : |s + a| ≤ |s| + |y| := (abs_add_le s a).trans (by linarith)
  have h2 : |s| ≤ |s + a| + |y| := by
    have := abs_add_le (s + a) (-a)
    simp only [add_neg_cancel_right, abs_neg] at this
    linarith
  have hexp : Real.exp (-(π * |s + a|)) ≤ Real.exp (π * |y|) * Real.exp (-(π * |s|)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hlin : 1 + |s + a| ≤ (1 + |y|) * Real.exp |s| := by
    have h3 : 1 + |s| ≤ Real.exp |s| := by linarith [Real.add_one_le_exp |s|]
    have h4 : 1 + |s + a| ≤ (1 + |y|) * (1 + |s|) := by nlinarith [abs_nonneg y, abs_nonneg s]
    calc 1 + |s + a| ≤ (1 + |y|) * (1 + |s|) := h4
      _ ≤ (1 + |y|) * Real.exp |s| := mul_le_mul_of_nonneg_left h3 (by positivity)
  calc |G (s + a)| ≤ C * (1 + |s + a|) * Real.exp (-(π * |s + a|)) := hD
    _ ≤ C * ((1 + |y|) * Real.exp |s|) * (Real.exp (π * |y|) * Real.exp (-(π * |s|))) := by
        gcongr
    _ = C * (1 + |y|) * Real.exp (π * |y|) * Real.exp (-((π - 1) * |s|)) := by
        rw [show C * ((1 + |y|) * Real.exp |s|) * (Real.exp (π * |y|) * Real.exp (-(π * |s|))) =
          C * (1 + |y|) * Real.exp (π * |y|) * (Real.exp |s| * Real.exp (-(π * |s|))) by ring,
          ← Real.exp_add]
        congr 2
        ring

/-! ## Section 2: the space derivative of the prime kernel -/

theorem exists_abs_dAlembertDeriv_le_const :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, |dAlembertDeriv v| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_dAlembertDeriv_le
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

/-- The space derivative `∂_s K_y(s)` of the prime kernel, in light-cone form. -/
def kernelDeriv (y s : ℝ) : ℝ :=
  dAlembertDeriv (s + y) + dAlembertDeriv (s - y) -
    y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
      (dAlembertDeriv (s + y * t) + dAlembertDeriv (s - y * t))

/-- The light-cone tail is differentiable in the space variable, with derivative given by the
`D'`-tail. -/
theorem hasDerivAt_lightConeTail (y s : ℝ) :
    HasDerivAt (lightConeTail y)
      (∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
        (dAlembertDeriv (s + y * t) + dAlembertDeriv (s - y * t))) s := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_dAlembertDeriv_le_const
  set Bt : ℝ → ℝ := fun t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) with hBt
  have hBc : Continuous Bt := continuous_lightConeBesselReal.comp (by fun_prop)
  set F : ℝ → ℝ → ℝ := fun x t => Bt t * (dAlembertReal (x + y * t) + dAlembertReal (x - y * t))
    with hF
  set F' : ℝ → ℝ → ℝ := fun x t => Bt t * (dAlembertDeriv (x + y * t) + dAlembertDeriv (x - y * t))
    with hF'
  have hFc : ∀ x, Continuous (F x) := fun x =>
    hBc.mul ((continuous_dAlembertReal.comp (by fun_prop)).add (continuous_dAlembertReal.comp (by fun_prop)))
  have hF'c : ∀ x, Continuous (F' x) := fun x =>
    hBc.mul ((continuous_dAlembertDeriv.comp (by fun_prop)).add
      (continuous_dAlembertDeriv.comp (by fun_prop)))
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
    have h3 : |dAlembertDeriv (x + y * t) + dAlembertDeriv (x - y * t)| ≤ 2 * C := by
      calc |dAlembertDeriv (x + y * t) + dAlembertDeriv (x - y * t)|
          ≤ |dAlembertDeriv (x + y * t)| + |dAlembertDeriv (x - y * t)| := abs_add_le _ _
        _ ≤ 2 * C := by linarith
    exact mul_le_mul hB h3 (abs_nonneg _) (Real.exp_pos _).le
  · simp only [hF, hF']
    have h1 := (hasDerivAt_dAlembertReal (x + y * t)).comp x ((hasDerivAt_id' x).add_const (y * t))
    have h2 := (hasDerivAt_dAlembertReal (x - y * t)).comp x ((hasDerivAt_id' x).sub_const (y * t))
    have h := (h1.add h2).const_mul (Bt t)
    simp only [mul_one] at h
    exact h

theorem continuous_lightConeDerivTail (y : ℝ) :
    Continuous fun s => ∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
      (dAlembertDeriv (s + y * t) + dAlembertDeriv (s - y * t)) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun s t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
      (dAlembertDeriv (s + y * t) + dAlembertDeriv (s - y * t)))
    ((continuous_lightConeBesselReal.comp (by fun_prop)).mul
      ((continuous_dAlembertDeriv.comp (by fun_prop)).add (continuous_dAlembertDeriv.comp (by fun_prop))))
    _ _

theorem continuous_kernelDeriv (y : ℝ) : Continuous (kernelDeriv y) := by
  unfold kernelDeriv
  exact ((continuous_dAlembertDeriv.comp (by fun_prop)).add
    (continuous_dAlembertDeriv.comp (by fun_prop))).sub
    (continuous_const.mul (continuous_lightConeDerivTail y))

/-- **The prime kernel is differentiable in space**, with derivative `kernelDeriv y s`. -/
theorem hasDerivAt_chmdPrimeKernel_right (y s : ℝ) :
    HasDerivAt (fun s => chmdPrimeKernel y s) (kernelDeriv y s) s := by
  have hfun : (fun s => chmdPrimeKernel y s) = fun s =>
      (dAlembertReal (s + y) + dAlembertReal (s - y)) - y ^ 2 / 2 * lightConeTail y s :=
    funext fun s => chmdPrimeKernel_eq_pair_sub_tail y s
  rw [hfun]
  have h1 := (hasDerivAt_dAlembertReal (s + y)).comp s ((hasDerivAt_id' s).add_const y)
  have h2 := (hasDerivAt_dAlembertReal (s - y)).comp s ((hasDerivAt_id' s).sub_const y)
  have h3 := (hasDerivAt_lightConeTail y s).const_mul (y ^ 2 / 2)
  have h := (h1.add h2).sub h3
  simp only [mul_one] at h
  exact h

/-- Exponential decay of the space derivative of the prime kernel. -/
theorem exists_abs_kernelDeriv_le (y : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |kernelDeriv y s| ≤ C * Real.exp (-((π - 1) * |s|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_dAlembertDeriv_le
  set K : ℝ := C * (1 + |y|) * Real.exp (π * |y|) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * K + y ^ 2 * (Real.exp (y ^ 2 / 2) * (2 * K)),
    add_nonneg (by linarith) (mul_nonneg (sq_nonneg y) (mul_nonneg (Real.exp_pos _).le (by linarith))),
    fun s => ?_⟩
  have hpair : |dAlembertDeriv (s + y) + dAlembertDeriv (s - y)| ≤
      2 * K * Real.exp (-((π - 1) * |s|)) := by
    have e1 := shift_decay_le hC0 hC y (a := y) le_rfl s
    have e2 := shift_decay_le hC0 hC y (a := -y) (by rw [abs_neg]) s
    rw [← sub_eq_add_neg] at e2
    calc |dAlembertDeriv (s + y) + dAlembertDeriv (s - y)|
        ≤ |dAlembertDeriv (s + y)| + |dAlembertDeriv (s - y)| := abs_add_le _ _
      _ ≤ 2 * K * Real.exp (-((π - 1) * |s|)) := by rw [hK]; linarith
  have htail : |∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
      (dAlembertDeriv (s + y * t) + dAlembertDeriv (s - y * t))| ≤
      Real.exp (y ^ 2 / 2) * (2 * K * Real.exp (-((π - 1) * |s|))) * 2 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
      (C := Real.exp (y ^ 2 / 2) * (2 * K * Real.exp (-((π - 1) * |s|))))
      (f := fun t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
        (dAlembertDeriv (s + y * t) + dAlembertDeriv (s - y * t))) fun t ht => by
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
        calc |dAlembertDeriv (s + y * t) + dAlembertDeriv (s - y * t)|
            ≤ |dAlembertDeriv (s + y * t)| + |dAlembertDeriv (s - y * t)| := abs_add_le _ _
          _ ≤ 2 * K * Real.exp (-((π - 1) * |s|)) := by rw [hK]; linarith
    rw [Real.norm_eq_abs] at h
    simpa [abs_of_pos (by norm_num : (0 : ℝ) < 1 - -1), show (1 : ℝ) - -1 = 2 by norm_num] using h
  unfold kernelDeriv
  have hy2 : 0 ≤ y ^ 2 / 2 := by positivity
  calc |dAlembertDeriv (s + y) + dAlembertDeriv (s - y) - y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1,
        lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
          (dAlembertDeriv (s + y * t) + dAlembertDeriv (s - y * t))|
      ≤ |dAlembertDeriv (s + y) + dAlembertDeriv (s - y)| + y ^ 2 / 2 * |∫ t in (-1 : ℝ)..1,
        lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
          (dAlembertDeriv (s + y * t) + dAlembertDeriv (s - y * t))| := by
        rw [sub_eq_add_neg]
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_mul, abs_of_nonneg hy2]
    _ ≤ 2 * K * Real.exp (-((π - 1) * |s|)) +
        y ^ 2 / 2 * (Real.exp (y ^ 2 / 2) * (2 * K * Real.exp (-((π - 1) * |s|))) * 2) := by
        gcongr
    _ = (2 * K + y ^ 2 * (Real.exp (y ^ 2 / 2) * (2 * K))) * Real.exp (-((π - 1) * |s|)) := by
        ring

/-- Exponential decay of the prime kernel itself in the space variable. -/
theorem exists_abs_chmdPrimeKernel_le (y : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |chmdPrimeKernel y s| ≤ C * Real.exp (-((π - 1) * |s|)) := by
  set K : ℝ := 16 * (1 + |y|) * Real.exp (π * |y|) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K + y ^ 2 * (Real.exp (y ^ 2 / 2) * K),
    add_nonneg hK0 (mul_nonneg (sq_nonneg y) (mul_nonneg (Real.exp_pos _).le hK0)), fun s => ?_⟩
  have hpair : |dAlembertReal (s + y) + dAlembertReal (s - y)| ≤ K * Real.exp (-((π - 1) * |s|)) := by
    have e := dAlembert_pair_shift_le y (t := 1) (by simp) s
    rw [mul_one] at e
    rw [abs_of_pos (add_pos (dAlembertReal_pos _) (dAlembertReal_pos _))]
    exact e
  have htail : |lightConeTail y s| ≤ Real.exp (y ^ 2 / 2) * (K * Real.exp (-((π - 1) * |s|))) * 2 := by
    unfold lightConeTail
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
      (C := Real.exp (y ^ 2 / 2) * (K * Real.exp (-((π - 1) * |s|))))
      (f := fun t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
        (dAlembertReal (s + y * t) + dAlembertReal (s - y * t))) fun t ht => by
        have hta := mem_uIoc_neg_one_one_abs_le ht
        have hB := abs_lightConeBesselReal_light_cone_le y hta
        have e := dAlembert_pair_shift_le y hta s
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (add_pos (dAlembertReal_pos _) (dAlembertReal_pos _))]
        exact mul_le_mul hB e (add_pos (dAlembertReal_pos _) (dAlembertReal_pos _)).le
          (Real.exp_pos _).le
    rw [Real.norm_eq_abs] at h
    simpa [abs_of_pos (by norm_num : (0 : ℝ) < 1 - -1), show (1 : ℝ) - -1 = 2 by norm_num] using h
  rw [chmdPrimeKernel_eq_pair_sub_tail]
  have hy2 : 0 ≤ y ^ 2 / 2 := by positivity
  calc |dAlembertReal (s + y) + dAlembertReal (s - y) - y ^ 2 / 2 * lightConeTail y s|
      ≤ |dAlembertReal (s + y) + dAlembertReal (s - y)| + y ^ 2 / 2 * |lightConeTail y s| := by
        rw [sub_eq_add_neg]
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_mul, abs_of_nonneg hy2]
    _ ≤ K * Real.exp (-((π - 1) * |s|)) +
        y ^ 2 / 2 * (Real.exp (y ^ 2 / 2) * (K * Real.exp (-((π - 1) * |s|))) * 2) := by
        gcongr
    _ = (K + y ^ 2 * (Real.exp (y ^ 2 / 2) * K)) * Real.exp (-((π - 1) * |s|)) := by ring

theorem tendsto_exp_neg_mul_abs_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun s : ℝ => Real.exp (-(c * |s|))) atTop (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => c * |s|) atTop atTop :=
    (tendsto_abs_atTop_atTop).const_mul_atTop hc
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h

theorem tendsto_chmdPrimeKernel_atTop (y : ℝ) :
    Tendsto (fun s => chmdPrimeKernel y s) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_chmdPrimeKernel_le y
  refine squeeze_zero_norm (fun s => ?_) ((tendsto_exp_neg_mul_abs_atTop (c := π - 1)
    (by linarith [Real.pi_gt_three])).const_mul C |>.trans ?_)
  · rw [Real.norm_eq_abs]; exact hC s
  · simp

theorem tendsto_chmdPrimeKernel_mul_exp_half_atTop (y : ℝ) :
    Tendsto (fun s => chmdPrimeKernel y s * (2 * Real.exp (s / 2))) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_chmdPrimeKernel_le y
  have hβ : 0 < π - 3 / 2 := by linarith [Real.pi_gt_three]
  refine squeeze_zero_norm (fun s => ?_)
    (((tendsto_exp_neg_mul_abs_atTop hβ).const_mul (2 * C)).trans (by simp))
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.exp (s / 2))]
  have h1 := hC s
  have h2 : Real.exp (s / 2) ≤ Real.exp (|s| / 2) := Real.exp_le_exp.mpr (by linarith [le_abs_self s])
  calc |chmdPrimeKernel y s| * (2 * Real.exp (s / 2))
      ≤ C * Real.exp (-((π - 1) * |s|)) * (2 * Real.exp (|s| / 2)) := by gcongr
    _ = 2 * C * Real.exp (-((π - 3 / 2) * |s|)) := by
        rw [show C * Real.exp (-((π - 1) * |s|)) * (2 * Real.exp (|s| / 2)) =
          2 * C * (Real.exp (-((π - 1) * |s|)) * Real.exp (|s| / 2)) by ring, ← Real.exp_add]
        congr 2
        ring

theorem integrable_kernelDeriv (y : ℝ) : Integrable (kernelDeriv y) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_kernelDeriv_le y
  have hβ : 0 < π - 1 := by linarith [Real.pi_gt_three]
  refine ((integrable_exp_neg_mul_abs_sub hβ 0).const_mul C).mono'
    (continuous_kernelDeriv y).aestronglyMeasurable (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, zero_sub, abs_neg]
  exact hC s

theorem integrable_kernelDeriv_mul_exp_half (y : ℝ) :
    Integrable fun s => kernelDeriv y s * Real.exp (s / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_kernelDeriv_le y
  have hβ : 0 < π - 3 / 2 := by linarith [Real.pi_gt_three]
  refine ((integrable_exp_neg_mul_abs_sub hβ 0).const_mul C).mono'
    ((continuous_kernelDeriv y).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, zero_sub, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h2 : Real.exp (s / 2) ≤ Real.exp (|s| / 2) := Real.exp_le_exp.mpr (by linarith [le_abs_self s])
  calc |kernelDeriv y s| * Real.exp (s / 2)
      ≤ C * Real.exp (-((π - 1) * |s|)) * Real.exp (|s| / 2) := by gcongr; exact hC s
    _ = C * Real.exp (-((π - 3 / 2) * |s|)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-! ## Section 3: the `√`-weighted Chebyshev step and discrepancy -/

/-- The strict `√`-weighted Chebyshev step `Ψ(s) = Σ_{log n < s} Λ(n)/√n`. -/
def chebyshevStep (s : ℝ) : ℝ :=
  ∑' n : ℕ, if Real.log n < s then chmdPrimeWeight n else 0

/-- The `√`-weighted Chebyshev discrepancy `Δ(s) = Ψ(s) − 2 e^{s/2}`. -/
def chebyshevDiscrepancy (s : ℝ) : ℝ := chebyshevStep s - 2 * Real.exp (s / 2)

theorem chebyshevStep_term_eq_zero {s : ℝ} {n : ℕ} (hn : ⌊Real.exp s⌋₊ + 1 ≤ n) :
    (if Real.log n < s then chmdPrimeWeight n else 0) = 0 := by
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have h1 : Real.exp s < n := by
    have := Nat.lt_floor_add_one (Real.exp s)
    have h2 : ((⌊Real.exp s⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have h3 : s < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr h1
  rw [if_neg (not_lt.mpr h3.le)]

theorem summable_chebyshevStep_term (s : ℝ) :
    Summable fun n : ℕ => if Real.log n < s then chmdPrimeWeight n else 0 :=
  summable_of_ne_finset_zero (s := Finset.range (⌊Real.exp s⌋₊ + 1)) fun n hn =>
    chebyshevStep_term_eq_zero (by simpa [Finset.mem_range, not_lt] using hn)

theorem chebyshevStep_eq_sum (s : ℝ) :
    chebyshevStep s = ∑ n ∈ Finset.range (⌊Real.exp s⌋₊ + 1),
      if Real.log n < s then chmdPrimeWeight n else 0 :=
  tsum_eq_sum fun n hn => chebyshevStep_term_eq_zero (by simpa [Finset.mem_range, not_lt] using hn)

theorem chebyshevStep_nonneg (s : ℝ) : 0 ≤ chebyshevStep s :=
  tsum_nonneg fun n => by
    split_ifs
    · exact chmdPrimeWeight_nonneg n
    · exact le_rfl

theorem chebyshevStep_mono : Monotone chebyshevStep := by
  intro s s' hss'
  refine (summable_chebyshevStep_term s).tsum_le_tsum (fun n => ?_) (summable_chebyshevStep_term s')
  by_cases h : Real.log n < s
  · rw [if_pos h, if_pos (lt_of_lt_of_le h hss')]
  · rw [if_neg h]
    split_ifs
    · exact chmdPrimeWeight_nonneg n
    · exact le_rfl

theorem measurable_chebyshevStep : Measurable chebyshevStep :=
  chebyshevStep_mono.measurable

theorem chebyshevStep_eq_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) : chebyshevStep s = 0 := by
  unfold chebyshevStep
  have h : ∀ n : ℕ, (if Real.log n < s then chmdPrimeWeight n else 0) = 0 := by
    intro n
    rw [if_neg]
    have := Real.log_natCast_nonneg n
    linarith
  simp_rw [h]
  exact tsum_zero

theorem chebyshevStep_term_le (s : ℝ) (n : ℕ) :
    (if Real.log n < s then chmdPrimeWeight n else 0) ≤
      ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
  have hnn : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  split_ifs with h
  · unfold chmdPrimeWeight
    split_ifs
    · exact le_rfl
    · exact hnn
  · exact hnn

/-- **Chebyshev bound for the step**: `Ψ(s) ≤ (2 log 4 + 16) e^{s/2}` for `s ≥ 0`. -/
theorem chebyshevStep_le {s : ℝ} (hs : 0 ≤ s) :
    chebyshevStep s ≤ (2 * Real.log 4 + 16) * Real.exp (s / 2) := by
  rw [chebyshevStep_eq_sum]
  set N := ⌊Real.exp s⌋₊ with hN
  have h1 : (∑ n ∈ Finset.range (N + 1), if Real.log n < s then chmdPrimeWeight n else 0) ≤
      ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    Finset.sum_le_sum fun n _ => chebyshevStep_term_le s n
  have h2 : (∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n / Real.sqrt n) =
      ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
    symm
    refine Finset.sum_subset (fun n hn => ?_) fun n hn hn' => ?_
    · rw [Finset.mem_Ioc] at hn
      rw [Finset.mem_range]
      omega
    · rw [Finset.mem_range] at hn
      rw [Finset.mem_Ioc] at hn'
      have : n = 0 := by omega
      subst this
      simp
  have h3 := Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le (x := Real.exp s)
    (Real.one_le_exp_iff.mpr hs)
  have h4 : Real.sqrt (Real.exp s) = Real.exp (s / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  rw [h4, ← hN] at h3
  linarith

/-! ## Section 4: Stieltjes integration by parts over the prime powers -/

theorem integral_Ioi_exp_neg_mul' {c : ℝ} (hc : 0 < c) (ℓ : ℝ) :
    ∫ s in Ioi ℓ, Real.exp (-(c * s)) = c⁻¹ * Real.exp (-(c * ℓ)) := by
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) ℓ hc
  simp only [smul_eq_mul, integral_exp_neg_Ioi] at h
  exact h

/-- The prime kernel is the integral of its space derivative over the forward half-line. -/
theorem chmdPrimeKernel_eq_neg_integral_Ioi (y ℓ : ℝ) :
    chmdPrimeKernel y ℓ = -∫ s in Ioi ℓ, kernelDeriv y s := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun s => chmdPrimeKernel y s)
    (f' := kernelDeriv y) (a := ℓ) (m := 0)
    (continuous_chmdPrimeKernel_right y).continuousWithinAt
    (fun x _ => hasDerivAt_chmdPrimeKernel_right y x)
    (integrable_kernelDeriv y).integrableOn
    (tendsto_chmdPrimeKernel_atTop y)
  rw [h]
  ring

theorem chmdPrimeWeight_mul_exp_le (n : ℕ) :
    chmdPrimeWeight n * Real.exp (-((π - 1) * Real.log n)) ≤ ((n : ℝ) ^ (π - 2))⁻¹ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [chmdPrimeWeight_eq_zero_of_lt_two (by norm_num : (0 : ℕ) < 2), zero_mul,
      Nat.cast_zero]
    rw [Real.zero_rpow (by linarith [Real.pi_gt_three])]
    simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hw := chmdPrimeWeight_le n
    have hw0 := chmdPrimeWeight_nonneg n
    have he : Real.exp (-((π - 1) * Real.log n)) = ((n : ℝ) ^ (π - 1))⁻¹ := by
      rw [Real.rpow_def_of_pos hn', ← Real.exp_neg]
      congr 1
      ring
    have hsub : (n : ℝ) ^ (π - 2) = (n : ℝ) ^ (π - 1) / (n : ℝ) := by
      rw [show π - 2 = (π - 1) - 1 by ring, Real.rpow_sub hn', Real.rpow_one]
    rw [he, hsub, inv_div]
    have hp : 0 < (n : ℝ) ^ (π - 1) := Real.rpow_pos_of_pos hn' _
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hw (inv_pos.mpr hp).le

theorem summable_chmdPrimeWeight_mul_exp :
    Summable fun n : ℕ => chmdPrimeWeight n * Real.exp (-((π - 1) * Real.log n)) := by
  refine (Real.summable_nat_rpow_inv.mpr (by linarith [Real.pi_gt_three] : 1 < π - 2)).of_nonneg_of_le
    (fun n => mul_nonneg (chmdPrimeWeight_nonneg n) (Real.exp_pos _).le)
    fun n => chmdPrimeWeight_mul_exp_le n

/-- **Stieltjes integration by parts over the prime powers.**  The prime sum of the kernel is the
integral of the space derivative against the Chebyshev step:
`Σ_n (Λ(n)/√n) K_y(log n) = −∫_0^∞ ∂_sK_y(s) Ψ(s) ds`. -/
theorem tsum_chmdPrimeWeight_mul_kernel_eq (y : ℝ) :
    (∑' n : ℕ, chmdPrimeWeight n * chmdPrimeKernel y (Real.log n)) =
      -∫ s in Ioi (0 : ℝ), kernelDeriv y s * chebyshevStep s := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_kernelDeriv_le y
  set F : ℕ → ℝ → ℝ := fun n s =>
    (Ioi (Real.log n)).indicator (fun s => -(chmdPrimeWeight n * kernelDeriv y s)) s with hF
  have hFint : ∀ n, Integrable (F n) := fun n =>
    (((integrable_kernelDeriv y).const_mul (chmdPrimeWeight n)).neg).indicator measurableSet_Ioi
  -- each integral is the prime-weighted kernel value
  have hFval : ∀ n, ∫ s, F n s = chmdPrimeWeight n * chmdPrimeKernel y (Real.log n) := by
    intro n
    simp only [hF]
    rw [integral_indicator measurableSet_Ioi, integral_neg, integral_const_mul,
      chmdPrimeKernel_eq_neg_integral_Ioi y (Real.log n)]
    ring
  -- summability of the norms
  have hβ : 0 < π - 1 := by linarith [Real.pi_gt_three]
  have hFnorm : ∀ n, ∫ s, ‖F n s‖ ≤
      chmdPrimeWeight n * (C * ((π - 1)⁻¹ * Real.exp (-((π - 1) * Real.log n)))) := by
    intro n
    have hln := Real.log_natCast_nonneg n
    have hbound : ∀ s, ‖F n s‖ ≤
        (Ioi (Real.log n)).indicator (fun s => chmdPrimeWeight n * (C * Real.exp (-((π - 1) * s)))) s := by
      intro s
      simp only [hF]
      by_cases hs : s ∈ Ioi (Real.log n)
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, Real.norm_eq_abs, abs_neg, abs_mul,
          abs_of_nonneg (chmdPrimeWeight_nonneg n)]
        have hs0 : 0 ≤ s := le_trans hln (le_of_lt hs)
        have := hC s
        rw [abs_of_nonneg hs0] at this
        exact mul_le_mul_of_nonneg_left this (chmdPrimeWeight_nonneg n)
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, norm_zero]
    have hint : Integrable fun s =>
        (Ioi (Real.log n)).indicator (fun s => chmdPrimeWeight n * (C * Real.exp (-((π - 1) * s)))) s := by
      refine IntegrableOn.integrable_indicator ?_ measurableSet_Ioi
      have h : IntegrableOn (fun x : ℝ => chmdPrimeWeight n * C * Real.exp (-(π - 1) * x))
          (Ioi (Real.log n)) :=
        (exp_neg_integrableOn_Ioi (Real.log n) hβ).const_mul (chmdPrimeWeight n * C)
      refine MeasureTheory.IntegrableOn.congr_fun h (fun s _ => ?_) measurableSet_Ioi
      simp only [neg_mul]
      ring
    have hmono := integral_mono_of_nonneg (μ := volume) (f := fun s => ‖F n s‖)
      (g := fun s => (Ioi (Real.log n)).indicator
        (fun s => chmdPrimeWeight n * (C * Real.exp (-((π - 1) * s)))) s)
      (Eventually.of_forall fun s => norm_nonneg _) hint (Eventually.of_forall hbound)
    refine hmono.trans (le_of_eq ?_)
    rw [integral_indicator measurableSet_Ioi, integral_const_mul, integral_const_mul,
      integral_Ioi_exp_neg_mul' hβ]
  have hFsum : Summable fun n => ∫ s, ‖F n s‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun s => norm_nonneg _)
      (fun n => hFnorm n) ?_
    refine (summable_chmdPrimeWeight_mul_exp.mul_left (C * (π - 1)⁻¹)).congr fun n => ?_
    ring
  have hswap := integral_tsum_of_summable_integral_norm hFint hFsum
  simp_rw [hFval] at hswap
  rw [hswap]
  -- identify the series pointwise
  have hpt : ∀ s, (∑' n, F n s) = -(kernelDeriv y s * chebyshevStep s) := by
    intro s
    unfold chebyshevStep
    rw [← tsum_mul_left, ← tsum_neg]
    refine tsum_congr fun n => ?_
    simp only [hF]
    by_cases hs : s ∈ Ioi (Real.log n)
    · rw [Set.indicator_of_mem hs, if_pos (Set.mem_Ioi.mp hs)]
      ring
    · rw [Set.indicator_of_notMem hs, if_neg (fun h => hs (Set.mem_Ioi.mpr h))]
      ring
  simp_rw [hpt]
  rw [integral_neg]
  congr 1
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_
  have hs0 : s ≤ 0 := by simpa [Set.mem_Ioi, not_lt] using hs
  rw [chebyshevStep_eq_zero_of_nonpos hs0, mul_zero]

/-! ## Section 5: the pole counterterm integrated by parts -/

theorem integrableOn_kernelDeriv_mul_two_exp_half (y : ℝ) :
    IntegrableOn (fun s => kernelDeriv y s * (2 * Real.exp (s / 2))) (Ioi (0 : ℝ)) := by
  have := ((integrable_kernelDeriv_mul_exp_half y).const_mul 2).integrableOn (s := Ioi (0 : ℝ))
  refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
  ring

/-- Integration by parts of the pole density against the space derivative of the kernel:
`∫_0^∞ ∂_sK_y(s)·2e^{s/2} ds = −2K_y(0) − ∫_0^∞ K_y(s) e^{s/2} ds`. -/
theorem integral_Ioi_kernelDeriv_mul_two_exp_half (y : ℝ) :
    ∫ s in Ioi (0 : ℝ), kernelDeriv y s * (2 * Real.exp (s / 2)) =
      -(2 * chmdPrimeKernel y 0) - ∫ s in Ioi (0 : ℝ), chmdPrimeKernel y s * Real.exp (s / 2) := by
  have he : ∀ s : ℝ, HasDerivAt (fun s => 2 * Real.exp (s / 2)) (Real.exp (s / 2)) s := by
    intro s
    have := (((hasDerivAt_id' s).div_const 2).exp).const_mul 2
    refine this.congr_deriv ?_
    ring
  have hf : ∀ x : ℝ, HasDerivAt (fun s => chmdPrimeKernel y s * (2 * Real.exp (s / 2)))
      (kernelDeriv y x * (2 * Real.exp (x / 2)) + chmdPrimeKernel y x * Real.exp (x / 2)) x :=
    fun x => (hasDerivAt_chmdPrimeKernel_right y x).mul (he x)
  have hint1 := integrableOn_kernelDeriv_mul_two_exp_half y
  have hint2 : IntegrableOn (fun s => chmdPrimeKernel y s * Real.exp (s / 2)) (Ioi (0 : ℝ)) :=
    (integrable_chmdPrimeKernel_mul_exp_half y).integrableOn
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (m := 0)
    ((continuous_chmdPrimeKernel_right y).mul (by fun_prop)).continuousWithinAt
    (fun x _ => hf x) (hint1.add hint2) (tendsto_chmdPrimeKernel_mul_exp_half_atTop y)
  rw [integral_add hint1 hint2] at h
  have h0 : chmdPrimeKernel y 0 * (2 * Real.exp (0 / 2)) = 2 * chmdPrimeKernel y 0 := by
    rw [zero_div, Real.exp_zero]; ring
  simp only [Pi.mul_apply] at h
  linarith

theorem integrableOn_kernelDeriv_mul_chebyshevStep (y : ℝ) :
    IntegrableOn (fun s => kernelDeriv y s * chebyshevStep s) (Ioi (0 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_kernelDeriv_le y
  have hβ : 0 < π - 3 / 2 := by linarith [Real.pi_gt_three]
  have hg : IntegrableOn (fun s => C * (2 * Real.log 4 + 16) * Real.exp (-((π - 3 / 2) * s)))
      (Ioi (0 : ℝ)) := by
    have h : IntegrableOn (fun x : ℝ => C * (2 * Real.log 4 + 16) * Real.exp (-(π - 3 / 2) * x))
        (Ioi (0 : ℝ)) :=
      (exp_neg_integrableOn_Ioi (0 : ℝ) hβ).const_mul (C * (2 * Real.log 4 + 16))
    refine MeasureTheory.IntegrableOn.congr_fun h (fun s _ => ?_) measurableSet_Ioi
    simp only [neg_mul]
  refine hg.mono' ((continuous_kernelDeriv y).measurable.mul measurable_chebyshevStep).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun s hs => ?_
  have hs' : 0 < s := hs
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (chebyshevStep_nonneg s)]
  have h1 := hC s
  rw [abs_of_pos hs'] at h1
  have h2 := chebyshevStep_le hs'.le
  calc |kernelDeriv y s| * chebyshevStep s
      ≤ C * Real.exp (-((π - 1) * s)) * ((2 * Real.log 4 + 16) * Real.exp (s / 2)) :=
        mul_le_mul h1 h2 (chebyshevStep_nonneg s) (by positivity)
    _ = C * (2 * Real.log 4 + 16) * Real.exp (-((π - 3 / 2) * s)) := by
        rw [show C * Real.exp (-((π - 1) * s)) * ((2 * Real.log 4 + 16) * Real.exp (s / 2)) =
          C * (2 * Real.log 4 + 16) * (Real.exp (-((π - 1) * s)) * Real.exp (s / 2)) by ring,
          ← Real.exp_add]
        congr 2
        ring

/-- **Function form of the transport law.**  The prime wave is the pole wave, plus the bounded
origin terms `2K_y(0) − poleShadow y`, minus the space derivative of the kernel paired with the
`√`-weighted Chebyshev discrepancy `Δ(s) = Σ_{log n < s} Λ(n)/√n − 2e^{s/2}`. -/
theorem chmdPrimeWave_eq_pole_add_derivative_transport (y : ℝ) :
    chmdPrimeWave y = chmdPoleWave y + 2 * chmdPrimeKernel y 0 - poleShadow y -
      ∫ s in Ioi (0 : ℝ), kernelDeriv y s * chebyshevDiscrepancy s := by
  have hT := chmdPrimeWave_eq_chmdPoleWave_add_transport y
  have h1 := tsum_chmdPrimeWeight_mul_kernel_eq y
  have h2 := integral_Ioi_kernelDeriv_mul_two_exp_half y
  have hsplit : ∫ s in Ioi (0 : ℝ), kernelDeriv y s * chebyshevDiscrepancy s =
      (∫ s in Ioi (0 : ℝ), kernelDeriv y s * chebyshevStep s) -
        ∫ s in Ioi (0 : ℝ), kernelDeriv y s * (2 * Real.exp (s / 2)) := by
    rw [← integral_sub (integrableOn_kernelDeriv_mul_chebyshevStep y)
      (integrableOn_kernelDeriv_mul_two_exp_half y)]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    unfold chebyshevDiscrepancy
    ring
  unfold chebyshevDiscrepancyTransport at hT
  rw [hT, h1, hsplit, h2]
  ring

/-- The transported discrepancy measure equals the origin term minus the derivative pairing. -/
theorem chebyshevDiscrepancyTransport_eq (y : ℝ) :
    chebyshevDiscrepancyTransport y = 2 * chmdPrimeKernel y 0 -
      ∫ s in Ioi (0 : ℝ), kernelDeriv y s * chebyshevDiscrepancy s := by
  have h1 := chmdPrimeWave_eq_chmdPoleWave_add_transport y
  have h2 := chmdPrimeWave_eq_pole_add_derivative_transport y
  linarith

/-- **Riemann hypothesis through the derivative pairing with the Chebyshev discrepancy (upper form).** -/
theorem riemannHypothesis_iff_integral_kernelDeriv_mul_discrepancy_bddAbove :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ y : ℝ, 0 ≤ y →
      (∫ s in Ioi (0 : ℝ), kernelDeriv y s * chebyshevDiscrepancy s) ≤ M := by
  rw [riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddBelow]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M + 8 / π, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_chmdPrimeKernel_le y 0
    have h3 := chebyshevDiscrepancyTransport_eq y
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    have h8 : (8 : ℝ) / π = 2 * (4 / π) := by ring
    linarith
  · rintro ⟨M, hM⟩
    refine ⟨M + 8 / π, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_chmdPrimeKernel_le y 0
    have h3 := chebyshevDiscrepancyTransport_eq y
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    have h8 : (8 : ℝ) / π = 2 * (4 / π) := by ring
    linarith

/-- **Riemann hypothesis through the derivative pairing with the Chebyshev discrepancy (lower form).** -/
theorem riemannHypothesis_iff_integral_kernelDeriv_mul_discrepancy_bddBelow :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ y : ℝ, 0 ≤ y →
      -M ≤ ∫ s in Ioi (0 : ℝ), kernelDeriv y s * chebyshevDiscrepancy s := by
  rw [riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddAbove]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M + 8 / π, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_chmdPrimeKernel_le y 0
    have h3 := chebyshevDiscrepancyTransport_eq y
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    have h8 : (8 : ℝ) / π = 2 * (4 / π) := by ring
    linarith
  · rintro ⟨M, hM⟩
    refine ⟨M + 8 / π, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_chmdPrimeKernel_le y 0
    have h3 := chebyshevDiscrepancyTransport_eq y
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    have h8 : (8 : ℝ) / π = 2 * (4 / π) := by ring
    linarith

end

end RHTower.CHMDChebyshevTransport

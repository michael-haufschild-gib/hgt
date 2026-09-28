import GaloisForLFunctions.RHTower.ThetaRenewalResonanceDivisor
import GaloisForLFunctions.HTGeometry.LogDerivativeResidue
import GaloisForLFunctions.HTGeometry.BernsteinWidder
import GaloisForLFunctions.RHTower.ThetaHalfPortStieltjesSpectral

/-!
# The theta phase kernel is not completely monotone

Let `W(t) = e^{-t/4}/t + Q(t) > 0` be the odd phase kernel of the renewal factorization and
`D = c - N` the renewal denominator.

* **(6), (7).** `Q̂'(z) = -∫ t e^{-zt} Q(t) dt` on `Re z > -1/4`, and differentiating
  `D = c e^{-Q̂}` gives `∫ t e^{-zt} Q = D'/D`.  Hence the regularized transform
  `J(z) = ∫₀^∞ t e^{-zt} W(t) dt = 1/(z + 1/4) - N'(z)/(c - N(z))`, which continues
  meromorphically with a genuine pole of residue `m` at every renewal root of multiplicity `m`.
* **(8).** Suppose `W(t + ε) = ∫ e^{-st} ψ(s) dρ(s)` for all `t > 0`, with `ρ` finite on
  `[0, ∞)` and `ψ` bounded.  Then `∫₀^∞ (t + ε) e^{-zt} W(t + ε) dt` equals
  `G(z) = ∫ ψ(s) ((z + s)⁻² + ε (z + s)⁻¹) dρ(s)`, holomorphic on the slit plane, and also
  `e^{zε} (J(z) - E_ε(z))` with an entire head `E_ε`.  The identity theorem transports
  `D (e^{-zε} G + E_ε - 1/(z + 1/4)) = D'` from the positive axis to the slit plane, where at a
  nonreal renewal root it contradicts the residue of `D'/D`.
* Consequently `W` is not completely monotone (via the Bernstein–Widder representation of the
  shifted kernel), is not a Laplace transform of a positive measure on `[0, ∞)`, and is not the
  transform of any signed or complex measure of finite weighted variation `∫ (z₀ + s)⁻² d|μ|`.
-/

open Complex Filter Topology Set MeasureTheory HurwitzZeta

namespace RHTower

noncomputable section

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## The first moment of the renewal log kernel -/

theorem norm_cexp_neg_mul_le {z : ℂ} {b : ℝ} (hb : -b ≤ z.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖cexp (-(z * t))‖ ≤ Real.exp (b * t) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  nlinarith

/-- `Q̂'(z) = -∫₀^∞ t e^{-zt} Q(t) dt` on `Re z > -1/4`. -/
theorem hasDerivAt_thetaRenewalLogKernelLaplace {z : ℂ} (hz : -(1 / 4) < z.re) :
    HasDerivAt thetaRenewalLogKernelLaplace
      (-∫ t in Ioi (0 : ℝ), (t : ℂ) * cexp (-(z * t)) * (thetaRenewalLogKernel t : ℂ)) z := by
  set δ := (z.re + 1 / 4) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set b := -z.re + δ with hb
  have hb4 : b < 1 / 4 := by rw [hb, hδ]; linarith
  have hQc := continuous_thetaRenewalLogKernel
  have hball : ∀ w ∈ Metric.ball z δ, -b ≤ w.re := by
    intro w hw
    have h1 : |w.re - z.re| < δ := by
      have := Complex.abs_re_le_norm (w - z)
      rw [Complex.sub_re] at this
      exact lt_of_le_of_lt this (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw)
    rw [abs_lt] at h1
    rw [hb]; linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun w (t : ℝ) => cexp (-(w * t)) * (thetaRenewalLogKernel t : ℂ))
    (F' := fun w (t : ℝ) => -((t : ℂ) * cexp (-(w * t)) * (thetaRenewalLogKernel t : ℂ)))
    (bound := fun t => t * Real.exp (b * t) * thetaRenewalLogKernel t) (x₀ := z)
    (Metric.ball_mem_nhds z hδ0)
    (Eventually.of_forall fun w => ((by fun_prop : Continuous fun t : ℝ =>
      cexp (-(w * t)) * (thetaRenewalLogKernel t : ℂ))).aestronglyMeasurable.restrict)
    (by
      refine integrableOn_exp_mul_thetaRenewalLogKernel.mono' ((by fun_prop : Continuous
        fun t : ℝ => cexp (-(z * t)) * (thetaRenewalLogKernel t : ℂ))).aestronglyMeasurable.restrict
        ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht0 : (0 : ℝ) < t := ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (thetaRenewalLogKernel_pos ht0)]
      refine mul_le_mul_of_nonneg_right ?_ (thetaRenewalLogKernel_pos ht0).le
      have := norm_cexp_neg_mul_le (b := 1 / 4) (z := z) (by linarith) ht0.le
      rwa [show 1 / 4 * t = t / 4 by ring] at this)
    ((by fun_prop : Continuous fun t : ℝ =>
      -((t : ℂ) * cexp (-(z * t)) * (thetaRenewalLogKernel t : ℂ))).aestronglyMeasurable.restrict)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht w hw => by
      have ht0 : (0 : ℝ) < t := ht
      rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos ht0, abs_of_pos (thetaRenewalLogKernel_pos ht0)]
      have := norm_cexp_neg_mul_le (hball w hw) ht0.le
      have hQ := (thetaRenewalLogKernel_pos ht0).le
      calc t * ‖cexp (-(w * t))‖ * thetaRenewalLogKernel t ≤
            t * Real.exp (b * t) * thetaRenewalLogKernel t := by gcongr))
    (integrableOn_mul_exp_mul_thetaRenewalLogKernel hb4)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ w _ => by
      have h := (((hasDerivAt_id w).mul_const (t : ℂ)).neg.cexp).mul_const
        (thetaRenewalLogKernel t : ℂ)
      simp only [Pi.neg_apply, id] at h
      exact h.congr_deriv (by ring)))
  have h := key.2
  rw [integral_neg] at h
  exact h

/-- **(6), first moment.** `∫₀^∞ t e^{-zt} Q(t) dt = -Q̂'(z) = D'(z)/D(z)` on `Re z > -1/4`. -/
theorem integral_mul_cexp_thetaRenewalLogKernel_eq_logDeriv {z : ℂ} (hz : -(1 / 4) < z.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) * cexp (-(z * t)) * (thetaRenewalLogKernel t : ℂ) =
      logDeriv thetaRenewalDenominator z := by
  have hQ := hasDerivAt_thetaRenewalLogKernelLaplace hz
  have hopen : IsOpen {w : ℂ | -(1 / 4) < w.re} := isOpen_lt continuous_const continuous_re
  have heq : thetaRenewalDenominator =ᶠ[𝓝 z]
      fun w => ((Θ 1 : ℝ) : ℂ) * cexp (-thetaRenewalLogKernelLaplace w) := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact thetaRenewalDenominator_eq_exp (le_of_lt hw)
  have hd : HasDerivAt (fun w => ((Θ 1 : ℝ) : ℂ) * cexp (-thetaRenewalLogKernelLaplace w))
      (((Θ 1 : ℝ) : ℂ) * (cexp (-thetaRenewalLogKernelLaplace z) *
        -(-∫ t in Ioi (0 : ℝ), (t : ℂ) * cexp (-(z * t)) * (thetaRenewalLogKernel t : ℂ)))) z :=
    (hQ.neg.cexp).const_mul _
  have hDz : thetaRenewalDenominator z ≠ 0 := thetaRenewalDenominator_ne_zero hz.le
  set I := ∫ t in Ioi (0 : ℝ), (t : ℂ) * cexp (-(z * t)) * (thetaRenewalLogKernel t : ℂ)
  rw [logDeriv_apply, heq.deriv_eq, hd.deriv, heq.eq_of_nhds]
  have hc : ((Θ 1 : ℝ) : ℂ) * cexp (-thetaRenewalLogKernelLaplace z) ≠ 0 := by
    rw [← thetaRenewalDenominator_eq_exp hz.le]; exact hDz
  rw [neg_neg, show ((Θ 1 : ℝ) : ℂ) * (cexp (-thetaRenewalLogKernelLaplace z) * I) =
    I * (((Θ 1 : ℝ) : ℂ) * cexp (-thetaRenewalLogKernelLaplace z)) by ring, mul_div_assoc,
    div_self hc, mul_one]

/-! ## The regularized phase transform `J` (7) -/

/-- The regularized phase transform `J(z) = ∫₀^∞ t e^{-zt} W(t) dt`. -/
def thetaRenewalPhaseTransform (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (t : ℂ) * cexp (-(z * t)) * (thetaRenewalOddKernel t : ℂ)

theorem integrableOn_mul_cexp_thetaRenewalLogKernel {z : ℂ} (hz : -(1 / 4) < z.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * cexp (-(z * t)) * (thetaRenewalLogKernel t : ℂ))
      (Ioi 0) := by
  have hQc := continuous_thetaRenewalLogKernel
  refine (integrableOn_mul_exp_mul_thetaRenewalLogKernel (b := -z.re) (by linarith)).mono'
    (by fun_prop) ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos ht0, abs_of_pos (thetaRenewalLogKernel_pos ht0)]
  have := norm_cexp_neg_mul_le (b := -z.re) (z := z) (by linarith) ht0.le
  have hQ := (thetaRenewalLogKernel_pos ht0).le
  gcongr

/-- **(7).** `J(z) = 1/(z + a) - N'(z)/(c - N(z)) = 1/(z + a) + D'(z)/D(z)` on `Re z > -1/4`. -/
theorem thetaRenewalPhaseTransform_eq {z : ℂ} (hz : -(1 / 4) < z.re) :
    thetaRenewalPhaseTransform z = 1 / (z + 1 / 4) + logDeriv thetaRenewalDenominator z := by
  have hz4 : (-(z + 1 / 4)).re < 0 := by simp; linarith
  have h1 : IntegrableOn (fun t : ℝ => cexp (-(z + 1 / 4) * t)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hz4 0
  have h2 := integrableOn_mul_cexp_thetaRenewalLogKernel hz
  have hsplit : thetaRenewalPhaseTransform z = ∫ t in Ioi (0 : ℝ), (cexp (-(z + 1 / 4) * t) +
      (t : ℂ) * cexp (-(z * t)) * (thetaRenewalLogKernel t : ℂ)) := by
    rw [thetaRenewalPhaseTransform]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (mem_Ioi.mp ht).ne'
    rw [thetaRenewalOddKernel]
    push_cast
    rw [show -(z + 1 / 4) * (t : ℂ) = -(z * t) + -((t : ℂ) / 4) by ring, Complex.exp_add]
    field_simp
  have hz0 : z + 1 / 4 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  rw [hsplit, integral_add h1 h2, integral_exp_mul_complex_Ioi hz4,
    integral_mul_cexp_thetaRenewalLogKernel_eq_logDeriv hz]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

theorem logDeriv_thetaRenewalDenominator_eq_laplace (z : ℂ) :
    logDeriv thetaRenewalDenominator z =
      -deriv thetaRenewalLaplace z / (((Θ 1 : ℝ) : ℂ) - thetaRenewalLaplace z) := by
  have h : thetaRenewalDenominator = fun w => ((Θ 1 : ℝ) : ℂ) - thetaRenewalLaplace w := by
    funext w; rw [thetaRenewalDenominator]
  rw [logDeriv_apply, h, deriv_const_sub]

/-- **(7), meromorphic continuation with a genuine pole at every renewal root.** At a zero `ζ`
of `D` of multiplicity `m ≥ 1`, `(z - ζ) (1/(z + a) + D'(z)/D(z)) → m`. -/
theorem tendsto_mul_thetaRenewalPhaseContinuation {ζ : ℂ} (hζ : thetaRenewalDenominator ζ = 0) :
    ∃ m : ℕ, 1 ≤ m ∧ analyticOrderAt thetaRenewalDenominator ζ = m ∧
      Tendsto (fun z => (z - ζ) * (1 / (z + 1 / 4) + logDeriv thetaRenewalDenominator z))
        (𝓝[≠] ζ) (𝓝 (m : ℂ)) := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_thetaRenewalDenominator_ne_top ζ)
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exfalso
      have : analyticOrderAt thetaRenewalDenominator ζ = 0 := by rw [← hm, h0]; rfl
      exact ((analyticOnNhd_thetaRenewalDenominator ζ (mem_univ ζ)).analyticOrderAt_eq_zero.mp
        this) hζ
    · exact hpos
  refine ⟨m, hm1, hm.symm, ?_⟩
  have hres := GaloisForLFunctions.HTGeometry.tendsto_sub_mul_logDeriv_of_analyticOrderAt
    (analyticOnNhd_thetaRenewalDenominator ζ (mem_univ ζ)) hm.symm
  have hζ4 : ζ + 1 / 4 ≠ 0 := by
    intro h
    have := re_lt_of_thetaRenewalDenominator_eq_zero hζ
    have h2 := congrArg Complex.re h
    simp at h2; linarith
  have hpole : Tendsto (fun z => (z - ζ) * (1 / (z + 1 / 4))) (𝓝[≠] ζ) (𝓝 0) := by
    have hc : ContinuousAt (fun z => (z - ζ) * (1 / (z + 1 / 4))) ζ :=
      (continuousAt_id.sub continuousAt_const).mul (continuousAt_const.div
        (continuousAt_id.add continuousAt_const) hζ4)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {ζ}ᶜ))
    simpa using this
  have := hpole.add hres
  simp only [zero_add] at this
  refine this.congr fun z => ?_
  ring

/-! ## No real-rate Laplace representation (8) -/

/-- `V(t) = t W(t) = e^{-t/4} + t Q(t)`, continuous on the line. -/
def thetaRenewalPhaseWeight (t : ℝ) : ℝ := Real.exp (-(t / 4)) + t * thetaRenewalLogKernel t

theorem continuous_thetaRenewalPhaseWeight : Continuous thetaRenewalPhaseWeight := by
  have := continuous_thetaRenewalLogKernel
  unfold thetaRenewalPhaseWeight; fun_prop

theorem mul_thetaRenewalOddKernel {t : ℝ} (ht : 0 < t) :
    t * thetaRenewalOddKernel t = thetaRenewalPhaseWeight t := by
  rw [thetaRenewalOddKernel, thetaRenewalPhaseWeight]
  field_simp

/-- The head `E_ε(z) = ∫₀^ε t e^{-zt} W(t) dt`. -/
def thetaRenewalPhaseHead (ε : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioc 0 ε, cexp (-(z * t)) * (thetaRenewalPhaseWeight t : ℂ)

/-- The head is entire. -/
theorem differentiable_thetaRenewalPhaseHead {ε : ℝ} (hε : 0 < ε) :
    Differentiable ℂ (thetaRenewalPhaseHead ε) := by
  intro z
  obtain ⟨V, hV⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := ε)).exists_bound_of_continuousOn
    continuous_thetaRenewalPhaseWeight.continuousOn
  set K := Real.exp ((|z.re| + 1) * ε)
  have hVc := continuous_thetaRenewalPhaseWeight
  have hbd : ∀ w ∈ Metric.ball z 1, ∀ t ∈ Ioc 0 ε, ‖cexp (-(w * t))‖ ≤ K := by
    intro w hw t ht
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have h1 : |w.re - z.re| < 1 := by
      have := Complex.abs_re_le_norm (w - z)
      rw [Complex.sub_re] at this
      exact lt_of_le_of_lt this (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw)
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    rw [abs_lt] at h1
    have ht0 := ht.1
    have hte := ht.2
    have habs := neg_abs_le z.re
    nlinarith [abs_nonneg z.re]
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) ε)) := by
    rw [isFiniteMeasure_restrict]; simp
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (0 : ℝ) ε))
    (F := fun w (t : ℝ) => cexp (-(w * t)) * (thetaRenewalPhaseWeight t : ℂ))
    (F' := fun w (t : ℝ) => -((t : ℂ) * cexp (-(w * t)) * (thetaRenewalPhaseWeight t : ℂ)))
    (bound := fun _ => ε * K * V) (x₀ := z) (Metric.ball_mem_nhds z one_pos)
    (Eventually.of_forall fun w => ((by fun_prop : Continuous fun t : ℝ =>
      cexp (-(w * t)) * (thetaRenewalPhaseWeight t : ℂ))).aestronglyMeasurable.restrict)
    ((by fun_prop : Continuous fun t : ℝ =>
      cexp (-(z * t)) * (thetaRenewalPhaseWeight t : ℂ)).integrableOn_Ioc)
    ((by fun_prop : Continuous fun t : ℝ =>
      -((t : ℂ) * cexp (-(z * t)) * (thetaRenewalPhaseWeight t : ℂ))).aestronglyMeasurable.restrict)
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht w hw => by
      rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht.1]
      have h1 := hbd w hw t ht
      have h2 := hV t ⟨ht.1.le, ht.2⟩
      rw [Real.norm_eq_abs] at h2
      have hK : 0 ≤ K := (Real.exp_pos _).le
      calc t * ‖cexp (-(w * t))‖ * |thetaRenewalPhaseWeight t| ≤ ε * K * V := by
            gcongr
            exact ht.2))
    (integrableOn_const (by simp))
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t _ w _ => by
      have h := (((hasDerivAt_id w).mul_const (t : ℂ)).neg.cexp).mul_const
        (thetaRenewalPhaseWeight t : ℂ)
      simp only [Pi.neg_apply, id] at h
      exact h.congr_deriv (by ring)))
  exact key.2.differentiableAt

/-- The Stieltjes pair transform `G(z) = ∫ ψ(s) ((z + s)⁻² + ε (z + s)⁻¹) dρ(s)`. -/
def stieltjesPairTransform (ρ : Measure ℝ) (ψ : ℝ → ℂ) (ε : ℝ) (z : ℂ) : ℂ :=
  ∫ s, ψ s * (((z + s) ^ 2)⁻¹ + ε * (z + s)⁻¹) ∂ρ

theorem ae_nonneg_of_measure_Iio {ρ : Measure ℝ} (hρ : ρ (Iio 0) = 0) : ∀ᵐ s ∂ρ, 0 ≤ s := by
  rw [ae_iff]
  have : {a : ℝ | ¬0 ≤ a} = Iio 0 := by ext; simp
  rw [this]; exact hρ

/-- A slit-plane point stays uniformly away from `-[0, ∞)` on a small ball. -/
theorem exists_ball_norm_add_ge {z₁ : ℂ} (hz₁ : z₁ ∈ slitPlane) :
    ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Metric.ball z₁ c, ∀ s : ℝ, 0 ≤ s → c ≤ ‖w + s‖ := by
  obtain ⟨c, hc, hle⟩ := GaloisForLFunctions.HTGeometry.exists_mul_one_add_le_norm_sub
    (ζ := -z₁) (by rwa [neg_neg])
  refine ⟨c / 2, by positivity, fun w hw s hs => ?_⟩
  have h1 := hle s hs
  rw [sub_neg_eq_add] at h1
  have h2 : ‖w - z₁‖ < c / 2 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw
  have h3 : ‖(s : ℂ) + z₁‖ ≤ ‖w + s‖ + ‖w - z₁‖ := by
    calc ‖(s : ℂ) + z₁‖ = ‖(w + s) - (w - z₁)‖ := by ring_nf
      _ ≤ ‖w + s‖ + ‖w - z₁‖ := norm_sub_le _ _
  nlinarith

theorem differentiableOn_stieltjesPairTransform {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ : ρ (Iio 0) = 0) {ψ : ℝ → ℂ} (hψm : Measurable ψ) {M : ℝ} (hψ : ∀ s, ‖ψ s‖ ≤ M)
    (ε : ℝ) : DifferentiableOn ℂ (stieltjesPairTransform ρ ψ ε) slitPlane := by
  intro z₁ hz₁
  obtain ⟨c, hc, hball⟩ := exists_ball_norm_add_ge hz₁
  have hM : 0 ≤ M := (norm_nonneg _).trans (hψ 0)
  have hpos := ae_nonneg_of_measure_Iio hρ
  have hne : ∀ w ∈ Metric.ball z₁ c, ∀ s : ℝ, 0 ≤ s → w + s ≠ 0 := fun w hw s hs h => by
    have := hball w hw s hs; rw [h, norm_zero] at this; linarith
  have hinv : ∀ w ∈ Metric.ball z₁ c, ∀ s : ℝ, 0 ≤ s → ‖(w + s)⁻¹‖ ≤ c⁻¹ := fun w hw s hs => by
    rw [norm_inv]; exact inv_anti₀ hc (hball w hw s hs)
  have hmeasF : ∀ w : ℂ, Measurable fun s : ℝ => ψ s * (((w + s) ^ 2)⁻¹ + ε * (w + s)⁻¹) :=
    fun w => hψm.mul (((by fun_prop : Continuous fun s : ℝ => (w + s) ^ 2).measurable.inv).add
      (measurable_const.mul (by fun_prop : Continuous fun s : ℝ => w + (s : ℂ)).measurable.inv))
  have hmeasF' : ∀ w : ℂ, Measurable fun s : ℝ =>
      ψ s * (-2 * ((w + s) ^ 3)⁻¹ - ε * ((w + s) ^ 2)⁻¹) :=
    fun w => hψm.mul ((measurable_const.mul
      (by fun_prop : Continuous fun s : ℝ => (w + s) ^ 3).measurable.inv).sub
      (measurable_const.mul (by fun_prop : Continuous fun s : ℝ => (w + s) ^ 2).measurable.inv))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ρ)
    (F := fun (w : ℂ) (s : ℝ) => ψ s * (((w + s) ^ 2)⁻¹ + ε * (w + s)⁻¹))
    (F' := fun (w : ℂ) (s : ℝ) => ψ s * (-2 * ((w + s) ^ 3)⁻¹ - ε * ((w + s) ^ 2)⁻¹))
    (bound := fun _ => M * (2 * c⁻¹ ^ 3 + |ε| * c⁻¹ ^ 2)) (x₀ := z₁)
    (Metric.ball_mem_nhds z₁ hc)
    (Eventually.of_forall fun w => (hmeasF w).aestronglyMeasurable)
    (by
      refine (integrable_const (M * (c⁻¹ ^ 2 + |ε| * c⁻¹))).mono'
        (hmeasF z₁).aestronglyMeasurable ?_
      filter_upwards [hpos] with s hs
      have h1 := hinv z₁ (Metric.mem_ball_self hc) s hs
      rw [norm_mul]
      refine mul_le_mul (hψ s) ?_ (norm_nonneg _) hM
      calc ‖((z₁ + s) ^ 2)⁻¹ + ε * (z₁ + s)⁻¹‖ ≤ ‖((z₁ + s) ^ 2)⁻¹‖ + ‖(ε : ℂ) * (z₁ + s)⁻¹‖ :=
            norm_add_le _ _
        _ = ‖(z₁ + s)⁻¹‖ ^ 2 + |ε| * ‖(z₁ + s)⁻¹‖ := by
            rw [← inv_pow, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ c⁻¹ ^ 2 + |ε| * c⁻¹ := by gcongr)
    ((hmeasF' z₁).aestronglyMeasurable)
    (by
      filter_upwards [hpos] with s hs w hw
      have h1 := hinv w hw s hs
      rw [norm_mul]
      refine mul_le_mul (hψ s) ?_ (norm_nonneg _) hM
      calc ‖-2 * ((w + s) ^ 3)⁻¹ - ε * ((w + s) ^ 2)⁻¹‖
          ≤ ‖(-2 : ℂ) * ((w + s) ^ 3)⁻¹‖ + ‖(ε : ℂ) * ((w + s) ^ 2)⁻¹‖ := norm_sub_le _ _
        _ = 2 * ‖(w + s)⁻¹‖ ^ 3 + |ε| * ‖(w + s)⁻¹‖ ^ 2 := by
            rw [norm_mul, norm_mul, ← inv_pow, ← inv_pow, norm_pow, norm_pow, Complex.norm_real,
              Real.norm_eq_abs, norm_neg, Complex.norm_ofNat]
        _ ≤ 2 * c⁻¹ ^ 3 + |ε| * c⁻¹ ^ 2 := by gcongr)
    (integrable_const _)
    (by
      filter_upwards [hpos] with s hs w hw
      have h0 := hne w hw s hs
      have h2 : HasDerivAt (fun w : ℂ => ((w + s) ^ 2)⁻¹) (-2 * ((w + s) ^ 3)⁻¹) w := by
        have hsq : HasDerivAt (fun w : ℂ => (w + s) ^ 2) (2 * (w + s)) w := by
          have := (hasDerivAt_pow 2 (w + s)).comp w ((hasDerivAt_id w).add_const (s : ℂ))
          simpa [Function.comp_def] using this
        have h := hsq.inv (pow_ne_zero 2 h0)
        refine h.congr_deriv ?_
        field_simp
      have h3 : HasDerivAt (fun w : ℂ => (w + s)⁻¹) (-((w + s) ^ 2)⁻¹) w := by
        have h := ((hasDerivAt_id w).add_const (s : ℂ)).inv h0
        refine h.congr_deriv ?_
        simp only [id]
        field_simp
      have h := (h2.add (h3.const_mul (ε : ℂ))).const_mul (ψ s)
      refine h.congr_deriv ?_
      ring)
  exact key.2.differentiableAt.differentiableWithinAt

theorem integral_add_mul_exp_neg {a ε : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), (t + ε) * Real.exp (-(a * t)) = 1 / a ^ 2 + ε / a := by
  have h1 : IntegrableOn (fun t : ℝ => t * Real.exp (-(a * t))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := a) (by norm_num)
      le_rfl ha
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp [Real.rpow_one]
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-(a * t))) (Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0
    refine this.congr_fun (fun t _ => by ring_nf) measurableSet_Ioi
  have hG : ∫ t in Ioi (0 : ℝ), t * Real.exp (-(a * t)) = 1 / a ^ 2 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := a) (by norm_num) ha
    norm_num [Real.Gamma_two] at h
    rw [h, one_div]
  have hE : ∫ t in Ioi (0 : ℝ), Real.exp (-(a * t)) = 1 / a := by
    have h := integral_exp_mul_Ioi (a := -a) (by linarith) 0
    simp only [mul_zero, Real.exp_zero] at h
    rw [show (fun t : ℝ => Real.exp (-(a * t))) = fun t => Real.exp (-a * t) by
      funext t; ring_nf, h]
    field_simp
  rw [show (fun t : ℝ => (t + ε) * Real.exp (-(a * t))) =
    fun t => t * Real.exp (-(a * t)) + ε * Real.exp (-(a * t)) by funext t; ring,
    integral_add h1 (h2.const_mul ε), integral_const_mul, hG, hE]
  ring

/-- **Fubini.** For real `x > 0`,
`G(x) = ∫₀^∞ (t + ε) e^{-xt} (∫ e^{-st} ψ(s) dρ(s)) dt`. -/
theorem stieltjesPairTransform_ofReal_eq {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ : ρ (Iio 0) = 0) {ψ : ℝ → ℂ} (hψm : Measurable ψ) {M : ℝ} (hψ : ∀ s, ‖ψ s‖ ≤ M)
    {ε : ℝ} (hε : 0 ≤ ε) {x : ℝ} (hx : 0 < x) :
    stieltjesPairTransform ρ ψ ε x = ∫ t in Ioi (0 : ℝ),
      (((t + ε) * Real.exp (-(x * t)) : ℝ) : ℂ) * ∫ s, cexp (-(s * t)) * ψ s ∂ρ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hψ 0)
  set f : ℝ × ℝ → ℂ := fun p =>
    (((p.1 + ε) * Real.exp (-(x * p.1)) * Real.exp (-(p.2 * p.1)) : ℝ) : ℂ) * ψ p.2 with hf
  have hfm : Measurable f := by simp only [hf]; fun_prop
  have hnull : ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod ρ), 0 ≤ p.2 := by
    rw [ae_iff]
    have : {p : ℝ × ℝ | ¬0 ≤ p.2} = univ ×ˢ Iio 0 := by ext p; simp
    rw [this, Measure.prod_prod, hρ, mul_zero]
  have hdom : Integrable (fun p : ℝ × ℝ => (M * ((p.1 + ε) * Real.exp (-(x * p.1)))) * (1 : ℝ))
      ((volume.restrict (Ioi (0 : ℝ))).prod ρ) := by
    have h1 : Integrable (fun t : ℝ => M * ((t + ε) * Real.exp (-(x * t))))
        (volume.restrict (Ioi (0 : ℝ))) := by
      refine Integrable.const_mul ?_ M
      have hi : IntegrableOn (fun t : ℝ => (t + ε) * Real.exp (-(x * t))) (Ioi 0) := by
        by_contra hni
        have := integral_undef hni
        rw [integral_add_mul_exp_neg hx] at this
        have : 0 < 1 / x ^ 2 + ε / x := by positivity
        linarith
      exact hi
    exact h1.mul_prod (integrable_const (1 : ℝ))
  have hnull1 : ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod ρ), 0 < p.1 := by
    rw [ae_iff]
    have : {p : ℝ × ℝ | ¬0 < p.1} = Iic 0 ×ˢ univ := by ext p; simp
    rw [this, Measure.prod_prod, Measure.restrict_apply measurableSet_Iic,
      Iic_inter_Ioi, Ioc_self, measure_empty, zero_mul]
  have hint : Integrable f ((volume.restrict (Ioi (0 : ℝ))).prod ρ) := by
    refine hdom.mono' hfm.aestronglyMeasurable ?_
    filter_upwards [hnull, hnull1] with p hp hp1
    simp only [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_one]
    rw [abs_of_nonneg (by linarith : 0 ≤ p.1 + ε), abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-(p.2 * p.1)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hψp := hψ p.2
    calc (p.1 + ε) * Real.exp (-(x * p.1)) * Real.exp (-(p.2 * p.1)) * ‖ψ p.2‖
        ≤ (p.1 + ε) * Real.exp (-(x * p.1)) * 1 * M := by gcongr
      _ = M * ((p.1 + ε) * Real.exp (-(x * p.1))) := by ring
  have hswap := integral_integral_swap (f := fun t s => f (t, s)) hint
  have hleft : ∫ t in Ioi (0 : ℝ), (((t + ε) * Real.exp (-(x * t)) : ℝ) : ℂ) *
      ∫ s, cexp (-(s * t)) * ψ s ∂ρ = ∫ t in Ioi (0 : ℝ), ∫ s, f (t, s) ∂ρ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [hf]
    rw [show cexp (-((s : ℂ) * t)) = ((Real.exp (-(s * t)) : ℝ) : ℂ) by push_cast; ring_nf]
    push_cast; ring
  have hright : stieltjesPairTransform ρ ψ ε x = ∫ s, (∫ t in Ioi (0 : ℝ), f (t, s)) ∂ρ := by
    rw [stieltjesPairTransform]
    refine integral_congr_ae ?_
    filter_upwards [ae_nonneg_of_measure_Iio hρ] with s hs
    have hxs : 0 < x + s := by linarith
    have hin : ∫ t in Ioi (0 : ℝ), f (t, s) =
        ψ s * (((∫ t in Ioi (0 : ℝ), (t + ε) * Real.exp (-((x + s) * t)) : ℝ)) : ℂ) := by
      rw [← integral_complex_ofReal, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [hf]
      rw [show -((x + s) * t) = -(x * t) + -(s * t) by ring, Real.exp_add]
      push_cast; ring
    rw [hin, integral_add_mul_exp_neg hxs]
    have hxs' : (x : ℂ) + s ≠ 0 := by exact_mod_cast hxs.ne'
    push_cast
    field_simp
  rw [hleft, hswap, hright]

theorem integrableOn_thetaRenewalPhaseIntegrand {z : ℂ} (hz : -(1 / 4) < z.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * cexp (-(z * t)) * (thetaRenewalOddKernel t : ℂ))
      (Ioi 0) := by
  have hz4 : (-(z + 1 / 4)).re < 0 := by simp; linarith
  have h := (integrableOn_exp_mul_complex_Ioi hz4 0).add
    (integrableOn_mul_cexp_thetaRenewalLogKernel hz)
  refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (mem_Ioi.mp ht).ne'
  simp only [Pi.add_apply]
  rw [thetaRenewalOddKernel]
  push_cast
  rw [show -(z + 1 / 4) * (t : ℂ) = -(z * t) + -((t : ℂ) / 4) by ring, Complex.exp_add]
  field_simp

/-- **The shifted kernel.** For real `x > 0` and `ε > 0`,
`∫₀^∞ (t + ε) e^{-xt} W(t + ε) dt = e^{xε} (J(x) - E_ε(x))`. -/
theorem integral_shift_thetaRenewalOddKernel {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), (((t + ε) * Real.exp (-(x * t)) : ℝ) : ℂ) *
        (thetaRenewalOddKernel (t + ε) : ℂ) =
      cexp (x * ε) * (thetaRenewalPhaseTransform x - thetaRenewalPhaseHead ε x) := by
  set g : ℝ → ℂ := fun u => (u : ℂ) * cexp (-((x : ℂ) * u)) * (thetaRenewalOddKernel u : ℂ)
  have hg : IntegrableOn g (Ioi 0) :=
    integrableOn_thetaRenewalPhaseIntegrand (z := (x : ℂ)) (by simp; linarith)
  have hcomp : ∫ t in Ioi (0 : ℝ), (((t + ε) * Real.exp (-(x * t)) : ℝ) : ℂ) *
      (thetaRenewalOddKernel (t + ε) : ℂ) = cexp (x * ε) * ∫ t in Ioi (0 : ℝ), g (ε + t) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [g]
    rw [add_comm ε t]
    push_cast
    rw [show -((x : ℂ) * (t + ε)) = -(x * t) + -(x * ε) by ring, Complex.exp_add]
    have : cexp (x * ε) * cexp (-(x * ε)) = 1 := by
      rw [← Complex.exp_add]; simp
    linear_combination (-(((t : ℂ) + ε) * cexp (-(x * t)) *
      (thetaRenewalOddKernel (t + ε) : ℂ))) * this
  have hsplit := intervalIntegral.integral_interval_add_Ioi (a := 0) (b := ε) hg
    (hg.mono_set (Ioi_subset_Ioi hε.le))
  rw [intervalIntegral.integral_of_le hε.le] at hsplit
  have hJ : ∫ u in Ioi (0 : ℝ), g u = thetaRenewalPhaseTransform x := rfl
  have hE : ∫ u in Ioc 0 ε, g u = thetaRenewalPhaseHead ε x := by
    rw [thetaRenewalPhaseHead]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    simp only [g]
    rw [← mul_thetaRenewalOddKernel hu.1]
    push_cast; ring
  rw [hcomp, integral_Ioi_comp_add g ε, ← hJ, ← hE, ← hsplit]
  ring

/-- **No shifted real-rate representation.** For no `ε > 0`, finite measure `ρ` on `[0, ∞)` and
bounded measurable `ψ` does `W(t + ε) = ∫ e^{-st} ψ(s) dρ(s)` hold for all `t > 0`.  Such a
representation would continue `(t + ε)`-weighted transforms of `W` holomorphically to the slit
plane, while `J = 1/(z + a) + D'/D` has a genuine pole at every nonreal renewal root. -/
theorem not_forall_shifted_laplace_thetaRenewalOddKernel {ε : ℝ} (hε : 0 < ε)
    {ρ : Measure ℝ} [IsFiniteMeasure ρ] (hρ : ρ (Iio 0) = 0) {ψ : ℝ → ℂ} (hψm : Measurable ψ)
    {M : ℝ} (hψ : ∀ s, ‖ψ s‖ ≤ M) :
    ¬ ∀ t : ℝ, 0 < t →
      (thetaRenewalOddKernel (t + ε) : ℂ) = ∫ s, cexp (-(s * t)) * ψ s ∂ρ := by
  intro hrep
  set h : ℂ → ℂ := fun z => cexp (-(z * ε)) * stieltjesPairTransform ρ ψ ε z +
    thetaRenewalPhaseHead ε z - 1 / (z + 1 / 4) with hhdef
  set F : ℂ → ℂ := fun z => thetaRenewalDenominator z * h z - deriv thetaRenewalDenominator z
    with hFdef
  have hGd := differentiableOn_stieltjesPairTransform hρ hψm hψ ε
  have hEd := differentiable_thetaRenewalPhaseHead hε
  have hD'd : Differentiable ℂ (deriv thetaRenewalDenominator) := fun z =>
    (analyticOnNhd_thetaRenewalDenominator.deriv z (mem_univ z)).differentiableAt
  have hq : ∀ z ∈ slitPlane, z + 1 / 4 ≠ 0 := by
    intro z hz h0
    have hz' : z = -(1 / 4) := by linear_combination h0
    rw [hz', mem_slitPlane_iff] at hz
    norm_num at hz
  have hhd : DifferentiableOn ℂ h slitPlane := by
    intro z hz
    have hG := hGd.differentiableAt (isOpen_slitPlane.mem_nhds hz)
    have h1 : DifferentiableAt ℂ (fun w : ℂ => cexp (-(w * ε))) z := by fun_prop
    have h2 : DifferentiableAt ℂ (fun w : ℂ => 1 / (w + 1 / 4)) z :=
      (differentiableAt_const _).div (differentiableAt_id.add_const _) (hq z hz)
    exact ((h1.mul hG).add (hEd z)).sub h2 |>.differentiableWithinAt
  have hFd : DifferentiableOn ℂ F slitPlane :=
    (differentiable_thetaRenewalDenominator.differentiableOn.mul hhd).sub hD'd.differentiableOn
  have hFa : AnalyticOnNhd ℂ F slitPlane := hFd.analyticOnNhd isOpen_slitPlane
  have hFx : ∀ x : ℝ, 0 < x → F x = 0 := by
    intro x hx
    have hGx := stieltjesPairTransform_ofReal_eq hρ hψm hψ hε.le hx
    have hint : ∫ t in Ioi (0 : ℝ), (((t + ε) * Real.exp (-(x * t)) : ℝ) : ℂ) *
        ∫ s, cexp (-(s * t)) * ψ s ∂ρ = ∫ t in Ioi (0 : ℝ),
          (((t + ε) * Real.exp (-(x * t)) : ℝ) : ℂ) * (thetaRenewalOddKernel (t + ε) : ℂ) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [hrep t ht]
    rw [hint, integral_shift_thetaRenewalOddKernel hε hx] at hGx
    have hxre : -(1 / 4) < (x : ℂ).re := by simp; linarith
    have hJ := thetaRenewalPhaseTransform_eq hxre
    have hDx : thetaRenewalDenominator x ≠ 0 := thetaRenewalDenominator_ne_zero hxre.le
    have hhx : h x = logDeriv thetaRenewalDenominator x := by
      simp only [hhdef]
      rw [hGx, ← mul_assoc, ← Complex.exp_add,
        show -((x : ℂ) * ε) + x * ε = 0 by ring, Complex.exp_zero, one_mul]
      rw [hJ]; ring
    simp only [hFdef]
    rw [hhx, logDeriv_apply]
    field_simp
    ring
  have hpre : IsPreconnected slitPlane :=
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), F z = 0 := by
    have htend : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using hx
    refine htend.frequently (Eventually.frequently ?_)
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx
    exact hFx x hx
  have hF0 := hFa.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre one_mem_slitPlane hfreq
  obtain ⟨ζ, hζ, hζim⟩ := infinite_nonreal_thetaRenewalDenominator_zeros.nonempty
  have hζs : ζ ∈ slitPlane := Or.inr hζim
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_thetaRenewalDenominator_ne_top ζ)
  have hm1 : m ≠ 0 := by
    rintro rfl
    have : analyticOrderAt thetaRenewalDenominator ζ = 0 := by rw [← hm]; rfl
    exact ((analyticOnNhd_thetaRenewalDenominator ζ (mem_univ ζ)).analyticOrderAt_eq_zero.mp
      this) hζ
  have hres := GaloisForLFunctions.HTGeometry.tendsto_sub_mul_logDeriv_of_analyticOrderAt
    (analyticOnNhd_thetaRenewalDenominator ζ (mem_univ ζ)) hm.symm
  have hhc : ContinuousAt h ζ := (hhd.differentiableAt (isOpen_slitPlane.mem_nhds hζs)).continuousAt
  have hzero : Tendsto (fun z => (z - ζ) * h z) (𝓝[≠] ζ) (𝓝 0) := by
    have hc : ContinuousAt (fun z => (z - ζ) * h z) ζ :=
      ContinuousAt.mul (f := fun z => z - ζ) (g := h) (by fun_prop) hhc
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {ζ}ᶜ))
    simpa using this
  have hne : ∀ᶠ z in 𝓝[≠] ζ, thetaRenewalDenominator z ≠ 0 := by
    rcases (analyticOnNhd_thetaRenewalDenominator ζ (mem_univ ζ)).eventually_eq_zero_or_eventually_ne_zero
      with h0 | h0
    · exact absurd (analyticOrderAt_eq_top.mpr h0) (analyticOrderAt_thetaRenewalDenominator_ne_top ζ)
    · exact h0
  have heq : (fun z => (z - ζ) * logDeriv thetaRenewalDenominator z) =ᶠ[𝓝[≠] ζ]
      fun z => (z - ζ) * h z := by
    filter_upwards [hne, nhdsWithin_le_nhds (isOpen_slitPlane.mem_nhds hζs)] with z hz hzs
    have hFz := hF0 hzs
    simp only [hFdef, Pi.zero_apply] at hFz
    rw [logDeriv_apply, show deriv thetaRenewalDenominator z = thetaRenewalDenominator z * h z by
      linear_combination -hFz, mul_div_cancel_left₀ _ hz]
  have hlim := tendsto_nhds_unique (hres.congr' heq) hzero
  exact hm1 (by exact_mod_cast hlim)

theorem continuousOn_thetaRenewalOddKernel : ContinuousOn thetaRenewalOddKernel (Ioi 0) := by
  have hQ := continuous_thetaRenewalLogKernel
  unfold thetaRenewalOddKernel
  exact (((by fun_prop : Continuous fun t : ℝ => Real.exp (-(t / 4))).continuousOn).div
    continuousOn_id fun t ht => (mem_Ioi.mp ht).ne').add hQ.continuousOn

theorem cexp_ofReal_neg_mul (s t : ℝ) :
    cexp (-((s : ℂ) * t)) = ((Real.exp (-(s * t)) : ℝ) : ℂ) := by
  push_cast; ring_nf

/-- Shifting a completely monotone profile keeps it completely monotone. -/
theorem completelyMonotoneOn_comp_add {H : ℝ → ℝ}
    (hH : GaloisForLFunctions.HTGeometry.CompletelyMonotoneOn H) {ε : ℝ} (hε : 0 ≤ ε) :
    GaloisForLFunctions.HTGeometry.CompletelyMonotoneOn fun t => H (t + ε) := by
  refine ⟨fun k δ hδ t ht => ?_, ?_⟩
  · have h := hH.1 k δ hδ (t + ε) (by linarith)
    have hsh : (fwdDiff δ)^[k] (fun t => H (t + ε)) t = (fwdDiff δ)^[k] H (t + ε) := by
      rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 2; ring
    rwa [hsh]
  · exact hH.2.comp (by fun_prop : Continuous fun t : ℝ => t + ε).continuousOn
      fun t ht => mem_Ioi.mpr (by linarith [mem_Ioi.mp ht])

/-- **(8), the headline.** The positive odd theta phase kernel `W(t) = e^{-t/4}/t + Q(t)` is **not**
completely monotone on `(0, ∞)`. -/
theorem not_completelyMonotoneOn_thetaRenewalOddKernel :
    ¬ GaloisForLFunctions.HTGeometry.CompletelyMonotoneOn thetaRenewalOddKernel := by
  intro hCM
  have hshift := completelyMonotoneOn_comp_add hCM zero_le_one
  have hlim : Tendsto (fun t => thetaRenewalOddKernel (t + 1)) (𝓝[>] 0)
      (𝓝 (thetaRenewalOddKernel 1)) := by
    have hc : ContinuousAt thetaRenewalOddKernel 1 :=
      continuousOn_thetaRenewalOddKernel.continuousAt (Ioi_mem_nhds one_pos)
    have hc' : ContinuousAt thetaRenewalOddKernel ((fun t : ℝ => t + 1) 0) := by simpa using hc
    have h := (hc'.comp (x := 0) (by fun_prop : ContinuousAt (fun t : ℝ => t + 1) 0)).tendsto
    simp only [Function.comp_def, zero_add] at h
    exact h.mono_left nhdsWithin_le_nhds
  obtain ⟨τ, hτfin, hτ, hrep⟩ :=
    GaloisForLFunctions.HTGeometry.exists_finiteLaplaceMeasure_of_completelyMonotoneOn hshift hlim
  haveI := hτfin
  have hτ0 : τ (Iio 0) = 0 := by rwa [← compl_Ici]
  refine not_forall_shifted_laplace_thetaRenewalOddKernel one_pos hτ0 (ψ := fun _ => 1)
    measurable_const (M := 1) (fun _ => by simp) fun t ht => ?_
  rw [hrep t ht, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [mul_one]
  rw [cexp_ofReal_neg_mul]
  congr 2
  ring

/-- Passing an exponential density: `∫ e^{-s(t+1)} g dρ = ∫ e^{-st} g d(e^{-s} ρ)`. -/
theorem integral_withDensity_exp_neg {ρ : Measure ℝ} (g : ℝ → ℂ) (t : ℝ) :
    ∫ s, cexp (-((s : ℂ) * t)) * g s ∂(ρ.withDensity fun s => ENNReal.ofReal (Real.exp (-s))) =
      ∫ s, cexp (-((s : ℂ) * (t + 1 : ℝ))) * g s ∂ρ := by
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul, cexp_ofReal_neg_mul,
    cexp_ofReal_neg_mul]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2; ring

/-- **(8).** `W` is not an absolutely convergent nonnegative real-rate Laplace mixture: there is no
positive measure `μ` on `[0, ∞)` with `W(t) = ∫ e^{-st} μ(ds)` for all `t > 0`. -/
theorem not_exists_laplaceMeasure_thetaRenewalOddKernel :
    ¬ ∃ μ : Measure ℝ, μ (Iio 0) = 0 ∧
      ∀ t : ℝ, 0 < t → thetaRenewalOddKernel t = ∫ s, Real.exp (-(s * t)) ∂μ := by
  rintro ⟨μ, hμ, hrep⟩
  have hW1 : 0 < thetaRenewalOddKernel 1 := by
    rw [thetaRenewalOddKernel]; have := thetaRenewalLogKernel_pos one_pos; positivity
  have hint : Integrable (fun s : ℝ => Real.exp (-s)) μ := by
    by_contra hni
    have h := hrep 1 one_pos
    simp only [mul_one] at h
    rw [integral_undef hni] at h
    linarith
  haveI : IsFiniteMeasure (μ.withDensity fun s => ENNReal.ofReal (Real.exp (-s))) :=
    isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral
  have hρ0 : (μ.withDensity fun s => ENNReal.ofReal (Real.exp (-s))) (Iio 0) = 0 :=
    withDensity_absolutelyContinuous μ _ hμ
  refine not_forall_shifted_laplace_thetaRenewalOddKernel one_pos hρ0 (ψ := fun _ => 1)
    measurable_const (M := 1) (fun _ => by simp) fun t ht => ?_
  rw [integral_withDensity_exp_neg, hrep (t + 1) (by linarith), ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  dsimp only
  rw [mul_one, cexp_ofReal_neg_mul]

theorem exp_neg_le_mul_inv_sq {z₀ s : ℝ} (hz₀ : 0 < z₀) (hs : 0 ≤ s) :
    Real.exp (-s) ≤ 2 * max z₀ 1 ^ 2 * ((z₀ + s) ^ 2)⁻¹ := by
  have hq := Real.quadratic_le_exp_of_nonneg hs
  have hm : z₀ ≤ max z₀ 1 := le_max_left _ _
  have hm1 : 1 ≤ max z₀ 1 := le_max_right _ _
  have hzs : z₀ + s ≤ max z₀ 1 * (1 + s) := by nlinarith
  have hpos : 0 < z₀ + s := by linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div,
    div_le_iff₀ (Real.exp_pos s)]
  have h2 : (z₀ + s) ^ 2 ≤ max z₀ 1 ^ 2 * (1 + s) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hpos.le hzs 2
  have h3 : (1 + s) ^ 2 ≤ 2 * Real.exp s := by nlinarith
  nlinarith [sq_nonneg (max z₀ 1)]

/-- **(8), signed and complex rates.** No representation `W(t) = ∫ e^{-st} μ(ds)` exists with a
signed or complex measure `μ = φ ρ` on `[0, ∞)`, `|φ| ≤ 1`, of finite weighted total variation
`∫ (z₀ + s)⁻² ρ(ds) < ∞`. -/
theorem not_exists_complexLaplaceMeasure_thetaRenewalOddKernel :
    ¬ ∃ (ρ : Measure ℝ) (φ : ℝ → ℂ) (z₀ : ℝ), 0 < z₀ ∧ ρ (Iio 0) = 0 ∧ Measurable φ ∧
      (∀ s, ‖φ s‖ ≤ 1) ∧ Integrable (fun s => ((z₀ + s) ^ 2)⁻¹) ρ ∧
      ∀ t : ℝ, 0 < t → (thetaRenewalOddKernel t : ℂ) = ∫ s, cexp (-(s * t)) * φ s ∂ρ := by
  rintro ⟨ρ, φ, z₀, hz₀, hρ, hφm, hφ, hwt, hrep⟩
  have hint : Integrable (fun s : ℝ => Real.exp (-s)) ρ := by
    refine (hwt.const_mul (2 * max z₀ 1 ^ 2)).mono' (by fun_prop) ?_
    filter_upwards [ae_nonneg_of_measure_Iio hρ] with s hs
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact exp_neg_le_mul_inv_sq hz₀ hs
  haveI : IsFiniteMeasure (ρ.withDensity fun s => ENNReal.ofReal (Real.exp (-s))) :=
    isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral
  have hρ0 : (ρ.withDensity fun s => ENNReal.ofReal (Real.exp (-s))) (Iio 0) = 0 :=
    withDensity_absolutelyContinuous ρ _ hρ
  refine not_forall_shifted_laplace_thetaRenewalOddKernel one_pos hρ0 hφm hφ fun t ht => ?_
  rw [integral_withDensity_exp_neg, hrep (t + 1) (by linarith)]

/-- **(2).** `Re[λ/(s² - λ²)] = Re λ (s² - |λ|²)/|s² - λ²|²`: the real part of each real-rate
component changes sign as `|λ|` crosses `s`, so even a positive mixture fixes no off-axis sign. -/
theorem re_div_sq_sub_sq (s : ℝ) (lam : ℂ) :
    (lam / ((s : ℂ) ^ 2 - lam ^ 2)).re =
      lam.re * (s ^ 2 - ‖lam‖ ^ 2) / ‖(s : ℂ) ^ 2 - lam ^ 2‖ ^ 2 := by
  rw [Complex.div_re, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [sub_re, sub_im, sq, mul_re, mul_im, ofReal_re, ofReal_im]
  ring

end

end RHTower

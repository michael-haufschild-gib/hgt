import GaloisForLFunctions.RHTower.ThetaCuspHawkingPreDivisorOpticalCancellationRegularLocusMeromorphicNoGo

/-!
# Optical cancellation: local analytic-branch obstruction

The exact HC74 optical-cancellation profile has a coefficient-faithful complex rational
continuation, holomorphic throughout the open critical strip. A scalar branch holomorphic on any
nonempty open subdomain cannot equal the horizontal profile there. Vertical accumulation first
forces the local branch to be constant in an interior ball. Horizontal accumulation then forces the
rational continuation to be constant on the entire strip, contradicting its exact quarter/half
separation.

Thus neither isolated poles nor branch cuts rescue pointwise scalar cancellation on an open
frequency domain. Distributional, support-changing, antiholomorphic, or operator-valued survivors
remain outside this theorem.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- Complexified first reflected-real-pair horizon angular shift. -/
def d4PreDivisorHorizonAngularShiftHolomorphic (z : ℂ) : ℂ :=
  z * (3 - z)

/-- Complexified reflected horizon angular shift. -/
def d4PreDivisorReflectedHorizonAngularShiftHolomorphic (z : ℂ) : ℂ :=
  (1 - z) * (2 + z)

/-- Complexification of the exact moving-horizon third-mass cross numerator. -/
def d4EventHorizonThirdMassParityCrossNumeratorHolomorphic (A B : ℂ) : ℂ :=
  A ^ 2 * (2 - B) + B ^ 2 * (2 - A) + 2 * A * B

/-- Coefficient-faithful complex rational continuation of the HC74 pre-divisor optical-cancellation
profile. Its only possible denominator zeros come from the four horizon-shift boundary roots. -/
def d4PreDivisorOpticalCancellationHolomorphicContinuation (z : ℂ) : ℂ :=
  let A := d4PreDivisorHorizonAngularShiftHolomorphic z
  let B := d4PreDivisorReflectedHorizonAngularShiftHolomorphic z
  (648 * d4EventHorizonThirdMassParityCrossNumeratorHolomorphic A B /
      (A ^ 3 * B ^ 3)) *
    (z * (1 - z) * (2 - z) * (3 - z) * (z + 1) * (z + 2)) / 12

/-- The complex rational continuation specializes literally to the real HC74 optical-cancellation
profile. -/
theorem d4PreDivisorOpticalCancellationHolomorphicContinuation_ofReal (x : ℝ) :
    d4PreDivisorOpticalCancellationHolomorphicContinuation (x : ℂ) =
      (d4PreDivisorOpticalCancellationSusceptibility x : ℂ) := by
  simp [d4PreDivisorOpticalCancellationHolomorphicContinuation,
    d4PreDivisorHorizonAngularShiftHolomorphic,
    d4PreDivisorReflectedHorizonAngularShiftHolomorphic,
    d4EventHorizonThirdMassParityCrossNumeratorHolomorphic,
    d4PreDivisorOpticalCancellationSusceptibility,
    d4PreDivisorEventHorizonThirdMassReflectionSusceptibility,
    d4PreDivisorThetaMirrorAIMEDenominator,
    d4PreDivisorHorizonAngularShift,
    d4PreDivisorReflectedHorizonAngularShift,
    d4EventHorizonThirdMassParityCrossNumerator]

/-- The coefficient-faithful rational continuation is holomorphic on the full open critical strip;
all four horizon-shift roots lie on or outside its boundary. -/
theorem analyticOnNhd_d4PreDivisorOpticalCancellationHolomorphicContinuation :
    AnalyticOnNhd ℂ d4PreDivisorOpticalCancellationHolomorphicContinuation
      {z : ℂ | 0 < z.re ∧ z.re < 1} := by
  intro z hz
  change 0 < z.re ∧ z.re < 1 at hz
  have hz0 : z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hz3 : (3 : ℂ) - z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hz1 : (1 : ℂ) - z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hzn2 : (2 : ℂ) + z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hA : d4PreDivisorHorizonAngularShiftHolomorphic z ≠ 0 := by
    unfold d4PreDivisorHorizonAngularShiftHolomorphic
    exact mul_ne_zero hz0 hz3
  have hB : d4PreDivisorReflectedHorizonAngularShiftHolomorphic z ≠ 0 := by
    unfold d4PreDivisorReflectedHorizonAngularShiftHolomorphic
    exact mul_ne_zero hz1 hzn2
  have hAan : AnalyticAt ℂ d4PreDivisorHorizonAngularShiftHolomorphic z := by
    unfold d4PreDivisorHorizonAngularShiftHolomorphic
    fun_prop
  have hBan : AnalyticAt ℂ d4PreDivisorReflectedHorizonAngularShiftHolomorphic z := by
    unfold d4PreDivisorReflectedHorizonAngularShiftHolomorphic
    fun_prop
  have hcross : AnalyticAt ℂ
      (fun w => d4EventHorizonThirdMassParityCrossNumeratorHolomorphic
        (d4PreDivisorHorizonAngularShiftHolomorphic w)
        (d4PreDivisorReflectedHorizonAngularShiftHolomorphic w)) z := by
    unfold d4EventHorizonThirdMassParityCrossNumeratorHolomorphic
    fun_prop
  have hthird : AnalyticAt ℂ
      (fun w => 648 * d4EventHorizonThirdMassParityCrossNumeratorHolomorphic
          (d4PreDivisorHorizonAngularShiftHolomorphic w)
          (d4PreDivisorReflectedHorizonAngularShiftHolomorphic w) /
        (d4PreDivisorHorizonAngularShiftHolomorphic w ^ 3 *
          d4PreDivisorReflectedHorizonAngularShiftHolomorphic w ^ 3)) z := by
    exact (analyticAt_const.mul hcross).div
      ((hAan.pow 3).mul (hBan.pow 3))
      (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hB))
  have hden : AnalyticAt ℂ
      (fun w : ℂ => w * (1 - w) * (2 - w) * (3 - w) * (w + 1) * (w + 2)) z := by
    fun_prop
  unfold d4PreDivisorOpticalCancellationHolomorphicContinuation
  dsimp only
  exact (hthird.mul hden).div analyticAt_const (by norm_num)

/-- No scalar function holomorphic on any nonempty open subdomain of the critical strip can equal
the exact horizontal optical-cancellation profile there. The domain need not be connected. -/
theorem not_exists_localAnalyticBranch_preDivisorOpticalCancellationSusceptibility :
    ¬ ∃ (Ω : Set ℂ) (f : ℂ → ℂ),
      IsOpen Ω ∧
      Ω.Nonempty ∧
      Ω ⊆ {z : ℂ | 0 < z.re ∧ z.re < 1} ∧
      AnalyticOnNhd ℂ f Ω ∧
      ∀ z ∈ Ω,
        f z = (d4PreDivisorOpticalCancellationSusceptibility z.re : ℂ) := by
  rintro ⟨Ω, f, hΩ, hΩne, hΩsub, hf, hprofile⟩
  obtain ⟨s₀, hs₀⟩ := hΩne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ s₀ hs₀
  let H : ℂ → ℂ := fun z => f z - f s₀
  have hHan : AnalyticOnNhd ℂ H (Metric.ball s₀ ε) :=
    (hf.mono hball).sub analyticOnNhd_const
  let u : ℕ → ℂ := fun m => s₀ + Complex.I * ((1 : ℝ) / (m + 1) : ℝ)
  have hutend : Tendsto u atTop (nhds s₀) := by
    have hzero : Tendsto (fun m : ℕ => ((1 : ℝ) / (m + 1) : ℝ))
        atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hcast : Tendsto
        (fun m : ℕ => (((1 : ℝ) / (m + 1) : ℝ) : ℂ)) atTop (nhds 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp hzero
    have hmul : Tendsto
        (fun m : ℕ => Complex.I * (((1 : ℝ) / (m + 1) : ℝ) : ℂ))
        atTop (nhds 0) := by
      simpa using hcast.const_mul Complex.I
    simpa [u] using hmul.const_add s₀
  have hune : ∀ m : ℕ, u m ≠ s₀ := by
    intro m hm
    have hzero : Complex.I * (((1 : ℝ) / (m + 1) : ℝ) : ℂ) = 0 := by
      simpa [u] using sub_eq_zero.mpr hm
    rcases mul_eq_zero.mp hzero with hI | hdiv
    · exact Complex.I_ne_zero hI
    · have hpos : (0 : ℝ) < (1 : ℝ) / (m + 1) := by positivity
      have : (1 : ℝ) / (m + 1) = 0 := by exact_mod_cast hdiv
      linarith
  have hure : ∀ m : ℕ, (u m).re = s₀.re := by
    intro m
    simp [u]
  have humem : ∀ᶠ m in atTop, u m ∈ Metric.ball s₀ ε :=
    hutend.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
  have hHzero : ∀ᶠ m in atTop, H (u m) = 0 := by
    filter_upwards [humem] with m hm
    change f (u m) - f s₀ = 0
    rw [hprofile (u m) (hball hm), hprofile s₀ hs₀, hure m, sub_self]
  have hHfrequently : ∃ᶠ z in nhdsWithin s₀ {s₀}ᶜ, H z = 0 := by
    have htendWithin : Tendsto u atTop (nhdsWithin s₀ {s₀}ᶜ) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hutend
        (Eventually.of_forall hune)
    exact htendWithin.frequently hHzero.frequently
  have hHeq := hHan.eqOn_zero_of_preconnected_of_frequently_eq_zero
    Metric.isPreconnected_ball (Metric.mem_ball_self hε) hHfrequently
  have hlocal : ∀ z ∈ Metric.ball s₀ ε, f z = f s₀ := by
    intro z hz
    have hzero : H z = 0 := hHeq hz
    exact sub_eq_zero.mp hzero
  let v : ℕ → ℂ := fun m =>
    s₀ + Complex.ofReal ((1 : ℝ) / ((m : ℝ) + 1))
  have hvtend : Tendsto v atTop (nhds s₀) := by
    have hzero : Tendsto (fun m : ℕ => ((1 : ℝ) / (m + 1) : ℝ))
        atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hcast : Tendsto
        (fun m : ℕ => (((1 : ℝ) / (m + 1) : ℝ) : ℂ)) atTop (nhds 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp hzero
    simpa [v] using hcast.const_add s₀
  have hvmem : ∀ᶠ m in atTop, v m ∈ Metric.ball s₀ ε :=
    hvtend.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
  let w₀ : ℂ := Complex.ofReal s₀.re
  let w : ℕ → ℂ := fun m =>
    Complex.ofReal (s₀.re + (1 : ℝ) / ((m : ℝ) + 1))
  let K : ℂ → ℂ := fun z =>
    d4PreDivisorOpticalCancellationHolomorphicContinuation z -
      d4PreDivisorOpticalCancellationHolomorphicContinuation w₀
  have hKan : AnalyticOnNhd ℂ K {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    analyticOnNhd_d4PreDivisorOpticalCancellationHolomorphicContinuation.sub
      analyticOnNhd_const
  have hwtend : Tendsto w atTop (nhds w₀) := by
    have hzero : Tendsto (fun m : ℕ => ((1 : ℝ) / (m + 1) : ℝ))
        atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hadd : Tendsto (fun m : ℕ => s₀.re + (1 : ℝ) / (m + 1))
        atTop (nhds s₀.re) := by
      simpa using hzero.const_add s₀.re
    change Tendsto
      (fun m : ℕ => Complex.ofReal (s₀.re + (1 : ℝ) / ((m : ℝ) + 1)))
      atTop (nhds (Complex.ofReal s₀.re))
    exact (Complex.continuous_ofReal.tendsto s₀.re).comp hadd
  have hwne : ∀ m : ℕ, w m ≠ w₀ := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [w, w₀, Complex.ofReal_re] at hre
    have hpos : (0 : ℝ) < (1 : ℝ) / (m + 1) := by positivity
    linarith
  have hKzero : ∀ᶠ m in atTop, K (w m) = 0 := by
    filter_upwards [hvmem] with m hm
    have hfeq : f (v m) = f s₀ := hlocal (v m) hm
    rw [hprofile (v m) (hball hm), hprofile s₀ hs₀] at hfeq
    have hvre : (v m).re = s₀.re + (1 : ℝ) / ((m : ℝ) + 1) := by
      change (s₀ + Complex.ofReal ((1 : ℝ) / ((m : ℝ) + 1))).re = _
      simp only [Complex.add_re, Complex.ofReal_re]
    have hprof :
        (d4PreDivisorOpticalCancellationSusceptibility
            (s₀.re + (1 : ℝ) / (m + 1)) : ℂ) =
          (d4PreDivisorOpticalCancellationSusceptibility s₀.re : ℂ) := by
      rwa [hvre] at hfeq
    change d4PreDivisorOpticalCancellationHolomorphicContinuation (w m) -
      d4PreDivisorOpticalCancellationHolomorphicContinuation w₀ = 0
    rw [show w m = ((s₀.re + (1 : ℝ) / (m + 1) : ℝ) : ℂ) by rfl,
      show w₀ = (s₀.re : ℂ) by rfl,
      d4PreDivisorOpticalCancellationHolomorphicContinuation_ofReal,
      d4PreDivisorOpticalCancellationHolomorphicContinuation_ofReal,
      hprof, sub_self]
  have hKfrequently : ∃ᶠ z in nhdsWithin w₀ {w₀}ᶜ, K z = 0 := by
    have htendWithin : Tendsto w atTop (nhdsWithin w₀ {w₀}ᶜ) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within w hwtend
        (Eventually.of_forall hwne)
    exact htendWithin.frequently hKzero.frequently
  have hw₀mem : w₀ ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    have hsstrip := hΩsub hs₀
    simpa [w₀] using hsstrip
  have hKeq := hKan.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_criticalStrip hw₀mem hKfrequently
  have hquarter : K (((1 / 4 : ℝ) : ℂ)) = 0 := hKeq (by norm_num)
  have hhalf : K (((1 / 2 : ℝ) : ℂ)) = 0 := hKeq (by norm_num)
  have hP :
      d4PreDivisorOpticalCancellationHolomorphicContinuation (((1 / 4 : ℝ) : ℂ)) =
        d4PreDivisorOpticalCancellationHolomorphicContinuation
          (((1 / 2 : ℝ) : ℂ)) := by
    have hq :
        d4PreDivisorOpticalCancellationHolomorphicContinuation (((1 / 4 : ℝ) : ℂ)) =
          d4PreDivisorOpticalCancellationHolomorphicContinuation w₀ :=
      sub_eq_zero.mp hquarter
    have hh :
        d4PreDivisorOpticalCancellationHolomorphicContinuation (((1 / 2 : ℝ) : ℂ)) =
          d4PreDivisorOpticalCancellationHolomorphicContinuation w₀ :=
      sub_eq_zero.mp hhalf
    exact hq.trans hh.symm
  rw [d4PreDivisorOpticalCancellationHolomorphicContinuation_ofReal,
    d4PreDivisorOpticalCancellationHolomorphicContinuation_ofReal] at hP
  apply d4PreDivisorOpticalCancellationSusceptibility_quarter_ne_half
  exact_mod_cast hP

end

end RHTower

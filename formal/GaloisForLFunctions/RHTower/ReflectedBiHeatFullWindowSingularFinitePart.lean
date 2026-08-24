import GaloisForLFunctions.RHTower.ReflectedBiHeatFixedRegulatorIdentity
import GaloisForLFunctions.RHTower.ReflectedBiHeatGammaCoefficient
import GaloisForLFunctions.RHTower.HeatRemainderDerivative
import GaloisForLFunctions.RHTower.HeatLadderAsymptotic
import GaloisForLFunctions.RHTower.GaussianLogFinitePart
import GaloisForLFunctions.RHTower.DigammaSeries
import GaloisForLFunctions.HTGeometry.ComplexBallMeanValue
import GaloisForLFunctions.HTGeometry.InteriorIntegrationByParts
import GaloisForLFunctions.HTGeometry.InverseSqrtEndpointIntegral

/-!
# Exact full-window singular finite part

The Gaussian singular moment has residue `x⁻¹ᐟ²`, whereas the circle heat multiplier has exact
residue `Theta(x)`.  This module fills the full-window Mellin pole by subtracting the multiplier's
value at the phase origin inside the integral.  The filled unit is holomorphic at regulator zero,
agrees off the pole with `epsilon * heatMoment x (epsilon - 1)`, and therefore supplies the exact
singular finite part compatible with theta-row subtraction.
-/

open Complex Filter Set Topology MeasureTheory Metric

namespace RHTower

noncomputable section

/-- Entire complex-phase extension of the additive heat multiplier. -/
def complexHeatMultiplier (x : ℝ) (z : ℂ) : ℂ :=
  jacobiTheta₂ (z / (2 * (Real.pi : ℂ))) (I * (x : ℂ))

theorem complexHeatMultiplier_ofReal (x theta : ℝ) :
    complexHeatMultiplier x (theta : ℂ) = heatMultiplier x theta := by
  rw [complexHeatMultiplier, heatMultiplier_eq_jacobiTheta₂]
  congr 2
  push_cast
  rfl

theorem differentiable_complexHeatMultiplier {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (complexHeatMultiplier x) := by
  have him : 0 < (I * (x : ℂ)).im := by
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, one_mul, zero_mul]
    simpa using hx
  have hjac : Differentiable ℂ (fun z : ℂ => jacobiTheta₂ z (I * (x : ℂ))) :=
    fun z => differentiableAt_jacobiTheta₂_fst z him
  rw [show complexHeatMultiplier x = fun z : ℂ =>
      jacobiTheta₂ (z / (2 * (Real.pi : ℂ))) (I * (x : ℂ)) by rfl]
  exact hjac.comp (by fun_prop)

/-- Compact Cauchy control makes the phase divided difference uniformly bounded. -/
theorem exists_heatMultiplier_divided_bound {x : ℝ} (hx : 0 < x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ theta ∈ Ioc (0 : ℝ) Real.pi,
      ‖(heatMultiplier x theta - heatMultiplier x 0) / (theta : ℂ)‖ ≤ M := by
  let f : ℂ → ℂ := complexHeatMultiplier x
  have hf : Differentiable ℂ f := differentiable_complexHeatMultiplier hx
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (4 * Real.pi)).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  have hB0 : 0 ≤ B :=
    (norm_nonneg (f 0)).trans (hB 0 (mem_closedBall_self (by positivity)))
  let M : ℝ := 2 * B / (4 * Real.pi)
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hderiv : ∀ w ∈ closedBall (0 : ℂ) Real.pi, ‖deriv f w‖ ≤ M := by
    intro w hw
    have hw' : w ∈ ball (0 : ℂ) ((4 * Real.pi) / 2) := by
      rw [mem_ball, dist_zero_right]
      have hn := hw
      rw [mem_closedBall, dist_zero_right] at hn
      linarith [Real.pi_pos]
    exact Bottcher.norm_deriv_le_of_bounded_on_ball (by positivity)
      hf.differentiableOn (fun z hz => hB z (ball_subset_closedBall hz)) w hw'
  refine ⟨M, hM0, fun theta htheta => ?_⟩
  have hthetaBall : (theta : ℂ) ∈ closedBall (0 : ℂ) Real.pi := by
    rw [mem_closedBall, dist_zero_right, norm_real, Real.norm_of_nonneg htheta.1.le]
    exact htheta.2
  have hzeroBall : (0 : ℂ) ∈ closedBall (0 : ℂ) Real.pi :=
    mem_closedBall_self Real.pi_pos.le
  have hlip := HTGeometry.norm_sub_le_of_hasDerivAt_ball
    (f := f) (f' := deriv f) (c := 0) (r := Real.pi) (C := M)
    (fun w => (hf w).hasDerivAt) hderiv hzeroBall hthetaBall
  dsimp [f] at hlip
  have hzero : complexHeatMultiplier x 0 = heatMultiplier x 0 := by
    simpa using complexHeatMultiplier_ofReal x 0
  rw [complexHeatMultiplier_ofReal, hzero] at hlip
  rw [norm_div, norm_real, Real.norm_of_nonneg htheta.1.le]
  exact (div_le_iff₀ htheta.1).mpr
    (by simpa [norm_real, abs_of_pos htheta.1] using hlip)

/-- Divided difference of the heat multiplier at the singular phase. -/
def heatMultiplierDivided (x theta : ℝ) : ℂ :=
  if theta = 0 then 0 else (heatMultiplier x theta - heatMultiplier x 0) / (theta : ℂ)

theorem norm_heatMultiplierDivided_le {x : ℝ} (hx : 0 < x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ theta ∈ Ioc (0 : ℝ) Real.pi,
      ‖heatMultiplierDivided x theta‖ ≤ M := by
  obtain ⟨M, hM0, hM⟩ := exists_heatMultiplier_divided_bound hx
  refine ⟨M, hM0, fun theta htheta => ?_⟩
  rw [heatMultiplierDivided, if_neg htheta.1.ne']
  exact hM theta htheta

/-- Holomorphic regular Mellin remainder after subtracting the phase-origin value. -/
def heatMomentRegularMellin (x : ℝ) (epsilon : ℂ) : ℂ :=
  (1 / (Real.pi : ℂ)) *
    ∫ theta in Ioc (0 : ℝ) Real.pi,
      ((theta : ℂ) ^ epsilon) * heatMultiplierDivided x theta

theorem continuousOn_heatMultiplierDivided {x : ℝ} (hx : 0 < x) :
    ContinuousOn (heatMultiplierDivided x) (Ioc (0 : ℝ) Real.pi) := by
  have hquot : ContinuousOn (fun theta : ℝ =>
      (heatMultiplier x theta - heatMultiplier x 0) / (theta : ℂ))
      (Ioc (0 : ℝ) Real.pi) := by
    intro theta htheta
    exact (((continuous_heatMultiplier hx).continuousAt.sub
      (continuousAt_const : ContinuousAt (fun _ : ℝ => heatMultiplier x 0) theta)).div
        (Complex.continuous_ofReal.continuousAt)
        (Complex.ofReal_ne_zero.mpr htheta.1.ne')).continuousWithinAt
  exact hquot.congr fun theta htheta => by
    simp [heatMultiplierDivided, htheta.1.ne']

theorem differentiableAt_heatMomentRegularMellin_zero {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℂ (heatMomentRegularMellin x) 0 := by
  obtain ⟨M, hM0, hM⟩ := norm_heatMultiplierDivided_le hx
  let F : ℂ → ℝ → ℂ := fun epsilon theta =>
    (Ioc (0 : ℝ) Real.pi).indicator
      (fun theta => ((theta : ℂ) ^ epsilon) * heatMultiplierDivided x theta) theta
  let bound : ℝ → ℝ := fun theta =>
    (Ioc (0 : ℝ) Real.pi).indicator
      (fun theta => M * (theta ^ (-(1 : ℝ) / 2) + Real.pi ^ ((1 : ℝ) / 2))) theta
  have hmeas : ∀ epsilon ∈ ball (0 : ℂ) (1 / 2 : ℝ),
      AEStronglyMeasurable (F epsilon)
        (volume.restrict (Ioc (0 : ℝ) Real.pi)) := by
    intro epsilon hepsilon
    have hpow : ContinuousOn (fun theta : ℝ => (theta : ℂ) ^ epsilon)
        (Ioc (0 : ℝ) Real.pi) := continuousOn_Ioc_cpow epsilon Real.pi
    have hraw : AEStronglyMeasurable
        (fun theta : ℝ => (theta : ℂ) ^ epsilon * heatMultiplierDivided x theta)
        (volume.restrict (Ioc (0 : ℝ) Real.pi)) :=
      (hpow.mul (continuousOn_heatMultiplierDivided hx)).aestronglyMeasurable
        measurableSet_Ioc
    apply hraw.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with theta htheta
    simp [F, Set.indicator_of_mem htheta]
  have hdiff : ∀ theta : ℝ,
      DifferentiableOn ℂ (fun epsilon : ℂ => F epsilon theta)
        (ball (0 : ℂ) (1 / 2 : ℝ)) := by
    intro theta
    by_cases htheta : theta ∈ Ioc (0 : ℝ) Real.pi
    · have htheta0 : ((theta : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr htheta.1.ne'
      simpa [F, Set.indicator_of_mem htheta] using
        ((differentiable_id.const_cpow (Or.inl htheta0)).mul_const
          (heatMultiplierDivided x theta)).differentiableOn
    · simp [F, Set.indicator_of_notMem htheta]
  have hbound : ∀ theta : ℝ, ∀ epsilon ∈ ball (0 : ℂ) (1 / 2 : ℝ),
      ‖F epsilon theta‖ ≤ bound theta := by
    intro theta epsilon hepsilon
    by_cases htheta : theta ∈ Ioc (0 : ℝ) Real.pi
    · rw [show F epsilon theta = (theta : ℂ) ^ epsilon * heatMultiplierDivided x theta by
          simp [F, Set.indicator_of_mem htheta],
        show bound theta = M *
            (theta ^ (-(1 : ℝ) / 2) + Real.pi ^ ((1 : ℝ) / 2)) by
          simp [bound, Set.indicator_of_mem htheta], norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos htheta.1]
      have hepsNorm : ‖epsilon‖ < 1 / 2 := by simpa [mem_ball, dist_zero_right] using hepsilon
      have hreLower : -(1 / 2 : ℝ) ≤ epsilon.re := by
        have habs : |epsilon.re| < 1 / 2 :=
          lt_of_le_of_lt (Complex.abs_re_le_norm epsilon) hepsNorm
        exact (abs_lt.mp habs).1.le
      have hreUpper : epsilon.re ≤ 1 / 2 := by
        have habs : |epsilon.re| < 1 / 2 :=
          lt_of_le_of_lt (Complex.abs_re_le_norm epsilon) hepsNorm
        exact (abs_lt.mp habs).2.le
      have hpow : theta ^ epsilon.re ≤
          theta ^ (-(1 : ℝ) / 2) + Real.pi ^ ((1 : ℝ) / 2) := by
        by_cases hthetaOne : theta ≤ 1
        · have hle := Real.rpow_le_rpow_of_exponent_ge htheta.1 hthetaOne hreLower
          calc
            theta ^ epsilon.re ≤ theta ^ (-(1 / 2 : ℝ)) := hle
            _ = theta ^ (-(1 : ℝ) / 2) := by congr 1 <;> ring
            _ ≤ theta ^ (-(1 : ℝ) / 2) + Real.pi ^ ((1 : ℝ) / 2) :=
              le_add_of_nonneg_right (Real.rpow_nonneg Real.pi_pos.le _)
        · have hone : 1 ≤ theta := (le_of_not_ge hthetaOne)
          have hthetaPi : theta ≤ Real.pi := htheta.2
          have hle1 := Real.rpow_le_rpow_of_exponent_le hone hreUpper
          have hle2 := Real.rpow_le_rpow (by positivity) hthetaPi (by norm_num : 0 ≤ (1 / 2 : ℝ))
          exact (hle1.trans hle2).trans
            (le_add_of_nonneg_left (Real.rpow_nonneg htheta.1.le _))
      calc
        theta ^ epsilon.re * ‖heatMultiplierDivided x theta‖ ≤
            (theta ^ (-(1 : ℝ) / 2) + Real.pi ^ ((1 : ℝ) / 2)) *
              ‖heatMultiplierDivided x theta‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
        _ ≤ (theta ^ (-(1 : ℝ) / 2) + Real.pi ^ ((1 : ℝ) / 2)) * M :=
          mul_le_mul_of_nonneg_left (hM theta htheta)
            (add_nonneg (Real.rpow_nonneg htheta.1.le _)
              (Real.rpow_nonneg Real.pi_pos.le _))
        _ = M * (theta ^ (-(1 : ℝ) / 2) + Real.pi ^ ((1 : ℝ) / 2)) := by ring
    · simp [F, bound, Set.indicator_of_notMem htheta]
  have hboundInt : Integrable bound
      (volume.restrict (Ioc (0 : ℝ) Real.pi)) := by
    have hsing : IntegrableOn (fun theta : ℝ => theta ^ (-(1 : ℝ) / 2))
        (Ioc (0 : ℝ) Real.pi) := integrableOn_rpow_window (by norm_num)
    have hconst : IntegrableOn (fun _ : ℝ => Real.pi ^ ((1 : ℝ) / 2))
        (Ioc (0 : ℝ) Real.pi) := by
      change Integrable (fun _ : ℝ => Real.pi ^ ((1 : ℝ) / 2))
        (volume.restrict (Ioc (0 : ℝ) Real.pi))
      simpa using (integrableOn_rpow_window (sig := 0) (by norm_num)).const_mul
        (Real.pi ^ ((1 : ℝ) / 2))
    have hraw := (hsing.add hconst).const_mul M
    apply hraw.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with theta htheta
    simp [bound, Set.indicator_of_mem htheta]
  have hIntegral :=
    GaloisForLFunctions.HTGeometry.differentiableAt_integral_of_cauchy_dominated
      (μ := volume.restrict (Ioc (0 : ℝ) Real.pi)) (by norm_num : 0 < (1 / 2 : ℝ))
      hmeas hdiff hbound hboundInt
  have hfun : (fun epsilon : ℂ => ∫ theta : ℝ, F epsilon theta
        ∂(volume.restrict (Ioc (0 : ℝ) Real.pi))) =
      fun epsilon : ℂ => ∫ theta in Ioc (0 : ℝ) Real.pi,
        ((theta : ℂ) ^ epsilon) * heatMultiplierDivided x theta := by
    funext epsilon
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with theta htheta
    simp [F, Set.indicator_of_mem htheta]
  rw [hfun] at hIntegral
  change DifferentiableAt ℂ (fun epsilon : ℂ => (1 / (Real.pi : ℂ)) *
    ∫ theta in Ioc (0 : ℝ) Real.pi,
      (theta : ℂ) ^ epsilon * heatMultiplierDivided x theta) 0
  exact (differentiableAt_const (c := (1 / (Real.pi : ℂ)))).mul hIntegral

/-- Pole-filled exact full-window heat moment. -/
def heatMomentPoleUnit (x : ℝ) (epsilon : ℂ) : ℂ :=
  (heatMultiplier x 0 / (Real.pi : ℂ)) *
      Complex.exp (epsilon * (Real.log Real.pi : ℂ)) +
    epsilon * heatMomentRegularMellin x epsilon

theorem heatMomentPoleUnit_zero (x : ℝ) :
    heatMomentPoleUnit x 0 = heatMultiplier x 0 / (Real.pi : ℂ) := by
  simp [heatMomentPoleUnit]

theorem differentiableAt_heatMomentPoleUnit_zero {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℂ (heatMomentPoleUnit x) 0 := by
  rw [show heatMomentPoleUnit x = fun epsilon : ℂ =>
      (heatMultiplier x 0 / (Real.pi : ℂ)) *
          Complex.exp (epsilon * (Real.log Real.pi : ℂ)) +
        epsilon * heatMomentRegularMellin x epsilon by rfl]
  exact ((by fun_prop : DifferentiableAt ℂ (fun epsilon : ℂ =>
      (heatMultiplier x 0 / (Real.pi : ℂ)) *
        Complex.exp (epsilon * (Real.log Real.pi : ℂ))) 0).add
    (differentiableAt_id.mul (differentiableAt_heatMomentRegularMellin_zero hx)))

theorem deriv_heatMomentPoleUnit_zero {x : ℝ} (hx : 0 < x) :
    deriv (heatMomentPoleUnit x) 0 =
      (heatMultiplier x 0 / (Real.pi : ℂ)) * (Real.log Real.pi : ℂ) +
        heatMomentRegularMellin x 0 := by
  have hreg := differentiableAt_heatMomentRegularMellin_zero hx
  have hmain : HasDerivAt (fun epsilon : ℂ =>
      (heatMultiplier x 0 / (Real.pi : ℂ)) *
        Complex.exp (epsilon * (Real.log Real.pi : ℂ)))
      ((heatMultiplier x 0 / (Real.pi : ℂ)) * (Real.log Real.pi : ℂ)) 0 := by
    have h := (((hasDerivAt_id (0 : ℂ)).mul_const
      (Real.log Real.pi : ℂ)).cexp.const_mul
        (heatMultiplier x 0 / (Real.pi : ℂ)))
    simpa [mul_comm] using h
  have htail := (hasDerivAt_id (0 : ℂ)).mul hreg.hasDerivAt
  have hsum := hmain.add htail
  have hderiv := hsum.deriv
  change deriv (heatMomentPoleUnit x) 0 = _ at hderiv
  simpa using hderiv

/-- Exact positive-half integral of the singular Mellin power. -/
theorem integral_Ioc_cpow_epsilon_sub_one {epsilon : ℂ} (hepsilon : 0 < epsilon.re) :
    (∫ theta in Ioc (0 : ℝ) Real.pi, (theta : ℂ) ^ (epsilon - 1)) =
      (Real.pi : ℂ) ^ epsilon / epsilon := by
  have hre : (-1 : ℝ) < (epsilon - 1).re := by simp; linarith
  have hne : epsilon ≠ 0 := by
    intro h
    rw [h] at hepsilon
    norm_num at hepsilon
  rw [← intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_cpow (Or.inl hre)]
  rw [show epsilon - 1 + 1 = epsilon by ring]
  rw [Complex.ofReal_zero, Complex.zero_cpow hne]
  simp

theorem heatMomentRegularMellin_eq_subtracted_integral
    {x : ℝ} {epsilon : ℂ} :
    heatMomentRegularMellin x epsilon =
      (1 / (Real.pi : ℂ)) *
        ∫ theta in Ioc (0 : ℝ) Real.pi,
          (theta : ℂ) ^ (epsilon - 1) *
            (heatMultiplier x theta - heatMultiplier x 0) := by
  rw [heatMomentRegularMellin]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro theta htheta
  simp only [heatMultiplierDivided, if_neg htheta.1.ne']
  rw [Complex.cpow_sub epsilon 1 (Complex.ofReal_ne_zero.mpr htheta.1.ne'),
    Complex.cpow_one]
  ring

/-- Exact pole filling: away from zero the analytic unit is
`epsilon * heatMoment x (epsilon - 1)`. -/
theorem heatMomentPoleUnit_eq_mul_heatMoment
    {x : ℝ} (hx : 0 < x) {epsilon : ℂ} (hepsilon : 0 < epsilon.re) :
    heatMomentPoleUnit x epsilon = epsilon * heatMoment x (epsilon - 1) := by
  have hlam : -1 < (epsilon - 1).re := by simp; linarith
  have hmain := integrableOn_cpow_mul_heatMultiplier hlam hx
  have hpure : IntegrableOn (fun theta : ℝ =>
      heatMultiplier x 0 * (theta : ℂ) ^ (epsilon - 1))
      (Ioc (0 : ℝ) Real.pi) := by
    have hpow : IntegrableOn (fun theta : ℝ => (theta : ℂ) ^ (epsilon - 1))
        (Ioc (0 : ℝ) Real.pi) := by
      have h := intervalIntegral.intervalIntegrable_cpow' (a := (0 : ℝ))
        (b := Real.pi) (r := epsilon - 1) hlam
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mp h
    exact hpow.const_mul _
  have hsub : IntegrableOn (fun theta : ℝ =>
      (theta : ℂ) ^ (epsilon - 1) *
        (heatMultiplier x theta - heatMultiplier x 0))
      (Ioc (0 : ℝ) Real.pi) := by
    exact hmain.sub hpure |>.congr_fun (fun theta _ => by
      simp only [Pi.sub_apply]
      ring_nf) measurableSet_Ioc
  have hsplit : (∫ theta in Ioc (0 : ℝ) Real.pi,
      (theta : ℂ) ^ (epsilon - 1) * heatMultiplier x theta) =
      heatMultiplier x 0 * ((Real.pi : ℂ) ^ epsilon / epsilon) +
        ∫ theta in Ioc (0 : ℝ) Real.pi,
          (theta : ℂ) ^ (epsilon - 1) *
            (heatMultiplier x theta - heatMultiplier x 0) := by
    rw [← integral_Ioc_cpow_epsilon_sub_one hepsilon,
      ← MeasureTheory.integral_const_mul]
    have hadd := MeasureTheory.integral_add hpure hsub
    calc
      _ = ∫ theta in Ioc (0 : ℝ) Real.pi,
          heatMultiplier x 0 * (theta : ℂ) ^ (epsilon - 1) +
            (theta : ℂ) ^ (epsilon - 1) *
              (heatMultiplier x theta - heatMultiplier x 0) := by
            apply setIntegral_congr_fun measurableSet_Ioc
            intro theta htheta
            ring
      _ = _ := hadd
  have hhalf := integral_abs_cpow_mul_heatMultiplier_window hlam hx
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hepsilon0 : epsilon ≠ 0 := by
    intro h
    rw [h] at hepsilon
    norm_num at hepsilon
  have hpowExp : Complex.exp (epsilon * (Real.log Real.pi : ℂ)) =
      (Real.pi : ℂ) ^ epsilon := by
    rw [Complex.cpow_def_of_ne_zero hpi]
    congr 1
    have hlog : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) := by
      apply Complex.ext
      · rw [Complex.log_ofReal_re]
        rfl
      · rw [Complex.log_im, Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
        simp
    rw [hlog]
    ring
  rw [heatMomentPoleUnit, heatMomentRegularMellin_eq_subtracted_integral,
    hpowExp, heatMoment, hhalf, hsplit]
  field_simp [hpi, hepsilon0]

/-- At phase zero, the multiplier is the exact theta residue. -/
theorem heatMultiplier_zero_eq_heatCoeffSum {x : ℝ} (hx : 0 < x) :
    heatMultiplier x 0 = ((heatCoeffSum x : ℝ) : ℂ) := by
  rw [heatMultiplier, heatCoeffSum]
  push_cast
  apply tsum_congr
  intro k
  rw [heatCoeff]
  congr 1
  push_cast
  ring

/-- Pole-filled exact full-window singular channel.  Unlike the whole-line Gaussian model, its
residue is the exact theta mass `heatCoeffSum P.x`. -/
noncomputable def reflectedFullWindowSingularPoleUnit
    (P : ReflectedBiHeatRegulator) (epsilon : ℂ) : ℂ :=
  reflectedGammaCoefficient P.z epsilon * heatMomentPoleUnit P.x epsilon

theorem differentiableAt_reflectedFullWindowSingularPoleUnit_zero
    (P : ReflectedBiHeatRegulator) :
    DifferentiableAt ℂ (reflectedFullWindowSingularPoleUnit P) 0 := by
  exact (differentiableAt_reflectedGammaCoefficient_zero P).mul
    (differentiableAt_heatMomentPoleUnit_zero P.x_pos)

/-- Exact residue of the full-window reflected singular channel. -/
theorem reflectedFullWindowSingularPoleUnit_zero
    (P : ReflectedBiHeatRegulator) :
    reflectedFullWindowSingularPoleUnit P 0 =
      ((heatCoeffSum P.x : ℝ) : ℂ) := by
  rw [reflectedFullWindowSingularPoleUnit, reflectedGammaCoefficient_zero,
    heatMomentPoleUnit_zero, heatMultiplier_zero_eq_heatCoeffSum P.x_pos]
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- Away from the pole, the filled unit is exactly epsilon times the full-window singular
channel. -/
theorem reflectedFullWindowSingularPoleUnit_eq_mul
    (P : ReflectedBiHeatRegulator) {epsilon : ℂ} (hepsilon : 0 < epsilon.re) :
    reflectedFullWindowSingularPoleUnit P epsilon =
      epsilon * reflectedGammaCoefficient P.z epsilon *
        heatMoment P.x (epsilon - 1) := by
  rw [reflectedFullWindowSingularPoleUnit,
    heatMomentPoleUnit_eq_mul_heatMoment P.x_pos hepsilon]
  ring

/-- Exact full-window singular finite part: derivative of its pole-filled analytic unit. -/
noncomputable def reflectedFullWindowSingularFinitePart
    (P : ReflectedBiHeatRegulator) : ℂ :=
  deriv (reflectedFullWindowSingularPoleUnit P) 0

/-- Closed formula for the exact full-window singular finite part. -/
theorem reflectedFullWindowSingularFinitePart_eq
    (P : ReflectedBiHeatRegulator) :
    reflectedFullWindowSingularFinitePart P =
      ((heatCoeffSum P.x : ℝ) : ℂ) *
          ((Real.log Real.pi : ℂ) -
            (Complex.digamma (1 - P.z) + Complex.digamma P.z) / 2) +
        (Real.pi : ℂ) * heatMomentRegularMellin P.x 0 := by
  have hC := differentiableAt_reflectedGammaCoefficient_zero P
  have hH := differentiableAt_heatMomentPoleUnit_zero P.x_pos
  rw [reflectedFullWindowSingularFinitePart]
  change deriv
    ((reflectedGammaCoefficient P.z) * (heatMomentPoleUnit P.x)) 0 = _
  rw [deriv_mul hC hH,
    deriv_reflectedGammaCoefficient_zero,
    deriv_heatMomentPoleUnit_zero P.x_pos,
    reflectedGammaCoefficient_zero,
    heatMomentPoleUnit_zero,
    heatMultiplier_zero_eq_heatCoeffSum P.x_pos]
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

/-! ## Exact Gaussian/remainder decomposition -/

/-- The real Poisson form separates the central Gaussian from the off-centre remainder. -/
theorem heatMultiplier_eq_gaussian_add_remainder {x : ℝ} (hx : 0 < x) (theta : ℝ) :
    heatMultiplier x theta =
      ((x ^ (-(1 : ℝ) / 2) *
        (Real.exp (-(theta ^ 2 / (4 * Real.pi * x))) + heatRemainder x theta) : ℝ) : ℂ) := by
  rw [heatMultiplier_eq_ofReal hx, tsum_heatGauss_split hx theta, heatGauss]
  congr 3
  ring

/-- At the pole, the regular Mellin term is the divided-difference integral itself. -/
theorem pi_mul_heatMomentRegularMellin_zero (x : ℝ) :
    (Real.pi : ℂ) * heatMomentRegularMellin x 0 =
      ∫ theta in Ioc (0 : ℝ) Real.pi,
        (heatMultiplier x theta - heatMultiplier x 0) / (theta : ℂ) := by
  rw [heatMomentRegularMellin]
  have hintegral :
      (∫ theta in Ioc (0 : ℝ) Real.pi,
          (theta : ℂ) ^ (0 : ℂ) * heatMultiplierDivided x theta) =
        ∫ theta in Ioc (0 : ℝ) Real.pi,
          (heatMultiplier x theta - heatMultiplier x 0) / (theta : ℂ) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro theta htheta
    simp [heatMultiplierDivided, htheta.1.ne', Complex.cpow_zero]
  rw [hintegral]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- Pointwise divided-difference split into the central Gaussian and Poisson remainder. -/
theorem heatMultiplier_dividedDifference_eq_gaussian_add_remainder
    {x theta : ℝ} (hx : 0 < x) (htheta : theta ≠ 0) :
    (heatMultiplier x theta - heatMultiplier x 0) / (theta : ℂ) =
      ((x ^ (-(1 : ℝ) / 2) *
        ((Real.exp (-(theta ^ 2 / (4 * Real.pi * x))) - 1) / theta +
          (heatRemainder x theta - heatRemainder x 0) / theta) : ℝ) : ℂ) := by
  rw [heatMultiplier_eq_gaussian_add_remainder hx theta,
    heatMultiplier_eq_gaussian_add_remainder hx 0]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, neg_zero, Real.exp_zero]
  push_cast
  field_simp
  ring

/-- The Poisson remainder is continuous in phase. -/
theorem continuous_heatRemainder {x : ℝ} (hx : 0 < x) :
    Continuous (heatRemainder x) := by
  have hmul : x ^ ((1 : ℝ) / 2) * x ^ (-(1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hx]
    norm_num
  have heq : heatRemainder x = fun theta : ℝ =>
      x ^ ((1 : ℝ) / 2) * (heatMultiplier x theta).re -
        Real.exp (-(theta ^ 2 / (4 * Real.pi * x))) := by
    funext theta
    have hreal := congrArg Complex.re
      (heatMultiplier_eq_gaussian_add_remainder hx theta)
    simp only [ofReal_re] at hreal
    rw [hreal]
    calc
      heatRemainder x theta =
          (x ^ ((1 : ℝ) / 2) * x ^ (-(1 : ℝ) / 2)) *
              (Real.exp (-(theta ^ 2 / (4 * Real.pi * x))) +
                heatRemainder x theta) -
            Real.exp (-(theta ^ 2 / (4 * Real.pi * x))) := by rw [hmul]; ring
      _ = _ := by ring
  rw [heq]
  exact (continuous_const.mul
      (Complex.continuous_re.comp (continuous_heatMultiplier hx))).sub
    (Real.continuous_exp.comp
      (((continuous_id.pow 2).div_const (4 * Real.pi * x)).neg))

/-- The Gaussian divided difference is uniformly bounded on the phase window. -/
theorem abs_gaussianDivided_le {x theta : ℝ} (hx : 0 < x)
    (htheta0 : 0 < theta) (hthetaPi : theta ≤ Real.pi) :
    |(Real.exp (-(theta ^ 2 / (4 * Real.pi * x))) - 1) / theta| ≤ 1 / (4 * x) := by
  let u : ℝ := theta ^ 2 / (4 * Real.pi * x)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hexpLe : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hlinear : 1 - Real.exp (-u) ≤ u := by
    linarith [Real.add_one_le_exp (-u)]
  have huLe : u ≤ theta / (4 * x) := by
    dsimp [u]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * Real.pi * x)
      (by positivity : (0 : ℝ) < 4 * x)).mpr
    have hsquare : theta ^ 2 ≤ theta * Real.pi := by nlinarith
    calc
      theta ^ 2 * (4 * x) ≤ (theta * Real.pi) * (4 * x) :=
        mul_le_mul_of_nonneg_right hsquare (by positivity)
      _ = theta * (4 * Real.pi * x) := by ring
  rw [abs_div, abs_of_pos htheta0, abs_of_nonpos (sub_nonpos.mpr hexpLe)]
  rw [show -(Real.exp (-u) - 1) = 1 - Real.exp (-u) by ring]
  rw [div_le_iff₀ htheta0]
  calc
    1 - Real.exp (-u) ≤ u := hlinear
    _ ≤ theta / (4 * x) := huLe
    _ = (1 / (4 * x)) * theta := by ring

/-- The Gaussian divided difference is integrable across the logarithmic endpoint. -/
theorem intervalIntegrable_gaussianDivided {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun theta : ℝ =>
      (Real.exp (-(theta ^ 2 / (4 * Real.pi * x))) - 1) / theta)
      volume 0 Real.pi := by
  apply GaloisForLFunctions.HTGeometry.intervalIntegrable_of_continuousOn_Ioo_of_bounded
    Real.pi_pos.le
  · exact ((Real.continuous_exp.comp
      (((continuous_id.pow 2).div_const (4 * Real.pi * x)).neg)).sub
        continuous_const).continuousOn.div continuousOn_id
          (fun theta htheta => htheta.1.ne')
  · intro theta htheta
    exact abs_gaussianDivided_le hx htheta.1 htheta.2.le

/-- The Poisson-remainder divided difference is integrable with its explicit derivative bound. -/
theorem intervalIntegrable_heatRemainderDivided {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    IntervalIntegrable (fun theta : ℝ =>
      (heatRemainder x theta - heatRemainder x 0) / theta)
      volume 0 Real.pi := by
  apply GaloisForLFunctions.HTGeometry.intervalIntegrable_of_continuousOn_Ioo_of_bounded
    Real.pi_pos.le
  · exact ((continuous_heatRemainder hx).sub continuous_const).continuousOn.div
      continuousOn_id (fun theta htheta => htheta.1.ne')
  · intro theta htheta
    rw [abs_div, abs_of_pos htheta.1]
    apply (div_le_iff₀ htheta.1).mpr
    simpa [mul_comm] using
      abs_heatRemainder_sub_zero_le hx hx1 htheta.1.le htheta.2.le

/-- Central Gaussian contribution to the regular Mellin value. -/
noncomputable def gaussianDividedIntegral (x : ℝ) : ℝ :=
  ∫ theta in Ioc (0 : ℝ) Real.pi,
    (Real.exp (-(theta ^ 2 / (4 * Real.pi * x))) - 1) / theta

/-- Off-centre Poisson contribution to the regular Mellin value. -/
noncomputable def heatRemainderDividedIntegral (x : ℝ) : ℝ :=
  ∫ theta in Ioc (0 : ℝ) Real.pi,
    (heatRemainder x theta - heatRemainder x 0) / theta

/-- Exact decomposition of the regular Mellin value into Gaussian and Poisson-remainder heads. -/
theorem pi_mul_heatMomentRegularMellin_zero_eq_split
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (Real.pi : ℂ) * heatMomentRegularMellin x 0 =
      ((x ^ (-(1 : ℝ) / 2) *
        (gaussianDividedIntegral x + heatRemainderDividedIntegral x) : ℝ) : ℂ) := by
  have hg : IntegrableOn (fun theta : ℝ =>
      (Real.exp (-(theta ^ 2 / (4 * Real.pi * x))) - 1) / theta)
      (Ioc (0 : ℝ) Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mp
      (intervalIntegrable_gaussianDivided hx)
  have hr : IntegrableOn (fun theta : ℝ =>
      (heatRemainder x theta - heatRemainder x 0) / theta)
      (Ioc (0 : ℝ) Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mp
      (intervalIntegrable_heatRemainderDivided hx hx1)
  rw [pi_mul_heatMomentRegularMellin_zero]
  calc
    (∫ theta in Ioc (0 : ℝ) Real.pi,
        (heatMultiplier x theta - heatMultiplier x 0) / (theta : ℂ)) =
        ∫ theta in Ioc (0 : ℝ) Real.pi,
          ((x ^ (-(1 : ℝ) / 2) *
            ((Real.exp (-(theta ^ 2 / (4 * Real.pi * x))) - 1) / theta +
              (heatRemainder x theta - heatRemainder x 0) / theta) : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro theta htheta
      exact heatMultiplier_dividedDifference_eq_gaussian_add_remainder hx htheta.1.ne'
    _ = ((∫ theta in Ioc (0 : ℝ) Real.pi,
        x ^ (-(1 : ℝ) / 2) *
          ((Real.exp (-(theta ^ 2 / (4 * Real.pi * x))) - 1) / theta +
            (heatRemainder x theta - heatRemainder x 0) / theta) : ℝ) : ℂ) := by
      exact integral_ofReal
    _ = _ := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add hg hr]
      rfl

/-- The exact theta residue is the central Gaussian residue plus the phase-zero Poisson tail. -/
theorem heatCoeffSum_eq_invSqrt_mul_one_add_remainder {x : ℝ} (hx : 0 < x) :
    heatCoeffSum x = x ^ (-(1 : ℝ) / 2) * (1 + heatRemainder x 0) := by
  have h := heatMultiplier_eq_gaussian_add_remainder hx 0
  rw [heatMultiplier_zero_eq_heatCoeffSum hx] at h
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, neg_zero,
    Real.exp_zero] at h
  exact_mod_cast h

/-- Terminal exponential-integral tail in the Gaussian logarithmic finite part. -/
noncomputable def gaussianLogTail (x : ℝ) : ℝ :=
  ∫ t in Ioi (Real.pi / (4 * x)), Real.exp (-t) / t

theorem log_pi_add_gaussianDividedIntegral_eq
    {x : ℝ} (hx : 0 < x) (hxUpper : x ≤ Real.pi / 4) :
    Real.log Real.pi + gaussianDividedIntegral x =
      (Real.log (4 * Real.pi * x) - Real.eulerMascheroniConstant) / 2 -
        gaussianLogTail x / 2 := by
  simpa [gaussianDividedIntegral, gaussianLogTail] using
    gaussianLogFinitePart_eq_tail hx hxUpper

/-- Exact comparison between the canonical full-window finite part and the whole-line Gaussian
anomaly.  Every discrepancy is an explicit exponentially small Poisson or `E₁` tail. -/
theorem reflectedFullWindowSingularFinitePart_eq_gaussian_add_correction
    (P : ReflectedBiHeatRegulator) (hx1 : P.x ≤ 1)
    (hxUpper : P.x ≤ Real.pi / 4) :
    reflectedFullWindowSingularFinitePart P =
      deriv (reflectedSingularPoleUnit P) 0 +
        ((P.x ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
          (((heatRemainder P.x 0 : ℝ) : ℂ) *
              ((Real.log Real.pi : ℂ) -
                (Complex.digamma (1 - P.z) + Complex.digamma P.z) / 2) +
            (heatRemainderDividedIntegral P.x : ℝ) -
            (gaussianLogTail P.x : ℝ) / 2) := by
  have hthetaR := heatCoeffSum_eq_invSqrt_mul_one_add_remainder P.x_pos
  have hthetaC : ((heatCoeffSum P.x : ℝ) : ℂ) =
      (((P.x ^ (-(1 : ℝ) / 2) * (1 + heatRemainder P.x 0) : ℝ)) : ℂ) := by
    exact_mod_cast hthetaR
  have hgaussR := log_pi_add_gaussianDividedIntegral_eq P.x_pos hxUpper
  have hscaleC :
      (((Real.log (4 * Real.pi * P.x) - Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ) =
        (Real.log Real.pi : ℂ) + (gaussianDividedIntegral P.x : ℝ) +
          (gaussianLogTail P.x : ℝ) / 2 := by
    exact_mod_cast (by linarith [hgaussR] :
      (Real.log (4 * Real.pi * P.x) - Real.eulerMascheroniConstant) / 2 =
        Real.log Real.pi + gaussianDividedIntegral P.x + gaussianLogTail P.x / 2)
  have hsqrt := GaloisForLFunctions.HTGeometry.rpow_neg_half_eq_inv_sqrt P.x_pos.le
  have hfactor : (1 / (2 * Real.sqrt P.x) : ℂ) =
      ((P.x ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) / 2 := by
    rw [hsqrt]
    push_cast
    ring
  have hderiv :
      deriv (reflectedSingularPoleUnit P) 0 =
        ((P.x ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
          ((Real.log Real.pi : ℂ) + (gaussianDividedIntegral P.x : ℝ) +
            (gaussianLogTail P.x : ℝ) / 2 -
            (Complex.digamma (1 - P.z) + Complex.digamma P.z) / 2) := by
    rw [deriv_reflectedSingularPoleUnit_zero_eq_anomaly, hfactor]
    rw [show (Real.log (4 * Real.pi * P.x) : ℂ) -
          (Real.eulerMascheroniConstant : ℂ) =
        (((Real.log (4 * Real.pi * P.x) - Real.eulerMascheroniConstant : ℝ)) : ℂ) by
          push_cast; ring]
    rw [show (((Real.log (4 * Real.pi * P.x) - Real.eulerMascheroniConstant : ℝ)) : ℂ) =
        2 * (((Real.log (4 * Real.pi * P.x) - Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ) by
          push_cast; ring,
      hscaleC]
    ring
  rw [reflectedFullWindowSingularFinitePart_eq,
    pi_mul_heatMomentRegularMellin_zero_eq_split P.x_pos hx1,
    hthetaC, hderiv]
  push_cast
  ring

/-- Explicit exponentially small discrepancy between the exact circle finite part and its
whole-line Gaussian model. -/
noncomputable def reflectedFullWindowSingularCorrection (z : ℂ) (x : ℝ) : ℂ :=
  ((x ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
    (((heatRemainder x 0 : ℝ) : ℂ) *
        ((Real.log Real.pi : ℂ) -
          (Complex.digamma (1 - z) + Complex.digamma z) / 2) +
      (heatRemainderDividedIntegral x : ℝ) -
      (gaussianLogTail x : ℝ) / 2)

/-- Concise exact form of the full-window/Gaussian comparison. -/
theorem reflectedFullWindowSingularFinitePart_eq_gaussian_add_explicitCorrection
    (P : ReflectedBiHeatRegulator) (hx1 : P.x ≤ 1)
    (hxUpper : P.x ≤ Real.pi / 4) :
    reflectedFullWindowSingularFinitePart P =
      deriv (reflectedSingularPoleUnit P) 0 +
        reflectedFullWindowSingularCorrection P.z P.x := by
  simpa [reflectedFullWindowSingularCorrection] using
    reflectedFullWindowSingularFinitePart_eq_gaussian_add_correction P hx1 hxUpper

/-- Uniform derivative-tail bound for the divided Poisson correction. -/
theorem abs_heatRemainderDividedIntegral_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    |heatRemainderDividedIntegral x| ≤
      (3 / (2 * x) * Real.exp (-(Real.pi / (4 * x))) * heatTailDerivativeConst) *
        Real.pi := by
  rw [heatRemainderDividedIntegral,
    ← intervalIntegral.integral_of_le Real.pi_pos.le, ← Real.norm_eq_abs]
  calc
    ‖∫ theta in (0 : ℝ)..Real.pi,
        (heatRemainder x theta - heatRemainder x 0) / theta‖
        ≤ (3 / (2 * x) * Real.exp (-(Real.pi / (4 * x))) *
            heatTailDerivativeConst) * |Real.pi - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun theta htheta => by
        have hthetaIoc : theta ∈ Ioc (0 : ℝ) Real.pi := by
          simpa [uIoc_of_le Real.pi_pos.le] using htheta
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hthetaIoc.1]
        apply (div_le_iff₀ hthetaIoc.1).mpr
        simpa [mul_comm] using
          abs_heatRemainder_sub_zero_le hx hx1 hthetaIoc.1.le hthetaIoc.2
    _ = _ := by rw [sub_zero, abs_of_pos Real.pi_pos]

/-- The terminal `E₁` tail is bounded by its first exponential. -/
theorem abs_gaussianLogTail_le {x : ℝ} (hx : 0 < x) (hxUpper : x ≤ Real.pi / 4) :
    |gaussianLogTail x| ≤ Real.exp (-(Real.pi / (4 * x))) := by
  rw [gaussianLogTail]
  apply abs_integral_exp_neg_div_Ioi_le
  apply (le_div_iff₀ (by positivity : 0 < 4 * x)).mpr
  nlinarith

/-- The phase-zero Poisson tail remains negligible after inverse-square-root scaling. -/
theorem tendsto_invSqrtScale_mul_heatRemainder_zero :
    Tendsto (fun x : ℝ => x ^ (-(1 : ℝ) / 2) * heatRemainder x 0)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hdecay : Tendsto
      (fun x : ℝ => x ^ (-(1 : ℝ) / 2) *
        Real.exp (-(Real.pi / 4 / x))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert tendsto_rpow_neg_mul_exp (a := Real.pi / 4) (by positivity) (1 / 2) using 1 <;>
      ring
  have hmajor := hdecay.mul_const heatTailConst
  rw [zero_mul] at hmajor
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx hx1
  have hx0 : 0 < x := hx
  have hdiv : Real.pi / (4 * x) = Real.pi / 4 / x := by
    field_simp
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.rpow_nonneg hx0.le _) (heatRemainder_nonneg x 0))]
  calc
    x ^ (-(1 : ℝ) / 2) * heatRemainder x 0
        ≤ x ^ (-(1 : ℝ) / 2) *
            (Real.exp (-(Real.pi / (4 * x))) * heatTailConst) :=
      mul_le_mul_of_nonneg_left (heatRemainder_zero_le hx0 hx1.2.le)
        (Real.rpow_nonneg hx0.le _)
    _ = (x ^ (-(1 : ℝ) / 2) * Real.exp (-(Real.pi / 4 / x))) *
          heatTailConst := by rw [hdiv]; ring

/-- The terminal `E₁` tail remains negligible after inverse-square-root scaling. -/
theorem tendsto_invSqrtScale_mul_gaussianLogTail :
    Tendsto (fun x : ℝ => x ^ (-(1 : ℝ) / 2) * gaussianLogTail x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hdecay : Tendsto
      (fun x : ℝ => x ^ (-(1 : ℝ) / 2) *
        Real.exp (-(Real.pi / 4 / x))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert tendsto_rpow_neg_mul_exp (a := Real.pi / 4) (by positivity) (1 / 2) using 1 <;>
      ring
  refine squeeze_zero_norm' ?_ hdecay
  filter_upwards [self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < Real.pi / 4)] with x hx hxUpper
  have hx0 : 0 < x := hx
  have hdiv : Real.pi / (4 * x) = Real.pi / 4 / x := by
    field_simp
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx0.le _)
  simpa [hdiv] using abs_gaussianLogTail_le hx0 hxUpper.2.le

/-- The divided Poisson correction remains negligible after inverse-square-root scaling. -/
theorem tendsto_invSqrtScale_mul_heatRemainderDividedIntegral :
    Tendsto (fun x : ℝ => x ^ (-(1 : ℝ) / 2) * heatRemainderDividedIntegral x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hdecay : Tendsto
      (fun x : ℝ => x ^ (-(3 : ℝ) / 2) *
        Real.exp (-(Real.pi / 4 / x))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert tendsto_rpow_neg_mul_exp (a := Real.pi / 4) (by positivity) (3 / 2) using 1 <;>
      ring
  have hmajor := hdecay.mul_const
    ((3 / 2) * heatTailDerivativeConst * Real.pi)
  rw [zero_mul] at hmajor
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx hx1
  have hx0 : 0 < x := hx
  have hdiv : Real.pi / (4 * x) = Real.pi / 4 / x := by
    field_simp
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  calc
    x ^ (-(1 : ℝ) / 2) * |heatRemainderDividedIntegral x|
        ≤ x ^ (-(1 : ℝ) / 2) *
            ((3 / (2 * x) * Real.exp (-(Real.pi / (4 * x))) *
                heatTailDerivativeConst) * Real.pi) :=
      mul_le_mul_of_nonneg_left (abs_heatRemainderDividedIntegral_le hx0 hx1.2.le)
        (Real.rpow_nonneg hx0.le _)
    _ = (x ^ (-(3 : ℝ) / 2) * Real.exp (-(Real.pi / 4 / x))) *
          ((3 / 2) * heatTailDerivativeConst * Real.pi) := by
      rw [show 3 / (2 * x) = (3 / 2) * x⁻¹ by field_simp]
      calc
        x ^ (-(1 : ℝ) / 2) *
              ((3 / 2 * x⁻¹ * Real.exp (-(Real.pi / (4 * x))) *
                heatTailDerivativeConst) * Real.pi) =
            (x ^ (-(1 : ℝ) / 2) * x⁻¹) *
              Real.exp (-(Real.pi / (4 * x))) *
                ((3 / 2) * heatTailDerivativeConst * Real.pi) := by ring
        _ = _ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hx0, hdiv]
          congr 3
          ring

/-- Exact full-window correction vanishes at Gaussian scale. -/
theorem tendsto_reflectedFullWindowSingularCorrection_zero (z : ℂ) :
    Tendsto (fun x : ℝ => reflectedFullWindowSingularCorrection z x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let A : ℂ := (Real.log Real.pi : ℂ) -
    (Complex.digamma (1 - z) + Complex.digamma z) / 2
  have hR := tendsto_invSqrtScale_mul_heatRemainder_zero.ofReal
  have hI := tendsto_invSqrtScale_mul_heatRemainderDividedIntegral.ofReal
  have hT := tendsto_invSqrtScale_mul_gaussianLogTail.ofReal
  have hcombined := (hR.mul_const A).add hI |>.sub (hT.div_const (2 : ℂ))
  have hcombined0 : Tendsto (fun x : ℝ =>
      ((x ^ (-(1 : ℝ) / 2) * heatRemainder x 0 : ℝ) : ℂ) * A +
        ((x ^ (-(1 : ℝ) / 2) * heatRemainderDividedIntegral x : ℝ) : ℂ) -
        ((x ^ (-(1 : ℝ) / 2) * gaussianLogTail x : ℝ) : ℂ) / 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hcombined
  refine hcombined0.congr' ?_
  filter_upwards with x
  dsimp only [A]
  rw [reflectedFullWindowSingularCorrection]
  push_cast
  ring

end

end RHTower

import GaloisForLFunctions.RHTower.CCMFirstClockLandauNormal

/-!
# Infinite-rank analytic first-clock continuation

The reciprocal-square endpoint-cancellation law is uniformized on every half-radius disk centered
on the positive Laplace axis.  The complete multiplicity-exact Xi divisor then converges normally
there, so its first-clock continuation is holomorphic at every positive real point.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Every point of a half-radius disk about a positive real point has real part strictly larger
than half the center. -/
theorem re_lower_of_mem_firstClock_ball
    {r : ℝ} (_hr : 0 < r) {s : ℂ}
    (hs : s ∈ Metric.ball (r : ℂ) (r / 2)) :
    r / 2 < s.re := by
  have hnorm : ‖s - (r : ℂ)‖ < r / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hs
  have hre : |s.re - r| ≤ ‖s - (r : ℂ)‖ := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using
      Complex.abs_re_le_norm (s - (r : ℂ))
  linarith [neg_le_abs (s.re - r)]

private theorem mem_firstClock_cone_of_mem_ball
    {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : s ∈ Metric.ball (r : ℂ) (r / 2)) :
    0 < s.re ∧ |s.im| ≤ 8 * s.re :=
  closedBall_real_axis_subset_ccmFirstClockLaplaceCone hr
    (Metric.ball_subset_closedBall hs)

private theorem norm_inv_sub_le_twenty_div
    {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : s ∈ Metric.ball (r : ℂ) (r / 2))
    (q : XiZeroCopy) {u : ℝ} (hu : 0 ≤ u) :
    ‖1 / (s - I * xiSpectralPoint q * (u : ℂ))‖ ≤ 20 / r := by
  have hcone := mem_firstClock_cone_of_mem_ball hr hs
  have hsep := ccmFirstClockLaplaceCone_norm_sub hcone.1 hcone.2 q hu
  have hdenpos : 0 < ‖s - I * xiSpectralPoint q * (u : ℂ)‖ := by
    have : 0 < s.re / 10 := div_pos hcone.1 (by norm_num)
    exact this.trans_le hsep
  rw [norm_div, norm_one]
  apply (div_le_div_iff₀ hdenpos hr).2
  have hre := re_lower_of_mem_firstClock_ball hr hs
  nlinarith

private theorem norm_inv_add_le_twenty_div
    {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : s ∈ Metric.ball (r : ℂ) (r / 2))
    (q : XiZeroCopy) {u : ℝ} (hu : 0 ≤ u) :
    ‖1 / (s + I * xiSpectralPoint q * (u : ℂ))‖ ≤ 20 / r := by
  have hcone := mem_firstClock_cone_of_mem_ball hr hs
  have hsep := ccmFirstClockLaplaceCone_norm_add hcone.1 hcone.2 q hu
  have hdenpos : 0 < ‖s + I * xiSpectralPoint q * (u : ℂ)‖ := by
    have : 0 < s.re / 10 := div_pos hcone.1 (by norm_num)
    exact this.trans_le hsep
  rw [norm_div, norm_one]
  apply (div_le_div_iff₀ hdenpos hr).2
  have hre := re_lower_of_mem_firstClock_ball hr hs
  nlinarith

private theorem hasDerivAt_inv_sub_cube
    {a s : ℂ} (hne : s - a ≠ 0) :
    HasDerivAt (fun w : ℂ => 1 / (w - a) ^ 3)
      (-3 / (s - a) ^ 4) s := by
  have hp := ((hasDerivAt_id s).sub_const a).pow 3
  have hi := hp.inv (pow_ne_zero 3 hne)
  have hi' : HasDerivAt
      (fun w : ℂ => 1 / (w - a) ^ 3)
      (-(3 * (s - a) ^ 2) / ((s - a) ^ 3) ^ 2) s := by
    have hfun : (fun w : ℂ => 1 / (w - a) ^ 3) =
        fun w : ℂ => ((w - a) ^ 3)⁻¹ := by
      funext w
      rw [one_div]
    rw [hfun]
    refine hi.congr_deriv ?_
    norm_num [id_eq]
    try ring
  convert hi' using 1
  field_simp [hne]

/-- Every single cubic first-clock continuation atom is holomorphic throughout each universal
positive-axis disk. -/
theorem differentiableOn_ccmFirstClockLaplaceContinuationAtom_ball
    {r : ℝ} (hr : 0 < r) (q : XiZeroCopy) :
    DifferentiableOn ℂ
      (fun s : ℂ =>
        ccmFirstClockLaplaceContinuationAtom s (xiSpectralPoint q))
      (Metric.ball (r : ℂ) (r / 2)) := by
  intro s hs
  let z : ℂ := xiSpectralPoint q
  let F : ℂ → ℝ → ℂ := fun w u =>
    Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
      (1 / (w - I * z * (u : ℂ)) ^ 3 +
        1 / (w + I * z * (u : ℂ)) ^ 3)
  let F' : ℂ → ℝ → ℂ := fun w u =>
    Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
      (-3 / (w - I * z * (u : ℂ)) ^ 4 +
        -3 / (w + I * z * (u : ℂ)) ^ 4)
  let bound : ℝ → ℝ := fun _ => 6 * (20 / r) ^ 4
  have hdenSub : ∀ w ∈ Metric.ball (r : ℂ) (r / 2),
      ∀ u : ℝ, u ∈ Set.uIcc (0 : ℝ) 1 →
        w - I * z * (u : ℂ) ≠ 0 := by
    intro w hw u hu
    have hcone := mem_firstClock_cone_of_mem_ball hr hw
    have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by simpa using hu
    exact ccmFirstClockLaplaceCone_sub_ne_zero hcone.1 hcone.2 q hu'.1
  have hdenAdd : ∀ w ∈ Metric.ball (r : ℂ) (r / 2),
      ∀ u : ℝ, u ∈ Set.uIcc (0 : ℝ) 1 →
        w + I * z * (u : ℂ) ≠ 0 := by
    intro w hw u hu
    have hcone := mem_firstClock_cone_of_mem_ball hr hw
    have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by simpa using hu
    exact ccmFirstClockLaplaceCone_add_ne_zero hcone.1 hcone.2 q hu'.1
  have hFint : ∀ w ∈ Metric.ball (r : ℂ) (r / 2),
      IntervalIntegrable (F w) volume 0 1 := by
    intro w hw
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : Continuous
      (fun u : ℝ =>
        Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)))).continuousOn.mul
      (((by fun_prop : Continuous
          (fun u : ℝ => (1 : ℂ))) |>.continuousOn.div
        (by fun_prop : Continuous
          (fun u : ℝ => (w - I * z * (u : ℂ)) ^ 3)).continuousOn
        (fun u hu => pow_ne_zero 3 (hdenSub w hw u (by simpa using hu)))).add
       ((by fun_prop : Continuous
          (fun u : ℝ => (1 : ℂ))) |>.continuousOn.div
        (by fun_prop : Continuous
          (fun u : ℝ => (w + I * z * (u : ℂ)) ^ 3)).continuousOn
        (fun u hu => pow_ne_zero 3 (hdenAdd w hw u (by simpa using hu)))))
  have hFmeas : ∀ᶠ w in 𝓝 s,
      AEStronglyMeasurable (F w)
        (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hs] with w hw
    exact (hFint w hw).aestronglyMeasurable_restrict_uIoc
  have hF'int : IntervalIntegrable (F' s) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : Continuous
      (fun u : ℝ =>
        Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)))).continuousOn.mul
      (((by fun_prop : Continuous
          (fun u : ℝ => (-3 : ℂ))) |>.continuousOn.div
        (by fun_prop : Continuous
          (fun u : ℝ => (s - I * z * (u : ℂ)) ^ 4)).continuousOn
        (fun u hu => pow_ne_zero 4 (hdenSub s hs u (by simpa using hu)))).add
       ((by fun_prop : Continuous
          (fun u : ℝ => (-3 : ℂ))) |>.continuousOn.div
        (by fun_prop : Continuous
          (fun u : ℝ => (s + I * z * (u : ℂ)) ^ 4)).continuousOn
        (fun u hu => pow_ne_zero 4 (hdenAdd s hs u (by simpa using hu)))))
  have hbound : ∀ᵐ u ∂volume, u ∈ Set.uIoc (0 : ℝ) 1 →
      ∀ w ∈ Metric.ball (r : ℂ) (r / 2),
        ‖F' w u‖ ≤ bound u := by
    filter_upwards with u
    intro hu w hw
    have hu0 : 0 ≤ u := by
      have hu' : u ∈ Set.Ioc (0 : ℝ) 1 := by simpa using hu
      exact hu'.1.le
    have hsin :
        ‖Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ))‖ ≤ 1 := by
      rw [show (2 * (Real.pi : ℂ)) * (u : ℂ) =
          ((2 * Real.pi * u : ℝ) : ℂ) by
        push_cast
        ring]
      rw [← Complex.ofReal_sin, norm_real, Real.norm_eq_abs]
      exact Real.abs_sin_le_one _
    have hsub := norm_inv_sub_le_twenty_div hr hw q hu0
    have hadd := norm_inv_add_le_twenty_div hr hw q hu0
    have hsub4 :
        ‖(-3 : ℂ) / (w - I * z * (u : ℂ)) ^ 4‖ ≤
          3 * (20 / r) ^ 4 := by
      rw [norm_div, norm_neg, norm_ofNat, norm_pow]
      calc
        3 / ‖w - I * z * (u : ℂ)‖ ^ 4 =
            3 * ‖1 / (w - I * z * (u : ℂ))‖ ^ 4 := by
          rw [one_div, norm_inv, inv_pow]
          ring
        _ ≤ 3 * (20 / r) ^ 4 := by gcongr
    have hadd4 :
        ‖(-3 : ℂ) / (w + I * z * (u : ℂ)) ^ 4‖ ≤
          3 * (20 / r) ^ 4 := by
      rw [norm_div, norm_neg, norm_ofNat, norm_pow]
      calc
        3 / ‖w + I * z * (u : ℂ)‖ ^ 4 =
            3 * ‖1 / (w + I * z * (u : ℂ))‖ ^ 4 := by
          rw [one_div, norm_inv, inv_pow]
          ring
        _ ≤ 3 * (20 / r) ^ 4 := by
          gcongr
    dsimp only [F', bound]
    rw [norm_mul]
    calc
      ‖Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ))‖ *
          ‖-3 / (w - I * z * (u : ℂ)) ^ 4 +
            -3 / (w + I * z * (u : ℂ)) ^ 4‖ ≤
          1 * (3 * (20 / r) ^ 4 + 3 * (20 / r) ^ 4) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add hsub4 hadd4)
      _ = 6 * (20 / r) ^ 4 := by ring
  have hboundInt : IntervalIntegrable bound volume 0 1 := by
    exact continuous_const.intervalIntegrable 0 1
  have hdiff : ∀ᵐ u ∂volume, u ∈ Set.uIoc (0 : ℝ) 1 →
      ∀ w ∈ Metric.ball (r : ℂ) (r / 2),
        HasDerivAt (fun w => F w u) (F' w u) w := by
    filter_upwards with u
    intro hu w hw
    have hu0 : 0 ≤ u := by
      have hu' : u ∈ Set.Ioc (0 : ℝ) 1 := by simpa using hu
      exact hu'.1.le
    have hcone := mem_firstClock_cone_of_mem_ball hr hw
    have hsubNe :=
      ccmFirstClockLaplaceCone_sub_ne_zero hcone.1 hcone.2 q hu0
    have haddNe :=
      ccmFirstClockLaplaceCone_add_ne_zero hcone.1 hcone.2 q hu0
    have hsub := hasDerivAt_inv_sub_cube
      (a := I * z * (u : ℂ)) hsubNe
    have hadd : HasDerivAt
        (fun y : ℂ => 1 / (y + I * z * (u : ℂ)) ^ 3)
        (-3 / (w + I * z * (u : ℂ)) ^ 4) w := by
      have h := hasDerivAt_inv_sub_cube
        (a := -(I * z * (u : ℂ))) (by simpa only [sub_neg_eq_add] using haddNe)
      simpa only [sub_neg_eq_add] using h
    dsimp only [F, F']
    exact (hsub.add hadd).const_mul
      (Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)))
  have hmain :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := bound)
      (Metric.isOpen_ball.mem_nhds hs)
      hFmeas (hFint s hs)
      hF'int.aestronglyMeasurable_restrict_uIoc
      hbound hboundInt hdiff
  have hscaled := hmain.2.const_mul (-(1 / (2 * (Real.pi : ℂ))))
  exact (by
    simpa only [ccmFirstClockLaplaceContinuationAtom, F] using
      hscaled.differentiableAt.differentiableWithinAt)

/-- Explicit locally uniform majorant coefficient for the complete first-clock continuation. -/
def ccmFirstClockBallMajorantConstant (r : ℝ) : ℝ :=
  ‖1 / (4 * (Real.pi : ℂ))‖ *
    (‖(2 * (Real.pi : ℂ))‖ * (44 / r) +
      ‖(2 * (Real.pi : ℂ)) ^ 2‖ * (40 / r))

/-- The reciprocal-square atom bound is uniform on a full positive-axis disk. -/
theorem norm_ccmFirstClockLaplaceContinuationAtom_le_ball
    {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : s ∈ Metric.ball (r : ℂ) (r / 2))
    (q : XiZeroCopy) :
    ‖ccmFirstClockLaplaceContinuationAtom s (xiSpectralPoint q)‖ ≤
      ccmFirstClockBallMajorantConstant r *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  have hcone := mem_firstClock_cone_of_mem_ball hr hs
  have h := norm_ccmFirstClockLaplaceContinuationAtom_le
    hcone.1 hcone.2 q
  have hre := re_lower_of_mem_firstClock_ball hr hs
  have h22 : 22 / s.re ≤ 44 / r := by
    exact (div_le_div_iff₀ hcone.1 hr).2 (by nlinarith)
  have h20 : 20 / s.re ≤ 40 / r := by
    exact (div_le_div_iff₀ hcone.1 hr).2 (by nlinarith)
  calc
    ‖ccmFirstClockLaplaceContinuationAtom s (xiSpectralPoint q)‖ ≤
        (‖1 / (4 * (Real.pi : ℂ))‖ *
          (‖(2 * (Real.pi : ℂ))‖ * (22 / s.re) +
            ‖(2 * (Real.pi : ℂ)) ^ 2‖ * (20 / s.re))) *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := h
    _ ≤ ccmFirstClockBallMajorantConstant r *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by
      dsimp only [ccmFirstClockBallMajorantConstant]
      gcongr

/-- Complete multiplicity-exact analytic continuation of the first-clock Xi divisor. -/
def ccmFirstClockLaplaceContinuation (s : ℂ) : ℂ :=
  ∑' q : XiZeroCopy,
    ccmFirstClockLaplaceContinuationAtom s (xiSpectralPoint q)

/-- **Infinite-rank first-clock normal-convergence law.**  The complete Xi divisor, with analytic
multiplicity and no finite truncation, is holomorphic on every half-radius disk centered on the
positive Laplace axis. -/
theorem differentiableOn_ccmFirstClockLaplaceContinuation_ball
    {r : ℝ} (hr : 0 < r) :
    DifferentiableOn ℂ ccmFirstClockLaplaceContinuation
      (Metric.ball (r : ℂ) (r / 2)) := by
  unfold ccmFirstClockLaplaceContinuation
  apply Complex.differentiableOn_tsum_of_summable_norm
    (u := fun q : XiZeroCopy =>
      ccmFirstClockBallMajorantConstant r *
        (1 / ‖xiSpectralPoint q‖ ^ 2))
  · exact xiSpectralPoint_inv_sq_summable.mul_left
      (ccmFirstClockBallMajorantConstant r)
  · exact differentiableOn_ccmFirstClockLaplaceContinuationAtom_ball hr
  · exact Metric.isOpen_ball
  · intro q s hs
    exact norm_ccmFirstClockLaplaceContinuationAtom_le_ball hr hs q

/-- Every positive point of the real Laplace axis is an analytic germ of the complete
first-clock continuation. -/
theorem analyticAt_ccmFirstClockLaplaceContinuation_positive_real
    {r : ℝ} (hr : 0 < r) :
    AnalyticAt ℂ ccmFirstClockLaplaceContinuation (r : ℂ) :=
  (differentiableOn_ccmFirstClockLaplaceContinuation_ball hr).analyticAt
    (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self (by positivity : 0 < r / 2)))

end

end RHTower

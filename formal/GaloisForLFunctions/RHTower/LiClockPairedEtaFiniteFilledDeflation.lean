import GaloisForLFunctions.RHTower.LiClockPairedEtaFiniteDeflation
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteLaplaceHalfTurn
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCompletedResidual

/-!
# Filled finite eta deflation and exact central traces

The positive finite eta Laplace partition is entire and is nonzero throughout
its centered half-turn phase strip, at every real tilt. The elementary eta
factor is exactly the first finite prefix at `s - 1`. This identity and the
archimedean recurrence give explicit filled deflations after one and two
Gamma shifts, with every completion factor retained.

The filled sources are analytic and nonzero on the closed disks used by the
short-prefix clock proof. Their central logarithmic traces therefore supply
`DiffContOnCl` directly. Literal completion and trace equalities are confined
to regular source germs; no equality of totalized endpoint values is asserted.
The first-prefix second-pole split retains its literal negative residue.

This is source infrastructure for `li-clock-short-prefix-pole-asymptotic.md`.
Contour estimates and asymptotic conclusions belong to the downstream leaves.
-/

open Complex Filter Set Metric Topology RiemannGaussian
namespace RHTower
noncomputable section

private theorem analyticAt_gammaReal_right {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Gammaℝ s := by
  have hd : DifferentiableOn ℂ Gammaℝ {w : ℂ | 0 < w.re} := by
    intro w hw
    exact (differentiableAt_Gammaℝ_of_re_pos hw).differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

/-- Compact finite logarithmic eta measures give entire Laplace partitions. -/
theorem analyticAt_liClockPairedEtaFiniteLaplacePartition_entire (N : ℕ) (s : ℂ) :
    AnalyticAt ℂ (pairedEtaFiniteLaplacePartition N) s := by
  rw [pairedEtaFiniteLaplacePartition_eq_complexMGF_fun]
  exact ProbabilityTheory.analyticAt_complexMGF
    (pairedEtaFinite_re_mem_interior_negId_integrableExpSet N s)

/-- Centered phase positivity excludes finite Laplace zeros at every real tilt. -/
theorem liClockPairedEtaFiniteLaplacePartition_ne_zero {N : ℕ} (hN : 0 < N)
    {s : ℂ} (hphase : |s.im| * Real.log (2 * (N : ℝ)) ≤ Real.pi) :
    pairedEtaFiniteLaplacePartition N s ≠ 0 := by
  intro hzero
  have hsplit := pairedEtaFiniteLaplacePartition_eq_cosine_sub_I_sine N s.re s.im
  rw [Complex.re_add_im, hzero] at hsplit
  have hc : pairedEtaFiniteTiltedCosineMoment N s.re s.im = 0 := by
    have h := congrArg Complex.re hsplit
    simpa using h.symm
  have hs : pairedEtaFiniteTiltedSineMoment N s.re s.im = 0 := by
    have h := congrArg Complex.im hsplit
    simpa using h
  have hpos := pairedEtaFiniteCenteredTiltedCosineMoment_pos_of_phase_le_pi
    hN s.re s.im hphase
  rw [pairedEtaFiniteCenteredTiltedCosineMoment_eq_rotation, hc, hs] at hpos
  simp at hpos

/-- The elementary eta factor is the literal first prefix at the shifted argument. -/
theorem liClockPairedEtaFactor_eq_firstPrefix_shift (s : ℂ) :
    pairedEtaFactor s = pairedEtaCorePartialSum 1 (s - 1) := by
  simp only [pairedEtaFactor, pairedEtaCorePartialSum, Finset.sum_range_one,
    pairedEtaCoreSummand]
  norm_num
  rw [show 1 - s = 1 + (-s) by ring,
    Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]

/-- Exact first-interval Laplace factorization, including the totalized point at one. -/
theorem liClockPairedEtaFactor_eq_shift_mul_firstLaplace (s : ℂ) :
    pairedEtaFactor s = (s - 1) * pairedEtaFiniteLaplacePartition 1 (s - 1) := by
  rw [liClockPairedEtaFactor_eq_firstPrefix_shift,
    pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition]

/-- The filled deflated completion; literal completion equality is used only on regular points. -/
def liClockPairedEtaFiniteFilledDeflation (N : ℕ) (s : ℂ) : ℂ :=
  (-2 * (Real.pi : ℂ)) * Gammaℝ (s + 2) *
    pairedEtaFiniteLaplacePartition N s / pairedEtaFiniteLaplacePartition 1 (s - 1)

/-- The first prefix after two archimedean shifts. -/
def liClockPairedEtaFirstPrefixTwiceFilledDeflation (s : ℂ) : ℂ :=
  (-4 * (Real.pi : ℂ) ^ 2) * Gammaℝ (s + 4) *
    pairedEtaFiniteLaplacePartition 1 s / pairedEtaFiniteLaplacePartition 1 (s - 1)

/-- Central logarithmic trace of the filled deflated source. -/
def liClockPairedEtaFiniteFilledSourceTrace (N : ℕ) (z : ℂ) : ℂ :=
  I * logDeriv (liClockPairedEtaFiniteFilledDeflation N) (1 / 2 + z * I)

/-- Central logarithmic trace of the twice-filled first prefix. -/
def liClockPairedEtaFirstPrefixTwiceFilledSourceTrace (z : ℂ) : ℂ :=
  I * logDeriv liClockPairedEtaFirstPrefixTwiceFilledDeflation (1 / 2 + z * I)

/-- Filled finite source is holomorphic wherever shifted Gamma and the denominator are regular. -/
theorem analyticAt_liClockPairedEtaFiniteFilledDeflation (N : ℕ) {s : ℂ}
    (hgamma : 0 < (s + 2).re)
    (hden : pairedEtaFiniteLaplacePartition 1 (s - 1) ≠ 0) :
    AnalyticAt ℂ (liClockPairedEtaFiniteFilledDeflation N) s := by
  have hg : AnalyticAt ℂ (fun w : ℂ => Gammaℝ (w + 2)) s :=
    (analyticAt_gammaReal_right hgamma).comp (f := fun w : ℂ => w + 2)
      (analyticAt_id.add analyticAt_const)
  have hd : AnalyticAt ℂ (fun w : ℂ => pairedEtaFiniteLaplacePartition 1 (w - 1)) s :=
    (analyticAt_liClockPairedEtaFiniteLaplacePartition_entire 1 (s - 1)).comp
      (f := fun w : ℂ => w - 1) (analyticAt_id.sub analyticAt_const)
  exact ((analyticAt_const.mul hg).mul
    (analyticAt_liClockPairedEtaFiniteLaplacePartition_entire N s)).div hd hden

/-- The filled finite source never vanishes when its three literal factors do not. -/
theorem liClockPairedEtaFiniteFilledDeflation_ne_zero {N : ℕ} {s : ℂ}
    (hgamma : 0 < (s + 2).re)
    (hnum : pairedEtaFiniteLaplacePartition N s ≠ 0)
    (hden : pairedEtaFiniteLaplacePartition 1 (s - 1) ≠ 0) :
    liClockPairedEtaFiniteFilledDeflation N s ≠ 0 := by
  exact div_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    (Complex.Gammaℝ_ne_zero_of_re_pos hgamma)) hnum) hden

/-- The twice-filled first source is holomorphic on its regular shifted domain. -/
theorem analyticAt_liClockPairedEtaFirstPrefixTwiceFilledDeflation {s : ℂ}
    (hgamma : 0 < (s + 4).re)
    (hden : pairedEtaFiniteLaplacePartition 1 (s - 1) ≠ 0) :
    AnalyticAt ℂ liClockPairedEtaFirstPrefixTwiceFilledDeflation s := by
  have hg : AnalyticAt ℂ (fun w : ℂ => Gammaℝ (w + 4)) s :=
    (analyticAt_gammaReal_right hgamma).comp (f := fun w : ℂ => w + 4)
      (analyticAt_id.add analyticAt_const)
  have hd : AnalyticAt ℂ (fun w : ℂ => pairedEtaFiniteLaplacePartition 1 (w - 1)) s :=
    (analyticAt_liClockPairedEtaFiniteLaplacePartition_entire 1 (s - 1)).comp
      (f := fun w : ℂ => w - 1) (analyticAt_id.sub analyticAt_const)
  exact ((analyticAt_const.mul hg).mul
    (analyticAt_liClockPairedEtaFiniteLaplacePartition_entire 1 s)).div hd hden

/-- Nonzero literal factors give a nonzero twice-filled first source. -/
theorem liClockPairedEtaFirstPrefixTwiceFilledDeflation_ne_zero {s : ℂ}
    (hgamma : 0 < (s + 4).re)
    (hnum : pairedEtaFiniteLaplacePartition 1 s ≠ 0)
    (hden : pairedEtaFiniteLaplacePartition 1 (s - 1) ≠ 0) :
    liClockPairedEtaFirstPrefixTwiceFilledDeflation s ≠ 0 := by
  exact div_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    (Complex.Gammaℝ_ne_zero_of_re_pos hgamma)) hnum) hden


/-- Filled deflation agrees with the full literal completion at regular strip points. -/
theorem liClockPairedEtaFiniteFilledDeflation_eq_completion_mul_laplace
    (N : ℕ) {s : ℂ} (hlower : 0 < s.re) (hupper : s.re < 1) :
    liClockPairedEtaFiniteFilledDeflation N s =
      pairedEtaXiCompletionFactor s * pairedEtaFiniteLaplacePartition N s := by
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hlower
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s = 1 := sub_eq_zero.mp h
    subst s
    norm_num at hupper
  have hd : pairedEtaFiniteLaplacePartition 1 (s - 1) ≠ 0 := by
    intro h
    have hf : pairedEtaFactor s ≠ 0 := pairedEtaFactor_ne_zero_of_re_lt_one hupper
    rw [liClockPairedEtaFactor_eq_shift_mul_firstLaplace, h, mul_zero] at hf
    exact hf rfl
  unfold liClockPairedEtaFiniteFilledDeflation pairedEtaXiCompletionFactor
    pairedEtaXiCompletionNumerator
  rw [liClockPairedEtaFactor_eq_shift_mul_firstLaplace,
    GaloisForLFunctions.gammaReal_shift_two hs0]
  field_simp [hs0, hs1, hd, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

/-- Literal and filled deflated traces share the same regular source germ. -/
theorem liClockPairedEtaFiniteDeflatedSourceTrace_eq_filled
    (N : ℕ) {z : ℂ} (hlower : 0 < (1 / 2 + z * I).re)
    (hupper : (1 / 2 + z * I).re < 1) :
    liClockPairedEtaFiniteDeflatedSourceTrace N z =
      liClockPairedEtaFiniteFilledSourceTrace N z := by
  let s : ℂ := 1 / 2 + z * I
  have heq : (fun w : ℂ => pairedEtaXiCompletionFactor w *
      pairedEtaFiniteLaplacePartition N w) =ᶠ[𝓝 s]
      liClockPairedEtaFiniteFilledDeflation N := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hlower,
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hupper] with w hwl hwu
    exact (liClockPairedEtaFiniteFilledDeflation_eq_completion_mul_laplace N hwl hwu).symm
  unfold liClockPairedEtaFiniteDeflatedSourceTrace liClockPairedEtaFiniteFilledSourceTrace
  change I * logDeriv (fun w : ℂ => pairedEtaXiCompletionFactor w *
    pairedEtaFiniteLaplacePartition N w) s =
    I * logDeriv (liClockPairedEtaFiniteFilledDeflation N) s
  rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]

/-- A second Gamma shift removes the first remaining archimedean pole exactly. -/
theorem liClockPairedEtaFirstPrefixFilledDeflation_eq_twice_div_add_two {s : ℂ}
    (hs : s + 2 ≠ 0) :
    liClockPairedEtaFiniteFilledDeflation 1 s =
      liClockPairedEtaFirstPrefixTwiceFilledDeflation s / (s + 2) := by
  have hg := GaloisForLFunctions.gammaReal_shift_two hs
  rw [show s + 2 + 2 = s + 4 by ring] at hg
  unfold liClockPairedEtaFiniteFilledDeflation liClockPairedEtaFirstPrefixTwiceFilledDeflation
  rw [hg]
  by_cases hd : pairedEtaFiniteLaplacePartition 1 (s - 1) = 0
  · simp [hd]
  · field_simp [hd, hs, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring


private theorem firstLaplace_shift_ne_zero_of_regular {s : ℂ} (hupper : s.re < 1) :
    pairedEtaFiniteLaplacePartition 1 (s - 1) ≠ 0 := by
  intro h
  have hf : pairedEtaFactor s ≠ 0 := pairedEtaFactor_ne_zero_of_re_lt_one hupper
  rw [liClockPairedEtaFactor_eq_shift_mul_firstLaplace, h, mul_zero] at hf
  exact hf rfl

/-- Exact second-pole split of the literal first-prefix deflated trace on its regular germ. -/
theorem liClockPairedEtaFirstPrefixDeflatedSourceTrace_eq_secondPole_add_twiceFilled
    {z : ℂ} (hlower : 0 < (1 / 2 + z * I).re)
    (hupper : (1 / 2 + z * I).re < 1)
    (hnum : pairedEtaFiniteLaplacePartition 1 (1 / 2 + z * I) ≠ 0) :
    liClockPairedEtaFiniteDeflatedSourceTrace 1 z =
      -I / (1 / 2 + z * I + 2) + liClockPairedEtaFirstPrefixTwiceFilledSourceTrace z := by
  let s : ℂ := 1 / 2 + z * I
  have hs : s + 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re] at hre
    have : 0 < s.re := hlower
    linarith
  have hg : 0 < (s + 4).re := by
    have : 0 < s.re := hlower
    norm_num [Complex.add_re]
    linarith
  have hd := firstLaplace_shift_ne_zero_of_regular hupper
  have ha := analyticAt_liClockPairedEtaFirstPrefixTwiceFilledDeflation hg hd
  have hn := liClockPairedEtaFirstPrefixTwiceFilledDeflation_ne_zero hg hnum hd
  have heq : liClockPairedEtaFiniteFilledDeflation 1 =ᶠ[𝓝 s]
      (fun w : ℂ => liClockPairedEtaFirstPrefixTwiceFilledDeflation w / (w + 2)) := by
    filter_upwards [(continuousAt_id.add continuousAt_const).eventually_ne hs] with w hw
    exact liClockPairedEtaFirstPrefixFilledDeflation_eq_twice_div_add_two hw
  have hlog : logDeriv (liClockPairedEtaFiniteFilledDeflation 1) s =
      logDeriv (fun w : ℂ => liClockPairedEtaFirstPrefixTwiceFilledDeflation w / (w + 2)) s := by
    rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]
  have hlinear : logDeriv (fun w : ℂ => w + 2) s = 1 / (s + 2) := by
    have hdlin : deriv (fun w : ℂ => w + 2) s = 1 := by
      exact ((hasDerivAt_id s).add_const 2).deriv
    rw [logDeriv_apply, hdlin]
  rw [liClockPairedEtaFiniteDeflatedSourceTrace_eq_filled 1 hlower hupper]
  unfold liClockPairedEtaFiniteFilledSourceTrace liClockPairedEtaFirstPrefixTwiceFilledSourceTrace
  change I * logDeriv (liClockPairedEtaFiniteFilledDeflation 1) s =
    -I / (s + 2) + I * logDeriv liClockPairedEtaFirstPrefixTwiceFilledDeflation s
  rw [hlog, logDeriv_div s hn hs ha.differentiableAt (by fun_prop), hlinear]
  ring

private theorem central_phase_le_norm (z : ℂ) :
    |(1 / 2 + z * I).im| ≤ ‖z‖ := by
  simpa [Complex.mul_im] using Complex.abs_re_le_norm z

private theorem log_two_le_log_two_mul {N : ℕ} (hN : 0 < N) :
    Real.log 2 ≤ Real.log (2 * (N : ℝ)) := by
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  exact Real.log_le_log (by norm_num) (by linarith)

private theorem central_partition_factors {N : ℕ} (hN : 0 < N) {rho : ℝ}
    (hphase : rho * Real.log (2 * (N : ℝ)) < Real.pi) {z : ℂ} (hz : ‖z‖ ≤ rho) :
    pairedEtaFiniteLaplacePartition N (1 / 2 + z * I) ≠ 0 ∧
      pairedEtaFiniteLaplacePartition 1 (1 / 2 + z * I - 1) ≠ 0 := by
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hl : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by linarith)
  have hpn : |(1 / 2 + z * I).im| * Real.log (2 * (N : ℝ)) < Real.pi :=
    (mul_le_mul_of_nonneg_right ((central_phase_le_norm z).trans hz) hl).trans_lt hphase
  constructor
  · exact liClockPairedEtaFiniteLaplacePartition_ne_zero hN hpn.le
  · apply liClockPairedEtaFiniteLaplacePartition_ne_zero (by norm_num : 0 < (1 : ℕ))
    have hp1 := (mul_le_mul_of_nonneg_left (log_two_le_log_two_mul hN)
      (abs_nonneg (1 / 2 + z * I : ℂ).im)).trans hpn.le
    simpa using hp1

/-- Both analyticity and nonvanishing of the filled source hold on the full closed central disk. -/
theorem liClockPairedEtaFiniteFilledDeflation_central_regular {N : ℕ} (hN : 0 < N)
    {rho : ℝ} (hrho : rho < 5 / 2)
    (hphase : rho * Real.log (2 * (N : ℝ)) < Real.pi)
    {z : ℂ} (hz : ‖z‖ ≤ rho) :
    AnalyticAt ℂ (liClockPairedEtaFiniteFilledDeflation N) (1 / 2 + z * I) ∧
      liClockPairedEtaFiniteFilledDeflation N (1 / 2 + z * I) ≠ 0 := by
  have hzi := abs_le.mp ((Complex.abs_im_le_norm z).trans hz)
  have hg : 0 < (1 / 2 + z * I + 2).re := by
    norm_num [Complex.mul_re]
    linarith
  obtain ⟨hn, hd⟩ := central_partition_factors hN hphase hz
  exact ⟨analyticAt_liClockPairedEtaFiniteFilledDeflation N hg hd,
    liClockPairedEtaFiniteFilledDeflation_ne_zero hg hn hd⟩

/-- The filled logarithmic central trace is analytic throughout the larger closed disk. -/
theorem analyticAt_liClockPairedEtaFiniteFilledSourceTrace_of_norm_le {N : ℕ} (hN : 0 < N)
    {rho : ℝ} (hrho : rho < 5 / 2)
    (hphase : rho * Real.log (2 * (N : ℝ)) < Real.pi)
    {z : ℂ} (hz : ‖z‖ ≤ rho) :
    AnalyticAt ℂ (liClockPairedEtaFiniteFilledSourceTrace N) z := by
  obtain ⟨ha, hn⟩ := liClockPairedEtaFiniteFilledDeflation_central_regular hN hrho hphase hz
  have hlog : AnalyticAt ℂ (logDeriv (liClockPairedEtaFiniteFilledDeflation N))
      (1 / 2 + z * I) := ha.deriv.div ha hn
  change AnalyticAt ℂ (fun w : ℂ => I *
    logDeriv (liClockPairedEtaFiniteFilledDeflation N) (1 / 2 + w * I)) z
  exact analyticAt_const.mul (hlog.comp (f := fun w : ℂ => 1 / 2 + w * I)
    (analyticAt_const.add (analyticAt_id.mul analyticAt_const)))

/-- Larger filled-source disks provide the exact interface required by the central sine contour. -/
theorem diffContOnCl_liClockPairedEtaFiniteFilledSourceTrace_ball {N : ℕ} (hN : 0 < N)
    {rho : ℝ} (hrho : rho < 5 / 2)
    (hphase : rho * Real.log (2 * (N : ℝ)) < Real.pi) :
    DiffContOnCl ℂ (liClockPairedEtaFiniteFilledSourceTrace N) (ball (0 : ℂ) rho) := by
  have ha : AnalyticOnNhd ℂ (liClockPairedEtaFiniteFilledSourceTrace N)
      (closedBall (0 : ℂ) rho) := by
    intro z hz
    exact analyticAt_liClockPairedEtaFiniteFilledSourceTrace_of_norm_le hN hrho hphase
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  exact ha.differentiableOn.diffContOnCl_ball (Subset.refl _)

private theorem central_first_partition_factors {z : ℂ} (hz : ‖z‖ ≤ 3) :
    pairedEtaFiniteLaplacePartition 1 (1 / 2 + z * I) ≠ 0 ∧
      pairedEtaFiniteLaplacePartition 1 (1 / 2 + z * I - 1) ≠ 0 := by
  apply central_partition_factors (by norm_num : 0 < (1 : ℕ)) (rho := 3) _ hz
  have hl : Real.log 2 < 1 := by
    have hh := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    norm_num at hh
    exact hh
  norm_num
  linarith [Real.pi_gt_three]

/-- Twice-filled first-prefix source is analytic and nonzero throughout closed central radius three. -/
theorem liClockPairedEtaFirstPrefixTwiceFilledDeflation_central_regular {z : ℂ}
    (hz : ‖z‖ ≤ 3) :
    AnalyticAt ℂ liClockPairedEtaFirstPrefixTwiceFilledDeflation (1 / 2 + z * I) ∧
      liClockPairedEtaFirstPrefixTwiceFilledDeflation (1 / 2 + z * I) ≠ 0 := by
  have hzi := abs_le.mp ((Complex.abs_im_le_norm z).trans hz)
  have hg : 0 < (1 / 2 + z * I + 4).re := by
    norm_num [Complex.mul_re]
    linarith
  obtain ⟨hn, hd⟩ := central_first_partition_factors hz
  exact ⟨analyticAt_liClockPairedEtaFirstPrefixTwiceFilledDeflation hg hd,
    liClockPairedEtaFirstPrefixTwiceFilledDeflation_ne_zero hg hn hd⟩

/-- The twice-filled first-prefix logarithmic trace is analytic on the full closed radius-three disk. -/
theorem analyticAt_liClockPairedEtaFirstPrefixTwiceFilledSourceTrace_of_norm_le_three {z : ℂ}
    (hz : ‖z‖ ≤ 3) :
    AnalyticAt ℂ liClockPairedEtaFirstPrefixTwiceFilledSourceTrace z := by
  obtain ⟨ha, hn⟩ := liClockPairedEtaFirstPrefixTwiceFilledDeflation_central_regular hz
  have hlog : AnalyticAt ℂ (logDeriv liClockPairedEtaFirstPrefixTwiceFilledDeflation)
      (1 / 2 + z * I) := ha.deriv.div ha hn
  change AnalyticAt ℂ (fun w : ℂ => I *
    logDeriv liClockPairedEtaFirstPrefixTwiceFilledDeflation (1 / 2 + w * I)) z
  exact analyticAt_const.mul (hlog.comp (f := fun w : ℂ => 1 / 2 + w * I)
    (analyticAt_const.add (analyticAt_id.mul analyticAt_const)))

/-- The twice-filled first-prefix trace admits the radius-three central contour. -/
theorem diffContOnCl_liClockPairedEtaFirstPrefixTwiceFilledSourceTrace_ball_three :
    DiffContOnCl ℂ liClockPairedEtaFirstPrefixTwiceFilledSourceTrace (ball (0 : ℂ) 3) := by
  have ha : AnalyticOnNhd ℂ liClockPairedEtaFirstPrefixTwiceFilledSourceTrace
      (closedBall (0 : ℂ) 3) := by
    intro z hz
    exact analyticAt_liClockPairedEtaFirstPrefixTwiceFilledSourceTrace_of_norm_le_three
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  exact ha.differentiableOn.diffContOnCl_ball (Subset.refl _)


/-- The full literal regular trace retains its first pole and the exact filled deflation. -/
theorem liClockPairedEtaFiniteSourceTrace_eq_pole_add_filled (N : ℕ) {z : ℂ}
    (hlower : 0 < (1 / 2 + z * I).re) (hupper : (1 / 2 + z * I).re < 1)
    (heta : pairedEtaCorePartialSum N (1 / 2 + z * I) ≠ 0) :
    liClockPairedEtaFiniteSourceTrace N z =
      I / (1 / 2 + z * I) + liClockPairedEtaFiniteFilledSourceTrace N z := by
  rw [liClockPairedEtaFiniteSourceTrace_eq_pole_add_deflated N hlower hupper heta,
    liClockPairedEtaFiniteDeflatedSourceTrace_eq_filled N hlower hupper]

/-- The first-prefix second-pole split needs no unproved nonvanishing premise on the regular central disk. -/
theorem liClockPairedEtaFirstPrefixDeflatedSourceTrace_eq_secondPole_add_twiceFilled_of_norm_lt_half
    {z : ℂ} (hz : ‖z‖ < 1 / 2) :
    liClockPairedEtaFiniteDeflatedSourceTrace 1 z =
      -I / (1 / 2 + z * I + 2) + liClockPairedEtaFirstPrefixTwiceFilledSourceTrace z := by
  have hzi := abs_lt.mp ((Complex.abs_im_le_norm z).trans_lt hz)
  have hl : 0 < (1 / 2 + z * I).re := by
    norm_num [Complex.mul_re]
    linarith
  have hu : (1 / 2 + z * I).re < 1 := by
    norm_num [Complex.mul_re]
    linarith
  obtain ⟨hn, _⟩ := central_first_partition_factors
    (hz.le.trans (by norm_num : (1 / 2 : ℝ) ≤ 3))
  exact liClockPairedEtaFirstPrefixDeflatedSourceTrace_eq_secondPole_add_twiceFilled hl hu hn

end
end RHTower

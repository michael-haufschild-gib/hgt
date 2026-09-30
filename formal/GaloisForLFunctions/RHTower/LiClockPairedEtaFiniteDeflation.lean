import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPairedEtaApproximation
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteLaplacePartition
import Mathlib.Analysis.Calculus.Deriv.ZPow


/-!
# Exact finite eta deflation and calibrated clock compensation

The actual finite Laplace partition removes the explicit eta factor `s` from
its completed logarithmic derivative. On a regular central circle, the removed
pole contributes exactly `-2 sinh (2t)` to the negative trace sine contour.
The complete source approximation calibrates the compensation on clocks up to
twenty, uniformly down to zero. The literal completion factor is used only in
the regular strip; no value at the original Gamma endpoint is extended here.
-/

open Complex Set Metric Filter Topology MeasureTheory RiemannGaussian
namespace RHTower
noncomputable section

/-- The logarithmic derivative of the full completion factor times the actual finite Laplace partition. -/
def liClockPairedEtaFiniteDeflatedSourceTrace (N : ℕ) (z : ℂ) : ℂ :=
  I * logDeriv (fun s : ℂ => pairedEtaXiCompletionFactor s *
    pairedEtaFiniteLaplacePartition N s) (1/2+z*I)

/-- The regular finite eta premise excludes the empty prefix. -/
theorem liClockPairedEtaFiniteDeflation_prefix_pos {N : ℕ} {s : ℂ}
    (heta : pairedEtaCorePartialSum N s ≠ 0) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [pairedEtaCorePartialSum] at heta
  · exact hN

/-- Away from zero, the exact identity `E_N = s L_N` gives analytic finite Laplace source. -/
theorem analyticAt_liClockPairedEtaFiniteLaplacePartition {N : ℕ} {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ (pairedEtaFiniteLaplacePartition N) s := by
  have ha := ((differentiable_pairedEtaCorePartialSum N).analyticAt s).div
    analyticAt_id hs
  apply ha.congr
  filter_upwards [continuousAt_id.eventually_ne hs] with w hw
  change pairedEtaCorePartialSum N w / w = pairedEtaFiniteLaplacePartition N w
  rw [pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition]
  exact mul_div_cancel_left₀ _ hw

/-- Exact completed source split throughout the regular strip, with finite eta nonzero. -/
theorem liClockPairedEtaFiniteSourceTrace_eq_pole_add_deflated (N : ℕ) {z : ℂ}
    (hlower : 0 < (1/2+z*I).re) (hupper : (1/2+z*I).re < 1)
    (heta : pairedEtaCorePartialSum N (1/2+z*I) ≠ 0) :
    liClockPairedEtaFiniteSourceTrace N z =
      I/(1/2+z*I) + liClockPairedEtaFiniteDeflatedSourceTrace N z := by
  let s : ℂ := 1/2+z*I
  have hs : s ≠ 0 := by
    intro h
    have hp : 0 < s.re := hlower
    rw [h] at hp
    norm_num at hp
  have hL : pairedEtaFiniteLaplacePartition N s ≠ 0 := by
    intro h
    have hE := pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition N s
    rw [h, mul_zero] at hE
    exact heta hE
  have hfun : (fun w : ℂ => pairedEtaXiCompletionFactor w * pairedEtaCorePartialSum N w) =
      (fun w : ℂ => w * (pairedEtaXiCompletionFactor w * pairedEtaFiniteLaplacePartition N w)) := by
    funext w
    rw [pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition]
    ring
  rw [liClockPairedEtaFiniteSourceTrace_eq_completion_logDeriv N hlower hupper heta, hfun,
    logDeriv_mul (f := fun w : ℂ => w)
      (g := fun w => pairedEtaXiCompletionFactor w * pairedEtaFiniteLaplacePartition N w)
      s hs (mul_ne_zero (pairedEtaXiCompletionFactor_ne_zero hlower hupper) hL)
      differentiableAt_id
      ((analyticAt_pairedEtaXiCompletionFactor hlower hupper).mul
        (analyticAt_liClockPairedEtaFiniteLaplacePartition hs)).differentiableAt]
  simp only [logDeriv_id']
  unfold liClockPairedEtaFiniteDeflatedSourceTrace
  dsimp only [s]
  ring

/-- Odd pole derivatives retain the literal factorial and reciprocal half-height normalization. -/
theorem iteratedDeriv_liClockCentralEtaPole_odd (j : ℕ) :
    iteratedDeriv (2*j+1) (fun z : ℂ => 1/(z-I/2)) 0 =
      (-1:ℂ)^j * 4^(j+1) * ((2*j+1).factorial:ℂ) := by
  have hfun : (fun z : ℂ => 1/(z-I/2)) = (fun z => (1*z-I/2)⁻¹) := by
    funext z
    simp
  rw [hfun, iteratedDeriv_eq_iterate, iter_deriv_inv_linear_sub]
  simp only [one_mul, zero_sub, one_pow, mul_one]
  have hinv : (-(I/2):ℂ)⁻¹ = 2*I := by
    apply inv_eq_of_mul_eq_one_right
    ring_nf
    norm_num [Complex.I_sq]
  have hexp : (-1-(2*j+1:ℕ):ℤ) = -((2*j+2:ℕ):ℤ) := by omega
  rw [hexp, zpow_neg, zpow_natCast, ← inv_pow, hinv]
  have hp : (2*I:ℂ)^(2*j+2) = (-4:ℂ)^(j+1) := by
    rw [show 2*j+2 = 2*(j+1) by omega, pow_mul]
    norm_num [mul_pow, Complex.I_sq]
  rw [hp]
  have hodd : (-1:ℂ)^(2*j+1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hodd, neg_pow (4:ℂ), pow_succ (-1:ℂ)]
  ring

/-- The central sine contour of the source-defined deflated finite completion. -/
def liClockPairedEtaFiniteDeflatedClockResponse (N : ℕ) (r : ℝ) (t : ℂ) : ℂ :=
  liClockCentralTraceSineContour (liClockPairedEtaFiniteDeflatedSourceTrace N) r t

/-- The deflated completed source is analytic at every regular finite eta point in the full strip. -/
theorem analyticAt_liClockPairedEtaFiniteDeflatedSourceTrace (N : ℕ) {z : ℂ}
    (hlower : 0 < (1/2+z*I).re) (hupper : (1/2+z*I).re < 1)
    (heta : pairedEtaCorePartialSum N (1/2+z*I) ≠ 0) :
    AnalyticAt ℂ (liClockPairedEtaFiniteDeflatedSourceTrace N) z := by
  let s : ℂ := 1/2+z*I
  have hs : s ≠ 0 := by
    intro h
    have hp : 0 < s.re := hlower
    rw [h] at hp
    norm_num at hp
  have hL : pairedEtaFiniteLaplacePartition N s ≠ 0 := by
    intro h
    have hE := pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition N s
    rw [h, mul_zero] at hE
    exact heta hE
  let H : ℂ → ℂ := fun w => pairedEtaXiCompletionFactor w * pairedEtaFiniteLaplacePartition N w
  have hH : AnalyticAt ℂ H s :=
    (analyticAt_pairedEtaXiCompletionFactor hlower hupper).mul (analyticAt_liClockPairedEtaFiniteLaplacePartition hs)
  have hHne : H s ≠ 0 := mul_ne_zero
    (pairedEtaXiCompletionFactor_ne_zero hlower hupper) hL
  have hlog : AnalyticAt ℂ (logDeriv H) s := hH.deriv.div hH hHne
  have hc : AnalyticAt ℂ (fun w : ℂ => 1/2+w*I) z :=
    analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hlogc : AnalyticAt ℂ (logDeriv H) ((fun w : ℂ => 1/2+w*I) z) := hlog
  change AnalyticAt ℂ (fun w : ℂ => I*logDeriv H (1/2+w*I)) z
  exact analyticAt_const.mul (hlogc.comp (f := fun w : ℂ => 1/2+w*I) hc)

private theorem central_strip {r : ℝ} (hr : r < 1/2) {z : ℂ} (hz : ‖z‖ ≤ r) :
    0 < (1/2+z*I).re ∧ (1/2+z*I).re < 1 := by
  have hi := abs_le.mp ((Complex.abs_im_le_norm z).trans hz)
  have heq : (1/2+z*I).re = (1/2:ℝ)-z.im := by
    norm_num [Complex.add_re, Complex.mul_re]
    ring
  rw [heq]
  constructor <;> linarith

private theorem pole_ne_zero {r : ℝ} (hr : r < 1/2) {z : ℂ} (hz : ‖z‖ ≤ r) :
    z-I/2 ≠ 0 := by
  intro h
  have heq : z = I/2 := sub_eq_zero.mp h
  rw [heq, norm_div, norm_I] at hz
  norm_num at hz
  linarith

private theorem diffContOnCl_liClockCentralEtaPole {r : ℝ} (hr : r < 1/2) :
    DiffContOnCl ℂ (fun z : ℂ => 1/(z-I/2)) (ball 0 r) := by
  have ha : AnalyticOnNhd ℂ (fun z : ℂ => 1/(z-I/2)) (closedBall 0 r) := by
    intro z hz
    have hn : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (pole_ne_zero hr hn)
  exact ha.differentiableOn.diffContOnCl_ball (Subset.refl _)

private theorem liClockCentralEtaPole_contourTerm (j : ℕ) (t : ℂ) :
    liClockCentralTraceSineContourTerm (fun z : ℂ => 1/(z-I/2)) t j =
      2*((2*t)^(2*j+1)/((2*j+1).factorial:ℂ)) := by
  unfold liClockCentralTraceSineContourTerm
  rw [iteratedDeriv_liClockCentralEtaPole_odd]
  have hfac : ((2*j+1).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*j+1)
  have hsign : (-1:ℂ)^j * (-1:ℂ)^j = 1 := by
    rw [← mul_pow]
    norm_num
  have hcoef : (-1:ℂ)^j*((-1:ℂ)^j*4^(j+1)*((2*j+1).factorial:ℂ)) =
      4^(j+1)*((2*j+1).factorial:ℂ) := by
    calc
      _ = ((-1:ℂ)^j*(-1:ℂ)^j)*(4^(j+1)*((2*j+1).factorial:ℂ)) := by ring
      _ = _ := by rw [hsign, one_mul]
  rw [hcoef]
  have hp4 : (4:ℂ)^(j+1) = (2:ℂ)^(2*j+2) := by
    rw [show (4:ℂ) = 2^2 by norm_num, ← pow_mul]
    congr 1
  rw [hp4, show 2*j+2 = (2*j+1)+1 by omega, pow_succ, mul_pow]
  field_simp [hfac]

/-- The removed pole contributes exactly negative twice the hyperbolic sine at every complex clock. -/
theorem liClockCentralTraceSineContour_eta_pole {r : ℝ} (hr : 0 < r) (hrhalf : r < 1/2) (t : ℂ) :
    liClockCentralTraceSineContour (fun z : ℂ => 1/(z-I/2)) r t =
      -2*Complex.sinh (2*t) := by
  rw [liClockCentralTraceSineContour_eq_neg_tsum hr (diffContOnCl_liClockCentralEtaPole hrhalf)]
  simp_rw [liClockCentralEtaPole_contourTerm]
  rw [tsum_mul_left, (Complex.hasSum_sinh (2*t)).tsum_eq]
  ring

private theorem trace_contour_add {r : ℝ} (hr : 0 < r) {T U : ℂ → ℂ}
    (hT : ContinuousOn T (sphere 0 r)) (hU : ContinuousOn U (sphere 0 r)) (t : ℂ) :
    liClockCentralTraceSineContour (fun z => T z+U z) r t =
      liClockCentralTraceSineContour T r t + liClockCentralTraceSineContour U r t := by
  have hnz (z : ℂ) (hz : z ∈ sphere (0:ℂ) r) : z ≠ 0 := by
    intro h
    have hn : ‖z‖ = r := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    rw [h, norm_zero] at hn
    linarith
  have hs : ContinuousOn (fun z : ℂ => Complex.sin (t/z)) (sphere 0 r) :=
    Complex.continuous_sin.comp_continuousOn (continuousOn_const.div continuousOn_id hnz)
  have hTi : CircleIntegrable (fun z : ℂ => T z*Complex.sin (t/z)/z) 0 r :=
    ((hT.mul hs).div continuousOn_id hnz).circleIntegrable hr.le
  have hUi : CircleIntegrable (fun z : ℂ => U z*Complex.sin (t/z)/z) 0 r :=
    ((hU.mul hs).div continuousOn_id hnz).circleIntegrable hr.le
  have hi : (∮ z in C(0,r), (T z+U z)*Complex.sin (t/z)/z) =
      (∮ z in C(0,r), T z*Complex.sin (t/z)/z) +
      (∮ z in C(0,r), U z*Complex.sin (t/z)/z) := by
    rw [← circleIntegral.integral_add hTi hUi]
    apply circleIntegral.integral_congr hr.le
    intro z _
    dsimp only
    ring
  unfold liClockCentralTraceSineContour
  rw [hi]
  ring

/-- The exact all-complex clock decomposition needs nonvanishing only on the integration circle. -/
theorem liClockPairedEtaFiniteClockResponse_eq_neg_two_sinh_add_deflated (N : ℕ) {r : ℝ} (hr : 0 < r) (hrhalf : r < 1/2)
    (heta : ∀ z ∈ sphere (0:ℂ) r, pairedEtaCorePartialSum N (1/2+z*I) ≠ 0)
    (t : ℂ) :
    liClockPairedEtaFiniteClockResponse N r t = -2*Complex.sinh (2*t) +
      liClockPairedEtaFiniteDeflatedClockResponse N r t := by
  have hstrip (z : ℂ) (hz : z ∈ sphere (0:ℂ) r) :
      0 < (1/2+z*I).re ∧ (1/2+z*I).re < 1 :=
    central_strip hrhalf (show ‖z‖ ≤ r by
      exact (show ‖z‖ = r by simpa only [mem_sphere_iff_norm, sub_zero] using hz).le)
  have hD : ContinuousOn (liClockPairedEtaFiniteDeflatedSourceTrace N) (sphere 0 r) := by
    intro z hz
    exact (analyticAt_liClockPairedEtaFiniteDeflatedSourceTrace N (hstrip z hz).1 (hstrip z hz).2 (heta z hz)).continuousAt.continuousWithinAt
  have hP : ContinuousOn (fun z : ℂ => 1/(z-I/2)) (sphere 0 r) := by
    exact ((diffContOnCl_liClockCentralEtaPole hrhalf).continuousOn_ball).mono sphere_subset_closedBall
  have hsource : ∀ z ∈ sphere (0:ℂ) r, liClockPairedEtaFiniteSourceTrace N z =
      1/(z-I/2)+liClockPairedEtaFiniteDeflatedSourceTrace N z := by
    intro z hz
    rw [liClockPairedEtaFiniteSourceTrace_eq_pole_add_deflated N (hstrip z hz).1 (hstrip z hz).2 (heta z hz)]
    have hs : 1/2+z*I ≠ 0 := by
      intro h
      have hp := (hstrip z hz).1
      rw [h] at hp
      norm_num at hp
    have hp := pole_ne_zero hrhalf (show ‖z‖ ≤ r by
      exact (show ‖z‖ = r by simpa only [mem_sphere_iff_norm, sub_zero] using hz).le)
    congr 1
    apply (div_eq_div_iff hs hp).2
    ring_nf
    norm_num [Complex.I_sq]
    ring
  have hc : liClockPairedEtaFiniteClockResponse N r t =
      liClockCentralTraceSineContour (fun z => 1/(z-I/2)+
        liClockPairedEtaFiniteDeflatedSourceTrace N z) r t := by
    unfold liClockPairedEtaFiniteClockResponse liClockCentralTraceSineContour
    congr 1
    apply circleIntegral.integral_congr hr.le
    intro z hz
    dsimp only
    rw [hsource z hz]
  rw [hc, trace_contour_add hr hP hD, liClockCentralTraceSineContour_eta_pole hr hrhalf]
  rfl

private theorem finite_eta_ne_zero {N : ℕ}
    (hsmall : 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16) {z : ℂ} (hz : ‖z‖ ≤ 1/128) :
    pairedEtaCorePartialSum N (1/2+z*I) ≠ 0 := by
  have h := liClockPairedEtaFiniteCore_re_gt_one_sixteenth N hsmall hz
  intro hzero
  norm_num [hzero] at h

/-- The deflated finite clock is real on real clocks under the quantitative finite denominator floor. -/
theorem liClockPairedEtaFiniteDeflatedClockResponse_im_ofReal_eq_zero (N : ℕ)
    (hsmall : 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16)
    {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1/128) (t : ℝ) :
    (liClockPairedEtaFiniteDeflatedClockResponse N r (t:ℂ)).im = 0 := by
  have hnz (z : ℂ) (hz : z ∈ sphere (0:ℂ) r) :
      pairedEtaCorePartialSum N (1/2+z*I) ≠ 0 :=
    finite_eta_ne_zero hsmall ((show ‖z‖ = r by
      simpa only [mem_sphere_iff_norm, sub_zero] using hz).le.trans hrsmall)
  have hs := liClockPairedEtaFiniteClockResponse_eq_neg_two_sinh_add_deflated N hr (by linarith) hnz (t:ℂ)
  have hsi : Complex.sinh (2*(t:ℂ)) = (Real.sinh (2*t):ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using (Complex.ofReal_sinh (2*t)).symm
  have hi := congrArg Complex.im hs
  have hF := liClockPairedEtaFiniteClockResponse_im_ofReal_eq_zero N hsmall hr hrsmall t
  have hpi : (-2*Complex.sinh (2*(t:ℂ))).im = 0 := by
    rw [hsi, show (-2:ℂ) = ((-2:ℝ):ℂ) by norm_num,
      ← Complex.ofReal_mul, Complex.ofReal_im]
  simp only [Complex.add_im, hpi, hF, zero_add] at hi
  exact hi.symm

/-- The actual positive clock margin gives the exact finite-error compensation coefficient. -/
theorem liClockPairedEtaFiniteDeflatedClockResponse_ge_calibrated_margin {N : ℕ} {r t : ℝ} (hr : 0 < r)
    (hrsmall : r ≤ 1/128) (hsmall : 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16)
    (ht : 0 ≤ t) (ht20 : t ≤ 20)
    (herror : ‖liClockPairedEtaFiniteClockResponse N r (t:ℂ)-
      (liEvenCrossActualClockResponse t:ℂ)‖ ≤
        liClockPairedEtaSourceErrorEnvelope N*Real.sinh (t/r)) :
    2*Real.sinh (2*t) +
      ((1051/2184:ℝ)*xiShiftAbsoluteMass 0-
        liClockPairedEtaSourceErrorEnvelope N*Real.cosh (20/r)/r)*t ≤
      (liClockPairedEtaFiniteDeflatedClockResponse N r (t:ℂ)).re := by
  have he := herror.trans (mul_le_mul_of_nonneg_left
    (liClock_sinh_clock_le_linear hr ht ht20) (liClockPairedEtaSourceErrorEnvelope_nonneg N))
  have hre : liEvenCrossActualClockResponse t -
      (liClockPairedEtaFiniteClockResponse N r (t:ℂ)).re ≤
        ‖liClockPairedEtaFiniteClockResponse N r (t:ℂ)-
          (liEvenCrossActualClockResponse t:ℂ)‖ := by
    simpa only [Complex.sub_re, Complex.ofReal_re, neg_sub] using
      (neg_le_abs (liClockPairedEtaFiniteClockResponse N r (t:ℂ)-
        (liEvenCrossActualClockResponse t:ℂ)).re).trans (Complex.abs_re_le_norm _)
  have hmargin := liEvenCrossActualClockResponse_ge_positive_margin ht ht20
  have hnz (z : ℂ) (hz : z ∈ sphere (0:ℂ) r) :
      pairedEtaCorePartialSum N (1/2+z*I) ≠ 0 :=
    finite_eta_ne_zero hsmall ((show ‖z‖ = r by
      simpa only [mem_sphere_iff_norm, sub_zero] using hz).le.trans hrsmall)
  have hs := liClockPairedEtaFiniteClockResponse_eq_neg_two_sinh_add_deflated N hr (by linarith) hnz (t:ℂ)
  have hsi : Complex.sinh (2*(t:ℂ)) = (Real.sinh (2*t):ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using (Complex.ofReal_sinh (2*t)).symm
  have hsr := congrArg Complex.re hs
  have hpr : (-2*Complex.sinh (2*(t:ℂ))).re = -2*Real.sinh (2*t) := by
    rw [hsi, show (-2:ℂ) = ((-2:ℝ):ℂ) by norm_num,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [Complex.add_re, hpr] at hsr
  have halgebra : liClockPairedEtaSourceErrorEnvelope N*((Real.cosh (20/r)/r)*t) =
      (liClockPairedEtaSourceErrorEnvelope N*Real.cosh (20/r)/r)*t := by ring
  rw [halgebra] at he
  nlinarith

/-- One actual radius gives the complete complex error, the calibrated real margin, and every eventual positive fraction of that margin. -/
theorem exists_liClockPairedEtaFiniteDeflatedClockResponse_calibration_radius :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1/128 ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      (∀ N : ℕ, 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16 → ∀ t : ℂ,
        ‖liClockPairedEtaFiniteDeflatedClockResponse N r t-2*Complex.sinh (2*t)-
          liEvenCrossActualComplexClockResponse t‖ ≤
            liClockPairedEtaSourceErrorEnvelope N*Real.sinh (‖t‖/r)) ∧
      (∀ N : ℕ, 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16 → ∀ t : ℝ, 0 ≤ t → t ≤ 20 →
        2*Real.sinh (2*t)+((1051/2184:ℝ)*xiShiftAbsoluteMass 0-
          liClockPairedEtaSourceErrorEnvelope N*Real.cosh (20/r)/r)*t ≤
            (liClockPairedEtaFiniteDeflatedClockResponse N r (t:ℂ)).re) ∧
      (∀ θ : ℝ, 0 < θ → θ < 1 → ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ 20 →
        2*Real.sinh (2*t)+θ*((1051/2184:ℝ)*xiShiftAbsoluteMass 0)*t ≤
          (liClockPairedEtaFiniteDeflatedClockResponse N r (t:ℂ)).re) := by
  obtain ⟨r₀, hr₀, hr₀small, herror⟩ := exists_liClockPairedEtaFiniteClockResponse_error_radius
  refine ⟨r₀, hr₀, hr₀small, fun r hr hrr₀ => ?_⟩
  have hrs : r ≤ 1/128 := hrr₀.le.trans hr₀small
  have hnz (N : ℕ) (hsmall : 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16)
      (z : ℂ) (hz : z ∈ sphere (0:ℂ) r) : pairedEtaCorePartialSum N (1/2+z*I) ≠ 0 :=
    finite_eta_ne_zero hsmall ((show ‖z‖ = r by
      simpa only [mem_sphere_iff_norm, sub_zero] using hz).le.trans hrs)
  have hm (N : ℕ) (hsmall : 3*(2*(N:ℝ)+1)^(-(1/4:ℝ)) ≤ 1/16)
      (t : ℝ) (ht : 0 ≤ t) (ht20 : t ≤ 20) :=
    liClockPairedEtaFiniteDeflatedClockResponse_ge_calibrated_margin hr hrs hsmall ht ht20 (by
      simpa only [liEvenCrossActualComplexClockResponse_ofReal, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht] using herror r hr hrr₀ N hsmall (t:ℂ))
  refine ⟨?_, hm, ?_⟩
  · intro N hsmall t
    have hs := liClockPairedEtaFiniteClockResponse_eq_neg_two_sinh_add_deflated N hr (by linarith) (hnz N hsmall) t
    have heq : liClockPairedEtaFiniteDeflatedClockResponse N r t-2*Complex.sinh (2*t)-
        liEvenCrossActualComplexClockResponse t =
      liClockPairedEtaFiniteClockResponse N r t-liEvenCrossActualComplexClockResponse t := by
      linear_combination -hs
    rw [heq]
    exact herror r hr hrr₀ N hsmall t
  · intro θ _hθ hθ1
    have hmargin : 0 < (1-θ)*((1051/2184:ℝ)*xiShiftAbsoluteMass 0) :=
      mul_pos (sub_pos.mpr hθ1) (mul_pos (by norm_num) (xiShiftAbsoluteMass_pos 0))
    have hlim : Tendsto (fun N : ℕ => liClockPairedEtaSourceErrorEnvelope N*
        (Real.cosh (20/r)/r)) atTop (𝓝 0) := by
      simpa only [zero_mul] using liClockPairedEtaSourceErrorEnvelope_tendsto_zero.mul_const
        (Real.cosh (20/r)/r)
    filter_upwards [liClockPairedEta_eventually_valueTail_le_one_sixteenth,
      hlim.eventually (eventually_lt_nhds hmargin)] with N hsmall hN
    intro t ht ht20
    have hmt := mul_le_mul_of_nonneg_right hN.le ht
    have halgebra : liClockPairedEtaSourceErrorEnvelope N*(Real.cosh (20/r)/r) =
        liClockPairedEtaSourceErrorEnvelope N*Real.cosh (20/r)/r := by ring
    rw [halgebra] at hmt
    linarith [hm N hsmall t ht ht20]

end
end RHTower



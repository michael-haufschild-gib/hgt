import GaloisForLFunctions.RHTower.LiClockPairedEtaContiguousSource
import GaloisForLFunctions.RHTower.LiClockPairedEtaCompletionAsymptotic
import GaloisForLFunctions.RHTower.LiClockPairedEtaCompletionMoments
import GaloisForLFunctions.RHTower.LiClockPairedEtaFiniteFilledDeflation
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPairedEtaApproximation
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockDampedResolvent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Literal arithmetic cancellation in the paired-eta clock

The actual eta logarithmic trace is retained independently of completion.
Every regular finite actual-to-contiguous partition ratio gives the exact
all-complex identity `F_N = C - K_N + H_N`, with circle-only finite eta
nonvanishing. On a fixed family of small central circles, the literal infinite
eta clock has normalized leading coefficient `-1/5`, ratio to completion
tending to `-1`, and real part tending to minus infinity.

Literal finite eta and gap clocks converge at every fixed complex clock.
Consequently, every fixed fractional loss floor with fraction below one is
impossible on any eventually expanding positive logarithmic window. These
source cancellation laws impose no RH or clock-sign hypothesis.
-/

open GaloisForLFunctions RiemannGaussian Complex Set Metric Filter Topology MeasureTheory
namespace RHTower
noncomputable section

/-- Literal eta logarithmic trace, independent of any completion subtraction. -/
def liClockPairedEtaArithmeticSourceTrace (z : ℂ) : ℂ :=
  I*logDeriv pairedEtaCore (1/2+z*I)

/-- Literal arithmetic eta clock on its regular central circle. -/
def liClockPairedEtaArithmeticClockResponse (r : ℝ) (t : ℂ) : ℂ :=
  liClockCentralTraceSineContour liClockPairedEtaArithmeticSourceTrace r t

/-- The literal finite eta logarithmic trace retains the entire finite polynomial. -/
def liClockPairedEtaFiniteArithmeticSourceTrace (N : ℕ) (z : ℂ) : ℂ :=
  I*logDeriv (pairedEtaCorePartialSum N) (1/2+z*I)

/-- Literal finite arithmetic clock before adding the completion source. -/
def liClockPairedEtaFiniteArithmeticClockResponse (N : ℕ) (r : ℝ) (t : ℂ) : ℂ :=
  liClockCentralTraceSineContour (liClockPairedEtaFiniteArithmeticSourceTrace N) r t

private theorem arithmetic_central_strip {r : ℝ} (hr : r < 1/2)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    0 < (1/2+z*I).re ∧ (1/2+z*I).re < 1 := by
  have hi := abs_le.mp ((Complex.abs_im_le_norm z).trans hz)
  norm_num [Complex.mul_re]
  constructor <;> linarith

/-- Exact completed trace split on the whole regular strip, with no chosen logarithm. -/
theorem liClockPairedEtaSourceTrace_eq_arithmetic_add_completion {z : ℂ}
    (hl : 0 < (1/2+z*I).re) (hu : (1/2+z*I).re < 1) :
    liEvenCrossActualClockPairedEtaSourceTrace z =
      liClockPairedEtaArithmeticSourceTrace z + liClockPairedEtaCompletionSourceTrace z := by
  unfold liEvenCrossActualClockPairedEtaSourceTrace liClockPairedEtaArithmeticSourceTrace
    liClockPairedEtaCompletionSourceTrace
  rw [logDeriv_pairedEtaCore_eq_tsum hl,logDeriv_pairedEtaXiCompletionFactor hl hu]
  dsimp only [pairedEtaArithmeticDerivativeValue,pairedEtaArithmeticXiRegularCorrection,
    gammaRealLogConnection]
  rw [Complex.ofReal_log Real.pi_pos.le]
  ring

/-- The finite logarithmic source split holds pointwise throughout the regular strip. -/
theorem liClockPairedEtaFiniteSourceTrace_eq_arithmetic_add_completion (N : ℕ) {z : ℂ}
    (hl : 0 < (1/2+z*I).re) (hu : (1/2+z*I).re < 1) :
    liClockPairedEtaFiniteSourceTrace N z =
      liClockPairedEtaFiniteArithmeticSourceTrace N z + liClockPairedEtaCompletionSourceTrace z := by
  unfold liClockPairedEtaFiniteSourceTrace liClockPairedEtaFiniteArithmeticSourceTrace
    liClockPairedEtaCompletionSourceTrace
  rw [logDeriv_pairedEtaXiCompletionFactor hl hu]
  simp only [logDeriv_apply,deriv_pairedEtaCorePartialSum]
  dsimp only [pairedEtaArithmeticQuotientPartialSum,pairedEtaArithmeticXiRegularCorrection,
    gammaRealLogConnection]
  rw [Complex.ofReal_log Real.pi_pos.le]
  ring

/-- Actual eta is nonzero and analytic on the established full central disk. -/
theorem analyticAt_liClockPairedEtaArithmeticSourceTrace_of_norm_le {z : ℂ}
    (hz : ‖z‖ ≤ 1/128) : AnalyticAt ℂ liClockPairedEtaArithmeticSourceTrace z := by
  have hs := arithmetic_central_strip (by norm_num : (1/128:ℝ)<1/2) hz
  have hn : pairedEtaCore (1/2+z*I) ≠ 0 :=
    liClockPairedEtaCore_ne_zero_of_norm_sub_half_le (by
      simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,
        add_sub_cancel_left,norm_mul,norm_I,mul_one] using hz)
  have ha := analyticOnNhd_pairedEtaCore (1/2+z*I) hs.1
  have hq : AnalyticAt ℂ (logDeriv pairedEtaCore) (1/2+z*I) := ha.deriv.div ha hn
  have hc : AnalyticAt ℂ (fun w : ℂ => 1/2+w*I) z :=
    analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  exact analyticAt_const.mul (hq.comp (f := fun w : ℂ => 1/2+w*I) hc)

/-- Closed-disk holomorphy for the literal eta clock, using the actual source floor. -/
theorem diffContOnCl_liClockPairedEtaArithmeticSourceTrace {r : ℝ} (hr : r ≤ 1/128) :
    DiffContOnCl ℂ liClockPairedEtaArithmeticSourceTrace (ball (0:ℂ) r) := by
  have ha : AnalyticOnNhd ℂ liClockPairedEtaArithmeticSourceTrace (closedBall (0:ℂ) r) := by
    intro z hz
    apply analyticAt_liClockPairedEtaArithmeticSourceTrace_of_norm_le
    exact (show ‖z‖ ≤ r by simpa only [mem_closedBall,dist_zero_right] using hz).trans hr
  exact ha.differentiableOn.diffContOnCl_ball (Subset.refl _)

private theorem arithmetic_contour_add {r : ℝ} (hr : 0 < r) {T U : ℂ → ℂ}
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
    intro z _; dsimp only; ring
  unfold liClockCentralTraceSineContour
  rw [hi]
  ring

/-- The literal arithmetic contour equals the full actual clock minus completion,
for every complex clock on one established family of regular central circles. -/
theorem exists_liClockPairedEtaArithmeticClockResponse_source_radius :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1/128 ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ t : ℂ,
      liClockPairedEtaArithmeticClockResponse r t =
        liEvenCrossActualComplexClockResponse t-liClockPairedEtaCompletionClockResponse r t := by
  obtain ⟨r₀,hr₀,hr₀small,hclock⟩ := exists_liEvenCrossActualClockPairedEtaContour_radius
  refine ⟨r₀,hr₀,hr₀small,fun r hr hrr₀ t => ?_⟩
  have hrsmall : r ≤ 1/128 := hrr₀.le.trans hr₀small
  have hrhalf : r < 1/2 := by linarith
  have hA : ContinuousOn liClockPairedEtaArithmeticSourceTrace (sphere (0:ℂ) r) :=
    ((diffContOnCl_liClockPairedEtaArithmeticSourceTrace hrsmall).continuousOn_ball).mono sphere_subset_closedBall
  have hC : ContinuousOn liClockPairedEtaCompletionSourceTrace (sphere (0:ℂ) r) :=
    ((diffContOnCl_liClockPairedEtaCompletionSourceTrace hrhalf).continuousOn_ball).mono sphere_subset_closedBall
  have htrace : liClockCentralTraceSineContour liEvenCrossActualClockPairedEtaSourceTrace r t =
      liClockCentralTraceSineContour
        (fun z => liClockPairedEtaArithmeticSourceTrace z+liClockPairedEtaCompletionSourceTrace z) r t := by
    unfold liClockCentralTraceSineContour
    congr 1
    apply circleIntegral.integral_congr hr.le
    intro z hz
    dsimp only
    have hn : ‖z‖ ≤ r := (show ‖z‖ = r by
      simpa only [mem_sphere_iff_norm,sub_zero] using hz).le
    have hs := arithmetic_central_strip hrhalf hn
    rw [liClockPairedEtaSourceTrace_eq_arithmetic_add_completion hs.1 hs.2]
  have he := (hclock r hr hrr₀).2 t
  rw [htrace,arithmetic_contour_add hr hA hC] at he
  change liClockPairedEtaArithmeticClockResponse r t+
    liClockPairedEtaCompletionClockResponse r t=liEvenCrossActualComplexClockResponse t at he
  exact eq_sub_of_add_eq he

private theorem finiteArithmeticSourceTrace_analytic (N : ℕ) {z : ℂ}
    (heta : pairedEtaCorePartialSum N (1/2+z*I) ≠ 0) :
    AnalyticAt ℂ (liClockPairedEtaFiniteArithmeticSourceTrace N) z := by
  have hf : pairedEtaCorePartialSum N = fun s : ℂ => s*pairedEtaFiniteLaplacePartition N s :=
    funext (pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition N)
  have ha : AnalyticAt ℂ (pairedEtaCorePartialSum N) (1/2+z*I) := by
    rw [hf]
    exact analyticAt_id.mul (analyticAt_liClockPairedEtaFiniteLaplacePartition_entire N (1/2+z*I))
  have hq : AnalyticAt ℂ (logDeriv (pairedEtaCorePartialSum N)) (1/2+z*I) :=
    ha.deriv.div ha heta
  have hc : AnalyticAt ℂ (fun w : ℂ => 1/2+w*I) z :=
    analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  exact analyticAt_const.mul (hq.comp (f := fun w : ℂ => 1/2+w*I) hc)

/-- Exact finite arithmetic/completion contour split; only circle eta regularity is needed. -/
theorem liClockPairedEtaFiniteClockResponse_eq_arithmetic_add_completion (N : ℕ) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2)
    (heta : ∀ z ∈ sphere (0:ℂ) r, pairedEtaCorePartialSum N (1/2+z*I) ≠ 0)
    (t : ℂ) :
    liClockPairedEtaFiniteClockResponse N r t =
      liClockPairedEtaFiniteArithmeticClockResponse N r t+liClockPairedEtaCompletionClockResponse r t := by
  have hA : ContinuousOn (liClockPairedEtaFiniteArithmeticSourceTrace N) (sphere (0:ℂ) r) := by
    intro z hz
    exact (finiteArithmeticSourceTrace_analytic N (heta z hz)).continuousAt.continuousWithinAt
  have hC : ContinuousOn liClockPairedEtaCompletionSourceTrace (sphere (0:ℂ) r) :=
    ((diffContOnCl_liClockPairedEtaCompletionSourceTrace hrhalf).continuousOn_ball).mono sphere_subset_closedBall
  have he : liClockPairedEtaFiniteClockResponse N r t =
      liClockCentralTraceSineContour
        (fun z => liClockPairedEtaFiniteArithmeticSourceTrace N z+liClockPairedEtaCompletionSourceTrace z) r t := by
    unfold liClockPairedEtaFiniteClockResponse liClockCentralTraceSineContour
    congr 1
    apply circleIntegral.integral_congr hr.le
    intro z hz
    dsimp only
    have hn : ‖z‖ ≤ r := (show ‖z‖ = r by
      simpa only [mem_sphere_iff_norm,sub_zero] using hz).le
    have hs := arithmetic_central_strip hrhalf hn
    rw [liClockPairedEtaFiniteSourceTrace_eq_arithmetic_add_completion N hs.1 hs.2]
  rw [he,arithmetic_contour_add hr hA hC]
  rfl

/-- The complete actual clock is negligible at the completion's leading positive rate,
without any zero-location or clock-sign premise. -/
theorem liEvenCrossActualComplexClockResponse_exp_neg_two_fifths_tendsto_zero :
    Tendsto (fun t : ℝ => (Real.exp (-(2/5)*t):ℂ)*liEvenCrossActualComplexClockResponse (t:ℂ))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t*Real.exp (-(119/300)*t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one,neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (119/300) (by norm_num)
  have hb : Tendsto (fun t : ℝ => xiShiftAbsoluteMass 0*t*Real.exp (-(119/300)*t))
      atTop (𝓝 0) := by
    simpa only [mul_zero,mul_assoc] using tendsto_const_nhds.mul ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hb
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht0
  rw [norm_mul,liEvenCrossActualComplexClockResponse_ofReal]
  have he : ‖(Real.exp (-(2/5)*t):ℂ)‖ = Real.exp (-(2/5)*t) := by
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (norm_liEvenCrossActualClockResponse_le_mass_mul_exp ht0)
    (Real.exp_pos (-(2/5)*t)).le
  have hn : ‖(liEvenCrossActualClockResponse t:ℂ)‖ = ‖liEvenCrossActualClockResponse t‖ := by
    exact Complex.norm_real _
  rw [hn]
  calc
    _ ≤ Real.exp (-(2/5)*t)*(xiShiftAbsoluteMass 0*t*Real.exp (t/300)) := hh
    _ = xiShiftAbsoluteMass 0*t*(Real.exp (-(2/5)*t)*Real.exp (t/300)) := by ring
    _ = xiShiftAbsoluteMass 0*t*Real.exp (-(2/5)*t+t/300) := by rw [← Real.exp_add]
    _ = _ := by congr 2; ring

/-- Exact finite eta logarithmic derivative, retaining the filled Laplace partition. -/
theorem logDeriv_liClockPairedEtaFiniteCore_eq_inverse_add_partition (N : ℕ)
    {s : ℂ} (hs : s ≠ 0) (hA : pairedEtaFiniteLaplacePartition N s ≠ 0) :
    logDeriv (pairedEtaCorePartialSum N) s =
      1/s+logDeriv (pairedEtaFiniteLaplacePartition N) s := by
  have hf : pairedEtaCorePartialSum N = fun w : ℂ => w*pairedEtaFiniteLaplacePartition N w :=
    funext (pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition N)
  rw [hf]
  simpa only [logDeriv_id,id_eq] using logDeriv_mul (f := id)
    (g := pairedEtaFiniteLaplacePartition N) s hs hA differentiableAt_id
    (analyticAt_liClockPairedEtaFiniteLaplacePartition_entire N s).differentiableAt

/-- At each fixed complex clock, literal finite completed responses converge to the
actual complete clock on one common family of admissible central circles. -/
theorem exists_liClockPairedEtaFiniteClockResponse_fixed_tendsto_radius :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1/128 ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ t : ℂ,
      Tendsto (fun N : ℕ => liClockPairedEtaFiniteClockResponse N r t)
        atTop (𝓝 (liEvenCrossActualComplexClockResponse t)) := by
  obtain ⟨r₀,hr₀,hsmall,he⟩ := exists_liClockPairedEtaFiniteClockResponse_error_radius
  refine ⟨r₀,hr₀,hsmall,?_⟩
  intro r hr hrr t
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : Tendsto (fun N : ℕ => liClockPairedEtaSourceErrorEnvelope N*Real.sinh (‖t‖/r))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using liClockPairedEtaSourceErrorEnvelope_tendsto_zero.mul_const
      (Real.sinh (‖t‖/r))
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hb
  filter_upwards [liClockPairedEta_eventually_valueTail_le_one_sixteenth] with N hN
  exact he r hr hrr N hN t

/-- Finite literal eta clocks converge to the literal infinite eta clock. -/
theorem exists_liClockPairedEtaFiniteArithmeticClockResponse_fixed_tendsto_radius :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1/128 ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ t : ℂ,
      Tendsto (fun N : ℕ => liClockPairedEtaFiniteArithmeticClockResponse N r t)
        atTop (𝓝 (liClockPairedEtaArithmeticClockResponse r t)) := by
  obtain ⟨a,ha,has,hsplit⟩ := exists_liClockPairedEtaArithmeticClockResponse_source_radius
  obtain ⟨b,hb,hbs,hlim⟩ := exists_liClockPairedEtaFiniteClockResponse_fixed_tendsto_radius
  refine ⟨min a b,lt_min ha hb,(min_le_left _ _).trans has,?_⟩
  intro r hr hrr t
  have hra : r < a := hrr.trans_le (min_le_left _ _)
  have hrb : r < b := hrr.trans_le (min_le_right _ _)
  have hrs : r ≤ 1/128 := hra.le.trans has
  have hrhalf : r < 1/2 := lt_of_le_of_lt hrs (by norm_num)
  rw [hsplit r hr hra t]
  apply (hlim r hr hrb t).sub_const (liClockPairedEtaCompletionClockResponse r t) |>.congr'
  filter_upwards [liClockPairedEta_eventually_valueTail_le_one_sixteenth] with N hN
  have heta : ∀ z ∈ sphere (0:ℂ) r, pairedEtaCorePartialSum N (1/2+z*I) ≠ 0 := by
    intro z hz hzero
    have hn : ‖z‖ ≤ 1/128 := (show ‖z‖ = r by
      simpa only [mem_sphere_iff_norm,sub_zero] using hz).le.trans hrs
    have hf := liClockPairedEtaFiniteCore_re_gt_one_sixteenth N hN hn
    norm_num [hzero] at hf
  rw [liClockPairedEtaFiniteClockResponse_eq_arithmetic_add_completion N hr hrhalf heta t]
  simp only [add_sub_cancel_right]

private theorem arithmeticClock_scaled_tendsto {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2)
    (heq : ∀ t : ℂ, liClockPairedEtaArithmeticClockResponse r t =
      liEvenCrossActualComplexClockResponse t-liClockPairedEtaCompletionClockResponse r t) :
    Tendsto (fun t : ℝ => (Real.exp (-(2/5)*t):ℂ)*
      liClockPairedEtaArithmeticClockResponse r (t:ℂ)) atTop (𝓝 (-1/5:ℂ)) := by
  have hh := liEvenCrossActualComplexClockResponse_exp_neg_two_fifths_tendsto_zero.sub
    (liClockPairedEtaCompletionClockResponse_exp_neg_mul_tendsto hr hrhalf)
  convert hh using 1
  · funext t
    rw [heq]
    ring
  · norm_num

private theorem arithmeticClock_ratio_tendsto {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2)
    (heq : ∀ t : ℂ, liClockPairedEtaArithmeticClockResponse r t =
      liEvenCrossActualComplexClockResponse t-liClockPairedEtaCompletionClockResponse r t) :
    Tendsto (fun t : ℝ => liClockPairedEtaArithmeticClockResponse r (t:ℂ)/
      liClockPairedEtaCompletionClockResponse r (t:ℂ)) atTop (𝓝 (-1:ℂ)) := by
  have hh := (arithmeticClock_scaled_tendsto hr hrhalf heq).div
    (liClockPairedEtaCompletionClockResponse_exp_neg_mul_tendsto hr hrhalf)
    (by norm_num : (1/5:ℂ) ≠ 0)
  have hh' : Tendsto (fun t : ℝ =>
      ((Real.exp (-(2/5)*t):ℂ)*liClockPairedEtaArithmeticClockResponse r (t:ℂ))/
      ((Real.exp (-(2/5)*t):ℂ)*liClockPairedEtaCompletionClockResponse r (t:ℂ)))
      atTop (𝓝 (-1:ℂ)) := by norm_num at hh ⊢; exact hh
  apply hh'.congr'
  filter_upwards [] with t
  have he : (Real.exp (-(2/5)*t):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  exact mul_div_mul_left _ _ he

private theorem arithmeticClock_re_tendsto_atBot {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2)
    (heq : ∀ t : ℂ, liClockPairedEtaArithmeticClockResponse r t =
      liEvenCrossActualComplexClockResponse t-liClockPairedEtaCompletionClockResponse r t) :
    Tendsto (fun t : ℝ => (liClockPairedEtaArithmeticClockResponse r (t:ℂ)).re)
      atTop atBot := by
  have hf := arithmeticClock_scaled_tendsto hr hrhalf heq
  have hre : Tendsto (fun t : ℝ => Real.exp (-(2/5)*t)*
      (liClockPairedEtaArithmeticClockResponse r (t:ℂ)).re)
      atTop (𝓝 (-1/5:ℝ)) := by
    have h := (Complex.continuous_re.tendsto (-1/5:ℂ)).comp hf
    simp only [Function.comp_def,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero] at h
    norm_num at h
    simpa only [neg_mul,neg_div] using h
  have he : Tendsto (fun t : ℝ => Real.exp ((2/5)*t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2/5))
  have hm := hre.neg_mul_atTop (by norm_num) he
  convert hm using 1
  funext t
  have heqexp : Real.exp (-(2/5)*t)*Real.exp ((2/5)*t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc
    (liClockPairedEtaArithmeticClockResponse r (t:ℂ)).re =
      (liClockPairedEtaArithmeticClockResponse r (t:ℂ)).re*1 := by ring
    _ = (liClockPairedEtaArithmeticClockResponse r (t:ℂ)).re*
      (Real.exp (-(2/5)*t)*Real.exp ((2/5)*t)) := by rw [heqexp]
    _ = _ := by ring

/-- Exact complex cancellation and real negative escape for the literal actual eta
clock on one family of regular central circles. No RH or finite-clock sign is assumed. -/
theorem exists_liClockPairedEtaArithmeticClockResponse_cancellation_radius :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1/128 ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      Tendsto (fun t : ℝ => (Real.exp (-(2/5)*t):ℂ)*
        liClockPairedEtaArithmeticClockResponse r (t:ℂ)) atTop (𝓝 (-1/5:ℂ)) ∧
      Tendsto (fun t : ℝ => liClockPairedEtaArithmeticClockResponse r (t:ℂ)/
        liClockPairedEtaCompletionClockResponse r (t:ℂ)) atTop (𝓝 (-1:ℂ)) ∧
      Tendsto (fun t : ℝ => (liClockPairedEtaArithmeticClockResponse r (t:ℂ)).re) atTop atBot ∧
      ∀ t : ℝ, (liClockPairedEtaArithmeticClockResponse r (t:ℂ)).im = 0 := by
  obtain ⟨r₀,hr₀,hr₀s,heq⟩ := exists_liClockPairedEtaArithmeticClockResponse_source_radius
  refine ⟨r₀,hr₀,hr₀s,?_⟩
  intro r hr hrr
  have hrhalf : r < 1/2 := lt_of_le_of_lt (hrr.le.trans hr₀s) (by norm_num)
  refine ⟨arithmeticClock_scaled_tendsto hr hrhalf (heq r hr hrr),
    arithmeticClock_ratio_tendsto hr hrhalf (heq r hr hrr),
    arithmeticClock_re_tendsto_atBot hr hrhalf (heq r hr hrr),?_⟩
  intro t
  rw [heq r hr hrr,Complex.sub_im,liEvenCrossActualComplexClockResponse_ofReal,
    Complex.ofReal_im,liClockPairedEtaCompletionClockResponse_im_ofReal_eq_zero hr hrhalf]
  norm_num

private theorem fixedClockFractionalFloor_not_eventually
    (C E : ℝ → ℝ) (M : ℕ → ℝ → ℝ)
    (hC : Tendsto (fun t : ℝ => Real.exp (-(2 / 5) * t) * C t)
      atTop (𝓝 (1 / 5)))
    (hE : Tendsto (fun t : ℝ => Real.exp (-(2 / 5) * t) * E t)
      atTop (𝓝 (-1 / 5)))
    (hM : ∀ t : ℝ, Tendsto (fun N : ℕ => M N t) atTop (𝓝 (E t)))
    {c θ : ℝ} (hc : 0 < c) (hθ : θ < 1) :
    ¬ (∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 0 < t →
      t ≤ c * Real.log (2 * (N : ℝ) + 1) → -θ * C t ≤ M N t) := by
  have hs : Tendsto (fun t : ℝ => Real.exp (-(2 / 5) * t) *
      (E t + θ * C t)) atTop (𝓝 ((θ - 1) / 5)) := by
    have hh := hE.add (hC.const_mul θ)
    have hconstant : (-1 / 5 : ℝ) + θ * (1 / 5) = (θ - 1) / 5 := by ring
    rw [hconstant] at hh
    apply hh.congr'
    filter_upwards [] with t
    ring
  have hnegative : (θ - 1) / 5 < 0 := by linarith
  obtain ⟨T, hTscaled, hTlarge⟩ :=
    ((hs.eventually_lt_const hnegative).and (eventually_ge_atTop (1 : ℝ))).exists
  have hT : 0 < T := by linarith
  have hTnegative : E T + θ * C T < 0 := by
    by_contra h
    have hn : 0 ≤ Real.exp (-(2 / 5) * T) * (E T + θ * C T) :=
      mul_nonneg (Real.exp_pos _).le (le_of_not_gt h)
    exact (not_le_of_gt hTscaled) hn
  have hfinite : ∀ᶠ N : ℕ in atTop, M N T + θ * C T < 0 :=
    ((hM T).add_const (θ * C T)).eventually_lt_const hTnegative
  have hodd : Tendsto (fun N : ℕ => 2 * (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ)
      (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
  have hwindow : Tendsto (fun N : ℕ => c * Real.log (2 * (N : ℝ) + 1))
      atTop atTop :=
    (Real.tendsto_log_atTop.comp hodd).const_mul_atTop hc
  intro hfloor
  obtain ⟨N, hNfloor, hNnegative, hNwindow⟩ :=
    (hfloor.and (hfinite.and (hwindow.eventually_ge_atTop T))).exists
  have hh := hNfloor T hT hNwindow
  linarith

/-- Every fixed-fraction eta-loss floor on any expanding logarithmic window is
impossible for the original finite arithmetic source. -/
theorem exists_liClockPairedEtaFiniteArithmeticClockResponse_fractional_floor_no_go_radius :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1/128 ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∀ c : ℝ, 0 < c → ∀ θ : ℝ, θ < 1 →
        ¬ (∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 0 < t →
          t ≤ c*Real.log (2*(N:ℝ)+1) →
            -θ*(liClockPairedEtaCompletionClockResponse r (t:ℂ)).re ≤
              (liClockPairedEtaFiniteArithmeticClockResponse N r (t:ℂ)).re) := by
  obtain ⟨a,ha,has,hcan⟩ := exists_liClockPairedEtaArithmeticClockResponse_cancellation_radius
  obtain ⟨b,hb,hbs,hfinite⟩ := exists_liClockPairedEtaFiniteArithmeticClockResponse_fixed_tendsto_radius
  refine ⟨min a b,lt_min ha hb,(min_le_left _ _).trans has,?_⟩
  intro r hr hrr c hc θ hθ
  have hra : r < a := hrr.trans_le (min_le_left _ _)
  have hrb : r < b := hrr.trans_le (min_le_right _ _)
  have hrhalf : r < 1/2 := lt_of_le_of_lt (hra.le.trans has) (by norm_num)
  have hC : Tendsto (fun t : ℝ => Real.exp (-(2/5)*t)*
      (liClockPairedEtaCompletionClockResponse r (t:ℂ)).re) atTop (𝓝 (1/5:ℝ)) := by
    have h := (Complex.continuous_re.tendsto (1/5:ℂ)).comp
      (liClockPairedEtaCompletionClockResponse_exp_neg_mul_tendsto hr hrhalf)
    convert h using 1
    · funext t
      simp only [Function.comp_def,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero]
    · norm_num
  have hE : Tendsto (fun t : ℝ => Real.exp (-(2/5)*t)*
      (liClockPairedEtaArithmeticClockResponse r (t:ℂ)).re) atTop (𝓝 (-1/5:ℝ)) := by
    have h := (Complex.continuous_re.tendsto (-1/5:ℂ)).comp (hcan r hr hra).1
    convert h using 1
    · funext t
      simp only [Function.comp_def,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero]
    · norm_num
  have hM (t : ℝ) : Tendsto
      (fun N : ℕ => (liClockPairedEtaFiniteArithmeticClockResponse N r (t:ℂ)).re)
      atTop (𝓝 (liClockPairedEtaArithmeticClockResponse r (t:ℂ)).re) := by
    exact (Complex.continuous_re.tendsto _).comp (hfinite r hr hrb (t:ℂ))
  exact fixedClockFractionalFloor_not_eventually _ _ _ hC hE hM hc hθ

/-- Literal ratio of the actual union-of-intervals partition to its filled contiguous model. -/
def liClockPairedEtaFiniteGapRatio (N : ℕ) (s : ℂ) : ℂ :=
  pairedEtaFiniteLaplacePartition N s/
    liClockPairedEtaContiguousPartition (Real.log (2*(N:ℝ))) s

/-- Literal logarithmic source of the finite actual-to-model gap ratio. -/
def liClockPairedEtaFiniteGapSourceTrace (N : ℕ) (z : ℂ) : ℂ :=
  I*logDeriv (liClockPairedEtaFiniteGapRatio N) (1/2+z*I)

/-- Gap clock from the literal finite ratio, retaining the entire arithmetic source. -/
def liClockPairedEtaFiniteGapClockResponse (N : ℕ) (r : ℝ) (t : ℂ) : ℂ :=
  liClockCentralTraceSineContour (liClockPairedEtaFiniteGapSourceTrace N) r t

private theorem contiguous_length_pos {N : ℕ} (hN : 0 < N) :
    0 < Real.log (2*(N:ℝ)) := by
  apply Real.log_pos
  have hn : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  linarith

private theorem finite_partition_ne_zero_of_core {N : ℕ} {s : ℂ}
    (heta : pairedEtaCorePartialSum N s ≠ 0) : pairedEtaFiniteLaplacePartition N s ≠ 0 := by
  intro hzero
  apply heta
  rw [pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition,hzero,mul_zero]

theorem analyticAt_liClockPairedEtaFiniteGapRatio {N : ℕ} (hN : 0 < N)
    {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ (liClockPairedEtaFiniteGapRatio N) s :=
  (analyticAt_liClockPairedEtaFiniteLaplacePartition_entire N s).div
    (analyticAt_liClockPairedEtaContiguousPartition _ s)
    (liClockPairedEtaContiguousPartition_ne_zero (contiguous_length_pos hN) hs)

/-- Exact regular-germ gap connection. Both filled partitions remain in the source. -/
theorem logDeriv_liClockPairedEtaFiniteGapRatio {N : ℕ} (hN : 0 < N)
    {s : ℂ} (hs : 0 < s.re) (heta : pairedEtaCorePartialSum N s ≠ 0) :
    logDeriv (liClockPairedEtaFiniteGapRatio N) s =
      logDeriv (pairedEtaCorePartialSum N) s-
        liClockPairedEtaContiguousConnection (Real.log (2*(N:ℝ))) s := by
  have hL := contiguous_length_pos hN
  have hA := finite_partition_ne_zero_of_core heta
  have hs0 : s ≠ 0 := by intro hzero; simp [hzero] at hs
  change logDeriv (fun w : ℂ => pairedEtaFiniteLaplacePartition N w/
    liClockPairedEtaContiguousPartition (Real.log (2*(N:ℝ))) w) s = _
  rw [logDeriv_div s hA (liClockPairedEtaContiguousPartition_ne_zero hL hs)
    (analyticAt_liClockPairedEtaFiniteLaplacePartition_entire N s).differentiableAt
    (analyticAt_liClockPairedEtaContiguousPartition _ s).differentiableAt,
    logDeriv_liClockPairedEtaContiguousPartition hL hs,
    logDeriv_liClockPairedEtaFiniteCore_eq_inverse_add_partition N hs0 hA]
  ring

theorem liClockPairedEtaFiniteArithmeticSourceTrace_eq_gap_add_contiguous {N : ℕ}
    (hN : 0 < N) {z : ℂ} (hs : 0 < (1/2+z*I).re)
    (heta : pairedEtaCorePartialSum N (1/2+z*I) ≠ 0) :
    liClockPairedEtaFiniteArithmeticSourceTrace N z =
      liClockPairedEtaFiniteGapSourceTrace N z+
        liClockPairedEtaContiguousSourceTrace (Real.log (2*(N:ℝ))) z := by
  unfold liClockPairedEtaFiniteArithmeticSourceTrace liClockPairedEtaFiniteGapSourceTrace
    liClockPairedEtaContiguousSourceTrace
  rw [logDeriv_liClockPairedEtaFiniteGapRatio hN hs heta]
  ring

theorem analyticAt_liClockPairedEtaFiniteGapSourceTrace {N : ℕ} (hN : 0 < N)
    {z : ℂ} (hs : 0 < (1/2+z*I).re)
    (heta : pairedEtaCorePartialSum N (1/2+z*I) ≠ 0) :
    AnalyticAt ℂ (liClockPairedEtaFiniteGapSourceTrace N) z := by
  have hR := analyticAt_liClockPairedEtaFiniteGapRatio hN hs
  have hn : liClockPairedEtaFiniteGapRatio N (1/2+z*I) ≠ 0 :=
    div_ne_zero (finite_partition_ne_zero_of_core heta)
      (liClockPairedEtaContiguousPartition_ne_zero (contiguous_length_pos hN) hs)
  have hq : AnalyticAt ℂ (logDeriv (liClockPairedEtaFiniteGapRatio N)) (1/2+z*I) :=
    hR.deriv.div hR hn
  exact analyticAt_const.mul (hq.comp (f := fun w : ℂ => 1/2+w*I)
    (analyticAt_const.add (analyticAt_id.mul analyticAt_const)))

/-- Exact all-complex gap clock. Circle-only eta regularity suffices. -/
theorem liClockPairedEtaFiniteGapClockResponse_eq_arithmetic_add_contiguous {N : ℕ}
    (hN : 0 < N) {r : ℝ} (hr : 0 < r) (hrhalf : r < 1/2)
    (heta : ∀ z ∈ sphere (0:ℂ) r, pairedEtaCorePartialSum N (1/2+z*I) ≠ 0)
    (t : ℂ) : liClockPairedEtaFiniteGapClockResponse N r t =
      liClockPairedEtaFiniteArithmeticClockResponse N r t+
        liClockPairedEtaContiguousClock (Real.log (2*(N:ℝ))) t := by
  have hL := contiguous_length_pos hN
  have hG : ContinuousOn (liClockPairedEtaFiniteGapSourceTrace N) (sphere (0:ℂ) r) := by
    intro z hz
    have hn : ‖z‖ ≤ r := (show ‖z‖=r by
      simpa only [mem_sphere_iff_norm,sub_zero] using hz).le
    exact (analyticAt_liClockPairedEtaFiniteGapSourceTrace hN
      (arithmetic_central_strip hrhalf hn).1 (heta z hz)).continuousAt.continuousWithinAt
  have hQ : ContinuousOn (liClockPairedEtaContiguousSourceTrace (Real.log (2*(N:ℝ))))
      (sphere (0:ℂ) r) :=
    (diffContOnCl_liClockPairedEtaContiguousSourceTrace hL hrhalf).continuousOn_ball.mono
      sphere_subset_closedBall
  have he : liClockPairedEtaFiniteArithmeticClockResponse N r t =
      liClockCentralTraceSineContour (fun z => liClockPairedEtaFiniteGapSourceTrace N z+
        liClockPairedEtaContiguousSourceTrace (Real.log (2*(N:ℝ))) z) r t := by
    unfold liClockPairedEtaFiniteArithmeticClockResponse liClockCentralTraceSineContour
    congr 1
    apply circleIntegral.integral_congr hr.le
    intro z hz
    dsimp only
    have hn : ‖z‖ ≤ r := (show ‖z‖=r by
      simpa only [mem_sphere_iff_norm,sub_zero] using hz).le
    rw [liClockPairedEtaFiniteArithmeticSourceTrace_eq_gap_add_contiguous hN
      (arithmetic_central_strip hrhalf hn).1 (heta z hz)]
  rw [he,arithmetic_contour_add hr hG hQ,
    liClockPairedEtaContiguousClock_eq_neg_contour hL hr hrhalf]
  change _ = (_+_)+ -_
  abel

/-- Exact finite compensation formula for the original eta prefix, never a model substitution. -/
theorem liClockPairedEtaFiniteClockResponse_eq_completion_sub_contiguous_add_gap {N : ℕ}
    (hN : 0 < N) {r : ℝ} (hr : 0 < r) (hrhalf : r < 1/2)
    (heta : ∀ z ∈ sphere (0:ℂ) r, pairedEtaCorePartialSum N (1/2+z*I) ≠ 0)
    (t : ℂ) : liClockPairedEtaFiniteClockResponse N r t =
      liClockPairedEtaCompletionClockResponse r t-
        liClockPairedEtaContiguousClock (Real.log (2*(N:ℝ))) t+
          liClockPairedEtaFiniteGapClockResponse N r t := by
  rw [liClockPairedEtaFiniteClockResponse_eq_arithmetic_add_completion N hr hrhalf heta,
    liClockPairedEtaFiniteGapClockResponse_eq_arithmetic_add_contiguous hN hr hrhalf heta]
  ring

/-- Every fixed complex finite gap clock converges to the literal actual eta clock. -/
theorem exists_liClockPairedEtaFiniteGapClockResponse_fixed_tendsto_radius :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1/128 ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ t : ℂ,
      Tendsto (fun N : ℕ => liClockPairedEtaFiniteGapClockResponse N r t)
        atTop (𝓝 (liClockPairedEtaArithmeticClockResponse r t)) := by
  obtain ⟨r₀,hr₀,hr₀s,hfinite⟩ := exists_liClockPairedEtaFiniteArithmeticClockResponse_fixed_tendsto_radius
  refine ⟨r₀,hr₀,hr₀s,?_⟩
  intro r hr hrr t
  have hrs : r ≤ 1/128 := hrr.le.trans hr₀s
  have hrhalf : r < 1/2 := lt_of_le_of_lt hrs (by norm_num)
  have hsum : Tendsto (fun N : ℕ => liClockPairedEtaFiniteArithmeticClockResponse N r t+
      liClockPairedEtaContiguousClock (Real.log (2*(N:ℝ))) t)
      atTop (𝓝 (liClockPairedEtaArithmeticClockResponse r t)) := by
    simpa only [add_zero] using (hfinite r hr hrr t).add
      (liClockPairedEtaContiguousClock_log_two_mul_tendsto_zero t)
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ),liClockPairedEta_eventually_valueTail_le_one_sixteenth]
    with N hN hsmall
  have heta : ∀ z ∈ sphere (0:ℂ) r, pairedEtaCorePartialSum N (1/2+z*I) ≠ 0 := by
    intro z hz hzero
    have hn : ‖z‖ ≤ 1/128 := (show ‖z‖=r by
      simpa only [mem_sphere_iff_norm,sub_zero] using hz).le.trans hrs
    have hf := liClockPairedEtaFiniteCore_re_gt_one_sixteenth N hsmall hn
    norm_num [hzero] at hf
  exact (liClockPairedEtaFiniteGapClockResponse_eq_arithmetic_add_contiguous hN hr hrhalf heta t).symm

/-- No fixed fractional loss of completion can bound the literal finite gap
throughout any eventual positive logarithmic clock window. -/
theorem exists_liClockPairedEtaFiniteGapClockResponse_fractional_floor_no_go_radius :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1/128 ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∀ c : ℝ, 0 < c → ∀ θ : ℝ, θ < 1 →
        ¬ (∀ᶠ N : ℕ in atTop, ∀ t : ℝ, 0 < t →
          t ≤ c*Real.log (2*(N:ℝ)+1) →
            -θ*(liClockPairedEtaCompletionClockResponse r (t:ℂ)).re ≤
              (liClockPairedEtaFiniteGapClockResponse N r (t:ℂ)).re) := by
  obtain ⟨a,ha,has,hcan⟩ := exists_liClockPairedEtaArithmeticClockResponse_cancellation_radius
  obtain ⟨b,hb,hbs,hfinite⟩ := exists_liClockPairedEtaFiniteGapClockResponse_fixed_tendsto_radius
  refine ⟨min a b,lt_min ha hb,(min_le_left _ _).trans has,?_⟩
  intro r hr hrr c hc θ hθ
  have hra : r < a := hrr.trans_le (min_le_left _ _)
  have hrb : r < b := hrr.trans_le (min_le_right _ _)
  have hrhalf : r < 1/2 := lt_of_le_of_lt (hra.le.trans has) (by norm_num)
  have hC : Tendsto (fun t : ℝ => Real.exp (-(2/5)*t)*
      (liClockPairedEtaCompletionClockResponse r (t:ℂ)).re) atTop (𝓝 (1/5:ℝ)) := by
    have h := (Complex.continuous_re.tendsto (1/5:ℂ)).comp
      (liClockPairedEtaCompletionClockResponse_exp_neg_mul_tendsto hr hrhalf)
    convert h using 1
    · funext t
      simp only [Function.comp_def,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero]
    · norm_num
  have hE : Tendsto (fun t : ℝ => Real.exp (-(2/5)*t)*
      (liClockPairedEtaArithmeticClockResponse r (t:ℂ)).re) atTop (𝓝 (-1/5:ℝ)) := by
    have h := (Complex.continuous_re.tendsto (-1/5:ℂ)).comp (hcan r hr hra).1
    convert h using 1
    · funext t
      simp only [Function.comp_def,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero]
    · norm_num
  have hM (t : ℝ) : Tendsto
      (fun N : ℕ => (liClockPairedEtaFiniteGapClockResponse N r (t:ℂ)).re)
      atTop (𝓝 (liClockPairedEtaArithmeticClockResponse r (t:ℂ)).re) := by
    exact (Complex.continuous_re.tendsto _).comp (hfinite r hr hrb (t:ℂ))
  exact fixedClockFractionalFloor_not_eventually _ _ _ hC hE hM hc hθ

end
end RHTower

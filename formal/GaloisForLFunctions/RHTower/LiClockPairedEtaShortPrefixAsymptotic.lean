import GaloisForLFunctions.RHTower.LiClockPairedEtaFiniteFilledDeflation
import Mathlib.Topology.Algebra.Order.Field
import GaloisForLFunctions.RHTower.LiClockCentralTraceSineGrowth
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Exact short-prefix pole asymptotics

These are statements about the literal finite eta clocks. A short fixed prefix has
normalized completed response `-1`, while the first deflated prefix has normalized
response `1/5`. Larger circles are used only for the analytic filled remainder;
literal completion values at removable endpoints are never identified with it.
The eventual-prefix growing-window sign question remains open.
-/

open Complex Set Metric Filter Topology MeasureTheory RiemannGaussian
namespace RHTower
noncomputable section

private theorem unscale_real_atBot {f : ℝ → ℝ} {k c : ℝ}
    (hk : 0 < k) (hc : c < 0)
    (hf : Tendsto (fun t => Real.exp (-k*t)*f t) atTop (𝓝 c)) :
    Tendsto f atTop atBot := by
  have he : Tendsto (fun t : ℝ => Real.exp (k*t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hk)
  have hm := hf.neg_mul_atTop hc he
  convert hm using 1
  funext t
  have hexp : Real.exp (-k*t)*Real.exp (k*t)=1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc
    f t = f t*1 := by ring
    _ = f t*(Real.exp (-k*t)*Real.exp (k*t)) := by rw [hexp]
    _ = (Real.exp (-k*t)*f t)*Real.exp (k*t) := by ring

private theorem unscale_real_atTop {f : ℝ → ℝ} {k c : ℝ}
    (hk : 0 < k) (hc : 0 < c)
    (hf : Tendsto (fun t => Real.exp (-k*t)*f t) atTop (𝓝 c)) :
    Tendsto f atTop atTop := by
  have he : Tendsto (fun t : ℝ => Real.exp (k*t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hk)
  have hm := hf.pos_mul_atTop hc he
  convert hm using 1
  funext t
  have hexp : Real.exp (-k*t)*Real.exp (k*t)=1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc
    f t = f t*1 := by ring
    _ = f t*(Real.exp (-k*t)*Real.exp (k*t)) := by rw [hexp]
    _ = (Real.exp (-k*t)*f t)*Real.exp (k*t) := by ring

private theorem secondPole_odd_deriv (j : ℕ) :
    iteratedDeriv (2*j+1) (fun z : ℂ => 1/(z-5*I/2)) 0 =
      (-1:ℂ)^j * (4/25)^(j+1) * ((2*j+1).factorial:ℂ) := by
  have hfun : (fun z : ℂ => 1/(z-5*I/2)) = (fun z => (1*z-5*I/2)⁻¹) := by
    funext z
    simp
  rw [hfun, iteratedDeriv_eq_iterate, iter_deriv_inv_linear_sub]
  simp only [one_mul, zero_sub, one_pow, mul_one]
  have hinv : (-(5*I/2):ℂ)⁻¹ = (2/5)*I := by
    apply inv_eq_of_mul_eq_one_right
    ring_nf
    norm_num [Complex.I_sq]
  have hexp : (-1-(2*j+1:ℕ):ℤ) = -((2*j+2:ℕ):ℤ) := by omega
  rw [hexp, zpow_neg, zpow_natCast, ← inv_pow, hinv]
  have hp : ((2/5)*I:ℂ)^(2*j+2) = (-4/25:ℂ)^(j+1) := by
    rw [show 2*j+2 = 2*(j+1) by omega, pow_mul]
    norm_num [mul_pow, Complex.I_sq]
  rw [hp]
  have hodd : (-1:ℂ)^(2*j+1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hodd, neg_div, neg_pow (4/25:ℂ), pow_succ (-1:ℂ)]
  ring

private theorem secondPole_traceTerm (j : ℕ) (t : ℂ) :
    liClockCentralTraceSineContourTerm (fun z : ℂ => -(1/(z-5*I/2))) t j =
      -(2/5:ℂ)*(((2/5:ℂ)*t)^(2*j+1)/((2*j+1).factorial:ℂ)) := by
  unfold liClockCentralTraceSineContourTerm
  rw [iteratedDeriv_fun_neg, secondPole_odd_deriv]
  have hfac : ((2*j+1).factorial:ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2*j+1)
  have hsign : (-1:ℂ)^j * (-1:ℂ)^j = 1 := by
    rw [← mul_pow]
    norm_num
  have hcoef : (-1:ℂ)^j * -((-1:ℂ)^j*(4/25)^(j+1)*((2*j+1).factorial:ℂ)) =
      -((4/25)^(j+1)*((2*j+1).factorial:ℂ)) := by
    calc
      _ = -(((-1:ℂ)^j*(-1:ℂ)^j)*((4/25)^(j+1)*((2*j+1).factorial:ℂ))) := by ring
      _ = _ := by rw [hsign, one_mul]
  rw [hcoef]
  have hp4 : (4/25:ℂ)^(j+1) = (2/5:ℂ)^(2*j+2) := by
    rw [show (4/25:ℂ) = (2/5)^2 by norm_num, ← pow_mul]
    congr 1
  rw [hp4, show 2*j+2 = (2*j+1)+1 by omega, pow_succ, mul_pow]
  field_simp [hfac]

private theorem secondPole_diffContOnCl {r : ℝ} (hr : r < 5/2) :
    DiffContOnCl ℂ (fun z : ℂ => -(1/(z-5*I/2))) (ball 0 r) := by
  have ha : AnalyticOnNhd ℂ (fun z : ℂ => 1/(z-5*I/2)) (closedBall 0 r) := by
    intro z hz
    have hn : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
    have hnz : z-5*I/2 ≠ 0 := by
      intro h
      have heq : z = 5*I/2 := sub_eq_zero.mp h
      have hnorm : ‖z‖ = (5/2:ℝ) := by
        rw [heq]
        norm_num [norm_div, norm_mul, norm_I]
      linarith
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) hnz
  exact (ha.differentiableOn.diffContOnCl_ball (Subset.refl _)).neg

/-- The literal second completion pole has positive clock coefficient exactly `2/5`. -/
private theorem liClockCentralTraceSineContour_second_pole {r : ℝ} (hr : 0 < r)
    (hrpole : r < 5/2) (t : ℂ) :
    liClockCentralTraceSineContour (fun z : ℂ => -I/(1/2+z*I+2)) r t =
      (2/5:ℂ)*Complex.sinh ((2/5:ℂ)*t) := by
  have hfun : (fun z : ℂ => -I/(1/2+z*I+2)) =
      (fun z : ℂ => -(1/(z-5*I/2))) := by
    funext z
    have hden : (1/2+z*I+2:ℂ) = I*(z-5*I/2) := by
      ring_nf
      norm_num [Complex.I_sq]
      ring
    rw [hden, ← div_div]
    simp only [neg_div, div_self Complex.I_ne_zero]
  rw [hfun, liClockCentralTraceSineContour_eq_neg_tsum hr (secondPole_diffContOnCl hrpole)]
  simp_rw [secondPole_traceTerm]
  rw [tsum_mul_left, (Complex.hasSum_sinh ((2/5:ℂ)*t)).tsum_eq]
  ring

/-- Literal contour additivity needs only continuous sources on its positive-radius circle. -/
private theorem liClockCentralTraceSineContour_add {r : ℝ} (hr : 0 < r) {T U : ℂ → ℂ}
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


private theorem exists_shortPrefix_source_radius {N : ℕ} (hN : 0 < N)
    (hshort : Real.log (2*(N:ℝ)) < 2*Real.pi) :
    ∃ ρ : ℝ, 1/2 < ρ ∧ ρ < 5/2 ∧ ρ*Real.log (2*(N:ℝ)) < Real.pi := by
  have hNreal : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hL : 0 < Real.log (2*(N:ℝ)) := Real.log_pos (by linarith)
  have hph : (1/2:ℝ) < Real.pi/Real.log (2*(N:ℝ)) :=
    (lt_div_iff₀ hL).2 (by linarith)
  obtain ⟨ρ, hρhalf, hρmax⟩ := exists_between
    (lt_min (by norm_num : (1/2:ℝ)<5/2) hph)
  exact ⟨ρ, hρhalf, hρmax.trans_le (min_le_left _ _),
    (lt_div_iff₀ hL).mp (hρmax.trans_le (min_le_right _ _))⟩

private theorem shortPrefix_central_strip {r : ℝ} (hr : r < 1/2) {z : ℂ} (hz : ‖z‖ ≤ r) :
    0 < (1/2+z*I).re ∧ (1/2+z*I).re < 1 := by
  have hi := abs_le.mp ((Complex.abs_im_le_norm z).trans hz)
  norm_num [Complex.mul_re]
  constructor <;> linarith

private theorem shortPrefix_eta_ne_zero {N : ℕ} (hN : 0 < N)
    (hshort : Real.log (2*(N:ℝ)) < 2*Real.pi) {r : ℝ} (hrhalf : r < 1/2)
    (z : ℂ) (hz : z ∈ sphere (0:ℂ) r) :
    pairedEtaCorePartialSum N (1/2+z*I) ≠ 0 := by
  have hn : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hL : 0 < Real.log (2*(N:ℝ)) := Real.log_pos (by linarith)
  have hnorm : ‖z‖ = r := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
  have hphase : |(1/2+z*I).im| * Real.log (2*(N:ℝ)) ≤ Real.pi := by
    have hi : |(1/2+z*I).im| ≤ r := by
      simpa [Complex.mul_im, hnorm] using Complex.abs_re_le_norm z
    apply le_of_lt
    calc
      _ ≤ r*Real.log (2*(N:ℝ)) := mul_le_mul_of_nonneg_right hi hL.le
      _ < (1/2)*Real.log (2*(N:ℝ)) := mul_lt_mul_of_pos_right hrhalf hL
      _ < Real.pi := by linarith
  have hln := liClockPairedEtaFiniteLaplacePartition_ne_zero hN hphase
  have hs : (1/2+z*I:ℂ) ≠ 0 := by
    intro h
    have hl := (shortPrefix_central_strip hrhalf hnorm.le).1
    rw [h] at hl
    norm_num at hl
  rw [pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition]
  exact mul_ne_zero hs hln

private theorem traceContour_congr {r : ℝ} (hr : 0 < r) {T U : ℂ → ℂ}
    (heq : ∀ z ∈ sphere (0:ℂ) r, T z=U z) (t : ℂ) :
    liClockCentralTraceSineContour T r t = liClockCentralTraceSineContour U r t := by
  unfold liClockCentralTraceSineContour
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro z hz
  dsimp only
  rw [heq z hz]

private theorem finiteDeflatedClock_eq_filled (N : ℕ) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (t : ℂ) :
    liClockPairedEtaFiniteDeflatedClockResponse N r t =
      liClockCentralTraceSineContour (liClockPairedEtaFiniteFilledSourceTrace N) r t := by
  apply traceContour_congr hr _ t
  intro z hz
  have hn : ‖z‖ ≤ r :=
    (show ‖z‖ = r by simpa only [mem_sphere_iff_norm, sub_zero] using hz).le
  have hs := shortPrefix_central_strip hrhalf hn
  exact liClockPairedEtaFiniteDeflatedSourceTrace_eq_filled N hs.1 hs.2

private theorem shortPrefixClock_split_filled {N : ℕ} (hN : 0 < N)
    (hshort : Real.log (2*(N:ℝ)) < 2*Real.pi) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (t : ℂ) :
    liClockPairedEtaFiniteClockResponse N r t = -2*Complex.sinh (2*t)+
      liClockCentralTraceSineContour (liClockPairedEtaFiniteFilledSourceTrace N) r t := by
  rw [liClockPairedEtaFiniteClockResponse_eq_neg_two_sinh_add_deflated N hr hrhalf
    (shortPrefix_eta_ne_zero hN hshort hrhalf), finiteDeflatedClock_eq_filled N hr hrhalf t]

/-- A short literal prefix has an exact leading pole and a strictly slower complete remainder. -/
theorem exists_liClockPairedEtaShortPrefixClockResponse_error_bound {N : ℕ} (hN : 0 < N)
    (hshort : Real.log (2*(N:ℝ)) < 2*Real.pi) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) :
    ∃ ρ : ℝ, 1/2 < ρ ∧ ρ < 5/2 ∧ ρ*Real.log (2*(N:ℝ)) < Real.pi ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℂ,
        ‖liClockPairedEtaFiniteClockResponse N r t+2*Complex.sinh (2*t)‖ ≤
          M*Real.sinh (‖t‖/ρ) := by
  obtain ⟨ρ, hρhalf, hργ, hρphase⟩ := exists_shortPrefix_source_radius hN hshort
  have hT := diffContOnCl_liClockPairedEtaFiniteFilledSourceTrace_ball hN hργ hρphase
  have hrr : r ≤ ρ := hrhalf.le.trans hρhalf.le
  obtain ⟨M, hM, hb⟩ := exists_liClockCentralTraceSineContour_growth_bound hr hrr hT
  refine ⟨ρ, hρhalf, hργ, hρphase, M, hM, fun t => ?_⟩
  rw [shortPrefixClock_split_filled hN hshort hr hrhalf t]
  convert hb t using 1
  congr 1
  ring_nf

/-- The same literal finite clock has normalized leading coefficient exactly negative one. -/
theorem liClockPairedEtaShortPrefixClockResponse_exp_neg_mul_tendsto {N : ℕ} (hN : 0 < N)
    (hshort : Real.log (2*(N:ℝ)) < 2*Real.pi) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) :
    Tendsto (fun t : ℝ => (Real.exp (-2*t):ℂ)*liClockPairedEtaFiniteClockResponse N r (t:ℂ))
      atTop (𝓝 (-1:ℂ)) := by
  obtain ⟨ρ, hρhalf, hργ, hρphase⟩ := exists_shortPrefix_source_radius hN hshort
  have hρpos : 0 < ρ := by linarith
  have hT := diffContOnCl_liClockPairedEtaFiniteFilledSourceTrace_ball hN hργ hρphase
  have hdec := liClockCentralTraceSineContour_exp_neg_mul_tendsto_zero hr
    (hrhalf.le.trans hρhalf.le) hT (k:=2)
    ((div_lt_iff₀ hρpos).2 (by linarith))
  have hsinh := liClock_exp_neg_mul_complex_sinh_ofReal_tendsto (by norm_num : (0:ℝ)<2)
  convert (hsinh.const_mul (-2:ℂ)).add hdec using 1
  · funext t
    rw [shortPrefixClock_split_filled hN hshort hr hrhalf (t:ℂ)]
    norm_num only [Complex.ofReal_ofNat]
    ring_nf
  · norm_num

/-- Every such actual fixed prefix is negative throughout a tail and escapes to minus infinity. -/
theorem liClockPairedEtaShortPrefixClockResponse_re_tendsto_atBot {N : ℕ} (hN : 0 < N)
    (hshort : Real.log (2*(N:ℝ)) < 2*Real.pi) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) :
    Tendsto (fun t : ℝ => (liClockPairedEtaFiniteClockResponse N r (t:ℂ)).re) atTop atBot := by
  have hf := liClockPairedEtaShortPrefixClockResponse_exp_neg_mul_tendsto hN hshort hr hrhalf
  have hre : Tendsto (fun t : ℝ => Real.exp (-2*t)*
      (liClockPairedEtaFiniteClockResponse N r (t:ℂ)).re) atTop (𝓝 (-1:ℝ)) := by
    simpa only [Function.comp_def, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.neg_re, Complex.one_re] using
      (Complex.continuous_re.tendsto (-1:ℂ)).comp hf
  exact unscale_real_atBot (by norm_num) (by norm_num) hre

private theorem firstPrefix_secondPole_source_eq :
    (fun z : ℂ => -I/(1/2+z*I+2)) = (fun z : ℂ => -(1/(z-5*I/2))) := by
  funext z
  have hden : (1/2+z*I+2:ℂ) = I*(z-5*I/2) := by
    ring_nf
    norm_num [Complex.I_sq]
    ring
  rw [hden, ← div_div]
  simp only [neg_div, div_self Complex.I_ne_zero]

/-- The first literal deflated clock separates its next pole from a radius-three analytic source. -/
theorem liClockPairedEtaFirstPrefixDeflatedClockResponse_eq_secondPole_add_filled
    {r : ℝ} (hr : 0 < r) (hrhalf : r < 1/2) (t : ℂ) :
    liClockPairedEtaFiniteDeflatedClockResponse 1 r t =
      (2/5:ℂ)*Complex.sinh ((2/5:ℂ)*t)+
        liClockCentralTraceSineContour liClockPairedEtaFirstPrefixTwiceFilledSourceTrace r t := by
  have hrpole : r < 5/2 := by linarith
  have heq : liClockPairedEtaFiniteDeflatedClockResponse 1 r t =
      liClockCentralTraceSineContour
        (fun z => -I/(1/2+z*I+2)+liClockPairedEtaFirstPrefixTwiceFilledSourceTrace z) r t := by
    apply traceContour_congr hr _ t
    intro z hz
    have hn : ‖z‖ < 1/2 :=
      (show ‖z‖ = r by simpa only [mem_sphere_iff_norm, sub_zero] using hz).trans_lt hrhalf
    exact liClockPairedEtaFirstPrefixDeflatedSourceTrace_eq_secondPole_add_twiceFilled_of_norm_lt_half hn
  have hP : ContinuousOn (fun z : ℂ => -I/(1/2+z*I+2)) (sphere 0 r) := by
    rw [firstPrefix_secondPole_source_eq]
    exact (secondPole_diffContOnCl hrpole).continuousOn_ball.mono sphere_subset_closedBall
  have hR : ContinuousOn liClockPairedEtaFirstPrefixTwiceFilledSourceTrace (sphere 0 r) :=
    (diffContOnCl_liClockPairedEtaFirstPrefixTwiceFilledSourceTrace_ball_three.mono
      (ball_subset_ball (by linarith : r ≤ 3))).continuousOn_ball.mono sphere_subset_closedBall
  rw [heq, liClockCentralTraceSineContour_add hr hP hR,
    liClockCentralTraceSineContour_second_pole hr hrpole t]

/-- Its entire complex remainder grows no faster than a complete radius-three sinh envelope. -/
theorem exists_liClockPairedEtaFirstPrefixDeflatedClockResponse_error_bound
    {r : ℝ} (hr : 0 < r) (hrhalf : r < 1/2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℂ,
      ‖liClockPairedEtaFiniteDeflatedClockResponse 1 r t-
        (2/5:ℂ)*Complex.sinh ((2/5:ℂ)*t)‖ ≤ M*Real.sinh (‖t‖/3) := by
  obtain ⟨M, hM, hb⟩ := exists_liClockCentralTraceSineContour_growth_bound hr
    (by linarith : r ≤ 3) diffContOnCl_liClockPairedEtaFirstPrefixTwiceFilledSourceTrace_ball_three
  refine ⟨M, hM, fun t => ?_⟩
  rw [liClockPairedEtaFirstPrefixDeflatedClockResponse_eq_secondPole_add_filled hr hrhalf t]
  simpa only [add_sub_cancel_left] using hb t

/-- The first actual deflated clock has positive normalized leading coefficient exactly `1/5`. -/
theorem liClockPairedEtaFirstPrefixDeflatedClockResponse_exp_neg_mul_tendsto
    {r : ℝ} (hr : 0 < r) (hrhalf : r < 1/2) :
    Tendsto (fun t : ℝ => (Real.exp (-(2/5)*t):ℂ)*
      liClockPairedEtaFiniteDeflatedClockResponse 1 r (t:ℂ)) atTop (𝓝 (1/5:ℂ)) := by
  have hdec := liClockCentralTraceSineContour_exp_neg_mul_tendsto_zero hr
    (by linarith : r ≤ 3) diffContOnCl_liClockPairedEtaFirstPrefixTwiceFilledSourceTrace_ball_three
    (k:=2/5) (by norm_num)
  have hsinh := liClock_exp_neg_mul_complex_sinh_ofReal_tendsto (by norm_num : (0:ℝ)<2/5)
  convert (hsinh.const_mul (2/5:ℂ)).add hdec using 1
  · funext t
    rw [liClockPairedEtaFirstPrefixDeflatedClockResponse_eq_secondPole_add_filled hr hrhalf (t:ℂ)]
    push_cast
    ring
  · norm_num

/-- The first literal deflated clock escapes to plus infinity despite the completed clock's negative tail. -/
theorem liClockPairedEtaFirstPrefixDeflatedClockResponse_re_tendsto_atTop
    {r : ℝ} (hr : 0 < r) (hrhalf : r < 1/2) :
    Tendsto (fun t : ℝ => (liClockPairedEtaFiniteDeflatedClockResponse 1 r (t:ℂ)).re)
      atTop atTop := by
  have hf := liClockPairedEtaFirstPrefixDeflatedClockResponse_exp_neg_mul_tendsto hr hrhalf
  have hre : Tendsto (fun t : ℝ => Real.exp (-(2/5)*t)*
      (liClockPairedEtaFiniteDeflatedClockResponse 1 r (t:ℂ)).re) atTop (𝓝 (1/5:ℝ)) := by
    have h := (Complex.continuous_re.tendsto (1/5:ℂ)).comp hf
    simp only [Function.comp_def, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at h
    norm_num at h
    simpa only [neg_mul] using h
  exact unscale_real_atTop (by norm_num) (by norm_num) hre


/-- On a common tail the first prefix is negative, while its positive deflation is below the removed pole. -/
theorem liClockPairedEtaFirstPrefixClockResponse_eventual_sign_separation
    {r : ℝ} (hr : 0 < r) (hrhalf : r < 1/2) :
    ∀ᶠ t : ℝ in atTop,
      (liClockPairedEtaFiniteClockResponse 1 r (t:ℂ)).re < 0 ∧
      0 < (liClockPairedEtaFiniteDeflatedClockResponse 1 r (t:ℂ)).re ∧
      (liClockPairedEtaFiniteDeflatedClockResponse 1 r (t:ℂ)).re < 2*Real.sinh (2*t) := by
  have hlog : Real.log (2*((1:ℕ):ℝ)) < 2*Real.pi := by
    norm_num only [Nat.cast_one, mul_one]
    have hh := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)
    linarith [Real.pi_gt_three]
  have hneg := (liClockPairedEtaShortPrefixClockResponse_re_tendsto_atBot
    (by norm_num : 0<(1:ℕ)) hlog hr hrhalf).eventually_lt_atBot 0
  have hpos := (liClockPairedEtaFirstPrefixDeflatedClockResponse_re_tendsto_atTop
    hr hrhalf).eventually_gt_atTop 0
  filter_upwards [hneg, hpos] with t ht hp
  refine ⟨ht, hp, ?_⟩
  have heq := liClockPairedEtaFiniteClockResponse_eq_neg_two_sinh_add_deflated
    1 hr hrhalf (shortPrefix_eta_ne_zero (by norm_num : 0<(1:ℕ)) hlog hrhalf) (t:ℂ)
  have hre := congrArg Complex.re heq
  have hs : Complex.sinh (2*(t:ℂ)) = (Real.sinh (2*t):ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
      (Complex.ofReal_sinh (2*t)).symm
  rw [hs] at hre
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hre
  norm_num at hre
  linarith

end
end RHTower

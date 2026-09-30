import GaloisForLFunctions.RHTower.LiClockPairedEtaFiniteFilledDeflation
import GaloisForLFunctions.RHTower.LiClockPairedEtaFirstPrefixGammaBounds
import Mathlib.Analysis.Calculus.Deriv.CompMul
/-!
# Exact first finite-prefix Gamma clock and global signs

The literal first Laplace interval reflects as an entire source identity.
Its regular quotient connection is even around the central point, so every
selected odd jet and the complete quotient clock vanish. The literal
filled deflation therefore has exactly the shifted Gamma packet, with every
source index and factorial retained. All-complex identities transfer the
sharp packet norm, genuine zero-clock slope, and strict positive real
bounds to the actual source. Restoring the rational pole makes the original
first-prefix clock strictly negative at every positive real clock.

These first-prefix statements do not settle the eventual large-prefix
pointwise growing-window condition.
-/

open scoped Interval
open GaloisForLFunctions Complex Set Metric Filter Topology MeasureTheory RiemannGaussian
namespace RHTower
noncomputable section

/-- Literal first interval Laplace source, reflected as an entire identity. -/
theorem liClock_firstLaplace_neg (s : ℂ) :
    pairedEtaFiniteLaplacePartition 1 (-s) =
      Complex.exp ((Real.log 2 : ℂ) * s) * pairedEtaFiniteLaplacePartition 1 s := by
  have hL (w : ℂ) : pairedEtaFiniteLaplacePartition 1 w =
      ∫ u : ℝ in 0..Real.log 2, Complex.exp (-w * (u : ℂ)) := by
    simp [pairedEtaFiniteLaplacePartition]
  rw [hL, hL]
  simp only [neg_neg]
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => Complex.exp (s * (u : ℂ))) (a := 0) (b := Real.log 2) (Real.log 2)
  calc
    (∫ u : ℝ in 0..Real.log 2, Complex.exp (s * (u : ℂ))) =
        ∫ u : ℝ in 0..Real.log 2, Complex.exp (s * ((Real.log 2 - u : ℝ) : ℂ)) := by
      simpa only [sub_self, sub_zero] using hsub.symm
    _ = ∫ u : ℝ in 0..Real.log 2,
        Complex.exp ((Real.log 2 : ℂ) * s) * Complex.exp (-s * (u : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      change Complex.exp (s * ((Real.log 2 - u : ℝ) : ℂ)) =
        Complex.exp ((Real.log 2 : ℂ) * s) * Complex.exp (-s * (u : ℂ))
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- Reflection of the logarithmic connection is asserted only at regular source values. -/
theorem liClock_firstLaplace_logDeriv_neg (s : ℂ)
    (hL : pairedEtaFiniteLaplacePartition 1 s ≠ 0) :
    logDeriv (pairedEtaFiniteLaplacePartition 1) (-s) =
      -(Real.log 2 : ℂ) - logDeriv (pairedEtaFiniteLaplacePartition 1) s := by
  let L : ℂ → ℂ := pairedEtaFiniteLaplacePartition 1
  let l : ℂ := (Real.log 2 : ℂ)
  have hfun : (fun w : ℂ => L (-w)) = fun w => Complex.exp (l * w) * L w :=
    funext liClock_firstLaplace_neg
  have he : HasDerivAt (fun w : ℂ => Complex.exp (l * w))
      (Complex.exp (l * s) * l) s :=
    (Complex.hasDerivAt_exp (l * s)).comp s
      (by convert! (hasDerivAt_id s).const_mul l using 1; simp)
  have hLs : HasDerivAt L (deriv L s) s :=
    (analyticAt_liClockPairedEtaFiniteLaplacePartition_entire 1 s).differentiableAt.hasDerivAt
  have hd := congrArg (fun f : ℂ → ℂ => deriv f s) hfun
  rw [deriv_comp_neg] at hd
  have hprod : deriv (fun w : ℂ => Complex.exp (l * w) * L w) s =
      Complex.exp (l * s) * l * L s + Complex.exp (l * s) * deriv L s := by
    convert! (he.mul hLs).deriv using 1
  rw [hprod] at hd
  change -(deriv L (-s)) = Complex.exp (l * s) * l * L s +
    Complex.exp (l * s) * deriv L s at hd
  change deriv L (-s) / L (-s) = -l - deriv L s / L s
  have hLneg : L (-s) = Complex.exp (l * s) * L s := liClock_firstLaplace_neg s
  rw [hLneg]
  have hexp : Complex.exp (l * s) ≠ 0 := Complex.exp_ne_zero _
  have hLn : L s ≠ 0 := hL
  have hDn : deriv L (-s) = Complex.exp (l * s) * (-l * L s - deriv L s) := by
    linear_combination -hd
  rw [hDn, mul_div_mul_left _ _ hexp, sub_div, mul_div_cancel_right₀ _ hLn]

/-- Exact first-prefix quotient connection; its parity is a regular germ identity. -/
def liClockFirstPrefixRatioConnection (s : ℂ) : ℂ :=
  logDeriv (pairedEtaFiniteLaplacePartition 1) s -
    logDeriv (pairedEtaFiniteLaplacePartition 1) (s - 1)

/-- Central trace of the exact quotient connection. -/
def liClockFirstPrefixRatioTrace (z : ℂ) : ℂ :=
  I * liClockFirstPrefixRatioConnection (1 / 2 + z * I)

theorem liClock_firstPrefixRatioConnection_reflect (s : ℂ)
    (hL : pairedEtaFiniteLaplacePartition 1 s ≠ 0)
    (hLshift : pairedEtaFiniteLaplacePartition 1 (s - 1) ≠ 0) :
    liClockFirstPrefixRatioConnection (1 - s) = liClockFirstPrefixRatioConnection s := by
  unfold liClockFirstPrefixRatioConnection
  rw [show 1 - s = -(s - 1) by ring, show -(s - 1) - 1 = -s by ring,
    liClock_firstLaplace_logDeriv_neg (s - 1) hLshift,
    liClock_firstLaplace_logDeriv_neg s hL]
  ring

private theorem firstLaplace_central_nonzero {r : ℝ} (hrhalf : r < 1 / 2)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    pairedEtaFiniteLaplacePartition 1 (1 / 2 + z * I) ≠ 0 ∧
      pairedEtaFiniteLaplacePartition 1 (1 / 2 + z * I - 1) ≠ 0 := by
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl1 : Real.log 2 ≤ 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    norm_num at h
    exact h.le
  have him : |(1 / 2 + z * I).im| ≤ ‖z‖ := by
    simpa [Complex.mul_im] using Complex.abs_re_le_norm z
  have hphase : |(1 / 2 + z * I).im| * Real.log 2 ≤ Real.pi := by
    calc
      _ ≤ ‖z‖ * Real.log 2 := mul_le_mul_of_nonneg_right him hl0
      _ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hl1 (norm_nonneg z)
      _ ≤ 1 / 2 := by simpa only [mul_one] using hz.trans hrhalf.le
      _ ≤ Real.pi := by linarith [Real.pi_gt_three]
  constructor
  · exact liClockPairedEtaFiniteLaplacePartition_ne_zero (by norm_num : 0 < (1 : ℕ))
      (by simpa using hphase)
  · exact liClockPairedEtaFiniteLaplacePartition_ne_zero (by norm_num : 0 < (1 : ℕ))
      (by simpa using hphase)

/-- Evenness on the whole actual regular central disk; no denominator premise remains. -/
theorem liClock_firstPrefixRatioTrace_even {r : ℝ} (hrhalf : r < 1 / 2)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    liClockFirstPrefixRatioTrace (-z) = liClockFirstPrefixRatioTrace z := by
  obtain ⟨hn, hd⟩ := firstLaplace_central_nonzero hrhalf hz
  unfold liClockFirstPrefixRatioTrace
  rw [show 1 / 2 + -z * I = 1 - (1 / 2 + z * I) by ring,
    liClock_firstPrefixRatioConnection_reflect (1 / 2 + z * I) hn hd]

/-- Every selected odd central jet of the actual first-prefix ratio trace vanishes. -/
theorem liClock_firstPrefixRatioTrace_odd_jet_zero (j : ℕ) :
    iteratedDeriv (2 * j + 1) liClockFirstPrefixRatioTrace 0 = 0 := by
  have he : (fun z : ℂ => liClockFirstPrefixRatioTrace (-z)) =ᶠ[𝓝 0]
      liClockFirstPrefixRatioTrace := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)] with z hz
    have hzN : ‖z‖ < (1 / 4 : ℝ) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact liClock_firstPrefixRatioTrace_even (by norm_num : (1 / 4 : ℝ) < 1 / 2) hzN.le
  have hd := he.iteratedDeriv_eq (2 * j + 1)
  rw [iteratedDeriv_comp_neg] at hd
  have hsign : (-1 : ℂ) ^ (2 * j + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  simp only [neg_zero, smul_eq_mul, hsign, neg_mul, one_mul] at hd
  linear_combination -hd / 2

/-- The ratio trace is holomorphic at every point of the actual regular closed disk. -/
theorem analyticAt_liClockFirstPrefixRatioTrace_of_norm_le {r : ℝ} (hrhalf : r < 1 / 2)
    {z : ℂ} (hz : ‖z‖ ≤ r) : AnalyticAt ℂ liClockFirstPrefixRatioTrace z := by
  obtain ⟨hn, hd⟩ := firstLaplace_central_nonzero hrhalf hz
  have hL := analyticAt_liClockPairedEtaFiniteLaplacePartition_entire 1 (1 / 2 + z * I)
  have hLm := analyticAt_liClockPairedEtaFiniteLaplacePartition_entire 1 (1 / 2 + z * I - 1)
  have hq : AnalyticAt ℂ (logDeriv (pairedEtaFiniteLaplacePartition 1)) (1 / 2 + z * I) :=
    hL.deriv.div hL hn
  have hqm : AnalyticAt ℂ (logDeriv (pairedEtaFiniteLaplacePartition 1)) (1 / 2 + z * I - 1) :=
    hLm.deriv.div hLm hd
  have hc : AnalyticAt ℂ (fun w : ℂ => 1 / 2 + w * I) z :=
    analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  exact analyticAt_const.mul
    ((hq.comp (f := fun w : ℂ => 1 / 2 + w * I) hc).sub
      (hqm.comp (f := fun w : ℂ => 1 / 2 + w * I - 1) (hc.sub analyticAt_const)))

/-- The installed contour interface holds throughout the actual small disk. -/
theorem diffContOnCl_liClockFirstPrefixRatioTrace_ball {r : ℝ} (hrhalf : r < 1 / 2) :
    DiffContOnCl ℂ liClockFirstPrefixRatioTrace (ball (0 : ℂ) r) := by
  have ha : AnalyticOnNhd ℂ liClockFirstPrefixRatioTrace (closedBall (0 : ℂ) r) := by
    intro z hz
    exact analyticAt_liClockFirstPrefixRatioTrace_of_norm_le hrhalf
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  exact ha.differentiableOn.diffContOnCl_ball (Subset.refl _)

/-- The complete first-prefix ratio clock vanishes for every complex clock. -/
theorem liClock_firstPrefixRatioTrace_contour_eq_zero {r : ℝ} (hr : 0 < r)
    (hrhalf : r < 1 / 2) (t : ℂ) :
    liClockCentralTraceSineContour liClockFirstPrefixRatioTrace r t = 0 := by
  rw [liClockCentralTraceSineContour_eq_neg_tsum hr
    (diffContOnCl_liClockFirstPrefixRatioTrace_ball hrhalf)]
  simp only [liClockCentralTraceSineContourTerm, liClock_firstPrefixRatioTrace_odd_jet_zero,
    mul_zero, zero_mul, zero_div, tsum_zero, neg_zero]

/-- Literal filled-source connection splits into the shifted Gamma and exact ratio traces. -/
theorem liClock_firstPrefixFilledSourceTrace_eq_gamma_add_ratio {r : ℝ}
    (hrhalf : r < 1 / 2) {z : ℂ} (hz : ‖z‖ ≤ r) :
    liClockPairedEtaFiniteFilledSourceTrace 1 z =
      I * GaloisForLFunctions.gammaRealLogConnection (1 / 2 + z * I + 2) +
        liClockFirstPrefixRatioTrace z := by
  let s : ℂ := 1 / 2 + z * I
  let L : ℂ → ℂ := pairedEtaFiniteLaplacePartition 1
  let g : ℂ → ℂ := fun w => Gammaℝ (w + 2)
  obtain ⟨hn, hd⟩ := firstLaplace_central_nonzero hrhalf hz
  have hgamma : 0 < (s + 2).re := by
    have hi := abs_le.mp ((Complex.abs_im_le_norm z).trans hz)
    dsimp only [s]
    norm_num [Complex.mul_re]
    linarith
  have hgn : g s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hgamma
  have hgd : DifferentiableAt ℂ g s := by
    change DifferentiableAt ℂ (fun w : ℂ => Gammaℝ (w + 2)) s
    exact (differentiableAt_Gammaℝ_of_re_pos hgamma).comp s
      ((hasDerivAt_id s).add_const 2).differentiableAt
  have hLd : DifferentiableAt ℂ L s :=
    (analyticAt_liClockPairedEtaFiniteLaplacePartition_entire 1 s).differentiableAt
  have hLmd : DifferentiableAt ℂ (fun w : ℂ => L (w - 1)) s :=
    (analyticAt_liClockPairedEtaFiniteLaplacePartition_entire 1 (s - 1)).differentiableAt.comp
      (f := fun w : ℂ => w - 1) s ((hasDerivAt_id s).sub_const 1).differentiableAt
  have hc : (-2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hfun : liClockPairedEtaFiniteFilledDeflation 1 =
      fun w : ℂ => (-2 * (Real.pi : ℂ)) * (g w * L w / L (w - 1)) := by
    funext w
    unfold liClockPairedEtaFiniteFilledDeflation
    dsimp only [g, L]
    ring
  have hglog : logDeriv g s = GaloisForLFunctions.gammaRealLogConnection (s + 2) := by
    change deriv (fun w : ℂ => Gammaℝ (w + 2)) s / Gammaℝ (s + 2) = _
    rw [deriv_comp_add_const]
    change logDeriv Gammaℝ (s + 2) = _
    rw [RiemannGaussian.logDeriv_Gammaℝ hgamma]
    unfold GaloisForLFunctions.gammaRealLogConnection
    rw [Complex.ofReal_log Real.pi_pos.le]
    ring
  have hLmlog : logDeriv (fun w : ℂ => L (w - 1)) s = logDeriv L (s - 1) := by
    simp only [logDeriv_apply, sub_eq_add_neg, deriv_comp_add_const]
  have hnL : L s ≠ 0 := hn
  have hdL : L (s - 1) ≠ 0 := hd
  have hlog : logDeriv (liClockPairedEtaFiniteFilledDeflation 1) s =
      GaloisForLFunctions.gammaRealLogConnection (s + 2) +
        liClockFirstPrefixRatioConnection s := by
    rw [hfun, logDeriv_const_mul (f := fun w : ℂ => g w * L w / L (w - 1)) s _ hc,
      logDeriv_div (f := fun w : ℂ => g w * L w) (g := fun w : ℂ => L (w - 1))
        s (mul_ne_zero hgn hnL) hdL (hgd.mul hLd) hLmd,
      logDeriv_mul (f := g) (g := L) s hgn hnL hgd hLd, hglog, hLmlog]
    unfold liClockFirstPrefixRatioConnection
    dsimp only [L]
    ring
  change I * logDeriv (liClockPairedEtaFiniteFilledDeflation 1) s =
    I * GaloisForLFunctions.gammaRealLogConnection (s + 2) + I * liClockFirstPrefixRatioConnection s
  rw [hlog]
  ring


private theorem firstPrefix_strip {r : ℝ} (hr : r < 1/2) {z : ℂ} (hz : ‖z‖ ≤ r) :
    0 < (1/2+z*I).re ∧ (1/2+z*I).re < 1 := by
  have hi := abs_le.mp ((Complex.abs_im_le_norm z).trans hz)
  norm_num [Complex.mul_re]
  constructor <;> linarith

private theorem firstPrefix_phase_radius {r : ℝ} (hr : r < 1/2) :
    r*Real.log (2*((1:ℕ):ℝ)) < Real.pi := by
  norm_num only [Nat.cast_one, mul_one]
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLu : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)
    linarith
  have hprod := mul_lt_mul_of_pos_right hr hL
  nlinarith [Real.pi_gt_three]

private theorem firstPrefix_filled_regular {r : ℝ} (hr : r < 1/2) :
    DiffContOnCl ℂ (liClockPairedEtaFiniteFilledSourceTrace 1) (ball 0 r) :=
  diffContOnCl_liClockPairedEtaFiniteFilledSourceTrace_ball (by norm_num) (by linarith)
    (firstPrefix_phase_radius hr)

/-- The regular literal deflation is exactly its filled-source contour, with arbitrary finite prefix. -/
theorem liClockPairedEtaFiniteDeflatedClockResponse_eq_filledContour (N : ℕ) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (t : ℂ) :
    liClockPairedEtaFiniteDeflatedClockResponse N r t =
      liClockCentralTraceSineContour (liClockPairedEtaFiniteFilledSourceTrace N) r t := by
  unfold liClockPairedEtaFiniteDeflatedClockResponse liClockCentralTraceSineContour
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro z hz
  dsimp only
  have hn : ‖z‖ ≤ r :=
    (show ‖z‖ = r by simpa only [mem_sphere_iff_norm, sub_zero] using hz).le
  have hs := firstPrefix_strip hrhalf hn
  rw [liClockPairedEtaFiniteDeflatedSourceTrace_eq_filled N hs.1 hs.2]

private def firstPrefixGammaSourceTrace (z : ℂ) : ℂ :=
  I*gammaRealLogConnection (1/2+z*I+2)

private theorem firstPrefixGammaSourceTrace_odd (j : ℕ) :
    iteratedDeriv (2*j+1) firstPrefixGammaSourceTrace 0 =
      (-1:ℂ)^(j+1)*((2*j+1).factorial:ℂ)*
        ∑' n : ℕ, (2*(n:ℂ)+5/2)^(-((2*j+2:ℕ):ℤ)) := by
  unfold firstPrefixGammaSourceTrace
  have hc : (fun z : ℂ => gammaRealLogConnection (1/2+z*I+2)) =
      (fun z => (fun s => gammaRealLogConnection (s+2)) (I*z+1/2)) := by
    funext z
    congr 1
    ring
  rw [iteratedDeriv_const_mul_field,hc]
  change I*iteratedDeriv (2*j+1)
    (fun z => (fun s => gammaRealLogConnection (s+2)) (I*z+1/2)) 0 = _
  rw [liClock_iteratedDeriv_comp_affine (2*j+1)
    (fun s : ℂ => gammaRealLogConnection (s+2)) I (1/2) 0]
  simp only [mul_zero,zero_add]
  rw [liClock_gammaRealLogConnection_filled_odd]
  have hi : (I:ℂ)*(I:ℂ)^(2*j+1) = (-1:ℂ)^(j+1) := by
    rw [← pow_succ',show 2*j+1+1=2*(j+1) by omega,pow_mul,Complex.I_sq]
  rw [← mul_assoc,← mul_assoc,hi]

private theorem firstPrefixGammaConnection_analytic :
    AnalyticAt ℂ (fun s => gammaRealLogConnection (s+2)) (1/2:ℂ) := by
  have hd : AnalyticAt ℂ Complex.digamma (((1/2:ℂ)+2)/2) := by
    apply analyticAt_digamma_of_offPoles
    intro p hp
    have hh := congrArg Complex.re hp
    norm_num at hh
    have hn : 0 ≤ (p:ℝ) := Nat.cast_nonneg p
    linarith
  have ha : AnalyticAt ℂ (fun s : ℂ => (s+2)/2) (1/2:ℂ) :=
    (analyticAt_id.add analyticAt_const).div_const
  unfold gammaRealLogConnection
  exact analyticAt_const.add ((hd.comp (f := fun s : ℂ => (s+2)/2) ha).div_const)

private theorem firstPrefixGammaSourceTrace_analytic :
    AnalyticAt ℂ firstPrefixGammaSourceTrace 0 := by
  have ha : AnalyticAt ℂ (fun z : ℂ => 1/2+z*I) 0 :=
    analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hc : AnalyticAt ℂ (fun z : ℂ => gammaRealLogConnection ((1/2+z*I)+2)) 0 := by
    have hg : AnalyticAt ℂ (fun s => gammaRealLogConnection (s+2)) (1/2+(0:ℂ)*I) := by
      simpa only [zero_mul,add_zero] using firstPrefixGammaConnection_analytic
    exact hg.comp (f := fun z : ℂ => 1/2+z*I) ha
  exact analyticAt_const.mul hc

private theorem firstPrefixGammaSourceTrace_term_eq (t : ℂ) (j : ℕ) :
    liClockCentralTraceSineContourTerm firstPrefixGammaSourceTrace t j =
      -((∑' n : ℕ,(2*(n:ℂ)+5/2)^(-((2*j+2:ℕ):ℤ)))*
        t^(2*j+1)/((2*j+1).factorial:ℂ)) := by
  unfold liClockCentralTraceSineContourTerm
  rw [firstPrefixGammaSourceTrace_odd]
  have hfac : ((2*j+1).factorial:ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2*j+1)
  have hsign : (-1:ℂ)^j*(-1:ℂ)^(j+1) = -1 := by
    rw [pow_succ,← mul_assoc,← mul_pow]
    norm_num
  have hs : (-1:ℂ)^j*((-1:ℂ)^(j+1)*((2*j+1).factorial:ℂ)*
      ∑' n : ℕ,(2*(n:ℂ)+5/2)^(-((2*j+2:ℕ):ℤ))) =
      -((2*j+1).factorial:ℂ)*∑' n : ℕ,(2*(n:ℂ)+5/2)^(-((2*j+2:ℕ):ℤ)) := by
    calc
      _ = ((-1:ℂ)^j*(-1:ℂ)^(j+1))*((2*j+1).factorial:ℂ)*
        ∑' n : ℕ,(2*(n:ℂ)+5/2)^(-((2*j+2:ℕ):ℤ)) := by ring
      _ = _ := by rw [hsign]; ring
  rw [hs]
  field_simp [hfac]

private theorem firstPrefixFilledSourceTrace_odd (j : ℕ) :
    iteratedDeriv (2*j+1) (liClockPairedEtaFiniteFilledSourceTrace 1) 0 =
      (-1:ℂ)^(j+1)*((2*j+1).factorial:ℂ)*
        ∑' n : ℕ, (2*(n:ℂ)+5/2)^(-((2*j+2:ℕ):ℤ)) := by
  have he : liClockPairedEtaFiniteFilledSourceTrace 1 =ᶠ[𝓝 0]
      (fun z => firstPrefixGammaSourceTrace z + liClockFirstPrefixRatioTrace z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1/4)] with z hz
    have hn : ‖z‖ < (1/4 : ℝ) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact liClock_firstPrefixFilledSourceTrace_eq_gamma_add_ratio
      (by norm_num : (1/4 : ℝ) < 1/2) hn.le
  have ha : AnalyticAt ℂ liClockFirstPrefixRatioTrace (0:ℂ) :=
    analyticAt_liClockFirstPrefixRatioTrace_of_norm_le
      (by norm_num : (1/4 : ℝ) < 1/2) (by norm_num)
  rw [he.iteratedDeriv_eq (2*j+1)]
  change iteratedDeriv (2*j+1) (firstPrefixGammaSourceTrace + liClockFirstPrefixRatioTrace) 0 = _
  rw [iteratedDeriv_add firstPrefixGammaSourceTrace_analytic.contDiffAt ha.contDiffAt,
    firstPrefixGammaSourceTrace_odd, liClock_firstPrefixRatioTrace_odd_jet_zero, add_zero]

private theorem firstPrefixFilledSourceTrace_term_eq (t : ℂ) (j : ℕ) :
    liClockCentralTraceSineContourTerm (liClockPairedEtaFiniteFilledSourceTrace 1) t j =
      -((∑' n : ℕ,(2*(n:ℂ)+5/2)^(-((2*j+2:ℕ):ℤ)))*
        t^(2*j+1)/((2*j+1).factorial:ℂ)) := by
  have he : liClockCentralTraceSineContourTerm (liClockPairedEtaFiniteFilledSourceTrace 1) t j =
      liClockCentralTraceSineContourTerm firstPrefixGammaSourceTrace t j := by
    unfold liClockCentralTraceSineContourTerm
    rw [firstPrefixFilledSourceTrace_odd,firstPrefixGammaSourceTrace_odd]
  exact he.trans (firstPrefixGammaSourceTrace_term_eq t j)

/-- Exact entire Gamma odd-jet series for the literal first-prefix deflated clock. -/
theorem liClockPairedEtaFirstPrefixDeflatedClockResponse_eq_gamma_oddSum {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (t : ℂ) :
    liClockPairedEtaFiniteDeflatedClockResponse 1 r t =
      ∑' j : ℕ, (∑' n : ℕ,(2*(n:ℂ)+5/2)^(-((2*j+2:ℕ):ℤ)))*
        t^(2*j+1)/((2*j+1).factorial:ℂ) := by
  rw [liClockPairedEtaFiniteDeflatedClockResponse_eq_filledContour 1 hr hrhalf,
    liClockCentralTraceSineContour_eq_neg_tsum hr (firstPrefix_filled_regular hrhalf)]
  simp_rw [firstPrefixFilledSourceTrace_term_eq]
  rw [tsum_neg,neg_neg]

/-- Literal deflation is the full shifted Gamma packet for every complex clock. -/
theorem liClockPairedEtaFirstPrefixDeflatedClockResponse_eq_gammaClock {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (t : ℂ) :
    liClockPairedEtaFiniteDeflatedClockResponse 1 r t =
      liClockPairedEtaFirstPrefixGammaClock t := by
  rw [liClockPairedEtaFirstPrefixDeflatedClockResponse_eq_gamma_oddSum hr hrhalf,
    liClockPairedEtaFirstPrefixGammaClock_eq_tsum_odd]

private theorem firstPrefix_eta_nonzero {r : ℝ} (hrhalf : r < 1/2)
    {z : ℂ} (hz : ‖z‖ ≤ r) : pairedEtaCorePartialSum 1 (1/2+z*I) ≠ 0 := by
  have hs := firstPrefix_strip hrhalf hz
  have hn : (1/2+z*I : ℂ) ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  rw [pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition]
  exact mul_ne_zero hn (firstLaplace_central_nonzero hrhalf hz).1

/-- Exact source clock, retaining the removed rational pole and every Gamma atom. -/
theorem liClockPairedEtaFirstPrefixClockResponse_eq_neg_two_sinh_add_gammaClock {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (t : ℂ) :
    liClockPairedEtaFiniteClockResponse 1 r t =
      -2*Complex.sinh (2*t)+liClockPairedEtaFirstPrefixGammaClock t := by
  have heta : ∀ z ∈ sphere (0:ℂ) r, pairedEtaCorePartialSum 1 (1/2+z*I) ≠ 0 := by
    intro z hz
    exact firstPrefix_eta_nonzero hrhalf
      (show ‖z‖ ≤ r from (show ‖z‖ = r by
        simpa only [mem_sphere_iff_norm, sub_zero] using hz).le)
  rw [liClockPairedEtaFiniteClockResponse_eq_neg_two_sinh_add_deflated 1 hr hrhalf heta,
    liClockPairedEtaFirstPrefixDeflatedClockResponse_eq_gammaClock hr hrhalf]

/-- The full literal deflated clock obeys its sharp complex Gamma envelope. -/
theorem norm_liClockPairedEtaFirstPrefixDeflatedClockResponse_le {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (t : ℂ) :
    ‖liClockPairedEtaFiniteDeflatedClockResponse 1 r t‖ ≤
      (5*liClockPairedEtaFirstPrefixGammaSquareMass/2)*Real.sinh ((2/5)*‖t‖) := by
  rw [liClockPairedEtaFirstPrefixDeflatedClockResponse_eq_gammaClock hr hrhalf]
  exact norm_liClockPairedEtaFirstPrefixGammaClock_le t

theorem liClockPairedEtaFirstPrefixDeflatedClockResponse_im_ofReal {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (t : ℝ) :
    (liClockPairedEtaFiniteDeflatedClockResponse 1 r (t:ℂ)).im = 0 := by
  rw [liClockPairedEtaFirstPrefixDeflatedClockResponse_eq_gammaClock hr hrhalf]
  exact liClockPairedEtaFirstPrefixGammaClock_im_ofReal t

private theorem firstPrefixClockResponse_re {r : ℝ} (hr : 0 < r) (hrhalf : r < 1/2)
    (t : ℝ) :
    (liClockPairedEtaFiniteClockResponse 1 r (t:ℂ)).re =
      -2*Real.sinh (2*t)+(liClockPairedEtaFirstPrefixGammaClock (t:ℂ)).re := by
  rw [liClockPairedEtaFirstPrefixClockResponse_eq_neg_two_sinh_add_gammaClock hr hrhalf]
  have hsi : Complex.sinh (2*(t:ℂ)) = (Real.sinh (2*t):ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using (Complex.ofReal_sinh (2*t)).symm
  rw [hsi]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  norm_num

theorem liClockPairedEtaFirstPrefixClockResponse_im_ofReal {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (t : ℝ) :
    (liClockPairedEtaFiniteClockResponse 1 r (t:ℂ)).im = 0 := by
  rw [liClockPairedEtaFirstPrefixClockResponse_eq_neg_two_sinh_add_gammaClock hr hrhalf]
  have hsi : Complex.sinh (2*(t:ℂ)) = (Real.sinh (2*t):ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using (Complex.ofReal_sinh (2*t)).symm
  rw [hsi]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    liClockPairedEtaFirstPrefixGammaClock_im_ofReal]
  norm_num

/-- The deflated literal source is strictly positive for every positive real clock. -/
theorem liClockPairedEtaFirstPrefixDeflatedClockResponse_re_pos {r t : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (ht : 0 < t) :
    0 < (liClockPairedEtaFiniteDeflatedClockResponse 1 r (t:ℂ)).re := by
  rw [liClockPairedEtaFirstPrefixDeflatedClockResponse_eq_gammaClock hr hrhalf]
  exact liClockPairedEtaFirstPrefixGammaClock_re_pos ht

/-- Exact literal positive chain, including both sharp mass envelopes and explicit fences. -/
theorem liClockPairedEtaFirstPrefixDeflatedClockResponse_re_bounds {r t : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (ht : 0 < t) :
    ((2/5)*Real.sinh ((2/5)*t) < (liClockPairedEtaFiniteDeflatedClockResponse 1 r (t:ℂ)).re) ∧
    ((liClockPairedEtaFiniteDeflatedClockResponse 1 r (t:ℂ)).re <
      (5*liClockPairedEtaFirstPrefixGammaSquareMass/2)*Real.sinh ((2/5)*t)) ∧
    ((5*liClockPairedEtaFirstPrefixGammaSquareMass/2)*Real.sinh ((2/5)*t) <
      (9/10)*Real.sinh ((2/5)*t)) ∧
    ((liClockPairedEtaFiniteDeflatedClockResponse 1 r (t:ℂ)).re <
      (liClockPairedEtaFirstPrefixGammaSquareMass/2)*Real.sinh (2*t)) ∧
    ((liClockPairedEtaFirstPrefixGammaSquareMass/2)*Real.sinh (2*t) <
      (9/50)*Real.sinh (2*t)) := by
  rw [liClockPairedEtaFirstPrefixDeflatedClockResponse_eq_gammaClock hr hrhalf]
  exact liClockPairedEtaFirstPrefixGammaClock_re_bounds ht

/-- The actual first-prefix clock is quantitatively negative at every positive clock. -/
theorem liClockPairedEtaFirstPrefixClockResponse_re_lt_neg_ninety_one_fiftieths {r t : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (ht : 0 < t) :
    (liClockPairedEtaFiniteClockResponse 1 r (t:ℂ)).re < -(91/50)*Real.sinh (2*t) := by
  rw [firstPrefixClockResponse_re hr hrhalf]
  have h := liClockPairedEtaFirstPrefixGammaClock_re_lt_nine_fiftieths ht
  linarith

theorem liClockPairedEtaFirstPrefixClockResponse_re_neg {r t : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (ht : 0 < t) :
    (liClockPairedEtaFiniteClockResponse 1 r (t:ℂ)).re < 0 := by
  have h := liClockPairedEtaFirstPrefixClockResponse_re_lt_neg_ninety_one_fiftieths hr hrhalf ht
  have hs := Real.sinh_pos_iff.mpr (by positivity : 0 < 2*t)
  linarith

/-- Genuine complex derivative of the literal deflated source clock at zero. -/
theorem hasDerivAt_liClockPairedEtaFirstPrefixDeflatedClockResponse_zero {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) :
    HasDerivAt (liClockPairedEtaFiniteDeflatedClockResponse 1 r)
      (liClockPairedEtaFirstPrefixGammaSquareMass:ℂ) 0 := by
  have he : liClockPairedEtaFiniteDeflatedClockResponse 1 r = liClockPairedEtaFirstPrefixGammaClock :=
    funext (liClockPairedEtaFirstPrefixDeflatedClockResponse_eq_gammaClock hr hrhalf)
  rw [he]
  exact hasDerivAt_liClockPairedEtaFirstPrefixGammaClock_zero

theorem hasDerivAt_liClockPairedEtaFirstPrefixDeflatedClockResponse_re_zero {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) :
    HasDerivAt (fun t : ℝ => (liClockPairedEtaFiniteDeflatedClockResponse 1 r (t:ℂ)).re)
      liClockPairedEtaFirstPrefixGammaSquareMass 0 :=
  (hasDerivAt_liClockPairedEtaFirstPrefixDeflatedClockResponse_zero hr hrhalf).real_of_complex

/-- The exact reciprocal-square slope uses the positive punctured approach to zero. -/
theorem liClockPairedEtaFirstPrefixDeflatedClockResponse_re_div_tendsto_zero_right {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) :
    Tendsto (fun t : ℝ => (liClockPairedEtaFiniteDeflatedClockResponse 1 r (t:ℂ)).re/t)
      (nhdsWithin 0 (Ioi 0)) (𝓝 liClockPairedEtaFirstPrefixGammaSquareMass) := by
  simpa only [liClockPairedEtaFirstPrefixDeflatedClockResponse_eq_gammaClock hr hrhalf] using
    liClockPairedEtaFirstPrefixGammaClock_re_div_tendsto_zero_right

/-- Every global complex envelope coefficient is forced by the literal central slope. -/
theorem liClockPairedEtaFirstPrefixDeflatedClockResponse_sharp_norm_coefficient {r B : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2)
    (hB : ∀ t : ℂ, ‖liClockPairedEtaFiniteDeflatedClockResponse 1 r t‖ ≤
      B*Real.sinh ((2/5)*‖t‖)) : 5*liClockPairedEtaFirstPrefixGammaSquareMass/2 ≤ B := by
  apply liClockPairedEtaFirstPrefixGammaClock_sharp_norm_coefficient
  intro t
  rw [← liClockPairedEtaFirstPrefixDeflatedClockResponse_eq_gammaClock hr hrhalf]
  exact hB t

/-- The sharp removed-pole comparison coefficient is likewise an actual source invariant. -/
theorem liClockPairedEtaFirstPrefixDeflatedClockResponse_sharp_two_sinh_coefficient {r B : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2)
    (hB : ∀ t : ℝ, 0<t → (liClockPairedEtaFiniteDeflatedClockResponse 1 r (t:ℂ)).re ≤
      B*Real.sinh (2*t)) : liClockPairedEtaFirstPrefixGammaSquareMass/2 ≤ B := by
  apply liClockPairedEtaFirstPrefixGammaClock_sharp_two_sinh_coefficient
  intro t ht
  rw [← liClockPairedEtaFirstPrefixDeflatedClockResponse_eq_gammaClock hr hrhalf]
  exact hB t ht

end
end RHTower

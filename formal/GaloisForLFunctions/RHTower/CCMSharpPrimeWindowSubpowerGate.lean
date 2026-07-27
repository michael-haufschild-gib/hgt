import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowDirichlet
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowCancellation
import GaloisForLFunctions.RHTower.CCMRectangularSubpowerLowerGate

/-!
# The dyadic sharp prime-window subpower gate

The exact sharp prime coefficient

`4 * (1 - 1 / sqrt 2) * sqrt n - 2 * W(n)`

has the continued sharp source as its ordinary Dirichlet series.  Consequently an eventual
all-epsilon lower subpower bound on this coefficient is a Landau positivity hypothesis.  This
module turns that value relation into an unconditional implication to RH.
-/

open Complex Filter Function Set

noncomputable section

namespace RHTower

/-- The sharp source coefficient after adjoining a positive power correction. -/
def dyadicSharpPowerLandauCoefficient (C alpha : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    dyadicSharpPrimeSourceCoefficient n +
      C * powerCorrectionCoefficient alpha n

theorem dyadicSharpPowerLandauCoefficient_nonneg
    {C alpha : ℝ}
    (hlower : ∀ n : ℕ, n ≠ 0 →
      0 ≤ dyadicSharpPrimeSourceCoefficient n +
        C * powerCorrectionCoefficient alpha n) :
    ∀ n, 0 ≤ dyadicSharpPowerLandauCoefficient C alpha n := by
  intro n
  rw [dyadicSharpPowerLandauCoefficient]
  split_ifs with hn
  · exact le_rfl
  · exact hlower n hn

theorem dyadicSharpPowerLandauCoefficient_LSeriesSummable
    (C : ℝ) {alpha : ℝ} {s : ℂ}
    (hssharp : 3 / 2 < s.re) (hsalpha : 1 + alpha < s.re) :
    LSeriesSummable
      (fun n => ((dyadicSharpPowerLandauCoefficient C alpha n : ℝ) : ℂ)) s := by
  have hsharp := dyadicSharpPrimeSourceCoefficient_LSeriesSummable hssharp
  have hpower := (powerCorrectionCoefficient_LSeriesSummable hsalpha).smul (C : ℂ)
  have hadd : LSeriesSummable
      ((fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) +
        (C : ℂ) • (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ))) s :=
    hsharp.add hpower
  change Summable (LSeries.term
    (fun n => ((dyadicSharpPowerLandauCoefficient C alpha n : ℝ) : ℂ)) s)
  change Summable (LSeries.term _ s) at hadd
  apply hadd.congr
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [LSeries.term_zero]
  · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      dyadicSharpPowerLandauCoefficient, if_neg hn0,
      ofReal_add, ofReal_mul]

/-- Meromorphic continuation of the power-corrected nonnegative sharp Dirichlet series. -/
def dyadicSharpPowerLandauContinuation (C alpha : ℝ) (s : ℂ) : ℂ :=
  dyadicSharpPrimeContinuedSource s + C * riemannZeta (s - alpha)

theorem LSeries_dyadicSharpPowerLandauCoefficient_eq_continuation
    (C : ℝ) {alpha : ℝ} {s : ℂ}
    (hssharp : 3 / 2 < s.re) (hsalpha : 1 + alpha < s.re) :
    LSeries
        (fun n => ((dyadicSharpPowerLandauCoefficient C alpha n : ℝ) : ℂ)) s =
      dyadicSharpPowerLandauContinuation C alpha s := by
  have hsharp := dyadicSharpPrimeSourceCoefficient_LSeriesSummable hssharp
  have hpower0 := powerCorrectionCoefficient_LSeriesSummable hsalpha
  have hpower := hpower0.smul (C : ℂ)
  calc
    LSeries
        (fun n => ((dyadicSharpPowerLandauCoefficient C alpha n : ℝ) : ℂ)) s =
        LSeries
          ((fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) +
            (C : ℂ) •
              (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ))) s := by
      apply LSeries_congr
      intro n hn
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        dyadicSharpPowerLandauCoefficient, if_neg hn,
        ofReal_add, ofReal_mul]
    _ = LSeries
          (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) s +
        LSeries ((C : ℂ) •
          (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ))) s :=
      LSeries_add hsharp hpower
    _ = dyadicSharpPrimeContinuedSource s +
        C * LSeries
          (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ)) s := by
      rw [LSeries_dyadicSharpPrimeSourceCoefficient_eq_continuedSource hssharp,
        LSeries_smul]
    _ = dyadicSharpPowerLandauContinuation C alpha s := by
      rw [LSeries_powerCorrectionCoefficient_eq_riemannZeta hsalpha]
      rfl

/-- A sufficiently narrow ball about the real transverse boundary contains no shifted zero of
the pole-filled zeta, so the corrected sharp continuation is holomorphic there. -/
theorem differentiableOn_dyadicSharpPowerLandauContinuation_landauBall
    (C alpha : ℝ) {delta eta r : ℝ}
    (hdelta0 : 0 ≤ delta) (hr : 0 < r)
    (hrquarter : r ≤ 1 / 4) (hreta : r ≤ eta / 2)
    (halpha : alpha + r < delta)
    (hordinate : ∀ ρ : XiDivisorSupport, eta ≤ |(ρ : ℂ).im|) :
    DifferentiableOn ℂ (dyadicSharpPowerLandauContinuation C alpha)
      (Metric.ball (((1 + delta : ℝ) : ℂ)) r) := by
  intro s hs
  have hdist : ‖s - (((1 + delta : ℝ) : ℂ))‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hs
  have hsreLower : 1 / 2 < s.re := by
    have habs := Complex.abs_re_le_norm (s - (((1 + delta : ℝ) : ℂ)))
    rw [Complex.sub_re, ofReal_re] at habs
    have hlower : -r < s.re - (1 + delta) := by
      have := lt_of_le_of_lt habs hdist
      rw [abs_lt] at this
      exact this.1
    linarith
  have hsim : |s.im| < eta := by
    have himnorm : |(s - (((1 + delta : ℝ) : ℂ))).im| ≤
        ‖s - (((1 + delta : ℝ) : ℂ))‖ := Complex.abs_im_le_norm _
    have himzero : (s - (((1 + delta : ℝ) : ℂ))).im = s.im := by simp
    rw [himzero] at himnorm
    have : |s.im| < r := lt_of_le_of_lt himnorm hdist
    linarith
  have hreg : regularizedRiemannZeta (s - 1 / 2) ≠ 0 := by
    intro hz
    let t : ℂ := s - 1 / 2
    change regularizedRiemannZeta t = 0 at hz
    have htpos : 0 < t.re := by
      dsimp only [t]
      simp only [Complex.sub_re]
      norm_num
      linarith
    have ht1 : t ≠ 1 := by
      intro ht
      rw [ht, regularizedRiemannZeta_one] at hz
      norm_num at hz
    have hzeta : riemannZeta t = 0 := by
      rw [regularizedRiemannZeta_of_ne_one ht1] at hz
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ht1)
    have hxi : xi t = 0 := (xi_eq_zero_iff htpos ht1).mpr hzeta
    let ρ : XiDivisorSupport := ⟨t, mem_xi_divisor_support_of_eq_zero hxi⟩
    have him : t.im = s.im := by
      dsimp only [t]
      simp
    have hgap := hordinate ρ
    dsimp only [ρ] at hgap
    rw [him] at hgap
    linarith
  have hsource :=
    analyticAt_dyadicSharpPrimeContinuedSource_of_regularizedZeta_ne_zero
      hsreLower hreg
  have hre : 1 + alpha < s.re := by
    have habs := Complex.abs_re_le_norm (s - (((1 + delta : ℝ) : ℂ)))
    rw [Complex.sub_re, ofReal_re] at habs
    have hlower : -r < s.re - (1 + delta) := by
      have := lt_of_le_of_lt habs hdist
      rw [abs_lt] at this
      exact this.1
    linarith
  have hne : s - (alpha : ℂ) ≠ 1 := by
    intro heq
    have hreeq := congrArg Complex.re heq
    simp only [Complex.sub_re, ofReal_re, Complex.one_re] at hreeq
    linarith
  have hzeta : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (z - alpha)) s :=
    (differentiableAt_riemannZeta hne).comp s
      (differentiableAt_id.sub (differentiableAt_const (c := (alpha : ℂ))))
  simpa only [dyadicSharpPowerLandauContinuation] using
    hsource.differentiableAt.differentiableWithinAt.add
      (hzeta.differentiableWithinAt.const_mul (C : ℂ))

/-- To the right of an upper bound for all positive-transverse Xi zeros, the corrected sharp
continuation is holomorphic on the whole half-plane. -/
theorem differentiableOn_dyadicSharpPowerLandauContinuation_rightOf
    (C alpha delta : ℝ) (hdelta0 : 0 ≤ delta) (halpha : alpha < delta)
    (hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta) :
    DifferentiableOn ℂ (dyadicSharpPowerLandauContinuation C alpha)
      {s : ℂ | 1 + delta < s.re} := by
  intro s hs
  change 1 + delta < s.re at hs
  have hsHalf : 1 / 2 < s.re := by linarith
  have hreg : regularizedRiemannZeta (s - 1 / 2) ≠ 0 := by
    intro hz
    have hs1 : 1 < s.re := by linarith
    have htpos : 0 < (s - 1 / 2).re := by
      norm_num [Complex.sub_re]
      linarith
    have ht1 : s - 1 / 2 ≠ 1 := by
      intro ht
      rw [ht, regularizedRiemannZeta_one] at hz
      norm_num at hz
    have hzeta : riemannZeta (s - 1 / 2) = 0 := by
      rw [regularizedRiemannZeta_of_ne_one ht1] at hz
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ht1)
    have hxi : xi (s - 1 / 2) = 0 :=
      (xi_eq_zero_iff htpos ht1).mpr hzeta
    obtain ⟨q, hq⟩ :=
      exists_xiRightZeroCopy_shiftedPole_eq_of_xi_shifted_eq_zero hs1 hxi
    have hre := congrArg Complex.re hq
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re] at hre
    linarith [hupper q]
  have hsource :=
    analyticAt_dyadicSharpPrimeContinuedSource_of_regularizedZeta_ne_zero
      hsHalf hreg
  have hne : s - (alpha : ℂ) ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [Complex.sub_re, ofReal_re, Complex.one_re] at hre
    linarith
  have hzeta : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (z - alpha)) s :=
    (differentiableAt_riemannZeta hne).comp s
      (differentiableAt_id.sub (differentiableAt_const (c := (alpha : ℂ))))
  simpa only [dyadicSharpPowerLandauContinuation] using
    hsource.differentiableAt.differentiableWithinAt.add
      (hzeta.differentiableWithinAt.const_mul (C : ℂ))

/-- Once the corrected coefficient series converges at a point to the right of the transverse
boundary, its L-series is the sharp continuation throughout that right half-plane. -/
theorem dyadicSharpPowerLandauContinuation_eq_LSeries_rightOf
    (C alpha delta : ℝ) (hdelta0 : 0 ≤ delta) (halpha : alpha < delta)
    (hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    {sigma : ℝ} (hsigma : 1 + delta < sigma)
    (hsum : LSeriesSummable
      (fun n => ((dyadicSharpPowerLandauCoefficient C alpha n : ℝ) : ℂ))
      (sigma : ℂ)) :
    Set.EqOn (dyadicSharpPowerLandauContinuation C alpha)
      (LSeries
        (fun n => ((dyadicSharpPowerLandauCoefficient C alpha n : ℝ) : ℂ)))
      {s : ℂ | sigma < s.re} := by
  let U : Set ℂ := {s : ℂ | sigma < s.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt sigma).isPreconnected
  have hGdiff : DifferentiableOn ℂ
      (dyadicSharpPowerLandauContinuation C alpha) U :=
    (differentiableOn_dyadicSharpPowerLandauContinuation_rightOf
      C alpha delta hdelta0 halpha hupper).mono (by
        intro s hs
        change sigma < s.re at hs
        change 1 + delta < s.re
        linarith)
  have hLdiff : DifferentiableOn ℂ
      (LSeries
        (fun n => ((dyadicSharpPowerLandauCoefficient C alpha n : ℝ) : ℂ))) U := by
    intro s hs
    change sigma < s.re at hs
    have habs := hsum.abscissaOfAbsConv_le
    have habslt : LSeries.abscissaOfAbsConv
        (fun n => ((dyadicSharpPowerLandauCoefficient C alpha n : ℝ) : ℂ)) <
        s.re := lt_of_le_of_lt habs (by exact_mod_cast hs)
    exact (LSeries_hasDerivAt habslt).differentiableAt.differentiableWithinAt
  let x0 : ℝ := max sigma (3 / 2) + 1
  let z0 : ℂ := (x0 : ℂ)
  have hz0U : z0 ∈ U := by
    change sigma < x0
    dsimp only [x0]
    linarith [le_max_left sigma (3 / 2)]
  have hfar : 3 / 2 < z0.re := by
    change 3 / 2 < x0
    dsimp only [x0]
    linarith [le_max_right sigma (3 / 2)]
  have halphaFar : 1 + alpha < z0.re := by
    change 1 + alpha < x0
    dsimp only [x0]
    linarith [le_max_left sigma (3 / 2)]
  have hrightOpen : IsOpen {s : ℂ | 3 / 2 < s.re ∧ 1 + alpha < s.re} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_re)
  have hevent : dyadicSharpPowerLandauContinuation C alpha =ᶠ[nhds z0]
      LSeries
        (fun n => ((dyadicSharpPowerLandauCoefficient C alpha n : ℝ) : ℂ)) := by
    filter_upwards [hrightOpen.mem_nhds ⟨hfar, halphaFar⟩] with s hs
    exact (LSeries_dyadicSharpPowerLandauCoefficient_eq_continuation
      C hs.1 hs.2).symm
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hGdiff.analyticOnNhd hUopen) (hLdiff.analyticOnNhd hUopen)
      hUpre hz0U hevent

/-- Landau transfer across the real transverse boundary.  Under coefficientwise nonnegativity,
the corrected sharp series converges at a real point strictly left of every hypothetical
rightmost shifted Xi pole. -/
theorem exists_dyadicSharpPowerLandauCoefficient_summable_left_of_boundary
    (C alpha : ℝ) (hne : Nonempty XiRightZeroCopy)
    (halphaDelta : alpha < xiRightTransverseSup)
    (hlower : ∀ n : ℕ, n ≠ 0 →
      0 ≤ dyadicSharpPrimeSourceCoefficient n +
        C * powerCorrectionCoefficient alpha n) :
    ∃ sigma : ℝ,
      1 + alpha < sigma ∧
      sigma < 1 + xiRightTransverseSup ∧
      LSeriesSummable
        (fun n => ((dyadicSharpPowerLandauCoefficient C alpha n : ℝ) : ℂ))
        (sigma : ℂ) := by
  let delta : ℝ := xiRightTransverseSup
  have hdelta : 0 < delta := xiRightTransverseSup_pos hne
  have hdeltahalf : delta ≤ 1 / 2 := xiRightTransverseSup_le_half hne
  have hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta :=
    fun q => xiRightCenteredZero_re_le_sup q
  obtain ⟨eta, heta, hordinate⟩ := exists_xiDivisorSupport_abs_im_lower_bound
  let r : ℝ := min (min (1 / 8) (eta / 4)) ((delta - alpha) / 4)
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min
      (lt_min (by norm_num) (div_pos heta (by norm_num)))
      (div_pos (sub_pos.mpr (by simpa only [delta] using halphaDelta)) (by norm_num))
  have hrquarter : r ≤ 1 / 4 :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (by norm_num))
  have hreta : r ≤ eta / 2 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (by linarith))
  have hrgap : r ≤ (delta - alpha) / 4 := min_le_right _ _
  have halpha : alpha + r < delta := by
    have hgap : 0 < delta - alpha := by
      simpa only [delta] using sub_pos.mpr halphaDelta
    linarith
  have hnonneg := dyadicSharpPowerLandauCoefficient_nonneg hlower
  let sigmaFar : ℝ := 2
  have hsumFar : LSeriesSummable
      (fun n => ((dyadicSharpPowerLandauCoefficient C alpha n : ℝ) : ℂ))
      (sigmaFar : ℂ) := by
    apply dyadicSharpPowerLandauCoefficient_LSeriesSummable C
    · norm_num [sigmaFar]
    · dsimp only [sigmaFar]
      simp only [ofReal_re]
      linarith
  let Rfar : NNReal :=
    ⟨2 - delta - r / 16, by
      linarith [hdeltahalf, hrquarter]⟩
  have hGfar : DifferentiableOn ℂ (dyadicSharpPowerLandauContinuation C alpha)
      (Metric.closedBall (((sigmaFar + 1 : ℝ) : ℂ)) (Rfar : ℝ)) := by
    apply (differentiableOn_dyadicSharpPowerLandauContinuation_rightOf
      C alpha delta hdelta.le (by simpa only [delta] using halphaDelta) hupper).mono
    intro s hs
    rw [Metric.mem_closedBall, dist_eq_norm] at hs
    change 1 + delta < s.re
    have habs := Complex.abs_re_le_norm
      (s - (((sigmaFar + 1 : ℝ) : ℂ)))
    rw [Complex.sub_re, ofReal_re] at habs
    have hlower : -(Rfar : ℝ) ≤ s.re - (sigmaFar + 1) := by
      have := (le_trans habs hs)
      rw [abs_le] at this
      exact this.1
    change -(2 - delta - r / 16) ≤ s.re - (sigmaFar + 1) at hlower
    dsimp only [sigmaFar] at hlower
    linarith
  have hagreeFar : ∀ s : ℂ, sigmaFar < s.re →
      dyadicSharpPowerLandauContinuation C alpha s =
        LSeries
          (fun n => ((dyadicSharpPowerLandauCoefficient C alpha n : ℝ) : ℂ)) s := by
    intro s hs
    symm
    apply LSeries_dyadicSharpPowerLandauCoefficient_eq_continuation C
    · dsimp only [sigmaFar] at hs
      linarith
    · dsimp only [sigmaFar] at hs
      linarith
  let sigmaNear : ℝ := 1 + delta + r / 8
  have hsumNear : LSeriesSummable
      (fun n => ((dyadicSharpPowerLandauCoefficient C alpha n : ℝ) : ℂ))
      (sigmaNear : ℂ) := by
    apply landau_local_summability_transfer hnonneg (h := 1) (by norm_num)
      hsumFar (R := Rfar) (G := dyadicSharpPowerLandauContinuation C alpha)
      hGfar hagreeFar
    change sigmaFar + 1 - (2 - delta - r / 16) < sigmaNear
    dsimp only [sigmaFar, sigmaNear]
    linarith
  have hsigmaNear : 1 + delta < sigmaNear := by
    dsimp only [sigmaNear]
    linarith
  have heqNear := dyadicSharpPowerLandauContinuation_eq_LSeries_rightOf
    C alpha delta hdelta.le (by simpa only [delta] using halphaDelta) hupper
      hsigmaNear hsumNear
  have hcont := differentiableOn_dyadicSharpPowerLandauContinuation_landauBall
    C alpha hdelta.le hr hrquarter hreta halpha hordinate
  let h : ℝ := r / 8
  let R : NNReal := ⟨r / 2, div_nonneg hr.le (by norm_num)⟩
  have hh : 0 < h := by dsimp only [h]; positivity
  have hGlocal : DifferentiableOn ℂ
      (dyadicSharpPowerLandauContinuation C alpha)
      (Metric.closedBall (((sigmaNear + h : ℝ) : ℂ)) (R : ℝ)) := by
    apply hcont.mono
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm]
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hcenter :
        ‖(((sigmaNear + h : ℝ) : ℂ) - (((1 + delta : ℝ) : ℂ)))‖ = r / 4 := by
      have heq : (((sigmaNear + h : ℝ) : ℂ) - (((1 + delta : ℝ) : ℂ))) =
          ((r / 4 : ℝ) : ℂ) := by
        dsimp only [sigmaNear, h]
        push_cast
        ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
      positivity
    calc
      ‖z - (((1 + delta : ℝ) : ℂ))‖ ≤
          ‖z - (((sigmaNear + h : ℝ) : ℂ))‖ +
            ‖(((sigmaNear + h : ℝ) : ℂ) - (((1 + delta : ℝ) : ℂ)))‖ := by
        have := norm_add_le
          (z - (((sigmaNear + h : ℝ) : ℂ)))
          ((((sigmaNear + h : ℝ) : ℂ)) - (((1 + delta : ℝ) : ℂ)))
        simpa only [sub_add_sub_cancel] using this
      _ ≤ r / 2 + r / 4 := by
        rw [hcenter]
        exact add_le_add hz le_rfl
      _ < r := by linarith
  let sigma : ℝ := 1 + delta - r / 8
  have hsum : LSeriesSummable
      (fun n => ((dyadicSharpPowerLandauCoefficient C alpha n : ℝ) : ℂ))
      (sigma : ℂ) := by
    apply landau_local_summability_transfer hnonneg hh hsumNear
      (R := R) (G := dyadicSharpPowerLandauContinuation C alpha)
      hGlocal
    · intro s hs
      exact heqNear hs
    · change sigmaNear + h - r / 2 < sigma
      dsimp only [sigmaNear, h, sigma]
      linarith
  refine ⟨sigma, ?_, ?_, hsum⟩
  · dsimp only [sigma, delta]
    have hgap : 0 < xiRightTransverseSup - alpha := sub_pos.mpr halphaDelta
    have := hrgap
    dsimp only [delta] at this
    linarith
  · dsimp only [sigma, delta]
    linarith

/-- A convergent sharp-source L-series is holomorphic on its open half-plane of convergence. -/
theorem differentiableOn_LSeries_dyadicSharpPrimeSourceCoefficient
    {sigma : ℝ}
    (hsum : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ))
      (sigma : ℂ)) :
    DifferentiableOn ℂ
      (LSeries (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)))
      {s : ℂ | sigma < s.re} := by
  intro s hs
  change sigma < s.re at hs
  have habs := hsum.abscissaOfAbsConv_le
  have habslt : LSeries.abscissaOfAbsConv
      (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) < s.re :=
    lt_of_le_of_lt habs (by exact_mod_cast hs)
  exact (LSeries_hasDerivAt habslt).differentiableAt.differentiableWithinAt

/-- On any half-plane where the sharp coefficient series converges, the pole-cancelled source is
the shifted pole-filled zeta times that analytic L-series.  Cancellation makes both sides
holomorphic, so the far-right Dirichlet identity propagates across every shifted zero. -/
theorem dyadicSharpPrimeCancelledSource_eq_regularized_mul_LSeries
    {sigma : ℝ} (hsigma : 1 / 2 < sigma)
    (hsum : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ))
      (sigma : ℂ)) :
    Set.EqOn dyadicSharpPrimeCancelledSource
      (fun s => regularizedRiemannZeta (s - 1 / 2) *
        LSeries
          (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) s)
      {s : ℂ | sigma < s.re} := by
  let U : Set ℂ := {s : ℂ | sigma < s.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt sigma).isPreconnected
  have hcancelDiff : DifferentiableOn ℂ dyadicSharpPrimeCancelledSource U :=
    differentiableOn_dyadicSharpPrimeCancelledSource_rightHalf.mono (by
      intro s hs
      change sigma < s.re at hs
      change 1 / 2 < s.re
      linarith)
  have hLdiff := differentiableOn_LSeries_dyadicSharpPrimeSourceCoefficient hsum
  have hprodDiff : DifferentiableOn ℂ
      (fun s => regularizedRiemannZeta (s - 1 / 2) *
        LSeries
          (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) s) U := by
    intro s hs
    have hR : DifferentiableAt ℂ
        (fun z : ℂ => regularizedRiemannZeta (z - 1 / 2)) s :=
      differentiable_regularizedRiemannZeta.differentiableAt.comp s
        (differentiableAt_id.sub_const (1 / 2))
    exact hR.differentiableWithinAt.mul (hLdiff s hs)
  let x0 : ℝ := max sigma (3 / 2) + 1
  let z0 : ℂ := (x0 : ℂ)
  have hz0U : z0 ∈ U := by
    change sigma < x0
    dsimp only [x0]
    linarith [le_max_left sigma (3 / 2)]
  have hz0far : 3 / 2 < z0.re := by
    change 3 / 2 < x0
    dsimp only [x0]
    linarith [le_max_right sigma (3 / 2)]
  have hfarOpen : IsOpen {s : ℂ | 3 / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hevent : dyadicSharpPrimeCancelledSource =ᶠ[nhds z0]
      fun s => regularizedRiemannZeta (s - 1 / 2) *
        LSeries
          (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) s := by
    filter_upwards [hfarOpen.mem_nhds hz0far] with s hs
    have ht : s - 1 / 2 ≠ 1 := by
      intro heq
      have hre := congrArg Complex.re heq
      norm_num [Complex.sub_re] at hre
      linarith
    have htRe : 1 < (s - 1 / 2).re := by
      norm_num [Complex.sub_re]
      linarith
    have hR : regularizedRiemannZeta (s - 1 / 2) ≠ 0 := by
      rw [regularizedRiemannZeta_of_ne_one ht]
      exact mul_ne_zero (sub_ne_zero.mpr ht)
        (riemannZeta_ne_zero_of_one_lt_re htRe)
    rw [dyadicSharpPrimeCancelledSource_eq_mul_continuedSource hR,
      LSeries_dyadicSharpPrimeSourceCoefficient_eq_continuedSource hs]
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hcancelDiff.analyticOnNhd hUopen) (hprodDiff.analyticOnNhd hUopen)
      hUpre hz0U hevent

/-- Positive continuation theorem for the sharp values: convergence of their exact source series
at `sigma` places every shifted right Xi pole on or left of `sigma`. -/
theorem xiRightShiftedPole_re_le_of_dyadicSharpSource_summable
    {sigma : ℝ} (hsigma : 1 / 2 < sigma)
    (hsum : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ))
      (sigma : ℂ))
    (q : XiRightZeroCopy) :
    (xiRightShiftedPole q).re ≤ sigma := by
  by_contra hnot
  have hpole : sigma < (xiRightShiftedPole q).re := lt_of_not_ge hnot
  let U : Set ℂ := {s : ℂ | sigma < s.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hpoleU : xiRightShiftedPole q ∈ U := hpole
  have heqOn := dyadicSharpPrimeCancelledSource_eq_regularized_mul_LSeries
    hsigma hsum
  have hevent : dyadicSharpPrimeCancelledSource =ᶠ[nhds (xiRightShiftedPole q)]
      fun s => regularizedRiemannZeta (s - 1 / 2) *
        LSeries
          (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) s := by
    filter_upwards [hUopen.mem_nhds hpoleU] with s hs
    exact heqOn hs
  have horders := analyticOrderAt_congr hevent
  have hLdiff := differentiableOn_LSeries_dyadicSharpPrimeSourceCoefficient hsum
  have hLAn : AnalyticAt ℂ
      (LSeries (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)))
      (xiRightShiftedPole q) :=
    (hLdiff.analyticOnNhd hUopen) _ hpoleU
  have hRAn : AnalyticAt ℂ
      (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2))
      (xiRightShiftedPole q) := by
    have hreg : AnalyticAt ℂ regularizedRiemannZeta
        (xiRightShiftedPole q - 1 / 2) :=
      (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
        isOpen_univ) _ (Set.mem_univ _)
    have hshift : AnalyticAt ℂ (fun z : ℂ => z - 1 / 2)
        (xiRightShiftedPole q) := by fun_prop
    exact AnalyticAt.comp (f := fun z : ℂ => z - 1 / 2)
      (x := xiRightShiftedPole q) hreg hshift
  obtain ⟨m, hRorder, hcancelOrder⟩ :=
    analyticOrderAt_dyadicSharpPrimeCancelledSource_eq_pred q
  have hprod : (m + 1 : ℕ∞) ≤
      analyticOrderAt
        (fun s => regularizedRiemannZeta (s - 1 / 2) *
          LSeries
            (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) s)
        (xiRightShiftedPole q) := by
    rw [show (fun s => regularizedRiemannZeta (s - 1 / 2) *
          LSeries
            (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) s) =
        (fun s => regularizedRiemannZeta (s - 1 / 2)) *
          LSeries
            (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) by rfl,
      analyticOrderAt_mul hRAn hLAn, hRorder]
    exact le_add_right le_rfl
  rw [hcancelOrder] at horders
  rw [← horders] at hprod
  exact (not_lt_of_ge hprod) (by exact_mod_cast (Nat.lt_succ_self m))

/-- **Fixed-exponent zero-free law.**  A global `n^alpha` lower correction for the exact sharp
source coefficient bounds every positive transverse Xi displacement by `alpha`. -/
theorem xiRightCenteredZero_re_le_of_dyadicSharpSource_powerLower
    {C alpha : ℝ} (halpha : 0 ≤ alpha)
    (hlower : ∀ n : ℕ, n ≠ 0 →
      0 ≤ dyadicSharpPrimeSourceCoefficient n +
        C * powerCorrectionCoefficient alpha n)
    (q : XiRightZeroCopy) :
    (xiRightCenteredZero q).re ≤ alpha := by
  by_contra hnot
  have hqalpha : alpha < (xiRightCenteredZero q).re := lt_of_not_ge hnot
  have hne : Nonempty XiRightZeroCopy := ⟨q⟩
  have halphaSup : alpha < xiRightTransverseSup :=
    hqalpha.trans_le (xiRightCenteredZero_re_le_sup q)
  obtain ⟨sigma, hsigmaAlpha, hsigmaSup, hsumPower⟩ :=
    exists_dyadicSharpPowerLandauCoefficient_summable_left_of_boundary
      C alpha hne halphaSup hlower
  have hpower : LSeriesSummable
      (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ))
      (sigma : ℂ) := by
    apply powerCorrectionCoefficient_LSeriesSummable
    simpa only [ofReal_re] using hsigmaAlpha
  have hdiff := hsumPower.sub (hpower.smul (C : ℂ))
  have hsource : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ))
      (sigma : ℂ) := by
    change Summable (LSeries.term
      (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ))
      (sigma : ℂ))
    change Summable (LSeries.term _ (sigma : ℂ)) at hdiff
    apply hdiff.congr
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        dyadicSharpPowerLandauCoefficient, if_neg hn0,
        ofReal_add, ofReal_mul]
      ring
  have hsigmaHalf : 1 / 2 < sigma := by linarith
  have hpoleBound : ∀ r : XiRightZeroCopy,
      (xiRightShiftedPole r).re ≤ sigma :=
    xiRightShiftedPole_re_le_of_dyadicSharpSource_summable
      hsigmaHalf hsource
  have hcenterBound : ∀ r : XiRightZeroCopy,
      (xiRightCenteredZero r).re ≤ sigma - 1 := by
    intro r
    have hr := hpoleBound r
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re] at hr
    linarith
  have hsupBound : xiRightTransverseSup ≤ sigma - 1 := by
    apply csSup_le (Set.range_nonempty _)
    intro x hx
    obtain ⟨r, rfl⟩ := hx
    exact hcenterBound r
  linarith

/-- A single eventual `n^alpha` version of the prime-window inequality gives the explicit
zero-free region `Re rho ≤ 1/2 + alpha`. -/
theorem xiRightCenteredZero_re_le_of_eventually_dyadicWeightedPrimeWindow_upper
    {N : ℕ} {C alpha : ℝ} (halpha : 0 ≤ alpha) (hC : 0 ≤ C)
    (hwindow : ∀ n : ℕ, N ≤ n →
      dyadicWeightedPrimeWindow n ≤
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
          C * (n : ℝ) ^ alpha)
    (q : XiRightZeroCopy) :
    (xiRightCenteredZero q).re ≤ alpha := by
  have hevent : ∀ n : ℕ, N ≤ n → n ≠ 0 →
      0 ≤ dyadicSharpPrimeSourceCoefficient n +
        (2 * C) * powerCorrectionCoefficient alpha n := by
    intro n hnN hn0
    have h :=
      (dyadicWeightedPrimeWindow_upper_iff_sourceCoefficient_lower
        n C alpha).mp (hwindow n hnN)
    rw [powerCorrectionCoefficient, if_neg hn0]
    exact h
  obtain ⟨D, _hD, hglobal⟩ := exists_global_power_lower_of_eventual
    dyadicSharpPrimeSourceCoefficient halpha
      (mul_nonneg (by norm_num) hC) hevent
  exact xiRightCenteredZero_re_le_of_dyadicSharpSource_powerLower
    halpha hglobal q

/-- The user's eventual all-epsilon upper estimate for the exact dyadic von-Mangoldt window. -/
def DyadicWeightedPrimeWindowSubpowerUpper (N : ℕ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
      dyadicWeightedPrimeWindow n ≤
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
          C * (n : ℝ) ^ epsilon

/-- **Dyadic sharp-window subpower criterion.**  The requested inequality, for every positive
epsilon with an epsilon-dependent constant and from any fixed index onward, implies RH. -/
theorem riemannHypothesis_of_dyadicWeightedPrimeWindowSubpowerUpper
    {N : ℕ} (hwindow : DyadicWeightedPrimeWindowSubpowerUpper N) :
    RiemannHypothesis := by
  by_contra hRH
  have hne : Nonempty XiRightZeroCopy :=
    nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
  let delta : ℝ := xiRightTransverseSup
  let alpha : ℝ := delta / 4
  have hdelta : 0 < delta := xiRightTransverseSup_pos hne
  have halpha : 0 < alpha := by dsimp only [alpha]; positivity
  obtain ⟨C, hC, htail⟩ := hwindow alpha halpha
  have hevent : ∀ n : ℕ, N ≤ n → n ≠ 0 →
      0 ≤ dyadicSharpPrimeSourceCoefficient n +
        (2 * C) * powerCorrectionCoefficient alpha n := by
    intro n hnN hn0
    have h :=
      (dyadicWeightedPrimeWindow_upper_iff_sourceCoefficient_lower
        n C alpha).mp (htail n hnN)
    rw [powerCorrectionCoefficient, if_neg hn0]
    exact h
  obtain ⟨D, hD, hglobal⟩ := exists_global_power_lower_of_eventual
    dyadicSharpPrimeSourceCoefficient halpha.le (mul_nonneg (by norm_num) hC) hevent
  obtain ⟨sigma, hsigmaAlpha, hsigmaDelta, hsumPower⟩ :=
    exists_dyadicSharpPowerLandauCoefficient_summable_left_of_boundary
      D alpha hne (by
        dsimp only [alpha, delta]
        linarith) hglobal
  have hpower : LSeriesSummable
      (fun n => ((powerCorrectionCoefficient alpha n : ℝ) : ℂ))
      (sigma : ℂ) := by
    apply powerCorrectionCoefficient_LSeriesSummable
    simpa only [ofReal_re] using hsigmaAlpha
  have hdiff := hsumPower.sub (hpower.smul (D : ℂ))
  have hsource : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ))
      (sigma : ℂ) := by
    change Summable (LSeries.term
      (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ))
      (sigma : ℂ))
    change Summable (LSeries.term _ (sigma : ℂ)) at hdiff
    apply hdiff.congr
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        dyadicSharpPowerLandauCoefficient, if_neg hn0,
        ofReal_add, ofReal_mul]
      ring
  have hsigmaHalf : 1 / 2 < sigma := by
    have : 0 < alpha := halpha
    linarith
  have hpoleBound : ∀ q : XiRightZeroCopy,
      (xiRightShiftedPole q).re ≤ sigma :=
    xiRightShiftedPole_re_le_of_dyadicSharpSource_summable
      hsigmaHalf hsource
  have hsupBound : xiRightTransverseSup ≤ sigma - 1 :=
    xiRightTransverseSup_le_of_shiftedPole_re_le hne hpoleBound
  linarith

/-- Direct theorem surface, with no bundled proposition interface. -/
theorem riemannHypothesis_of_eventually_dyadicWeightedPrimeWindow_upper
    {N : ℕ}
    (hwindow : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        dyadicWeightedPrimeWindow n ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
            C * (n : ℝ) ^ epsilon) :
    RiemannHypothesis :=
  riemannHypothesis_of_dyadicWeightedPrimeWindowSubpowerUpper hwindow

end RHTower

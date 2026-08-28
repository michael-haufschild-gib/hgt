import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyPrimeWeightedPoleEscape
import GaloisForLFunctions.RHTower.CountableWindowBasis
import GaloisForLFunctions.RHTower.BurnolSoninEvaluationNonvanishing

/-!
# Localized D2 Gaussian-rational pole escape

The existing D2 theorem says false RH drives the pure-prime log-height defect below every floor
somewhere on the unbounded Gaussian-rational high-frequency tail. This module proves a stronger
local law: one off-line zero creates all such violations inside one fixed rational rectangle of
bounded height. The normalized defect residue is minus twice the Xi multiplicity; zero isolation,
continuity, and Gaussian-rational density retain the escape on exact rational samples.

Consequently false RH is equivalent to existence of one admissible rational window containing a
Gaussian-rational sequence along which the D2 defect tends to minus infinity. Equivalently, RH is
finite lower boundedness on each admissible rational window.
-/

open Complex Filter Topology Set Metric

namespace RHTower

noncomputable section

/-- Exact normalized residue of D2's complex pure-prime log-height defect at a positive-height
Xi zero. The logarithmic height correction has zero residue. -/
theorem tendsto_primeArchLogHeightComplexDefect_normalizedResidue
    {rho : ℂ} (hrhoRe : 0 < rho.re) (hrhoReOne : rho.re < 1)
    (hrhoIm : 0 < rho.im) :
    Tendsto
      (fun s : ℂ ↦ (s - rho) * primeArchLogHeightComplexDefect s)
      (nhdsWithin rho ({rho}ᶜ))
      (nhds (-2 * ((analyticOrderAt xi rho).toNat : ℂ))) := by
  have hprime : Tendsto
      (fun s : ℂ ↦ (s - rho) * infinitePrimeFlux s)
      (nhdsWithin rho ({rho}ᶜ))
      (nhds (-((analyticOrderAt xi rho).toNat : ℂ))) := by
    simpa [infinitePrimeFlux] using
      (riemannZeta_normalizedLogDeriv_tendsto_xi_order_of_mem_strip rho
        ⟨hrhoRe, hrhoReOne⟩).neg
  have hlogReal : ContinuousAt (fun s : ℂ ↦ Real.log s.im) rho :=
    (Real.continuousAt_log hrhoIm.ne').comp Complex.continuous_im.continuousAt
  have hlog : ContinuousAt (fun s : ℂ ↦ (Real.log s.im : ℂ)) rho :=
    Complex.continuous_ofReal.continuousAt.comp hlogReal
  have hheight : Tendsto
      (fun s : ℂ ↦ (s - rho) * (Real.log s.im : ℂ))
      (nhdsWithin rho ({rho}ᶜ)) (nhds 0) := by
    have hcont : ContinuousAt
        (fun s : ℂ ↦ (s - rho) * (Real.log s.im : ℂ)) rho :=
      (continuousAt_id.sub continuousAt_const).mul hlog
    exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using hcont.tendsto)
  have hlim := (hprime.const_mul (2 : ℂ)).sub hheight
  convert hlim using 1
  · funext s
    rw [primeArchLogHeightComplexDefect]
    ring_nf
  · ring_nf

/-- D2's complex pure-prime defect is continuous at every positive-height regular zeta point. -/
theorem continuousAt_primeArchLogHeightComplexDefect_of_riemannZeta_ne_zero
    {s : ℂ} (hsIm : 0 < s.im) (hzeta : riemannZeta s ≠ 0) :
    ContinuousAt primeArchLogHeightComplexDefect s := by
  have hsOne : s ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    rw [one_im] at him
    linarith
  have hzetaAn : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hsOne
  have hflux : ContinuousAt infinitePrimeFlux s := by
    rw [show infinitePrimeFlux = fun w : ℂ ↦
        -(deriv riemannZeta w / riemannZeta w) by
      funext w
      rw [infinitePrimeFlux, logDeriv_apply]]
    exact (hzetaAn.deriv.continuousAt.div hzetaAn.continuousAt hzeta).neg
  have hlogReal : ContinuousAt (fun w : ℂ ↦ Real.log w.im) s :=
    (Real.continuousAt_log hsIm.ne').comp Complex.continuous_im.continuousAt
  have hlog : ContinuousAt (fun w : ℂ ↦ (Real.log w.im : ℂ)) s :=
    Complex.continuous_ofReal.continuousAt.comp hlogReal
  change ContinuousAt
    (fun w : ℂ ↦ 2 * infinitePrimeFlux w - (Real.log w.im : ℂ)) s
  exact (continuousAt_const.mul hflux).sub hlog

/-- Every rational rectangle containing a positive-height left-strip Xi zero contains
Gaussian-rational D2 defect samples below every real floor. -/
theorem exists_gaussianRat_primeArchLogHeightDefect_lt_in_ratRectangle_of_xiZero
    {rho : ℂ} (hrhoRe : 0 < rho.re) (hrhoHalf : rho.re < 1 / 2)
    (hrhoIm : 0 < rho.im) (hrhoZero : xi rho = 0)
    {u v x y : ℚ} (hx : 0 < (x : ℝ))
    (hrhoRect : rho ∈ ratRectangle u v x y) (B : ℝ) :
    ∃ q : ℚ × ℚ, gaussianRatPoint q ∈ ratRectangle u v x y ∧
      primeArchLogHeightDefect (gaussianRatPoint q) < B := by
  let m : ℕ := (analyticOrderAt xi rho).toNat
  let C : ℂ := -2 * (m : ℂ)
  let f : ℂ → ℂ := primeArchLogHeightComplexDefect
  have hmPos : 0 < m := Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hrhoZero)
  have hmNe : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmPos)
  have hC : C ≠ 0 := mul_ne_zero (by norm_num) hmNe
  have hres : Tendsto (fun s : ℂ ↦ (s - rho) * f s)
      (nhdsWithin rho ({rho}ᶜ)) (nhds C) := by
    simpa only [f, C, m] using
      tendsto_primeArchLogHeightComplexDefect_normalizedResidue
        hrhoRe (by linarith) hrhoIm
  have hrectNh : ratRectangle u v x y ∈ nhds rho :=
    (isOpen_ratRectangle u v x y).mem_nhds hrhoRect
  obtain ⟨rRect, hrRect, hballRect⟩ := Metric.mem_nhds_iff.mp hrectNh
  have hzeroFree : ∀ᶠ s in 𝓝[≠] rho, riemannZeta s ≠ 0 :=
    eventually_riemannZeta_ne_zero_nhdsNE hrhoRe (by linarith)
  obtain ⟨rZero, hrZero, hballZero⟩ := Metric.mem_nhdsWithin_iff.mp hzeroFree
  have hrMin : 0 < min rRect rZero := lt_min hrRect hrZero
  obtain ⟨s, hsNe, _hfNe, hsDist, hsLt⟩ :=
    exists_realPart_lt_near_of_punctured_residue hC hres
      (min rRect rZero) hrMin B
  have hsRect : s ∈ ratRectangle u v x y :=
    hballRect (by
      rw [mem_ball]
      exact hsDist.trans_le (min_le_left _ _))
  have hsZeta : riemannZeta s ≠ 0 := by
    refine hballZero ⟨?_, ?_⟩
    · rw [mem_ball]
      exact hsDist.trans_le (min_le_right _ _)
    · simpa only [mem_compl_iff, mem_singleton_iff] using hsNe
  have hsIm : 0 < s.im := by
    exact hx.trans hsRect.2.2.1
  have hcont :=
    continuousAt_primeArchLogHeightComplexDefect_of_riemannZeta_ne_zero hsIm hsZeta
  have hcontRe : ContinuousAt (fun w : ℂ ↦ primeArchLogHeightDefect w) s := by
    have hre : ContinuousAt (fun w : ℂ ↦ (primeArchLogHeightComplexDefect w).re) s :=
      Complex.continuous_re.continuousAt.comp hcont
    simpa only [primeArchLogHeightComplexDefect_re] using hre
  have hsLtScalar : primeArchLogHeightDefect s < B := by
    simpa only [f, primeArchLogHeightComplexDefect_re] using hsLt
  have hsublevel : {w : ℂ | primeArchLogHeightDefect w < B} ∈ nhds s :=
    hcontRe.tendsto (Iio_mem_nhds hsLtScalar)
  have hinter : ratRectangle u v x y ∩
      {w : ℂ | primeArchLogHeightDefect w < B} ∈ nhds s :=
    inter_mem ((isOpen_ratRectangle u v x y).mem_nhds hsRect) hsublevel
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hinter
  obtain ⟨q, hqball⟩ := denseRange_gaussianRatPoint.exists_mem_open isOpen_ball
    ⟨s, mem_ball_self hr⟩
  exact ⟨q, (hball hqball).1, (hball hqball).2⟩

/-- Rational rectangles whose closed envelope lies in D2's left critical half-strip above the
formal fourth-trace verified-height threshold. -/
def IsAdmissibleD2RatRectangle (u v x y : ℚ) : Prop :=
  0 < (u : ℝ) ∧ (u : ℝ) < (v : ℝ) ∧ (v : ℝ) < 1 / 2 ∧
    233 / 20 < (x : ℝ) ∧ (x : ℝ) < (y : ℝ)

theorem exists_admissibleD2RatRectangle_containing
    {rho : ℂ} (hrhoRe : 0 < rho.re) (hrhoHalf : rho.re < 1 / 2)
    (hrhoHigh : 233 / 20 < rho.im) :
    ∃ u v x y : ℚ, IsAdmissibleD2RatRectangle u v x y ∧
      rho ∈ ratRectangle u v x y := by
  obtain ⟨u, hu0, hurho⟩ := exists_rat_btwn hrhoRe
  obtain ⟨v, hrhov, hvhalf⟩ := exists_rat_btwn hrhoHalf
  obtain ⟨x, hxhigh, hxrhoa⟩ := exists_rat_btwn hrhoHigh
  obtain ⟨y, hrhoy, _hy⟩ := exists_rat_btwn
    (show rho.im < rho.im + 1 by linarith)
  refine ⟨u, v, x, y, ?_, ?_⟩
  · exact ⟨hu0, hurho.trans hrhov, hvhalf, hxhigh, hxrhoa.trans hrhoy⟩
  · exact ⟨hurho, hrhov, hxrhoa, hrhoy⟩

/-- False RH supplies a positive-height Xi zero in the left critical half-strip beyond D2's
formal verified-height threshold. -/
theorem exists_leftUpperXiZero_above_twoHundredThirtyThree_twentieths_of_not_rh
    (hnot : ¬ RiemannHypothesis) :
    ∃ rho : ℂ, 0 < rho.re ∧ rho.re < 1 / 2 ∧
      233 / 20 < rho.im ∧ xi rho = 0 := by
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_of_not_riemannHypothesis hnot
  have hqImPos : 0 < (q.1.1.1 : ℂ).im := by
    have h := q.2
    rw [xiRightCenteredZero, I_mul_xiSpectralPoint] at h
    simpa using h
  have hqAbsHigh : 243 / 20 < |(q.1.1.1 : ℂ).im| := by
    by_contra hhigh
    have hle : |(q.1.1.1 : ℂ).im| ≤ 243 / 20 := le_of_not_gt hhigh
    exact xiRightUpperZeroCopy_offLine q
      (xiZeroCopy_re_eq_half_of_verifiedThrough_of_abs_im_le
        (243 / 20) rhVerifiedThrough_twoHundredFortyThree_twentieths q.1.1 hle)
  have hqHigh : 233 / 20 < (q.1.1.1 : ℂ).im := by
    rw [abs_of_pos hqImPos] at hqAbsHigh
    linarith
  let alpha : ℂ := (starRingEnd ℂ) (xiSpectralPoint q.1.1)
  let rho : ℂ := 1 / 2 + alpha * I
  have halphaRe : alpha.re = (q.1.1.1 : ℂ).im := by
    dsimp only [alpha]
    rw [Complex.conj_re, xiSpectralPoint_eq_support]
    simp [xiSpectralPointSupport, Complex.mul_re]
  have halphaIm : alpha.im = (q.1.1.1 : ℂ).re - 1 / 2 := by
    dsimp only [alpha]
    rw [Complex.conj_im, xiSpectralPoint_eq_support]
    simp [xiSpectralPointSupport, Complex.mul_im]
  have hrhoRe : rho.re = 1 / 2 - alpha.im := by
    simp [rho, Complex.mul_re]
    ring
  have hrhoIm : rho.im = alpha.re := by
    simp [rho, Complex.mul_im]
  have hqRight : 1 / 2 < (q.1.1.1 : ℂ).re := by
    have h := xiRightCenteredZero_re_pos q.1
    rw [xiRightCenteredZero, I_mul_xiSpectralPoint] at h
    simpa using h
  have hqStrip := xi_divisor_support_re_mem_open_unit q.1.1.1
  have hrhoPos : 0 < rho.re := by rw [hrhoRe, halphaIm]; linarith
  have hrhoHalf : rho.re < 1 / 2 := by rw [hrhoRe, halphaIm]; linarith
  have hrhoHigh : 233 / 20 < rho.im := by rw [hrhoIm, halphaRe]; exact hqHigh
  have halphaXi : XiC alpha = 0 := by
    dsimp only [alpha]
    rw [XiC_conj, XiC_xiSpectralPoint_eq_zero, map_zero]
  refine ⟨rho, hrhoPos, hrhoHalf, hrhoHigh, ?_⟩
  simpa only [XiC, rho] using halphaXi

/-- D2 failure localized to one bounded rational rectangle. -/
def PrimeArchLogHeightDefectGaussianRatLocalizedUnboundedBelow : Prop :=
  ∃ u v x y : ℚ, IsAdmissibleD2RatRectangle u v x y ∧
    ∀ B : ℝ, ∃ q : ℚ × ℚ,
      gaussianRatPoint q ∈ ratRectangle u v x y ∧
      primeArchLogHeightDefect (gaussianRatPoint q) < B

theorem primeArchLogHeightDefectGaussianRatLocalizedUnboundedBelow_of_not_rh
    (hnot : ¬ RiemannHypothesis) :
    PrimeArchLogHeightDefectGaussianRatLocalizedUnboundedBelow := by
  obtain ⟨rho, hrhoRe, hrhoHalf, hrhoHigh, hrhoZero⟩ :=
    exists_leftUpperXiZero_above_twoHundredThirtyThree_twentieths_of_not_rh hnot
  obtain ⟨u, v, x, y, hRect, hrhoRect⟩ :=
    exists_admissibleD2RatRectangle_containing hrhoRe hrhoHalf hrhoHigh
  refine ⟨u, v, x, y, hRect, ?_⟩
  intro B
  exact exists_gaussianRat_primeArchLogHeightDefect_lt_in_ratRectangle_of_xiZero
    hrhoRe hrhoHalf (by linarith) hrhoZero (by linarith [hRect.2.2.2.1]) hrhoRect B

theorem not_rh_of_primeArchLogHeightDefectGaussianRatLocalizedUnboundedBelow
    (hlocal : PrimeArchLogHeightDefectGaussianRatLocalizedUnboundedBelow) :
    ¬RiemannHypothesis := by
  intro hRH
  obtain ⟨L, hL⟩ :=
    (primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh.mpr
      hRH)
  obtain ⟨u, v, x, y, hRect, hbad⟩ := hlocal
  obtain ⟨q, hqRect, hqBad⟩ := hbad L
  have hqRe : 0 < (gaussianRatPoint q).re := hRect.1.trans hqRect.1
  have hqHalf : (gaussianRatPoint q).re < 1 / 2 :=
    hqRect.2.1.trans hRect.2.2.1
  have hqHigh : 233 / 20 < (gaussianRatPoint q).im :=
    hRect.2.2.2.1.trans hqRect.2.2.1
  exact (not_lt_of_ge (hL q hqRe hqHalf hqHigh)) hqBad

theorem primeArchLogHeightDefectGaussianRatLocalizedUnboundedBelow_iff_not_rh :
    PrimeArchLogHeightDefectGaussianRatLocalizedUnboundedBelow ↔
      ¬RiemannHypothesis :=
  ⟨not_rh_of_primeArchLogHeightDefectGaussianRatLocalizedUnboundedBelow,
    primeArchLogHeightDefectGaussianRatLocalizedUnboundedBelow_of_not_rh⟩

/-- Finite lower boundedness on each admissible rational window. -/
def PrimeArchLogHeightDefectGaussianRatAdmissibleWindowsBoundedBelow : Prop :=
  ∀ u v x y : ℚ, IsAdmissibleD2RatRectangle u v x y →
    ∃ L : ℝ, ∀ q : ℚ × ℚ, gaussianRatPoint q ∈ ratRectangle u v x y →
      L ≤ primeArchLogHeightDefect (gaussianRatPoint q)

theorem primeArchLogHeightDefectGaussianRatAdmissibleWindowsBoundedBelow_of_rh
    (hRH : RiemannHypothesis) :
    PrimeArchLogHeightDefectGaussianRatAdmissibleWindowsBoundedBelow := by
  obtain ⟨L, hL⟩ :=
    (primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh.mpr
      hRH)
  intro u v x y hRect
  refine ⟨L, ?_⟩
  intro q hqRect
  exact hL q (hRect.1.trans hqRect.1)
    (hqRect.2.1.trans hRect.2.2.1)
    (hRect.2.2.2.1.trans hqRect.2.2.1)

theorem riemannHypothesis_of_primeArchLogHeightDefectGaussianRatAdmissibleWindowsBoundedBelow
    (hwindows : PrimeArchLogHeightDefectGaussianRatAdmissibleWindowsBoundedBelow) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨u, v, x, y, hRect, hbad⟩ :=
    primeArchLogHeightDefectGaussianRatLocalizedUnboundedBelow_of_not_rh hRH
  obtain ⟨L, hL⟩ := hwindows u v x y hRect
  obtain ⟨q, hqRect, hqBad⟩ := hbad L
  exact (not_lt_of_ge (hL q hqRect)) hqBad

theorem primeArchLogHeightDefectGaussianRatAdmissibleWindowsBoundedBelow_iff_rh :
    PrimeArchLogHeightDefectGaussianRatAdmissibleWindowsBoundedBelow ↔
      RiemannHypothesis :=
  ⟨riemannHypothesis_of_primeArchLogHeightDefectGaussianRatAdmissibleWindowsBoundedBelow,
    primeArchLogHeightDefectGaussianRatAdmissibleWindowsBoundedBelow_of_rh⟩

/-- A single bounded-window Gaussian-rational witness sequence whose D2 defect tends to minus
infinity. -/
def PrimeArchLogHeightDefectGaussianRatLocalizedTendstoAtBot : Prop :=
  ∃ u v x y : ℚ, ∃ q : ℕ → ℚ × ℚ,
    IsAdmissibleD2RatRectangle u v x y ∧
    (∀ n : ℕ, gaussianRatPoint (q n) ∈ ratRectangle u v x y) ∧
    Tendsto (fun n : ℕ ↦ primeArchLogHeightDefect (gaussianRatPoint (q n)))
      atTop atBot

theorem primeArchLogHeightDefectGaussianRatLocalizedTendstoAtBot_of_not_rh
    (hnot : ¬RiemannHypothesis) :
    PrimeArchLogHeightDefectGaussianRatLocalizedTendstoAtBot := by
  obtain ⟨u, v, x, y, hRect, hbad⟩ :=
    primeArchLogHeightDefectGaussianRatLocalizedUnboundedBelow_of_not_rh hnot
  choose q hqRect hqLt using fun n : ℕ ↦ hbad (-((n : ℝ)))
  refine ⟨u, v, x, y, q, hRect, hqRect, ?_⟩
  apply Filter.tendsto_atBot.2
  intro B
  filter_upwards [
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (-B)] with n hn
  exact (hqLt n).le.trans (by linarith)

theorem not_rh_of_primeArchLogHeightDefectGaussianRatLocalizedTendstoAtBot
    (hseq : PrimeArchLogHeightDefectGaussianRatLocalizedTendstoAtBot) :
    ¬RiemannHypothesis := by
  intro hRH
  obtain ⟨L, hL⟩ :=
    (primeArchLogHeightDefectGaussianRatPositiveFrequencyAboveBoundedBelow_twoHundredThirtyThree_twentieths_iff_rh.mpr
      hRH)
  obtain ⟨u, v, x, y, q, hRect, hqRect, hlim⟩ := hseq
  have hev : ∀ᶠ n : ℕ in atTop,
      primeArchLogHeightDefect (gaussianRatPoint (q n)) ≤ L - 1 :=
    (Filter.tendsto_atBot.1 hlim) (L - 1)
  obtain ⟨n, hn⟩ := hev.exists
  have hglobal := hL (q n)
    (hRect.1.trans (hqRect n).1)
    ((hqRect n).2.1.trans hRect.2.2.1)
    (hRect.2.2.2.1.trans (hqRect n).2.2.1)
  linarith

theorem primeArchLogHeightDefectGaussianRatLocalizedTendstoAtBot_iff_not_rh :
    PrimeArchLogHeightDefectGaussianRatLocalizedTendstoAtBot ↔
      ¬RiemannHypothesis :=
  ⟨not_rh_of_primeArchLogHeightDefectGaussianRatLocalizedTendstoAtBot,
    primeArchLogHeightDefectGaussianRatLocalizedTendstoAtBot_of_not_rh⟩

end

end RHTower

import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyPrimeWeightedPoleEscape
import GaloisForLFunctions.RHTower.CountableWindowBasis

/-!
# Countable D2 Gaussian-rational window criterion for the physical direct-prime source

Loop93's local pole-escape criterion quantifies over arbitrary complex neighborhoods. This module
removes that uncountable sampling burden. Every off-line centered Xi zero lies in a rational
rectangle compactly contained in the centered upper strip. At a cofinally selected natural
aperture, direct-prime pole escape produces arbitrarily negative regular samples in that window;
continuity and Gaussian-rational density preserve strict negativity at an exact rational sample.
An exact rational coordinate rotation realizes this centered sample as the D2 contour coordinate
of a Gaussian-rational point in the original `s` plane.

Conversely, RH makes the physical direct-prime source continuous on every closed admissible
rational rectangle, so compactness supplies a finite lower bound. Thus eventual finite lower
boundedness on this entirely countable family of D2 samples is exactly RH.
-/

open Complex Filter Topology Set Metric

namespace RHTower

noncomputable section

/-- Rotate a centered Gaussian-rational contour coordinate back to its original `s`-plane
Gaussian-rational index. -/
def centeredGaussianRatToPrimeFluxIndex (q : ℚ × ℚ) : ℚ × ℚ :=
  (1 / 2 - q.2, q.1)

theorem gaussianRatPoint_centeredGaussianRatToPrimeFluxIndex (q : ℚ × ℚ) :
    gaussianRatPoint (centeredGaussianRatToPrimeFluxIndex q) =
      1 / 2 + gaussianRatPoint q * I := by
  apply Complex.ext
  · simp [centeredGaussianRatToPrimeFluxIndex, gaussianRatPoint, Complex.mul_re]
    ring
  · simp [centeredGaussianRatToPrimeFluxIndex, gaussianRatPoint, Complex.mul_im]

theorem primeFluxContourCoordinate_centeredGaussianRatToPrimeFluxIndex (q : ℚ × ℚ) :
    primeFluxContourCoordinate (gaussianRatPoint (centeredGaussianRatToPrimeFluxIndex q)) =
      gaussianRatPoint q := by
  apply Complex.ext
  · rw [primeFluxContourCoordinate_re]
    simp [centeredGaussianRatToPrimeFluxIndex, gaussianRatPoint]
  · rw [primeFluxContourCoordinate_im]
    simp [centeredGaussianRatToPrimeFluxIndex, gaussianRatPoint]

/-- Closed rational rectangle used as compact envelope of `ratRectangle`. -/
def closedRatRectangle (a b c d : ℚ) : Set ℂ :=
  Set.Icc (a : ℝ) (b : ℝ) ×ℂ Set.Icc (c : ℝ) (d : ℝ)

theorem isCompact_closedRatRectangle (a b c d : ℚ) :
    IsCompact (closedRatRectangle a b c d) := by
  have himg : closedRatRectangle a b c d =
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℝ) * I) ''
        (Set.Icc (a : ℝ) (b : ℝ) ×ˢ Set.Icc (c : ℝ) (d : ℝ)) := by
    ext z
    constructor
    · intro hz
      refine ⟨(z.re, z.im), ⟨hz.1, hz.2⟩, ?_⟩
      apply Complex.ext <;> simp
    · rintro ⟨p, hp, rfl⟩
      exact ⟨by simpa using hp.1, by simpa using hp.2⟩
  rw [himg]
  exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)

theorem ratRectangle_subset_closedRatRectangle (a b c d : ℚ) :
    ratRectangle a b c d ⊆ closedRatRectangle a b c d := by
  rintro z ⟨haz, hzb, hcz, hzd⟩
  exact ⟨⟨haz.le, hzb.le⟩, hcz.le, hzd.le⟩

/-- Rational rectangles whose closed envelope lies in the centered upper half-strip and to the
right of the centered seam. -/
def IsAdmissibleCenteredUpperRatRectangle (a b c d : ℚ) : Prop :=
  0 < (a : ℝ) ∧ (a : ℝ) < (b : ℝ) ∧
    0 < (c : ℝ) ∧ (c : ℝ) < (d : ℝ) ∧ (d : ℝ) < 1 / 2

theorem exists_admissibleCenteredUpperRatRectangle_containing
    {alpha : ℂ} (hare : 0 < alpha.re) (haim : 0 < alpha.im)
    (haimhalf : alpha.im < 1 / 2) :
    ∃ a b c d : ℚ, IsAdmissibleCenteredUpperRatRectangle a b c d ∧
      alpha ∈ ratRectangle a b c d := by
  obtain ⟨a, ha0, haalpha⟩ := exists_rat_btwn hare
  obtain ⟨b, halphab, hb⟩ := exists_rat_btwn (show alpha.re < alpha.re + 1 by linarith)
  obtain ⟨c, hc0, hcalpha⟩ := exists_rat_btwn haim
  obtain ⟨d, halphad, hdhalf⟩ := exists_rat_btwn haimhalf
  refine ⟨a, b, c, d, ?_, ?_⟩
  · exact ⟨ha0, haalpha.trans halphab, hc0, hcalpha.trans halphad, hdhalf⟩
  · exact ⟨haalpha, halphab, hcalpha, halphad⟩

/-- The literal physical direct-prime weighted source is continuous at every regular centered
upper-strip point. -/
theorem continuousAt_xiPhysicalThetaAbelEnergyPrimeWeightedSource_of_XiC_ne_zero
    (L A c a : ℝ) {z : ℂ} (hzim : 0 < z.im) (hzimhalf : z.im < 1 / 2)
    (hXi : XiC z ≠ 0) :
    ContinuousAt (xiPhysicalThetaAbelEnergyPrimeWeightedSource L A c a) z := by
  let s : ℂ := 1 / 2 + z * I
  have hsRe : s.re = 1 / 2 - z.im := by
    simp [s, Complex.mul_re, sub_eq_add_neg]
  have hsPos : 0 < s.re := by rw [hsRe]; linarith
  have hsLt : s.re < 1 := by rw [hsRe]; linarith
  have hsNeOne : s ≠ 1 := by
    intro hsOne
    have hreOne := congrArg Complex.re hsOne
    rw [one_re, hsRe] at hreOne
    linarith
  have hzeta : riemannZeta s ≠ 0 := by
    intro hzetaZero
    apply hXi
    rw [XiC]
    exact (xi_eq_zero_iff hsPos hsNeOne).mpr hzetaZero
  have hzetaAn : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s hsNeOne
  have hflux : ContinuousAt infinitePrimeFlux s := by
    rw [show infinitePrimeFlux = fun w : ℂ ↦
        -(deriv riemannZeta w / riemannZeta w) by
      funext w
      rw [infinitePrimeFlux, logDeriv_apply]]
    exact (hzetaAn.deriv.continuousAt.div hzetaAn.continuousAt hzeta).neg
  have hcoord : ContinuousAt (fun w : ℂ ↦ 1 / 2 + w * I) z := by
    fun_prop
  have hweight : ContinuousAt
      (fun w : ℂ ↦ xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a w ^ 2) z :=
    (xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_analyticOnNhd
      L A c a z (mem_univ z)).continuousAt
  have hfluxCoord : ContinuousAt
      (fun w : ℂ ↦ infinitePrimeFlux (1 / 2 + w * I)) z := by
    exact ContinuousAt.comp (x := z)
      (f := fun w : ℂ ↦ 1 / 2 + w * I) (g := infinitePrimeFlux) hflux hcoord
  change ContinuousAt (fun w : ℂ ↦
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a w ^ 2 *
      (-I * infinitePrimeFlux (1 / 2 + w * I))) z
  exact hweight.mul (continuousAt_const.mul hfluxCoord)

/-- Strict negativity of a regular direct-prime sample persists at an exact Gaussian-rational
centered coordinate inside the same rational window. -/
theorem exists_gaussianRatPoint_mem_ratRectangle_primeWeightedSource_re_lt
    (L A c a : ℝ) {u v x y : ℚ} {z : ℂ} {B : ℝ}
    (hzRect : z ∈ ratRectangle u v x y)
    (hzim : 0 < z.im) (hzimhalf : z.im < 1 / 2) (hXi : XiC z ≠ 0)
    (hzLt : (xiPhysicalThetaAbelEnergyPrimeWeightedSource L A c a z).re < B) :
    ∃ q : ℚ × ℚ, gaussianRatPoint q ∈ ratRectangle u v x y ∧
      (xiPhysicalThetaAbelEnergyPrimeWeightedSource
        L A c a (gaussianRatPoint q)).re < B := by
  have hrectNh : ratRectangle u v x y ∈ nhds z :=
    (isOpen_ratRectangle u v x y).mem_nhds hzRect
  have hsource :=
    continuousAt_xiPhysicalThetaAbelEnergyPrimeWeightedSource_of_XiC_ne_zero
      L A c a hzim hzimhalf hXi
  have hsourceRe : ContinuousAt (fun w : ℂ ↦
      (xiPhysicalThetaAbelEnergyPrimeWeightedSource L A c a w).re) z :=
    Complex.continuous_re.continuousAt.comp hsource
  have hltNh : {w : ℂ |
      (xiPhysicalThetaAbelEnergyPrimeWeightedSource L A c a w).re < B} ∈ nhds z :=
    hsourceRe.tendsto (Iio_mem_nhds hzLt)
  have hinter : ratRectangle u v x y ∩ {w : ℂ |
      (xiPhysicalThetaAbelEnergyPrimeWeightedSource L A c a w).re < B} ∈ nhds z :=
    inter_mem hrectNh hltNh
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hinter
  obtain ⟨q, hqball⟩ := denseRange_gaussianRatPoint.exists_mem_open isOpen_ball
    ⟨z, mem_ball_self hr⟩
  exact ⟨q, (hball hqball).1, (hball hqball).2⟩

/-- Countable D2-window test at every exact natural logarithmic aperture. The sample index lives
in the original `s` plane; `primeFluxContourCoordinate` moves it to the centered physical contour. -/
def XiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsBoundedBelow
    (L A c : ℝ) : Prop :=
  ∀ u v x y : ℚ, IsAdmissibleCenteredUpperRatRectangle u v x y →
    ∀ n : ℕ, ∃ B : ℝ, ∀ q : ℚ × ℚ,
      primeFluxContourCoordinate (gaussianRatPoint q) ∈ ratRectangle u v x y →
        B ≤ (xiPhysicalThetaAbelEnergyPrimeWeightedSource L A c
          (Real.log n / 2) (primeFluxContourCoordinate (gaussianRatPoint q))).re

theorem xiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsBoundedBelow_of_riemannHypothesis
    (L A c : ℝ) (hRH : RiemannHypothesis) :
    XiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsBoundedBelow L A c := by
  intro u v x y hRect n
  let K : Set ℂ := closedRatRectangle u v x y
  let f : ℂ → ℂ := xiPhysicalThetaAbelEnergyPrimeWeightedSource
    L A c (Real.log n / 2)
  have hK : IsCompact K := isCompact_closedRatRectangle u v x y
  have hcont : ContinuousOn f K := by
    intro z hz
    have hzre : 0 < z.re := lt_of_lt_of_le hRect.1 hz.1.1
    have hzim : 0 < z.im := lt_of_lt_of_le hRect.2.2.1 hz.2.1
    have hzimhalf : z.im < 1 / 2 := lt_of_le_of_lt hz.2.2 hRect.2.2.2.2
    have hXi : XiC z ≠ 0 :=
      XiC_ne_zero_upperHalf_of_rh hRH (by
        simpa only [xiCenteredUpperHalfPlane, mem_setOf_eq] using hzim)
    exact (continuousAt_xiPhysicalThetaAbelEnergyPrimeWeightedSource_of_XiC_ne_zero
      L A c (Real.log n / 2) hzim hzimhalf hXi).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.bddAbove_image hcont.norm
  refine ⟨-C, ?_⟩
  intro q hqRect
  let z : ℂ := primeFluxContourCoordinate (gaussianRatPoint q)
  have hzK : z ∈ K :=
    ratRectangle_subset_closedRatRectangle u v x y hqRect
  have hnorm : ‖f z‖ ≤ C := hC ⟨z, hzK, rfl⟩
  have hnegNorm : -‖f z‖ ≤ (f z).re :=
    neg_le_of_abs_le (abs_re_le_norm (f z))
  exact (neg_le_neg hnorm).trans hnegNorm

theorem riemannHypothesis_of_xiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsBoundedBelow
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    (hwindows : XiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsBoundedBelow L A c) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨qZero⟩ := nonempty_xiRightUpperZeroCopy_of_not_riemannHypothesis hRH
  let alpha : ℂ := (starRingEnd ℂ) (xiSpectralPoint qZero.1.1)
  have hare : 0 < alpha.re := by
    simpa only [alpha, Complex.conj_re, xiRightCenteredZero, mul_im, I_re, zero_mul,
      I_im, one_mul, zero_add] using qZero.2
  have haim : 0 < alpha.im := by
    simpa only [alpha, Complex.conj_im, xiRightCenteredZero, mul_re, I_re, zero_mul,
      I_im, one_mul, zero_sub] using qZero.1.2
  have haimhalf : alpha.im < 1 / 2 := by
    have h := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half qZero.1)).2
    simpa only [alpha, Complex.conj_im, xiRightCenteredZero, mul_re, I_re, zero_mul,
      I_im, one_mul, zero_sub] using h
  have haXi : XiC alpha = 0 := by
    dsimp only [alpha]
    rw [XiC_conj, XiC_xiSpectralPoint_eq_zero, map_zero]
  obtain ⟨u, v, x, y, hRect, hAlphaRect⟩ :=
    exists_admissibleCenteredUpperRatRectangle_containing hare haim haimhalf
  obtain ⟨n, _hn, hescape⟩ :=
    exists_logMesh_physicalPrimeWeightedSource_cofinally_unboundedBelow_near_of_xiZero
      hL hA hc hare haim haimhalf haXi 0
  obtain ⟨B, hB⟩ := hwindows u v x y hRect n
  have hrectNh : ratRectangle u v x y ∈ nhds alpha :=
    (isOpen_ratRectangle u v x y).mem_nhds hAlphaRect
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hrectNh
  obtain ⟨z, _hzRe, hzIm, hzImHalf, hzXi, hzDist, hzLt⟩ :=
    hescape r hr B
  have hzRect : z ∈ ratRectangle u v x y :=
    hball (by simpa only [mem_ball] using hzDist)
  obtain ⟨q, hqRect, hqLt⟩ :=
    exists_gaussianRatPoint_mem_ratRectangle_primeWeightedSource_re_lt
      L A c (Real.log n / 2) hzRect hzIm hzImHalf hzXi hzLt
  let p : ℚ × ℚ := centeredGaussianRatToPrimeFluxIndex q
  have hpCoord : primeFluxContourCoordinate (gaussianRatPoint p) = gaussianRatPoint q := by
    simpa only [p] using primeFluxContourCoordinate_centeredGaussianRatToPrimeFluxIndex q
  have hpBound := hB p (by rw [hpCoord]; exact hqRect)
  rw [hpCoord] at hpBound
  exact (not_lt_of_ge hpBound) hqLt

theorem xiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsBoundedBelow_iff_riemannHypothesis
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    XiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsBoundedBelow L A c ↔
      RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsBoundedBelow
      hL hA hc,
    xiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsBoundedBelow_of_riemannHypothesis
      L A c⟩

/-- Eventual-in-aperture version of the countable D2 rational-window lower-bound criterion. -/
def XiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow
    (L A c : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ u v x y : ℚ,
    IsAdmissibleCenteredUpperRatRectangle u v x y →
      ∃ B : ℝ, ∀ q : ℚ × ℚ,
        primeFluxContourCoordinate (gaussianRatPoint q) ∈ ratRectangle u v x y →
          B ≤ (xiPhysicalThetaAbelEnergyPrimeWeightedSource L A c
            (Real.log n / 2) (primeFluxContourCoordinate (gaussianRatPoint q))).re

theorem xiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow_of_riemannHypothesis
    (L A c : ℝ) (hRH : RiemannHypothesis) :
    XiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow L A c := by
  refine ⟨0, ?_⟩
  intro n _hn u v x y hRect
  exact xiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsBoundedBelow_of_riemannHypothesis
    L A c hRH u v x y hRect n

theorem riemannHypothesis_of_xiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    (hwindows :
      XiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow L A c) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨qZero⟩ := nonempty_xiRightUpperZeroCopy_of_not_riemannHypothesis hRH
  let alpha : ℂ := (starRingEnd ℂ) (xiSpectralPoint qZero.1.1)
  have hare : 0 < alpha.re := by
    simpa only [alpha, Complex.conj_re, xiRightCenteredZero, mul_im, I_re, zero_mul,
      I_im, one_mul, zero_add] using qZero.2
  have haim : 0 < alpha.im := by
    simpa only [alpha, Complex.conj_im, xiRightCenteredZero, mul_re, I_re, zero_mul,
      I_im, one_mul, zero_sub] using qZero.1.2
  have haimhalf : alpha.im < 1 / 2 := by
    have h := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half qZero.1)).2
    simpa only [alpha, Complex.conj_im, xiRightCenteredZero, mul_re, I_re, zero_mul,
      I_im, one_mul, zero_sub] using h
  have haXi : XiC alpha = 0 := by
    dsimp only [alpha]
    rw [XiC_conj, XiC_xiSpectralPoint_eq_zero, map_zero]
  obtain ⟨N, hN⟩ := hwindows
  obtain ⟨n, hn, hescape⟩ :=
    exists_logMesh_physicalPrimeWeightedSource_cofinally_unboundedBelow_near_of_xiZero
      hL hA hc hare haim haimhalf haXi N
  obtain ⟨u, v, x, y, hRect, hAlphaRect⟩ :=
    exists_admissibleCenteredUpperRatRectangle_containing hare haim haimhalf
  obtain ⟨B, hB⟩ := hN n hn u v x y hRect
  have hrectNh : ratRectangle u v x y ∈ nhds alpha :=
    (isOpen_ratRectangle u v x y).mem_nhds hAlphaRect
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hrectNh
  obtain ⟨z, _hzRe, hzIm, hzImHalf, hzXi, hzDist, hzLt⟩ :=
    hescape r hr B
  have hzRect : z ∈ ratRectangle u v x y :=
    hball (by simpa only [mem_ball] using hzDist)
  obtain ⟨q, hqRect, hqLt⟩ :=
    exists_gaussianRatPoint_mem_ratRectangle_primeWeightedSource_re_lt
      L A c (Real.log n / 2) hzRect hzIm hzImHalf hzXi hzLt
  let p : ℚ × ℚ := centeredGaussianRatToPrimeFluxIndex q
  have hpCoord : primeFluxContourCoordinate (gaussianRatPoint p) = gaussianRatPoint q := by
    simpa only [p] using primeFluxContourCoordinate_centeredGaussianRatToPrimeFluxIndex q
  have hpBound := hB p (by rw [hpCoord]; exact hqRect)
  rw [hpCoord] at hpBound
  exact (not_lt_of_ge hpBound) hqLt

theorem xiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow_iff_riemannHypothesis
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    XiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow L A c ↔
      RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow
      hL hA hc,
    xiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow_of_riemannHypothesis
      L A c⟩

theorem unitPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow_iff_riemannHypothesis :
    XiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow 1 1 1 ↔
      RiemannHypothesis :=
  xiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow_iff_riemannHypothesis
    (by norm_num) (by norm_num) (by norm_num)

end

end RHTower

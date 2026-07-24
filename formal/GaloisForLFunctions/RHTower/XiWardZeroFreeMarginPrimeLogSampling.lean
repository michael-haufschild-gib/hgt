import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardEulerEdgeCompleteness
import GaloisForLFunctions.RHTower.CCMShiftedXiCancellation
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegion
import GaloisForLFunctions.RHTower.ZetaLowHeightZeroFree
import GaloisForLFunctions.RHTower.ShrinkingWindowPrimeSupply

/-!
# Zero-free margin and prime-log sampled completeness of the four-unit Ward law

The de la Vallée Poussin region and the low-height margin force every strict-right
centered Xi zero `λ` to satisfy `Re λ ≤ 1/2 − m(Im λ)` with the explicit margin
`m(y) = c/log⁹(|y|+9)`.  Consequently the continued Ward response exceeds the
four-unit budget not only at the exact adapted height of an off-line pair but on a
detection window of squared half-width `m/2` around it.

Three completeness laws follow.  First, the Euler-edge scalar law keeps its RH
completeness after the four-unit budget is relaxed pointwise to `4 + 8·m(t)`.
Second, the scalar law sampled on any set meeting every detection window is
RH-complete.  Third, the shrinking-window prime supply shows that the signed prime
logarithms, together with one finite uniform grid below a cutoff, meet every
detection window, because the prime-log gaps decay stretched-exponentially while
the detection radius decays only polylogarithmically; the four-unit law sampled on
this locally finite arithmetic set is therefore exactly RH.
-/

open Complex Filter Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The zero-free margin -/

/-- The low-height zero-free radius, selected once. -/
def zetaLowHeightZeroFreeDelta : ℝ :=
  Classical.choose exists_low_height_zeta_zero_free

theorem zetaLowHeightZeroFreeDelta_spec :
    0 < zetaLowHeightZeroFreeDelta ∧ zetaLowHeightZeroFreeDelta ≤ 1 / 8 ∧
      ∀ s : ℂ, 1 - zetaLowHeightZeroFreeDelta ≤ s.re → |s.im| ≤ 9 → s ≠ 1 →
        riemannZeta s ≠ 0 :=
  Classical.choose_spec exists_low_height_zeta_zero_free

theorem zetaLowHeightZeroFreeDelta_pos : 0 < zetaLowHeightZeroFreeDelta :=
  zetaLowHeightZeroFreeDelta_spec.1

/-- The Ward-lane zero-free margin constant. -/
def xiWardZeroFreeMarginC : ℝ :=
  min zetaZeroFreeC zetaLowHeightZeroFreeDelta

theorem xiWardZeroFreeMarginC_pos : 0 < xiWardZeroFreeMarginC :=
  lt_min zetaZeroFreeC_pos zetaLowHeightZeroFreeDelta_pos

theorem xiWardZeroFreeMarginC_le_half : xiWardZeroFreeMarginC ≤ 1 / 2 :=
  le_trans (min_le_left _ _) zetaZeroFreeC_le_half

/-- The Ward detection margin at edge height `y`. -/
def xiWardZeroFreeMargin (y : ℝ) : ℝ :=
  xiWardZeroFreeMarginC / Real.log (|y| + 9) ^ (9 : ℕ)

theorem two_lt_log_of_nine_le {x : ℝ} (hx : 9 ≤ x) : 2 < Real.log x := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h3 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 := by
    nlinarith [Real.exp_pos 1]
  have hexp2 : Real.exp 2 < 9 := by rw [h2]; nlinarith
  calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
    _ < Real.log 9 := Real.log_lt_log (Real.exp_pos 2) hexp2
    _ ≤ Real.log x := Real.log_le_log (by norm_num) hx

theorem one_lt_log_abs_add_nine (y : ℝ) : 1 < Real.log (|y| + 9) := by
  have h := two_lt_log_of_nine_le (x := |y| + 9) (by linarith [abs_nonneg y])
  linarith

theorem xiWardZeroFreeMargin_pos (y : ℝ) : 0 < xiWardZeroFreeMargin y :=
  div_pos xiWardZeroFreeMarginC_pos
    (pow_pos (by linarith [one_lt_log_abs_add_nine y]) 9)

theorem xiWardZeroFreeMargin_le_marginC (y : ℝ) :
    xiWardZeroFreeMargin y ≤ xiWardZeroFreeMarginC := by
  apply div_le_self xiWardZeroFreeMarginC_pos.le
  calc (1 : ℝ) = 1 ^ (9 : ℕ) := by norm_num
    _ ≤ Real.log (|y| + 9) ^ (9 : ℕ) :=
        pow_le_pow_left₀ (by norm_num)
          (by linarith [one_lt_log_abs_add_nine y]) 9

theorem xiWardZeroFreeMargin_le_half (y : ℝ) : xiWardZeroFreeMargin y ≤ 1 / 2 :=
  le_trans (xiWardZeroFreeMargin_le_marginC y) xiWardZeroFreeMarginC_le_half

theorem xiWardZeroFreeMargin_neg (y : ℝ) :
    xiWardZeroFreeMargin (-y) = xiWardZeroFreeMargin y := by
  unfold xiWardZeroFreeMargin
  rw [abs_neg]

theorem xiWardZeroFreeMargin_anti {y z : ℝ} (h : |y| ≤ |z|) :
    xiWardZeroFreeMargin z ≤ xiWardZeroFreeMargin y := by
  have h1 : (0 : ℝ) ≤ Real.log (|y| + 9) := by
    linarith [one_lt_log_abs_add_nine y]
  have h2 : Real.log (|y| + 9) ≤ Real.log (|z| + 9) :=
    Real.log_le_log (by linarith [abs_nonneg y]) (by linarith)
  exact div_le_div₀ xiWardZeroFreeMarginC_pos.le le_rfl
    (pow_pos (by linarith [one_lt_log_abs_add_nine y]) 9)
    (pow_le_pow_left₀ h1 h2 9)

/-- **Zero-free margin transported to the centered Xi divisor**: every strict-right
centered Xi zero lies at least `xiWardZeroFreeMargin (Im λ)` left of `Re = 1/2`. -/
theorem xiRightCenteredZero_re_le_half_sub_margin (q : XiRightZeroCopy) :
    (xiRightCenteredZero q).re ≤
      1 / 2 - xiWardZeroFreeMargin (xiRightCenteredZero q).im := by
  have hsub : xiRightCenteredZero q = ((q.1.1 : ℂ)) - 1 / 2 :=
    xiRightCenteredZero_eq_support_sub_half q
  set rho : ℂ := (q.1.1 : ℂ)
  have hre : rho.re = (xiRightCenteredZero q).re + 1 / 2 := by
    rw [hsub]
    simp
  have him : rho.im = (xiRightCenteredZero q).im := by
    rw [hsub]
    simp
  have ha0 : 0 < (xiRightCenteredZero q).re := xiRightCenteredZero_re_pos q
  have hahalf : (xiRightCenteredZero q).re < 1 / 2 :=
    (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2
  have hrho1 : rho ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have hrhopos : 0 < rho.re := by rw [hre]; linarith
  have hxi : xi rho = 0 := xi_eq_zero_of_mem_divisor_support q.1.1
  have hzeta : riemannZeta rho = 0 := (xi_eq_zero_iff hrhopos hrho1).mp hxi
  by_cases hb : 9 ≤ |(xiRightCenteredZero q).im|
  · -- de la Vallée Poussin region
    have him9 : 9 ≤ |rho.im| := by rw [him]; exact hb
    have hle : rho.re ≤ 1 - zetaZeroFreeC / Real.log |rho.im| ^ (9 : ℕ) := by
      by_contra hcon
      push Not at hcon
      have hzn := riemannZeta_ne_zero_of_re_gt_one_sub
        (β := rho.re) (t := rho.im) him9 hcon
      rw [Complex.re_add_im rho] at hzn
      exact hzn hzeta
    have hlogpos : 0 < Real.log |rho.im| := by
      have := two_lt_log_of_nine_le him9
      linarith
    have hlogle : Real.log |rho.im| ≤
        Real.log (|(xiRightCenteredZero q).im| + 9) := by
      rw [him]
      exact Real.log_le_log (by linarith)
        (by linarith [abs_nonneg (xiRightCenteredZero q).im])
    have hmarg : xiWardZeroFreeMargin (xiRightCenteredZero q).im ≤
        zetaZeroFreeC / Real.log |rho.im| ^ (9 : ℕ) :=
      div_le_div₀ zetaZeroFreeC_pos.le (min_le_left _ _)
        (pow_pos hlogpos 9) (pow_le_pow_left₀ hlogpos.le hlogle 9)
    linarith
  · -- low-height margin
    push Not at hb
    obtain ⟨_, _, hδfree⟩ := zetaLowHeightZeroFreeDelta_spec
    have him9 : |rho.im| ≤ 9 := by rw [him]; linarith
    have hlt : rho.re < 1 - zetaLowHeightZeroFreeDelta := by
      by_contra hcon
      push Not at hcon
      exact hδfree rho hcon him9 hrho1 hzeta
    have hmarg : xiWardZeroFreeMargin (xiRightCenteredZero q).im ≤
        zetaLowHeightZeroFreeDelta :=
      le_trans (xiWardZeroFreeMargin_le_marginC _) (min_le_right _ _)
    linarith

/-! ## The detection window -/

/-- **Detection window**: within the geometric window
`(t + Im λ)² < (Re λ + 1/2)(1/2 − Re λ)` around the reflected height of a
strict-right pair, the selected pair response alone exceeds two. -/
theorem re_xiAntiCausalWardSchwarzPairResponse_window_gt_two
    (q : XiRightUpperZeroCopy) {t : ℝ}
    (hwin : (t + (xiRightCenteredZero q.1).im) ^ 2 <
      ((xiRightCenteredZero q.1).re + 1 / 2) *
        (1 / 2 - (xiRightCenteredZero q.1).re)) :
    2 < (xiAntiCausalWardSchwarzPairResponse q
      ((1 / 2 : ℂ) + I * (t : ℂ))).re := by
  set lam := xiRightCenteredZero q.1
  set w : ℂ := (1 / 2 : ℂ) + I * (t : ℂ) with hwdef
  have ha : 0 < lam.re := xiRightCenteredZero_re_pos q.1
  have hconj :
      xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1) =
        (starRingEnd ℂ) lam :=
    xiRightCenteredZero_conj q.1
  have hwre : w.re = 1 / 2 := by
    rw [hwdef]
    norm_num [Complex.add_re, Complex.mul_re]
  have hwim : w.im = t := by
    rw [hwdef]
    norm_num [Complex.add_im, Complex.mul_im]
  have hzre : (w + lam).re = lam.re + 1 / 2 := by
    rw [Complex.add_re, hwre]
    ring
  have hzim : (w + lam).im = t + lam.im := by
    rw [Complex.add_im, hwim]
  have hznormSq : Complex.normSq (w + lam) =
      (lam.re + 1 / 2) ^ 2 + (t + lam.im) ^ 2 := by
    rw [Complex.normSq_apply, hzre, hzim]
    ring
  have hfirst : 1 < ((w + lam)⁻¹).re := by
    rw [Complex.inv_re, hzre, hznormSq]
    rw [lt_div_iff₀ (by nlinarith [sq_nonneg (t + lam.im)])]
    nlinarith [hwin]
  have hother : 0 < (w + (starRingEnd ℂ) lam).re := by
    rw [Complex.add_re, hwre, Complex.conj_re]
    linarith
  have hiother : 0 < ((w + (starRingEnd ℂ) lam)⁻¹).re :=
    re_inv_pos_of_re_pos hother
  rw [xiAntiCausalWardSchwarzPairResponse, hconj]
  rw [show (2 : ℂ) * ((w + lam)⁻¹ + (w + (starRingEnd ℂ) lam)⁻¹) =
    2 * (w + lam)⁻¹ + 2 * (w + (starRingEnd ℂ) lam)⁻¹ by ring]
  rw [Complex.add_re]
  have h2a : (2 * (w + lam)⁻¹).re = 2 * ((w + lam)⁻¹).re := by
    norm_num [Complex.mul_re]
  have h2b : (2 * (w + (starRingEnd ℂ) lam)⁻¹).re =
      2 * ((w + (starRingEnd ℂ) lam)⁻¹).re := by
    norm_num [Complex.mul_re]
  rw [h2a, h2b]
  nlinarith [hfirst, hiother]

/-- Inside the geometric detection window the complete continued Ward response
breaks the scalar four-unit budget. -/
theorem normSq_continuedXiAntiCausalWardResponse_window_gt_four
    (q : XiRightUpperZeroCopy) {t : ℝ}
    (hwin : (t + (xiRightCenteredZero q.1).im) ^ 2 <
      ((xiRightCenteredZero q.1).re + 1 / 2) *
        (1 / 2 - (xiRightCenteredZero q.1).re)) :
    4 < Complex.normSq
      (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))) := by
  have hw : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  have hpair := re_xiAntiCausalWardSchwarzPairResponse_window_gt_two q hwin
  have hfull := re_xiAntiCausalWardSchwarzPairResponse_le_continued q hw
  have hre : 2 <
      (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))).re :=
    lt_of_lt_of_le hpair hfull
  have hsq := Complex.re_sq_le_normSq
    (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ)))
  nlinarith

/-- **Margin window**: any edge sample within squared distance `m/2` of the
reflected height of a strict-right pair already witnesses the four-unit failure;
the zero-free margin quantifies the aperture of the required sampling. -/
theorem normSq_continuedXiAntiCausalWardResponse_marginWindow_gt_four
    (q : XiRightUpperZeroCopy) {t : ℝ}
    (ht : (t + (xiRightCenteredZero q.1).im) ^ 2 ≤
      xiWardZeroFreeMargin (xiRightCenteredZero q.1).im / 2) :
    4 < Complex.normSq
      (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))) := by
  apply normSq_continuedXiAntiCausalWardResponse_window_gt_four q
  have hM := xiRightCenteredZero_re_le_half_sub_margin q.1
  have ha : 0 < (xiRightCenteredZero q.1).re := xiRightCenteredZero_re_pos q.1
  have hm := xiWardZeroFreeMargin_pos (xiRightCenteredZero q.1).im
  nlinarith [ht, hM, ha, hm, mul_pos hm ha]

/-! ## Herglotz positivity of the continued response -/

/-- The continued Ward response has nonnegative real part on the open right
half-plane: it is a Herglotz sum of strict-right Schwarz pair kernels. -/
theorem re_continuedXiAntiCausalWardResponse_nonneg {w : ℂ} (hw : 0 < w.re) :
    0 ≤ (continuedXiAntiCausalWardResponse w).re := by
  have hsum := summable_xiAntiCausalWardSchwarzPairResponse hw
  rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw,
    Complex.re_tsum hsum]
  exact tsum_nonneg fun q =>
    (re_xiAntiCausalWardSchwarzPairResponse_pos q hw).le

/-! ## Relaxed-budget completeness -/

/-- Euler-edge scalar law with the four-unit budget relaxed by the zero-free
margin. -/
def ContinuedXiWardRelaxedEulerEdgeScalarLaw : Prop :=
  ∀ t : ℝ,
    Complex.normSq
        (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))) ≤
      4 + 8 * xiWardZeroFreeMargin t

/-- At the adapted node of a strict-right pair the continued response exceeds even
the margin-relaxed budget. -/
theorem normSq_continuedXiAntiCausalWardResponse_at_eulerEdge_gt_relaxed
    (q : XiRightUpperZeroCopy) :
    4 + 8 * xiWardZeroFreeMargin (-(xiRightCenteredZero q.1).im) <
      Complex.normSq
        (continuedXiAntiCausalWardResponse
          ((1 / 2 : ℂ) + I * ((-(xiRightCenteredZero q.1).im : ℝ) : ℂ))) := by
  set lam := xiRightCenteredZero q.1
  set w : ℂ := (1 / 2 : ℂ) + I * ((-lam.im : ℝ) : ℂ) with hwdef
  set m : ℝ := xiWardZeroFreeMargin lam.im with hmdef
  have ha : 0 < lam.re := xiRightCenteredZero_re_pos q.1
  have hm0 : 0 < m := xiWardZeroFreeMargin_pos lam.im
  have hmhalf : m ≤ 1 / 2 := xiWardZeroFreeMargin_le_half lam.im
  have hM : lam.re ≤ 1 / 2 - m := xiRightCenteredZero_re_le_half_sub_margin q.1
  have hwre : w.re = 1 / 2 := by
    rw [hwdef]
    norm_num [Complex.add_re, Complex.mul_re]
  have hwim : w.im = -lam.im := by
    rw [hwdef]
    norm_num [Complex.add_im, Complex.mul_im]
  have hw0 : 0 < w.re := by rw [hwre]; norm_num
  have hconj :
      xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1) =
        (starRingEnd ℂ) lam :=
    xiRightCenteredZero_conj q.1
  have hwlam : w + lam = ((lam.re + 1 / 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.add_re, hwre, Complex.ofReal_re]
      ring
    · rw [Complex.add_im, hwim, Complex.ofReal_im]
      ring
  have hdenpos : 0 < lam.re + 1 / 2 := by linarith
  have hfirstEq : (2 * (((lam.re + 1 / 2 : ℝ) : ℂ))⁻¹).re =
      2 / (lam.re + 1 / 2) := by
    rw [← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    simp only [Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hother : 0 < (w + (starRingEnd ℂ) lam).re := by
    rw [Complex.add_re, hwre, Complex.conj_re]
    linarith
  have hiother : 0 < ((w + (starRingEnd ℂ) lam)⁻¹).re :=
    re_inv_pos_of_re_pos hother
  have hpair : 2 / (lam.re + 1 / 2) <
      (xiAntiCausalWardSchwarzPairResponse q w).re := by
    rw [xiAntiCausalWardSchwarzPairResponse, hconj, hwlam]
    rw [show (2 : ℂ) * ((((lam.re + 1 / 2 : ℝ) : ℂ))⁻¹ +
        (w + (starRingEnd ℂ) lam)⁻¹) =
      2 * (((lam.re + 1 / 2 : ℝ) : ℂ))⁻¹ +
        2 * (w + (starRingEnd ℂ) lam)⁻¹ by ring]
    rw [Complex.add_re, hfirstEq]
    have h2b : (2 * (w + (starRingEnd ℂ) lam)⁻¹).re =
        2 * ((w + (starRingEnd ℂ) lam)⁻¹).re := by
      norm_num [Complex.mul_re]
    rw [h2b]
    linarith
  have hfull := re_xiAntiCausalWardSchwarzPairResponse_le_continued q hw0
  have hre : 2 / (lam.re + 1 / 2) <
      (continuedXiAntiCausalWardResponse w).re :=
    lt_of_lt_of_le hpair hfull
  have hDpos : 0 < 1 - m := by linarith
  have hlow : 2 / (1 - m) ≤ 2 / (lam.re + 1 / 2) := by
    apply div_le_div₀ (by norm_num) le_rfl hdenpos
    linarith
  have hrelow : 2 / (1 - m) < (continuedXiAntiCausalWardResponse w).re :=
    lt_of_le_of_lt hlow hre
  have h2D : 0 < 2 / (1 - m) := div_pos (by norm_num) hDpos
  have hsq := Complex.re_sq_le_normSq (continuedXiAntiCausalWardResponse w)
  have hsqlt : (2 / (1 - m)) ^ 2 <
      (continuedXiAntiCausalWardResponse w).re ^ 2 :=
    pow_lt_pow_left₀ hrelow h2D.le (by norm_num)
  have hbudget : 4 + 8 * m ≤ (2 / (1 - m)) ^ 2 := by
    rw [div_pow, le_div_iff₀ (pow_pos hDpos 2)]
    nlinarith [mul_nonneg (sq_nonneg m) (by linarith : (0 : ℝ) ≤ 3 - 2 * m)]
  have hmneg : xiWardZeroFreeMargin (-lam.im) = m := by
    rw [xiWardZeroFreeMargin_neg, hmdef]
  rw [hmneg]
  linarith [hsq, hsqlt, hbudget]

theorem continuedXiWardRelaxedEulerEdgeScalarLaw_of_riemannHypothesis
    (hRH : RiemannHypothesis) : ContinuedXiWardRelaxedEulerEdgeScalarLaw := by
  intro t
  have hw : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  rw [continuedXiAntiCausalWardResponse_eq_zero_of_riemannHypothesis hRH hw,
    Complex.normSq_zero]
  have := xiWardZeroFreeMargin_pos t
  linarith

theorem riemannHypothesis_of_continuedXiWardRelaxedEulerEdgeScalarLaw
    (hlaw : ContinuedXiWardRelaxedEulerEdgeScalarLaw) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
  have h1 := hlaw (-(xiRightCenteredZero q.1).im)
  have h2 := normSq_continuedXiAntiCausalWardResponse_at_eulerEdge_gt_relaxed q
  linarith

/-- **Relaxed-budget completeness law.**  The four-unit Euler-edge budget has
unconditional slack: enlarging it pointwise by `8·xiWardZeroFreeMargin t` yields a
law that is still exactly RH.  Any mechanism achieving the four-unit bound only up
to the zero-free margin therefore already proves RH. -/
theorem riemannHypothesis_iff_continuedXiWardRelaxedEulerEdgeScalarLaw :
    RiemannHypothesis ↔ ContinuedXiWardRelaxedEulerEdgeScalarLaw :=
  ⟨continuedXiWardRelaxedEulerEdgeScalarLaw_of_riemannHypothesis,
    riemannHypothesis_of_continuedXiWardRelaxedEulerEdgeScalarLaw⟩

/-! ## Sampled completeness -/

/-- A set of edge heights meeting the Ward detection window of every height. -/
def XiWardDetectionCover (S : Set ℝ) : Prop :=
  ∀ y : ℝ, ∃ t ∈ S, (t + y) ^ 2 ≤ xiWardZeroFreeMargin y / 2

/-- The four-unit Euler-edge scalar law sampled on `S`. -/
def ContinuedXiWardSampledScalarLaw (S : Set ℝ) : Prop :=
  ∀ t ∈ S,
    Complex.normSq
      (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))) ≤ 4

theorem continuedXiWardSampledScalarLaw_of_riemannHypothesis
    (hRH : RiemannHypothesis) (S : Set ℝ) :
    ContinuedXiWardSampledScalarLaw S := by
  intro t _
  have hw : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  rw [continuedXiAntiCausalWardResponse_eq_zero_of_riemannHypothesis hRH hw,
    Complex.normSq_zero]
  norm_num

theorem riemannHypothesis_of_continuedXiWardSampledScalarLaw
    {S : Set ℝ} (hcov : XiWardDetectionCover S)
    (hlaw : ContinuedXiWardSampledScalarLaw S) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
  obtain ⟨t, htS, htwin⟩ := hcov (xiRightCenteredZero q.1).im
  have hgt :=
    normSq_continuedXiAntiCausalWardResponse_marginWindow_gt_four q htwin
  have hle := hlaw t htS
  linarith

/-- **Sampled completeness law.**  On every set of edge heights meeting all
detection windows, the sampled four-unit scalar law is exactly RH. -/
theorem riemannHypothesis_iff_continuedXiWardSampledScalarLaw
    {S : Set ℝ} (hcov : XiWardDetectionCover S) :
    RiemannHypothesis ↔ ContinuedXiWardSampledScalarLaw S :=
  ⟨fun hRH => continuedXiWardSampledScalarLaw_of_riemannHypothesis hRH S,
    riemannHypothesis_of_continuedXiWardSampledScalarLaw hcov⟩

/-! ## The prime-log sample family -/

/-- Grid spacing at cutoff `Y`. -/
def xiWardSampleGridStep (Y : ℝ) : ℝ :=
  Real.sqrt (xiWardZeroFreeMargin Y / 2)

theorem xiWardSampleGridStep_pos (Y : ℝ) : 0 < xiWardSampleGridStep Y :=
  Real.sqrt_pos.mpr (by linarith [xiWardZeroFreeMargin_pos Y])

theorem sq_xiWardSampleGridStep (Y : ℝ) :
    xiWardSampleGridStep Y ^ 2 = xiWardZeroFreeMargin Y / 2 :=
  Real.sq_sqrt (by linarith [xiWardZeroFreeMargin_pos Y])

theorem xiWardSampleGridStep_le_half (Y : ℝ) :
    xiWardSampleGridStep Y ≤ 1 / 2 := by
  have h1 : xiWardZeroFreeMargin Y / 2 ≤ 1 / 4 := by
    linarith [xiWardZeroFreeMargin_le_half Y]
  calc xiWardSampleGridStep Y ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt h1
    _ = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- The discrete prime-log sample family: signed prime logarithms together with
one finite uniform grid below the cutoff `Y`. -/
def xiWardPrimeLogSampleSet (Y : ℝ) : Set ℝ :=
  {t : ℝ | ∃ p : ℕ, p.Prime ∧ |t| = Real.log p} ∪
    {t : ℝ | (∃ k : ℤ, t = (k : ℝ) * xiWardSampleGridStep Y) ∧ |t| ≤ Y + 1}

/-- Past an explicit cutoff, the prime-log sample family meets every Ward
detection window: the grid covers heights below the cutoff, and the shrinking
multiplicative prime windows cover all larger heights, because the prime-log gaps
decay stretched-exponentially while the detection radius decays only
polylogarithmically. -/
theorem exists_cutoff_xiWardDetectionCover_primeLogSampleSet :
    ∃ y₁ : ℝ, 3 ≤ y₁ ∧ ∀ Y : ℝ, y₁ ≤ Y →
      XiWardDetectionCover (xiWardPrimeLogSampleSet Y) := by
  obtain ⟨c₂, K, y₀, hc₂, hK, _hy₀3, hsupply⟩ :=
    exists_prime_log_in_shrinking_window
  -- eventual domination of the prime-gap scale by the detection radius
  have htend : Tendsto
      (fun y : ℝ => 4 * K ^ 2 * 100 ^ (9 : ℕ) *
        (y ^ ((1 : ℝ) / 10) * Real.exp (-(2 * c₂ * y ^ ((1 : ℝ) / 10)))))
      atTop (nhds 0) := by
    have houter : Tendsto
        (fun u : ℝ => u * Real.exp (-(2 * c₂ * u))) atTop (nhds 0) := by
      have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
      have hmul : Tendsto (fun u : ℝ => 2 * c₂ * u) atTop atTop :=
        Filter.Tendsto.const_mul_atTop (by linarith) tendsto_id
      have hcomp := hbase.comp hmul
      have hcomp' : Tendsto
          (fun u : ℝ => (2 * c₂ * u) * Real.exp (-(2 * c₂ * u)))
          atTop (nhds 0) := by
        simpa [Function.comp, pow_one] using hcomp
      have hscaled := hcomp'.const_mul (1 / (2 * c₂))
      rw [mul_zero] at hscaled
      apply hscaled.congr
      intro u
      field_simp
    have hinner : Tendsto (fun y : ℝ => y ^ ((1 : ℝ) / 10)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    have hcomp := houter.comp hinner
    have hcomp' : Tendsto
        (fun y : ℝ => y ^ ((1 : ℝ) / 10) *
          Real.exp (-(2 * c₂ * y ^ ((1 : ℝ) / 10)))) atTop (nhds 0) := by
      simpa [Function.comp] using hcomp
    have hfinal := hcomp'.const_mul (4 * K ^ 2 * 100 ^ (9 : ℕ))
    rw [mul_zero] at hfinal
    exact hfinal
  have hevsmall : ∀ᶠ y : ℝ in atTop,
      4 * K ^ 2 * 100 ^ (9 : ℕ) *
        (y ^ ((1 : ℝ) / 10) * Real.exp (-(2 * c₂ * y ^ ((1 : ℝ) / 10)))) ≤
        xiWardZeroFreeMarginC :=
    Filter.Tendsto.eventually_le_const xiWardZeroFreeMarginC_pos htend
  obtain ⟨y₂, hy₂⟩ := Filter.eventually_atTop.mp hevsmall
  refine ⟨max (max y₀ 3) (max y₂ 1),
    le_trans (le_max_right y₀ 3) (le_max_left _ _), ?_⟩
  intro Y hY y
  have hY3 : 3 ≤ Y :=
    le_trans (le_trans (le_max_right y₀ 3) (le_max_left _ _)) hY
  have hY0 : 0 ≤ Y := by linarith
  by_cases hyY : |y| ≤ Y
  · -- grid coverage below the cutoff
    have hstep0 : 0 < xiWardSampleGridStep Y := xiWardSampleGridStep_pos Y
    have hstephalf : xiWardSampleGridStep Y ≤ 1 / 2 :=
      xiWardSampleGridStep_le_half Y
    set step := xiWardSampleGridStep Y
    set k : ℤ := round (-y / step) with hkdef
    have hround : |(-y / step) - (k : ℝ)| ≤ 1 / 2 := by
      rw [hkdef]
      exact abs_sub_round _
    have habs : |(k : ℝ) * step + y| ≤ step / 2 := by
      have h2 : |(-y / step) - (k : ℝ)| * step = |(k : ℝ) * step + y| := by
        have hs : |step| = step := abs_of_pos hstep0
        calc |(-y / step) - (k : ℝ)| * step
            = |(-y / step) - (k : ℝ)| * |step| := by rw [hs]
          _ = |((-y / step) - (k : ℝ)) * step| := (abs_mul _ _).symm
          _ = |-((k : ℝ) * step + y)| := by
              congr 1
              field_simp
              ring
          _ = |(k : ℝ) * step + y| := abs_neg _
      have h1 : |(-y / step) - (k : ℝ)| * step ≤ (1 / 2) * step :=
        mul_le_mul_of_nonneg_right hround hstep0.le
      rw [h2] at h1
      linarith
    refine ⟨(k : ℝ) * step, Or.inr ⟨⟨k, rfl⟩, ?_⟩, ?_⟩
    · have h3 : |(k : ℝ) * step| ≤ |(k : ℝ) * step + y| + |y| := by
        calc |(k : ℝ) * step| = |((k : ℝ) * step + y) + -y| := by
              congr 1
              ring
          _ ≤ |(k : ℝ) * step + y| + |-y| := abs_add_le _ _
          _ = |(k : ℝ) * step + y| + |y| := by rw [abs_neg]
      linarith
    · have hsq2 : ((k : ℝ) * step + y) ^ 2 ≤ (step / 2) ^ 2 := by
        rw [← sq_abs ((k : ℝ) * step + y)]
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      have hanti : xiWardZeroFreeMargin Y ≤ xiWardZeroFreeMargin y :=
        xiWardZeroFreeMargin_anti (by rw [abs_of_nonneg hY0]; exact hyY)
      have hstepsq : step ^ 2 = xiWardZeroFreeMargin Y / 2 :=
        sq_xiWardSampleGridStep Y
      nlinarith [hsq2, hstepsq, hanti, xiWardZeroFreeMargin_pos Y]
  · -- prime-log coverage above the cutoff
    push Not at hyY
    have hy0abs : 0 ≤ |y| := abs_nonneg y
    have hyy₀ : y₀ ≤ |y| := by
      have h := le_trans (le_trans (le_max_left y₀ 3) (le_max_left _ _)) hY
      linarith
    have hyy₂ : y₂ ≤ |y| := by
      have h := le_trans (le_trans (le_max_left y₂ 1) (le_max_right _ _)) hY
      linarith
    have hy1 : 1 ≤ |y| := by
      have h := le_trans (le_trans (le_max_right y₂ 1) (le_max_right _ _)) hY
      linarith
    set eta : ℝ := Real.sqrt (xiWardZeroFreeMargin y / 2) with hetadef
    have hmy := xiWardZeroFreeMargin_pos y
    have heta0 : 0 < eta := Real.sqrt_pos.mpr (by linarith)
    have hetasq : eta ^ 2 = xiWardZeroFreeMargin y / 2 :=
      Real.sq_sqrt (by linarith)
    have heta1 : eta ≤ 1 := by
      have h1 : xiWardZeroFreeMargin y / 2 ≤ 1 / 4 := by
        linarith [xiWardZeroFreeMargin_le_half y]
      calc eta ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt h1
        _ = 1 / 2 := by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        _ ≤ 1 := by norm_num
    -- the prime-gap scale is below the detection radius
    have hgap : K * Real.exp (-(c₂ * |y| ^ ((1 : ℝ) / 10))) ≤ eta := by
      have hchain := hy₂ |y| hyy₂
      have hL : (0 : ℝ) ≤ Real.log (|y| + 9) := by
        linarith [one_lt_log_abs_add_nine y]
      have hLpos : 0 < Real.log (|y| + 9) ^ (9 : ℕ) :=
        pow_pos (by linarith [one_lt_log_abs_add_nine y]) 9
      have hpoly : Real.log (|y| + 9) ^ (9 : ℕ) ≤
          100 ^ (9 : ℕ) * 2 * |y| ^ ((1 : ℝ) / 10) := by
        have h1 : Real.log (|y| + 9) ≤
            (|y| + 9) ^ ((1 : ℝ) / 100) / ((1 : ℝ) / 100) :=
          Real.log_le_rpow_div (by linarith) (by norm_num)
        have h1' : Real.log (|y| + 9) ≤ 100 * (|y| + 9) ^ ((1 : ℝ) / 100) := by
          rw [div_div_eq_mul_div, div_one] at h1
          linarith
        have h3 : (100 * (|y| + 9) ^ ((1 : ℝ) / 100)) ^ (9 : ℕ) =
            100 ^ (9 : ℕ) * (|y| + 9) ^ ((9 : ℝ) / 100) := by
          rw [mul_pow]
          congr 1
          rw [← Real.rpow_natCast ((|y| + 9) ^ ((1 : ℝ) / 100)) 9,
            ← Real.rpow_mul (by linarith)]
          norm_num
        have h4 : (|y| + 9) ^ ((9 : ℝ) / 100) ≤ (|y| + 9) ^ ((1 : ℝ) / 10) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        have h5 : (|y| + 9) ^ ((1 : ℝ) / 10) ≤ 2 * |y| ^ ((1 : ℝ) / 10) := by
          have h6 : |y| + 9 ≤ 1024 * |y| := by linarith
          have h7 : (|y| + 9) ^ ((1 : ℝ) / 10) ≤
              (1024 * |y|) ^ ((1 : ℝ) / 10) :=
            Real.rpow_le_rpow (by linarith) h6 (by norm_num)
          have h8 : ((1024 : ℝ) * |y|) ^ ((1 : ℝ) / 10) =
              2 * |y| ^ ((1 : ℝ) / 10) := by
            rw [Real.mul_rpow (by norm_num) hy0abs]
            congr 1
            rw [show (1024 : ℝ) = 2 ^ (10 : ℕ) by norm_num,
              ← Real.rpow_natCast 2 10, ← Real.rpow_mul (by norm_num)]
            norm_num
          rw [h8] at h7
          exact h7
        calc Real.log (|y| + 9) ^ (9 : ℕ)
            ≤ (100 * (|y| + 9) ^ ((1 : ℝ) / 100)) ^ (9 : ℕ) :=
              pow_le_pow_left₀ hL h1' 9
          _ = 100 ^ (9 : ℕ) * (|y| + 9) ^ ((9 : ℝ) / 100) := h3
          _ ≤ 100 ^ (9 : ℕ) * (|y| + 9) ^ ((1 : ℝ) / 10) :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
          _ ≤ 100 ^ (9 : ℕ) * (2 * |y| ^ ((1 : ℝ) / 10)) :=
              mul_le_mul_of_nonneg_left h5 (by positivity)
          _ = 100 ^ (9 : ℕ) * 2 * |y| ^ ((1 : ℝ) / 10) := by ring
      have hexpand : (K * Real.exp (-(c₂ * |y| ^ ((1 : ℝ) / 10)))) ^ 2 =
          K ^ 2 * Real.exp (-(2 * c₂ * |y| ^ ((1 : ℝ) / 10))) := by
        rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
        congr 1
        congr 1
        ring
      have hmargy : xiWardZeroFreeMargin y =
          xiWardZeroFreeMarginC / Real.log (|y| + 9) ^ (9 : ℕ) := rfl
      have hsqgap : (K * Real.exp (-(c₂ * |y| ^ ((1 : ℝ) / 10)))) ^ 2 ≤
          xiWardZeroFreeMargin y / 2 := by
        rw [hexpand, hmargy, le_div_iff₀ (by norm_num : (0 : ℝ) < 2),
          le_div_iff₀ hLpos]
        have hE0 : 0 ≤ Real.exp (-(2 * c₂ * |y| ^ ((1 : ℝ) / 10))) :=
          (Real.exp_pos _).le
        calc K ^ 2 * Real.exp (-(2 * c₂ * |y| ^ ((1 : ℝ) / 10))) * 2 *
              Real.log (|y| + 9) ^ (9 : ℕ)
            ≤ K ^ 2 * Real.exp (-(2 * c₂ * |y| ^ ((1 : ℝ) / 10))) * 2 *
              (100 ^ (9 : ℕ) * 2 * |y| ^ ((1 : ℝ) / 10)) := by
              apply mul_le_mul_of_nonneg_left hpoly
              positivity
          _ = 4 * K ^ 2 * 100 ^ (9 : ℕ) *
              (|y| ^ ((1 : ℝ) / 10) *
                Real.exp (-(2 * c₂ * |y| ^ ((1 : ℝ) / 10)))) := by ring
          _ ≤ xiWardZeroFreeMarginC := hchain
      have hgap0 : 0 ≤ K * Real.exp (-(c₂ * |y| ^ ((1 : ℝ) / 10))) :=
        mul_nonneg hK.le (Real.exp_pos _).le
      rw [hetadef]
      exact (Real.le_sqrt hgap0 (by linarith)).mpr hsqgap
    obtain ⟨p, hp, hlog1, hlog2⟩ :=
      hsupply |y| eta hyy₀ heta0 heta1 hgap
    have hlogp0 : 0 ≤ Real.log p := by linarith
    rcases le_or_gt 0 y with hy | hy
    · -- positive height: sample at `−log p`
      have habs : |y| = y := abs_of_nonneg hy
      refine ⟨-(Real.log p), Or.inl ⟨p, hp, by
        rw [abs_neg, abs_of_nonneg hlogp0]⟩, ?_⟩
      have h1 : y ≤ Real.log p := by rwa [habs] at hlog1
      have h2 : Real.log p ≤ y + eta := by rwa [habs] at hlog2
      have hsqb : (-(Real.log p) + y) ^ 2 ≤ eta ^ 2 := by
        apply sq_le_sq'
        · linarith
        · linarith
      linarith [hetasq, hsqb]
    · -- negative height: sample at `log p`
      have habs : |y| = -y := abs_of_neg hy
      refine ⟨Real.log p, Or.inl ⟨p, hp, abs_of_nonneg hlogp0⟩, ?_⟩
      have h1 : -y ≤ Real.log p := by rwa [habs] at hlog1
      have h2 : Real.log p ≤ -y + eta := by rwa [habs] at hlog2
      have hsqb : (Real.log p + y) ^ 2 ≤ eta ^ 2 := by
        apply sq_le_sq'
        · linarith
        · linarith
      linarith [hetasq, hsqb]

/-- **Prime-log sampled completeness law.**  Past an explicit cutoff, the
four-unit Euler-edge scalar law sampled only on the signed prime logarithms and
one finite grid is exactly RH: the primes themselves form a sufficient jury for
the Ward law. -/
theorem exists_cutoff_riemannHypothesis_iff_primeLogSampledScalarLaw :
    ∃ y₁ : ℝ, 3 ≤ y₁ ∧ ∀ Y : ℝ, y₁ ≤ Y →
      (RiemannHypothesis ↔
        ContinuedXiWardSampledScalarLaw (xiWardPrimeLogSampleSet Y)) := by
  obtain ⟨y₁, hy₁3, hcov⟩ := exists_cutoff_xiWardDetectionCover_primeLogSampleSet
  exact ⟨y₁, hy₁3, fun Y hY =>
    riemannHypothesis_iff_continuedXiWardSampledScalarLaw (hcov Y hY)⟩

/-- The prime-log sample family is locally finite: every bounded height band
meets it in a finite set.  The sampled law is therefore a strictly discrete
criterion, not recoverable from the full edge law by any density argument. -/
theorem xiWardPrimeLogSampleSet_bounded_finite (Y R : ℝ) :
    {t : ℝ | t ∈ xiWardPrimeLogSampleSet Y ∧ |t| ≤ R}.Finite := by
  have hstep0 : 0 < xiWardSampleGridStep Y := xiWardSampleGridStep_pos Y
  set step := xiWardSampleGridStep Y
  set N : ℕ := Nat.ceil (Real.exp R)
  set M : ℤ := Int.ceil ((Y + 1) / step)
  have hfin : (((fun p : ℕ => Real.log p) '' Set.Iic N) ∪
      ((fun p : ℕ => -Real.log p) '' Set.Iic N) ∪
      ((fun k : ℤ => (k : ℝ) * step) '' Set.Icc (-M) M)).Finite :=
    (((Set.finite_Iic N).image _).union ((Set.finite_Iic N).image _)).union
      ((Set.finite_Icc (-M) M).image _)
  apply hfin.subset
  rintro t ⟨htS, htR⟩
  rcases htS with ⟨p, hp, habs⟩ | ⟨⟨k, rfl⟩, hbound⟩
  · -- prime-log points below `R` come from primes below `exp R`
    have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlogle : Real.log p ≤ R := by rw [← habs]; exact htR
    have hpleR : (p : ℝ) ≤ Real.exp R :=
      (Real.log_le_iff_le_exp hppos).mp hlogle
    have hpN : p ≤ N := by
      have h1 : (p : ℝ) ≤ (N : ℝ) :=
        le_trans hpleR (Nat.le_ceil (Real.exp R))
      exact_mod_cast h1
    have hlogp0 : 0 ≤ Real.log p := by
      apply Real.log_nonneg
      exact_mod_cast hp.one_lt.le
    rcases (abs_eq hlogp0).mp habs with ht | ht
    · exact Or.inl (Or.inl ⟨p, hpN, ht.symm⟩)
    · exact Or.inl (Or.inr ⟨p, hpN, by rw [ht]⟩)
  · -- grid points below the padded cutoff come from bounded integers
    have hkabs : |(k : ℝ)| * step ≤ Y + 1 := by
      calc |(k : ℝ)| * step = |(k : ℝ) * step| := by
            rw [abs_mul, abs_of_pos hstep0]
        _ ≤ Y + 1 := hbound
    have hkle : |(k : ℝ)| ≤ (Y + 1) / step :=
      (le_div_iff₀ hstep0).mpr hkabs
    have hkM : k ∈ Set.Icc (-M) M := by
      have h1 : |(k : ℝ)| ≤ (M : ℝ) := le_trans hkle (Int.le_ceil _)
      have h2 : |k| ≤ M := by rwa [← Int.cast_abs, Int.cast_le] at h1
      exact abs_le.mp h2
    exact Or.inr ⟨k, hkM, rfl⟩

end

end RHTower

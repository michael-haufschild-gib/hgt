import GaloisForLFunctions.RHTower.CCMFirstClockVolterra
import GaloisForLFunctions.RHTower.LandauIntegralTransfer
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# First-clock CCM Landau completeness

This module develops the converse direction of the literal first-clock CCM sign law.  The key
mechanism is a branch-free bypass:

1. the positive Laplace axis has a universal open cone disjoint from every dilated Xi segment;
2. Landau propagation acts on the first-clock rational divisor in that cone;
3. the exact dilation-Volterra law reflects all positive exponential moments to the Xi screw;
4. the screw Laplace transform is rational and equals the centered Xi logarithmic derivative.

Thus an off-line Xi zero becomes an unavoidable rational pole.  No rightmost zero, discrete
sampling, zero enumeration, or contour-deformation hypothesis is used.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The strong endpoint-source height gap is a gap in the real coordinate of every centered
Xi point.  Its strict margin over `9 / 2` is what makes the first-clock cone separation
quantitative rather than merely nonvanishing. -/
theorem nine_halves_lt_abs_re_xiSpectralPoint (q : XiZeroCopy) :
    9 / 2 < |(xiSpectralPoint q).re| := by
  by_contra h
  have hre : |(xiSpectralPoint q).re| ≤ 9 / 2 := le_of_not_gt h
  exact (XiC_ne_zero_of_abs_re_le_nine_halves hre)
    (XiC_xiSpectralPoint_eq_zero q)

/-- The weaker integer form retained for downstream first-clock estimates. -/
theorem four_lt_abs_re_xiSpectralPoint (q : XiZeroCopy) :
    4 < |(xiSpectralPoint q).re| :=
  lt_trans (by norm_num : (4 : ℝ) < 9 / 2)
    (nine_halves_lt_abs_re_xiSpectralPoint q)

/-- **Positive-axis cone law, negative orientation.**  No negatively oriented dilation segment
of the complete Xi divisor enters the universal cone `|Im s| ≤ 8 Re s`, `Re s > 0`. -/
theorem ccmFirstClockLaplaceCone_sub_ne_zero
    {s : ℂ} (hsre : 0 < s.re) (hscone : |s.im| ≤ 8 * s.re)
    (q : XiZeroCopy) {u : ℝ} (hu : 0 ≤ u) :
    s - I * xiSpectralPoint q * (u : ℂ) ≠ 0 := by
  intro hzero
  have heq : s = I * xiSpectralPoint q * (u : ℂ) := sub_eq_zero.mp hzero
  have hre : s.re = -(xiSpectralPoint q).im * u := by
    rw [heq]
    simp [mul_re]
  have him : s.im = (xiSpectralPoint q).re * u := by
    rw [heq]
    simp [mul_im]
  have hu0 : u ≠ 0 := by
    intro hu0
    simp [hu0] at hre
    linarith
  have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have hzstrip := xiSpectralPoint_im_mem_openHalf q
  have hrele : 8 * s.re < 4 * u := by
    rw [hre]
    nlinarith
  have himgt : 4 * u < |s.im| := by
    rw [him, abs_mul, abs_of_nonneg hu]
    exact mul_lt_mul_of_pos_right
      (four_lt_abs_re_xiSpectralPoint q) hupos
  linarith

/-- **Positive-axis cone law, positive orientation.**  No positively oriented dilation segment
of the complete Xi divisor enters the universal cone `|Im s| ≤ 8 Re s`, `Re s > 0`. -/
theorem ccmFirstClockLaplaceCone_add_ne_zero
    {s : ℂ} (hsre : 0 < s.re) (hscone : |s.im| ≤ 8 * s.re)
    (q : XiZeroCopy) {u : ℝ} (hu : 0 ≤ u) :
    s + I * xiSpectralPoint q * (u : ℂ) ≠ 0 := by
  intro hzero
  have heq : s = -(I * xiSpectralPoint q * (u : ℂ)) :=
    eq_neg_of_add_eq_zero_left hzero
  have hre : s.re = (xiSpectralPoint q).im * u := by
    rw [heq]
    simp [mul_re]
  have him : s.im = -(xiSpectralPoint q).re * u := by
    rw [heq]
    simp [mul_im]
  have hu0 : u ≠ 0 := by
    intro hu0
    simp [hu0] at hre
    linarith
  have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have hzstrip := xiSpectralPoint_im_mem_openHalf q
  have hrele : 8 * s.re < 4 * u := by
    rw [hre]
    nlinarith
  have himgt : 4 * u < |s.im| := by
    rw [him, abs_mul, abs_neg, abs_of_nonneg hu]
    exact mul_lt_mul_of_pos_right
      (four_lt_abs_re_xiSpectralPoint q) hupos
  linarith

/-- **Quantitative cone separation, negative orientation.**  The strong source height gap
`|Re z_q| > 9/2`, rather than the weaker integer gap `> 4`, creates a uniform angular margin
from the slope-eight cone.  Every dilated negative Xi ray stays at distance at least
`Re(s)/10`.  This is the missing uniform estimate needed for normal convergence of the
first-clock continuation. -/
theorem ccmFirstClockLaplaceCone_norm_sub
    {s : ℂ} (hsre : 0 < s.re) (hscone : |s.im| ≤ 8 * s.re)
    (q : XiZeroCopy) {u : ℝ} (hu : 0 ≤ u) :
    s.re / 10 ≤ ‖s - I * xiSpectralPoint q * (u : ℂ)‖ := by
  by_contra hnot
  have hnorm : ‖s - I * xiSpectralPoint q * (u : ℂ)‖ < s.re / 10 :=
    lt_of_not_ge hnot
  have hu0 : u ≠ 0 := by
    intro hu0
    simp [hu0] at hnorm
    have hreNorm : s.re ≤ ‖s‖ :=
      (le_abs_self s.re).trans (Complex.abs_re_le_norm s)
    linarith
  have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  let d : ℂ := s - I * xiSpectralPoint q * (u : ℂ)
  have hdre : d.re = s.re + (xiSpectralPoint q).im * u := by
    dsimp only [d]
    simp [mul_re]
  have hdim : d.im = s.im - (xiSpectralPoint q).re * u := by
    dsimp only [d]
    simp [mul_im]
  have hdreAbs : |d.re| < s.re / 10 :=
    (Complex.abs_re_le_norm d).trans_lt hnorm
  have hdimAbs : |d.im| < s.re / 10 :=
    (Complex.abs_im_le_norm d).trans_lt hnorm
  have hb := xiSpectralPoint_im_mem_openHalf q
  have hb' : -(1 / 2 : ℝ) < (xiSpectralPoint q).im := by
    linarith [hb.1]
  have hbmul : -(1 / 2 : ℝ) * u < (xiSpectralPoint q).im * u :=
    mul_lt_mul_of_pos_right hb' hupos
  have hulower : 9 / 5 * s.re < u := by
    have hdreUpper := (abs_lt.mp hdreAbs).2
    rw [hdre] at hdreUpper
    nlinarith
  have ha := nine_halves_lt_abs_re_xiSpectralPoint q
  have hau : 9 / 2 * u < |(xiSpectralPoint q).re| * u :=
    mul_lt_mul_of_pos_right ha hupos
  have hrewrite : |(xiSpectralPoint q).re| * u =
      |(xiSpectralPoint q).re * u| := by
    rw [abs_mul, abs_of_pos hupos]
  rw [hrewrite] at hau
  have htri : |(xiSpectralPoint q).re * u| ≤ |s.im| + |d.im| := by
    have heq : (xiSpectralPoint q).re * u = s.im - d.im := by
      linarith
    rw [heq, sub_eq_add_neg]
    exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
  have huupper : 9 / 2 * u < 81 / 10 * s.re := by
    calc
      9 / 2 * u < |(xiSpectralPoint q).re * u| := hau
      _ ≤ |s.im| + |d.im| := htri
      _ < 8 * s.re + s.re / 10 := by linarith
      _ = 81 / 10 * s.re := by ring
  nlinarith

/-- **Quantitative cone separation, positive orientation.**  The same universal distance
bound holds for every positively oriented dilated Xi ray. -/
theorem ccmFirstClockLaplaceCone_norm_add
    {s : ℂ} (hsre : 0 < s.re) (hscone : |s.im| ≤ 8 * s.re)
    (q : XiZeroCopy) {u : ℝ} (hu : 0 ≤ u) :
    s.re / 10 ≤ ‖s + I * xiSpectralPoint q * (u : ℂ)‖ := by
  by_contra hnot
  have hnorm : ‖s + I * xiSpectralPoint q * (u : ℂ)‖ < s.re / 10 :=
    lt_of_not_ge hnot
  have hu0 : u ≠ 0 := by
    intro hu0
    simp [hu0] at hnorm
    have hreNorm : s.re ≤ ‖s‖ :=
      (le_abs_self s.re).trans (Complex.abs_re_le_norm s)
    linarith
  have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  let d : ℂ := s + I * xiSpectralPoint q * (u : ℂ)
  have hdre : d.re = s.re - (xiSpectralPoint q).im * u := by
    dsimp only [d]
    simp [mul_re]
    ring
  have hdim : d.im = s.im + (xiSpectralPoint q).re * u := by
    dsimp only [d]
    simp [mul_im]
  have hdreAbs : |d.re| < s.re / 10 :=
    (Complex.abs_re_le_norm d).trans_lt hnorm
  have hdimAbs : |d.im| < s.re / 10 :=
    (Complex.abs_im_le_norm d).trans_lt hnorm
  have hb := xiSpectralPoint_im_mem_openHalf q
  have hbmul : (xiSpectralPoint q).im * u < (1 / 2 : ℝ) * u :=
    mul_lt_mul_of_pos_right hb.2 hupos
  have hulower : 9 / 5 * s.re < u := by
    have hdreUpper := (abs_lt.mp hdreAbs).2
    rw [hdre] at hdreUpper
    nlinarith
  have ha := nine_halves_lt_abs_re_xiSpectralPoint q
  have hau : 9 / 2 * u < |(xiSpectralPoint q).re| * u :=
    mul_lt_mul_of_pos_right ha hupos
  have hrewrite : |(xiSpectralPoint q).re| * u =
      |(xiSpectralPoint q).re * u| := by
    rw [abs_mul, abs_of_pos hupos]
  rw [hrewrite] at hau
  have htri : |(xiSpectralPoint q).re * u| ≤ |s.im| + |d.im| := by
    have heq : (xiSpectralPoint q).re * u = d.im - s.im := by
      linarith
    rw [heq, sub_eq_add_neg]
    calc
      |d.im + -s.im| ≤ |d.im| + |-s.im| := abs_add_le _ _
      _ = |s.im| + |d.im| := by rw [abs_neg, add_comm]
  have huupper : 9 / 2 * u < 81 / 10 * s.re := by
    calc
      9 / 2 * u < |(xiSpectralPoint q).re * u| := hau
      _ ≤ |s.im| + |d.im| := htri
      _ < 8 * s.re + s.re / 10 := by linarith
      _ = 81 / 10 * s.re := by ring
  nlinarith

/-- Every half-radius disk centered on the positive real axis lies in the universal first-clock
Laplace cone.  These overlapping disks give a geometric Landau continuation chain down to zero. -/
theorem closedBall_real_axis_subset_ccmFirstClockLaplaceCone
    {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : s ∈ Metric.closedBall (r : ℂ) (r / 2)) :
    0 < s.re ∧ |s.im| ≤ 8 * s.re := by
  have hdist : dist s (r : ℂ) ≤ r / 2 := by
    simpa only [Metric.mem_closedBall] using hs
  have hnorm : ‖s - (r : ℂ)‖ ≤ r / 2 := by
    simpa only [dist_eq, dist_zero_right] using hdist
  have hreAbs : |s.re - r| ≤ r / 2 := by
    calc
      |s.re - r| = |(s - (r : ℂ)).re| := by simp
      _ ≤ ‖s - (r : ℂ)‖ := Complex.abs_re_le_norm _
      _ ≤ r / 2 := hnorm
  have himAbs : |s.im| ≤ r / 2 := by
    calc
      |s.im| = |(s - (r : ℂ)).im| := by simp
      _ ≤ ‖s - (r : ℂ)‖ := Complex.abs_im_le_norm _
      _ ≤ r / 2 := hnorm
  constructor
  · have := (abs_le.mp hreAbs).1
    linarith
  · have := (abs_le.mp hreAbs).1
    linarith

/-- Every reciprocal-square screw atom is Laplace integrable on the initial Xi half-plane. -/
theorem integrableOn_exp_mul_ccmFirstClockScrewKernel
    {s z : ℂ} (hz : z ≠ 0)
    (hzstrip : |z.im| < 1 / 2) (hsHalf : 1 / 2 < s.re) :
    IntegrableOn (fun L : ℝ =>
      Complex.exp (-s * (L : ℂ)) * ccmFirstClockScrewKernel L z) (Ioi 0) := by
  have hminus : (-s + I * z).re < 0 := by
    simp only [add_re, neg_re, mul_re, I_re, zero_mul, I_im, one_mul,
      zero_sub]
    have hzlow : -(1 / 2 : ℝ) < z.im := (abs_lt.mp hzstrip).1
    linarith
  have hplus : (-s - I * z).re < 0 := by
    simp only [sub_re, neg_re, mul_re, I_re, zero_mul, I_im, one_mul,
      zero_sub]
    have hzhigh : z.im < 1 / 2 := (abs_lt.mp hzstrip).2
    linarith
  have hsneg : (-s).re < 0 := by
    simp
    linarith
  have hibase := integrableOn_exp_mul_complex_Ioi hsneg 0
  have hileft := integrableOn_exp_mul_complex_Ioi hminus 0
  have hiright := integrableOn_exp_mul_complex_Ioi hplus 0
  have htarget : IntegrableOn (fun L : ℝ =>
      (Complex.exp ((-s) * L) -
        (Complex.exp ((-s + I * z) * L) +
          Complex.exp ((-s - I * z) * L)) / 2) / z ^ 2) (Ioi 0) :=
    (hibase.sub ((hileft.add hiright).div_const 2)).div_const _
  refine htarget.congr_fun ?_ measurableSet_Ioi
  intro L _hL
  simp only
  rw [ccmFirstClockScrewKernel, Complex.cos]
  have hleftExp :
      Complex.exp ((L : ℂ) * (-s + I * z)) =
        Complex.exp (-(s * (L : ℂ))) *
          Complex.exp ((L : ℂ) * I * z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hrightExp :
      Complex.exp ((L : ℂ) * (-s - I * z)) =
        Complex.exp (-(s * (L : ℂ))) *
          Complex.exp (-((L : ℂ) * I * z)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  field_simp [hz]
  rw [hleftExp, hrightExp]
  ring

/-- Exact one-atom Laplace transform of the reciprocal-square screw kernel.  The only analytic
input is `Re s > 1/2`, the sharp unconditional centered Xi strip containing every possible
spectral point. -/
theorem integral_exp_mul_ccmFirstClockScrewKernel
    {s z : ℂ} (hz : z ≠ 0)
    (hzstrip : |z.im| < 1 / 2) (hsHalf : 1 / 2 < s.re) :
    (∫ L : ℝ in Ioi 0,
      Complex.exp (-s * (L : ℂ)) * ccmFirstClockScrewKernel L z) =
        1 / (s * (s ^ 2 + z ^ 2)) := by
  have hminus : (-s + I * z).re < 0 := by
    simp only [add_re, neg_re, mul_re, I_re, zero_mul, I_im, one_mul,
      zero_sub]
    have hzlow : -(1 / 2 : ℝ) < z.im := (abs_lt.mp hzstrip).1
    linarith
  have hplus : (-s - I * z).re < 0 := by
    simp only [sub_re, neg_re, mul_re, I_re, zero_mul, I_im, one_mul,
      zero_sub]
    have hzhigh : z.im < 1 / 2 := (abs_lt.mp hzstrip).2
    linarith
  have hsneg : (-s).re < 0 := by
    simp
    linarith
  have hdenMinus : s - I * z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [sub_re, mul_re, I_re, zero_mul, I_im, one_mul, zero_sub,
      zero_re] at hre
    have hzlow : -(1 / 2 : ℝ) < z.im := (abs_lt.mp hzstrip).1
    linarith
  have hdenPlus : s + I * z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, mul_re, I_re, zero_mul, I_im, one_mul, zero_sub,
      zero_re] at hre
    have hzhigh : z.im < 1 / 2 := (abs_lt.mp hzstrip).2
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, zero_re] at hsHalf
    linarith
  have hsq : s ^ 2 + z ^ 2 ≠ 0 := by
    rw [show s ^ 2 + z ^ 2 = (s - I * z) * (s + I * z) by
      rw [mul_add, sub_mul]
      ring_nf
      rw [I_sq]
      ring]
    exact mul_ne_zero hdenMinus hdenPlus
  have hbase :
      (∫ L : ℝ in Ioi 0, Complex.exp ((-s) * L)) = 1 / s := by
    rw [integral_exp_mul_complex_Ioi hsneg 0]
    simp
  have hleft :
      (∫ L : ℝ in Ioi 0, Complex.exp ((-s + I * z) * L)) =
        1 / (s - I * z) := by
    rw [integral_exp_mul_complex_Ioi hminus 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have hneg : -s + I * z = -(s - I * z) := by ring
    rw [hneg]
    field_simp [hdenMinus]
  have hright :
      (∫ L : ℝ in Ioi 0, Complex.exp ((-s - I * z) * L)) =
        1 / (s + I * z) := by
    rw [integral_exp_mul_complex_Ioi hplus 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have hneg : -s - I * z = -(s + I * z) := by ring
    rw [hneg]
    field_simp [hdenPlus]
  have hibase := integrableOn_exp_mul_complex_Ioi hsneg 0
  have hileft := integrableOn_exp_mul_complex_Ioi hminus 0
  have hiright := integrableOn_exp_mul_complex_Ioi hplus 0
  have hfun : (fun L : ℝ =>
      Complex.exp (-s * (L : ℂ)) *
        ((1 - Complex.cos ((L : ℂ) * z)) / z ^ 2)) =
      fun L : ℝ =>
        (Complex.exp ((-s) * L) -
          (Complex.exp ((-s + I * z) * L) +
            Complex.exp ((-s - I * z) * L)) / 2) / z ^ 2 := by
    funext L
    rw [Complex.cos]
    have hleftExp :
        Complex.exp (-(s * (L : ℂ))) *
            Complex.exp (((L : ℂ) * z) * I) =
          Complex.exp ((L : ℂ) * (-s + z * I)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have hrightExp :
        Complex.exp (-(s * (L : ℂ))) *
            Complex.exp (-(((L : ℂ) * z) * I)) =
          Complex.exp ((L : ℂ) * (-s - z * I)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    field_simp [hz]
    rw [mul_sub, mul_add]
    rw [hleftExp, hrightExp]
  have hiavg : IntegrableOn (fun L : ℝ =>
      (Complex.exp ((-s + I * z) * L) +
        Complex.exp ((-s - I * z) * L)) / 2) (Ioi 0) :=
    (hileft.add hiright).div_const 2
  have hinner :
      (∫ L : ℝ in Ioi 0,
        Complex.exp ((-s) * L) -
          (Complex.exp ((-s + I * z) * L) +
            Complex.exp ((-s - I * z) * L)) / 2) =
        1 / s - (1 / (s - I * z) + 1 / (s + I * z)) / 2 := by
    rw [integral_sub hibase hiavg]
    rw [integral_div, integral_add hileft hiright]
    rw [hbase, hleft, hright]
  simp_rw [ccmFirstClockScrewKernel]
  rw [hfun]
  rw [integral_div]
  rw [hinner]
  field_simp [hz, hs0, hdenMinus, hdenPlus, hsq]
  have hfactor : (s - I * z) * (s + I * z) = s ^ 2 + z ^ 2 := by
    rw [mul_add, sub_mul]
    ring_nf
    rw [I_sq]
    ring
  simp_rw [hfactor]
  ring_nf
  rw [I_sq]
  ring

/-- **Branch-free Xi screw transform law.**  On the initial half-plane, the complete
multiplicity-exact rational pole series is exactly the centered Xi logarithmic derivative.
This is the target that Landau propagation reaches after inverting the first-clock Volterra
filter. -/
theorem tsum_screwLaplace_eq_logDeriv_XiC
    {s : ℂ} (hsHalf : 1 / 2 < s.re) :
    (∑' q : XiZeroCopy,
      1 / (s * (s ^ 2 + xiSpectralPoint q ^ 2))) =
        I / s ^ 2 * logDeriv XiC (I * s) := by
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs, zero_re] at hsHalf
    linarith
  have hXi : XiC (I * s) ≠ 0 := by
    intro hzero
    have hstrip := xiC_zero_im_mem_openHalf hzero
    have him : (I * s).im = s.re := by simp [mul_im]
    rw [him] at hstrip
    linarith
  have hsum := summable_xiReciprocalSquareResolventTerm hXi
  have hterm (q : XiZeroCopy) :
      1 / (s * (s ^ 2 + xiSpectralPoint q ^ 2)) =
        (1 / s) * xiReciprocalSquareResolventTerm (I * s) q := by
    have hz0 := xiSpectralPoint_ne_zero q
    have hden :
        s ^ 2 + xiSpectralPoint q ^ 2 ≠ 0 := by
      intro hzero
      have hprod :
          (I * s - xiSpectralPoint q) *
              (I * s + xiSpectralPoint q) = 0 := by
        calc
          (I * s - xiSpectralPoint q) *
              (I * s + xiSpectralPoint q) =
              -(s ^ 2 + xiSpectralPoint q ^ 2) := by
                rw [mul_add, sub_mul]
                ring_nf
                rw [I_sq]
                ring
          _ = 0 := by rw [hzero, neg_zero]
      rcases mul_eq_zero.mp hprod with hpos | hneg
      · have heq : I * s = xiSpectralPoint q := sub_eq_zero.mp hpos
        exact hXi (by rw [heq]; exact XiC_xiSpectralPoint_eq_zero q)
      · have heq : I * s = -xiSpectralPoint q :=
          eq_neg_of_add_eq_zero_left hneg
        exact hXi (by
          rw [heq, XiC_even]
          exact XiC_xiSpectralPoint_eq_zero q)
    rw [xiReciprocalSquareResolventTerm, xiZeroCopyReciprocalSquare]
    field_simp [hs0, hz0, hden]
    rw [I_sq]
    ring_nf
    rw [← add_mul, mul_inv_cancel₀ hden]
  calc
    (∑' q : XiZeroCopy,
        1 / (s * (s ^ 2 + xiSpectralPoint q ^ 2))) =
        ∑' q : XiZeroCopy,
          (1 / s) * xiReciprocalSquareResolventTerm (I * s) q := by
            apply tsum_congr
            exact hterm
    _ = (1 / s) *
        ∑' q : XiZeroCopy, xiReciprocalSquareResolventTerm (I * s) q := by
          rw [tsum_mul_left]
    _ = I / s ^ 2 * logDeriv XiC (I * s) := by
      have htrace := xiRelativeResolventTrace_eq_reciprocalSquareResolvent hXi
      have hlog := logDeriv_XiC_eq_relativeResolventTrace hXi
      field_simp [hs0]
      rw [show s * I = I * s by ring]
      rw [hlog, htrace]
      ring_nf
      rw [I_sq]
      ring

/-- **Complete Xi screw Laplace law.**  The full multiplicity-exact screw profile, rather than
only its formal atom series, has Laplace transform equal to the centered Xi logarithmic
derivative on `Re s > 1/2`.  Absolute sum--integral exchange follows from the reciprocal-square
divisor mass and the sharp centered critical-strip bound. -/
theorem integral_exp_mul_xiScrewDivisor_eq_logDeriv_XiC
    {s : ℂ} (hsHalf : 1 / 2 < s.re) :
    (∫ L : ℝ in Ioi 0,
      Complex.exp (-s * (L : ℂ)) * xiScrewDivisor L) =
        I / s ^ 2 * logDeriv XiC (I * s) := by
  let F : XiZeroCopy → ℝ → ℂ := fun q L =>
    Complex.exp (-s * (L : ℂ)) *
      ccmFirstClockScrewKernel L (xiSpectralPoint q)
  let g : ℝ → ℝ := fun L =>
    Real.exp ((-s.re + 1 / 2) * L) + Real.exp ((-s.re) * L)
  have hdecay1 : -s.re + 1 / 2 < 0 := by linarith
  have hdecay2 : -s.re < 0 := by linarith
  have hgint : IntegrableOn g (Ioi 0) :=
    (integrableOn_exp_mul_Ioi hdecay1 0).add
      (integrableOn_exp_mul_Ioi hdecay2 0)
  have hFint : ∀ q : XiZeroCopy, IntegrableOn (F q) (Ioi 0) := by
    intro q
    have hzstrip : |(xiSpectralPoint q).im| < 1 / 2 := by
      rw [abs_lt]
      constructor <;> linarith [xiSpectralPoint_im_mem_openHalf q]
    exact integrableOn_exp_mul_ccmFirstClockScrewKernel
      (xiSpectralPoint_ne_zero q) hzstrip hsHalf
  have hpointBound (q : XiZeroCopy) (L : ℝ) (hL : L ∈ Ioi (0 : ℝ)) :
      ‖F q L‖ ≤ g L * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
    have hLpos : 0 < L := hL
    have hterm := norm_xiScrewDivisorTerm_le L q
    rw [abs_of_pos hLpos] at hterm
    change ‖Complex.exp (-s * (L : ℂ)) *
      ccmFirstClockScrewKernel L (xiSpectralPoint q)‖ ≤
        g L * (1 / ‖xiSpectralPoint q‖ ^ 2)
    rw [← xiScrewDivisorTerm_eq_ccmFirstClockScrewKernel,
      norm_mul, Complex.norm_exp]
    have hexpRe :
        (-s * (L : ℂ)).re = -s.re * L := by
      simp [mul_re]
    rw [hexpRe]
    calc
      Real.exp (-s.re * L) * ‖xiScrewDivisorTerm L q‖ ≤
          Real.exp (-s.re * L) *
            ((Real.exp (L / 2) + 1) / ‖xiSpectralPoint q‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hterm (Real.exp_pos _).le
      _ = g L * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        dsimp only [g]
        rw [show (-s.re + 1 / 2) * L =
          -s.re * L + L / 2 by ring]
        rw [Real.exp_add]
        ring
  have hnormSummable : Summable (fun q : XiZeroCopy =>
      ∫ L : ℝ in Ioi 0, ‖F q L‖) := by
    apply Summable.of_nonneg_of_le
      (fun q => integral_nonneg fun _ => norm_nonneg _)
      (fun q => ?_)
      (xiSpectralPoint_inv_sq_summable.mul_left
        (∫ L : ℝ in Ioi 0, g L))
    have hmajorInt :
        IntegrableOn
          (fun L : ℝ => g L * (1 / ‖xiSpectralPoint q‖ ^ 2)) (Ioi 0) :=
      hgint.mul_const _
    calc
      (∫ L : ℝ in Ioi 0, ‖F q L‖) ≤
          ∫ L : ℝ in Ioi 0,
            g L * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        apply integral_mono_ae (hFint q).norm hmajorInt
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
        exact hpointBound q L hL
      _ = (∫ L : ℝ in Ioi 0, g L) *
          (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        rw [integral_mul_const]
  have hswap :
      (∫ L : ℝ in Ioi 0, ∑' q : XiZeroCopy, F q L) =
        ∑' q : XiZeroCopy, ∫ L : ℝ in Ioi 0, F q L :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm
      hFint hnormSummable).symm
  have hpoint (L : ℝ) :
      (∑' q : XiZeroCopy, F q L) =
        Complex.exp (-s * (L : ℂ)) * xiScrewDivisor L := by
    rw [xiScrewDivisor, ← tsum_mul_left]
    apply tsum_congr
    intro q
    dsimp only [F]
    rw [xiScrewDivisorTerm_eq_ccmFirstClockScrewKernel]
  calc
    (∫ L : ℝ in Ioi 0,
        Complex.exp (-s * (L : ℂ)) * xiScrewDivisor L) =
        ∫ L : ℝ in Ioi 0, ∑' q : XiZeroCopy, F q L := by
      apply integral_congr_ae
      filter_upwards with L
      exact (hpoint L).symm
    _ = ∑' q : XiZeroCopy, ∫ L : ℝ in Ioi 0, F q L := hswap
    _ = ∑' q : XiZeroCopy,
        1 / (s * (s ^ 2 + xiSpectralPoint q ^ 2)) := by
      apply tsum_congr
      intro q
      have hzstrip : |(xiSpectralPoint q).im| < 1 / 2 := by
        rw [abs_lt]
        constructor <;> linarith [xiSpectralPoint_im_mem_openHalf q]
      exact integral_exp_mul_ccmFirstClockScrewKernel
        (xiSpectralPoint_ne_zero q) hzstrip hsHalf
    _ = I / s ^ 2 * logDeriv XiC (I * s) :=
      tsum_screwLaplace_eq_logDeriv_XiC hsHalf

/-- Every centered Xi zero is a simple pole of its logarithmic derivative, independently of
the zero multiplicity.  This is the local obstruction detected by an analytic CCM continuation. -/
theorem meromorphicOrderAt_logDeriv_XiC_eq_neg_one
    {ρ : ℂ} (hzero : XiC ρ = 0) :
    meromorphicOrderAt (logDeriv XiC) ρ = ((-1 : ℤ) : WithTop ℤ) := by
  have hXi : AnalyticAt ℂ XiC ρ := XiC_analytic ρ (Set.mem_univ ρ)
  have hmne : (analyticOrderAt XiC ρ).toNat ≠ 0 := by
    intro h0
    have horder0 : analyticOrderAt XiC ρ = 0 := by
      rw [(ENat.coe_toNat (XiC_order_ne_top ρ)).symm, h0]
      rfl
    rcases analyticOrderAt_eq_zero.mp horder0 with h | h
    · exact h hXi
    · exact h hzero
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmne
  have horder : analyticOrderAt XiC ρ = (k + 1 : ℕ) := by
    calc
      analyticOrderAt XiC ρ = ((analyticOrderAt XiC ρ).toNat : ℕ∞) :=
        (ENat.coe_toNat (XiC_order_ne_top ρ)).symm
      _ = (k + 1 : ℕ) := by rw [hk, Nat.succ_eq_add_one]
  have hderiv : analyticOrderAt (deriv XiC) ρ = k :=
    analyticOrderAt_deriv_of_pos hXi horder
  rw [show logDeriv XiC = deriv XiC / XiC by
    funext z
    rw [logDeriv_apply]
    rfl]
  rw [meromorphicOrderAt_div hXi.deriv.meromorphicAt hXi.meromorphicAt,
    hXi.deriv.meromorphicOrderAt_eq, hXi.meromorphicOrderAt_eq,
    hderiv, horder, ENat.map_coe, ENat.map_coe]
  exact_mod_cast (show (k : ℤ) - ((k + 1 : ℕ) : ℤ) = -1 by omega)

/-- A punctured-neighborhood identification of the centered Xi logarithmic derivative with an
analytic germ excludes a zero at the center. -/
theorem XiC_ne_zero_of_logDeriv_eventuallyEq_analytic
    {A : ℂ → ℂ} {ρ : ℂ} (hA : AnalyticAt ℂ A ρ)
    (heq : logDeriv XiC =ᶠ[𝓝[≠] ρ] A) :
    XiC ρ ≠ 0 := by
  intro hzero
  have horder := meromorphicOrderAt_logDeriv_XiC_eq_neg_one hzero
  have hcongr := meromorphicOrderAt_congr heq
  have hnonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt (logDeriv XiC) ρ := by
    rw [hcongr]
    exact hA.meromorphicOrderAt_nonneg
  rw [horder] at hnonneg
  exact (show ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) by
    exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)) hnonneg

/-- The centered upper half-plane on which a completed CCM Laplace transform must continue. -/
def ccmXiUpperHalfPlane : Set ℂ := {z : ℂ | 0 < z.im}

theorem isOpen_ccmXiUpperHalfPlane : IsOpen ccmXiUpperHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_im

/-- **Upper-extension completeness law.**  Any analytic continuation of the centered Xi
logarithmic derivative to the whole upper half-plane, agreeing on the unconditional initial
half-plane, proves RH.  The proof is branch-free: the analytic differential identity
`XiC' = A * XiC` propagates by connectedness, while the exact order `-1` at every Xi zero
prevents the continued coefficient `A` from crossing any upper-half-plane zero. -/
theorem riemannHypothesis_of_upper_logDeriv_extension
    (A : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ A ccmXiUpperHalfPlane)
    (hagree : ∀ w : ℂ, 1 / 2 < w.im → A w = logDeriv XiC w) :
    RiemannHypothesis := by
  have hUopen : IsOpen ccmXiUpperHalfPlane :=
    isOpen_ccmXiUpperHalfPlane
  have hUpre : IsPreconnected ccmXiUpperHalfPlane := by
    exact (convex_halfSpace_im_gt 0).isPreconnected
  let H : ℂ → ℂ := fun w => deriv XiC w - A w * XiC w
  have hHan : AnalyticOnNhd ℂ H ccmXiUpperHalfPlane := by
    intro w hw
    exact (XiC_analytic w (Set.mem_univ w)).deriv.sub
      ((hA w hw).mul (XiC_analytic w (Set.mem_univ w)))
  have hIUpper : I ∈ ccmXiUpperHalfPlane := by
    simp [ccmXiUpperHalfPlane]
  have hHev : H =ᶠ[𝓝 I] 0 := by
    have hhigh : {w : ℂ | 1 / 2 < w.im} ∈ 𝓝 I := by
      apply (isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      norm_num
    filter_upwards [hhigh] with w hw
    have hXi : XiC w ≠ 0 := by
      intro hzero
      have hstrip := xiC_zero_im_mem_openHalf hzero
      linarith
    have hag := hagree w hw
    dsimp only [H]
    rw [hag, logDeriv_apply]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ hXi).symm
  have hHzero : EqOn H 0 ccmXiUpperHalfPlane :=
    hHan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hUpre hIUpper hHev
  have hnozero : ∀ {z : ℂ}, z ∈ ccmXiUpperHalfPlane → XiC z ≠ 0 := by
    intro z hzU hzero
    have hXiNe : ∀ᶠ w in 𝓝[≠] z, XiC w ≠ 0 :=
      (XiC_analytic z
        (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
          (fun hlocal =>
            XiC_order_ne_top z (analyticOrderAt_eq_top.mpr hlocal))
    have hUevent : ∀ᶠ w in 𝓝[≠] z, w ∈ ccmXiUpperHalfPlane :=
      Filter.Eventually.filter_mono inf_le_left (hUopen.mem_nhds hzU)
    apply XiC_ne_zero_of_logDeriv_eventuallyEq_analytic (hA z hzU) ?_ hzero
    filter_upwards [hXiNe, hUevent] with w hwXi hwU
    rw [logDeriv_apply]
    apply (div_eq_iff hwXi).2
    exact sub_eq_zero.mp (hHzero hwU)
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  let z : ℂ := xiSpectralPoint q
  have hz0 : XiC z = 0 := XiC_xiSpectralPoint_eq_zero q
  have hnotpos : ¬ 0 < z.im := by
    intro hzpos
    exact hnozero (show z ∈ ccmXiUpperHalfPlane by exact hzpos) hz0
  have hnotneg : ¬ z.im < 0 := by
    intro hzneg
    have hnegUpper : -z ∈ ccmXiUpperHalfPlane := by
      change 0 < (-z).im
      simp only [neg_im]
      linarith
    have hnegZero : XiC (-z) = 0 := by rw [XiC_even, hz0]
    exact hnozero hnegUpper hnegZero
  have hzim : z.im = 0 :=
    le_antisymm (le_of_not_gt hnotpos) (not_lt.mp hnotneg)
  refine ⟨z.re, ?_⟩
  change z = (z.re : ℂ)
  apply Complex.ext
  · rfl
  · simpa using hzim

/-- The complete Xi screw has every positive exponential moment.  This is the exact output needed
from first-clock Landau propagation and Volterra reflection; no pointwise growth estimate is
built into the condition. -/
def CCMXiScrewAllExponentialMoments : Prop :=
  ∀ a : ℝ, 0 < a →
    IntegrableOn (fun L : ℝ =>
      Complex.exp (-(a : ℂ) * (L : ℂ)) * xiScrewDivisor L) (Ioi 0)

/-- The complete CCM screw Laplace transform. -/
def ccmXiScrewLaplace (s : ℂ) : ℂ :=
  ∫ L : ℝ in Ioi 0,
    Complex.exp (-s * (L : ℂ)) * xiScrewDivisor L

/-- Real exponential moments control the complex Laplace integrand throughout the corresponding
right half-plane: the imaginary part is a unit-modulus phase. -/
theorem integrableOn_exp_complex_mul_xiScrewDivisor
    (hMom : CCMXiScrewAllExponentialMoments)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun L : ℝ =>
      Complex.exp (-s * (L : ℂ)) * xiScrewDivisor L) (Ioi 0) := by
  let B : ℝ → ℂ := fun L =>
    Complex.exp (-(s.re : ℂ) * (L : ℂ)) * xiScrewDivisor L
  let P : ℝ → ℂ := fun L =>
    Complex.exp (-(s.im : ℂ) * I * (L : ℂ))
  have hB : IntegrableOn B (Ioi 0) := hMom s.re hs
  have hPmeas : AEStronglyMeasurable P (volume.restrict (Ioi 0)) := by
    exact (by fun_prop : Continuous P).aestronglyMeasurable
  have hPnorm : ∀ᵐ L : ℝ ∂volume.restrict (Ioi 0), ‖P L‖ ≤ 1 := by
    filter_upwards with L
    dsimp only [P]
    rw [show -(s.im : ℂ) * I * (L : ℂ) =
        (-(s.im * L) : ℝ) * I by
      push_cast
      ring]
    rw [Complex.norm_exp_ofReal_mul_I]
  have hPB : Integrable (fun L => P L * B L)
      (volume.restrict (Ioi 0)) := by
    exact hB.bdd_mul hPmeas hPnorm
  apply hPB.congr
  filter_upwards with L
  dsimp only [P, B]
  rw [← mul_assoc, ← Complex.exp_add]
  have harg :
      -(s.im : ℂ) * I * (L : ℂ) + -(s.re : ℂ) * (L : ℂ) =
        -s * (L : ℂ) := by
    calc
      -(s.im : ℂ) * I * (L : ℂ) + -(s.re : ℂ) * (L : ℂ) =
          -((s.re : ℂ) + (s.im : ℂ) * I) * (L : ℂ) := by ring
      _ = -s * (L : ℂ) := by rw [Complex.re_add_im]
  rw [harg]

/-- The all-moment condition differentiates the CCM screw transform at every point of `Re s > 0`.
One weaker exponential moment absorbs the derivative factor `L`; no numerical bound is used. -/
theorem hasDerivAt_ccmXiScrewLaplace
    (hMom : CCMXiScrewAllExponentialMoments)
    {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    HasDerivAt ccmXiScrewLaplace
      (∫ L : ℝ in Ioi 0,
        (-(L : ℂ)) * Complex.exp (-s₀ * (L : ℂ)) *
          xiScrewDivisor L) s₀ := by
  let δ : ℝ := s₀.re / 4
  let a : ℝ := s₀.re / 2
  let F : ℂ → ℝ → ℂ := fun s L =>
    Complex.exp (-s * (L : ℂ)) * xiScrewDivisor L
  let F' : ℂ → ℝ → ℂ := fun s L =>
    (-(L : ℂ)) * Complex.exp (-s * (L : ℂ)) * xiScrewDivisor L
  let B : ℝ → ℂ := fun L =>
    Complex.exp (-(a : ℂ) * (L : ℂ)) * xiScrewDivisor L
  let bound : ℝ → ℝ := fun L => δ⁻¹ * ‖B L‖
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have ha : 0 < a := by dsimp [a]; linarith
  have hball : Metric.ball s₀ δ ∈ 𝓝 s₀ :=
    Metric.ball_mem_nhds _ hδ
  have hFint : Integrable (F s₀) (volume.restrict (Ioi 0)) :=
    integrableOn_exp_complex_mul_xiScrewDivisor hMom hs₀
  have hFmeas : ∀ᶠ s in 𝓝 s₀,
      AEStronglyMeasurable (F s) (volume.restrict (Ioi 0)) := by
    filter_upwards [hball] with s hsball
    have hdist : ‖s - s₀‖ < δ := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hsball
    have hreDiff : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (s - s₀)
    have hsre : 0 < s.re := by
      have habs : |s.re - s₀.re| < s₀.re / 4 :=
        lt_of_le_of_lt hreDiff hdist
      dsimp only [δ] at hdist
      linarith [neg_le_abs (s.re - s₀.re)]
    exact (integrableOn_exp_complex_mul_xiScrewDivisor hMom hsre).1
  have hF'meas : AEStronglyMeasurable (F' s₀)
      (volume.restrict (Ioi 0)) := by
    have hlinear : AEStronglyMeasurable (fun L : ℝ => -(L : ℂ))
        (volume.restrict (Ioi 0)) :=
      (by fun_prop :
        Continuous (fun L : ℝ => -(L : ℂ))).aestronglyMeasurable
    have hbase : AEStronglyMeasurable (F s₀)
        (volume.restrict (Ioi 0)) := hFint.1
    exact (hlinear.mul hbase).congr
      (Eventually.of_forall fun L => by
        dsimp only [F', F, Pi.mul_apply]
        ring)
  have hBint : Integrable B (volume.restrict (Ioi 0)) := hMom a ha
  have hboundInt : Integrable bound (volume.restrict (Ioi 0)) := by
    exact hBint.norm.const_mul δ⁻¹
  have hbound : ∀ᵐ L : ℝ ∂volume.restrict (Ioi 0),
      ∀ s ∈ Metric.ball s₀ δ, ‖F' s L‖ ≤ bound L := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
    intro s hsball
    have hLpos : 0 < L := hL
    have hdist : ‖s - s₀‖ < δ := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hsball
    have hreDiff : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (s - s₀)
    have hsLower : a + δ < s.re := by
      dsimp only [a, δ] at hdist ⊢
      linarith [le_trans (neg_le_abs (s.re - s₀.re)) hreDiff]
    have hLabsorb := Real.le_inv_mul_exp L hδ
    have hscalar :
        L * Real.exp (-s.re * L) ≤ δ⁻¹ * Real.exp (-a * L) := by
      calc
        L * Real.exp (-s.re * L) ≤
            (δ⁻¹ * Real.exp (δ * L)) * Real.exp (-s.re * L) := by
          gcongr
        _ = δ⁻¹ * Real.exp ((δ - s.re) * L) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
        _ ≤ δ⁻¹ * Real.exp (-a * L) := by
          apply mul_le_mul_of_nonneg_left
          · apply Real.exp_le_exp.mpr
            nlinarith
          · exact inv_nonneg.mpr hδ.le
    dsimp only [F', bound, B]
    have hre1 : (-s * (L : ℂ)).re = -s.re * L := by
      simp [mul_re]
    have hre2 : (-(a : ℂ) * (L : ℂ)).re = -a * L := by
      simp [mul_re]
    simp only [norm_mul, norm_neg, norm_real, Complex.norm_exp, hre1, hre2]
    rw [Real.norm_eq_abs, abs_of_pos hLpos]
    calc
      L * Real.exp (-s.re * L) * ‖xiScrewDivisor L‖ ≤
          (δ⁻¹ * Real.exp (-a * L)) * ‖xiScrewDivisor L‖ :=
        mul_le_mul_of_nonneg_right hscalar
          (norm_nonneg (xiScrewDivisor L))
      _ = δ⁻¹ * (Real.exp (-a * L) * ‖xiScrewDivisor L‖) := by ring
  have hdiff : ∀ᵐ L : ℝ ∂volume.restrict (Ioi 0),
      ∀ s ∈ Metric.ball s₀ δ,
        HasDerivAt (fun s => F s L) (F' s L) s := by
    filter_upwards with L
    intro s hs
    have hexp : HasDerivAt
        (fun z : ℂ => Complex.exp (-z * (L : ℂ)))
        (-(L : ℂ) * Complex.exp (-s * (L : ℂ))) s := by
      simpa [mul_comm] using
        (((hasDerivAt_id s).neg.mul_const (L : ℂ)).cexp)
    simpa only [F, F', mul_assoc] using
      hexp.mul_const (xiScrewDivisor L)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := F) (F' := F')
    (x₀ := s₀) (s := Metric.ball s₀ δ) (bound := bound)
    hball hFmeas hFint hF'meas hbound hboundInt hdiff
  exact hmain.2.congr_of_eventuallyEq
    (Eventually.of_forall fun _ => rfl)

/-- All positive exponential moments make the full CCM screw Laplace transform analytic on the
entire right half-plane. -/
theorem analyticOnNhd_ccmXiScrewLaplace_rightHalf
    (hMom : CCMXiScrewAllExponentialMoments) :
    AnalyticOnNhd ℂ ccmXiScrewLaplace {s : ℂ | 0 < s.re} := by
  have hdiff : DifferentiableOn ℂ ccmXiScrewLaplace
      {s : ℂ | 0 < s.re} := by
    intro s hs
    exact (hasDerivAt_ccmXiScrewLaplace
      hMom hs).differentiableAt.differentiableWithinAt
  exact hdiff.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

/-- The upper-half-plane continuation reconstructed directly from the CCM screw transform. -/
def ccmXiLogDerivContinuation (w : ℂ) : ℂ :=
  I * w ^ 2 * ccmXiScrewLaplace (-I * w)

theorem analyticOnNhd_ccmXiLogDerivContinuation_upperHalf
    (hMom : CCMXiScrewAllExponentialMoments) :
    AnalyticOnNhd ℂ ccmXiLogDerivContinuation
      ccmXiUpperHalfPlane := by
  have hLap := analyticOnNhd_ccmXiScrewLaplace_rightHalf hMom
  intro w hw
  have hs : -I * w ∈ {s : ℂ | 0 < s.re} := by
    change 0 < (-I * w).re
    simp [mul_re]
    exact hw
  have hinner : AnalyticAt ℂ (fun z : ℂ => -I * z) w :=
    analyticAt_const.mul analyticAt_id
  have hcomp : AnalyticAt ℂ
      (fun z : ℂ => ccmXiScrewLaplace (-I * z)) w :=
    (hLap (-I * w) hs).comp hinner
  exact (analyticAt_const.mul (analyticAt_id.pow 2)).mul hcomp

/-- On the unconditional initial half-plane, the reconstructed continuation is exactly the
centered Xi logarithmic derivative. -/
theorem ccmXiLogDerivContinuation_eq_logDeriv
    {w : ℂ} (hw : 1 / 2 < w.im) :
    ccmXiLogDerivContinuation w = logDeriv XiC w := by
  have hs : 1 / 2 < (-I * w).re := by
    simpa [mul_re] using hw
  have hw0 : w ≠ 0 := by
    intro hzero
    rw [hzero, zero_im] at hw
    linarith
  rw [ccmXiLogDerivContinuation, ccmXiScrewLaplace,
    integral_exp_mul_xiScrewDivisor_eq_logDeriv_XiC hs]
  rw [show I * (-I * w) = w by
    rw [← mul_assoc, mul_neg, I_mul_I]
    ring]
  field_simp [hw0]

/-- **CCM all-moment completeness theorem.**  If the exact multiplicity-weighted CCM screw has
every positive exponential moment, then RH holds.  This converts a real-variable source statement
into global zero exclusion through the exact screw Laplace law and the upper-extension
completeness law. -/
theorem riemannHypothesis_of_ccmXiScrew_all_exponential_moments
    (hMom : CCMXiScrewAllExponentialMoments) :
    RiemannHypothesis :=
  riemannHypothesis_of_upper_logDeriv_extension
    ccmXiLogDerivContinuation
    (analyticOnNhd_ccmXiLogDerivContinuation_upperHalf hMom)
    (fun _w hw => ccmXiLogDerivContinuation_eq_logDeriv hw)

/-- Conjugating one first-clock rational atom is implemented exactly by the conjugate
divisor-copy equivalence. -/
theorem ccmFirstClockRationalKernel_copyConj
    (L : ℝ) (q : XiZeroCopy) :
    ccmFirstClockRationalKernel L
        (xiSpectralPoint (xiZeroCopyConjEquiv q)) =
      (starRingEnd ℂ)
        (ccmFirstClockRationalKernel L (xiSpectralPoint q)) := by
  rw [ccmFirstClockRationalKernel, ccmFirstClockRationalKernel,
    xiSpectralPoint_copyConj]
  rw [map_div₀, map_sub, map_one, map_sub]
  simp only [map_pow, Complex.conj_ofReal]
  congr 1
  · rw [mul_neg, Complex.cos_neg, ← Complex.cos_conj]
    congr 2
    simp
  · ring

/-- The complete first-clock rational divisor is real-valued at every aperture, without RH. -/
theorem star_ccmFirstClockXiRationalDivisor (L : ℝ) :
    (starRingEnd ℂ) (ccmFirstClockXiRationalDivisor L) =
      ccmFirstClockXiRationalDivisor L := by
  rw [ccmFirstClockXiRationalDivisor, Complex.conj_tsum]
  calc
    (∑' q : XiZeroCopy,
        (starRingEnd ℂ)
          (ccmFirstClockRationalKernel L (xiSpectralPoint q))) =
        ∑' q : XiZeroCopy,
          ccmFirstClockRationalKernel L
            (xiSpectralPoint (xiZeroCopyConjEquiv q)) := by
      apply tsum_congr
      intro q
      exact (ccmFirstClockRationalKernel_copyConj L q).symm
    _ = ∑' q : XiZeroCopy,
        ccmFirstClockRationalKernel L (xiSpectralPoint q) := by
      exact xiZeroCopyConjEquiv.tsum_eq
        (fun q : XiZeroCopy =>
          ccmFirstClockRationalKernel L (xiSpectralPoint q))

/-- Imaginary-part form of unconditional first-clock divisor reality. -/
theorem ccmFirstClockXiRationalDivisor_im_eq_zero (L : ℝ) :
    (ccmFirstClockXiRationalDivisor L).im = 0 :=
  Complex.conj_eq_iff_im.mp (star_ccmFirstClockXiRationalDivisor L)

end

end RHTower

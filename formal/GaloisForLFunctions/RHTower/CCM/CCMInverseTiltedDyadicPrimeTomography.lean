import GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowDivisorTomography
import GaloisForLFunctions.RHTower.RectangularWindowAmplitudeAnalytic
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# One inverse-tilted dyadic prime window sees the complete Xi divisor

The ordinary dyadic sharp window has Mellin multiplier `A_(log 2)(s - 1)`.  Its zero lattice
lies on `Re s = 1`, so it is ideal for detecting the off-critical divisor but can censor a
critical-line zero at an accidental dyadic resonance.

This file inserts the source-side weight `k / n` in the same finite interval `n / 2 < k <= n`.
The Mellin multiplier becomes `A_(log 2)(s)`, whose zero lattice lies on `Re s = 0`, strictly
outside the shifted nontrivial Xi divisor.  Consequently one source-defined scalar sequence
recovers the complete nontrivial Xi divisor, including the critical-line part and exact analytic
multiplicities.  No second window is required.
-/

open Complex Filter Function Finset Set LSeries Topology

namespace RHTower

noncomputable section

/-! ## The inverse-tilted source and its quadrature remainder -/

/-- Mellin multiplier of the inverse-tilted dyadic window `u^(-1) 1_[1,2](u)`.
It is exactly the rectangular amplitude `A_(log 2)(s)`. -/
def inverseTiltedDyadicMellin (s : ℂ) : ℂ :=
  sharpPrimeWindowMellin (Real.log 2) (s + 1)

theorem inverseTiltedDyadicMellin_eq_rectangularAmplitude (s : ℂ) :
    inverseTiltedDyadicMellin s =
      rectangularWindowAmplitude (Real.log 2) s := by
  simp only [inverseTiltedDyadicMellin, sharpPrimeWindowMellin]
  congr 1
  ring

theorem differentiable_inverseTiltedDyadicMellin :
    Differentiable ℂ inverseTiltedDyadicMellin := by
  unfold inverseTiltedDyadicMellin
  exact (sharpPrimeWindowMellin_differentiable (Real.log 2)).comp
    (differentiable_id.add_const 1)

/-- The inverse tilt moves the complete Mellin zero lattice to `Re s = 0`. -/
theorem inverseTiltedDyadicMellin_ne_zero_of_re_pos
    {s : ℂ} (hs : 0 < s.re) :
    inverseTiltedDyadicMellin s ≠ 0 := by
  rw [inverseTiltedDyadicMellin_eq_rectangularAmplitude]
  exact rectangularWindowAmplitude_ne_zero
    (Real.log_pos (by norm_num)) (by linarith)

/-- One inverse-tilted dyadic quadrature error term. -/
def inverseTiltedDyadicErrorSummand (s : ℂ) (k : ℕ) : ℂ :=
  (((ArithmeticFunction.vonMangoldt k / Real.sqrt k) * k : ℝ) : ℂ) *
    dyadicSharpPrimeWindowError k (s + 1)

/-- The inverse-tilted quadrature remainder. -/
def inverseTiltedDyadicErrorSeries (s : ℂ) : ℂ :=
  ∑' k : ℕ, inverseTiltedDyadicErrorSummand s k

theorem summable_inverseTiltedDyadicErrorSummand
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (inverseTiltedDyadicErrorSummand s) := by
  let z : ℂ := ((s.re + 1 / 2 : ℝ) : ℂ)
  have hz : 1 < z.re := by
    dsimp only [z]
    simp only [ofReal_re]
    linarith
  have hvm : LSeriesSummable
      (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) z :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hz
  have hdom : Summable (fun k => ‖s + 1‖ *
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z k‖) :=
    hvm.norm.mul_left ‖s + 1‖
  apply Summable.of_norm_bounded hdom
  intro k
  rcases k.eq_zero_or_pos with rfl | hk
  · simp [inverseTiltedDyadicErrorSummand,
      dyadicSharpPrimeWindowError, dyadicSharpPrimeWindowKernel,
      dyadicSharpPrimeWindowIntegralMain]
  · have hk1 : 1 ≤ k := hk
    have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
    have herr := norm_dyadicSharpPrimeWindowError_le hk1
      (s := s + 1) (by simp only [add_re, one_re]; linarith)
    rw [inverseTiltedDyadicErrorSummand, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg k))
        (Nat.cast_nonneg k))]
    calc
      (ArithmeticFunction.vonMangoldt k / Real.sqrt k * k) *
          ‖dyadicSharpPrimeWindowError k (s + 1)‖ ≤
        (ArithmeticFunction.vonMangoldt k / Real.sqrt k * k) *
          (‖s + 1‖ * (k : ℝ) ^ (-(s + 1).re)) := by
            exact mul_le_mul_of_nonneg_left herr
              (mul_nonneg
                (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
                  (Real.sqrt_nonneg k))
                (Nat.cast_nonneg k))
      _ = ‖s + 1‖ * ‖LSeries.term
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z k‖ := by
        rw [LSeries.term_of_ne_zero hk0, norm_div, norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Complex.norm_natCast_cpow_of_pos hk]
        simp only [z, ofReal_re, add_re, one_re]
        rw [Real.sqrt_eq_rpow]
        rw [show (ArithmeticFunction.vonMangoldt k /
              (k : ℝ) ^ (1 / 2 : ℝ) * k) *
              (‖s + 1‖ * (k : ℝ) ^ (-(s.re + 1))) =
            ‖s + 1‖ * ArithmeticFunction.vonMangoldt k *
              ((k : ℝ) ^ (-(1 / 2 : ℝ)) *
                ((k : ℝ) ^ (1 : ℝ) *
                  (k : ℝ) ^ (-(s.re + 1)))) by
              rw [div_eq_mul_inv, ← Real.rpow_neg hkreal.le, Real.rpow_one]
              ring]
        rw [← Real.rpow_add hkreal, ← Real.rpow_add hkreal]
        rw [show -(1 / 2 : ℝ) + (1 + -(s.re + 1)) =
            -(s.re + 1 / 2) by ring,
          Real.rpow_neg hkreal.le]
        field_simp

theorem differentiable_inverseTiltedDyadicErrorSummand (k : ℕ) :
    Differentiable ℂ (fun s => inverseTiltedDyadicErrorSummand s k) := by
  unfold inverseTiltedDyadicErrorSummand
  exact (differentiable_const
    ((((ArithmeticFunction.vonMangoldt k / Real.sqrt k) * k : ℝ) : ℂ))).mul
      ((differentiable_dyadicSharpPrimeWindowError k).comp
        (differentiable_id.add_const 1))

theorem summableLocallyUniformlyOn_inverseTiltedDyadicErrorSummand :
    SummableLocallyUniformlyOn
      (fun k : ℕ => fun s : ℂ => inverseTiltedDyadicErrorSummand s k)
      {s : ℂ | 1 / 2 < s.re} := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro s hs
  change 1 / 2 < s.re at hs
  let r : ℝ := (s.re - 1 / 2) / 2
  let sigma : ℝ := s.re - r
  let R : ℝ := ‖s + 1‖ + r
  have hr : 0 < r := by
    dsimp only [r]
    linarith
  have hsigma : 1 / 2 < sigma := by
    dsimp only [sigma, r]
    linarith
  let z : ℂ := ((sigma + 1 / 2 : ℝ) : ℂ)
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hz : 1 < z.re := by
    dsimp only [z]
    simp only [ofReal_re]
    linarith
  have hvm : LSeriesSummable
      (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) z :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hz
  have hmajor : Summable (fun k => R *
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z k‖) :=
    hvm.norm.mul_left R
  refine ⟨Metric.ball s r,
    mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self hr)), ?_⟩
  apply HasSumUniformlyOn.of_norm_le_summable hmajor
  intro k x hx
  have hxball : ‖x - s‖ < r := by
    simpa [dist_eq_norm] using Metric.mem_ball.mp hx
  have hxre : sigma < x.re := by
    have hre := Complex.abs_re_le_norm (x - s)
    rw [Complex.sub_re] at hre
    have hreLower := (abs_le.mp hre).1
    dsimp only [sigma]
    linarith
  have hxnorm : ‖x + 1‖ ≤ R := by
    dsimp only [R]
    calc
      ‖x + 1‖ ≤ ‖x - s‖ + ‖s + 1‖ := by
        calc
          ‖x + 1‖ = ‖(x - s) + (s + 1)‖ := by ring_nf
          _ ≤ ‖x - s‖ + ‖s + 1‖ := norm_add_le _ _
      _ ≤ ‖s + 1‖ + r := by linarith
  rcases k.eq_zero_or_pos with rfl | hk
  · simp [inverseTiltedDyadicErrorSummand,
      dyadicSharpPrimeWindowError, dyadicSharpPrimeWindowKernel,
      dyadicSharpPrimeWindowIntegralMain]
  · have hk1 : 1 ≤ k := hk
    have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
    have herr := norm_dyadicSharpPrimeWindowError_le hk1
      (s := x + 1) (by simp only [add_re, one_re]; linarith)
    rw [inverseTiltedDyadicErrorSummand, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg k))
        (Nat.cast_nonneg k))]
    calc
      (ArithmeticFunction.vonMangoldt k / Real.sqrt k * k) *
          ‖dyadicSharpPrimeWindowError k (x + 1)‖ ≤
        (ArithmeticFunction.vonMangoldt k / Real.sqrt k * k) *
          (‖x + 1‖ * (k : ℝ) ^ (-(x + 1).re)) := by
            exact mul_le_mul_of_nonneg_left herr
              (mul_nonneg
                (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
                  (Real.sqrt_nonneg k))
                (Nat.cast_nonneg k))
      _ ≤ (ArithmeticFunction.vonMangoldt k / Real.sqrt k * k) *
          (R * (k : ℝ) ^ (-(sigma + 1))) := by
        apply mul_le_mul_of_nonneg_left
        · calc
            ‖x + 1‖ * (k : ℝ) ^ (-(x + 1).re) ≤
                R * (k : ℝ) ^ (-(x + 1).re) :=
              mul_le_mul_of_nonneg_right hxnorm
                (Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le k)) _)
            _ ≤ R * (k : ℝ) ^ (-(sigma + 1)) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le
                  (by exact_mod_cast hk1) (by
                    simp only [add_re, one_re]
                    linarith)) hR0
        · exact mul_nonneg
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
              (Real.sqrt_nonneg k))
            (Nat.cast_nonneg k)
      _ = R * ‖LSeries.term
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z k‖ := by
        rw [LSeries.term_of_ne_zero hk0, norm_div, norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Complex.norm_natCast_cpow_of_pos hk]
        simp only [z, ofReal_re]
        rw [Real.sqrt_eq_rpow]
        rw [show (ArithmeticFunction.vonMangoldt k /
              (k : ℝ) ^ (1 / 2 : ℝ) * k) *
              (R * (k : ℝ) ^ (-(sigma + 1))) =
            R * ArithmeticFunction.vonMangoldt k *
              ((k : ℝ) ^ (-(1 / 2 : ℝ)) *
                ((k : ℝ) ^ (1 : ℝ) *
                  (k : ℝ) ^ (-(sigma + 1)))) by
              rw [div_eq_mul_inv, ← Real.rpow_neg hkreal.le, Real.rpow_one]
              ring]
        rw [← Real.rpow_add hkreal, ← Real.rpow_add hkreal]
        rw [show -(1 / 2 : ℝ) + (1 + -(sigma + 1)) =
            -(sigma + 1 / 2) by ring,
          Real.rpow_neg hkreal.le]
        field_simp

theorem differentiableOn_inverseTiltedDyadicErrorSeries_rightHalf :
    DifferentiableOn ℂ inverseTiltedDyadicErrorSeries
      {s : ℂ | 1 / 2 < s.re} := by
  apply SummableLocallyUniformlyOn.differentiableOn
    (isOpen_lt continuous_const Complex.continuous_re)
    summableLocallyUniformlyOn_inverseTiltedDyadicErrorSummand
  intro k s _hs
  exact differentiable_inverseTiltedDyadicErrorSummand k s

/-! ## Canonical pole-filled continuation -/

/-- Entire numerator encoding cancellation of the shifted zeta pole. -/
def inverseTiltedDyadicPoleNumerator (s : ℂ) : ℂ :=
  2 * inverseTiltedDyadicMellin (3 / 2) *
      regularizedRiemannZeta (s - 1 / 2) -
    2 * inverseTiltedDyadicMellin s

/-- Canonical continuation of the inverse-tilted dyadic prime-polar source. -/
def inverseTiltedDyadicContinuedSource (s : ℂ) : ℂ :=
  dslope inverseTiltedDyadicPoleNumerator (3 / 2) s +
    2 * inverseTiltedDyadicMellin s *
      logDeriv regularizedRiemannZeta (s - 1 / 2) -
    2 * inverseTiltedDyadicErrorSeries s

theorem differentiable_inverseTiltedDyadicPoleNumerator :
    Differentiable ℂ inverseTiltedDyadicPoleNumerator := by
  unfold inverseTiltedDyadicPoleNumerator
  exact ((differentiable_regularizedRiemannZeta.comp
      (differentiable_id.sub_const (1 / 2))).const_mul
        (2 * inverseTiltedDyadicMellin (3 / 2))).sub
    (differentiable_inverseTiltedDyadicMellin.const_mul 2)

@[simp] theorem inverseTiltedDyadicPoleNumerator_three_halves :
    inverseTiltedDyadicPoleNumerator (3 / 2) = 0 := by
  rw [inverseTiltedDyadicPoleNumerator]
  norm_num [regularizedRiemannZeta_one]

theorem differentiable_inverseTiltedDyadicPoleDividedDifference :
    Differentiable ℂ
      (dslope inverseTiltedDyadicPoleNumerator (3 / 2)) := by
  rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
  exact differentiable_inverseTiltedDyadicPoleNumerator.differentiableOn

theorem meromorphicOn_inverseTiltedDyadicContinuedSource_rightHalf :
    MeromorphicOn inverseTiltedDyadicContinuedSource
      {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  let U : Set ℂ := {z : ℂ | 1 / 2 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hdiv : AnalyticAt ℂ
      (dslope inverseTiltedDyadicPoleNumerator (3 / 2)) s :=
    (differentiable_inverseTiltedDyadicPoleDividedDifference.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hM : AnalyticAt ℂ inverseTiltedDyadicMellin s :=
    (differentiable_inverseTiltedDyadicMellin.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hshift : AnalyticAt ℂ (fun z : ℂ => z - 1 / 2) s := by fun_prop
  have hlog : MeromorphicAt
      (fun z : ℂ => logDeriv regularizedRiemannZeta (z - 1 / 2)) s :=
    MeromorphicAt.comp_analyticAt
      (meromorphicAt_logDeriv_regularizedRiemannZeta (s - 1 / 2)) hshift
  have herr : AnalyticAt ℂ inverseTiltedDyadicErrorSeries s :=
    (differentiableOn_inverseTiltedDyadicErrorSeries_rightHalf.analyticOnNhd
      hUopen) s hs
  exact (hdiv.meromorphicAt.add
    ((analyticAt_const.mul hM).meromorphicAt.mul hlog)).sub
      (analyticAt_const.mul herr).meromorphicAt

theorem analyticAt_inverseTiltedDyadicContinuedSource_of_regularizedZeta_ne_zero
    {s : ℂ} (hs : 1 / 2 < s.re)
    (hz : regularizedRiemannZeta (s - 1 / 2) ≠ 0) :
    AnalyticAt ℂ inverseTiltedDyadicContinuedSource s := by
  let U : Set ℂ := {z : ℂ | 1 / 2 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hdiv : AnalyticAt ℂ
      (dslope inverseTiltedDyadicPoleNumerator (3 / 2)) s :=
    (differentiable_inverseTiltedDyadicPoleDividedDifference.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hM : AnalyticAt ℂ inverseTiltedDyadicMellin s :=
    (differentiable_inverseTiltedDyadicMellin.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hreg : AnalyticAt ℂ regularizedRiemannZeta (s - 1 / 2) :=
    (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
      isOpen_univ) (s - 1 / 2) (Set.mem_univ _)
  have hlog : AnalyticAt ℂ
      (fun z : ℂ => logDeriv regularizedRiemannZeta (z - 1 / 2)) s := by
    rw [show (fun z : ℂ => logDeriv regularizedRiemannZeta (z - 1 / 2)) =
        fun z : ℂ => deriv regularizedRiemannZeta (z - 1 / 2) /
          regularizedRiemannZeta (z - 1 / 2) by
      funext z
      rw [logDeriv_apply]]
    have hshift : AnalyticAt ℂ (fun z : ℂ => z - 1 / 2) s := by fun_prop
    have hnum := AnalyticAt.comp (f := fun z : ℂ => z - 1 / 2) (x := s)
      hreg.deriv hshift
    have hden := AnalyticAt.comp (f := fun z : ℂ => z - 1 / 2) (x := s)
      hreg hshift
    refine (hnum.div hden hz).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.div_apply, Function.comp_apply]
  have herr : AnalyticAt ℂ inverseTiltedDyadicErrorSeries s :=
    (differentiableOn_inverseTiltedDyadicErrorSeries_rightHalf.analyticOnNhd
      hUopen) s hs
  exact (hdiv.add ((analyticAt_const.mul hM).mul hlog)).sub
    (analyticAt_const.mul herr)

/-! ## Exact ordinary Dirichlet-series source -/

/-- The finite inverse-tilted dyadic von-Mangoldt window. -/
def inverseTiltedDyadicWeightedPrimeWindow (n : ℕ) : ℝ :=
  ∑ k ∈ Ioc (n / 2) n,
    (ArithmeticFunction.vonMangoldt k / Real.sqrt k) * (k / n : ℝ)

/-- One term before regrouping the inverse-tilted moving-window sum. -/
def inverseTiltedDyadicDoubleTerm (s : ℂ) (kj : ℕ × ℕ) : ℂ :=
  if kj.2 < kj.1 then
    (((ArithmeticFunction.vonMangoldt kj.1 / Real.sqrt kj.1) * kj.1 : ℝ) : ℂ) *
      (((kj.1 + kj.2 : ℕ) : ℂ) ^ (-(s + 1)))
  else 0

private theorem summable_norm_inverseTiltedDyadicDoubleTerm
    {s : ℂ} (hs : 3 / 2 < s.re) :
    Summable (fun kj : ℕ × ℕ => ‖inverseTiltedDyadicDoubleTerm s kj‖) := by
  rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
  constructor
  · intro k
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (Finset.finite_toSet (range k))
    intro j hj
    simp only [Function.mem_support] at hj
    simp only [mem_coe, Finset.mem_range]
    by_contra hnot
    simp only [inverseTiltedDyadicDoubleTerm,
      if_neg hnot, norm_zero] at hj
    exact hj rfl
  · let z : ℂ := ((s.re - 1 / 2 : ℝ) : ℂ)
    have hz : 1 < z.re := by
      dsimp only [z]
      simp only [ofReal_re]
      linarith
    have hvm : LSeriesSummable
        (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) z :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt hz
    apply Summable.of_norm_bounded hvm.norm
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
    rcases k.eq_zero_or_pos with rfl | hk
    · simp [inverseTiltedDyadicDoubleTerm]
    · have hk0 : k ≠ 0 := Nat.ne_of_gt hk
      have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
      rw [tsum_eq_sum (s := range k) (fun j hj => by
        simp only [Finset.mem_range] at hj
        simp only [inverseTiltedDyadicDoubleTerm,
          if_neg hj, norm_zero])]
      calc
        (∑ j ∈ range k, ‖inverseTiltedDyadicDoubleTerm s (k, j)‖) ≤
            ∑ _j ∈ range k,
              (ArithmeticFunction.vonMangoldt k / Real.sqrt k * k) *
                (k : ℝ) ^ (-(s.re + 1)) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjk : j < k := mem_range.mp hj
          have hkjpos : 0 < k + j := by omega
          have hkle : (k : ℝ) ≤ ((k + j : ℕ) : ℝ) := by
            exact_mod_cast (show k ≤ k + j by omega)
          rw [inverseTiltedDyadicDoubleTerm, if_pos hjk,
            norm_mul, norm_real, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg
              (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
                (Real.sqrt_nonneg k)) (Nat.cast_nonneg k)),
            Complex.norm_natCast_cpow_of_pos hkjpos]
          simp only [neg_re, add_re, one_re]
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg
              (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
                (Real.sqrt_nonneg k)) (Nat.cast_nonneg k))
          exact Real.rpow_le_rpow_of_nonpos hkreal hkle (by linarith)
        _ = (ArithmeticFunction.vonMangoldt k / Real.sqrt k * k) *
              ((k : ℝ) * (k : ℝ) ^ (-(s.re + 1))) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          ring
        _ = ‖LSeries.term
              (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z k‖ := by
          rw [LSeries.term_of_ne_zero hk0, norm_div, norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
            Complex.norm_natCast_cpow_of_pos hk]
          simp only [z, ofReal_re]
          rw [Real.sqrt_eq_rpow]
          calc
            (ArithmeticFunction.vonMangoldt k /
                (k : ℝ) ^ (1 / 2 : ℝ) * k) *
                ((k : ℝ) * (k : ℝ) ^ (-(s.re + 1))) =
              ArithmeticFunction.vonMangoldt k *
                ((k : ℝ) ^ (-(1 / 2 : ℝ)) *
                  ((k : ℝ) ^ (1 : ℝ) *
                    ((k : ℝ) ^ (1 : ℝ) *
                      (k : ℝ) ^ (-(s.re + 1))))) := by
                rw [div_eq_mul_inv, ← Real.rpow_neg hkreal.le,
                  Real.rpow_one]
                ring
            _ = ArithmeticFunction.vonMangoldt k *
                (k : ℝ) ^ (-(1 / 2 : ℝ) + (1 + (1 + -(s.re + 1)))) := by
              rw [← Real.rpow_add hkreal, ← Real.rpow_add hkreal,
                ← Real.rpow_add hkreal]
            _ = ArithmeticFunction.vonMangoldt k /
                (k : ℝ) ^ (s.re - 1 / 2) := by
              rw [show -(1 / 2 : ℝ) + (1 + (1 + -(s.re + 1))) =
                  -(s.re - 1 / 2) by ring,
                Real.rpow_neg hkreal.le]
              ring

theorem summable_inverseTiltedDyadicDoubleTerm
    {s : ℂ} (hs : 3 / 2 < s.re) :
    Summable (inverseTiltedDyadicDoubleTerm s) :=
  (summable_norm_inverseTiltedDyadicDoubleTerm hs).of_norm

theorem tsum_inverseTiltedDyadicDoubleTerm_right
    (k : ℕ) (s : ℂ) :
    (∑' j : ℕ, inverseTiltedDyadicDoubleTerm s (k, j)) =
      ((((ArithmeticFunction.vonMangoldt k / Real.sqrt k) * k : ℝ) : ℂ)) *
        dyadicSharpPrimeWindowKernel k (s + 1) := by
  rw [tsum_eq_sum (s := range k) (fun j hj => by
    simp only [Finset.mem_range] at hj
    simp only [inverseTiltedDyadicDoubleTerm, if_neg hj])]
  rw [dyadicSharpPrimeWindowKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [inverseTiltedDyadicDoubleTerm,
    if_pos (Finset.mem_range.mp hj)]

private theorem antidiagonal_inverseTiltedDoubleTerm_eq_LSeriesTerm_window
    (s : ℂ) (n : ℕ) :
    (∑' p : ↥(Finset.HasAntidiagonal.antidiagonal n),
        inverseTiltedDyadicDoubleTerm s p.1) =
      LSeries.term
        (fun m => ((inverseTiltedDyadicWeightedPrimeWindow m : ℝ) : ℂ)) s n := by
  rw [tsum_fintype]
  rw [← Finset.sum_subtype (Finset.HasAntidiagonal.antidiagonal n) (fun _ => Iff.rfl)
    (fun p => inverseTiltedDyadicDoubleTerm s p)]
  change (∑ a ∈ Finset.HasAntidiagonal.antidiagonal n,
    inverseTiltedDyadicDoubleTerm s (a.1, a.2)) = _
  rw [show (∑ a ∈ Finset.HasAntidiagonal.antidiagonal n,
      inverseTiltedDyadicDoubleTerm s (a.1, a.2)) =
      ∑ k ∈ range n.succ,
        inverseTiltedDyadicDoubleTerm s (k, n - k) by
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k j => inverseTiltedDyadicDoubleTerm s (k, j)) n]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [inverseTiltedDyadicDoubleTerm,
      inverseTiltedDyadicWeightedPrimeWindow]
  · rw [LSeries.term_of_ne_zero hn.ne']
    rw [inverseTiltedDyadicWeightedPrimeWindow, ofReal_sum]
    have hset : (range n.succ).filter (fun k => n - k < k) =
        Finset.Ioc (n / 2) n := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
        Finset.mem_Ioc]
      omega
    calc
      (∑ k ∈ range n.succ,
          inverseTiltedDyadicDoubleTerm s (k, n - k)) =
          ∑ k ∈ (range n.succ).filter (fun k => n - k < k),
            ((((ArithmeticFunction.vonMangoldt k / Real.sqrt k) * k : ℝ) : ℂ)) *
              ((n : ℂ) ^ (-(s + 1))) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
        by_cases hcond : n - k < k
        · rw [if_pos hcond, inverseTiltedDyadicDoubleTerm, if_pos hcond,
            Nat.add_sub_of_le hkn]
        · rw [if_neg hcond, inverseTiltedDyadicDoubleTerm, if_neg hcond]
      _ = ∑ k ∈ Ioc (n / 2) n,
            ((((ArithmeticFunction.vonMangoldt k / Real.sqrt k) * k : ℝ) : ℂ)) *
              ((n : ℂ) ^ (-(s + 1))) := by rw [hset]
      _ = ∑ k ∈ Ioc (n / 2) n,
            ((((ArithmeticFunction.vonMangoldt k / Real.sqrt k) *
                (k / n : ℝ) : ℝ) : ℂ)) /
              (n : ℂ) ^ s := by
        apply Finset.sum_congr rfl
        intro k hk
        have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        rw [Complex.cpow_neg, Complex.cpow_add _ _ hnC]
        norm_num
        field_simp
      _ = (∑ k ∈ Ioc (n / 2) n,
            ((((ArithmeticFunction.vonMangoldt k / Real.sqrt k) *
                (k / n : ℝ) : ℝ) : ℂ))) /
              (n : ℂ) ^ s := by
        rw [Finset.sum_div]

/-- Reversing the inverse-tilted moving window produces the shifted dyadic kernel series. -/
theorem LSeries_inverseTiltedDyadicWeightedPrimeWindow_eq_kernelSeries
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries
        (fun n => ((inverseTiltedDyadicWeightedPrimeWindow n : ℝ) : ℂ)) s =
      ∑' k : ℕ,
        ((((ArithmeticFunction.vonMangoldt k / Real.sqrt k) * k : ℝ) : ℂ)) *
          dyadicSharpPrimeWindowKernel k (s + 1) := by
  let e := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ))
  have hdouble := summable_inverseTiltedDyadicDoubleTerm hs
  have hsigma : Summable
      (fun p : (n : ℕ) × ↥(Finset.HasAntidiagonal.antidiagonal n) =>
      inverseTiltedDyadicDoubleTerm s (e p)) := by
    exact (e.summable_iff (f := inverseTiltedDyadicDoubleTerm s)).mpr hdouble
  rw [LSeries]
  calc
    (∑' n : ℕ, LSeries.term
        (fun m => ((inverseTiltedDyadicWeightedPrimeWindow m : ℝ) : ℂ)) s n) =
        ∑' n : ℕ, ∑' p : ↥(Finset.HasAntidiagonal.antidiagonal n),
          inverseTiltedDyadicDoubleTerm s p.1 := by
      apply tsum_congr
      intro n
      exact (antidiagonal_inverseTiltedDoubleTerm_eq_LSeriesTerm_window s n).symm
    _ = ∑' p : (n : ℕ) × ↥(Finset.HasAntidiagonal.antidiagonal n),
          inverseTiltedDyadicDoubleTerm s (e p) := by
      change (∑' n : ℕ, ∑' p : ↥(Finset.HasAntidiagonal.antidiagonal n),
        inverseTiltedDyadicDoubleTerm s (e ⟨n, p⟩)) = _
      rw [← hsigma.tsum_sigma]
    _ = ∑' kj : ℕ × ℕ, inverseTiltedDyadicDoubleTerm s kj :=
      e.tsum_eq (f := inverseTiltedDyadicDoubleTerm s)
    _ = ∑' k : ℕ, ∑' j : ℕ,
          inverseTiltedDyadicDoubleTerm s (k, j) := hdouble.tsum_prod
    _ = ∑' k : ℕ,
        ((((ArithmeticFunction.vonMangoldt k / Real.sqrt k) * k : ℝ) : ℂ)) *
          dyadicSharpPrimeWindowKernel k (s + 1) := by
      apply tsum_congr
      intro k
      exact tsum_inverseTiltedDyadicDoubleTerm_right k s

theorem inverseTiltedDyadicWeightedPrimeWindow_LSeriesSummable
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable
      (fun n => ((inverseTiltedDyadicWeightedPrimeWindow n : ℝ) : ℂ)) s := by
  let e := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ))
  have hdouble := summable_inverseTiltedDyadicDoubleTerm hs
  have hsigma : Summable
      (fun p : (n : ℕ) × ↥(Finset.HasAntidiagonal.antidiagonal n) =>
      inverseTiltedDyadicDoubleTerm s (e p)) := by
    exact (e.summable_iff (f := inverseTiltedDyadicDoubleTerm s)).mpr hdouble
  exact hsigma.sigma.congr fun n => by
    change
      (∑' p : ↥(Finset.HasAntidiagonal.antidiagonal n),
        inverseTiltedDyadicDoubleTerm s p.1) =
        LSeries.term
          (fun m => ((inverseTiltedDyadicWeightedPrimeWindow m : ℝ) : ℂ)) s n
    exact antidiagonal_inverseTiltedDoubleTerm_eq_LSeriesTerm_window s n

private theorem inverseTilted_weightedKernel_eq_main_add_error
    (k : ℕ) (s : ℂ) :
    ((((ArithmeticFunction.vonMangoldt k / Real.sqrt k) * k : ℝ) : ℂ)) *
        dyadicSharpPrimeWindowKernel k (s + 1) =
      inverseTiltedDyadicMellin s *
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (s - 1 / 2) k +
        inverseTiltedDyadicErrorSummand s k := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp [inverseTiltedDyadicMellin, inverseTiltedDyadicErrorSummand,
      dyadicSharpPrimeWindowKernel, dyadicSharpPrimeWindowError,
      dyadicSharpPrimeWindowIntegralMain]
  · have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
    rw [inverseTiltedDyadicErrorSummand,
      dyadicSharpPrimeWindowError,
      dyadicSharpPrimeWindowIntegralMain_eq_scaledMellin hk (s + 1),
      LSeries.term_of_ne_zero hk0, inverseTiltedDyadicMellin]
    have hsqrt : ((Real.sqrt k : ℝ) : ℂ) = (k : ℂ) ^ (1 / 2 : ℂ) := by
      rw [Real.sqrt_eq_rpow]
      simpa using Complex.ofReal_cpow (Nat.cast_nonneg k) (1 / 2 : ℝ)
    rw [ofReal_mul, ofReal_div, hsqrt, ofReal_natCast]
    have hpow :
        (k : ℂ) * (k : ℂ) ^ (1 - (s + 1)) /
            (k : ℂ) ^ (1 / 2 : ℂ) =
          1 / (k : ℂ) ^ (s - 1 / 2) := by
      calc
        (k : ℂ) * (k : ℂ) ^ (1 - (s + 1)) /
            (k : ℂ) ^ (1 / 2 : ℂ) =
          (k : ℂ) ^ (1 : ℂ) * (k : ℂ) ^ (1 - (s + 1)) /
            (k : ℂ) ^ (1 / 2 : ℂ) := by rw [Complex.cpow_one]
        _ = (k : ℂ) ^ ((1 : ℂ) + (1 - (s + 1))) /
            (k : ℂ) ^ (1 / 2 : ℂ) := by
          rw [Complex.cpow_add _ _ hkC]
        _ = (k : ℂ) ^ (((1 : ℂ) + (1 - (s + 1))) - 1 / 2) := by
          rw [Complex.cpow_sub _ _ hkC]
        _ = (k : ℂ) ^ (-(s - 1 / 2)) := by
          congr 1
          ring
        _ = 1 / (k : ℂ) ^ (s - 1 / 2) := by
          rw [Complex.cpow_neg]
          simp only [one_div]
    rw [mul_sub]
    have hmain :
        ((((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) /
            (k : ℂ) ^ (1 / 2 : ℂ)) * (k : ℂ)) *
              ((k : ℂ) ^ (1 - (s + 1)) *
                sharpPrimeWindowMellin (Real.log 2) (s + 1)) =
          sharpPrimeWindowMellin (Real.log 2) (s + 1) *
            (((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) /
              (k : ℂ) ^ (s - 1 / 2)) := by
      calc
        ((((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) /
            (k : ℂ) ^ (1 / 2 : ℂ)) * (k : ℂ)) *
              ((k : ℂ) ^ (1 - (s + 1)) *
                sharpPrimeWindowMellin (Real.log 2) (s + 1)) =
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ) *
              ((k : ℂ) * (k : ℂ) ^ (1 - (s + 1)) /
                (k : ℂ) ^ (1 / 2 : ℂ)) *
                sharpPrimeWindowMellin (Real.log 2) (s + 1) := by ring
        _ = _ := by rw [hpow]; ring
    rw [hmain]
    ring

/-- The inverse-tilted finite prime window has the expected logarithmic-derivative transform. -/
theorem LSeries_inverseTiltedDyadicWeightedPrimeWindow_eq_zetaLogDeriv
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries
        (fun n => ((inverseTiltedDyadicWeightedPrimeWindow n : ℝ) : ℂ)) s =
      -inverseTiltedDyadicMellin s * zetaLogDeriv (s - 1 / 2) +
        inverseTiltedDyadicErrorSeries s := by
  have hshift : 1 < (s - 1 / 2).re := by
    norm_num [Complex.sub_re] at hs ⊢
    linarith
  have hvm : LSeriesSummable
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s - 1 / 2) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hshift
  have hmain : Summable (fun k =>
      inverseTiltedDyadicMellin s *
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (s - 1 / 2) k) := hvm.mul_left _
  have herr := summable_inverseTiltedDyadicErrorSummand
    (by linarith : 1 / 2 < s.re)
  calc
    LSeries
        (fun n => ((inverseTiltedDyadicWeightedPrimeWindow n : ℝ) : ℂ)) s =
        ∑' k : ℕ,
          ((((ArithmeticFunction.vonMangoldt k / Real.sqrt k) * k : ℝ) : ℂ)) *
            dyadicSharpPrimeWindowKernel k (s + 1) :=
      LSeries_inverseTiltedDyadicWeightedPrimeWindow_eq_kernelSeries hs
    _ = ∑' k : ℕ,
        (inverseTiltedDyadicMellin s *
            LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (s - 1 / 2) k +
          inverseTiltedDyadicErrorSummand s k) := by
      apply tsum_congr
      intro k
      exact inverseTilted_weightedKernel_eq_main_add_error k s
    _ = (∑' k : ℕ,
          inverseTiltedDyadicMellin s *
            LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (s - 1 / 2) k) +
        ∑' k : ℕ, inverseTiltedDyadicErrorSummand s k :=
      hmain.tsum_add herr
    _ = inverseTiltedDyadicMellin s *
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (s - 1 / 2) + inverseTiltedDyadicErrorSeries s := by
      rw [tsum_mul_left]
      rfl
    _ = -inverseTiltedDyadicMellin s * zetaLogDeriv (s - 1 / 2) +
        inverseTiltedDyadicErrorSeries s := by
      rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hshift,
        zetaLogDeriv]
      ring

theorem inverseTiltedDyadicPoleFilledMain_eq_zetaLogDeriv
    {s : ℂ} (hs : 3 / 2 < s.re) :
    dslope inverseTiltedDyadicPoleNumerator (3 / 2) s +
        2 * inverseTiltedDyadicMellin s *
          logDeriv regularizedRiemannZeta (s - 1 / 2) =
      2 * inverseTiltedDyadicMellin (3 / 2) *
          riemannZeta (s - 1 / 2) +
        2 * inverseTiltedDyadicMellin s *
          zetaLogDeriv (s - 1 / 2) := by
  have ht : s - 1 / 2 ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.sub_re] at hre
    linarith
  have hz : riemannZeta (s - 1 / 2) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      norm_num [Complex.sub_re]
      linarith)
  have hs0 : s ≠ 3 / 2 := by
    intro h
    rw [h] at hs
    norm_num at hs
  rw [dslope_of_ne _ hs0, slope_def_field,
    inverseTiltedDyadicPoleNumerator_three_halves, sub_zero,
    inverseTiltedDyadicPoleNumerator,
    regularizedRiemannZeta_of_ne_one ht,
    logDeriv_regularizedRiemannZeta_eq ht hz]
  have hden : (s - 1 / 2) - 1 = s - 3 / 2 := by ring
  rw [hden]
  have hden0 : s - 3 / 2 ≠ 0 := sub_ne_zero.mpr hs0
  let d : ℂ := s - 3 / 2
  have hd : d ≠ 0 := by simpa only [d] using hden0
  let A : ℂ := inverseTiltedDyadicMellin (3 / 2)
  let B : ℂ := inverseTiltedDyadicMellin s
  let Z : ℂ := riemannZeta (s - 1 / 2)
  let W : ℂ := zetaLogDeriv (s - 1 / 2)
  rw [show s - 3 / 2 = d by rfl]
  change (2 * A * (d * Z) - 2 * B) / d +
      2 * B * (1 / d + W) = 2 * A * Z + 2 * B * W
  rw [div_eq_mul_inv, one_div]
  have hc : d * d⁻¹ = 1 := mul_inv_cancel₀ hd
  calc
    (2 * A * (d * Z) - 2 * B) * d⁻¹ +
        2 * B * (d⁻¹ + W) =
      2 * A * Z * (d * d⁻¹) + 2 * B * W := by ring
    _ = 2 * A * Z + 2 * B * W := by rw [hc]; ring

theorem inverseTiltedDyadicContinuedSource_eq_zetaLogDeriv
    {s : ℂ} (hs : 3 / 2 < s.re) :
    inverseTiltedDyadicContinuedSource s =
      2 * inverseTiltedDyadicMellin (3 / 2) *
          riemannZeta (s - 1 / 2) +
        2 * inverseTiltedDyadicMellin s *
          zetaLogDeriv (s - 1 / 2) -
        2 * inverseTiltedDyadicErrorSeries s := by
  rw [inverseTiltedDyadicContinuedSource,
    inverseTiltedDyadicPoleFilledMain_eq_zetaLogDeriv hs]

/-- The finite prime-polar coefficient.  The complex constant is proved real below. -/
def inverseTiltedDyadicSourceCoefficient (n : ℕ) : ℂ :=
  2 * inverseTiltedDyadicMellin (3 / 2) * (Real.sqrt n : ℂ) -
    2 * (inverseTiltedDyadicWeightedPrimeWindow n : ℂ)

/-- Real-valued presentation of the same source coefficient. -/
def inverseTiltedDyadicRealSourceCoefficient (n : ℕ) : ℝ :=
  (2 * inverseTiltedDyadicMellin (3 / 2)).re * Real.sqrt n -
    2 * inverseTiltedDyadicWeightedPrimeWindow n

theorem inverseTiltedDyadicMellin_three_halves_im_eq_zero :
    (inverseTiltedDyadicMellin (3 / 2)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [inverseTiltedDyadicMellin_eq_rectangularAmplitude,
    rectangularWindowAmplitude_conj]
  congr 1
  rw [map_div₀, map_ofNat, map_ofNat]

theorem ofReal_inverseTiltedDyadicRealSourceCoefficient
    (n : ℕ) :
    ((inverseTiltedDyadicRealSourceCoefficient n : ℝ) : ℂ) =
      inverseTiltedDyadicSourceCoefficient n := by
  apply Complex.ext
  · simp [inverseTiltedDyadicRealSourceCoefficient,
      inverseTiltedDyadicSourceCoefficient]
  · simp [inverseTiltedDyadicRealSourceCoefficient,
      inverseTiltedDyadicSourceCoefficient,
      inverseTiltedDyadicMellin_three_halves_im_eq_zero]

theorem inverseTiltedDyadicSourceCoefficient_LSeriesSummable
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable inverseTiltedDyadicSourceCoefficient s := by
  have hsqrt := RHTower.CompactBVPrimeWindow.sqrt_LSeriesSummable hs
  have hwindow := inverseTiltedDyadicWeightedPrimeWindow_LSeriesSummable hs
  have hdiff := (hsqrt.smul
    (2 * inverseTiltedDyadicMellin (3 / 2))).sub
      (hwindow.smul (2 : ℂ))
  change Summable (LSeries.term inverseTiltedDyadicSourceCoefficient s)
  change Summable (LSeries.term _ s) at hdiff
  exact hdiff.congr fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        inverseTiltedDyadicSourceCoefficient]

/-- **Initial-half-plane source identity.** -/
theorem LSeries_inverseTiltedDyadicSourceCoefficient_eq_continuedSource
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries inverseTiltedDyadicSourceCoefficient s =
      inverseTiltedDyadicContinuedSource s := by
  have hsqrt := RHTower.CompactBVPrimeWindow.sqrt_LSeriesSummable hs
  have hwindow := inverseTiltedDyadicWeightedPrimeWindow_LSeriesSummable hs
  have hscaledSqrt := hsqrt.smul
    (2 * inverseTiltedDyadicMellin (3 / 2))
  have hscaledWindow := hwindow.smul (2 : ℂ)
  have hcontinued := inverseTiltedDyadicContinuedSource_eq_zetaLogDeriv hs
  calc
    LSeries inverseTiltedDyadicSourceCoefficient s =
        LSeries
          ((2 * inverseTiltedDyadicMellin (3 / 2)) •
              (fun n : ℕ => ((Real.sqrt n : ℝ) : ℂ)) -
            (2 : ℂ) •
              (fun n => ((inverseTiltedDyadicWeightedPrimeWindow n : ℝ) : ℂ))) s := by
      apply LSeries_congr
      intro n hn
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        inverseTiltedDyadicSourceCoefficient]
    _ = (2 * inverseTiltedDyadicMellin (3 / 2)) *
          LSeries (fun n : ℕ => ((Real.sqrt n : ℝ) : ℂ)) s -
        2 * LSeries
          (fun n => ((inverseTiltedDyadicWeightedPrimeWindow n : ℝ) : ℂ)) s := by
      rw [LSeries_sub hscaledSqrt hscaledWindow, LSeries_smul, LSeries_smul]
    _ = (2 * inverseTiltedDyadicMellin (3 / 2)) *
          riemannZeta (s - 1 / 2) -
        2 * (-inverseTiltedDyadicMellin s *
            zetaLogDeriv (s - 1 / 2) +
          inverseTiltedDyadicErrorSeries s) := by
      rw [RHTower.CompactBVPrimeWindow.LSeries_sqrt_eq_riemannZeta_shift hs,
        LSeries_inverseTiltedDyadicWeightedPrimeWindow_eq_zetaLogDeriv hs]
    _ = 2 * inverseTiltedDyadicMellin (3 / 2) *
          riemannZeta (s - 1 / 2) +
        2 * inverseTiltedDyadicMellin s *
          zetaLogDeriv (s - 1 / 2) -
        2 * inverseTiltedDyadicErrorSeries s := by ring
    _ = inverseTiltedDyadicContinuedSource s := hcontinued.symm

theorem LSeries_inverseTiltedDyadicRealSourceCoefficient_eq_continuedSource
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries
        (fun n => ((inverseTiltedDyadicRealSourceCoefficient n : ℝ) : ℂ)) s =
      inverseTiltedDyadicContinuedSource s := by
  rw [← LSeries_inverseTiltedDyadicSourceCoefficient_eq_continuedSource hs]
  apply LSeries_congr
  intro n _hn
  exact ofReal_inverseTiltedDyadicRealSourceCoefficient n

/-! ## Complete Xi-divisor tomography -/

/-- Shifted pole coordinate attached to an arbitrary point of the Xi divisor support. -/
def inverseTiltedXiPole (rho : XiDivisorSupport) : ℂ :=
  (rho : ℂ) + 1 / 2

/-- Analytic multiplicity at a point of the complete Xi divisor. -/
def inverseTiltedXiMultiplicity (rho : XiDivisorSupport) : ℕ :=
  (analyticOrderAt xi (rho : ℂ)).toNat

theorem inverseTiltedXiMultiplicity_pos (rho : XiDivisorSupport) :
    0 < inverseTiltedXiMultiplicity rho := by
  apply Nat.pos_of_ne_zero
  exact xi_order_toNat_ne_zero (xi_eq_zero_of_mem_divisor_support rho)

theorem inverseTiltedXiPole_re_gt_half (rho : XiDivisorSupport) :
    1 / 2 < (inverseTiltedXiPole rho).re := by
  rw [inverseTiltedXiPole, Complex.add_re]
  norm_num
  linarith [(xi_divisor_support_re_mem_open_unit rho).1]

theorem regularizedRiemannZeta_eq_zero_at_inverseTiltedXiPole
    (rho : XiDivisorSupport) :
    regularizedRiemannZeta (inverseTiltedXiPole rho - 1 / 2) = 0 := by
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  have hrho1 : (rho : ℂ) ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hstrip
    exact (lt_irrefl 1 hstrip.2).elim
  have hxi : xi (rho : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support rho
  have hzeta : riemannZeta (rho : ℂ) = 0 :=
    (xi_eq_zero_iff hstrip.1 hrho1).mp hxi
  rw [inverseTiltedXiPole]
  have hcoord : (rho : ℂ) + 1 / 2 - 1 / 2 = (rho : ℂ) := by ring
  rw [hcoord, regularizedRiemannZeta_of_ne_one hrho1, hzeta, mul_zero]

theorem analyticOrderAt_regularizedRiemannZeta_eq_xi_of_support
    (rho : XiDivisorSupport) :
    analyticOrderAt regularizedRiemannZeta (rho : ℂ) =
      analyticOrderAt xi (rho : ℂ) := by
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  have hrho1 : (rho : ℂ) ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hstrip
    exact (lt_irrefl 1 hstrip.2).elim
  have hev : regularizedRiemannZeta =ᶠ[nhds (rho : ℂ)]
      fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hrho1] with z hz
    exact regularizedRiemannZeta_of_ne_one hz
  have hlin : AnalyticAt ℂ (fun z : ℂ => z - 1) (rho : ℂ) := by fun_prop
  have hzeta : AnalyticAt ℂ riemannZeta (rho : ℂ) :=
    analyticOn_riemannZeta (rho : ℂ) hrho1
  calc
    analyticOrderAt regularizedRiemannZeta (rho : ℂ) =
        analyticOrderAt ((fun z : ℂ => z - 1) * riemannZeta) (rho : ℂ) := by
      rw [analyticOrderAt_congr hev]
      rfl
    _ = analyticOrderAt riemannZeta (rho : ℂ) := by
      rw [analyticOrderAt_mul hlin hzeta,
        hlin.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hrho1), zero_add]
    _ = analyticOrderAt xi (rho : ℂ) :=
      (xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip).symm

theorem tendsto_inverseTilted_shiftedLogDeriv_residue
    (rho : XiDivisorSupport) :
    Tendsto
      (fun s : ℂ => (s - inverseTiltedXiPole rho) *
        logDeriv regularizedRiemannZeta (s - 1 / 2))
      (nhdsWithin (inverseTiltedXiPole rho) ({inverseTiltedXiPole rho}ᶜ))
      (𝓝 (inverseTiltedXiMultiplicity rho : ℂ)) := by
  let p : ℂ := inverseTiltedXiPole rho
  have hprho : p - 1 / 2 = (rho : ℂ) := by
    dsimp only [p, inverseTiltedXiPole]
    ring
  have hreg : AnalyticAt ℂ regularizedRiemannZeta (rho : ℂ) :=
    (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
      isOpen_univ) (rho : ℂ) (Set.mem_univ _)
  have hzero : regularizedRiemannZeta (rho : ℂ) = 0 := by
    have h := regularizedRiemannZeta_eq_zero_at_inverseTiltedXiPole rho
    simpa only [p, hprho] using h
  have hbase := logDeriv_iteratedDeriv_residue_of_zero
    hreg (analyticOrderAt_regularizedRiemannZeta_ne_top (rho : ℂ)) hzero 0
  have hbase' : Tendsto
      (fun t : ℂ => (t - (rho : ℂ)) * logDeriv regularizedRiemannZeta t)
      (𝓝[≠] (rho : ℂ))
      (𝓝 ((analyticOrderAt regularizedRiemannZeta (rho : ℂ)).toNat : ℂ)) := by
    simpa only [zero_add, pow_one, iteratedDeriv_zero, logDeriv_apply,
      pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, mul_one] using hbase
  have hshift : Tendsto (fun s : ℂ => s - 1 / 2)
      (𝓝[≠] p) (𝓝[≠] (rho : ℂ)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have hc : ContinuousAt (fun s : ℂ => s - 1 / 2) p :=
        continuousAt_id.sub_const _
      have hle : 𝓝[≠] p ≤ 𝓝 p := inf_le_left
      simpa only [hprho] using hc.tendsto.mono_left hle
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change s - 1 / 2 ≠ (rho : ℂ)
      intro heq
      have hsp : s ≠ p := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs
      apply hsp
      linear_combination heq - hprho
  have hcomposed := hbase'.comp hshift
  rw [analyticOrderAt_regularizedRiemannZeta_eq_xi_of_support rho] at hcomposed
  change Tendsto _ _
    (𝓝 ((analyticOrderAt xi (rho : ℂ)).toNat : ℂ))
  convert hcomposed using 1
  funext s
  rw [Function.comp_apply]
  congr 1
  dsimp only [p] at hprho ⊢
  rw [← hprho]
  ring

theorem meromorphicOrderAt_inverseTilted_shiftedLogDeriv_eq_neg_one
    (rho : XiDivisorSupport) :
    meromorphicOrderAt
        (fun s : ℂ => logDeriv regularizedRiemannZeta (s - 1 / 2))
        (inverseTiltedXiPole rho) = ((-1 : ℤ) : WithTop ℤ) := by
  let p : ℂ := inverseTiltedXiPole rho
  have hprho : p - 1 / 2 = (rho : ℂ) := by
    dsimp only [p, inverseTiltedXiPole]
    ring
  have hzero : regularizedRiemannZeta (rho : ℂ) = 0 := by
    have h := regularizedRiemannZeta_eq_zero_at_inverseTiltedXiPole rho
    simpa only [p, hprho] using h
  let shift : ℂ → ℂ := fun z => z - 1 / 2
  have hshiftAnalytic : AnalyticAt ℂ shift p := by
    dsimp only [shift]
    fun_prop
  have hshiftDeriv : deriv shift p ≠ 0 := by
    dsimp only [shift]
    rw [deriv_sub_const, deriv_id'']
    norm_num
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := logDeriv regularizedRiemannZeta) (g := shift) (x := p)
    hshiftAnalytic hshiftDeriv
  rw [show shift p = (rho : ℂ) by simpa only [shift] using hprho,
    meromorphicOrderAt_logDeriv_regularizedRiemannZeta_eq_neg_one hzero] at hcomp
  simpa only [shift, Function.comp_apply, p] using! hcomp

theorem meromorphicTrailingCoeffAt_inverseTilted_shiftedLogDeriv
    (rho : XiDivisorSupport) :
    meromorphicTrailingCoeffAt
        (fun s : ℂ => logDeriv regularizedRiemannZeta (s - 1 / 2))
        (inverseTiltedXiPole rho) =
      (inverseTiltedXiMultiplicity rho : ℂ) := by
  let p : ℂ := inverseTiltedXiPole rho
  let f : ℂ → ℂ := fun s =>
    logDeriv regularizedRiemannZeta (s - 1 / 2)
  let shift : ℂ → ℂ := fun s => s - 1 / 2
  have hshiftAnalytic : AnalyticAt ℂ shift p := by
    dsimp only [shift]
    fun_prop
  have hbase : MeromorphicAt (logDeriv regularizedRiemannZeta) (shift p) :=
    meromorphicAt_logDeriv_regularizedRiemannZeta (shift p)
  have hf : MeromorphicAt f p := by
    have hcomp := MeromorphicAt.comp_analyticAt
      (f := logDeriv regularizedRiemannZeta) (g := shift)
      hbase hshiftAnalytic
    simpa only [f, shift, Function.comp_apply] using! hcomp
  have horder : meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ) := by
    simpa only [f, p] using
      meromorphicOrderAt_inverseTilted_shiftedLogDeriv_eq_neg_one rho
  have htrail := hf.tendsto_nhds_meromorphicTrailingCoeffAt
  rw [horder] at htrail
  simp only [WithTop.untop₀_coe, neg_neg, zpow_one, smul_eq_mul] at htrail
  have hres := tendsto_inverseTilted_shiftedLogDeriv_residue rho
  simpa only [f, p] using tendsto_nhds_unique htrail hres

theorem inverseTiltedDyadicMellin_ne_zero_at_xiPole
    (rho : XiDivisorSupport) :
    inverseTiltedDyadicMellin (inverseTiltedXiPole rho) ≠ 0 :=
  inverseTiltedDyadicMellin_ne_zero_of_re_pos
    (lt_trans (by norm_num : (0 : ℝ) < 1 / 2)
      (inverseTiltedXiPole_re_gt_half rho))

/-- **Pole data of the inverse-tilted dyadic continued source.**  At each shifted Xi pole the
source is a simple pole whose trailing coefficient is twice the dyadic Mellin factor times the
multiplicity.  Both readings come from the same splitting into a singular product and a
higher-order correction, so they are proved together. -/
theorem meromorphicOrderAt_and_trailingCoeffAt_inverseTiltedDyadicContinuedSource
    (rho : XiDivisorSupport) :
    meromorphicOrderAt inverseTiltedDyadicContinuedSource
        (inverseTiltedXiPole rho) = ((-1 : ℤ) : WithTop ℤ) ∧
      meromorphicTrailingCoeffAt inverseTiltedDyadicContinuedSource
          (inverseTiltedXiPole rho) =
        2 * inverseTiltedDyadicMellin (inverseTiltedXiPole rho) *
          (inverseTiltedXiMultiplicity rho : ℂ) := by

  let p : ℂ := inverseTiltedXiPole rho
  let shiftedLog : ℂ → ℂ := fun z =>
    logDeriv regularizedRiemannZeta (z - 1 / 2)
  let fac : ℂ → ℂ := fun z => 2 * inverseTiltedDyadicMellin z
  let singular : ℂ → ℂ := fun z => fac z * shiftedLog z
  let correction : ℂ → ℂ := fun z =>
    dslope inverseTiltedDyadicPoleNumerator (3 / 2) z -
      2 * inverseTiltedDyadicErrorSeries z
  have hpHalf : 1 / 2 < p.re := by
    simpa only [p] using inverseTiltedXiPole_re_gt_half rho
  have hM : AnalyticAt ℂ inverseTiltedDyadicMellin p :=
    (differentiable_inverseTiltedDyadicMellin.differentiableOn.analyticOnNhd
      isOpen_univ) p (Set.mem_univ p)
  have hfac : AnalyticAt ℂ fac p := by
    dsimp only [fac]
    exact analyticAt_const.mul hM
  have hfac0 : fac p ≠ 0 := by
    dsimp only [fac, p]
    exact mul_ne_zero (by norm_num)
      (inverseTiltedDyadicMellin_ne_zero_at_xiPole rho)
  have hshiftedLog : MeromorphicAt shiftedLog p := by
    let shift : ℂ → ℂ := fun z => z - 1 / 2
    have hshiftAnalytic : AnalyticAt ℂ shift p := by
      dsimp only [shift]
      fun_prop
    have hbase : MeromorphicAt (logDeriv regularizedRiemannZeta) (shift p) :=
      meromorphicAt_logDeriv_regularizedRiemannZeta (shift p)
    have hcomp := MeromorphicAt.comp_analyticAt
      (f := logDeriv regularizedRiemannZeta) (g := shift)
      hbase hshiftAnalytic
    simpa only [shiftedLog, shift, Function.comp_apply] using! hcomp
  have hsingular : MeromorphicAt singular p := by
    dsimp only [singular]
    exact hfac.meromorphicAt.mul hshiftedLog
  have hfacOrder : meromorphicOrderAt fac p = 0 := by
    rw [hfac.meromorphicOrderAt_eq,
      hfac.analyticOrderAt_eq_zero.mpr hfac0]
    simp
  have hshiftOrder : meromorphicOrderAt shiftedLog p =
      ((-1 : ℤ) : WithTop ℤ) := by
    simpa only [shiftedLog, p] using
      meromorphicOrderAt_inverseTilted_shiftedLogDeriv_eq_neg_one rho
  have hsingularOrder : meromorphicOrderAt singular p =
      ((-1 : ℤ) : WithTop ℤ) := by
    dsimp only [singular]
    rw [fun_meromorphicOrderAt_mul hfac.meromorphicAt hshiftedLog,
      hfacOrder, hshiftOrder]
    norm_num
  have hdiv : AnalyticAt ℂ
      (dslope inverseTiltedDyadicPoleNumerator (3 / 2)) p :=
    (differentiable_inverseTiltedDyadicPoleDividedDifference.differentiableOn.analyticOnNhd
      isOpen_univ) p (Set.mem_univ p)
  have herr : AnalyticAt ℂ inverseTiltedDyadicErrorSeries p :=
    (differentiableOn_inverseTiltedDyadicErrorSeries_rightHalf.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)) p hpHalf
  have hcorrection : AnalyticAt ℂ correction p := by
    dsimp only [correction]
    exact hdiv.sub (analyticAt_const.mul herr)
  have hlt : meromorphicOrderAt singular p <
      meromorphicOrderAt correction p := by
    rw [hsingularOrder]
    exact lt_of_lt_of_le
      (by exact_mod_cast (show (-1 : ℤ) < 0 by omega))
      hcorrection.meromorphicOrderAt_nonneg
  have hfun : inverseTiltedDyadicContinuedSource = singular + correction := by
    funext z
    simp only [inverseTiltedDyadicContinuedSource, singular, fac, shiftedLog,
      correction, Pi.add_apply]
    ring
  refine ⟨by
      rw [hfun, meromorphicOrderAt_add_eq_left_of_lt hcorrection.meromorphicAt hlt,
        hsingularOrder], ?_⟩
  rw [hfun]
  change meromorphicTrailingCoeffAt (fun z => singular z + correction z) p =
    fac p * (inverseTiltedXiMultiplicity rho : ℂ)
  rw [hcorrection.meromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt hlt]
  dsimp only [singular]
  rw [hfac.meromorphicAt.meromorphicTrailingCoeffAt_fun_mul hshiftedLog,
    hfac.meromorphicTrailingCoeffAt_of_ne_zero hfac0]
  have hlogTrail :=
    meromorphicTrailingCoeffAt_inverseTilted_shiftedLogDeriv rho
  rw [hlogTrail]

theorem meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one
    (rho : XiDivisorSupport) :
    meromorphicOrderAt inverseTiltedDyadicContinuedSource
        (inverseTiltedXiPole rho) = ((-1 : ℤ) : WithTop ℤ) :=
  (meromorphicOrderAt_and_trailingCoeffAt_inverseTiltedDyadicContinuedSource rho).1

theorem meromorphicTrailingCoeffAt_inverseTiltedDyadicContinuedSource
    (rho : XiDivisorSupport) :
    meromorphicTrailingCoeffAt inverseTiltedDyadicContinuedSource
        (inverseTiltedXiPole rho) =
      2 * inverseTiltedDyadicMellin (inverseTiltedXiPole rho) *
        (inverseTiltedXiMultiplicity rho : ℂ) :=
  (meromorphicOrderAt_and_trailingCoeffAt_inverseTiltedDyadicContinuedSource rho).2

theorem exists_xiDivisorSupport_of_inverseTilted_regularizedZeta_zero
    {s : ℂ} (hs : 1 / 2 < s.re)
    (hzero : regularizedRiemannZeta (s - 1 / 2) = 0) :
    ∃ rho : XiDivisorSupport, inverseTiltedXiPole rho = s := by
  have ht1 : s - 1 / 2 ≠ 1 := by
    intro ht
    rw [ht, regularizedRiemannZeta_one] at hzero
    norm_num at hzero
  have hzeta : riemannZeta (s - 1 / 2) = 0 := by
    rw [regularizedRiemannZeta_of_ne_one ht1] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr ht1)
  have htpos : 0 < (s - 1 / 2).re := by
    norm_num [Complex.sub_re]
    linarith
  have hxi : xi (s - 1 / 2) = 0 :=
    (xi_eq_zero_iff htpos ht1).mpr hzeta
  let rho : XiDivisorSupport :=
    ⟨s - 1 / 2, mem_xi_divisor_support_of_eq_zero hxi⟩
  refine ⟨rho, ?_⟩
  rw [inverseTiltedXiPole]
  dsimp only [rho]
  ring

theorem meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one_iff
    {s : ℂ} (hs : 1 / 2 < s.re) :
    meromorphicOrderAt inverseTiltedDyadicContinuedSource s =
        ((-1 : ℤ) : WithTop ℤ) ↔
      ∃ rho : XiDivisorSupport, inverseTiltedXiPole rho = s := by
  constructor
  · intro horder
    by_contra hnot
    push Not at hnot
    have hzeta : regularizedRiemannZeta (s - 1 / 2) ≠ 0 := by
      intro hz
      obtain ⟨rho, hrho⟩ :=
        exists_xiDivisorSupport_of_inverseTilted_regularizedZeta_zero hs hz
      exact hnot rho hrho
    have han :=
      analyticAt_inverseTiltedDyadicContinuedSource_of_regularizedZeta_ne_zero hs hzeta
    have hnonneg := han.meromorphicOrderAt_nonneg
    rw [horder] at hnonneg
    have hnotneg : ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) := by
      exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)
    exact hnotneg hnonneg
  · rintro ⟨rho, rfl⟩
    exact meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one rho

theorem normalizedInverseTiltedDyadicResidue_eq_multiplicity
    (rho : XiDivisorSupport) :
    meromorphicTrailingCoeffAt inverseTiltedDyadicContinuedSource
          (inverseTiltedXiPole rho) /
        (2 * inverseTiltedDyadicMellin (inverseTiltedXiPole rho)) =
      (inverseTiltedXiMultiplicity rho : ℂ) := by
  rw [meromorphicTrailingCoeffAt_inverseTiltedDyadicContinuedSource rho]
  field_simp [inverseTiltedDyadicMellin_ne_zero_at_xiPole rho]

/-- Complete simple-pole support of the one inverse-tilted source. -/
def inverseTiltedDyadicSimplePoleSupport : Set ℂ :=
  {s : ℂ | 1 / 2 < s.re ∧
    meromorphicOrderAt inverseTiltedDyadicContinuedSource s =
      ((-1 : ℤ) : WithTop ℤ)}

theorem range_inverseTiltedXiPole_eq_simplePoleSupport :
    Set.range inverseTiltedXiPole = inverseTiltedDyadicSimplePoleSupport := by
  ext s
  constructor
  · rintro ⟨rho, rfl⟩
    exact ⟨inverseTiltedXiPole_re_gt_half rho,
      meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one rho⟩
  · rintro ⟨hs, horder⟩
    exact (meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one_iff hs).mp
      horder

/-- The shifted Xi divisor embeds in the one-source pole support. -/
def inverseTiltedXiPoleEmbedding
    (rho : XiDivisorSupport) : inverseTiltedDyadicSimplePoleSupport :=
  ⟨inverseTiltedXiPole rho,
    inverseTiltedXiPole_re_gt_half rho,
    meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one rho⟩

theorem inverseTiltedXiPole_injective :
    Function.Injective inverseTiltedXiPole := by
  intro rho sigma h
  apply Subtype.ext
  dsimp only [inverseTiltedXiPole] at h
  linear_combination h

theorem inverseTiltedXiPoleEmbedding_bijective :
    Function.Bijective inverseTiltedXiPoleEmbedding := by
  constructor
  · intro rho sigma h
    apply inverseTiltedXiPole_injective
    exact congrArg Subtype.val h
  · intro s
    have hsRange : (s : ℂ) ∈ Set.range inverseTiltedXiPole := by
      rw [range_inverseTiltedXiPole_eq_simplePoleSupport]
      exact s.property
    obtain ⟨rho, hrho⟩ := hsRange
    refine ⟨rho, ?_⟩
    apply Subtype.ext
    exact hrho

/-- **Exact divisor equivalence.**  The nontrivial Xi divisor and the simple-pole support of the
single inverse-tilted dyadic source are canonically equivalent. -/
noncomputable def inverseTiltedXiDivisorEquivSimplePoleSupport :
    XiDivisorSupport ≃ inverseTiltedDyadicSimplePoleSupport :=
  Equiv.ofBijective inverseTiltedXiPoleEmbedding
    inverseTiltedXiPoleEmbedding_bijective

/-- The equivalence has the expected affine value `rho ↦ rho + 1/2`. -/
theorem inverseTiltedXiDivisorEquivSimplePoleSupport_apply
    (rho : XiDivisorSupport) :
    ((inverseTiltedXiDivisorEquivSimplePoleSupport rho :
        inverseTiltedDyadicSimplePoleSupport) : ℂ) = inverseTiltedXiPole rho := by
  rfl

/-- **Full-divisor RH criterion.**  RH says exactly that every pole of the complete prime-source
tomography lies on the shifted critical line `Re s = 1`. -/
theorem riemannHypothesis_iff_inverseTiltedDyadic_poles_on_line :
    RiemannHypothesis ↔
      ∀ s : ℂ, 1 / 2 < s.re →
        meromorphicOrderAt inverseTiltedDyadicContinuedSource s =
          ((-1 : ℤ) : WithTop ℤ) → s.re = 1 := by
  constructor
  · intro hRH s hs horder
    obtain ⟨rho, hrho⟩ :=
      (meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one_iff hs).mp
        horder
    have hzero : xi (rho : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support rho
    have hstrip := xi_divisor_support_re_mem_open_unit rho
    have hre : (rho : ℂ).re = 1 / 2 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hleft | hright
      · have hreflectZero : xi (1 - (rho : ℂ)) = 0 := by
          rw [xi_one_sub, hzero]
        have hreflectRight : 1 - (rho : ℂ) ∈ rightHalf := by
          rw [mem_rightHalf]
          simp only [Complex.sub_re, Complex.one_re]
          linarith
        exact (rh_iff_xi_ne_zero_right.mp hRH _ hreflectRight) hreflectZero
      · have hrightMem : (rho : ℂ) ∈ rightHalf := by
          rw [mem_rightHalf]
          exact hright
        exact (rh_iff_xi_ne_zero_right.mp hRH _ hrightMem) hzero
    rw [← hrho, inverseTiltedXiPole, Complex.add_re]
    norm_num
    linarith
  · intro hpoles
    apply rh_iff_xi_ne_zero_right.mpr
    intro z hz hzero
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
    let p : ℂ := inverseTiltedXiPole rho
    have hpHalf : 1 / 2 < p.re := inverseTiltedXiPole_re_gt_half rho
    have hpOrder : meromorphicOrderAt inverseTiltedDyadicContinuedSource p =
        ((-1 : ℤ) : WithTop ℤ) :=
      meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one rho
    have hpLine := hpoles p hpHalf hpOrder
    dsimp only [p, inverseTiltedXiPole] at hpLine
    rw [Complex.add_re] at hpLine
    norm_num at hpLine
    rw [mem_rightHalf] at hz
    linarith

/-- Equivalent open-half-plane formulation: RH is exactly holomorphy of the complete prime
source to the right of its critical polar line. -/
theorem riemannHypothesis_iff_inverseTiltedDyadic_analytic_rightOne :
    RiemannHypothesis ↔
      ∀ s : ℂ, 1 < s.re →
        AnalyticAt ℂ inverseTiltedDyadicContinuedSource s := by
  constructor
  · intro hRH s hs
    have hsHalf : 1 / 2 < s.re := by linarith
    apply analyticAt_inverseTiltedDyadicContinuedSource_of_regularizedZeta_ne_zero hsHalf
    intro hzero
    obtain ⟨rho, hrho⟩ :=
      exists_xiDivisorSupport_of_inverseTilted_regularizedZeta_zero hsHalf hzero
    have hrhoRight : (rho : ℂ) ∈ rightHalf := by
      rw [mem_rightHalf]
      have hre := congrArg Complex.re hrho
      rw [inverseTiltedXiPole, Complex.add_re] at hre
      norm_num at hre
      linarith
    exact (rh_iff_xi_ne_zero_right.mp hRH _ hrhoRight)
      (xi_eq_zero_of_mem_divisor_support rho)
  · intro han
    apply rh_iff_xi_ne_zero_right.mpr
    intro z hz hzero
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
    let p : ℂ := inverseTiltedXiPole rho
    have hpRight : 1 < p.re := by
      dsimp only [p, inverseTiltedXiPole]
      rw [mem_rightHalf] at hz
      rw [Complex.add_re]
      norm_num
      linarith
    have hpOrder :
        meromorphicOrderAt inverseTiltedDyadicContinuedSource p =
          ((-1 : ℤ) : WithTop ℤ) :=
      meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one rho
    have hpNonneg := (han p hpRight).meromorphicOrderAt_nonneg
    rw [hpOrder] at hpNonneg
    have : ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) := by
      exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)
    exact this hpNonneg

/-- Bundled source identity, meromorphic continuation, full support, multiplicity recovery, and
RH line criterion. -/
theorem inverseTiltedDyadicPrimeFullDivisorTomography_capstone :
    (∀ s : ℂ, 3 / 2 < s.re →
      LSeries
          (fun n => ((inverseTiltedDyadicRealSourceCoefficient n : ℝ) : ℂ)) s =
        inverseTiltedDyadicContinuedSource s) ∧
    MeromorphicOn inverseTiltedDyadicContinuedSource
      {s : ℂ | 1 / 2 < s.re} ∧
    (∀ s : ℂ, 1 / 2 < s.re →
      (meromorphicOrderAt inverseTiltedDyadicContinuedSource s =
          ((-1 : ℤ) : WithTop ℤ) ↔
        ∃ rho : XiDivisorSupport, inverseTiltedXiPole rho = s)) ∧
    (∀ rho : XiDivisorSupport,
      meromorphicTrailingCoeffAt inverseTiltedDyadicContinuedSource
            (inverseTiltedXiPole rho) /
          (2 * inverseTiltedDyadicMellin (inverseTiltedXiPole rho)) =
        (inverseTiltedXiMultiplicity rho : ℂ)) ∧
    (RiemannHypothesis ↔
      ∀ s : ℂ, 1 / 2 < s.re →
        meromorphicOrderAt inverseTiltedDyadicContinuedSource s =
          ((-1 : ℤ) : WithTop ℤ) → s.re = 1) ∧
    (RiemannHypothesis ↔
      ∀ s : ℂ, 1 < s.re →
        AnalyticAt ℂ inverseTiltedDyadicContinuedSource s) := by
  exact ⟨fun s hs =>
      LSeries_inverseTiltedDyadicRealSourceCoefficient_eq_continuedSource hs,
    meromorphicOn_inverseTiltedDyadicContinuedSource_rightHalf,
    fun s hs =>
      meromorphicOrderAt_inverseTiltedDyadicContinuedSource_eq_neg_one_iff hs,
    normalizedInverseTiltedDyadicResidue_eq_multiplicity,
    riemannHypothesis_iff_inverseTiltedDyadic_poles_on_line,
    riemannHypothesis_iff_inverseTiltedDyadic_analytic_rightOne⟩

end

end RHTower

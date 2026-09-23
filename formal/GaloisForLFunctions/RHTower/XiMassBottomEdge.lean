import GaloisForLFunctions.RHTower.XiMassSymmetricContour
import GaloisForLFunctions.RHTower.WeightedEulerStripFourierAnalytic
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularArchimedean

/-!
# Absolute convergence of the analytic-mass Euler bottom edge

For every contour depth `1/2 < c < a`, the analytic mass test decays exponentially on the
bottom line `z = x - c i`.  This absorbs both the uniformly absolutely convergent von-Mangoldt
series on `Re s = 1/2 + c` and the logarithmic growth of the completed archimedean derivative.
Thus the literal prime--archimedean bottom source is Bochner integrable without fixing `c = 1`.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Euler coordinate corresponding to the centered bottom point `x - c i`. -/
def xiMassBottomEulerPoint (c x : ℝ) : ℂ :=
  (((1 / 2 + c : ℝ) : ℂ) + x * I)

/-- Analytic mass test restricted to the bottom edge. -/
def xiMassBottomTest (a c : ℝ) (τ : ℂ) (x : ℝ) : ℂ :=
  xiMassAnalyticTest a τ ((x : ℂ) - c * I)

/-- Von-Mangoldt part of the mass bottom edge, before the contour orientation scalar. -/
def xiMassBottomPrimeIntegrand (a c : ℝ) (τ : ℂ) (x : ℝ) : ℂ :=
  xiMassBottomTest a c τ x *
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (xiMassBottomEulerPoint c x)

/-- Archimedean part of the mass bottom edge, before the contour orientation scalar. -/
def xiMassBottomArchIntegrand (a c : ℝ) (τ : ℂ) (x : ℝ) : ℂ :=
  xiMassBottomTest a c τ x * logDeriv archFactor (xiMassBottomEulerPoint c x)

/-- Literal prime--archimedean source on the mass bottom edge. -/
def xiMassBottomSourceIntegrand (a c : ℝ) (τ : ℂ) (x : ℝ) : ℂ :=
  xiMassBottomTest a c τ x *
    (-I *
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (xiMassBottomEulerPoint c x) -
        logDeriv archFactor (xiMassBottomEulerPoint c x)))

theorem xiMassBottomPoint_mem_strip {a c x : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) :
    ((x : ℂ) - c * I) ∈ xiMassStrip a := by
  change |(((x : ℂ) - c * I)).im| < a
  have hc0 : 0 < c := lt_trans (by norm_num) hhalf
  simpa [Complex.mul_im, abs_of_pos hc0] using hca

theorem continuous_xiMassBottomTest {a c : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (τ : ℂ) :
    Continuous (xiMassBottomTest a c τ) := by
  have ha : 0 < a := lt_trans (lt_trans (by norm_num) hhalf) hca
  rw [continuous_iff_continuousAt]
  intro x
  let z : ℝ → ℂ := fun y => (y : ℂ) - c * I
  have hz : HasDerivAt z 1 x := by
    dsimp only [z]
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).sub_const (c * I)
  exact ((hasDerivAt_xiMassAnalyticTest ha τ
    (xiMassBottomPoint_mem_strip hhalf hca)).comp x hz).continuousAt

theorem norm_xiMassBottomTest_le {a c x : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 ≤ τ.re) :
    ‖xiMassBottomTest a c τ x‖ ≤
      Real.exp (|τ.im| * c) * Real.exp (-(τ.re * |x|)) := by
  have ha : 0 < a := lt_trans (lt_trans (by norm_num) hhalf) hca
  have hc0 : 0 < c := lt_trans (by norm_num) hhalf
  have hraw := norm_xiMassAnalyticTest_le ha hτ
    (xiMassBottomPoint_mem_strip hhalf hca :
      ((x : ℂ) - c * I) ∈ xiMassStrip a)
  change ‖xiMassBottomTest a c τ x‖ ≤ _
  calc
    ‖xiMassBottomTest a c τ x‖ ≤
        Real.exp (-τ.re * |(((x : ℂ) - c * I)).re| +
          |τ.im| * |(((x : ℂ) - c * I)).im|) := hraw
    _ = Real.exp (|τ.im| * c) * Real.exp (-(τ.re * |x|)) := by
      simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, sub_zero, sub_im, mul_im, mul_one, add_zero, zero_sub, abs_neg]
      rw [abs_of_pos hc0]
      rw [← Real.exp_add]
      congr 1
      ring

/-- Absolute von-Mangoldt-series bound on the fixed Euler line `Re s = 1/2 + c`. -/
def xiMassBottomVonMangoldtBound (c : ℝ) : ℝ :=
  ∑' n : ℕ, ‖LSeries.term
    (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
      (((1 / 2 + c : ℝ) : ℂ)) n‖

theorem continuous_xiMassBottomVonMangoldtLSeries {c : ℝ} (hhalf : 1 / 2 < c) :
    Continuous (fun x : ℝ =>
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (xiMassBottomEulerPoint c x)) := by
  let s : ℝ → ℂ := xiMassBottomEulerPoint c
  have hs : Continuous s := by
    change Continuous (fun x : ℝ => (((1 / 2 + c : ℝ) : ℂ) + x * I))
    fun_prop
  have habs : LSeries.abscissaOfAbsConv
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy)
  apply continuous_iff_continuousAt.mpr
  intro x
  have hlt : LSeries.abscissaOfAbsConv
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < (s x).re := by
    have hsre : (s x).re = 1 / 2 + c := by simp [s, xiMassBottomEulerPoint]
    rw [hsre]
    exact lt_of_le_of_lt habs
      (by exact_mod_cast (show (1 : ℝ) < 1 / 2 + c by linarith))
  exact (LSeries_hasDerivAt hlt).continuousAt.comp hs.continuousAt

theorem norm_xiMassBottomVonMangoldtLSeries_le {c x : ℝ} (hhalf : 1 / 2 < c) :
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (xiMassBottomEulerPoint c x)‖ ≤ xiMassBottomVonMangoldtBound c := by
  have hsum : LSeriesSummable
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (xiMassBottomEulerPoint c x) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by
      simp only [xiMassBottomEulerPoint, add_re, ofReal_re, mul_re, ofReal_im,
        I_re, I_im, zero_mul, mul_zero]
      linarith)
  have hnorm : Summable (fun n => ‖LSeries.term
      (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
      (xiMassBottomEulerPoint c x) n‖) := summable_norm_iff.mpr hsum
  calc
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (xiMassBottomEulerPoint c x)‖ ≤
        ∑' n, ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
          (xiMassBottomEulerPoint c x) n‖ := norm_tsum_le_tsum_norm hnorm
    _ = xiMassBottomVonMangoldtBound c := by
      unfold xiMassBottomVonMangoldtBound
      congr 1
      funext n
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      simp [xiMassBottomEulerPoint, Complex.mul_re]

theorem continuous_xiMassBottomPrimeIntegrand {a c : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (τ : ℂ) :
    Continuous (xiMassBottomPrimeIntegrand a c τ) := by
  exact (continuous_xiMassBottomTest hhalf hca τ).mul
    (continuous_xiMassBottomVonMangoldtLSeries hhalf)

/-- The mass-weighted von-Mangoldt bottom edge is absolutely integrable at every legal depth. -/
theorem integrable_xiMassBottomPrimeIntegrand {a c : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Integrable (xiMassBottomPrimeIntegrand a c τ) := by
  let B : ℝ := xiMassBottomVonMangoldtBound c
  let E : ℝ := Real.exp (|τ.im| * c)
  have hmajor : Integrable (fun x : ℝ =>
      (E * |B|) * Real.exp (-(τ.re * |x|))) :=
    (integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hτ).const_mul (E * |B|)
  refine hmajor.mono'
    (continuous_xiMassBottomPrimeIntegrand hhalf hca τ).aestronglyMeasurable ?_
  filter_upwards with x
  have hm := norm_xiMassBottomTest_le hhalf hca hτ.le (x := x)
  have hL := norm_xiMassBottomVonMangoldtLSeries_le (x := x) hhalf
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hB : B ≤ |B| := le_abs_self B
  rw [xiMassBottomPrimeIntegrand, norm_mul]
  calc
    ‖xiMassBottomTest a c τ x‖ *
        ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (xiMassBottomEulerPoint c x)‖ ≤
        (E * Real.exp (-(τ.re * |x|))) * B := by
      exact mul_le_mul hm hL (norm_nonneg _) (by positivity)
    _ ≤ (E * Real.exp (-(τ.re * |x|))) * |B| :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    _ = (E * |B|) * Real.exp (-(τ.re * |x|)) := by ring

theorem xiMassBottomEulerPoint_re (c x : ℝ) :
    (xiMassBottomEulerPoint c x).re = 1 / 2 + c := by
  simp [xiMassBottomEulerPoint]

theorem xiMassBottomEulerPoint_ne_zero {c x : ℝ} (hhalf : 1 / 2 < c) :
    xiMassBottomEulerPoint c x ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [xiMassBottomEulerPoint_re, Complex.zero_re] at hre
  linarith

theorem xiMassBottomEulerPoint_ne_one {c x : ℝ} (hhalf : 1 / 2 < c) :
    xiMassBottomEulerPoint c x ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  rw [xiMassBottomEulerPoint_re, Complex.one_re] at hre
  linarith

theorem continuous_xiMassBottomArchLogDeriv {c : ℝ} (hhalf : 1 / 2 < c) :
    Continuous (fun x : ℝ => logDeriv archFactor (xiMassBottomEulerPoint c x)) := by
  let s : ℝ → ℂ := xiMassBottomEulerPoint c
  have hs : Continuous s := by
    change Continuous (fun x : ℝ => (((1 / 2 + c : ℝ) : ℂ) + x * I))
    fun_prop
  have hmaps : MapsTo s univ {z : ℂ | 0 < z.re} := by
    intro x _
    simp only [mem_setOf_eq, s, xiMassBottomEulerPoint_re]
    linarith
  have hderiv : Continuous (fun x : ℝ => archFactorDeriv (s x)) :=
    continuousOn_archFactorDeriv.comp_continuous hs (fun x => hmaps (mem_univ x))
  have hfactor : Continuous (fun x : ℝ => archFactor (s x)) :=
    archFactor_analyticOnNhd_re_pos.continuousOn.comp_continuous hs
      (fun x => hmaps (mem_univ x))
  have hfactor0 : ∀ x : ℝ, archFactor (s x) ≠ 0 := by
    intro x
    exact archFactor_ne_zero (xiMassBottomEulerPoint_ne_zero hhalf)
      (xiMassBottomEulerPoint_ne_one hhalf)
      (Gammaℝ_ne_zero_of_re_pos (by simp [s, xiMassBottomEulerPoint_re]; linarith))
  rw [show (fun x : ℝ => logDeriv archFactor (xiMassBottomEulerPoint c x)) =
      fun x : ℝ => archFactorDeriv (s x) / archFactor (s x) by
    funext x
    rw [logDeriv_apply, (hasDerivAt_archFactor_of_re_pos
      (by simp [xiMassBottomEulerPoint_re]; linarith)).deriv]]
  exact hderiv.div hfactor hfactor0

theorem continuous_xiMassBottomArchIntegrand {a c : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (τ : ℂ) :
    Continuous (xiMassBottomArchIntegrand a c τ) := by
  exact (continuous_xiMassBottomTest hhalf hca τ).mul
    (continuous_xiMassBottomArchLogDeriv hhalf)

/-- Digamma bound on an arbitrary fixed legal Euler line. -/
theorem norm_digamma_xiMassBottomEulerPoint_half_le
    {c x : ℝ} (hhalf : 1 / 2 < c)
    (hx : max 2 (1 / 2 + c) ≤ |x|) :
    ‖Complex.digamma (xiMassBottomEulerPoint c x / 2)‖ ≤
      |x| + GaloisForLFunctions.digammaVerticalLogConstant := by
  let σ : ℝ := 1 / 2 + c
  let t : ℝ := |x| / 2
  have hσ : 0 < σ / 2 := by dsimp only [σ]; linarith
  have ht1 : 1 ≤ t := by
    dsimp only [t]
    have := le_trans (le_max_left 2 (1 / 2 + c)) hx
    linarith
  have hσt : σ / 2 ≤ t := by
    dsimp only [σ, t]
    have := le_trans (le_max_right 2 (1 / 2 + c)) hx
    linarith
  have hbound := GaloisForLFunctions.norm_digamma_vertical_le_log hσ ht1 hσt
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hlog : Real.log t ≤ |x| := by
    have := Real.log_le_sub_one_of_pos ht
    dsimp only [t] at this ⊢
    linarith [abs_nonneg x]
  have hfinal : Real.log t + GaloisForLFunctions.digammaVerticalLogConstant ≤
      |x| + GaloisForLFunctions.digammaVerticalLogConstant := by linarith
  by_cases hx0 : 0 ≤ x
  · have harg : xiMassBottomEulerPoint c x / 2 =
        (((σ / 2 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) := by
      apply Complex.ext <;>
        simp [xiMassBottomEulerPoint, σ, t, abs_of_nonneg hx0,
          Complex.mul_re, Complex.mul_im]
    rw [harg]
    exact hbound.trans hfinal
  · have hxneg : x < 0 := lt_of_not_ge hx0
    have harg : xiMassBottomEulerPoint c x / 2 =
        (starRingEnd ℂ) ((((σ / 2 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I)) := by
      apply Complex.ext <;>
        simp [xiMassBottomEulerPoint, σ, t, abs_of_neg hxneg,
          Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im] <;> ring
    rw [harg, ReflectedDigammaAnomaly.digamma_conj, norm_conj]
    exact hbound.trans hfinal

/-- Fixed-line constant for the completed archimedean logarithmic derivative. -/
def xiMassBottomArchGrowthConstant (c : ℝ) : ℝ :=
  1 + 1 / (c - 1 / 2) + |Real.log Real.pi| / 2 +
    GaloisForLFunctions.digammaVerticalLogConstant / 2

theorem xiMassBottomArchGrowthConstant_nonneg {c : ℝ} (hhalf : 1 / 2 < c) :
    0 ≤ xiMassBottomArchGrowthConstant c := by
  unfold xiMassBottomArchGrowthConstant
  have hD : 0 ≤ GaloisForLFunctions.digammaVerticalLogConstant := by
    unfold GaloisForLFunctions.digammaVerticalLogConstant
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  positivity

theorem norm_logDeriv_archFactor_xiMassBottom_le
    {c x : ℝ} (hhalf : 1 / 2 < c)
    (hx : max 2 (1 / 2 + c) ≤ |x|) :
    ‖logDeriv archFactor (xiMassBottomEulerPoint c x)‖ ≤
      xiMassBottomArchGrowthConstant c + |x| / 2 := by
  let s : ℂ := xiMassBottomEulerPoint c x
  have hsre : s.re = 1 / 2 + c := xiMassBottomEulerPoint_re c x
  have hs0 : s ≠ 0 := xiMassBottomEulerPoint_ne_zero hhalf
  have hs1 : s ≠ 1 := xiMassBottomEulerPoint_ne_one hhalf
  have hsNorm : 1 ≤ ‖s‖ := by
    have hre : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
    rw [hsre, abs_of_pos (by linarith : 0 < 1 / 2 + c)] at hre
    linarith
  have hsSubNorm : c - 1 / 2 ≤ ‖s - 1‖ := by
    have hre : |(s - 1).re| ≤ ‖s - 1‖ := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, hsre, Complex.one_re] at hre
    have hc : 0 < c - 1 / 2 := by linarith
    rw [show 1 / 2 + c - 1 = c - 1 / 2 by ring, abs_of_pos hc] at hre
    exact hre
  have hInv : ‖1 / s‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (norm_pos_iff.mpr hs0)).2 hsNorm
  have hInvSub : ‖1 / (s - 1)‖ ≤ 1 / (c - 1 / 2) := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by linarith) hsSubNorm
  have hgamma : ‖GaloisForLFunctions.gammaRealLogConnection s‖ ≤
      |Real.log Real.pi| / 2 +
        (|x| + GaloisForLFunctions.digammaVerticalLogConstant) / 2 := by
    unfold GaloisForLFunctions.gammaRealLogConnection
    change ‖-((Real.log Real.pi : ℂ) / 2) + Complex.digamma (s / 2) / 2‖ ≤ _
    calc
      ‖-((Real.log Real.pi : ℂ) / 2) + Complex.digamma (s / 2) / 2‖ ≤
          ‖-((Real.log Real.pi : ℂ) / 2)‖ + ‖Complex.digamma (s / 2) / 2‖ :=
        norm_add_le _ _
      _ = |Real.log Real.pi| / 2 + ‖Complex.digamma (s / 2)‖ / 2 := by
        simp only [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_ofNat]
      _ ≤ _ := by
        have hdig := norm_digamma_xiMassBottomEulerPoint_half_le hhalf hx
        change ‖Complex.digamma (xiMassBottomEulerPoint c x / 2)‖ ≤ _ at hdig
        dsimp only [s]
        nlinarith
  have hclosed := logDeriv_archFactor_closed
    (s := s) (by rw [hsre]; linarith) hs0 hs1
  rw [hclosed]
  calc
    ‖1 / s + 1 / (s - 1) + GaloisForLFunctions.gammaRealLogConnection s‖ ≤
        ‖1 / s + 1 / (s - 1)‖ +
          ‖GaloisForLFunctions.gammaRealLogConnection s‖ := norm_add_le _ _
    _ ≤ ‖1 / s‖ + ‖1 / (s - 1)‖ +
          ‖GaloisForLFunctions.gammaRealLogConnection s‖ := by
      exact add_le_add (norm_add_le (1 / s : ℂ) (1 / (s - 1) : ℂ)) le_rfl
    _ ≤ 1 + 1 / (c - 1 / 2) +
        (|Real.log Real.pi| / 2 +
          (|x| + GaloisForLFunctions.digammaVerticalLogConstant) / 2) :=
      add_le_add (add_le_add hInv hInvSub) hgamma
    _ = xiMassBottomArchGrowthConstant c + |x| / 2 := by
      unfold xiMassBottomArchGrowthConstant
      ring

/-- The mass-weighted archimedean bottom edge is absolutely integrable at every legal depth. -/
theorem integrable_xiMassBottomArchIntegrand {a c : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Integrable (xiMassBottomArchIntegrand a c τ) := by
  let T : ℝ := max 2 (1 / 2 + c)
  let S : Set ℝ := {x : ℝ | T ≤ |x|}
  let E : ℝ := Real.exp (|τ.im| * c)
  let C : ℝ := xiMassBottomArchGrowthConstant c
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact xiMassBottomArchGrowthConstant_nonneg hhalf
  have hmajor : Integrable (fun x : ℝ =>
      (E * C) * Real.exp (-(τ.re * |x|)) +
        (E / 2) * (|x| * Real.exp (-(τ.re * |x|)))) :=
    ((integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hτ).const_mul (E * C)).add
      ((integrable_abs_mul_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hτ).const_mul (E / 2))
  have hS : MeasurableSet S := by
    dsimp only [S]
    exact measurableSet_le measurable_const continuous_abs.measurable
  have htail : IntegrableOn (xiMassBottomArchIntegrand a c τ) S := by
    refine hmajor.integrableOn.mono'
      (continuous_xiMassBottomArchIntegrand hhalf hca τ).aestronglyMeasurable.restrict ?_
    filter_upwards [self_mem_ae_restrict hS] with x hx
    have hm := norm_xiMassBottomTest_le hhalf hca hτ.le (x := x)
    have ha := norm_logDeriv_archFactor_xiMassBottom_le hhalf hx
    rw [xiMassBottomArchIntegrand, norm_mul]
    calc
      ‖xiMassBottomTest a c τ x‖ *
          ‖logDeriv archFactor (xiMassBottomEulerPoint c x)‖ ≤
        (E * Real.exp (-(τ.re * |x|))) * (C + |x| / 2) :=
          mul_le_mul hm ha (norm_nonneg _) (by positivity)
      _ = (E * C) * Real.exp (-(τ.re * |x|)) +
          (E / 2) * (|x| * Real.exp (-(τ.re * |x|))) := by ring
  have hcompact : IntegrableOn (xiMassBottomArchIntegrand a c τ) (Icc (-T) T) :=
    (continuous_xiMassBottomArchIntegrand hhalf hca τ).integrableOn_Icc
  have hcover : Icc (-T) T ∪ S = univ := by
    ext x
    simp only [mem_union, mem_Icc, mem_univ, iff_true, S, mem_setOf_eq]
    by_cases h : |x| ≤ T
    · exact Or.inl (abs_le.mp h)
    · exact Or.inr (by linarith)
  rw [← integrableOn_univ, ← hcover]
  exact hcompact.union htail

theorem xiMassBottomSourceIntegrand_eq (a c : ℝ) (τ : ℂ) (x : ℝ) :
    xiMassBottomSourceIntegrand a c τ x =
      -I * xiMassBottomPrimeIntegrand a c τ x +
        I * xiMassBottomArchIntegrand a c τ x := by
  unfold xiMassBottomSourceIntegrand xiMassBottomPrimeIntegrand
    xiMassBottomArchIntegrand
  ring

/-- Complete literal mass bottom source is absolutely integrable. -/
theorem integrable_xiMassBottomSourceIntegrand {a c : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Integrable (xiMassBottomSourceIntegrand a c τ) := by
  have hp := (integrable_xiMassBottomPrimeIntegrand hhalf hca hτ).const_mul (-I)
  have ha := (integrable_xiMassBottomArchIntegrand hhalf hca hτ).const_mul I
  exact (hp.add ha).congr (Filter.Eventually.of_forall fun x =>
    (xiMassBottomSourceIntegrand_eq a c τ x).symm)

/-- Symmetric truncations of the exact mass source converge to the complete Euler integral. -/
theorem tendsto_integral_xiMassBottomSourceIntegrand_atTop
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto (fun R : ℝ => ∫ x in -R..R, xiMassBottomSourceIntegrand a c τ x)
      atTop (𝓝 (∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x)) := by
  exact intervalIntegral_tendsto_integral
    (integrable_xiMassBottomSourceIntegrand hhalf hca hτ)
    (tendsto_neg_atBot_iff.mpr tendsto_id) tendsto_id

end

end RHTower

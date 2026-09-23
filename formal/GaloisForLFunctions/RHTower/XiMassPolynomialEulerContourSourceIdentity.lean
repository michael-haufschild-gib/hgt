import GaloisForLFunctions.RHTower.XiMassPolynomialFiniteContour
import GaloisForLFunctions.RHTower.XiMassEulerContourSourceIdentity
import GaloisForLFunctions.RHTower.XiMassPolynomialParabolicHeatTransfer
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments

/-!
# The polynomial-filtered mass source stays on one absolutely convergent Euler line

The even entire weight `P(z ^ (2 : ℕ)) ^ (2 : ℕ)` grows only polynomially on the bottom line `z = x - ci`,
while the analytic mass test decays exponentially there.  Hence the polynomial-filtered literal
prime–archimedean source is Bochner integrable, and the same rectangle exhaustion that proves the
unfiltered Euler-contour source identity proves its polynomial-filtered form.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Polynomial-filtered literal prime–archimedean source on the mass bottom edge. -/
def xiMassPolyBottomSourceIntegrand (P : Polynomial ℝ) (a c : ℝ) (τ : ℂ) (x : ℝ) : ℂ :=
  evalRealPolynomial P (((x : ℂ) - c * I) ^ (2 : ℕ)) ^ (2 : ℕ) * xiMassBottomSourceIntegrand a c τ x

/-- Normalized polynomial-filtered mass source on a legal Euler bottom line. -/
def normalizedXiMassPolyBottomEulerContour (P : Polynomial ℝ) (a c : ℝ) (τ : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * (2 * ∫ x : ℝ, xiMassPolyBottomSourceIntegrand P a c τ x)

/-- Normalized symmetric truncation of the polynomial-filtered mass Euler bottom source. -/
def normalizedXiMassPolyTruncatedBottomEulerContour
    (P : Polynomial ℝ) (a c R : ℝ) (τ : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * (2 * ∫ x in -R..R, xiMassPolyBottomSourceIntegrand P a c τ x)

private theorem one_add_abs_pow_le_two_pow (n : ℕ) (x : ℝ) :
    (1 + |x|) ^ n ≤ 2 ^ n * (1 + |x| ^ n) := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hxn : (0 : ℝ) ≤ |x| ^ n := by positivity
  rcases le_or_gt (|x|) 1 with h | h
  · have hstep : (1 + |x|) ^ n ≤ 2 ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    nlinarith
  · have hstep : (1 + |x|) ^ n ≤ (2 * |x|) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    rw [mul_pow] at hstep
    nlinarith

/-- Polynomial majorant constant for the even weight on the bottom line. -/
def xiMassPolyWeightConstant (P : Polynomial ℝ) (c : ℝ) : ℝ :=
  evalRealPolynomialCoeffSum (xiMassPolySquare P) * (1 + c) ^ (xiMassPolySquare P).natDegree *
    2 ^ (xiMassPolySquare P).natDegree

theorem xiMassPolyWeightConstant_nonneg (P : Polynomial ℝ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ xiMassPolyWeightConstant P c := by
  unfold xiMassPolyWeightConstant
  have := evalRealPolynomialCoeffSum_nonneg (xiMassPolySquare P)
  positivity

theorem norm_xiMassPolyBottomWeight_le (P : Polynomial ℝ) {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    ‖evalRealPolynomial P (((x : ℂ) - c * I) ^ (2 : ℕ)) ^ (2 : ℕ)‖ ≤
      xiMassPolyWeightConstant P c *
        (1 + |x| ^ (xiMassPolySquare P).natDegree) := by
  have hz : ‖((x : ℂ) - c * I)‖ ≤ |x| + c := by
    have hbound := norm_sub_le ((x : ℂ)) ((c : ℂ) * I)
    have h1 : ‖((x : ℂ))‖ = |x| := by simp
    have h2 : ‖((c : ℂ) * I)‖ = |c| := by simp
    rw [h1, h2, abs_of_nonneg hc] at hbound
    exact hbound
  have hrw : evalRealPolynomial P (((x : ℂ) - c * I) ^ (2 : ℕ)) ^ (2 : ℕ) =
      evalRealPolynomial (xiMassPolySquare P) ((x : ℂ) - c * I) :=
    (evalRealPolynomial_xiMassPolySquare P _).symm
  have habs0 : (0 : ℝ) ≤ |x| + c := by positivity
  have hstep := norm_evalRealPolynomial_le (xiMassPolySquare P) hz
  have hpoly := evalRealPolynomialNormBound_le_coeffSum_mul_pow (xiMassPolySquare P) habs0
    (le_refl (xiMassPolySquare P).natDegree)
  have hshift : (1 + (|x| + c)) ^ (xiMassPolySquare P).natDegree ≤
      (1 + c) ^ (xiMassPolySquare P).natDegree *
        (2 ^ (xiMassPolySquare P).natDegree *
          (1 + |x| ^ (xiMassPolySquare P).natDegree)) := by
    have hle : (1 + (|x| + c)) ≤ (1 + c) * (1 + |x|) := by nlinarith [abs_nonneg x, hc]
    calc (1 + (|x| + c)) ^ (xiMassPolySquare P).natDegree
        ≤ ((1 + c) * (1 + |x|)) ^ (xiMassPolySquare P).natDegree :=
          pow_le_pow_left₀ (by positivity) hle _
      _ = (1 + c) ^ (xiMassPolySquare P).natDegree *
            (1 + |x|) ^ (xiMassPolySquare P).natDegree := by rw [mul_pow]
      _ ≤ (1 + c) ^ (xiMassPolySquare P).natDegree *
            (2 ^ (xiMassPolySquare P).natDegree *
              (1 + |x| ^ (xiMassPolySquare P).natDegree)) := by
          exact mul_le_mul_of_nonneg_left (one_add_abs_pow_le_two_pow _ x) (by positivity)
  rw [hrw]
  calc ‖evalRealPolynomial (xiMassPolySquare P) ((x : ℂ) - c * I)‖
      ≤ evalRealPolynomialNormBound (xiMassPolySquare P) (|x| + c) := hstep
    _ ≤ evalRealPolynomialCoeffSum (xiMassPolySquare P) *
          (1 + (|x| + c)) ^ (xiMassPolySquare P).natDegree := hpoly
    _ ≤ evalRealPolynomialCoeffSum (xiMassPolySquare P) *
          ((1 + c) ^ (xiMassPolySquare P).natDegree *
            (2 ^ (xiMassPolySquare P).natDegree *
              (1 + |x| ^ (xiMassPolySquare P).natDegree))) :=
        mul_le_mul_of_nonneg_left hshift (evalRealPolynomialCoeffSum_nonneg _)
    _ = xiMassPolyWeightConstant P c * (1 + |x| ^ (xiMassPolySquare P).natDegree) := by
        unfold xiMassPolyWeightConstant
        ring

theorem continuous_xiMassBottomSourceIntegrand {a c : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (τ : ℂ) :
    Continuous (xiMassBottomSourceIntegrand a c τ) := by
  have heq : xiMassBottomSourceIntegrand a c τ =
      fun x : ℝ => -I * xiMassBottomPrimeIntegrand a c τ x +
        I * xiMassBottomArchIntegrand a c τ x :=
    funext (xiMassBottomSourceIntegrand_eq a c τ)
  rw [heq]
  exact (continuous_const.mul (continuous_xiMassBottomPrimeIntegrand hhalf hca τ)).add
    (continuous_const.mul (continuous_xiMassBottomArchIntegrand hhalf hca τ))

theorem continuous_xiMassPolyBottomSourceIntegrand (P : Polynomial ℝ) {a c : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (τ : ℂ) :
    Continuous (xiMassPolyBottomSourceIntegrand P a c τ) := by
  have hW : Continuous (fun x : ℝ => evalRealPolynomial P (((x : ℂ) - c * I) ^ (2 : ℕ)) ^ (2 : ℕ)) := by
    have hQ : Continuous (fun x : ℝ =>
        evalRealPolynomial (xiMassPolySquare P) ((x : ℂ) - c * I)) :=
      (continuous_evalRealPolynomial (xiMassPolySquare P)).comp (by fun_prop)
    exact hQ.congr fun x => evalRealPolynomial_xiMassPolySquare P _
  exact hW.mul (continuous_xiMassBottomSourceIntegrand hhalf hca τ)

theorem norm_xiMassBottomSourceIntegrand_le {a c x : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 ≤ τ.re)
    (hx : max 2 (1 / 2 + c) ≤ |x|) :
    ‖xiMassBottomSourceIntegrand a c τ x‖ ≤
      (Real.exp (|τ.im| * c) * Real.exp (-(τ.re * |x|))) *
        (xiMassBottomVonMangoldtBound c +
          (xiMassBottomArchGrowthConstant c + |x| / 2)) := by
  have hm := norm_xiMassBottomTest_le hhalf hca hτ (x := x)
  have hL := norm_xiMassBottomVonMangoldtLSeries_le (x := x) hhalf
  have hA := norm_logDeriv_archFactor_xiMassBottom_le hhalf hx
  have hfac : ‖-I *
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (xiMassBottomEulerPoint c x) -
        logDeriv archFactor (xiMassBottomEulerPoint c x))‖ ≤
      xiMassBottomVonMangoldtBound c +
        (xiMassBottomArchGrowthConstant c + |x| / 2) := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact le_trans (norm_sub_le _ _) (add_le_add hL hA)
  rw [xiMassBottomSourceIntegrand, norm_mul]
  exact mul_le_mul hm hfac (norm_nonneg _) (by positivity)

/-- The polynomial-filtered literal mass bottom source is absolutely integrable. -/
theorem integrable_xiMassPolyBottomSourceIntegrand (P : Polynomial ℝ) {a c : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Integrable (xiMassPolyBottomSourceIntegrand P a c τ) := by
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hhalf).le
  set D : ℕ := (xiMassPolySquare P).natDegree with hDEq
  set G : ℝ := xiMassPolyWeightConstant P c with hGEq
  set E : ℝ := Real.exp (|τ.im| * c) with hEEq
  set V : ℝ := xiMassBottomVonMangoldtBound c with hVEq
  set A : ℝ := xiMassBottomArchGrowthConstant c with hAEq
  let T : ℝ := max 2 (1 / 2 + c)
  let S : Set ℝ := {x : ℝ | T ≤ |x|}
  have hG : 0 ≤ G := xiMassPolyWeightConstant_nonneg P hc0
  have hE : 0 < E := Real.exp_pos _
  have hmajor : Integrable (fun x : ℝ =>
      (G * E * (V + A)) * (|x| ^ (0 : ℕ) * Real.exp (-τ.re * |x|)) +
      (G * E / 2) * (|x| ^ (1 : ℕ) * Real.exp (-τ.re * |x|)) +
      (G * E * (V + A)) * (|x| ^ D * Real.exp (-τ.re * |x|)) +
      (G * E / 2) * (|x| ^ (D + 1) * Real.exp (-τ.re * |x|))) := by
    exact ((((HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0
      hτ).const_mul (G * E * (V + A))).add
      ((HTGeometry.integrable_abs_pow_mul_exp_neg_abs 1
        hτ).const_mul (G * E / 2))).add
      ((HTGeometry.integrable_abs_pow_mul_exp_neg_abs D
        hτ).const_mul (G * E * (V + A)))).add
      ((HTGeometry.integrable_abs_pow_mul_exp_neg_abs (D + 1)
        hτ).const_mul (G * E / 2))
  have hS : MeasurableSet S := by
    dsimp only [S]
    exact measurableSet_le measurable_const continuous_abs.measurable
  have htail : IntegrableOn (xiMassPolyBottomSourceIntegrand P a c τ) S := by
    refine hmajor.integrableOn.mono'
      (continuous_xiMassPolyBottomSourceIntegrand P hhalf hca τ).aestronglyMeasurable.restrict ?_
    filter_upwards [self_mem_ae_restrict hS] with x hx
    have hxT : T ≤ |x| := hx
    have hw := norm_xiMassPolyBottomWeight_le P hc0 x
    have hsrc := norm_xiMassBottomSourceIntegrand_le hhalf hca hτ.le hxT
    have hexpEq : Real.exp (-(τ.re * |x|)) = Real.exp (-τ.re * |x|) := by
      rw [show -(τ.re * |x|) = -τ.re * |x| by ring]
    rw [xiMassPolyBottomSourceIntegrand, norm_mul]
    calc ‖evalRealPolynomial P (((x : ℂ) - c * I) ^ (2 : ℕ)) ^ (2 : ℕ)‖ *
          ‖xiMassBottomSourceIntegrand a c τ x‖
        ≤ (G * (1 + |x| ^ D)) *
            ((E * Real.exp (-(τ.re * |x|))) * (V + (A + |x| / 2))) := by
          refine mul_le_mul hw hsrc (norm_nonneg _) ?_
          positivity
      _ = (G * E * (V + A)) * (|x| ^ (0 : ℕ) * Real.exp (-τ.re * |x|)) +
          (G * E / 2) * (|x| ^ (1 : ℕ) * Real.exp (-τ.re * |x|)) +
          (G * E * (V + A)) * (|x| ^ D * Real.exp (-τ.re * |x|)) +
          (G * E / 2) * (|x| ^ (D + 1) * Real.exp (-τ.re * |x|)) := by
          rw [hexpEq, pow_succ]
          ring
  have hcompact : IntegrableOn (xiMassPolyBottomSourceIntegrand P a c τ) (Icc (-T) T) :=
    (continuous_xiMassPolyBottomSourceIntegrand P hhalf hca τ).integrableOn_Icc
  have hcover : Icc (-T) T ∪ S = univ := by
    ext x
    simp only [mem_union, mem_Icc, mem_univ, iff_true, S, mem_setOf_eq]
    by_cases h : |x| ≤ T
    · exact Or.inl (abs_le.mp h)
    · exact Or.inr (by linarith)
  rw [← integrableOn_univ, ← hcover]
  exact hcompact.union htail

/-- Symmetric truncations of the polynomial-filtered mass source converge to the complete Euler
integral. -/
theorem tendsto_integral_xiMassPolyBottomSourceIntegrand_atTop (P : Polynomial ℝ)
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto (fun R : ℝ => ∫ x in -R..R, xiMassPolyBottomSourceIntegrand P a c τ x)
      atTop (𝓝 (∫ x : ℝ, xiMassPolyBottomSourceIntegrand P a c τ x)) :=
  intervalIntegral_tendsto_integral
    (integrable_xiMassPolyBottomSourceIntegrand P hhalf hca hτ)
    (tendsto_neg_atBot_iff.mpr tendsto_id) tendsto_id

theorem tendsto_normalizedXiMassPolyTruncatedBottomEulerContour_atTop (P : Polynomial ℝ)
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto (fun R => normalizedXiMassPolyTruncatedBottomEulerContour P a c R τ)
      atTop (𝓝 (normalizedXiMassPolyBottomEulerContour P a c τ)) := by
  have hraw := tendsto_integral_xiMassPolyBottomSourceIntegrand_atTop P hhalf hca hτ
  have hscaled := (hraw.const_mul (2 : ℂ)).const_mul (2 * Real.pi * I)⁻¹
  simpa only [normalizedXiMassPolyTruncatedBottomEulerContour,
    normalizedXiMassPolyBottomEulerContour] using! hscaled

/-! ## Rectangle exhaustion and the polynomial-filtered source identity -/

theorem tendsto_symmetric_xiZeroCopy_xiMassPoly_sum_atTop (P : Polynomial ℝ)
    {a c : ℝ} (hhalf : 1 / 2 < c) (τ : ℂ)
    (hsum : Summable (fun q : XiZeroCopy =>
      ‖xiMassPolyAnalyticTest P a τ (xiSpectralPoint q)‖)) :
    Tendsto
      (fun R : ℝ =>
        ∑ q ∈ xiZeroCopyClosedRectangle
          (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I),
          xiMassPolyAnalyticTest P a τ (xiSpectralPoint q))
      atTop (𝓝 (∑' q : XiZeroCopy, xiMassPolyAnalyticTest P a τ (xiSpectralPoint q))) := by
  let f : XiZeroCopy → ℂ := fun q => xiMassPolyAnalyticTest P a τ (xiSpectralPoint q)
  have hf : Summable f := hsum.of_norm
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hball : Metric.ball (∑' q, f q) epsilon ∈ 𝓝 (∑' q, f q) :=
    Metric.ball_mem_nhds _ hepsilon
  have hevent : ∀ᶠ s : Finset XiZeroCopy in atTop,
      ∑ q ∈ s, f q ∈ Metric.ball (∑' q, f q) epsilon :=
    hf.hasSum.eventually hball
  rw [eventually_atTop] at hevent
  obtain ⟨t, ht⟩ := hevent
  let X : ℝ := 1 + ∑ q ∈ t, |(xiSpectralPoint q).re|
  refine ⟨X, fun R hRX => ?_⟩
  have hRpos : 0 < R := by
    have hsumNonneg : 0 ≤ ∑ q ∈ t, |(xiSpectralPoint q).re| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp only [X] at hRX
    linarith
  have hpacket : t ≤ xiZeroCopyClosedRectangle
      (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I) := by
    intro q hq
    rw [mem_xiZeroCopyClosedRectangle]
    apply Complex.mem_reProdIm.mpr
    have hqsum : |(xiSpectralPoint q).re| ≤ ∑ r ∈ t, |(xiSpectralPoint r).re| :=
      Finset.single_le_sum (fun r _ => abs_nonneg (xiSpectralPoint r).re) hq
    have hqbound : |(xiSpectralPoint q).re| < R := by
      dsimp only [X] at hRX
      linarith
    have him := xiSpectralPoint_im_mem_openHalf q
    constructor
    · rw [uIcc_of_le (by simp; linarith)]
      simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, zero_mul,
        mul_zero, sub_zero, add_re, add_zero]
      constructor <;> linarith [neg_le_abs (xiSpectralPoint q).re,
        le_abs_self (xiSpectralPoint q).re]
    · rw [uIcc_of_le (by simp; linarith)]
      simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, zero_mul,
        mul_one, zero_sub, add_im, zero_add]
      constructor <;> linarith
  have hnear := ht
    (xiZeroCopyClosedRectangle
      (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I)) hpacket
  rw [Metric.mem_ball] at hnear
  simpa only [f] using hnear

private theorem xiMassPolyLeftVertical_nonzero_of_avoiding
    (R y : ℝ) (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    XiC (((-R : ℝ) : ℂ) + y * I) ≠ 0 := by
  intro hzero
  have hnegzero : XiC (-((((-R : ℝ) : ℂ) + y * I))) = 0 := by
    rw [XiC_even]
    exact hzero
  have hpoint : -((((-R : ℝ) : ℂ) + y * I)) = (R : ℂ) + (-y) * I := by
    push_cast
    ring
  rw [hpoint] at hnegzero
  exact XiC_ne_zero_on_avoiding_vertical R (-y) havoid
    (by simpa only [Complex.ofReal_neg] using hnegzero)

/-- On each divisor-avoiding radius the finite polynomial-filtered mass spectrum equals the
normalized truncated source plus the normalized right-edge error. -/
theorem xiMassPolyFiniteRectangleSum_eq_truncatedBottom_add_vertical (P : Polynomial ℝ)
    {a c R : ℝ} (ha : 0 < a) (hhalf : 1 / 2 < c) (hca : c < a) (hR : 0 < R)
    (τ : ℂ) (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    (∑ q ∈ xiZeroCopyClosedRectangle
        (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I),
        xiMassPolyAnalyticTest P a τ (xiSpectralPoint q)) =
      normalizedXiMassPolyTruncatedBottomEulerContour P a c R τ +
        (2 * Real.pi * I)⁻¹ * 2 * I *
          (∫ y in -c..c,
            xiMassPolyAnalyticTest P a τ ((R : ℂ) + y * I) *
              logDeriv XiC ((R : ℂ) + y * I)) := by
  have hright : ∀ y ∈ uIcc (-c) c, XiC ((R : ℂ) + y * I) ≠ 0 := by
    intro y _
    exact XiC_ne_zero_on_avoiding_vertical R y havoid
  have hleft : ∀ y ∈ uIcc (-c) c, XiC (((-R : ℝ) : ℂ) + y * I) ≠ 0 := by
    intro y _
    exact xiMassPolyLeftVertical_nonzero_of_avoiding R y havoid
  have hfinite := xiMassPolyFiniteSpectralSum_eq_bottomPrimeArch_add_vertical
    P ha hhalf hca hR τ hright hleft
  have hsource : (∫ x in -R..R,
      xiMassPolyAnalyticTest P a τ ((x : ℂ) - c * I) *
        (-I *
          (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (((1 / 2 + c : ℝ) : ℂ) + x * I) -
            logDeriv archFactor (((1 / 2 + c : ℝ) : ℂ) + x * I)))) =
      ∫ x in -R..R, xiMassPolyBottomSourceIntegrand P a c τ x := by
    apply intervalIntegral.integral_congr
    intro x _
    show xiMassPolyAnalyticTest P a τ ((x : ℂ) - c * I) *
        (-I *
          (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (((1 / 2 + c : ℝ) : ℂ) + x * I) -
            logDeriv archFactor (((1 / 2 + c : ℝ) : ℂ) + x * I))) =
      xiMassPolyBottomSourceIntegrand P a c τ x
    rw [xiMassPolyBottomSourceIntegrand, xiMassBottomSourceIntegrand,
      xiMassPolyAnalyticTest, xiMassBottomTest, xiMassBottomEulerPoint]
    ring
  rw [hsource] at hfinite
  have hnorm : (2 * Real.pi * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  calc
    (∑ q ∈ xiZeroCopyClosedRectangle
        (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I),
        xiMassPolyAnalyticTest P a τ (xiSpectralPoint q)) =
      (2 * Real.pi * I)⁻¹ *
        (2 * Real.pi * I *
          ∑ q ∈ xiZeroCopyClosedRectangle
            (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I),
            xiMassPolyAnalyticTest P a τ (xiSpectralPoint q)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hnorm, one_mul]
    _ = (2 * Real.pi * I)⁻¹ *
        (2 * ((∫ x in -R..R, xiMassPolyBottomSourceIntegrand P a c τ x) +
          I • (∫ y in -c..c,
            xiMassPolyAnalyticTest P a τ ((R : ℂ) + y * I) *
              logDeriv XiC ((R : ℂ) + y * I)))) := by rw [hfinite]
    _ = normalizedXiMassPolyTruncatedBottomEulerContour P a c R τ +
        (2 * Real.pi * I)⁻¹ * 2 * I *
          (∫ y in -c..c,
            xiMassPolyAnalyticTest P a τ ((R : ℂ) + y * I) *
              logDeriv XiC ((R : ℂ) + y * I)) := by
      unfold normalizedXiMassPolyTruncatedBottomEulerContour
      simp only [smul_eq_mul]
      ring

/-- **Polynomial-filtered mass--Xi Euler-contour source identity.**  Whenever the filtered
spectral family is absolutely summable, its complete sum is the normalized absolutely convergent
von-Mangoldt minus archimedean bottom integral of the same polynomial-filtered test. -/
theorem tsum_xiMassPolyAnalyticTest_eq_normalizedBottomEulerContour (P : Polynomial ℝ)
    {a c : ℝ} (ha : 0 < a) (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re)
    (hsum : Summable (fun q : XiZeroCopy =>
      ‖xiMassPolyAnalyticTest P a τ (xiSpectralPoint q)‖)) :
    (∑' q : XiZeroCopy, xiMassPolyAnalyticTest P a τ (xiSpectralPoint q)) =
      normalizedXiMassPolyBottomEulerContour P a c τ := by
  let W : ℂ := ∑' q : XiZeroCopy, xiMassPolyAnalyticTest P a τ (xiSpectralPoint q)
  let B : ℂ := normalizedXiMassPolyBottomEulerContour P a c τ
  let Sfun : ℝ → ℂ := fun R =>
    ∑ q ∈ xiZeroCopyClosedRectangle
      (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I),
      xiMassPolyAnalyticTest P a τ (xiSpectralPoint q)
  let T : ℝ → ℂ := fun R => normalizedXiMassPolyTruncatedBottomEulerContour P a c R τ
  let V : ℝ → ℂ := fun R =>
    ∫ y in -c..c,
      xiMassPolyAnalyticTest P a τ ((R : ℂ) + y * I) * logDeriv XiC ((R : ℂ) + y * I)
  let k : ℂ := (2 * Real.pi * I)⁻¹ * 2 * I
  change W = B
  by_contra hWB
  have hd : 0 < dist W B := dist_pos.mpr hWB
  let epsilon : ℝ := dist W B / 4
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  have hS : Tendsto Sfun atTop (𝓝 W) := by
    simpa only [Sfun, W] using
      tendsto_symmetric_xiZeroCopy_xiMassPoly_sum_atTop P hhalf τ hsum
  have hT : Tendsto T atTop (𝓝 B) := by
    simpa only [T, B] using
      tendsto_normalizedXiMassPolyTruncatedBottomEulerContour_atTop P hhalf hca hτ
  obtain ⟨XS, hXS⟩ := (Metric.tendsto_atTop.mp hS) epsilon hepsilon
  obtain ⟨XT, hXT⟩ := (Metric.tendsto_atTop.mp hT) epsilon hepsilon
  let delta : ℝ := epsilon / (‖k‖ + 1)
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  obtain ⟨R, hRX, hR, havoid, hVsmall⟩ :=
    exists_large_integral_xiMassPoly_mul_logDeriv_XiC_norm_lt
      (xiMassPolySquare P) ha hhalf hca hτ (max XS XT) hdelta
  have hRXS : XS ≤ R := le_trans (le_max_left XS XT) (le_of_lt hRX)
  have hRXT : XT ≤ R := le_trans (le_max_right XS XT) (le_of_lt hRX)
  have hspec : dist (Sfun R) W < epsilon := hXS R hRXS
  have hbottom : dist (T R) B < epsilon := hXT R hRXT
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hVeq : V R = ∫ y in -c..c, evalRealPolynomial (xiMassPolySquare P) ((R : ℂ) + y * I) *
      (xiMassAnalyticTest a τ ((R : ℂ) + y * I) * logDeriv XiC ((R : ℂ) + y * I)) := by
    dsimp only [V]
    apply intervalIntegral.integral_congr
    intro y _
    show xiMassPolyAnalyticTest P a τ ((R : ℂ) + y * I) * logDeriv XiC ((R : ℂ) + y * I) =
      evalRealPolynomial (xiMassPolySquare P) ((R : ℂ) + y * I) *
        (xiMassAnalyticTest a τ ((R : ℂ) + y * I) * logDeriv XiC ((R : ℂ) + y * I))
    rw [xiMassPolyAnalyticTest, evalRealPolynomial_xiMassPolySquare]
    ring
  have hVnorm : ‖V R‖ < delta := by rw [hVeq]; exact hVsmall
  have hfinite : Sfun R = T R + k * V R := by
    simpa only [Sfun, T, k, V, mul_assoc] using
      xiMassPolyFiniteRectangleSum_eq_truncatedBottom_add_vertical
        P ha hhalf hca hRpos τ havoid
  have hST : dist (Sfun R) (T R) < epsilon := by
    calc
      dist (Sfun R) (T R) = ‖k * V R‖ := by
        rw [hfinite, dist_eq_norm]
        congr 1
        ring
      _ = ‖k‖ * ‖V R‖ := norm_mul _ _
      _ ≤ (‖k‖ + 1) * ‖V R‖ :=
        mul_le_mul_of_nonneg_right (by linarith [norm_nonneg k]) (norm_nonneg _)
      _ < (‖k‖ + 1) * delta := mul_lt_mul_of_pos_left hVnorm (by positivity)
      _ = epsilon := by
        dsimp only [delta]
        field_simp
  have htri := dist_triangle4 W (Sfun R) (T R) B
  rw [dist_comm W (Sfun R)] at htri
  dsimp only [epsilon] at hepsilon hspec hST hbottom
  nlinarith

/-! ## The literal parabolic Euler transfer -/

theorem xiMassPolynomialParabolicTerm_eq_expScale (P : Polynomial ℝ) (a t : ℝ)
    (q : XiZeroCopy) :
    xiMassPolynomialParabolicTerm P a t q =
      Complex.exp (((2 * a ^ (2 : ℕ) * t : ℝ) : ℂ)) *
        xiMassPolyAnalyticTest P a (((2 * a * t : ℝ) : ℂ)) (xiSpectralPoint q) := by
  rw [xiMassPolynomialParabolicTerm_eq_restEnergyRenormalized, xiMassPolyAnalyticTest]
  ring

theorem summable_norm_xiMassPolyAnalyticTest_parabolic (P : Polynomial ℝ) {a t : ℝ}
    (ha : 1 ≤ a) (ht : 0 < t) :
    Summable (fun q : XiZeroCopy =>
      ‖xiMassPolyAnalyticTest P a (((2 * a * t : ℝ) : ℂ)) (xiSpectralPoint q)‖) := by
  have hsummableTerm : Summable (fun q : XiZeroCopy =>
      ‖xiMassPolynomialParabolicTerm P a t q‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => norm_xiMassPolynomialParabolicTerm_le_poissonMajorant P ha ht q)
      (summable_norm_evalRealPolynomial_sq_mul_xiPoissonWeight P
        (show (0 : ℝ) < t / 2 by linarith))
  have hscale := hsummableTerm.mul_left (Real.exp (-(2 * a ^ (2 : ℕ) * t)))
  refine hscale.congr (fun q => ?_)
  rw [xiMassPolynomialParabolicTerm_eq_expScale, norm_mul, Complex.norm_exp,
    Complex.ofReal_re, ← mul_assoc, ← Real.exp_add]
  simp

/-- **(24.118)** The rest-energy-renormalized polynomial-filtered mass trace is exactly the
normalized absolutely convergent polynomial-filtered Euler bottom integral. -/
theorem xiMassPolynomialParabolicTrace_eq_normalizedBottomEulerContour (P : Polynomial ℝ)
    {a c t : ℝ} (ha : 1 ≤ a) (hhalf : 1 / 2 < c) (hca : c < a) (ht : 0 < t) :
    xiMassPolynomialParabolicTrace P a t =
      Complex.exp (((2 * a ^ (2 : ℕ) * t : ℝ) : ℂ)) *
        normalizedXiMassPolyBottomEulerContour P a c (((2 * a * t : ℝ) : ℂ)) := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hτ : 0 < (((2 * a * t : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    positivity
  have hsum := summable_norm_xiMassPolyAnalyticTest_parabolic P ha ht
  rw [xiMassPolynomialParabolicTrace]
  have hshift : (∑' q : XiZeroCopy, xiMassPolynomialParabolicTerm P a t q) =
      Complex.exp (((2 * a ^ (2 : ℕ) * t : ℝ) : ℂ)) *
        ∑' q : XiZeroCopy,
          xiMassPolyAnalyticTest P a (((2 * a * t : ℝ) : ℂ)) (xiSpectralPoint q) := by
    rw [← tsum_mul_left]
    exact tsum_congr (xiMassPolynomialParabolicTerm_eq_expScale P a t)
  rw [hshift,
    tsum_xiMassPolyAnalyticTest_eq_normalizedBottomEulerContour P ha0 hhalf hca hτ hsum]

/-- **(24.118), literal form.**  Every renormalized polynomial-filtered mass trace is one
absolutely convergent Euler-line integral of the literal prime--archimedean source. -/
theorem xiMassPolynomialParabolicTrace_eq_literalEulerLine (P : Polynomial ℝ)
    {a c t : ℝ} (ha : 1 ≤ a) (hhalf : 1 / 2 < c) (hca : c < a) (ht : 0 < t) :
    xiMassPolynomialParabolicTrace P a t =
      (2 * Real.pi * I)⁻¹ *
        (2 * ∫ x : ℝ,
          evalRealPolynomial P (((x : ℂ) - c * I) ^ (2 : ℕ)) ^ (2 : ℕ) *
            (Complex.exp (((2 * a ^ (2 : ℕ) * t : ℝ) : ℂ)) *
              xiMassAnalyticTest a (((2 * a * t : ℝ) : ℂ)) ((x : ℂ) - c * I)) *
            (-I *
              (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                  (((1 / 2 + c : ℝ) : ℂ) + x * I) -
                logDeriv archFactor (((1 / 2 + c : ℝ) : ℂ) + x * I)))) := by
  rw [xiMassPolynomialParabolicTrace_eq_normalizedBottomEulerContour P ha hhalf hca ht,
    normalizedXiMassPolyBottomEulerContour]
  rw [show Complex.exp (((2 * a ^ (2 : ℕ) * t : ℝ) : ℂ)) *
      ((2 * Real.pi * I)⁻¹ *
        (2 * ∫ x : ℝ, xiMassPolyBottomSourceIntegrand P a c (((2 * a * t : ℝ) : ℂ)) x)) =
      (2 * Real.pi * I)⁻¹ *
        (2 * (Complex.exp (((2 * a ^ (2 : ℕ) * t : ℝ) : ℂ)) *
          ∫ x : ℝ, xiMassPolyBottomSourceIntegrand P a c (((2 * a * t : ℝ) : ℂ)) x)) by ring]
  congr 2
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [xiMassPolyBottomSourceIntegrand, xiMassBottomSourceIntegrand, xiMassBottomTest,
    xiMassBottomEulerPoint]
  ring

end

end RHTower

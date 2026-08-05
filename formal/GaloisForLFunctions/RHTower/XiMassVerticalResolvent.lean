import GaloisForLFunctions.RHTower.XiGuinandWeilVerticalCauchyScaled
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularVerticalResolvent
import GaloisForLFunctions.RHTower.XiMassAnalyticTest

/-!
# Integrated Xi resolvent decay for the analytic mass test

The mass test has exponential decay on every closed substrip of its branch strip.  Combined with
the depth-parametric gap-free Cauchy estimate, this gives an integrated per-divisor bound uniform
in horizontal proximity to Xi zeros.  Reciprocal `3/2` and reciprocal-square divisor moments then
sum the near and far spectrum without a zero-density estimate.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- One relative-resolvent copy multiplied by the analytic mass test on the right vertical edge. -/
def xiMassVerticalRawTerm (a : ℝ) (τ : ℂ) (R : ℝ) (q : XiZeroCopy) (y : ℝ) : ℂ :=
  let z : ℂ := (R : ℂ) + y * I
  xiMassAnalyticTest a τ z *
    (-z / (xiSpectralPoint q * (xiSpectralPoint q - z)))

/-- Uniform mass-test envelope on the depth-`c` right edge. -/
def xiMassVerticalEnvelope (c : ℝ) (τ : ℂ) (R : ℝ) : ℝ :=
  Real.exp (-τ.re * R + |τ.im| * c)

/-- Gap-free integrated numerator for one divisor copy. -/
def xiMassVerticalIntegratedNumerator (c : ℝ) (τ : ℂ) (R : ℝ) : ℝ :=
  xiMassVerticalEnvelope c τ R *
    ((R + c) * xiVerticalCauchyKernelBoundAt c +
      (2 * c) * (‖τ‖ * (R + c) ^ 2 + 1))

theorem xiMassVerticalEnvelope_pos (c : ℝ) (τ : ℂ) (R : ℝ) :
    0 < xiMassVerticalEnvelope c τ R := by
  exact Real.exp_pos _

theorem xiMassVerticalIntegratedNumerator_nonneg
    {c R : ℝ} (hc : 1 / 2 < c) (hR : 0 ≤ R) (τ : ℂ) :
    0 ≤ xiMassVerticalIntegratedNumerator c τ R := by
  unfold xiMassVerticalIntegratedNumerator
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hc).le
  have hK := xiVerticalCauchyKernelBoundAt_nonneg hc
  exact mul_nonneg (xiMassVerticalEnvelope_pos c τ R).le
    (add_nonneg (mul_nonneg (by linarith) hK)
      (mul_nonneg (mul_nonneg (by positivity) hc0)
        (add_nonneg (mul_nonneg (norm_nonneg τ) (sq_nonneg _)) (by norm_num))))

private theorem norm_massVerticalPoint_le {R c y : ℝ}
    (hR : 0 ≤ R) (hy : |y| ≤ c) :
    ‖(R : ℂ) + y * I‖ ≤ R + c := by
  calc
    ‖(R : ℂ) + y * I‖ ≤ ‖(R : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
    _ = |R| + |y| := by simp
    _ = R + |y| := by rw [abs_of_nonneg hR]
    _ ≤ R + c := by simpa [add_comm] using add_le_add_left hy R

private theorem massVerticalPoint_mem_strip
    {a c R y : ℝ} (hca : c < a) (hy : |y| ≤ c) :
    ((R : ℂ) + y * I) ∈ xiMassStrip a := by
  change |(((R : ℂ) + y * I)).im| < a
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, zero_mul,
    mul_one, zero_add]
  simpa using hy.trans_lt hca

/-- The integrated contribution of one Xi divisor copy is exponentially small times `1/|p|`,
uniformly even when the vertical edge approaches the pole horizontally. -/
theorem norm_integral_xiMassVerticalRawTerm_le
    {a c R : ℝ} (ha : 0 < a) (hc : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (hR : 1 ≤ R) (q : XiZeroCopy)
    (havoid : R ≠ (xiSpectralPoint q).re) :
    ‖∫ y in -c..c, xiMassVerticalRawTerm a τ R q y‖ ≤
      xiMassVerticalIntegratedNumerator c τ R / ‖xiSpectralPoint q‖ := by
  let p : ℂ := xiSpectralPoint q
  let z : ℝ → ℂ := fun y => (R : ℂ) + y * I
  let g : ℂ → ℂ := xiMassAnalyticTest a τ
  let h : ℝ → ℂ := fun y => g (z y) * z y / p
  let E : ℝ := xiMassVerticalEnvelope c τ R
  let M : ℝ := E * (‖τ‖ * (R + c) ^ 2 + 1) / ‖p‖
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hp0 : p ≠ 0 := xiSpectralPoint_ne_zero q
  have hpNorm : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  have hpim := xiSpectralPoint_im_mem_openHalf q
  have hpimAbs : |p.im| ≤ c := by
    rw [abs_le]
    constructor <;> linarith [hpim.1, hpim.2]
  have hzMem : ∀ y ∈ Icc (-c) c, z y ∈ xiMassStrip a := by
    intro y hy
    exact massVerticalPoint_mem_strip hca ((abs_le).2 hy)
  have hzDeriv (y : ℝ) : HasDerivAt z I y := by
    dsimp only [z]
    have hmul : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I y := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
    simpa using hmul.const_add (R : ℂ)
  have hgDeriv (y : ℝ) (hy : y ∈ Icc (-c) c) : HasDerivAt (fun y => g (z y))
      ((-τ * (z y / xiMassAnalyticSqrt a (z y)) * g (z y)) * I) y := by
    exact (hasDerivAt_xiMassAnalyticTest ha τ (hzMem y hy)).comp y (hzDeriv y)
  have hhDeriv (y : ℝ) (hy : y ∈ Icc (-c) c) : HasDerivAt h
      ((((-τ * (z y / xiMassAnalyticSqrt a (z y)) * g (z y)) * I) * z y +
          g (z y) * I) / p) y := by
    dsimp only [h]
    exact ((hgDeriv y hy).mul (hzDeriv y)).div_const p
  have hE : 0 < E := xiMassVerticalEnvelope_pos c τ R
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hgValue : ∀ y ∈ Icc (-c) c, ‖g (z y)‖ ≤ E := by
    intro y hy
    have hyAbs : |y| ≤ c := (abs_le).2 hy
    have hraw := norm_xiMassAnalyticTest_le ha hτ.le (hzMem y hy)
    calc
      ‖g (z y)‖ ≤ Real.exp (-τ.re * |(z y).re| + |τ.im| * |(z y).im|) :=
        hraw
      _ ≤ E := by
        dsimp only [E, xiMassVerticalEnvelope]
        rw [Real.exp_le_exp]
        have hzre : |(z y).re| = R := by
          dsimp only [z]
          simp [abs_of_pos hRp]
        have hzim : |(z y).im| = |y| := by
          dsimp only [z]
          simp
        rw [hzre, hzim]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hyAbs (abs_nonneg τ.im))
  have hdiff : ∀ y ∈ Icc (-c) c, DifferentiableAt ℝ h y := by
    intro y hy
    exact (hhDeriv y hy).differentiableAt
  have hderiv : ∀ y ∈ Icc (-c) c, ‖deriv h y‖ ≤ M := by
    intro y hy
    have hyAbs : |y| ≤ c := (abs_le).2 hy
    have hzNorm := norm_massVerticalPoint_le hR0 hyAbs
    have hsqrtRe := abs_re_le_xiMassAnalyticSqrt_re a (z y)
    have hsqrtNorm : 1 ≤ ‖xiMassAnalyticSqrt a (z y)‖ := by
      have hreNorm := Complex.abs_re_le_norm (xiMassAnalyticSqrt a (z y))
      have hzre : |(z y).re| = R := by
        dsimp only [z]
        simp [abs_of_pos hRp]
      rw [hzre] at hsqrtRe
      exact hR.trans (hsqrtRe.trans ((le_abs_self _).trans hreNorm))
    have hratio : ‖z y / xiMassAnalyticSqrt a (z y)‖ ≤ R + c := by
      rw [norm_div]
      exact (div_le_self (norm_nonneg (z y)) hsqrtNorm).trans hzNorm
    have htest := hgValue y hy
    rw [(hhDeriv y hy).deriv, norm_div]
    calc
      ‖(((-τ * (z y / xiMassAnalyticSqrt a (z y)) * g (z y)) * I) * z y +
          g (z y) * I)‖ / ‖p‖ ≤
          ((‖τ‖ * (R + c) * E) * (R + c) + E) / ‖p‖ := by
        apply div_le_div_of_nonneg_right _ (norm_nonneg p)
        calc
          ‖(((-τ * (z y / xiMassAnalyticSqrt a (z y)) * g (z y)) * I) * z y +
              g (z y) * I)‖ ≤
              ‖((-τ * (z y / xiMassAnalyticSqrt a (z y)) * g (z y)) * I) *
                z y‖ + ‖g (z y) * I‖ := norm_add_le _ _
          _ = (‖τ‖ * ‖z y / xiMassAnalyticSqrt a (z y)‖ * ‖g (z y)‖) *
                ‖z y‖ + ‖g (z y)‖ := by simp [mul_assoc]
          _ ≤ (‖τ‖ * (R + c) * E) * (R + c) + E := by
            gcongr
      _ = M := by
        dsimp only [M]
        ring
  have hhValue : ‖h p.im‖ ≤ E * (R + c) / ‖p‖ := by
    have hpMem : p.im ∈ Icc (-c) c := (abs_le).mp hpimAbs
    dsimp only [h]
    rw [norm_div, norm_mul]
    apply div_le_div_of_nonneg_right _ (norm_nonneg p)
    exact mul_le_mul (hgValue p.im hpMem)
      (norm_massVerticalPoint_le hR0 hpimAbs) (norm_nonneg _) hE.le
  have hweighted := norm_integral_mul_vertical_cauchyKernel_le_at
    hc hM hdiff hderiv hpim (R := R) (by simpa only [p] using havoid)
  have hrewrite : ∀ y : ℝ,
      xiMassVerticalRawTerm a τ R q y = h y * ((z y - p)⁻¹) := by
    intro y
    have hzp : z y - p ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      simp only [z, p, sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        zero_mul, mul_zero, sub_zero, add_zero, zero_re] at hre
      exact havoid (sub_eq_zero.mp hre)
    dsimp only [xiMassVerticalRawTerm, h, g, z, p]
    rw [show xiSpectralPoint q - ((R : ℂ) + y * I) =
        -(((R : ℂ) + y * I) - xiSpectralPoint q) by ring,
      mul_neg, div_neg]
    simp only [neg_div, neg_neg]
    field_simp [hp0, hzp]
  calc
    ‖∫ y in -c..c, xiMassVerticalRawTerm a τ R q y‖ =
        ‖∫ y in -c..c, h y * ((z y - p)⁻¹)‖ := by
      congr 1
      apply integral_congr
      intro y _
      exact hrewrite y
    _ ≤ ‖h p.im‖ * xiVerticalCauchyKernelBoundAt c + (2 * c) * M := hweighted
    _ ≤ (E * (R + c) / ‖p‖) * xiVerticalCauchyKernelBoundAt c +
          (2 * c) * M := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hhValue (xiVerticalCauchyKernelBoundAt_nonneg hc)) le_rfl
    _ = xiMassVerticalIntegratedNumerator c τ R / ‖xiSpectralPoint q‖ := by
      dsimp only [M, E, p]
      unfold xiMassVerticalIntegratedNumerator
      field_simp

/-- Far divisor copies gain a reciprocal-square bound pointwise. -/
theorem norm_xiMassVerticalRawTerm_le_inv_sq
    {a c R : ℝ} (ha : 0 < a) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re)
    (hR : 1 ≤ R) (hc0 : 0 ≤ c) (q : XiZeroCopy)
    (hfar : 3 * (R + c) ≤ ‖xiSpectralPoint q‖)
    {y : ℝ} (hy : |y| ≤ c) :
    ‖xiMassVerticalRawTerm a τ R q y‖ ≤
      ((3 / 2 : ℝ) * xiMassVerticalEnvelope c τ R * (R + c)) /
        ‖xiSpectralPoint q‖ ^ 2 := by
  let p : ℂ := xiSpectralPoint q
  let z : ℂ := (R : ℂ) + y * I
  let E : ℝ := xiMassVerticalEnvelope c τ R
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hRc : 0 < R + c := by linarith
  have hp : 0 < ‖p‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hzMem : z ∈ xiMassStrip a := massVerticalPoint_mem_strip hca hy
  have hzNorm : ‖z‖ ≤ R + c := norm_massVerticalPoint_le hR0 hy
  have hg0 := norm_xiMassAnalyticTest_le ha hτ.le hzMem
  have hg : ‖xiMassAnalyticTest a τ z‖ ≤ E := by
    calc
      _ ≤ Real.exp (-τ.re * |z.re| + |τ.im| * |z.im|) := hg0
      _ ≤ E := by
        dsimp only [E, xiMassVerticalEnvelope]
        rw [Real.exp_le_exp]
        have hzre : |z.re| = R := by dsimp only [z]; simp [abs_of_pos hRp]
        have hzim : |z.im| = |y| := by dsimp only [z]; simp
        rw [hzre, hzim]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hy (abs_nonneg τ.im))
  have hzThird : ‖z‖ ≤ ‖p‖ / 3 := by linarith
  have hdiff0 := norm_sub_norm_le p z
  have hdiff : (2 / 3 : ℝ) * ‖p‖ ≤ ‖p - z‖ := by linarith
  have hdiffPos : 0 < ‖p - z‖ := lt_of_lt_of_le (mul_pos (by norm_num) hp) hdiff
  dsimp only [xiMassVerticalRawTerm, z, p]
  rw [norm_mul, norm_div, norm_neg, norm_mul]
  calc
    ‖xiMassAnalyticTest a τ z‖ * (‖z‖ / (‖p‖ * ‖p - z‖)) ≤
        E * ((R + c) / (‖p‖ * ‖p - z‖)) := by
      exact mul_le_mul hg
        (div_le_div_of_nonneg_right hzNorm (mul_nonneg hp.le hdiffPos.le))
        (div_nonneg (norm_nonneg z) (mul_nonneg hp.le hdiffPos.le))
        (xiMassVerticalEnvelope_pos c τ R).le
    _ ≤ E * ((R + c) / (‖p‖ * ((2 / 3 : ℝ) * ‖p‖))) := by
      apply mul_le_mul_of_nonneg_left _ (xiMassVerticalEnvelope_pos c τ R).le
      apply div_le_div_of_nonneg_left hRc.le
        (mul_pos hp (mul_pos (by norm_num) hp))
      exact mul_le_mul_of_nonneg_left hdiff hp.le
    _ = ((3 / 2 : ℝ) * E * (R + c)) / ‖p‖ ^ 2 := by
      field_simp

/-- Integrated far-copy reciprocal-square bound. -/
theorem norm_integral_xiMassVerticalRawTerm_le_inv_sq
    {a c R : ℝ} (ha : 0 < a) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re)
    (hR : 1 ≤ R) (hc0 : 0 ≤ c) (q : XiZeroCopy)
    (hfar : 3 * (R + c) ≤ ‖xiSpectralPoint q‖) :
    ‖∫ y in -c..c, xiMassVerticalRawTerm a τ R q y‖ ≤
      (3 * c * xiMassVerticalEnvelope c τ R * (R + c)) /
        ‖xiSpectralPoint q‖ ^ 2 := by
  have hpoint : ∀ y ∈ uIoc (-c) c,
      ‖xiMassVerticalRawTerm a τ R q y‖ ≤
        ((3 / 2 : ℝ) * xiMassVerticalEnvelope c τ R * (R + c)) /
          ‖xiSpectralPoint q‖ ^ 2 := by
    intro y hy
    have hyIoc : y ∈ Ioc (-c) c := by
      simpa [uIoc_of_le (by linarith : -c ≤ c)] using hy
    have hyAbs : |y| ≤ c := (abs_le).2 ⟨hyIoc.1.le, hyIoc.2⟩
    exact norm_xiMassVerticalRawTerm_le_inv_sq ha hca hτ hR hc0 q hfar hyAbs
  calc
    ‖∫ y in -c..c, xiMassVerticalRawTerm a τ R q y‖ ≤
        (((3 / 2 : ℝ) * xiMassVerticalEnvelope c τ R * (R + c)) /
          ‖xiSpectralPoint q‖ ^ 2) * |c - (-c)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (3 * c * xiMassVerticalEnvelope c τ R * (R + c)) /
          ‖xiSpectralPoint q‖ ^ 2 := by
      rw [abs_of_nonneg (by linarith : 0 ≤ c - -c)]
      ring

/-- Quantitative complete mass vertical-edge spectral law. -/
theorem summable_integral_xiMassVerticalRawTerm_and_norm_tsum_le
    {a c R : ℝ} (ha : 0 < a) (hc : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (hR : 1 ≤ R)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    Summable (fun q : XiZeroCopy => ∫ y in -c..c, xiMassVerticalRawTerm a τ R q y) ∧
      ‖∑' q : XiZeroCopy, ∫ y in -c..c, xiMassVerticalRawTerm a τ R q y‖ ≤
        (xiMassVerticalIntegratedNumerator c τ R * Real.sqrt (3 * (R + c))) *
            (∑' q : XiZeroCopy,
              1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)) +
          (3 * c * xiMassVerticalEnvelope c τ R * (R + c)) *
            (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) := by
  let T : XiZeroCopy → ℂ := fun q =>
    ∫ y in -c..c, xiMassVerticalRawTerm a τ R q y
  let w₃ : XiZeroCopy → ℝ := fun q =>
    1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)
  let w₂ : XiZeroCopy → ℝ := fun q => 1 / ‖xiSpectralPoint q‖ ^ 2
  let N : ℝ := xiMassVerticalIntegratedNumerator c τ R
  let c₃ : ℝ := N * Real.sqrt (3 * (R + c))
  let c₂ : ℝ := 3 * c * xiMassVerticalEnvelope c τ R * (R + c)
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hc).le
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hRc : 0 < R + c := by linarith
  have hN : 0 ≤ N := by
    dsimp only [N]
    exact xiMassVerticalIntegratedNumerator_nonneg hc hR0 τ
  have hc₃ : 0 ≤ c₃ := by dsimp only [c₃]; positivity
  have hc₂ : 0 ≤ c₂ := by
    dsimp only [c₂]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hc0) (xiMassVerticalEnvelope_pos c τ R).le)
      hRc.le
  have hw₃ : Summable w₃ := by
    simpa only [w₃] using xiSpectralPoint_inv_three_halves_summable
  have hw₂ : Summable w₂ := by
    simpa only [w₂] using xiSpectralPoint_inv_sq_summable
  have hsum₃ : Summable (fun q => c₃ * w₃ q) := hw₃.mul_left c₃
  have hsum₂ : Summable (fun q => c₂ * w₂ q) := hw₂.mul_left c₂
  have hmajorant : Summable (fun q => c₃ * w₃ q + c₂ * w₂ q) :=
    hsum₃.add hsum₂
  have hbound : ∀ q : XiZeroCopy, ‖T q‖ ≤ c₃ * w₃ q + c₂ * w₂ q := by
    intro q
    have hp : 0 < ‖xiSpectralPoint q‖ :=
      norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    by_cases hnear : ‖xiSpectralPoint q‖ ≤ 3 * (R + c)
    · have hinv := one_div_norm_le_sqrt_mul_one_div_norm_sqrt_norm q
        (by simpa [abs_of_pos hRc] using hnear)
      calc
        ‖T q‖ ≤ N / ‖xiSpectralPoint q‖ := by
          simpa only [T, N] using
            norm_integral_xiMassVerticalRawTerm_le ha hc hca hτ hR q (havoid q)
        _ = N * (1 / ‖xiSpectralPoint q‖) := by ring
        _ ≤ N * (Real.sqrt (3 * (R + c)) * w₃ q) := by
          exact mul_le_mul_of_nonneg_left (by simpa only [w₃] using hinv) hN
        _ = c₃ * w₃ q := by dsimp only [c₃]; ring
        _ ≤ c₃ * w₃ q + c₂ * w₂ q :=
          le_add_of_nonneg_right (mul_nonneg hc₂ (by dsimp only [w₂]; positivity))
    · have hfar : 3 * (R + c) ≤ ‖xiSpectralPoint q‖ :=
        le_of_lt (lt_of_not_ge hnear)
      calc
        ‖T q‖ ≤ c₂ / ‖xiSpectralPoint q‖ ^ 2 := by
          simpa only [T, c₂] using
            norm_integral_xiMassVerticalRawTerm_le_inv_sq ha hca hτ hR hc0 q hfar
        _ = c₂ * w₂ q := by dsimp only [w₂]; ring
        _ ≤ c₃ * w₃ q + c₂ * w₂ q :=
          le_add_of_nonneg_left (mul_nonneg hc₃ (by dsimp only [w₃]; positivity))
  have hT : Summable T := hmajorant.of_norm_bounded hbound
  refine ⟨by simpa only [T] using hT, ?_⟩
  calc
    ‖∑' q : XiZeroCopy, ∫ y in -c..c, xiMassVerticalRawTerm a τ R q y‖ =
        ‖∑' q, T q‖ := by rfl
    _ ≤ ∑' q, ‖T q‖ := norm_tsum_le_tsum_norm hT.norm
    _ ≤ ∑' q, (c₃ * w₃ q + c₂ * w₂ q) :=
      Summable.tsum_mono hT.norm hmajorant hbound
    _ = c₃ * (∑' q, w₃ q) + c₂ * (∑' q, w₂ q) := by
      rw [hsum₃.tsum_add hsum₂, tsum_mul_left, tsum_mul_left]
    _ =
        (xiMassVerticalIntegratedNumerator c τ R * Real.sqrt (3 * (R + c))) *
            (∑' q : XiZeroCopy,
              1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)) +
          (3 * c * xiMassVerticalEnvelope c τ R * (R + c)) *
            (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) := by
      rfl

/-- Mixed reciprocal-moment majorant for the integrated mass vertical edge. -/
def xiMassVerticalIntegratedMajorant (c : ℝ) (τ : ℂ) (R : ℝ) : ℝ :=
  (xiMassVerticalIntegratedNumerator c τ R * Real.sqrt (3 * (R + c))) *
      (∑' q : XiZeroCopy,
        1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)) +
    (3 * c * xiMassVerticalEnvelope c τ R * (R + c)) *
      (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2)

/-- Exponential mass decay absorbs the complete near/far reciprocal-moment majorant. -/
theorem tendsto_xiMassVerticalIntegratedMajorant_atTop
    {c : ℝ} (hc : 1 / 2 < c) {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto (xiMassVerticalIntegratedMajorant c τ) atTop (𝓝 0) := by
  let S₃ : ℝ := ∑' q : XiZeroCopy,
    1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)
  let S₂ : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  let K : ℝ := xiVerticalCauchyKernelBoundAt c
  let A₃ : ℝ := 6 * c * ‖τ‖ * S₃
  let A₂ : ℝ := 3 * K * S₃
  let A₁ : ℝ := 6 * c * S₃ + 3 * c * S₂
  let U : ℝ → ℝ := fun R =>
    xiMassVerticalEnvelope c τ R *
      (A₃ * (R + c) ^ 3 + A₂ * (R + c) ^ 2 + A₁ * (R + c))
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hc).le
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact xiVerticalCauchyKernelBoundAt_nonneg hc
  have hS₃ : 0 ≤ S₃ := by
    dsimp only [S₃]
    exact tsum_nonneg fun _ => by positivity
  have hS₂ : 0 ≤ S₂ := by
    dsimp only [S₂]
    exact tsum_nonneg fun _ => by positivity
  have hA₃ : 0 ≤ A₃ := by dsimp only [A₃]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp only [A₂]; positivity
  have hA₁ : 0 ≤ A₁ := by dsimp only [A₁]; positivity
  have hpow (n : ℕ) :
      Tendsto (fun R : ℝ => R ^ n * Real.exp (-τ.re * R)) atTop (𝓝 0) := by
    have hraw := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) τ.re hτ
    apply hraw.congr'
    filter_upwards with R
    exact congrArg (fun u : ℝ => u * Real.exp (-τ.re * R))
      (Real.rpow_natCast R n)
  have hpoly : Tendsto
      (fun R : ℝ =>
        (A₃ * (R + c) ^ 3 + A₂ * (R + c) ^ 2 + A₁ * (R + c)) *
          Real.exp (-τ.re * R)) atTop (𝓝 0) := by
    have h3 := (hpow 3).const_mul A₃
    have h2 := (hpow 2).const_mul (3 * c * A₃ + A₂)
    have h1 := (hpow 1).const_mul (3 * c ^ 2 * A₃ + 2 * c * A₂ + A₁)
    have h0 := (hpow 0).const_mul (c ^ 3 * A₃ + c ^ 2 * A₂ + c * A₁)
    have hsum := ((h3.add h2).add h1).add h0
    convert hsum using 1
    · funext R
      ring
    · norm_num
  have hU : Tendsto U atTop (𝓝 0) := by
    have hmul := hpoly.const_mul (Real.exp (|τ.im| * c))
    have hmul' : Tendsto
        (fun R : ℝ => Real.exp (|τ.im| * c) *
          ((A₃ * (R + c) ^ 3 + A₂ * (R + c) ^ 2 + A₁ * (R + c)) *
            Real.exp (-τ.re * R))) atTop (𝓝 0) := by
      simpa using hmul
    apply hmul'.congr'
    filter_upwards with R
    dsimp only [U, xiMassVerticalEnvelope]
    rw [Real.exp_add]
    ring
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hR0 : 0 ≤ R := le_trans (by norm_num) hR
    have hN := xiMassVerticalIntegratedNumerator_nonneg hc hR0 τ
    have hRc : 0 ≤ R + c := by linarith
    unfold xiMassVerticalIntegratedMajorant
    exact add_nonneg
      (mul_nonneg (mul_nonneg hN (Real.sqrt_nonneg _)) hS₃)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hc0)
            (xiMassVerticalEnvelope_pos c τ R).le) hRc) hS₂)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hR0 : 0 ≤ R := le_trans (by norm_num) hR
    have hRc : 0 < R + c := by linarith
    have hroot : Real.sqrt (3 * (R + c)) ≤ 3 * (R + c) := by
      have hs := Real.sq_sqrt (by positivity : 0 ≤ 3 * (R + c))
      have hs0 := Real.sqrt_nonneg (3 * (R + c))
      have hone : 1 ≤ 3 * (R + c) := by linarith
      nlinarith
    have hbracket : 0 ≤
        (R + c) * K + (2 * c) * (‖τ‖ * (R + c) ^ 2 + 1) :=
      add_nonneg (mul_nonneg hRc.le hK)
        (mul_nonneg (mul_nonneg (by positivity) hc0)
          (add_nonneg (mul_nonneg (norm_nonneg τ) (sq_nonneg _)) (by norm_num)))
    change xiMassVerticalIntegratedMajorant c τ R ≤ U R
    dsimp only [xiMassVerticalIntegratedMajorant, xiMassVerticalIntegratedNumerator,
      xiMassVerticalEnvelope, S₃, S₂, K, A₃, A₂, A₁, U]
    calc
      (Real.exp (-τ.re * R + |τ.im| * c) *
          ((R + c) * xiVerticalCauchyKernelBoundAt c +
            2 * c * (‖τ‖ * (R + c) ^ 2 + 1)) * Real.sqrt (3 * (R + c))) * S₃ +
          (3 * c * Real.exp (-τ.re * R + |τ.im| * c) * (R + c)) * S₂ ≤
        (Real.exp (-τ.re * R + |τ.im| * c) *
          ((R + c) * xiVerticalCauchyKernelBoundAt c +
            2 * c * (‖τ‖ * (R + c) ^ 2 + 1)) * (3 * (R + c))) * S₃ +
          (3 * c * Real.exp (-τ.re * R + |τ.im| * c) * (R + c)) * S₂ := by
            gcongr
      _ = Real.exp (-τ.re * R + |τ.im| * c) *
          ((6 * c * ‖τ‖ * S₃) * (R + c) ^ 3 +
            (3 * xiVerticalCauchyKernelBoundAt c * S₃) * (R + c) ^ 2 +
            (6 * c * S₃ + 3 * c * S₂) * (R + c)) := by ring
  · exact hU

/-- A mass vertical raw summand is continuous on every divisor-avoiding closed edge. -/
theorem continuousOn_xiMassVerticalRawTerm
    {a c R : ℝ} (ha : 0 < a) (hca : c < a)
    (τ : ℂ) (q : XiZeroCopy) (havoid : R ≠ (xiSpectralPoint q).re) :
    ContinuousOn (xiMassVerticalRawTerm a τ R q) (Icc (-c) c) := by
  let p : ℂ := xiSpectralPoint q
  let z : ℝ → ℂ := fun y => (R : ℂ) + y * I
  have hp0 : p ≠ 0 := xiSpectralPoint_ne_zero q
  have hz : Continuous z := by dsimp only [z]; fun_prop
  have hpz : ∀ y ∈ Icc (-c) c, p - z y ≠ 0 := by
    intro y _ hzero
    have hre := congrArg Complex.re hzero
    simp only [p, z, sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      zero_mul, mul_zero, sub_zero, add_zero, zero_re] at hre
    exact havoid (sub_eq_zero.mp hre).symm
  have hg : ContinuousOn (fun y : ℝ => xiMassAnalyticTest a τ (z y)) (Icc (-c) c) :=
    (analyticOnNhd_xiMassAnalyticTest ha τ).continuousOn.comp hz.continuousOn
      (fun y hy => massVerticalPoint_mem_strip hca ((abs_le).2 hy))
  have hquot : ContinuousOn
      (fun y : ℝ => -(z y) / (p * (p - z y))) (Icc (-c) c) := by
    apply hz.continuousOn.neg.div
      (continuousOn_const.mul (continuousOn_const.sub hz.continuousOn))
    intro y hy
    exact mul_ne_zero hp0 (hpz y hy)
  unfold xiMassVerticalRawTerm
  dsimp only [z, p]
  exact hg.mul hquot

/-- Far mass spectrum is absolutely integrable with reciprocal-square size. -/
theorem integral_norm_xiMassVerticalRawTerm_le_inv_sq
    {a c R : ℝ} (ha : 0 < a) (hc : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (hR : 1 ≤ R) (q : XiZeroCopy)
    (hfar : 3 * (R + c) ≤ ‖xiSpectralPoint q‖) :
    (∫ y in -c..c, ‖xiMassVerticalRawTerm a τ R q y‖) ≤
      (3 * c * xiMassVerticalEnvelope c τ R * (R + c)) /
        ‖xiSpectralPoint q‖ ^ 2 := by
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hc).le
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have him := xiSpectralPoint_im_mem_openHalf q
  have himAbs : |(xiSpectralPoint q).im| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith [him.1, him.2]
  have havoid : R ≠ (xiSpectralPoint q).re := by
    intro heq
    have hnorm := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
    rw [← heq, abs_of_nonneg hR0] at hnorm
    linarith
  have hcont := continuousOn_xiMassVerticalRawTerm ha hca τ q havoid
  have hfint : IntervalIntegrable (xiMassVerticalRawTerm a τ R q)
      volume (-c) c := by
    have hcontu : ContinuousOn (xiMassVerticalRawTerm a τ R q) (uIcc (-c) c) := by
      simpa only [uIcc_of_le (by linarith : -c ≤ c)] using hcont
    exact hcontu.intervalIntegrable
  let C : ℝ := ((3 / 2 : ℝ) * xiMassVerticalEnvelope c τ R * (R + c)) /
    ‖xiSpectralPoint q‖ ^ 2
  have hmono :
      (∫ y in -c..c, ‖xiMassVerticalRawTerm a τ R q y‖) ≤
        ∫ _y in -c..c, C := by
    apply intervalIntegral.integral_mono_on (by linarith) hfint.norm
      (continuous_const.intervalIntegrable _ _)
    intro y hy
    exact norm_xiMassVerticalRawTerm_le_inv_sq ha hca hτ hR hc0 q hfar
      ((abs_le).2 hy)
  calc
    (∫ y in -c..c, ‖xiMassVerticalRawTerm a τ R q y‖) ≤
        ∫ _y in -c..c, C := hmono
    _ = (3 * c * xiMassVerticalEnvelope c τ R * (R + c)) /
          ‖xiSpectralPoint q‖ ^ 2 := by
      rw [intervalIntegral.integral_const]
      dsimp only [C]
      simp only [smul_eq_mul]
      ring

/-- Beyond every height lies a divisor-avoiding mass edge with arbitrarily small integrated raw
resolvent sum. -/
theorem exists_large_integrated_xiMassVerticalRawTerm_tsum_lt
    {a c : ℝ} (ha : 0 < a) (hc : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (X : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ R : ℝ,
      X < R ∧ 1 ≤ R ∧
      (∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) ∧
      Summable (fun q : XiZeroCopy => ∫ y in -c..c, xiMassVerticalRawTerm a τ R q y) ∧
      ‖∑' q : XiZeroCopy, ∫ y in -c..c, xiMassVerticalRawTerm a τ R q y‖ < epsilon := by
  have hevent :=
    (tendsto_xiMassVerticalIntegratedMajorant_atTop hc hτ).eventually_lt_const hepsilon
  obtain ⟨M, hM⟩ := eventually_atTop.1 hevent
  let u : ℝ := max (max X 1) M
  obtain ⟨R, hRI, havoid⟩ :=
    exists_real_avoiding_all_xiSpectralPoint_re (show u < u + 1 by linarith)
  have hXu : X ≤ u := le_trans (le_max_left X 1) (le_max_left (max X 1) M)
  have h1u : 1 ≤ u := le_trans (le_max_right X 1) (le_max_left (max X 1) M)
  have hMu : M ≤ u := le_max_right (max X 1) M
  have hXR : X < R := lt_of_le_of_lt hXu hRI.1
  have hR : 1 ≤ R := le_trans h1u hRI.1.le
  have hMR : M ≤ R := le_trans hMu hRI.1.le
  obtain ⟨hsum, hbound⟩ :=
    summable_integral_xiMassVerticalRawTerm_and_norm_tsum_le
      ha hc hca hτ hR havoid
  have hsmall :
      ‖∑' q : XiZeroCopy, ∫ y in -c..c, xiMassVerticalRawTerm a τ R q y‖ <
        epsilon := by
    exact lt_of_le_of_lt hbound (hM R hMR)
  exact ⟨R, hXR, hR, havoid, hsum, hsmall⟩

/-- Absolute integrability justifies exchanging the full mass divisor sum with the edge integral. -/
theorem integral_tsum_xiMassVerticalRawTerm_eq_tsum_integral
    {a c R : ℝ} (ha : 0 < a) (hc : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (hR : 1 ≤ R)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    (∫ y in -c..c, ∑' q : XiZeroCopy, xiMassVerticalRawTerm a τ R q y) =
      ∑' q : XiZeroCopy, ∫ y in -c..c, xiMassVerticalRawTerm a τ R q y := by
  let A : ℝ := 3 * c * xiMassVerticalEnvelope c τ R * (R + c)
  let b : XiZeroCopy → ℝ := fun q => A / ‖xiSpectralPoint q‖ ^ 2
  have hc0 : 0 ≤ c := (lt_trans (by norm_num) hc).le
  have hRc : 0 < R + c := by linarith
  have hb : Summable b := by
    have hscaled := xiSpectralPoint_inv_sq_summable.mul_left A
    refine hscaled.congr (fun q => ?_)
    dsimp only [b]
    ring
  have hfarEventually :
      ∀ᶠ q : XiZeroCopy in Filter.cofinite,
        3 * (R + c) ≤ ‖xiSpectralPoint q‖ := by
    have hfinite := xiSpectralPoint_finite_norm_le (B := 3 * (R + c)) (by positivity)
    have houtside :
        ∀ᶠ q : XiZeroCopy in Filter.cofinite,
          3 * (R + c) < ‖xiSpectralPoint q‖ := by
      simpa only [Set.compl_setOf, Set.mem_setOf_eq, not_le] using!
        hfinite.compl_mem_cofinite
    filter_upwards [houtside] with q hq
    exact hq.le
  have hnormSum : Summable (fun q : XiZeroCopy =>
      ∫ y in -c..c, ‖xiMassVerticalRawTerm a τ R q y‖) := by
    apply hb.of_norm_bounded_eventually
    filter_upwards [hfarEventually] with q hfar
    have hnonneg : 0 ≤ ∫ y in -c..c, ‖xiMassVerticalRawTerm a τ R q y‖ :=
      intervalIntegral.integral_nonneg (by linarith) (fun _ _ => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simpa only [b, A] using
      integral_norm_xiMassVerticalRawTerm_le_inv_sq ha hc hca hτ hR q hfar
  have hFint : ∀ q : XiZeroCopy,
      Integrable (xiMassVerticalRawTerm a τ R q)
        (volume.restrict (Ioc (-c) c)) := by
    intro q
    have hcont := continuousOn_xiMassVerticalRawTerm ha hca τ q (havoid q)
    have hcontu : ContinuousOn (xiMassVerticalRawTerm a τ R q) (uIcc (-c) c) := by
      simpa only [uIcc_of_le (by linarith : -c ≤ c)] using hcont
    have hint : IntervalIntegrable (xiMassVerticalRawTerm a τ R q) volume (-c) c :=
      hcontu.intervalIntegrable
    rw [intervalIntegrable_iff] at hint
    simpa only [uIoc_of_le (by linarith : -c ≤ c)] using! hint
  have hnormSumRestrict : Summable (fun q : XiZeroCopy =>
      ∫ y in Ioc (-c) c, ‖xiMassVerticalRawTerm a τ R q y‖) := by
    apply hnormSum.congr
    intro q
    exact intervalIntegral.integral_of_le (by linarith)
  rw [intervalIntegral.integral_of_le (by linarith : -c ≤ c)]
  calc
    (∫ y in Ioc (-c) c, ∑' q : XiZeroCopy, xiMassVerticalRawTerm a τ R q y) =
      ∑' q : XiZeroCopy, ∫ y in Ioc (-c) c, xiMassVerticalRawTerm a τ R q y :=
        (MeasureTheory.integral_tsum_of_summable_integral_norm hFint
          hnormSumRestrict).symm
    _ = ∑' q : XiZeroCopy, ∫ y in -c..c, xiMassVerticalRawTerm a τ R q y := by
      apply tsum_congr
      intro q
      exact (intervalIntegral.integral_of_le (by linarith)).symm

/-- Pointwise raw mass divisor sum equals the mass test times canonical Xi relative resolvent. -/
theorem tsum_xiMassVerticalRawTerm_eq_mul_relativeResolventTrace
    (a : ℝ) (τ : ℂ) (R y : ℝ)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    (∑' q : XiZeroCopy, xiMassVerticalRawTerm a τ R q y) =
      xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
        xiRelativeResolventTrace ((R : ℂ) + y * I) := by
  let z : ℂ := (R : ℂ) + y * I
  let g : ℂ := xiMassAnalyticTest a τ z
  let t : XiZeroCopy → ℂ := fun q =>
    -z / (xiSpectralPoint q * (xiSpectralPoint q - z))
  have hzq : ∀ q : XiZeroCopy, z ≠ xiSpectralPoint q := by
    intro q heq
    have hre := congrArg Complex.re heq
    simp only [z, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, zero_mul,
      mul_zero, sub_self, add_zero] at hre
    exact havoid q hre
  have hterm : ∀ q : XiZeroCopy, xiRelativeResolventTerm z q = t q := by
    intro q
    have hp := xiSpectralPoint_ne_zero q
    have hpz : xiSpectralPoint q - z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hzq q))
    rw [xiRelativeResolventTerm, inv_eq_one_div]
    dsimp only [t]
    field_simp [hp, hpz]
    ring
  have htrace : (∑' q : XiZeroCopy, t q) = xiRelativeResolventTrace z := by
    rw [xiRelativeResolventTrace]
    apply tsum_congr
    intro q
    exact (hterm q).symm
  calc
    (∑' q : XiZeroCopy, xiMassVerticalRawTerm a τ R q y) =
        ∑' q : XiZeroCopy, g * t q := by
      apply tsum_congr
      intro q
      rfl
    _ = g * (∑' q : XiZeroCopy, t q) := tsum_mul_left
    _ = g * xiRelativeResolventTrace z := by rw [htrace]
    _ = xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
        xiRelativeResolventTrace ((R : ℂ) + y * I) := by rfl

/-- Exact integrated right-edge identity for the full Xi relative trace. -/
theorem integral_xiMass_mul_xiRelativeResolventTrace_eq_tsum_integral_rawTerm
    {a c R : ℝ} (ha : 0 < a) (hc : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (hR : 1 ≤ R)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    (∫ y in -c..c, xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
        xiRelativeResolventTrace ((R : ℂ) + y * I)) =
      ∑' q : XiZeroCopy, ∫ y in -c..c, xiMassVerticalRawTerm a τ R q y := by
  calc
    _ = ∫ y in -c..c, ∑' q : XiZeroCopy, xiMassVerticalRawTerm a τ R q y := by
      apply integral_congr
      intro y _
      exact (tsum_xiMassVerticalRawTerm_eq_mul_relativeResolventTrace
        a τ R y havoid).symm
    _ = _ := integral_tsum_xiMassVerticalRawTerm_eq_tsum_integral
      ha hc hca hτ hR havoid

/-- On a divisor-avoiding edge, the actual Xi logarithmic derivative equals its relative trace. -/
theorem integral_xiMass_mul_logDeriv_XiC_eq_relativeResolventTrace
    (a : ℝ) (τ : ℂ) {c R : ℝ}
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    (∫ y in -c..c, xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
        logDeriv XiC ((R : ℂ) + y * I)) =
      ∫ y in -c..c, xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
        xiRelativeResolventTrace ((R : ℂ) + y * I) := by
  apply integral_congr
  intro y _
  change xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
      logDeriv XiC ((R : ℂ) + y * I) = _
  rw [logDeriv_XiC_eq_relativeResolventTrace
    (XiC_ne_zero_on_avoiding_vertical R y havoid)]

/-- Full cofinal vanishing of the analytic-mass Xi logarithmic-derivative vertical edge. -/
theorem exists_large_integral_xiMass_mul_logDeriv_XiC_norm_lt
    {a c : ℝ} (ha : 0 < a) (hc : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (X : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ R : ℝ,
      X < R ∧ 1 ≤ R ∧
      (∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) ∧
      ‖∫ y in -c..c, xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
          logDeriv XiC ((R : ℂ) + y * I)‖ < epsilon := by
  obtain ⟨R, hXR, hR, havoid, _hsum, hsmall⟩ :=
    exists_large_integrated_xiMassVerticalRawTerm_tsum_lt
      ha hc hca hτ X hepsilon
  have hedge := integral_xiMass_mul_xiRelativeResolventTrace_eq_tsum_integral_rawTerm
    ha hc hca hτ hR havoid
  refine ⟨R, hXR, hR, havoid, ?_⟩
  rw [integral_xiMass_mul_logDeriv_XiC_eq_relativeResolventTrace a τ havoid,
    hedge]
  exact hsmall

end

end RHTower

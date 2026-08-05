import GaloisForLFunctions.RHTower.XiMassBottomEdge
import GaloisForLFunctions.RHTower.XiMassVerticalResolvent

/-!
# Exact mass--Xi Euler-contour source identity

The analytic mass trace is exactly the normalized, absolutely convergent Euler-line integral of
the von-Mangoldt minus completed archimedean source.  The proof exhausts the multiplicity-exact Xi
divisor by symmetric rectangles, uses gap-free integrated resolvent decay for a cofinal sequence of
vertical edges, and passes the bottom edge to its full Bochner integral.

No RH hypothesis, zero-separation assumption, or source-continuation convention occurs.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Normalized complete mass source on a legal Euler bottom line. -/
def normalizedXiMassBottomEulerContour (a c : ℝ) (τ : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    (2 * ∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x)

/-- Normalized symmetric truncation of the mass Euler bottom source. -/
def normalizedXiMassTruncatedBottomEulerContour (a c R : ℝ) (τ : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    (2 * ∫ x in -R..R, xiMassBottomSourceIntegrand a c τ x)

/-- Symmetric mass rectangles exhaust the complete multiplicity-exact analytic mass trace. -/
theorem tendsto_symmetric_xiZeroCopy_xiMass_sum_atTop
    {a c : ℝ} (ha : 1 / 2 ≤ a) (hhalf : 1 / 2 < c) {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto
      (fun R : ℝ =>
        ∑ q ∈ xiZeroCopyClosedRectangle
          (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I),
          xiMassAnalyticTest a τ (xiSpectralPoint q))
      atTop (𝓝 ((xiMassFamily ha).traceC τ)) := by
  rw [← tsum_xiMassAnalyticTest_spectralPoint_eq_traceC ha τ]
  let f : XiZeroCopy → ℂ := fun q => xiMassAnalyticTest a τ (xiSpectralPoint q)
  have hsum : Summable f :=
    (summable_norm_xiMassAnalyticTest_spectralPoint ha hτ).of_norm
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hball : Metric.ball (∑' q, f q) epsilon ∈ 𝓝 (∑' q, f q) :=
    Metric.ball_mem_nhds _ hepsilon
  have hevent : ∀ᶠ s : Finset XiZeroCopy in atTop,
      ∑ q ∈ s, f q ∈ Metric.ball (∑' q, f q) epsilon :=
    hsum.hasSum.eventually hball
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
    have hqsum : |(xiSpectralPoint q).re| ≤
        ∑ r ∈ t, |(xiSpectralPoint r).re| :=
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

/-- Complete bottom integrals are the limits of normalized symmetric truncations. -/
theorem tendsto_normalizedXiMassTruncatedBottomEulerContour_atTop
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    Tendsto (fun R => normalizedXiMassTruncatedBottomEulerContour a c R τ)
      atTop (𝓝 (normalizedXiMassBottomEulerContour a c τ)) := by
  have hraw := tendsto_integral_xiMassBottomSourceIntegrand_atTop hhalf hca hτ
  have hscaled := (hraw.const_mul (2 : ℂ)).const_mul (2 * Real.pi * I)⁻¹
  simpa only [normalizedXiMassTruncatedBottomEulerContour,
    normalizedXiMassBottomEulerContour] using! hscaled

private theorem xiMassLeftVertical_nonzero_of_avoiding
    (R y : ℝ) (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    XiC (((-R : ℝ) : ℂ) + y * I) ≠ 0 := by
  intro hzero
  have hnegzero : XiC (-((((-R : ℝ) : ℂ) + y * I))) = 0 := by
    rw [XiC_even]
    exact hzero
  have hpoint : -((((-R : ℝ) : ℂ) + y * I)) =
      (R : ℂ) + (-y) * I := by
    push_cast
    ring
  rw [hpoint] at hnegzero
  exact XiC_ne_zero_on_avoiding_vertical R (-y) havoid
    (by simpa only [Complex.ofReal_neg] using hnegzero)

/-- On each divisor-avoiding radius, finite mass spectrum equals normalized truncated source plus
the normalized right-edge error. -/
theorem xiMassFiniteRectangleSum_eq_truncatedBottom_add_vertical
    {a c R : ℝ} (ha : 0 < a) (hhalf : 1 / 2 < c) (hca : c < a) (hR : 0 < R)
    (τ : ℂ) (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    (∑ q ∈ xiZeroCopyClosedRectangle
        (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I),
        xiMassAnalyticTest a τ (xiSpectralPoint q)) =
      normalizedXiMassTruncatedBottomEulerContour a c R τ +
        (2 * Real.pi * I)⁻¹ * 2 * I *
          (∫ y in -c..c,
            xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
              logDeriv XiC ((R : ℂ) + y * I)) := by
  have hright : ∀ y ∈ uIcc (-c) c,
      XiC ((R : ℂ) + y * I) ≠ 0 := by
    intro y _
    exact XiC_ne_zero_on_avoiding_vertical R y havoid
  have hleft : ∀ y ∈ uIcc (-c) c,
      XiC (((-R : ℝ) : ℂ) + y * I) ≠ 0 := by
    intro y _
    exact xiMassLeftVertical_nonzero_of_avoiding R y havoid
  have hfinite := xiMassFiniteSpectralSum_eq_bottomPrimeArch_add_vertical
    ha hhalf hca hR τ hright hleft
  have hsource : (∫ x in -R..R,
      xiMassAnalyticTest a τ ((x : ℂ) - c * I) *
        (-I *
          (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (((1 / 2 + c : ℝ) : ℂ) + x * I) -
            logDeriv archFactor (((1 / 2 + c : ℝ) : ℂ) + x * I)))) =
      ∫ x in -R..R, xiMassBottomSourceIntegrand a c τ x := by
    apply intervalIntegral.integral_congr
    intro x _
    rfl
  rw [hsource] at hfinite
  have hnorm : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  calc
    (∑ q ∈ xiZeroCopyClosedRectangle
        (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I),
        xiMassAnalyticTest a τ (xiSpectralPoint q)) =
      (2 * Real.pi * I)⁻¹ *
        (2 * Real.pi * I *
          ∑ q ∈ xiZeroCopyClosedRectangle
            (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I),
            xiMassAnalyticTest a τ (xiSpectralPoint q)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hnorm, one_mul]
    _ = (2 * Real.pi * I)⁻¹ *
        (2 * ((∫ x in -R..R, xiMassBottomSourceIntegrand a c τ x) +
          I • (∫ y in -c..c,
            xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
              logDeriv XiC ((R : ℂ) + y * I)))) := by rw [hfinite]
    _ = normalizedXiMassTruncatedBottomEulerContour a c R τ +
        (2 * Real.pi * I)⁻¹ * 2 * I *
          (∫ y in -c..c,
            xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
              logDeriv XiC ((R : ℂ) + y * I)) := by
      unfold normalizedXiMassTruncatedBottomEulerContour
      simp only [smul_eq_mul]
      ring

/-- **Exact mass--Xi Euler-contour source identity.**  For every `a > 1/2`, every legal contour
depth `1/2 < c < a`, and every complex time with positive real part, the complete analytic mass
trace is the normalized absolutely convergent von-Mangoldt minus archimedean bottom integral. -/
theorem xiMassTraceC_eq_normalizedBottomEulerContour
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    (xiMassFamily (show 1 / 2 ≤ a by linarith)).traceC τ =
      normalizedXiMassBottomEulerContour a c τ := by
  let ha : 1 / 2 ≤ a := by linarith
  let W : ℂ := (xiMassFamily ha).traceC τ
  let B : ℂ := normalizedXiMassBottomEulerContour a c τ
  let S : ℝ → ℂ := fun R =>
    ∑ q ∈ xiZeroCopyClosedRectangle
      (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I),
      xiMassAnalyticTest a τ (xiSpectralPoint q)
  let T : ℝ → ℂ := fun R => normalizedXiMassTruncatedBottomEulerContour a c R τ
  let V : ℝ → ℂ := fun R =>
    ∫ y in -c..c,
      xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
        logDeriv XiC ((R : ℂ) + y * I)
  let k : ℂ := (2 * Real.pi * I)⁻¹ * 2 * I
  change W = B
  by_contra hWB
  have hd : 0 < dist W B := dist_pos.mpr hWB
  let epsilon : ℝ := dist W B / 4
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  have hS : Tendsto S atTop (𝓝 W) := by
    simpa only [S, W] using tendsto_symmetric_xiZeroCopy_xiMass_sum_atTop ha hhalf hτ
  have hT : Tendsto T atTop (𝓝 B) := by
    simpa only [T, B] using
      tendsto_normalizedXiMassTruncatedBottomEulerContour_atTop hhalf hca hτ
  obtain ⟨XS, hXS⟩ := (Metric.tendsto_atTop.mp hS) epsilon hepsilon
  obtain ⟨XT, hXT⟩ := (Metric.tendsto_atTop.mp hT) epsilon hepsilon
  let delta : ℝ := epsilon / (‖k‖ + 1)
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have ha0 : 0 < a := lt_trans (lt_trans (by norm_num) hhalf) hca
  obtain ⟨R, hRX, hR, havoid, hVsmall⟩ :=
    exists_large_integral_xiMass_mul_logDeriv_XiC_norm_lt
      ha0 hhalf hca hτ (max XS XT) hdelta
  have hRXS : XS ≤ R := le_trans (le_max_left XS XT) (le_of_lt hRX)
  have hRXT : XT ≤ R := le_trans (le_max_right XS XT) (le_of_lt hRX)
  have hspec : dist (S R) W < epsilon := hXS R hRXS
  have hbottom : dist (T R) B < epsilon := hXT R hRXT
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hfinite : S R = T R + k * V R := by
    simpa only [S, T, k, V, mul_assoc] using
      xiMassFiniteRectangleSum_eq_truncatedBottom_add_vertical
        ha0 hhalf hca hRpos τ havoid
  have hST : dist (S R) (T R) < epsilon := by
    calc
      dist (S R) (T R) = ‖k * V R‖ := by
        rw [hfinite, dist_eq_norm]
        congr 1
        ring
      _ = ‖k‖ * ‖V R‖ := norm_mul _ _
      _ ≤ (‖k‖ + 1) * ‖V R‖ := by
        exact mul_le_mul_of_nonneg_right (by linarith [norm_nonneg k]) (norm_nonneg _)
      _ < (‖k‖ + 1) * delta :=
        mul_lt_mul_of_pos_left (by simpa only [V] using hVsmall) (by positivity)
      _ = epsilon := by
        dsimp only [delta]
        field_simp
  have htri := dist_triangle4 W (S R) (T R) B
  rw [dist_comm W (S R)] at htri
  dsimp only [epsilon] at hepsilon hspec hST hbottom
  nlinarith

/-- Unnormalized form of the exact source identity. -/
theorem two_pi_I_mul_xiMassTraceC_eq_bottomEulerSource
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    2 * Real.pi * I * (xiMassFamily (show 1 / 2 ≤ a by linarith)).traceC τ =
      2 * ∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x := by
  rw [xiMassTraceC_eq_normalizedBottomEulerContour hhalf hca hτ,
    normalizedXiMassBottomEulerContour]
  have hnorm : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  change (2 * Real.pi * I) *
      ((2 * Real.pi * I)⁻¹ * (2 * ∫ x : ℝ, xiMassBottomSourceIntegrand a c τ x)) = _
  rw [← mul_assoc, mul_inv_cancel₀ hnorm, one_mul]

end

end RHTower

import GaloisForLFunctions.RHTower.XiGaussianVerticalResolvent
import GaloisForLFunctions.RHTower.XiGaussianHeatTuranDefect

/-!
# Full Gaussian Guinand--Weil explicit formula

The Gaussian--Hermite test is entire, even, and absolutely summable on the exact-multiplicity Xi
divisor.  The preceding vertical-resolvent theorem removes the only nonuniform contour edge.  This
module therefore exhausts symmetric depth-one rectangles and identifies the complete Gaussian Xi
heat moment with the literal completed prime--Gamma bottom source.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

theorem xiGaussianLogDerivIntegrand_neg (t : ℝ) (k : ℕ) (z : ℂ) :
    xiGaussianTestC t k (-z) * logDeriv XiC (-z) =
      -(xiGaussianTestC t k z * logDeriv XiC z) := by
  rw [xiGaussianTestC_neg, logDeriv_XiC_neg]
  ring

/-- Exact argument-principle extraction for a Gaussian test on a symmetric depth-one rectangle. -/
theorem rectIntegral_xiGaussianLogDeriv_symmetric_eq_xiZeroCopy_sum
    (t : ℝ) (k : ℕ) (R : ℝ) (hR : 0 < R)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    rectIntegral (fun z => xiGaussianTestC t k z * logDeriv XiC z)
        (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I) =
      2 * Real.pi * I *
        ∑ q ∈ xiZeroCopyClosedRectangle
          (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I),
          xiGaussianTestC t k (xiSpectralPoint q) := by
  let z₁ : ℂ := (((-R : ℝ) : ℂ) - I)
  let z₂ : ℂ := (((R : ℝ) : ℂ) + I)
  let g : ℂ → ℂ := xiGaussianTestC t k
  obtain ⟨m, h, hhan, hm, hhK, hfact⟩ :=
    exists_xiC_closedRectangle_factorization z₁ z₂
  let U : Set ℂ := {z : ℂ | h z ≠ 0}
  have hhcont : Continuous h := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (hhan z (Set.mem_univ z)).continuousAt
  have hUopen : IsOpen U := by
    change IsOpen (h ⁻¹' {0}ᶜ)
    exact isOpen_compl_singleton.preimage hhcont
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U :=
    fun z hz => hhK z hz
  have hz₁re : z₁.re = -R := by simp [z₁]
  have hz₂re : z₂.re = R := by simp [z₂]
  have hz₁im : z₁.im = -1 := by simp [z₁]
  have hz₂im : z₂.im = 1 := by simp [z₂]
  have hin : ∀ w ∈ xiCClosedRectangleZeros z₁ z₂,
      z₁.re < w.re ∧ w.re < z₂.re ∧ z₁.im < w.im ∧ w.im < z₂.im := by
    intro w hw
    obtain ⟨hwK, hwzero⟩ := mem_xiCClosedRectangleZeros.mp hw
    obtain ⟨hwre, hwim⟩ := Complex.mem_reProdIm.mp hwK
    rw [uIcc_of_le (by simp [hz₁re, hz₂re]; linarith)] at hwre
    rw [uIcc_of_le (by simp [hz₁im, hz₂im])] at hwim
    have hwstrip := xiC_zero_im_mem_openHalf hwzero
    have hreRight : w.re < z₂.re := by
      apply lt_of_le_of_ne hwre.2
      intro heq
      obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy w).mp hwzero
      apply havoid q
      rw [hz₂re] at heq
      have hqre := congrArg Complex.re hq
      linarith
    have hreLeft : z₁.re < w.re := by
      apply lt_of_le_of_ne hwre.1
      intro heq
      have hnegzero : XiC (-w) = 0 := by rw [XiC_even, hwzero]
      obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (-w)).mp hnegzero
      apply havoid q
      rw [hz₁re] at heq
      have hqre := congrArg Complex.re hq
      simp only [neg_re] at hqre
      linarith
    exact ⟨hreLeft, hreRight, by rw [hz₁im]; linarith,
      by rw [hz₂im]; linarith⟩
  have hres := rectIntegral_mul_logDeriv_boxCount
    (xiCClosedRectangleZeros z₁ z₂) (fun w => w) m
    (analyticOnNhd_xiGaussianTestC t k)
    hUopen hin hsub (fun z _ => hhan z (Set.mem_univ z))
    (fun _ hz => hz) (fun z _ => hfact z)
  calc
    rectIntegral (fun z => xiGaussianTestC t k z * logDeriv XiC z)
        (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I) =
      2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        (m w : ℂ) * g w := by
      simpa only [z₁, z₂, g] using hres
    _ = 2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        (xiSpectralMultiplicity w : ℂ) * g w := by
      congr 1
      apply Finset.sum_congr rfl
      intro w hw
      have hwzero : XiC w = 0 := (mem_xiCClosedRectangleZeros.mp hw).2
      rw [hm w hw, xiSpectralMultiplicity_eq_analyticOrderAt_toNat hwzero]
    _ = 2 * Real.pi * I * ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        g (xiSpectralPoint q) := by
      rw [sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum]
    _ = 2 * Real.pi * I *
        ∑ q ∈ xiZeroCopyClosedRectangle
          (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I),
          xiGaussianTestC t k (xiSpectralPoint q) := by rfl

/-- Gaussian Xi contour normalized by the argument-principle factor. -/
def normalizedXiGaussianSymmetricContour (t : ℝ) (k : ℕ) (R : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    rectIntegral (fun z => xiGaussianTestC t k z * logDeriv XiC z)
      (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I)

/-- Truncated normalized Gaussian bottom edge. -/
def normalizedXiGaussianTruncatedBottomContribution
    (t : ℝ) (k : ℕ) (R : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    (2 * ∫ x in -R..R, xiGaussianBottomXiLogIntegrand t k 1 x)

/-- Complete normalized Gaussian bottom edge. -/
def normalizedXiGaussianBottomContribution (t : ℝ) (k : ℕ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    (2 * ∫ x : ℝ, xiGaussianBottomXiLogIntegrand t k 1 x)

theorem normalizedXiGaussianSymmetricContour_eq_xiZeroCopy_sum
    (t : ℝ) (k : ℕ) (R : ℝ) (hR : 0 < R)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    normalizedXiGaussianSymmetricContour t k R =
      ∑ q ∈ xiZeroCopyClosedRectangle
        (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I),
        xiGaussianTestC t k (xiSpectralPoint q) := by
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  rw [normalizedXiGaussianSymmetricContour,
    rectIntegral_xiGaussianLogDeriv_symmetric_eq_xiZeroCopy_sum
      t k R hR havoid, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem normalizedXiGaussianSymmetricContour_eq_truncatedBottom_add_vertical
    (t : ℝ) (k : ℕ) (R : ℝ) :
    normalizedXiGaussianSymmetricContour t k R =
      normalizedXiGaussianTruncatedBottomContribution t k R +
        (2 * Real.pi * I)⁻¹ * 2 * I *
          (∫ y in (-1 : ℝ)..1,
            xiGaussianTestC t k ((R : ℂ) + y * I) *
              logDeriv XiC ((R : ℂ) + y * I)) := by
  have hfold := rectIntegral_symmetric_eq_two_bottom_add_vertical
    (fun z => xiGaussianTestC t k z * logDeriv XiC z)
    (xiGaussianLogDerivIntegrand_neg t k) R 1
  norm_num at hfold
  rw [normalizedXiGaussianSymmetricContour]
  rw [show (((-R : ℝ) : ℂ)) = -((R : ℝ) : ℂ) by simp]
  rw [hfold]
  unfold normalizedXiGaussianTruncatedBottomContribution
  simp [xiGaussianBottomXiLogIntegrand]
  ring

theorem tendsto_normalizedXiGaussianTruncatedBottomContribution_atTop
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Tendsto (normalizedXiGaussianTruncatedBottomContribution t k)
      atTop (nhds (normalizedXiGaussianBottomContribution t k)) := by
  have hraw : Tendsto
      (fun R : ℝ => ∫ x in -R..R, xiGaussianBottomXiLogIntegrand t k 1 x)
      atTop (nhds (∫ x : ℝ, xiGaussianBottomXiLogIntegrand t k 1 x)) :=
    intervalIntegral_tendsto_integral
      (integrable_xiGaussianBottomXiLogIntegrand ht (by norm_num) k)
      (tendsto_neg_atBot_iff.mpr tendsto_id) tendsto_id
  have hscaled := (hraw.const_mul (2 : ℂ)).const_mul (2 * Real.pi * I)⁻¹
  simpa only [normalizedXiGaussianTruncatedBottomContribution,
    normalizedXiGaussianBottomContribution] using! hscaled

theorem normalizedXiGaussianBottomContribution_eq_completedSource_div_pi
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    normalizedXiGaussianBottomContribution t k =
      (Real.pi : ℂ)⁻¹ *
        ∫ x : ℝ, xiGaussianCompletedBottomSource t k 1 x := by
  have hsource := integral_xiGaussianCompletedBottomSource_eq_neg_I_mul_XiLog
    ht (by norm_num : (1 / 2 : ℝ) < 1) k
  rw [normalizedXiGaussianBottomContribution, hsource]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hpi, I_ne_zero]
  ring_nf
  rw [I_sq]
  ring

/-- Symmetric depth-one rectangles exhaust the complete Gaussian heat moment. -/
theorem tendsto_symmetric_xiZeroCopy_gaussian_sum_atTop
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Tendsto
      (fun R : ℝ =>
        ∑ q ∈ xiZeroCopyClosedRectangle
          (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I),
          xiGaussianTestC t k (xiSpectralPoint q))
      atTop (nhds (xiGaussianHeatMoment k t)) := by
  let f : XiZeroCopy → ℂ := fun q => xiGaussianTestC t k (xiSpectralPoint q)
  have hsum : Summable f := by
    apply (summable_xiGaussianHeatMonomialTerm ht k).congr
    intro q
    exact (xiGaussianTestC_spectralPoint t k q).symm
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hball : Metric.ball (∑' q, f q) epsilon ∈ nhds (∑' q, f q) :=
    Metric.ball_mem_nhds _ hepsilon
  have hevent : ∀ᶠ s : Finset XiZeroCopy in atTop,
      ∑ q ∈ s, f q ∈ Metric.ball (∑' q, f q) epsilon :=
    hsum.hasSum.eventually hball
  rw [eventually_atTop] at hevent
  obtain ⟨s, hs⟩ := hevent
  let X : ℝ := 1 + ∑ q ∈ s, |(xiSpectralPoint q).re|
  refine ⟨X, fun R hRX => ?_⟩
  have hRpos : 0 < R := by
    have hsumNonneg : 0 ≤ ∑ q ∈ s, |(xiSpectralPoint q).re| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp only [X] at hRX
    linarith
  have hpacket : s ⊆ xiZeroCopyClosedRectangle
      (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I) := by
    intro q hq
    rw [mem_xiZeroCopyClosedRectangle]
    apply Complex.mem_reProdIm.mpr
    have hqsum : |(xiSpectralPoint q).re| ≤
        ∑ r ∈ s, |(xiSpectralPoint r).re| :=
      Finset.single_le_sum (fun r _ => abs_nonneg (xiSpectralPoint r).re) hq
    have hqbound : |(xiSpectralPoint q).re| < R := by
      dsimp only [X] at hRX
      linarith
    have him := xiSpectralPoint_im_mem_openHalf q
    constructor
    · rw [uIcc_of_le (by simp; linarith)]
      simp only [sub_re, ofReal_re, I_re, sub_zero, add_re]
      constructor <;> linarith [neg_le_abs (xiSpectralPoint q).re,
        le_abs_self (xiSpectralPoint q).re]
    · rw [uIcc_of_le (by simp)]
      simp only [sub_im, ofReal_im, I_im, zero_sub, add_im, zero_add]
      constructor <;> linarith
  have hnear := hs
    (xiZeroCopyClosedRectangle (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I))
    hpacket
  rw [Metric.mem_ball] at hnear
  have htarget : (∑' q, f q) = xiGaussianHeatMoment k t := by
    rw [xiGaussianHeatMoment]
    apply tsum_congr
    intro q
    exact xiGaussianTestC_spectralPoint t k q
  rw [← htarget]
  simpa only [f] using hnear

/-- **Full monomial Gaussian explicit formula.**  The exact-multiplicity Xi heat moment equals the
literal completed prime--Gamma source divided by `pi`. -/
theorem xiGaussianHeatMoment_eq_completedBottomSource_div_pi
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    xiGaussianHeatMoment k t =
      (Real.pi : ℂ)⁻¹ *
        ∫ x : ℝ, xiGaussianCompletedBottomSource t k 1 x := by
  let W : ℂ := xiGaussianHeatMoment k t
  let B : ℂ := normalizedXiGaussianBottomContribution t k
  let S : ℝ → ℂ := fun R =>
    ∑ q ∈ xiZeroCopyClosedRectangle
      (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I),
      xiGaussianTestC t k (xiSpectralPoint q)
  let T : ℝ → ℂ := normalizedXiGaussianTruncatedBottomContribution t k
  let V : ℝ → ℂ := fun R =>
    ∫ y in (-1 : ℝ)..1,
      xiGaussianTestC t k ((R : ℂ) + y * I) *
        logDeriv XiC ((R : ℂ) + y * I)
  let c : ℂ := (2 * Real.pi * I)⁻¹ * 2 * I
  have hWB : W = B := by
    by_contra hne
    have hd : 0 < dist W B := dist_pos.mpr hne
    let epsilon : ℝ := dist W B / 4
    have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
    have hS : Tendsto S atTop (nhds W) := by
      simpa only [S, W] using tendsto_symmetric_xiZeroCopy_gaussian_sum_atTop ht k
    have hT : Tendsto T atTop (nhds B) := by
      simpa only [T, B] using
        tendsto_normalizedXiGaussianTruncatedBottomContribution_atTop ht k
    obtain ⟨XS, hXS⟩ := (Metric.tendsto_atTop.mp hS) epsilon hepsilon
    obtain ⟨XT, hXT⟩ := (Metric.tendsto_atTop.mp hT) epsilon hepsilon
    let delta : ℝ := epsilon / (‖c‖ + 1)
    have hdelta : 0 < delta := by dsimp only [delta]; positivity
    obtain ⟨R, hRX, havoid, hVsmall⟩ :=
      exists_large_integral_xiGaussian_mul_logDeriv_XiC_norm_lt
        ht k (max (max XS XT) 1) hdelta
    have hRXS : XS ≤ R :=
      le_trans (le_trans (le_max_left XS XT) (le_max_left (max XS XT) 1)) hRX.le
    have hRXT : XT ≤ R :=
      le_trans (le_trans (le_max_right XS XT) (le_max_left (max XS XT) 1)) hRX.le
    have hspec : dist (S R) W < epsilon := hXS R hRXS
    have hbottom : dist (T R) B < epsilon := hXT R hRXT
    have hRpos : 0 < R :=
      lt_of_lt_of_le one_pos (le_trans (le_max_right (max XS XT) 1) hRX.le)
    have hcontour : normalizedXiGaussianSymmetricContour t k R = S R := by
      simpa only [S] using
        normalizedXiGaussianSymmetricContour_eq_xiZeroCopy_sum
          t k R hRpos havoid
    have hfold : normalizedXiGaussianSymmetricContour t k R = T R + c * V R := by
      simpa only [T, c, V, mul_assoc] using
        normalizedXiGaussianSymmetricContour_eq_truncatedBottom_add_vertical t k R
    have hST : dist (S R) (T R) < epsilon := by
      calc
        dist (S R) (T R) = ‖c * V R‖ := by
          rw [← hcontour, hfold, dist_eq_norm]
          congr 1
          ring
        _ = ‖c‖ * ‖V R‖ := norm_mul _ _
        _ ≤ (‖c‖ + 1) * ‖V R‖ := by
          exact mul_le_mul_of_nonneg_right (by linarith [norm_nonneg c]) (norm_nonneg _)
        _ < (‖c‖ + 1) * delta :=
          mul_lt_mul_of_pos_left (by simpa only [V] using hVsmall) (by positivity)
        _ = epsilon := by
          dsimp only [delta]
          field_simp
    have htri := dist_triangle4 W (S R) (T R) B
    rw [dist_comm W (S R)] at htri
    dsimp only [epsilon] at hepsilon hspec hST hbottom
    nlinarith
  rw [show xiGaussianHeatMoment k t = normalizedXiGaussianBottomContribution t k by
    simpa only [W, B] using hWB,
    normalizedXiGaussianBottomContribution_eq_completedSource_div_pi ht k]

end
end RHTower

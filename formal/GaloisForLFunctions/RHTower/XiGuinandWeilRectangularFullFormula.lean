import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularVerticalResolvent
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularBottomSlope
import GaloisForLFunctions.RHTower.XiGuinandWeilRectanglePeeling

/-!
# Full sharp rectangular Guinand--Weil formula

The sharp rectangular test has only piecewise-linear Fourier regularity.  The bottom edge is
already absolutely integrable, while the preceding vertical-resolvent theorem supplies cofinal
vanishing without a zero-separation hypothesis.  This module combines those values with the exact
finite Xi factorization on symmetric rectangles.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Exact argument-principle extraction on a symmetric depth-one rectangle whose right edge
avoids all Xi spectral real coordinates.  Evenness of `XiC` then also clears the left edge. -/
theorem rectIntegral_rectangularLogDeriv_symmetric_eq_xiZeroCopy_sum
    (L a R : ℝ) (hR : 0 < R)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    rectIntegral
        (fun z => xiRectangularTwoEdgeTransform L a z ^ (2 : ℕ) * logDeriv XiC z)
        (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I) =
      2 * Real.pi * I *
        ∑ q ∈ xiZeroCopyClosedRectangle
          (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I),
          xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ (2 : ℕ) := by
  let z₁ : ℂ := (((-R : ℝ) : ℂ) - I)
  let z₂ : ℂ := (((R : ℝ) : ℂ) + I)
  let g : ℂ → ℂ := fun z => xiRectangularTwoEdgeTransform L a z ^ (2 : ℕ)
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
    (xiRectangularTwoEdgeTransform_sq_analyticOnNhd L a)
    hUopen hin hsub (fun z _ => hhan z (Set.mem_univ z))
    (fun _ hz => hz) (fun z _ => hfact z)
  calc
    rectIntegral
        (fun z => xiRectangularTwoEdgeTransform L a z ^ (2 : ℕ) * logDeriv XiC z)
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
          xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ (2 : ℕ) := by
      rfl

/-- Symmetric Xi contour normalized by the argument-principle factor. -/
def normalizedRectangularSymmetricXiContour (L a R : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    rectIntegral
      (fun z => xiRectangularTwoEdgeTransform L a z ^ (2 : ℕ) * logDeriv XiC z)
      (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I)

/-- Truncated version of the normalized literal Xi bottom edge. -/
def normalizedRectangularTruncatedBottomXiContribution (L a R : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    (2 * ∫ x in -R..R, rectangularBottomXiLogDerivIntegrand L a x)

/-- On every admissible symmetric radius, the normalized contour is the exact finite copied Xi
value sum in the depth-one rectangle. -/
theorem normalizedRectangularSymmetricXiContour_eq_xiZeroCopy_sum
    (L a R : ℝ) (hR : 0 < R)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    normalizedRectangularSymmetricXiContour L a R =
      ∑ q ∈ xiZeroCopyClosedRectangle
        (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I),
        xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ (2 : ℕ) := by
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  rw [normalizedRectangularSymmetricXiContour,
    rectIntegral_rectangularLogDeriv_symmetric_eq_xiZeroCopy_sum L a R hR havoid]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- Exact bottom-plus-vertical decomposition of the normalized symmetric Xi contour. -/
theorem normalizedRectangularSymmetricXiContour_eq_truncatedBottom_add_vertical
    (L a R : ℝ) :
    normalizedRectangularSymmetricXiContour L a R =
      normalizedRectangularTruncatedBottomXiContribution L a R +
        (2 * Real.pi * I)⁻¹ * 2 * I *
          (∫ y in (-1 : ℝ)..1,
            xiRectangularTwoEdgeTransform L a ((R : ℂ) + y * I) ^ (2 : ℕ) *
              logDeriv XiC ((R : ℂ) + y * I)) := by
  have hfold := rectIntegral_rectangularLogDeriv_symmetric L a R 1
  norm_num at hfold
  rw [normalizedRectangularSymmetricXiContour]
  simp only [ofReal_neg]
  rw [hfold]
  unfold normalizedRectangularTruncatedBottomXiContribution
  simp only [rectangularBottomXiLogDerivIntegrand]
  ring

/-- The truncated literal Xi bottom edge converges to the already formalized complete bottom
contribution. -/
theorem tendsto_normalizedRectangularTruncatedBottomXiContribution_atTop
    (L a : ℝ) :
    Tendsto (normalizedRectangularTruncatedBottomXiContribution L a)
      atTop (𝓝 (normalizedRectangularBottomXiContribution L a)) := by
  have hraw : Tendsto
      (fun R : ℝ => ∫ x in -R..R, rectangularBottomXiLogDerivIntegrand L a x)
      atTop (𝓝 (∫ x : ℝ, rectangularBottomXiLogDerivIntegrand L a x)) :=
    intervalIntegral_tendsto_integral
      (integrable_rectangularBottomXiLogDerivIntegrand L a)
      (tendsto_neg_atBot_iff.mpr tendsto_id) tendsto_id
  have hscaled := (hraw.const_mul (2 : ℂ)).const_mul (2 * Real.pi * I)⁻¹
  simpa only [normalizedRectangularTruncatedBottomXiContribution,
    normalizedRectangularBottomXiContribution] using! hscaled

/-- Symmetric depth-one spectral rectangles exhaust the complete sharp rectangular Xi value. -/
theorem tendsto_symmetric_xiZeroCopy_rectangular_sum_atTop (L a : ℝ) :
    Tendsto
      (fun R : ℝ =>
        ∑ q ∈ xiZeroCopyClosedRectangle
          (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I),
          xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ (2 : ℕ))
      atTop
      (𝓝 (xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
        (xiRectangularTwoEdgeTransform L a))) := by
  rw [xiWeilPolarization_rectangular_eq_tsum_sq]
  let f : XiZeroCopy → ℂ := fun q =>
    xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ (2 : ℕ)
  have hsum : Summable f := xiRectangularTwoEdgeTransform_sq_summable L a
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
      (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I) := by
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
      simp only [sub_re, ofReal_re, I_re, sub_zero, add_re]
      constructor <;> linarith [neg_le_abs (xiSpectralPoint q).re,
        le_abs_self (xiSpectralPoint q).re]
    · rw [uIcc_of_le (by simp)]
      simp only [sub_im, ofReal_im, I_im, zero_sub, add_im, zero_add]
      constructor <;> linarith
  have hnear := ht
    (xiZeroCopyClosedRectangle (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I))
    hpacket
  rw [Metric.mem_ball] at hnear
  simpa only [f] using hnear

/-- **Full sharp rectangular Guinand--Weil identity.**  At the exact piecewise-linear
rectangular regularity, the complete Xi polarization equals the literal absolutely convergent
bottom-edge value.  All contour limits, divisor multiplicities, and sum--integral exchanges are
discharged internally. -/
theorem xiWeilPolarization_rectangular_eq_normalizedBottomXiContribution
    (L a : ℝ) :
    xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
        (xiRectangularTwoEdgeTransform L a) =
      normalizedRectangularBottomXiContribution L a := by
  let W : ℂ := xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
    (xiRectangularTwoEdgeTransform L a)
  let B : ℂ := normalizedRectangularBottomXiContribution L a
  let S : ℝ → ℂ := fun R =>
    ∑ q ∈ xiZeroCopyClosedRectangle
      (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I),
      xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ (2 : ℕ)
  let T : ℝ → ℂ := normalizedRectangularTruncatedBottomXiContribution L a
  let V : ℝ → ℂ := fun R =>
    ∫ y in (-1 : ℝ)..1,
      xiRectangularTwoEdgeTransform L a ((R : ℂ) + y * I) ^ (2 : ℕ) *
        logDeriv XiC ((R : ℂ) + y * I)
  let c : ℂ := (2 * Real.pi * I)⁻¹ * 2 * I
  change W = B
  by_contra hWB
  have hd : 0 < dist W B := dist_pos.mpr hWB
  let epsilon : ℝ := dist W B / 4
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  have hS : Tendsto S atTop (𝓝 W) := by
    simpa only [S, W] using tendsto_symmetric_xiZeroCopy_rectangular_sum_atTop L a
  have hT : Tendsto T atTop (𝓝 B) := by
    simpa only [T, B] using
      tendsto_normalizedRectangularTruncatedBottomXiContribution_atTop L a
  obtain ⟨XS, hXS⟩ := (Metric.tendsto_atTop.mp hS) epsilon hepsilon
  obtain ⟨XT, hXT⟩ := (Metric.tendsto_atTop.mp hT) epsilon hepsilon
  let delta : ℝ := epsilon / (‖c‖ + 1)
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  obtain ⟨R, hRX, hR, havoid, hVsmall⟩ :=
    exists_large_integral_rectangular_mul_logDeriv_XiC_norm_lt
      L a (max XS XT) hdelta
  have hRXS : XS ≤ R :=
    le_trans (le_max_left XS XT) (le_of_lt hRX)
  have hRXT : XT ≤ R :=
    le_trans (le_max_right XS XT) (le_of_lt hRX)
  have hspec : dist (S R) W < epsilon := hXS R hRXS
  have hbottom : dist (T R) B < epsilon := hXT R hRXT
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hcontour : normalizedRectangularSymmetricXiContour L a R = S R := by
    simpa only [S] using
      normalizedRectangularSymmetricXiContour_eq_xiZeroCopy_sum
        L a R hRpos havoid
  have hfold : normalizedRectangularSymmetricXiContour L a R =
      T R + c * V R := by
    simpa only [T, c, V, mul_assoc] using
      normalizedRectangularSymmetricXiContour_eq_truncatedBottom_add_vertical L a R
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

/-- Prime--Gamma form of the full sharp rectangular Guinand--Weil identity. -/
theorem xiWeilPolarization_rectangular_eq_prime_add_arch
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
        (xiRectangularTwoEdgeTransform L a) =
      -2 * (rectangularPrimeAutocorrelationSum L a : ℂ) +
        normalizedRectangularBottomArchContribution L a := by
  rw [xiWeilPolarization_rectangular_eq_normalizedBottomXiContribution,
    normalizedRectangularBottomXiContribution_eq_prime_add_arch hL ha]

/-- Corrected full Xi-Weil value: remove the Gamma edge and restore the elementary polar square. -/
def rectangularCorrectedXiWeilValue (L a : ℝ) : ℝ :=
  (xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
      (xiRectangularTwoEdgeTransform L a) -
    normalizedRectangularBottomArchContribution L a).re +
      2 * rectangularEvenPolarFeature L a ^ (2 : ℕ)

/-- The corrected full Xi spectral value is exactly the previously computed corrected bottom
value, now with the contour limit eliminated. -/
theorem rectangularCorrectedXiWeilValue_eq_correctedBottomXiValue (L a : ℝ) :
    rectangularCorrectedXiWeilValue L a = rectangularCorrectedBottomXiValue L a := by
  rw [rectangularCorrectedXiWeilValue, rectangularCorrectedBottomXiValue,
    xiWeilPolarization_rectangular_eq_normalizedBottomXiContribution]

/-- The corrected full Xi spectral value is exactly the finite rectangular prime--polar source. -/
theorem rectangularCorrectedXiWeilValue_eq_primePolarSource
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    rectangularCorrectedXiWeilValue L a =
      rectangularPrimePolarSourceCoefficient L a := by
  rw [rectangularCorrectedXiWeilValue_eq_correctedBottomXiValue,
    rectangularCorrectedBottomXiValue_eq_primePolarSource hL ha]

/-- The diagonal derivative of the corrected full Xi-Weil value reads the sharp dyadic prime
shell directly. -/
theorem hasDerivWithinAt_dyadicCorrectedXiWeilValue_diagonal_logSample
    {n : ℕ} (hn : 4 ≤ n) :
    HasDerivWithinAt
      (fun t : ℝ =>
        rectangularCorrectedXiWeilValue (Real.log 2 / 2 + t)
          ((Real.log n + t) / 2))
      (dyadicPrimePolarSourceDiagonalRightSlope n) (Ici 0) 0 := by
  simpa only [rectangularCorrectedXiWeilValue_eq_correctedBottomXiValue] using
    hasDerivWithinAt_dyadicCorrectedBottomXiValue_diagonal_logSample hn

/-- A lower bound for the actual corrected Xi-Weil slope gives the target sharp dyadic
von-Mangoldt upper bound, with no contour or formal-interface hypothesis left. -/
theorem dyadicWeightedPrimeWindow_upper_of_correctedXiWeilSlope_lower
    {n : ℕ} (hn : 4 ≤ n) (C epsilon d : ℝ)
    (hderiv : HasDerivWithinAt
      (fun t : ℝ =>
        rectangularCorrectedXiWeilValue (Real.log 2 / 2 + t)
          ((Real.log n + t) / 2))
      d (Ici 0) 0)
    (hslope :
      8 * (Real.exp (Real.log 2 / 4) - Real.exp (-Real.log 2 / 4)) +
          4 * (Real.sqrt 2 - 1) / Real.sqrt n -
          2 * C * (n : ℝ) ^ epsilon ≤ d) :
    dyadicWeightedPrimeWindow n ≤
      2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
        C * (n : ℝ) ^ epsilon := by
  apply dyadicWeightedPrimeWindow_upper_of_correctedBottomXiSlope_lower
    hn C epsilon d
  · simpa only [rectangularCorrectedXiWeilValue_eq_correctedBottomXiValue] using hderiv
  · exact hslope

end

end RHTower

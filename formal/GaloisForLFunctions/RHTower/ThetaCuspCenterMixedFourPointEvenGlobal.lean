import GaloisForLFunctions.RHTower.ThetaCuspGlobalReflectedRiccati
import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedFourPointParityWall
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedCorrelationAngle

open Set MeasureTheory

namespace HilbertMetric

noncomputable section

theorem toeplitzFourEvenParityWall_cos_nonneg_of_concave_step
    {theta1 theta2 theta3 : ℝ}
    (h10 : 0 ≤ theta1) (h12 : theta1 ≤ theta2) (h23 : theta2 ≤ theta3)
    (h3half : theta3 ≤ Real.pi / 2)
    (hmid : (theta1 + theta3) / 2 ≤ theta2)
    (hthree : theta3 ≤ 3 * theta1) :
    0 ≤ (1 + Real.cos theta3) * (1 + Real.cos theta1) -
      (Real.cos theta1 + Real.cos theta2) ^ (2 : ℕ) := by
  have h20 : 0 ≤ theta2 := h10.trans h12
  have h30 : 0 ≤ theta3 := h20.trans h23
  have h1pi : theta1 ≤ Real.pi :=
    h12.trans (h23.trans (h3half.trans (by linarith [Real.pi_pos])))
  have h2pi : theta2 ≤ Real.pi :=
    h23.trans (h3half.trans (by linarith [Real.pi_pos]))
  have hmid0 : 0 ≤ (theta1 + theta3) / 2 := by linarith
  have hdiff0 : 0 ≤ (theta3 - theta1) / 2 := by linarith
  have hdiffle : (theta3 - theta1) / 2 ≤ theta1 := by linarith
  have hcosMid : Real.cos theta2 ≤ Real.cos ((theta1 + theta3) / 2) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hmid0 h2pi hmid
  have hcosDiff : Real.cos theta1 ≤ Real.cos ((theta3 - theta1) / 2) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hdiff0 h1pi hdiffle
  let X := Real.cos (theta3 / 2) * Real.cos (theta1 / 2)
  let Y := Real.cos ((theta1 + theta2) / 2) * Real.cos ((theta2 - theta1) / 2)
  have htwoX : 2 * X = Real.cos ((theta3 - theta1) / 2) +
      Real.cos ((theta3 + theta1) / 2) := by
    dsimp [X]
    have h := Real.two_mul_cos_mul_cos (theta3 / 2) (theta1 / 2)
    rw [show theta3 / 2 - theta1 / 2 = (theta3 - theta1) / 2 by ring,
      show theta3 / 2 + theta1 / 2 = (theta3 + theta1) / 2 by ring] at h
    simpa only [mul_assoc] using h
  have htwoY : 2 * Y = Real.cos theta1 + Real.cos theta2 := by
    dsimp [Y]
    have h := Real.two_mul_cos_mul_cos ((theta1 + theta2) / 2)
      ((theta2 - theta1) / 2)
    rw [show (theta1 + theta2) / 2 - (theta2 - theta1) / 2 = theta1 by ring,
      show (theta1 + theta2) / 2 + (theta2 - theta1) / 2 = theta2 by ring] at h
    simpa only [mul_assoc] using h
  have hYX : Y ≤ X := by
    rw [show (theta3 + theta1) / 2 = (theta1 + theta3) / 2 by ring] at htwoX
    linarith
  have hX0 : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩)
  have hY0 : 0 ≤ Y := by
    dsimp [Y]
    exact mul_nonneg
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩)
  have hsq : Y ^ (2 : ℕ) ≤ X ^ (2 : ℕ) := (sq_le_sq₀ hY0 hX0).2 hYX
  have hcos1 : 1 + Real.cos theta1 = 2 * Real.cos (theta1 / 2) ^ (2 : ℕ) := by
    have h := Real.cos_two_mul (theta1 / 2)
    rw [show 2 * (theta1 / 2) = theta1 by ring] at h
    linarith
  have hcos3 : 1 + Real.cos theta3 = 2 * Real.cos (theta3 / 2) ^ (2 : ℕ) := by
    have h := Real.cos_two_mul (theta3 / 2)
    rw [show 2 * (theta3 / 2) = theta3 by ring] at h
    linarith
  rw [hcos1, hcos3, ← htwoY]
  dsimp [X] at hsq
  nlinarith

end

end HilbertMetric

namespace RHTower

noncomputable section

theorem thetaCuspReflectedSourceEvenParityWall_nonneg
    {u t : ℝ} (ht : 0 ≤ t) :
    0 ≤ toeplitzFourEvenParityWall
      (thetaCuspReflectedSourceProduct u 0)
      (thetaCuspReflectedSourceProduct u t)
      (thetaCuspReflectedSourceProduct u (2 * t))
      (thetaCuspReflectedSourceProduct u (3 * t)) := by
  let q : ℝ → ℝ := thetaCuspReflectedLogAction u
  let alpha : ℝ → ℝ := HilbertMetric.riccatiCorrelationAngle q
  let d : ℝ := thetaCuspReflectedSourceProduct u 0
  let p : ℝ → ℝ := thetaCuspReflectedSourceCorrelation u
  have hd : 0 < d := by
    dsimp [d, thetaCuspReflectedSourceProduct]
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  have hpPos (s : ℝ) : 0 < p s := by
    dsimp [p, thetaCuspReflectedSourceCorrelation]
    exact div_pos
      (mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)) hd
  have halpha (s : ℝ) : alpha s = Real.arccos (p s) := by
    dsimp [alpha, HilbertMetric.riccatiCorrelationAngle, q, p,
      thetaCuspReflectedSourceCorrelation, thetaCuspReflectedSourceProduct]
    rw [exp_neg_thetaCuspReflectedLogAction]
    congr 2
    simp [pow_two]
  have hconc : ConcaveOn ℝ (Icc 0 (3 * t)) alpha := by
    simpa only [alpha, q] using
      concaveOn_thetaCuspReflectedLogCorrelationAngle (u := u) (T := 3 * t)
        (mul_nonneg (by norm_num) ht)
  have halpha0 : alpha 0 = 0 := by
    rw [halpha]
    have hp0 : p 0 = 1 := by
      dsimp [p, thetaCuspReflectedSourceCorrelation]
      exact div_self hd.ne'
    rw [hp0, Real.arccos_one]
  have hraw12 : thetaCuspReflectedSourceProduct u (2 * t) ≤
      thetaCuspReflectedSourceProduct u t := by
    exact (strictAntiOn_thetaCuspFullSource_mul_reflect u).antitoneOn
      ht (mul_nonneg (by norm_num) ht) (by linarith)
  have hraw23 : thetaCuspReflectedSourceProduct u (3 * t) ≤
      thetaCuspReflectedSourceProduct u (2 * t) := by
    exact (strictAntiOn_thetaCuspFullSource_mul_reflect u).antitoneOn
      (mul_nonneg (by norm_num) ht) (mul_nonneg (by norm_num) ht) (by linarith)
  have hp12 : p (2 * t) ≤ p t := by
    dsimp [p, thetaCuspReflectedSourceCorrelation]
    exact div_le_div_of_nonneg_right hraw12 hd.le
  have hp23 : p (3 * t) ≤ p (2 * t) := by
    dsimp [p, thetaCuspReflectedSourceCorrelation]
    exact div_le_div_of_nonneg_right hraw23 hd.le
  have ha12 : alpha t ≤ alpha (2 * t) := by
    rw [halpha, halpha]
    exact Real.arccos_le_arccos hp12
  have ha23 : alpha (2 * t) ≤ alpha (3 * t) := by
    rw [halpha, halpha]
    exact Real.arccos_le_arccos hp23
  have ha10 : 0 ≤ alpha t := by rw [halpha]; exact Real.arccos_nonneg _
  have ha3half : alpha (3 * t) ≤ Real.pi / 2 := by
    rw [halpha]
    exact Real.arccos_le_pi_div_two.mpr (hpPos _).le
  have htmem : t ∈ Icc (0 : ℝ) (3 * t) := ⟨ht, by linarith⟩
  have h3tmem : 3 * t ∈ Icc (0 : ℝ) (3 * t) :=
    ⟨mul_nonneg (by norm_num) ht, le_rfl⟩
  have hmidRaw := hconc.2 htmem h3tmem
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hmid : (alpha t + alpha (3 * t)) / 2 ≤ alpha (2 * t) := by
    calc
      (alpha t + alpha (3 * t)) / 2 =
          (1 / 2 : ℝ) * alpha t + (1 / 2 : ℝ) * alpha (3 * t) := by ring
      _ ≤ alpha ((1 / 2 : ℝ) * t + (1 / 2 : ℝ) * (3 * t)) := by
        simpa only [smul_eq_mul] using hmidRaw
      _ = alpha (2 * t) := by congr 1; ring
  have ha2sub : alpha (2 * t) ≤ alpha t + alpha t := by
    have h := HilbertMetric.correlationAngle_subadditive_of_concaveOn hconc halpha0 ht ht
      (by linarith : t + t ≤ 3 * t)
    have heq : t + t = 2 * t := by ring
    simpa only [heq] using h
  have ha3sub : alpha (3 * t) ≤ alpha t + alpha (2 * t) := by
    have h := HilbertMetric.correlationAngle_subadditive_of_concaveOn hconc halpha0 ht
      (mul_nonneg (by norm_num) ht) (by linarith : t + 2 * t ≤ 3 * t)
    have heq : t + 2 * t = 3 * t := by ring
    simpa only [heq] using h
  have ha3three : alpha (3 * t) ≤ 3 * alpha t := by linarith
  have hnormalized :=
    HilbertMetric.toeplitzFourEvenParityWall_cos_nonneg_of_concave_step
      ha10 ha12 ha23 ha3half hmid ha3three
  rw [halpha, halpha, halpha] at hnormalized
  have hcos (s : ℝ) (hs : 0 ≤ s) : Real.cos (Real.arccos (p s)) = p s := by
    apply Real.cos_arccos
    · have := (hpPos s).le
      linarith
    · have hraw := (strictAntiOn_thetaCuspFullSource_mul_reflect u).antitoneOn
        (by norm_num : (0 : ℝ) ∈ Ici 0) hs hs
      have hraw' : thetaCuspReflectedSourceProduct u s ≤ d := by
        simpa only [thetaCuspReflectedSourceProduct, d] using hraw
      dsimp [p, thetaCuspReflectedSourceCorrelation]
      exact (div_le_one hd).mpr hraw'
  rw [hcos t ht, hcos (2 * t) (mul_nonneg (by norm_num) ht),
    hcos (3 * t) (mul_nonneg (by norm_num) ht)] at hnormalized
  have hscale (s : ℝ) : d * p s = thetaCuspReflectedSourceProduct u s := by
    dsimp [p, thetaCuspReflectedSourceCorrelation]
    exact mul_div_cancel₀ _ hd.ne'
  have hd2 : 0 < d ^ (2 : ℕ) := sq_pos_of_pos hd
  dsimp [toeplitzFourEvenParityWall]
  rw [← hscale 0, ← hscale t, ← hscale (2 * t), ← hscale (3 * t)]
  calc
    0 ≤ d ^ (2 : ℕ) * ((1 + p (3 * t)) * (1 + p t) - (p t + p (2 * t)) ^ (2 : ℕ)) :=
      mul_nonneg hd2.le hnormalized
    _ = (d * p 0 + d * p (3 * t)) * (d * p 0 + d * p t) -
        (d * p t + d * p (2 * t)) ^ (2 : ℕ) := by
      have hp0 : p 0 = 1 := by
        dsimp [p, thetaCuspReflectedSourceCorrelation]
        exact div_self hd.ne'
      rw [hp0]
      ring

/-- Reflection-even block of one unnormalized reflected source fibre. -/
def thetaCuspReflectedSourceFourPlusBlock (u t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  toeplitzFourPlusBlock
    (thetaCuspReflectedSourceProduct u 0)
    (thetaCuspReflectedSourceProduct u t)
    (thetaCuspReflectedSourceProduct u (2 * t))
    (thetaCuspReflectedSourceProduct u (3 * t))

theorem thetaCuspReflectedSourceFourPlusBlock_posSemidef
    {u t : ℝ} (ht : 0 ≤ t) :
    Matrix.PosSemidef (thetaCuspReflectedSourceFourPlusBlock u t) := by
  let P : ℝ → ℝ := thetaCuspReflectedSourceProduct u
  have hp0 : 0 < P 0 := by
    dsimp [P, thetaCuspReflectedSourceProduct]
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  have hp3 : 0 < P (3 * t) := by
    dsimp [P, thetaCuspReflectedSourceProduct]
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  change Matrix.PosSemidef
    (symmetricTwoByTwo (P 0 + P (3 * t)) (P t + P (2 * t)) (P 0 + P t))
  rw [symmetricTwoByTwo_posSemidef_iff_det_nonneg_of_pos_left (add_pos hp0 hp3)]
  simpa only [toeplitzFourEvenParityWall, P] using
    thetaCuspReflectedSourceEvenParityWall_nonneg (u := u) ht

/-- Positive source kernel whose integral is the center-mixed reflection-even block. -/
def thetaCuspCenterMixedFourPlusSourceKernel
    (a t r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (r * Real.sinh (a * r)) • thetaCuspReflectedSourceFourPlusBlock (r / 2) t

theorem integral_thetaCuspCenterMixedFourPlusSourceKernel
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    HTGeometry.integralMatrixKernel (volume.restrict (Ioi 0))
        (thetaCuspCenterMixedFourPlusSourceKernel a t) =
      toeplitzFourPlusBlock
        (thetaCuspCenterMixedDensity a 0)
        (thetaCuspCenterMixedDensity a t)
        (thetaCuspCenterMixedDensity a (2 * t))
        (thetaCuspCenterMixedDensity a (3 * t)) := by
  have hadd (x y : ℝ) :
      (∫ r : ℝ in Ioi 0, r * Real.sinh (a * r) *
        (thetaCuspFullSource (r / 2 + x) * thetaCuspFullSource (r / 2 - x) +
          thetaCuspFullSource (r / 2 + y) * thetaCuspFullSource (r / 2 - y))) =
        thetaCuspCenterMixedDensity a x + thetaCuspCenterMixedDensity a y := by
    have hx : Integrable
        (fun r : ℝ => r * Real.sinh (a * r) *
          (thetaCuspFullSource (r / 2 + x) * thetaCuspFullSource (r / 2 - x)))
        (volume.restrict (Ioi 0)) := by
      simpa only [IntegrableOn] using
        integrableOn_thetaCuspCenterMixedIntegrand ha0 ha x
    have hy : Integrable
        (fun r : ℝ => r * Real.sinh (a * r) *
          (thetaCuspFullSource (r / 2 + y) * thetaCuspFullSource (r / 2 - y)))
        (volume.restrict (Ioi 0)) := by
      simpa only [IntegrableOn] using
        integrableOn_thetaCuspCenterMixedIntegrand ha0 ha y
    calc
      _ = ∫ r : ℝ in Ioi 0,
          (r * Real.sinh (a * r) *
            (thetaCuspFullSource (r / 2 + x) * thetaCuspFullSource (r / 2 - x))) +
          (r * Real.sinh (a * r) *
            (thetaCuspFullSource (r / 2 + y) * thetaCuspFullSource (r / 2 - y))) := by
              congr 1
              funext r
              rw [mul_add]
      _ = (∫ r : ℝ in Ioi 0, r * Real.sinh (a * r) *
            (thetaCuspFullSource (r / 2 + x) * thetaCuspFullSource (r / 2 - x))) +
          (∫ r : ℝ in Ioi 0, r * Real.sinh (a * r) *
            (thetaCuspFullSource (r / 2 + y) * thetaCuspFullSource (r / 2 - y))) :=
        MeasureTheory.integral_add hx hy
      _ = thetaCuspCenterMixedDensity a x + thetaCuspCenterMixedDensity a y := rfl
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [HTGeometry.integralMatrixKernel, thetaCuspCenterMixedFourPlusSourceKernel,
      thetaCuspReflectedSourceFourPlusBlock, thetaCuspReflectedSourceProduct,
      toeplitzFourPlusBlock] using hadd 0 (3 * t)
  · simpa [HTGeometry.integralMatrixKernel, thetaCuspCenterMixedFourPlusSourceKernel,
      thetaCuspReflectedSourceFourPlusBlock, thetaCuspReflectedSourceProduct,
      toeplitzFourPlusBlock] using hadd t (2 * t)
  · simpa [HTGeometry.integralMatrixKernel, thetaCuspCenterMixedFourPlusSourceKernel,
      thetaCuspReflectedSourceFourPlusBlock, thetaCuspReflectedSourceProduct,
      toeplitzFourPlusBlock] using hadd t (2 * t)
  · simpa [HTGeometry.integralMatrixKernel, thetaCuspCenterMixedFourPlusSourceKernel,
      thetaCuspReflectedSourceFourPlusBlock, thetaCuspReflectedSourceProduct,
      toeplitzFourPlusBlock] using hadd 0 t

theorem thetaCuspCenterMixedFourPlusBlock_posSemidef
    {a t : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (ht : 0 ≤ t) :
    Matrix.PosSemidef
      (toeplitzFourPlusBlock
        (thetaCuspCenterMixedDensity a 0)
        (thetaCuspCenterMixedDensity a t)
        (thetaCuspCenterMixedDensity a (2 * t))
        (thetaCuspCenterMixedDensity a (3 * t))) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let kernel := thetaCuspCenterMixedFourPlusSourceKernel a t
  have hint (x y : ℝ) : Integrable
      (fun r : ℝ => r * Real.sinh (a * r) *
        (thetaCuspReflectedSourceProduct (r / 2) x +
          thetaCuspReflectedSourceProduct (r / 2) y)) mu := by
    have hsum := (integrableOn_thetaCuspCenterMixedIntegrand ha0.le ha x).add
      (integrableOn_thetaCuspCenterMixedIntegrand ha0.le ha y)
    have hsum' : Integrable
        ((fun r : ℝ => r * Real.sinh (a * r) *
          (thetaCuspFullSource (r / 2 + x) * thetaCuspFullSource (r / 2 - x))) +
        (fun r : ℝ => r * Real.sinh (a * r) *
          (thetaCuspFullSource (r / 2 + y) * thetaCuspFullSource (r / 2 - y)))) mu := by
      simpa only [mu, IntegrableOn] using hsum
    apply hsum'.congr
    filter_upwards with r
    simp only [Pi.add_apply]
    unfold thetaCuspReflectedSourceProduct
    rw [mul_add]
  have hentry : ∀ i j, Integrable (fun r => kernel r i j) mu := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [kernel, thetaCuspCenterMixedFourPlusSourceKernel,
        thetaCuspReflectedSourceFourPlusBlock, toeplitzFourPlusBlock] using hint 0 (3 * t)
    · simpa [kernel, thetaCuspCenterMixedFourPlusSourceKernel,
        thetaCuspReflectedSourceFourPlusBlock, toeplitzFourPlusBlock] using hint t (2 * t)
    · simpa [kernel, thetaCuspCenterMixedFourPlusSourceKernel,
        thetaCuspReflectedSourceFourPlusBlock, toeplitzFourPlusBlock] using hint t (2 * t)
    · simpa [kernel, thetaCuspCenterMixedFourPlusSourceKernel,
        thetaCuspReflectedSourceFourPlusBlock, toeplitzFourPlusBlock] using hint 0 t
  have hkernel : ∀ r, Matrix.PosSemidef (kernel r) := by
    intro r
    have hweight : 0 ≤ r * Real.sinh (a * r) := by
      rcases le_total 0 r with hr | hr
      · exact mul_nonneg hr
          (Real.sinh_nonneg_iff.mpr (mul_nonneg ha0.le hr))
      · exact mul_nonneg_of_nonpos_of_nonpos hr
          (Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ha0.le hr))
    exact (thetaCuspReflectedSourceFourPlusBlock_posSemidef (u := r / 2) ht).smul hweight
  have hintegral := HTGeometry.integralMatrixKernel_posSemidef mu kernel hentry hkernel
  rw [show HTGeometry.integralMatrixKernel mu kernel =
      toeplitzFourPlusBlock
        (thetaCuspCenterMixedDensity a 0)
        (thetaCuspCenterMixedDensity a t)
        (thetaCuspCenterMixedDensity a (2 * t))
        (thetaCuspCenterMixedDensity a (3 * t)) by
    simpa only [mu, kernel] using
      integral_thetaCuspCenterMixedFourPlusSourceKernel ha0.le ha t] at hintegral
  exact hintegral

theorem thetaCuspCenterMixedEvenParityWall_nonneg_global
    {a t : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (ht : 0 ≤ t) :
    0 ≤ thetaCuspCenterMixedEvenParityWall a t := by
  have hpsd := thetaCuspCenterMixedFourPlusBlock_posSemidef ha0 ha ht
  have hleft : 0 < thetaCuspCenterMixedDensity a 0 +
      thetaCuspCenterMixedDensity a (3 * t) :=
    add_pos (thetaCuspCenterMixedDensity_pos ha0 ha 0)
      (thetaCuspCenterMixedDensity_pos ha0 ha (3 * t))
  change 0 ≤ toeplitzFourEvenParityWall
    (thetaCuspCenterMixedDensity a 0)
    (thetaCuspCenterMixedDensity a t)
    (thetaCuspCenterMixedDensity a (2 * t))
    (thetaCuspCenterMixedDensity a (3 * t))
  exact (symmetricTwoByTwo_posSemidef_iff_det_nonneg_of_pos_left hleft).mp hpsd

/-- Global rank-four positivity is controlled solely by the reflection-odd wall. -/
theorem thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_oddParityWall
    {a t : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (ht : 0 < t) :
    Matrix.PosSemidef (thetaCuspCenterMixedGramFourEquispaced a t) ↔
      0 ≤ thetaCuspCenterMixedOddParityWall a t := by
  rw [thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_parityWalls ha0 ha ht]
  exact and_iff_right (thetaCuspCenterMixedEvenParityWall_nonneg_global ha0 ha ht.le)

end

end RHTower

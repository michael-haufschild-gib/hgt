import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TypicalHeightXiModel
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.GaussianSaddleWindow
import GaloisForLFunctions.RHTower.KiKimLeeSharpFarTerms

/-!
# Half-Gaussian approximation at typical heights

The saddle may lie anywhere a fixed positive distance right of the
critical line. A polylogarithmic source ratio pays for the lower tail;
the Euler model controls the distant endpoint.
-/

open Complex Set MeasureTheory Filter
open _root_.RHTower _root_.RHTower.DeBruijn
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- The source ratio on the bounded lower interval. -/
def typicalXiTailFactor (η T : ℝ) : ℝ :=
  3 * ((1 + Real.log (4 * T)) ^ (4 : ℕ) + 2) *
    Real.exp (12 * (4 * Real.log (1 + Real.log (4 * T)) + 9) / η + 3)

theorem typicalXiTailFactor_pos (η T : ℝ) : 0 < typicalXiTailFactor η T := by
  unfold typicalXiTailFactor
  positivity

/-- Relative error in approximating the half transform by the full Gaussian model. -/
def typicalHalfGaussError (η T τ α : ℝ) : ℝ :=
  (1 + typicalXiTailFactor η T) * Real.exp (-(25 * η ^ 2 / τ)) + kklR2 τ α +
    gaussianSaddleModelError (typicalXiSlopeError η T) τ +
    Real.exp (9 / 2 * typicalXiSlopeError η T) * kklRC τ α

/-- Relative slope error of the half transform. -/
def typicalHalfGaussSlopeError (η T τ α : ℝ) : ℝ :=
  typicalXiTailFactor η T *
      (1 / (2 * τ) + α + 1 + (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ))) *
        Real.exp (-(25 * η ^ 2 / τ)) +
    Real.exp (9 / 2 * typicalXiSlopeError η T) * (kklRC τ α + kklRB τ α) +
    typicalXiSlopeError η T * (1 + gaussianSaddleModelError (typicalXiSlopeError η T) τ)

/-- Relative size of the opposite half away from the real axis. -/
def typicalHalfGaussOppositeError (η T τ α : ℝ) : ℝ :=
  typicalXiTailFactor η T * Real.exp (-(8 * η * α)) +
    Real.exp (-(8 * η ^ 2 / τ)) * (1 + gaussianSaddleModelError (typicalXiSlopeError η T) τ) +
    Real.exp (9 / 2 * typicalXiSlopeError η T) * kklRC τ α

private theorem typical_saddle_bounds {η τ α y : ℝ}
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hα3 : 3 ≤ α)
    (hc : 16 * η ≤ 2 * τ * α) (hc2 : 2 * τ * α ≤ 2)
    (hy : -(4 * η) ≤ y) (hy2 : y ≤ 1 / 2) :
    |y| ≤ 1 / 2 ∧ 2 * η ≤ y + 2 * τ * α ∧ y + 2 * τ * α ≤ 3 ∧
      9 / 2 ≤ 2 * τ * α + α ^ 2 ∧ y + 2 * τ * α ≤ 2 * τ * α + α ^ 2 := by
  have hαsq : 9 ≤ α ^ 2 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hα3 2
    norm_num at hp
    exact hp
  exact ⟨abs_le.mpr ⟨by linarith only [hy, hη8], hy2⟩,
    by linarith only [hc, hy, hη], by linarith only [hc2, hy2],
    by linarith only [hc, hη, hαsq], by linarith only [hy2, hαsq]⟩

/-- A fixed separation of the lower endpoint from the saddle gives uniform Gaussian decay. -/
theorem typical_saddle_lower_exponential_le {η τ α y : ℝ} (hη : 0 < η) (hτ : 0 < τ)
    (hc : 16 * η ≤ 2 * τ * α) (hy : -(4 * η) ≤ y) :
    Real.exp (-((y + 2 * τ * α - 2 * η) ^ 2 / (4 * τ))) ≤
      Real.exp (-(25 * η ^ 2 / τ)) := by
  have hgap : 10 * η ≤ y + 2 * τ * α - 2 * η := by linarith only [hc, hy]
  have hs := pow_le_pow_left₀ (show 0 ≤ 10 * η by positivity) hgap 2
  apply Real.exp_le_exp.mpr
  rw [neg_le_neg_iff, div_le_div_iff₀ hτ (by positivity)]
  nlinarith only [mul_le_mul_of_nonneg_right hs hτ.le]

/-- The actual half transform follows its saddle model below the Euler line. -/
theorem norm_halfGauss_sub_main_le_of_typical {η T t X τ y : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hT : 8 ≤ T) (hX : 200 ≤ X) (hXt : |X - t| ≤ η)
    (hτ : 0 < τ) (hτ8 : τ ≤ 1 / 8) (hα3 : 3 ≤ (horizontalSlope X).re)
    (hc : 16 * η ≤ 2 * τ * (horizontalSlope X).re)
    (hc2 : 2 * τ * (horizontalSlope X).re ≤ 2) (hy : -(4 * η) ≤ y) (hy2 : y ≤ 1 / 2)
    (hWX : 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2) :
    ‖halfGaussTransform τ (xiLine X) y -
        xiLine X (y + 2 * τ * (horizontalSlope X).re) *
          Complex.exp (-((y + 2 * τ * (horizontalSlope X).re : ℝ) * horizontalSlope X)) *
          Complex.exp (y * horizontalSlope X + τ * horizontalSlope X ^ 2)‖ ≤
      (‖xiLine X (y + 2 * τ * (horizontalSlope X).re)‖ *
        Real.exp (-(τ * (horizontalSlope X).re ^ 2))) *
          typicalHalfGaussError η T τ (horizontalSlope X).re := by
  let α := (horizontalSlope X).re
  let u := y + 2 * τ * α
  let W := 2 * τ * α + α ^ 2
  let N := ‖xiLine X u‖
  let P := N * Real.exp (-(τ * α ^ 2))
  let B := typicalXiSlopeError η T
  let C := typicalXiTailFactor η T
  let R := Real.exp (-(25 * η ^ 2 / τ))
  have hη1 : η ≤ 1 := by linarith only [hη8]
  have hB : 0 ≤ B := (typicalXiSlopeError_pos (by linarith only [hT])).le
  have hC : 0 ≤ C := (typicalXiTailFactor_pos η T).le
  have hN : 0 ≤ N := norm_nonneg _
  have hP : 0 ≤ P := by positivity
  obtain ⟨hyabs, hu0, hu3, hW9, huW⟩ := typical_saddle_bounds hη hη8 hα3 hc hc2 hy hy2
  have huX : u ∈ Icc (2 * η) (X / 32 - 1 / 2) := ⟨hu0, huW.trans hWX⟩
  have hmodel : ∀ w ∈ Icc (2 * η) W,
      ‖xiLine X w - xiLine X u * Complex.exp (((w - u : ℝ) : ℂ) * horizontalSlope X)‖ ≤
        N * Real.exp ((w - u) * α) * (Real.exp (B * |w - u|) - 1) :=
    fun w hw => norm_xiLine_sub_model_le_of_typical h hη hη1 hT hX hXt huX ⟨hw.1, hw.2.trans hWX⟩
  have hQ := norm_halfGaussTransform_sub_main_le hτ (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine hτ X) (y := y) hB (by positivity) (hu0.trans huW) hmodel
  have hR := typical_saddle_lower_exponential_le hη hτ hc hy
  have hlow : N * Real.exp (-(u * α)) *
      (∫ w in Iic (2 * η), gaussDensity τ (w - y) * Real.exp (w * α)) ≤ P * R := by
    exact (gaussian_saddle_lower_tail_le hτ hN hu0).trans (by gcongr)
  have hupp := upperTail_le (α := α) hτ hyabs hN
  have herr := gaussian_saddle_model_error_le (α := α) (y := y) hτ hB hN
  have hsource : ∀ w ∈ Ioc 0 (2 * η), ‖xiLine X w‖ ≤ C * N * Real.exp ((w - u) * α) := by
    intro w hw
    exact norm_xiLine_lower_interval_le_of_typical h hη hη1 hT hX hXt hu0 hu3 hw.1.le
      (by linarith only [hw.2, hη8])
  have hstrip : (∫ w in Ioc 0 (2 * η), gaussDensity τ (w - y) * ‖xiLine X w‖) ≤ C * (P * R) := by
    exact (gaussian_saddle_lower_source_mass_le (continuous_xiLine X) hτ hN hC hu0 hsource).trans
      (by gcongr)
  have hFW : ‖xiLine X W‖ ≤ (Real.exp (9 / 2 * B) * N) *
      Real.exp ((W - u) * (α + 1 / 8)) :=
    norm_xiLine_far_end_le_of_typical h hη hη1 hT hX hXt
      ⟨hu0, by linarith only [hu3]⟩ ⟨hW9, hWX⟩
  have hfar := (far_terms_le_of_bound hτ hτ8 hX hyabs
    (by linarith only [hα3]) hW9 hFW).2.1
  refine hQ.trans ?_
  calc
    _ = N * Real.exp (-(u * α)) *
          (∫ w in Iic (2 * η), gaussDensity τ (w - y) * Real.exp (w * α)) +
        N * Real.exp (-(u * α)) *
          (∫ w in Ioi W, gaussDensity τ (w - y) * Real.exp (w * α)) +
        N * Real.exp (-(u * α)) *
          (∫ w, gaussDensity τ (w - y) * Real.exp (w * α) * (Real.exp (B * |w - u|) - 1)) +
        (∫ w in Ioc 0 (2 * η), gaussDensity τ (w - y) * ‖xiLine X w‖) +
        (∫ w in Ioi W, gaussDensity τ (w - y) * ‖xiLine X w‖) := by ring
    _ ≤ P * R + P * kklR2 τ α + P * gaussianSaddleModelError B τ +
        C * (P * R) + (Real.exp (9 / 2 * B) * N) * Real.exp (-(τ * α ^ 2)) * kklRC τ α := by
      gcongr
    _ = P * typicalHalfGaussError η T τ α := by
      unfold typicalHalfGaussError
      dsimp only [P, B, C, R]
      ring

/-- The slope of the actual half transform has a uniform relative error. -/
theorem norm_halfGauss_slope_sub_le_of_typical {η T t X τ y : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hT : 8 ≤ T) (hX : 200 ≤ X) (hXt : |X - t| ≤ η)
    (hτ : 0 < τ) (hτ8 : τ ≤ 1 / 8) (hα3 : 3 ≤ (horizontalSlope X).re)
    (hc : 16 * η ≤ 2 * τ * (horizontalSlope X).re)
    (hc2 : 2 * τ * (horizontalSlope X).re ≤ 2) (hy : -(4 * η) ≤ y) (hy2 : y ≤ 1 / 2)
    (hWX : 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2) :
    ‖(∫ w in Ioi (0 : ℝ), (((w - y) / (2 * τ) * gaussDensity τ (w - y) : ℝ) : ℂ) * xiLine X w) -
        horizontalSlope X * halfGaussTransform τ (xiLine X) y‖ ≤
      (‖xiLine X (y + 2 * τ * (horizontalSlope X).re)‖ *
        Real.exp (-(τ * (horizontalSlope X).re ^ 2))) *
          typicalHalfGaussSlopeError η T τ (horizontalSlope X).re := by
  let α := (horizontalSlope X).re
  let u := y + 2 * τ * α
  let W := 2 * τ * α + α ^ 2
  let N := ‖xiLine X u‖
  let P := N * Real.exp (-(τ * α ^ 2))
  let B := typicalXiSlopeError η T
  let C := typicalXiTailFactor η T
  let R := Real.exp (-(25 * η ^ 2 / τ))
  let K := 1 / (2 * τ) + α + 1
  let A := (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ))
  have hη1 : η ≤ 1 := by linarith only [hη8]
  have hB : 0 ≤ B := (typicalXiSlopeError_pos (by linarith only [hT])).le
  have hC : 0 ≤ C := (typicalXiTailFactor_pos η T).le
  have hN : 0 ≤ N := norm_nonneg _
  have hP : 0 ≤ P := by positivity
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  obtain ⟨hyabs, hu0, hu3, hW9, huW⟩ := typical_saddle_bounds hη hη8 hα3 hc hc2 hy hy2
  have huX : u ∈ Icc (2 * η) (X / 32 - 1 / 2) := ⟨hu0, huW.trans hWX⟩
  have hderiv : ∀ w ∈ Icc (2 * η) W,
      ‖xiLineDeriv X w - horizontalSlope X * xiLine X w‖ ≤ B * ‖xiLine X w‖ :=
    fun w hw => norm_xiLineDeriv_sub_le_of_typical h hη hη1 hT hX hXt hw.1 (hw.2.trans hWX)
  have hD := norm_slope_sub_mul_le hτ (hasDerivAt_xiLine X) (continuous_xiLineDeriv X)
    (integrable_exp_mul_norm_xiLine hτ X) (y := y) (by positivity) (hu0.trans huW) hderiv
  have hR := typical_saddle_lower_exponential_le hη hτ hc hy
  have hsource : ∀ w ∈ Icc 0 (2 * η), ‖xiLine X w‖ ≤ C * N * Real.exp ((w - u) * α) := by
    intro w hw
    exact norm_xiLine_lower_interval_le_of_typical h hη hη1 hT hX hXt hu0 hu3 hw.1
      (by linarith only [hw.2, hη8])
  have hstrip : (∫ w in Ioc 0 (2 * η), gaussDensity τ (w - y) * ‖xiLine X w‖) ≤ C * (P * R) := by
    exact (gaussian_saddle_lower_source_mass_le (continuous_xiLine X) hτ hN hC hu0
      (fun w hw => hsource w ⟨hw.1.le, hw.2⟩)).trans (by gcongr)
  have hweight : (2 * η + |y|) / (2 * τ) + ‖horizontalSlope X‖ ≤ K := by
    have hd : (2 * η + |y|) / (2 * τ) ≤ 1 / (2 * τ) := by
      gcongr
      linarith only [hη8, hyabs]
    have hs := _root_.RHTower.DeBruijn.norm_horizontalSlope_le (X := X)
      (by linarith only [hα3])
    dsimp only [K, α]
    linarith only [hd, hs]
  have hweight0 : 0 ≤ (2 * η + |y|) / (2 * τ) + ‖horizontalSlope X‖ := by positivity
  have hOA : (∫ w in Ioc 0 (2 * η),
      (|(w - y) / (2 * τ)| + ‖horizontalSlope X‖) * gaussDensity τ (w - y) * ‖xiLine X w‖) ≤
        P * (C * K * R) := by
    calc
      _ ≤ ((2 * η + |y|) / (2 * τ) + ‖horizontalSlope X‖) *
          (∫ w in Ioc 0 (2 * η), gaussDensity τ (w - y) * ‖xiLine X w‖) :=
        gaussian_lower_interval_slope_mass_le (continuous_xiLine X) hτ (horizontalSlope X)
      _ ≤ ((2 * η + |y|) / (2 * τ) + ‖horizontalSlope X‖) * (C * (P * R)) :=
        mul_le_mul_of_nonneg_left hstrip hweight0
      _ ≤ K * (C * (P * R)) :=
        mul_le_mul_of_nonneg_right hweight (mul_nonneg hC (mul_nonneg hP hR0))
      _ = _ := by ring
  have hgauss : gaussDensity τ (2 * η - u) ≤ A * R := by
    unfold gaussDensity
    rw [show (2 * η - u) ^ 2 = (u - 2 * η) ^ 2 by ring]
    exact mul_le_mul_of_nonneg_left hR (by positivity)
  have hB1 : gaussDensity τ (2 * η - y) * ‖xiLine X (2 * η)‖ ≤ P * (C * A * R) := by
    calc
      _ ≤ C * P * gaussDensity τ (2 * η - u) :=
        gaussian_saddle_lower_endpoint_le hτ (hsource (2 * η) ⟨by positivity, le_rfl⟩)
      _ ≤ C * P * (A * R) := mul_le_mul_of_nonneg_left hgauss (mul_nonneg hC hP)
      _ = _ := by ring
  have hFW : ‖xiLine X W‖ ≤ (Real.exp (9 / 2 * B) * N) *
      Real.exp ((W - u) * (α + 1 / 8)) :=
    norm_xiLine_far_end_le_of_typical h hη hη1 hT hX hXt
      ⟨hu0, by linarith only [hu3]⟩ ⟨hW9, hWX⟩
  have hfar := far_terms_le_of_bound hτ hτ8 hX hyabs (by linarith only [hα3]) hW9 hFW
  have hM : (∫ w in Ioc (2 * η) W, gaussDensity τ (w - y) * ‖xiLine X w‖) ≤
      P * (1 + gaussianSaddleModelError B τ) :=
    gaussian_saddle_window_mass_le (continuous_xiLine X) hτ hB hN
      (fun w hw => norm_xiLine_le_model_of_typical h hη hη1 hT hX hXt huX
        ⟨hw.1.le, hw.2.trans hWX⟩)
  refine hD.trans ?_
  calc
    _ ≤ P * (C * K * R) +
        (Real.exp (9 / 2 * B) * N) * Real.exp (-(τ * α ^ 2)) * kklRC τ α +
        P * (C * A * R) +
        (Real.exp (9 / 2 * B) * N) * Real.exp (-(τ * α ^ 2)) * kklRB τ α +
        B * (P * (1 + gaussianSaddleModelError B τ)) := by
      exact add_le_add (add_le_add (add_le_add (add_le_add hOA hfar.1) hB1) hfar.2.2)
        (mul_le_mul_of_nonneg_left hM hB)
    _ = P * typicalHalfGaussSlopeError η T τ α := by
      unfold typicalHalfGaussSlopeError
      dsimp only [P, B, C, R, K, A]
      ring

private theorem integrable_gaussDensity_norm_xiLine {τ : ℝ} (hτ : 0 < τ) (X y : ℝ) :
    Integrable (fun w => gaussDensity τ (w - y) * ‖xiLine X w‖) := by
  refine (integrable_gaussDensity_sub_mul hτ (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine hτ X) y).norm.congr (Eventually.of_forall fun w => ?_)
  exact norm_gauss_mul τ y w hτ _

/-- The opposite half is small once the observation point is separated from the axis. -/
theorem norm_halfGauss_opposite_le_of_typical {η T t X τ y : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hT : 8 ≤ T) (hX : 200 ≤ X) (hXt : |X - t| ≤ η)
    (hτ : 0 < τ) (hτ8 : τ ≤ 1 / 8) (hα3 : 3 ≤ (horizontalSlope X).re)
    (hc : 16 * η ≤ 2 * τ * (horizontalSlope X).re)
    (hc2 : 2 * τ * (horizontalSlope X).re ≤ 2) (hy : 4 * η ≤ y) (hy2 : y ≤ 1 / 2)
    (hWX : 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2) :
    ‖halfGaussTransform τ (xiLine X) (-y)‖ ≤
      (‖xiLine X (y + 2 * τ * (horizontalSlope X).re)‖ *
        Real.exp (-(τ * (horizontalSlope X).re ^ 2))) *
          typicalHalfGaussOppositeError η T τ (horizontalSlope X).re := by
  let α := (horizontalSlope X).re
  let u := y + 2 * τ * α
  let W := 2 * τ * α + α ^ 2
  let N := ‖xiLine X u‖
  let P := N * Real.exp (-(τ * α ^ 2))
  let B := typicalXiSlopeError η T
  let C := typicalXiTailFactor η T
  have hη1 : η ≤ 1 := by linarith only [hη8]
  have hB : 0 ≤ B := (typicalXiSlopeError_pos (by linarith only [hT])).le
  have hC : 0 ≤ C := (typicalXiTailFactor_pos η T).le
  have hN : 0 ≤ N := norm_nonneg _
  have hP : 0 ≤ P := by positivity
  have hα0 : 0 ≤ α := by dsimp only [α]; linarith only [hα3]
  have hy0 : 0 ≤ y := by linarith only [hy, hη]
  have hylow : -(4 * η) ≤ y := by linarith only [hy, hη]
  have hE := gaussianSaddleModelError_nonneg (t := τ) hB
  obtain ⟨hyabs, hu0, hu3, hW9, huW⟩ := typical_saddle_bounds hη hη8 hα3 hc hc2 hylow hy2
  have huX : u ∈ Icc (2 * η) (X / 32 - 1 / 2) := ⟨hu0, huW.trans hWX⟩
  have hsource : ∀ w ∈ Ioc 0 (2 * η), ‖xiLine X w‖ ≤ C * N * Real.exp ((w - u) * α) := by
    intro w hw
    exact norm_xiLine_lower_interval_le_of_typical h hη hη1 hT hX hXt hu0 hu3 hw.1.le
      (by linarith only [hw.2, hη8])
  have hlow : (∫ w in Ioc 0 (2 * η), gaussDensity τ (w + y) * ‖xiLine X w‖) ≤
      P * (C * Real.exp (-(8 * η * α))) := by
    calc
      _ ≤ C * P * Real.exp (-(2 * α * y)) :=
        opposite_lower_interval_mass_le (continuous_xiLine X) hτ hN hC hsource
      _ ≤ C * P * Real.exp (-(8 * η * α)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hP)
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_left hy hα0]
      _ = _ := by ring
  have hM : (∫ w in Ioc (2 * η) W, gaussDensity τ (w - y) * ‖xiLine X w‖) ≤
      P * (1 + gaussianSaddleModelError B τ) :=
    gaussian_saddle_window_mass_le (continuous_xiLine X) hτ hB hN
      (fun w hw => norm_xiLine_le_model_of_typical h hη hη1 hT hX hXt huX
        ⟨hw.1.le, hw.2.trans hWX⟩)
  have hmidExp : Real.exp (-(2 * η * y / τ)) ≤ Real.exp (-(8 * η ^ 2 / τ)) := by
    have hp : 8 * η ^ 2 ≤ 2 * η * y := by
      nlinarith only [mul_le_mul_of_nonneg_left hy (show 0 ≤ 2 * η by positivity)]
    gcongr
  have hmid : (∫ w in Ioc (2 * η) W, gaussDensity τ (w + y) * ‖xiLine X w‖) ≤
      P * (Real.exp (-(8 * η ^ 2 / τ)) * (1 + gaussianSaddleModelError B τ)) := by
    calc
      _ ≤ Real.exp (-(2 * η * y / τ)) *
          (∫ w in Ioc (2 * η) W, gaussDensity τ (w - y) * ‖xiLine X w‖) :=
        opposite_window_mass_le (continuous_xiLine X) hτ hy0
      _ ≤ Real.exp (-(2 * η * y / τ)) * (P * (1 + gaussianSaddleModelError B τ)) := by
        gcongr
      _ ≤ Real.exp (-(8 * η ^ 2 / τ)) * (P * (1 + gaussianSaddleModelError B τ)) := by
        gcongr
      _ = _ := by ring
  have hreflect : (∫ w in Ioi W, gaussDensity τ (w + y) * ‖xiLine X w‖) ≤
      ∫ w in Ioi W, gaussDensity τ (w - y) * ‖xiLine X w‖ := by
    refine setIntegral_mono_on ?_ (integrable_gaussDensity_norm_xiLine hτ X y).integrableOn
      measurableSet_Ioi ?_
    · simpa only [sub_neg_eq_add] using (integrable_gaussDensity_norm_xiLine hτ X (-y)).integrableOn
    · intro w hw
      have hW0 : 0 ≤ W := (by norm_num : (0 : ℝ) ≤ 9 / 2).trans hW9
      have hg := gaussDensity_add_le_of_lower_bound (b := 0) hτ hy0
        (hW0.trans (show W < w from hw).le)
      have hm := mul_le_mul_of_nonneg_right hg (norm_nonneg (xiLine X w))
      simpa only [zero_mul, zero_div, neg_zero, Real.exp_zero, one_mul] using hm
  have hFW : ‖xiLine X W‖ ≤ (Real.exp (9 / 2 * B) * N) *
      Real.exp ((W - u) * (α + 1 / 8)) :=
    norm_xiLine_far_end_le_of_typical h hη hη1 hT hX hXt
      ⟨hu0, by linarith only [hu3]⟩ ⟨hW9, hWX⟩
  have hfar : (∫ w in Ioi W, gaussDensity τ (w + y) * ‖xiLine X w‖) ≤
      P * (Real.exp (9 / 2 * B) * kklRC τ α) := by
    calc
      _ ≤ ∫ w in Ioi W, gaussDensity τ (w - y) * ‖xiLine X w‖ := hreflect
      _ ≤ (Real.exp (9 / 2 * B) * N) * Real.exp (-(τ * α ^ 2)) * kklRC τ α :=
        (far_terms_le_of_bound hτ hτ8 hX hyabs (by linarith only [hα3]) hW9 hFW).2.1
      _ = _ := by dsimp only [P]; ring
  have hQ := norm_halfGaussTransform_le_three_masses (continuous_xiLine X)
    (y := -y) hτ (show 0 ≤ 2 * η by positivity) (hu0.trans huW)
    (integrable_exp_mul_norm_xiLine hτ X)
  simp only [sub_neg_eq_add] at hQ
  refine hQ.trans ?_
  calc
    _ ≤ P * (C * Real.exp (-(8 * η * α))) +
        P * (Real.exp (-(8 * η ^ 2 / τ)) * (1 + gaussianSaddleModelError B τ)) +
        P * (Real.exp (9 / 2 * B) * kklRC τ α) := add_le_add (add_le_add hlow hmid) hfar
    _ = P * typicalHalfGaussOppositeError η T τ α := by
      unfold typicalHalfGaussOppositeError
      dsimp only [B, C]
      ring

#print axioms norm_halfGauss_sub_main_le_of_typical
#print axioms norm_halfGauss_slope_sub_le_of_typical
#print axioms norm_halfGauss_opposite_le_of_typical

end

end GaloisForLFunctions.ZeroConfigurationGeometry

import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TypicalHeightXiModel
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.GaussianSaddleWindow
import GaloisForLFunctions.RHTower.KiKimLeeSharpFarTerms

/-!
# Half-Gaussian approximation at typical heights

The saddle may lie anywhere a fixed positive distance right of the
critical line. A polylogarithmic source ratio pays for the lower tail;
the Euler model controls the distant endpoint.
-/

open Complex Set MeasureTheory
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
  have hyabs : |y| ≤ 1 / 2 := abs_le.mpr ⟨by linarith only [hy, hη8], hy2⟩
  have hu0 : 2 * η ≤ u := by dsimp only [u, α]; linarith only [hc, hy, hη]
  have hu3 : u ≤ 3 := by dsimp only [u, α]; linarith only [hc2, hy2]
  have hαsq : 9 ≤ α ^ 2 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hα3 2
    norm_num at hp
    exact hp
  have hW9 : 9 / 2 ≤ W := by
    change 9 / 2 ≤ 2 * τ * α + α ^ 2
    have hc' : 16 * η ≤ 2 * τ * α := hc
    linarith only [hc', hη, hαsq]
  have huW : u ≤ W := by dsimp only [u, W]; linarith only [hy2, hαsq]
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

#print axioms norm_halfGauss_sub_main_le_of_typical

end

end GaloisForLFunctions.ZeroConfigurationGeometry

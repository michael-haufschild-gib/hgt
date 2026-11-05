import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TypicalHeightHalfGaussBounds

/-!
# Reality from typical-height half-Gaussian bounds

Close to the real axis, positivity of `Re(Q' conjugate Q)` makes the
modulus strictly increase. Farther away, the opposite half is directly
smaller than the saddle term. Both arguments use the actual `ξ` source.
-/

open Complex Set MeasureTheory
open _root_.RHTower _root_.RHTower.DeBruijn
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- The two relative errors control the sign of the actual half-transform slope. -/
theorem re_halfGauss_slope_pos_of_typical_errors {η T t X τ y : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hT : 8 ≤ T) (hX : 200 ≤ X) (hXt : |X - t| ≤ η)
    (hτ : 0 < τ) (hτ8 : τ ≤ 1 / 8) (hα3 : 3 ≤ (horizontalSlope X).re)
    (hc : 16 * η ≤ 2 * τ * (horizontalSlope X).re)
    (hc2 : 2 * τ * (horizontalSlope X).re ≤ 2) (hy : -(4 * η) ≤ y) (hy2 : y ≤ 1 / 2)
    (hWX : 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2)
    (hE : typicalHalfGaussError η T τ (horizontalSlope X).re ≤ 1 / 5)
    (hS : typicalHalfGaussSlopeError η T τ (horizontalSlope X).re < 18 / 25 * (horizontalSlope X).re) :
    0 < ((∫ w in Ioi (0 : ℝ), (((w - y) / (2 * τ) * gaussDensity τ (w - y) : ℝ) : ℂ) * xiLine X w) *
      starRingEnd ℂ (halfGaussTransform τ (xiLine X) y)).re := by
  let α := (horizontalSlope X).re
  let u := y + 2 * τ * α
  let P := ‖xiLine X u‖ * Real.exp (-(τ * α ^ 2))
  let Main := xiLine X u * Complex.exp (-((u : ℂ) * horizontalSlope X)) *
    Complex.exp (y * horizontalSlope X + τ * horizontalSlope X ^ 2)
  have hα0 : 0 ≤ α := by dsimp only [α]; linarith only [hα3]
  have hu : 2 * η ≤ u := by dsimp only [u, α]; linarith only [hc, hy, hη]
  have hN : 0 < ‖xiLine X u‖ := norm_pos_iff.mpr
    (xiLine_ne_zero_of_typical h hη (by linarith only [hη8]) hX hXt hu)
  have hP : 0 < P := mul_pos hN (Real.exp_pos _)
  have hmain : ‖Main‖ = P * Real.exp (-(τ * (Real.pi / 4) ^ 2)) :=
    norm_main_eq (t := τ) (X := X) (y := y) (xiLine X u)
  have hmainlow : 23 / 25 * P ≤ ‖Main‖ := by
    rw [hmain]
    nlinarith only [mul_le_mul_of_nonneg_left (gaussPhase_ge hτ8 hτ) hP.le]
  have hE' := mul_le_mul_of_nonneg_left hE hP.le
  have hgap : 18 / 25 * P ≤ ‖Main‖ - P * typicalHalfGaussError η T τ α := by
    linarith only [hmainlow, hE']
  have hQ := norm_halfGauss_sub_main_le_of_typical h hη hη8 hT hX hXt hτ hτ8 hα3
    hc hc2 hy hy2 hWX
  have hD := norm_halfGauss_slope_sub_le_of_typical h hη hη8 hT hX hXt hτ hτ8 hα3
    hc hc2 hy hy2 hWX
  refine re_mul_conj_pos_of_estimates (Main := Main) hα0 hQ hD ?_ ?_
  · nlinarith only [hE', hmainlow, hP]
  · calc
      P * typicalHalfGaussSlopeError η T τ α < P * (18 / 25 * α) :=
        mul_lt_mul_of_pos_left hS hP
      _ = α * (18 / 25 * P) := by ring
      _ ≤ α * (‖Main‖ - P * typicalHalfGaussError η T τ α) :=
        mul_le_mul_of_nonneg_left hgap hα0

/-- Positive and opposite halves have strictly different moduli throughout the upper strip. -/
theorem norm_halfGauss_opposite_lt_of_typical_errors {η T t X τ y : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hT : 8 ≤ T) (hX : 200 ≤ X) (hXt : |X - t| ≤ η)
    (hτ : 0 < τ) (hτ8 : τ ≤ 1 / 8) (hα3 : 3 ≤ (horizontalSlope X).re)
    (hc : 16 * η ≤ 2 * τ * (horizontalSlope X).re)
    (hc2 : 2 * τ * (horizontalSlope X).re ≤ 2) (hy : 0 < y) (hy2 : y ≤ 1 / 2)
    (hWX : 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2)
    (hE : typicalHalfGaussError η T τ (horizontalSlope X).re ≤ 1 / 5)
    (hS : typicalHalfGaussSlopeError η T τ (horizontalSlope X).re < 18 / 25 * (horizontalSlope X).re)
    (hO : typicalHalfGaussOppositeError η T τ (horizontalSlope X).re ≤ 1 / 2) :
    ‖halfGaussTransform τ (xiLine X) (-y)‖ < ‖halfGaussTransform τ (xiLine X) y‖ := by
  rcases le_or_gt y (4 * η) with hnear | hfar
  · exact norm_lt_norm_of_re_mul_conj_pos (b := 4 * η)
      (fun v _ => hasDerivAt_halfGaussTransform hτ (continuous_xiLine X)
        (integrable_exp_mul_norm_xiLine hτ X) v)
      (fun v hv => re_halfGauss_slope_pos_of_typical_errors h hη hη8 hT hX hXt hτ hτ8 hα3
        hc hc2 hv.1 (by linarith only [hv.2, hη8]) hWX hE hS) hy hnear
  · let α := (horizontalSlope X).re
    let u := y + 2 * τ * α
    let P := ‖xiLine X u‖ * Real.exp (-(τ * α ^ 2))
    let Main := xiLine X u * Complex.exp (-((u : ℂ) * horizontalSlope X)) *
      Complex.exp (y * horizontalSlope X + τ * horizontalSlope X ^ 2)
    have hylow : -(4 * η) ≤ y := by linarith only [hy, hη]
    have hu : 2 * η ≤ u := by dsimp only [u, α]; linarith only [hc, hy, hη]
    have hN : 0 < ‖xiLine X u‖ := norm_pos_iff.mpr
      (xiLine_ne_zero_of_typical h hη (by linarith only [hη8]) hX hXt hu)
    have hP : 0 < P := mul_pos hN (Real.exp_pos _)
    have hmain : ‖Main‖ = P * Real.exp (-(τ * (Real.pi / 4) ^ 2)) :=
      norm_main_eq (t := τ) (X := X) (y := y) (xiLine X u)
    have hmainlow : 23 / 25 * P ≤ ‖Main‖ := by
      rw [hmain]
      nlinarith only [mul_le_mul_of_nonneg_left (gaussPhase_ge hτ8 hτ) hP.le]
    have hQ := norm_halfGauss_sub_main_le_of_typical h hη hη8 hT hX hXt hτ hτ8 hα3
      hc hc2 hylow hy2 hWX
    have hQlow := norm_sub_norm_le Main (halfGaussTransform τ (xiLine X) y)
    rw [norm_sub_rev] at hQlow
    have hOpp := norm_halfGauss_opposite_le_of_typical h hη hη8 hT hX hXt hτ hτ8 hα3
      hc hc2 hfar.le hy2 hWX
    have hE' := mul_le_mul_of_nonneg_left hE hP.le
    have hO' := mul_le_mul_of_nonneg_left hO hP.le
    nlinarith only [hmainlow, hQ, hQlow, hOpp, hE', hO', hP]

/-- The reflected decomposition excludes every nonreal zero in the critical strip. -/
theorem riemannHeat_ne_zero_of_typical_errors {η T t X τ y : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hT : 8 ≤ T) (hX : 200 ≤ X) (hXt : |X - t| ≤ η)
    (hτ : 0 < τ) (hτ8 : τ ≤ 1 / 8) (hα3 : 3 ≤ (horizontalSlope X).re)
    (hc : 16 * η ≤ 2 * τ * (horizontalSlope X).re)
    (hc2 : 2 * τ * (horizontalSlope X).re ≤ 2) (hy : y ≠ 0) (hy2 : |y| ≤ 1 / 2)
    (hWX : 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2)
    (hE : typicalHalfGaussError η T τ (horizontalSlope X).re ≤ 1 / 5)
    (hS : typicalHalfGaussSlopeError η T τ (horizontalSlope X).re < 18 / 25 * (horizontalSlope X).re)
    (hO : typicalHalfGaussOppositeError η T τ (horizontalSlope X).re ≤ 1 / 2) :
    riemannHeat τ ((X : ℂ) + I * y) ≠ 0 := by
  rw [riemannHeat_eq_halfGaussAverage hτ X y]
  apply add_conj_ne_zero_of_norm_ne
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · have hn := norm_halfGauss_opposite_lt_of_typical_errors h hη hη8 hT hX hXt hτ hτ8 hα3
      hc hc2 (y := -y) (by linarith only [hneg]) (by linarith only [(abs_le.mp hy2).1]) hWX hE hS hO
    rw [neg_neg] at hn
    exact ne_of_gt hn
  · exact ne_of_lt (norm_halfGauss_opposite_lt_of_typical_errors h hη hη8 hT hX hXt hτ hτ8 hα3
      hc hc2 hpos (abs_le.mp hy2).2 hWX hE hS hO)

#print axioms riemannHeat_ne_zero_of_typical_errors

end

end GaloisForLFunctions.ZeroConfigurationGeometry

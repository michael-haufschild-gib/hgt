import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheHalfGaussAtTheCriticalScale
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TypicalZetaLogDerivative
import GaloisForLFunctions.RHTower.ZetaTypicalScaleBounds

/-!
# The central inequality at the critical scale

The crystal forms at the scale of the zeros, on almost all heights. There is an absolute `c > 0` such that for every `δ > 0` there is `κ` with: for all large `T`, outside a set of `X ∈ [T, 2T]` of measure at most `δT`,

`(x′ − x)² ≥ c min(t, 1/log²(2 + |x|))`

for all real zeros `x < x′` of `H_t` with `|x − X| ≤ κ/(2 log T)` and `7κ/log T ≤ t log(x/2π) ≤ 1/8` (`exists_central_inequality_at_critical_scale`). In terms of `τ = t log²X` the range is `τ ≳ κ`: the crystal is reached at a bounded normalized time on a set of density arbitrarily close to one, and the window contains `≍ κ` zeros. The time `τ ≍ 1` is the scale of the local statistics, so the range cannot be improved beyond a constant by an estimate of this kind.

**Inputs.** Two typical properties at the critical scale `R ≍ κ/log T`, both from Selberg's zero-density and mean-value method: zeros of depth `a ≥ R₀` keep at distance `> 5a` from `X` outside measure `≪ T/κ` (`exists_volume_zetaZeroShadowScaled_le`), and `|ζ′/ζ| ≤ B` on the box at scale `R` outside measure `≪ T(1/(BR)² + …)` (`exists_volume_not_zetaLogDerivScaleData_le_uniform_level`). With `q = κ^{1/4}` and dyadic scales `R_j = 3κ 2^j/log T`, the choice `B_j R_j = q (5/4)^j` makes the exceptional measures summable, while `B_j² τ ≪ 1/q²` for `τ ≍ R_j/log T`.

**Mechanism.** No size bound for `ζ` enters: the source is controlled through the Poisson sum (`TheSlopeOfXiIsAPoissonSum`) and the half-Gauss transform through its slope on one window (`TheHalfGaussAtTheCriticalScale`), and the two quadratures space the zeros (`gap_ge_of_quadrature_data`).
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## The slope from scale data -/

/-- Scale data bound the slope of `ξ` on the box. -/
theorem norm_logDeriv_xi_sub_le_of_data {X R B Y r : ℝ} (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (hdata : ZetaLogDerivScaleData X R B) (hY : |Y - X| ≤ 6 * R) (hY200 : 200 ≤ Y) (hr1 : 3 * R / 4 ≤ r)
    (hr2 : r ≤ 6 * R) :
    riemannZeta (linePt Y r) ≠ 0 ∧ ‖logDeriv xi (linePt Y r) - horizontalSlope Y‖ ≤ B + 1 := by
  have hr0 : 0 < r := by linarith only [hR, hr1]
  have hre := linePt_re Y r
  have him := linePt_im Y r
  have hζ : riemannZeta (linePt Y r) ≠ 0 := by
    intro h0
    have h1 := hdata.zeroFree _ h0 (by rw [hre]; linarith only [hR, hr1])
    rw [hre, him] at h1
    linarith only [h1, hY, hR, hr0]
  refine ⟨hζ, ?_⟩
  have him0 : (linePt Y r).im ≠ 0 := by
    rw [him]
    linarith only [hY200]
  have hne1 : linePt Y r ≠ 1 := fun he => him0 (by rw [he]; simp)
  have he : logDeriv xi (linePt Y r) = logDeriv archG (linePt Y r) + logDeriv riemannZeta (linePt Y r) := by
    rw [logDeriv_xi_fourFactor_offReal him0 hζ, logDeriv_archG (by rw [hre]; linarith only [hr0]) hne1]
  have harch := norm_logDeriv_archG_sub_horizontalSlope_le_one (σ := r + 1 / 2) (X := Y)
    (by linarith only [hr0]) (by linarith only [hr2, hR16, hY200]) hY200
  have hz := hdata.logDeriv _ (by rw [hre]; linarith only [hr1]) (by rw [hre]; linarith only [hr2])
    (by rw [him]; exact hY)
  rw [he, add_sub_right_comm]
  refine (norm_add_le _ _).trans ?_
  have harch' : ‖logDeriv archG (linePt Y r) - horizontalSlope Y‖ ≤ 1 := by
    simpa [linePt] using harch
  linarith only [harch', hz]

/-- The slope error of the source on the box. -/
theorem norm_xiLineDeriv_sub_le_of_data {X R B Y r : ℝ} (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (hdata : ZetaLogDerivScaleData X R B) (hY : |Y - X| ≤ 6 * R) (hY200 : 200 ≤ Y) (hr1 : 3 * R / 4 ≤ r)
    (hr2 : r ≤ 6 * R) :
    ‖xiLineDeriv Y r - horizontalSlope Y * xiLine Y r‖ ≤ (B + 1) * ‖xiLine Y r‖ := by
  obtain ⟨hζ, hd⟩ := norm_logDeriv_xi_sub_le_of_data hR hR16 hdata hY hY200 hr1 hr2
  have hr0 : 0 < r := by linarith only [hR, hr1]
  have hre := linePt_re Y r
  have him := linePt_im Y r
  have hne1 : linePt Y r ≠ 1 := fun he => by
    rw [he] at him
    simp at him
    linarith only [him, hY200]
  have hne : xiLine Y r ≠ 0 := by
    rw [xiLine_eq]
    intro h0
    exact hζ ((xi_eq_zero_iff (by rw [hre]; linarith only [hr0]) hne1).mp h0)
  have he : xiLineDeriv Y r = logDeriv xi (linePt Y r) * xiLine Y r := by
    have h' := hne
    rw [xiLine_eq] at h' ⊢
    rw [logDeriv_apply, div_mul_cancel₀ _ h']
    unfold xiLineDeriv
    rw [xiLine_point]
  rw [he, ← sub_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right hd (norm_nonneg _)

/-! ## The transform at a height -/

/-- The half-Gauss estimates from the two typical properties. -/
theorem source_estimates {X R₀ R B τ Y v u : ℝ} (hR₀ : 0 < R₀) (hR16 : R ≤ 1 / 16) (hR₀R : 3 * R₀ ≤ R)
    (hK : ZeroKeeping X R₀) (hdata : ZetaLogDerivScaleData X R B) (hY : |Y - X| < R₀) (hY200 : 200 ≤ Y)
    (hτ : 0 < τ) (hβ1 : 1 ≤ (horizontalSlope Y).re) (hrel : v + 2 * τ * (horizontalSlope Y).re = u)
    (hu1 : 9 * R / 4 ≤ u) (hu2 : 24 * R / 5 ≤ 24 * R / 5) (hu3 : u ≤ 24 * R / 5) (hv : 100 * |v| ≤ u)
    (hB0 : 0 < B + 1) (hB : 100 * (B + 1) ≤ (horizontalSlope Y).re) (hΛ : 400 ≤ u * (horizontalSlope Y).re) :
    ‖halfGaussTransform τ (xiLine Y) v -
        xiLine Y u * Complex.exp (-(u * horizontalSlope Y)) *
          Complex.exp (v * horizontalSlope Y + τ * horizontalSlope Y ^ 2)‖ ≤
      (‖xiLine Y u‖ * Real.exp (-(τ * (horizontalSlope Y).re ^ 2))) *
        (gaussianSaddleModelError (B + 1) τ + 8 * Real.exp (-(u * (horizontalSlope Y).re / 40))) ∧
    ‖(∫ w in Ioi (0 : ℝ), (((w - v) / (2 * τ) * gaussDensity τ (w - v) : ℝ) : ℂ) * xiLine Y w) -
        horizontalSlope Y * halfGaussTransform τ (xiLine Y) v‖ ≤
      (‖xiLine Y u‖ * Real.exp (-(τ * (horizontalSlope Y).re ^ 2))) *
        ((B + 1) * (1 + gaussianSaddleModelError (B + 1) τ) +
          60 * (horizontalSlope Y).re * Real.exp (-(u * (horizontalSlope Y).re / 40))) := by
  have hR : 0 < R := by linarith only [hR₀, hR₀R]
  have hu : 0 < u := by linarith only [hR, hu1]
  have hY6 : |Y - X| ≤ 6 * R := by linarith only [hY, hR₀R, hR₀]
  have hbox (w : ℝ) (hw : w ∈ Icc (u / 3) (5 * u / 4)) : 3 * R / 4 ≤ w ∧ w ≤ 6 * R :=
    ⟨by linarith only [hw.1, hu1], by linarith only [hw.2, hu3]⟩
  have h2R₀ : 2 * R₀ ≤ u / 3 := by linarith only [hu1, hR₀R, hR₀]
  have hub : 2 * R₀ ≤ 5 * u / 4 := by linarith only [h2R₀, hu]
  refine halfGauss_estimates_of_source hτ hβ1 hu hrel hv hB0 hB hΛ ?_ ?_ ?_
  · intro w hw
    exact norm_xiLineDeriv_sub_le_of_data hR hR16 hdata hY6 hY200 (hbox w hw).1 (hbox w hw).2
  · intro w hw
    exact norm_xiLine_le_of_keeping hR₀ hK hY hw.1 hw.2 h2R₀
  · intro w hw
    refine norm_xiLine_le_growth hR₀ (hK.keepsAway hY.le) hub hw ?_
    obtain ⟨-, hd⟩ := norm_logDeriv_xi_sub_le_of_data hR hR16 hdata hY6 hY200
      (hbox _ ⟨by linarith only [hu], le_rfl⟩).1 (hbox _ ⟨by linarith only [hu], le_rfl⟩).2
    have h1 := Complex.re_le_norm (logDeriv xi (linePt Y (5 * u / 4)) - horizontalSlope Y)
    rw [Complex.sub_re] at h1
    linarith only [h1, hd]

/-! ## The gap -/

/-- **The gap from the two typical properties.** -/
theorem gap_ge_of_critical_data {X R₀ R B τ x x' : ℝ} (hR₀ : 0 < R₀) (hR16 : R ≤ 1 / 16) (hR₀R : 3 * R₀ ≤ R)
    (hK : ZeroKeeping X R₀) (hdata : ZetaLogDerivScaleData X R B) (hB0 : 0 ≤ B) (hX : 1100 ≤ X)
    (hx : |x - X| ≤ R₀ / 2) (hα : 1000 ≤ (horizontalSlope x).re) (hτ : 0 < τ)
    (hu₁ : 23 * R / 10 ≤ 2 * τ * (horizontalSlope x).re) (hu₂ : 2 * τ * (horizontalSlope x).re ≤ 46 * R / 10)
    (hRα : 10 ^ 6 ≤ R * (horizontalSlope x).re) (hR₀α : 8 ≤ R₀ * (horizontalSlope x).re)
    (hB : 400 * (B + 1) ≤ (horizontalSlope x).re - 1) (hq : (B + 1) * Real.sqrt τ ≤ 1 / 200)
    (hxx' : x < x') (hx0 : riemannHeat τ (x : ℂ) = 0) (hx'0 : riemannHeat τ (x' : ℂ) = 0) :
    1 / (20 * Real.exp 7) / (horizontalSlope x).re ≤ x' - x := by
  have hR : 0 < R := by linarith only [hR₀, hR₀R]
  have hR₀16 : R₀ ≤ 1 / 48 := by linarith only [hR₀R, hR16]
  have hB1 : 0 < B + 1 := by linarith only [hB0]
  have hx1 := abs_le.mp hx
  have hx1001 : 1001 ≤ x := by linarith only [hX, hx1.1, hR₀16]
  have hxpos : 0 < x := by linarith only [hx1001]
  set α := (horizontalSlope x).re with hαdef
  have hα0 : 0 < α := by linarith only [hα]
  have h1α : 1 / α ≤ 1 / 1000 := one_div_le_one_div_of_le (by norm_num) hα
  -- the model error
  have hmodel : gaussianSaddleModelError (B + 1) τ ≤ 1 / 10 := by
    have h1 := gaussianSaddleModelError_le_of_sqrt_le hτ hB1.le hq
    refine h1.trans ?_
    have h2 : Real.exp ((1 + 1 / 200 : ℝ) ^ 2) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    have h3 : Real.exp 2 ≤ 9 := by
      have h4 : Real.exp 2 = Real.exp 1 ^ 2 := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [h4]
      have h5 := Real.exp_one_lt_d9
      have h6 : Real.exp 1 ^ 2 ≤ 3 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith only [h5]) 2
      linarith only [h6]
    have h7 := h2.trans h3
    nlinarith only [h7]
  have hmodel0 := gaussianSaddleModelError_nonneg (t := τ) hB1.le
  -- the facts at each nearby height
  have hpt (ξ : ℝ) (hξ : |ξ - x| ≤ 2 * (1 / α)) :
      |ξ - X| < R₀ ∧ 1000 ≤ ξ ∧ α - 1 ≤ (horizontalSlope ξ).re ∧ (horizontalSlope ξ).re ≤ α + 1 := by
    have h1 := abs_le.mp hξ
    have h2 : 2 * (1 / α) ≤ R₀ / 4 := by
      have h3 : 8 * (1 / α) ≤ R₀ := by
        rw [mul_one_div, div_le_iff₀ hα0]
        exact hR₀α
      linarith only [h3]
    have hξX : |ξ - X| < R₀ := by
      rw [abs_lt]
      constructor <;> linarith only [h1.1, h1.2, hx1.1, hx1.2, h2, hR₀]
    have hξlo : 1000 ≤ ξ := by linarith only [hx1001, h1.1, h1α]
    have hξpos : 0 < ξ := by linarith only [hξlo]
    have h3 := abs_horizontalSlope_re_sub_le hxpos hξpos
    have h4 : |ξ - x| / min x ξ ≤ 1 := by
      rw [div_le_one (lt_min hxpos hξpos)]
      refine le_min ?_ ?_
      · linarith only [hξ, h1α, hx1001]
      · linarith only [hξ, h1α, hξlo]
    have hs := abs_le.mp (h3.trans h4)
    exact ⟨hξX, hξlo, by linarith only [hs.1], by linarith only [hs.2]⟩
  -- the position of the saddle
  have h2τ : 2 * τ ≤ 46 * R / 10 / α := by
    rw [le_div_iff₀ hα0]
    exact hu₂
  have hR1000 : 2 * (1 / α) ≤ R / 100 := by
    have h3 : 200 * (1 / α) ≤ R := by
      rw [mul_one_div, div_le_iff₀ hα0]
      nlinarith only [hRα, hα0]
    linarith only [h3]
  have hsad (ξ : ℝ) (hξ : |ξ - x| ≤ 2 * (1 / α)) (v : ℝ) (hv : |v| ≤ 2 * (1 / α)) :
      9 * R / 4 ≤ v + 2 * τ * (horizontalSlope ξ).re ∧ v + 2 * τ * (horizontalSlope ξ).re ≤ 24 * R / 5 := by
    obtain ⟨-, -, h7, h8⟩ := hpt ξ hξ
    have hv' := abs_le.mp hv
    have h2τ' : 2 * τ ≤ R / 100 := by
      refine h2τ.trans ?_
      rw [div_le_div_iff₀ hα0 (by norm_num)]
      nlinarith only [hα, hR]
    have h9 : 2 * τ * ((horizontalSlope ξ).re - α) ≤ 2 * τ * 1 :=
      mul_le_mul_of_nonneg_left (by linarith only [h8]) (by positivity)
    have h10 : 2 * τ * (-1) ≤ 2 * τ * ((horizontalSlope ξ).re - α) :=
      mul_le_mul_of_nonneg_left (by linarith only [h7]) (by positivity)
    constructor <;> nlinarith only [h9, h10, hu₁, hu₂, hv'.1, hv'.2, hR1000, h2τ', hR]
  refine gap_ge_of_quadrature_data (B := B + 1) (w₁ := 3 * R / 4) (w₂ := 6 * R) (by linarith only [hx1001])
    (by linarith only [hα]) hτ (by linarith only [hu₂, hR16]) hB1 ?_ ?_ ?_ ?_ ?_ ?_ hxx' hx0 hx'0
  · intro ξ hξ
    obtain ⟨-, -, h7, -⟩ := hpt ξ hξ
    linarith only [hB, h7, hα, hB1]
  · intro ξ hξ v hv
    obtain ⟨h1, h2⟩ := hsad ξ hξ v hv
    exact ⟨by linarith only [h1, hR], by linarith only [h2, hR]⟩
  · intro ξ hξ w hw
    obtain ⟨h1, h2, -, -⟩ := hpt ξ hξ
    exact norm_xiLineDeriv_sub_le_of_data hR hR16 hdata (by linarith only [abs_nonneg (ξ - X), h1, hR₀R, hR₀])
      (by linarith only [h2]) hw.1 hw.2
  · sorry
  · sorry
  · exact xiLine_ne_zero_of_keepsAway hR₀ (hK.keepsAway (by linarith only [hx, hR₀, abs_nonneg (x - X)]))
      (by linarith only [hu₁, hR₀R, hR₀])

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

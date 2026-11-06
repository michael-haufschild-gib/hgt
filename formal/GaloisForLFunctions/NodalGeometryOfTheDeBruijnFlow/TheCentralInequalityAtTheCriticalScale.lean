import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheHalfGaussAtTheCriticalScale
import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheCentralInequalityAtAPowerOfTheLogarithm
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
    (hu1 : 9 * R / 4 ≤ u) (hu3 : u ≤ 24 * R / 5) (hv : 100 * |v| ≤ u)
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
  · intro ξ hξ v hv
    obtain ⟨h1, h2, h7, -⟩ := hpt ξ hξ
    obtain ⟨hs1, hs2⟩ := hsad ξ hξ v hv
    have hβ1 : 1 ≤ (horizontalSlope ξ).re := by linarith only [h7, hα]
    have hv100 : 100 * |v| ≤ v + 2 * τ * (horizontalSlope ξ).re := by linarith only [hv, hR1000, hs1, hR]
    have hβα : α / 2 ≤ (horizontalSlope ξ).re := by linarith only [h7, hα]
    have huβ : 9 * R / 4 * (α / 2) ≤ (v + 2 * τ * (horizontalSlope ξ).re) * (horizontalSlope ξ).re :=
      mul_le_mul hs1 hβα (by positivity) (by linarith only [hs1, hR])
    have hRα' : 9 * R / 4 * (α / 2) = 9 / 8 * (R * α) := by ring
    have hest := source_estimates hR₀ hR16 hR₀R hK hdata h1 (by linarith only [h2]) hτ hβ1 rfl hs1 hs2 hv100 hB1
      (by linarith only [hB, h7, hB1]) (by linarith only [huβ, hRα', hRα])
    refine hest.1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hδ : Real.exp (-((v + 2 * τ * (horizontalSlope ξ).re) * (horizontalSlope ξ).re / 40)) ≤ 1 / 12000 :=
      exp_neg_le_of_le (by norm_num) (by linarith only [huβ, hRα', hRα])
    linarith only [hmodel, hδ]
  · obtain ⟨h1, h2, h7, -⟩ := hpt x (by rw [sub_self, abs_zero]; positivity)
    have hzero : |(0 : ℝ)| ≤ 2 * (1 / α) := by
      rw [abs_zero]
      positivity
    obtain ⟨hs1, hs2⟩ := hsad x (by rw [sub_self, abs_zero]; positivity) 0 hzero
    rw [zero_add] at hs1 hs2
    rw [← hαdef] at hs1 hs2 h7
    have huβ : 9 * R / 4 * (α / 2) ≤ 2 * τ * α * α :=
      mul_le_mul hs1 (by linarith only [hα]) (by positivity) (by linarith only [hs1, hR])
    have hRα' : 9 * R / 4 * (α / 2) = 9 / 8 * (R * α) := by ring
    have hest := source_estimates (Y := x) (v := 0) (u := 2 * τ * α) hR₀ hR16 hR₀R hK hdata h1
      (by linarith only [h2]) hτ (by linarith only [hα]) (by rw [zero_add]) hs1 hs2
      (by rw [abs_zero, mul_zero]; linarith only [hs1, hR]) hB1 (by linarith only [hB, hB1, hα])
      (by linarith only [huβ, hRα', hRα])
    refine hest.2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hδ : Real.exp (-(2 * τ * α * α / 40)) ≤ 1 / 12000 :=
      exp_neg_le_of_le (by norm_num) (by linarith only [huβ, hRα', hRα])
    rw [← hαdef]
    have h3 : (B + 1) * (1 + gaussianSaddleModelError (B + 1) τ) ≤ (α / 400) * (11 / 10) :=
      mul_le_mul (by linarith only [hB]) (by linarith only [hmodel]) (by linarith only [hmodel0]) (by positivity)
    have h4 : 60 * α * Real.exp (-(2 * τ * α * α / 40)) ≤ 60 * α * (1 / 12000) :=
      mul_le_mul_of_nonneg_left hδ (by positivity)
    linarith only [h3, h4, hα0]
  · exact xiLine_ne_zero_of_keepsAway hR₀ (hK.keepsAway (by linarith only [hx, hR₀, abs_nonneg (x - X)]))
      (by linarith only [hu₁, hR₀R, hR₀])

/-! ## The scales and the exceptional set -/

/-- The dyadic scales `R_j = 3 q⁴ 2^j/L`. -/
def critR (q L : ℝ) (j : ℕ) : ℝ := 3 * q ^ 4 * 2 ^ j / L

/-- The levels `B_j = L (5/8)^j/(3q³)`, so that `B_j R_j = q (5/4)^j`. -/
def critB (q L : ℝ) (j : ℕ) : ℝ := L * (5 / 8) ^ j / (3 * q ^ 3)

/-- The two typical properties, at the level `R₀ = q⁴/log T` and at all scales. -/
def CriticalGood (q T X : ℝ) : Prop :=
  ZeroKeeping X (q ^ 4 / Real.log T) ∧
    ∀ j : ℕ, critR q (Real.log T) j ≤ 1 / 16 →
      ZetaLogDerivScaleData X (critR q (Real.log T) j) (critB q (Real.log T) j)

/-- Outside the scaled shadow, all zeros of depth above `R₀` keep at distance more than five depths. -/
theorem zeroKeeping_of_not_mem_shadow {X R₀ : ℝ} (hR₀ : 0 < R₀) (h : X ∉ zetaZeroShadowScaled R₀ 5) :
    ZeroKeeping X R₀ := by
  have hpos (p : XiZeroCopy) (hp : R₀ < zeroDepth p) : 5 * zeroDepth p < |zeroOrdGap X p| := by
    by_contra hcon
    refine h ⟨(p.1 : ℂ), riemannZeta_xiZeroCopy_eq_zero p, ?_, ?_⟩
    · unfold zeroDepth at hp
      linarith only [hp]
    · have h2 := not_lt.mp hcon
      unfold zeroOrdGap at h2
      unfold zeroDepth at h2
      rwa [abs_sub_comm] at h2
  intro q hq
  rcases lt_abs.mp hq with h1 | h1
  · have h2 := hpos q h1
    rwa [abs_of_pos (by linarith only [h1, hR₀])]
  · have h2 := hpos (xiZeroCopyLineConjEquiv q) (by rw [zeroDepth_lineConj]; exact h1)
    rw [zeroDepth_lineConj, zeroOrdGap_lineConj] at h2
    rwa [abs_of_neg (by linarith only [h1, hR₀])]

theorem sum_range_geom_le (n : ℕ) : ∑ j ∈ Finset.range n, (16 / 25 : ℝ) ^ j ≤ 25 / 9 := by
  have h : ∑ j ∈ Finset.range n, (16 / 25 : ℝ) ^ j = 25 / 9 * (1 - (16 / 25) ^ n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring
  rw [h]
  have h2 : (0 : ℝ) ≤ (16 / 25) ^ n := by positivity
  linarith only [h2]

/-- The exceptional density at one scale. -/
theorem scale_term_le {q L : ℝ} {j : ℕ} (hq : (10 : ℝ) ^ 4 ≤ q) (hL : 0 < L) :
    L / critB q L j * Real.exp (-(critR q L j * L / 120000)) + 1 / (critB q L j ^ 2 * critR q L j ^ 2) ≤
      2 * ((16 / 25) ^ j / q ^ 2) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  set a : ℝ := (8 / 5) ^ j with ha
  have ha0 : 0 < a := by positivity
  have h58 : (5 / 8 : ℝ) ^ j = 1 / a := by
    rw [eq_div_iff ha0.ne', ha, ← mul_pow]
    norm_num
  have hLB : L / critB q L j = 3 * q ^ 3 * a := by
    unfold critB
    rw [h58]
    field_simp
  have hRL : critR q L j * L = 3 * q ^ 4 * 2 ^ j := by
    unfold critR
    field_simp
  have hBR : critB q L j * critR q L j = q * (5 / 4) ^ j := by
    have h1 : (5 / 8 : ℝ) ^ j * 2 ^ j = (5 / 4) ^ j := by
      rw [← mul_pow]
      norm_num
    unfold critB critR
    rw [← h1]
    field_simp
  have hinv : 1 / (critB q L j ^ 2 * critR q L j ^ 2) = (16 / 25) ^ j / q ^ 2 := by
    rw [← mul_pow, hBR, mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
    have h1 : ((5 / 4 : ℝ) ^ 2) ^ j * (16 / 25) ^ j = 1 := by
      rw [← mul_pow]
      norm_num
    field_simp
    linarith only [h1]
  rw [hLB, hRL, hinv]
  set x : ℝ := 3 * q ^ 4 * 2 ^ j / 120000 with hx
  have hx0 : 0 < x := by positivity
  have hexp : Real.exp (-x) ≤ 2 / x ^ 2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    have h1 := Real.quadratic_le_exp_of_nonneg hx0.le
    nlinarith only [h1, hx0, sq_nonneg x]
  have hpow : (2 / 5 : ℝ) ^ j ≤ (16 / 25) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have hmain : 3 * q ^ 3 * a * (2 / x ^ 2) ≤ (16 / 25) ^ j / q ^ 2 := by
    have h1 : 3 * q ^ 3 * a * (2 / x ^ 2) = 9600000000 * (2 / 5) ^ j / q ^ 5 := by
      have h2 : a = (2 / 5) ^ j * (2 : ℝ) ^ j * 2 ^ j := by
        rw [ha, ← mul_pow, ← mul_pow]
        norm_num
      rw [h2, hx]
      field_simp
      norm_num
    rw [h1, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (10 : ℝ) ^ 10 ≤ q ^ 3 := by
      have h4 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 10 ^ 4) hq 3
      refine le_trans ?_ h4
      norm_num
    have h5 : 9600000000 * (2 / 5 : ℝ) ^ j ≤ q ^ 3 * (16 / 25) ^ j :=
      mul_le_mul (by linarith only [h3]) hpow (by positivity) (by positivity)
    have h6 := mul_le_mul_of_nonneg_right h5 (by positivity : 0 ≤ q ^ 2)
    calc 9600000000 * (2 / 5 : ℝ) ^ j * q ^ 2 ≤ q ^ 3 * (16 / 25) ^ j * q ^ 2 := h6
      _ = _ := by ring
  have h7 := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 3 * q ^ 3 * a)
  linarith only [h7, hmain]

/-- The power of the logarithm and the square root are below any multiple of `T`. -/
theorem eventually_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, Real.log (5 * T) ^ 2 ≤ ε * T ∧ (Real.log T + 2) * T ^ ((1 : ℝ) / 2) ≤ ε * T := by
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h5 : Tendsto (fun T : ℝ => 5 * T) atTop atTop := tendsto_id.const_mul_atTop (by norm_num)
  have h2 := (h1.comp h5).eventually (ge_mem_nhds (show (0 : ℝ) < ε / 5 by positivity))
  have h3 := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).bound (show 0 < ε / 2 by positivity)
  have h4 := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_ge_atTop (4 / ε)
  filter_upwards [h2, h3, h4, eventually_gt_atTop (1 : ℝ)] with T hT2 hT3 hT4 hT1
  have hT0 : 0 < T := by linarith only [hT1]
  have hrpos : 0 < T ^ ((1 : ℝ) / 2) := by positivity
  constructor
  · simp only [Function.comp, one_mul, add_zero] at hT2
    rw [div_le_iff₀ (by positivity)] at hT2
    nlinarith only [hT2]
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hrpos, abs_of_pos (Real.log_pos hT1)] at hT3
    have h6 : 2 ≤ ε / 2 * T ^ ((1 : ℝ) / 2) := by
      rw [div_le_iff₀ hε] at hT4
      linarith only [hT4]
    have h7 : T ^ ((1 : ℝ) / 2) * T ^ ((1 : ℝ) / 2) = T := by
      rw [← Real.rpow_add hT0]
      norm_num
    have h8 : Real.log T + 2 ≤ ε * T ^ ((1 : ℝ) / 2) := by linarith only [hT3, h6]
    have h9 := mul_le_mul_of_nonneg_right h8 hrpos.le
    rw [mul_assoc, h7] at h9
    exact h9

/-- **The exceptional set.** The heights without the two typical properties have measure `≪ T/q²`, uniformly in `q`. -/
theorem exists_volume_not_criticalGood_le :
    ∃ A : ℝ, 0 < A ∧ ∀ q : ℝ, (10 : ℝ) ^ 4 ≤ q → ∀ᶠ T : ℝ in atTop,
      volume {X | X ∈ Icc T (2 * T) ∧ ¬ CriticalGood q T X} ≤ ENNReal.ofReal (A * T / q ^ 2) := by
  classical
  obtain ⟨C₁, hC₁, h₁⟩ := exists_volume_not_zetaLogDerivScaleData_le_uniform_level
  obtain ⟨D, K, hD, hK, h₂⟩ := exists_volume_zetaZeroShadowScaled_le
  refine ⟨40 * D + 6 * C₁ + 1, by positivity, ?_⟩
  intro q hq
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hq1 : 1 ≤ q := le_trans (by norm_num) hq
  have ht1 : Tendsto (fun T : ℝ => 4 * T - 24) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (by norm_num))
  have ht2 : Tendsto (fun T : ℝ => 4 * T + 12) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (by norm_num))
  have hε : 0 < 1 / (2 * q ^ 2 * (20 * K + C₁ + 1)) := by positivity
  filter_upwards [h₁, ht1.eventually h₂, ht2.eventually h₂, eventually_small hε, eventually_ge_atTop (1000 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with T h1 h21 h22 hsmall hT hlog
  have hT0 : 0 < T := by linarith only [hT]
  set L := Real.log T with hL
  have hL0 : 0 < L := by linarith only [hlog]
  set R₀ := q ^ 4 / L with hR₀
  have hR₀pos : 0 < R₀ := by positivity
  -- the shadow
  have hblock (U : ℝ) (hU1 : T ≤ U) (hU2 : U ≤ 5 * T)
      (h : ∀ a κ : ℝ, 2 / Real.log U ≤ a → 0 < κ →
        volume (zetaZeroShadowScaled a κ ∩ Icc (U / 4 + κ + 1) (U / 2 - κ - 1)) ≤
          ENNReal.ofReal (2 * κ * (D / (a * Real.log U) * (U / 4) + K * Real.log U ^ 2))) :
      volume (zetaZeroShadowScaled R₀ 5 ∩ Icc (U / 4 + 5 + 1) (U / 2 - 5 - 1)) ≤
        ENNReal.ofReal (10 * (2 * D * T / q ^ 4 + K * Real.log (5 * T) ^ 2)) := by
    have hlogU : L ≤ Real.log U := Real.log_le_log hT0 hU1
    have hlogU0 : 0 < Real.log U := by linarith only [hlogU, hL0]
    have hRU : q ^ 4 ≤ R₀ * Real.log U := by
      rw [hR₀, div_mul_eq_mul_div, le_div_iff₀ hL0]
      exact mul_le_mul_of_nonneg_left hlogU (by positivity)
    have h2R : 2 / Real.log U ≤ R₀ := by
      rw [div_le_iff₀ hlogU0]
      have : (2 : ℝ) ≤ q ^ 4 := by
        have h3 : (1 : ℝ) ≤ q ^ 4 - 1 + 0 + 0 := by
          have h4 : (10 : ℝ) ^ 4 ≤ q ^ 4 := (le_self_pow₀ hq1 (by norm_num)).trans' hq
          linarith only [h4]
        linarith only [h3]
      linarith only [this, hRU]
    refine (h R₀ 5 h2R (by norm_num)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h3 : D / (R₀ * Real.log U) ≤ D / q ^ 4 :=
      div_le_div_of_nonneg_left hD (by positivity) hRU
    have h4 : D / (R₀ * Real.log U) * (U / 4) ≤ D / q ^ 4 * (2 * T) :=
      mul_le_mul h3 (by linarith only [hU2, hT0]) (by linarith only [hU1, hT0]) (by positivity)
    have h5 : Real.log U ^ 2 ≤ Real.log (5 * T) ^ 2 :=
      pow_le_pow_left₀ hlogU0.le (Real.log_le_log (by linarith only [hU1, hT0]) hU2) 2
    have h6 := mul_le_mul_of_nonneg_left h5 hK
    have h7 : D / q ^ 4 * (2 * T) = 2 * D * T / q ^ 4 := by ring
    nlinarith only [h4, h6, h7]
  have hb1 := hblock (4 * T - 12 - 12) (by linarith only [hT]) (by linarith only [hT]) (by
    intro a κ ha hκ
    have := h21 a κ
    rw [show 4 * T - 24 = 4 * T - 12 - 12 by ring] at this
    exact this ha hκ)
  have hb2 := hblock (4 * T + 12) (by linarith only [hT]) (by linarith only [hT]) h22
  -- the scales
  set J : Finset ℕ := (Finset.range ⌈L⌉₊).filter (fun j => critR q L j ≤ 1 / 16) with hJ
  have hterm (j : ℕ) (hj : j ∈ J) :
      volume {X | X ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData X (critR q L j) (critB q L j)} ≤
        ENNReal.ofReal (C₁ * T * (2 * ((16 / 25) ^ j / q ^ 2)) + C₁ * T ^ ((1 : ℝ) / 2)) := by
    have hR16 := (Finset.mem_filter.mp hj).2
    have hRpos : 0 < critR q L j := by
      unfold critR
      positivity
    have hBR : critR q L j * L = 3 * q ^ 4 * 2 ^ j := by
      unfold critR
      field_simp
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hq4 : (10 : ℝ) ^ 4 ≤ q ^ 4 := (le_self_pow₀ hq1 (by norm_num)).trans' hq
    have hκ : 30000 ≤ critR q L j * L := by
      rw [hBR]
      nlinarith only [hq4, h2j]
    have hB4 : 4 ≤ critB q L j := by
      have h3 : critB q L j * critR q L j = q * (5 / 4) ^ j := by
        have h1 : (5 / 8 : ℝ) ^ j * 2 ^ j = (5 / 4) ^ j := by
          rw [← mul_pow]
          norm_num
        unfold critB critR
        rw [← h1]
        field_simp
      have h4 : (1 : ℝ) ≤ (5 / 4) ^ j := one_le_pow₀ (by norm_num)
      have h5 : q ≤ q * (5 / 4) ^ j := by nlinarith only [h4, hq0]
      have hBpos : 0 < critB q L j := by
        unfold critB
        positivity
      have h6 : critB q L j * critR q L j ≤ critB q L j * (1 / 16) := mul_le_mul_of_nonneg_left hR16 hBpos.le
      have h7 : (10 : ℝ) ^ 4 ≤ critB q L j * (1 / 16) := by linarith only [h3, h5, h6, hq]
      norm_num at h7
      linarith only [h7]
    have hBL : critB q L j ≤ L := by
      unfold critB
      rw [div_le_iff₀ (by positivity)]
      have h3 : (5 / 8 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h4 : (1 : ℝ) ≤ 3 * q ^ 3 := by
        have : (1 : ℝ) ≤ q ^ 3 := one_le_pow₀ hq1
        linarith only [this]
      nlinarith only [mul_le_mul h3 h4 (by norm_num) (by positivity), hL0]
    refine (h1 _ hB4 hBL _ hRpos hR16 hκ).trans (ENNReal.ofReal_le_ofReal ?_)
    have h3 := scale_term_le (j := j) hq hL0
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ C₁ * T)
    linarith only [h4]
  -- the cover
  have hcover : {X | X ∈ Icc T (2 * T) ∧ ¬ CriticalGood q T X} ⊆
      ((zetaZeroShadowScaled R₀ 5 ∩ Icc ((4 * T - 12 - 12) / 4 + 5 + 1) ((4 * T - 12 - 12) / 2 - 5 - 1)) ∪
        (zetaZeroShadowScaled R₀ 5 ∩ Icc ((4 * T + 12) / 4 + 5 + 1) ((4 * T + 12) / 2 - 5 - 1))) ∪
      ⋃ j ∈ J, {X | X ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData X (critR q L j) (critB q L j)} := by
    rintro X ⟨hX, hnot⟩
    by_cases hshadow : X ∈ zetaZeroShadowScaled R₀ 5
    · left
      rcases le_total X (2 * T - 18) with h3 | h3
      · exact Or.inl ⟨hshadow, by linarith only [hX.1], by linarith only [h3]⟩
      · exact Or.inr ⟨hshadow, by linarith only [h3, hT], by linarith only [hX.2]⟩
    · right
      have hK' := zeroKeeping_of_not_mem_shadow hR₀pos hshadow
      have h3 : ¬ ∀ j : ℕ, critR q L j ≤ 1 / 16 → ZetaLogDerivScaleData X (critR q L j) (critB q L j) :=
        fun h4 => hnot ⟨hK', h4⟩
      push Not at h3
      obtain ⟨j, hj1, hj2⟩ := h3
      refine mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hj1⟩, hX, hj2⟩
      -- `j < 2^j ≤ L`
      have h4 : 3 * q ^ 4 * 2 ^ j / L ≤ 1 / 16 := hj1
      rw [div_le_iff₀ hL0] at h4
      have hq4 : (1 : ℝ) ≤ q ^ 4 := one_le_pow₀ hq1
      have h2j : (0 : ℝ) < 2 ^ j := by positivity
      have h5 : (2 : ℝ) ^ j ≤ L := by nlinarith only [h4, hq4, h2j, hL0]
      have h6 : (j : ℝ) < 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self
      have h7 : (j : ℝ) < ⌈L⌉₊ := lt_of_lt_of_le (h6.trans_le h5) (Nat.le_ceil L)
      exact_mod_cast h7
  refine (measure_mono hcover).trans ((measure_union_le _ _).trans ?_)
  have hshadowv := (measure_union_le _ _).trans (add_le_add hb1 hb2)
  have hscalev : volume (⋃ j ∈ J, {X | X ∈ Icc T (2 * T) ∧
      ¬ ZetaLogDerivScaleData X (critR q L j) (critB q L j)}) ≤
      ∑ j ∈ J, ENNReal.ofReal (C₁ * T * (2 * ((16 / 25) ^ j / q ^ 2)) + C₁ * T ^ ((1 : ℝ) / 2)) :=
    (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hterm)
  have hsum0 (j : ℕ) : 0 ≤ C₁ * T * (2 * ((16 / 25 : ℝ) ^ j / q ^ 2)) + C₁ * T ^ ((1 : ℝ) / 2) := by positivity
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => hsum0 j] at hscalev
  have hs0 : 0 ≤ 2 * D * T / q ^ 4 + K * Real.log (5 * T) ^ 2 := by positivity
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hshadowv
  refine (add_le_add hshadowv hscalev).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun j _ => hsum0 j)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the sum over the scales
  have hJsum : ∑ j ∈ J, (C₁ * T * (2 * ((16 / 25 : ℝ) ^ j / q ^ 2)) + C₁ * T ^ ((1 : ℝ) / 2)) ≤
      C₁ * T * (2 * ((25 / 9) / q ^ 2)) + (L + 1) * (C₁ * T ^ ((1 : ℝ) / 2)) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div]
    have hJr : J ⊆ Finset.range ⌈L⌉₊ := Finset.filter_subset _ _
    have h3 : ∑ j ∈ J, (16 / 25 : ℝ) ^ j ≤ 25 / 9 :=
      (Finset.sum_le_sum_of_subset_of_nonneg hJr fun _ _ _ => by positivity).trans (sum_range_geom_le _)
    have h4 : (J.card : ℝ) ≤ L + 1 := by
      have h5 : J.card ≤ ⌈L⌉₊ := by
        simpa using Finset.card_le_card hJr
      have h6 : (J.card : ℝ) ≤ ⌈L⌉₊ := by exact_mod_cast h5
      have h7 := Nat.ceil_lt_add_one hL0.le
      linarith only [h6, h7]
    refine add_le_add ?_ (mul_le_mul_of_nonneg_right h4 (by positivity))
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num)) (by positivity)
    exact div_le_div_of_nonneg_right h3 (by positivity)
  obtain ⟨hs1, hs2⟩ := hsmall
  set ε := 1 / (2 * q ^ 2 * (20 * K + C₁ + 1)) with hεdef
  have hεK : (20 * K + C₁ + 1) * ε = 1 / (2 * q ^ 2) := by
    rw [hεdef]
    field_simp
  have hq24 : 1 / q ^ 4 ≤ 1 / q ^ 2 := one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ hq1 (by norm_num))
  have hT1 : 0 ≤ T := hT0.le
  have h3 : 10 * (K * Real.log (5 * T) ^ 2) ≤ 10 * K * (ε * T) := by
    have := mul_le_mul_of_nonneg_left hs1 hK
    linarith only [this]
  have h4 : (L + 1) * (C₁ * T ^ ((1 : ℝ) / 2)) ≤ C₁ * (ε * T) := by
    have h5 : (L + 1) * T ^ ((1 : ℝ) / 2) ≤ (L + 2) * T ^ ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right (by linarith only) (by positivity)
    have := mul_le_mul_of_nonneg_left (h5.trans hs2) hC₁.le
    linarith only [this]
  have h6 : (20 * K + C₁ + 1) * (ε * T) = T / (2 * q ^ 2) := by
    rw [← mul_assoc, hεK]
    ring
  have h7 : 2 * D * T / q ^ 4 ≤ 2 * D * T / q ^ 2 := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div (2 * D * T)]
    exact mul_le_mul_of_nonneg_left hq24 (by positivity)
  have hεT : 0 ≤ ε * T := by positivity
  have h8 : C₁ * T * (2 * ((25 / 9) / q ^ 2)) ≤ 6 * C₁ * T / q ^ 2 := by
    have h9 : C₁ * T * (2 * ((25 / 9) / q ^ 2)) = (50 / 9) * (C₁ * T) / q ^ 2 := by ring
    rw [h9]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    nlinarith only [mul_pos hC₁ hT0]
  have h10 : (40 * D + 6 * C₁ + 1) * T / q ^ 2 =
      40 * (D * T / q ^ 2) + 6 * C₁ * T / q ^ 2 + T / q ^ 2 := by ring
  have h11 : 2 * D * T / q ^ 2 = 2 * (D * T / q ^ 2) := by ring
  have h12 : T / q ^ 2 = 2 * (T / (2 * q ^ 2)) := by
    field_simp
  have h13 : 0 ≤ D * T / q ^ 2 := by positivity
  have h14 : 0 ≤ K * (ε * T) := by positivity
  have h15 : 0 ≤ C₁ * (ε * T) := by positivity
  nlinarith only [hJsum, h3, h4, h6, h7, h8, h10, h11, h12, h13, h14, h15, hεT]

/-! ## The theorem -/

/-- **The central inequality at the critical scale.** There is an absolute `c > 0` such that for every `δ > 0` there is `κ > 0` with: for all large `T`, outside a set of `X ∈ [T, 2T]` of measure at most `δT`, all real zeros `x < x'` of `H_t` with `|x − X| ≤ κ/(2 log T)` and `7κ/log T ≤ t log(x/2π) ≤ 1/8` satisfy `(x' − x)² ≥ c min(t, 1/log²(2 + |x|))`. -/
theorem exists_central_inequality_at_critical_scale :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ T : ℝ in atTop,
      volume {X | X ∈ Icc T (2 * T) ∧ ¬ ∀ t x x' : ℝ, 0 < t → |x - X| ≤ κ / (2 * Real.log T) →
          7 * κ / Real.log T ≤ t * Real.log (x / (2 * Real.pi)) → t * Real.log (x / (2 * Real.pi)) ≤ 1 / 8 → x < x' →
          riemannHeat t (x : ℂ) = 0 → riemannHeat t (x' : ℂ) = 0 →
          c * min t (1 / Real.log (2 + |x|) ^ 2) ≤ (x' - x) ^ 2} ≤ ENNReal.ofReal (δ * T) := by
  set c₀ := 1 / (20 * Real.exp 7) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  obtain ⟨A, hA, hbad⟩ := exists_volume_not_criticalGood_le
  refine ⟨4 * c₀ ^ 2, by positivity, ?_⟩
  intro δ hδ
  set q : ℝ := max ((10 : ℝ) ^ 4) (A / δ + 1) with hq
  have hq1 : (10 : ℝ) ^ 4 ≤ q := le_max_left _ _
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq1
  have hq11 : (1 : ℝ) ≤ q := le_trans (by norm_num) hq1
  have hqA : A ≤ δ * q ^ 2 := by
    have h1 : A / δ + 1 ≤ q := le_max_right _ _
    have h2 : A / δ ≤ q := by linarith only [h1]
    rw [div_le_iff₀ hδ] at h2
    have h3 : q ≤ q ^ 2 := le_self_pow₀ hq11 (by norm_num)
    nlinarith only [h2, h3, hδ]
  refine ⟨q ^ 4, by positivity, ?_⟩
  filter_upwards [hbad q hq1, eventually_ge_atTop (1100 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (10 ^ 6 : ℝ)] with T hvol hT hlog
  refine (measure_mono ?_).trans (hvol.trans (ENNReal.ofReal_le_ofReal ?_))
  swap
  · rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have hT0 : 0 < T := by linarith only [hT]
    nlinarith only [mul_le_mul_of_nonneg_right hqA hT0.le]
  rintro X ⟨hXT, hprop⟩
  refine ⟨hXT, fun hgood => hprop ?_⟩
  intro t x x' ht hx hκt ht1 hxx' h0 h0'
  obtain ⟨hK, hdata⟩ := hgood
  set L := Real.log T with hL
  have hL0 : 0 < L := by linarith only [hlog]
  set R₀ := q ^ 4 / L with hR₀
  have hR₀pos : 0 < R₀ := by positivity
  have hq4 : ((10 : ℝ) ^ 4) ^ 4 ≤ q ^ 4 := pow_le_pow_left₀ (by positivity) hq1 4
  have hq3 : ((10 : ℝ) ^ 4) ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (by positivity) hq1 3
  have hq2 : ((10 : ℝ) ^ 4) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by positivity) hq1 2
  have hx' : |x - X| ≤ R₀ / 2 := by
    refine hx.trans (le_of_eq ?_)
    rw [hR₀]
    field_simp
  have hL4 : 1 / L ≤ 1 / 10 ^ 6 := one_div_le_one_div_of_le (by positivity) hlog
  set u₀ := t * Real.log (x / (2 * Real.pi)) with hu₀
  have h7R₀ : 7 * R₀ ≤ u₀ := by
    rw [hR₀, mul_div_assoc'] 
    exact hκt
  have hR₀small : R₀ ≤ 1 / 56 := by linarith only [h7R₀, ht1]
  have hx1 := abs_le.mp hx'
  have hxlo : T - 1 ≤ x := by linarith only [hXT.1, hx1.1, hR₀small]
  have hxhi : x ≤ 2 * T + 1 := by linarith only [hXT.2, hx1.2, hR₀small]
  have hxpos : 0 < x := by linarith only [hxlo, hT]
  have hslope : 2 * t * (horizontalSlope x).re = u₀ := by
    rw [horizontalSlope_re, hu₀]
    ring
  have hT0 : 0 < T := by linarith only [hT]
  have hscale : L ≤ scaleLog T := by
    unfold scaleLog
    have := Real.log_le_log hT0 (show T ≤ 4 * T by linarith only [hT])
    linarith only [this]
  obtain ⟨hα1, -⟩ := slope_bounds (by linarith only [hT]) (by linarith only [hscale, hlog]) hxlo hxhi
  set α := (horizontalSlope x).re with hα
  have hαL : L / 8 ≤ α := by linarith only [hα1, hscale]
  have hα0 : 0 < α := by linarith only [hαL, hL0]
  -- the dyadic scale of the saddle
  set a := 69 / 10 * R₀ with ha
  have ha0 : 0 < a := by positivity
  have hau : 1 ≤ u₀ / a := by
    rw [le_div_iff₀ ha0, one_mul, ha]
    linarith only [h7R₀, hR₀pos]
  obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near hau (by norm_num : (1 : ℝ) < 2)
  rw [le_div_iff₀ ha0] at hj1
  rw [div_lt_iff₀ ha0] at hj2
  set R := critR q L j with hRdef
  set B := critB q L j with hBdef
  have hRval : R = 3 * 2 ^ j * R₀ := by
    rw [hRdef, hR₀]
    unfold critR
    ring
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hu₁ : 23 * R / 10 ≤ 2 * t * α := by
    rw [hslope, hRval]
    have : (2 : ℝ) ^ j * a = 69 / 10 * (2 ^ j * R₀) := by
      rw [ha]
      ring
    linarith only [hj1, this]
  have hu₂ : 2 * t * α ≤ 46 * R / 10 := by
    rw [hslope, hRval]
    have : (2 : ℝ) ^ (j + 1) * a = 69 / 5 * (2 ^ j * R₀) := by
      rw [ha, pow_succ]
      ring
    linarith only [hj2, this]
  have hRpos : 0 < R := by
    rw [hRval]
    positivity
  have hR16 : R ≤ 1 / 16 := by
    rw [hslope] at hu₁
    linarith only [hu₁, ht1]
  have hR₀R : 3 * R₀ ≤ R := by
    rw [hRval]
    nlinarith only [h2j, hR₀pos]
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    unfold critB
    positivity
  have hBle : B ≤ L / (3 * q ^ 3) := by
    rw [hBdef]
    unfold critB
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have h3 : (5 / 8 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith only [h3, hL0]
  -- the size of the products
  have hR₀α : q ^ 4 / 8 ≤ R₀ * α := by
    have h3 := mul_le_mul_of_nonneg_left hαL hR₀pos.le
    refine le_trans (le_of_eq ?_) h3
    rw [hR₀]
    field_simp
  have hRα : 10 ^ 6 ≤ R * α := by
    have h3 := mul_le_mul_of_nonneg_right hR₀R hα0.le
    norm_num at hq4
    nlinarith only [h3, hR₀α, hq4, mul_pos hR₀pos hα0]
  have hB400 : 400 * (B + 1) ≤ α - 1 := by
    have h3 : L / (3 * q ^ 3) ≤ L / 3000000000000 := by
      refine div_le_div_of_nonneg_left hL0.le (by norm_num) ?_
      norm_num at hq3
      linarith only [hq3]
    linarith only [hBle, h3, hαL, hlog]
  -- the model error
  have ht2 : t ≤ 92 / 5 * (R / L) := by
    have h3 : t * α ≤ 23 * R / 10 := by linarith only [hu₂]
    have h4 : t * (L / 8) ≤ t * α := mul_le_mul_of_nonneg_left hαL ht.le
    have h5 : t * L ≤ 92 / 5 * R := by linarith only [h3, h4]
    rw [mul_div_assoc', le_div_iff₀ hL0]
    exact h5
  have hq' : (B + 1) * Real.sqrt t ≤ 1 / 200 := by
    have h3 : ((B + 1) * Real.sqrt t) ^ 2 ≤ (1 / 200) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ht.le]
      have hB2R : B ^ 2 * (R / L) = (25 / 32) ^ j / (3 * q ^ 2) := by
        have h4 : ((5 / 8 : ℝ) ^ j) ^ 2 * 2 ^ j = (25 / 32) ^ j := by
          rw [← pow_mul, mul_comm j 2, pow_mul, ← mul_pow]
          norm_num
        rw [hBdef, hRdef, ← h4]
        unfold critB critR
        field_simp
      have h5 : (25 / 32 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h6 : B ^ 2 * t ≤ 92 / 5 * ((25 / 32) ^ j / (3 * q ^ 2)) := by
        have h7 := mul_le_mul_of_nonneg_left ht2 (sq_nonneg B)
        rw [← hB2R]
        linarith only [h7]
      have h8 : (25 / 32 : ℝ) ^ j / (3 * q ^ 2) ≤ 1 / 300000000 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        norm_num at hq2
        nlinarith only [h5, hq2]
      have h9 : t ≤ 2 / 1000000 := by
        have h10 : R / L ≤ (1 / 16) * (1 / L) := by
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_right hR16 (by positivity)
        norm_num at hL4
        norm_num at h10
        nlinarith only [ht2, h10, hL4]
      nlinarith only [h6, h8, h9, sq_nonneg (B - 1), ht, mul_nonneg (sq_nonneg (B - 1)) ht.le]
    have h4 : 0 ≤ (B + 1) * Real.sqrt t := by positivity
    exact (pow_le_pow_iff_left₀ h4 (by norm_num) (by norm_num)).mp h3
  have hX1100 : 1100 ≤ X := hT.trans hXT.1
  have hg := gap_ge_of_critical_data hR₀pos hR16 hR₀R hK (hdata j hR16) hB0 hX1100 hx'
    (by linarith only [hαL, hlog]) ht hu₁ hu₂ hRα (by norm_num at hq4; linarith only [hR₀α, hq4]) hB400 hq'
    hxx' h0 h0'
  -- the normalized form
  have hαlog : 2 * α ≤ Real.log x := by
    rw [hα, horizontalSlope_re]
    have h1 : x / (2 * Real.pi) ≤ x := div_le_self hxpos.le (by nlinarith only [Real.pi_gt_three])
    have h2 := Real.log_le_log (by positivity) h1
    linarith only [h2]
  have hL2 : Real.log x ≤ Real.log (2 + |x|) := by
    apply Real.log_le_log hxpos
    have := le_abs_self x
    linarith only [this]
  have hLpos : 0 < Real.log (2 + |x|) := by linarith only [hαlog, hα0, hL2]
  have hg2 : 2 * c₀ / Real.log (2 + |x|) ≤ x' - x := by
    refine le_trans ?_ hg
    rw [div_le_div_iff₀ hLpos hα0]
    have := mul_le_mul_of_nonneg_left (hαlog.trans hL2) hc₀pos.le
    linarith only [this]
  have hsq : (2 * c₀ / Real.log (2 + |x|)) ^ 2 ≤ (x' - x) ^ 2 := pow_le_pow_left₀ (by positivity) hg2 2
  refine le_trans ?_ hsq
  have hmin : min t (1 / Real.log (2 + |x|) ^ 2) ≤ 1 / Real.log (2 + |x|) ^ 2 := min_le_right _ _
  refine (mul_le_mul_of_nonneg_left hmin (by positivity)).trans (le_of_eq ?_)
  field_simp
  norm_num

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

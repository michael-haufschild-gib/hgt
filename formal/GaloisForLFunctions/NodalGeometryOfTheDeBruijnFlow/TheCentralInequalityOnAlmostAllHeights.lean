import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.AboveTheHorizonTheZerosAreSpaced
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TypicalHeightLocalNewman
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.DensityOneExtraction

/-!
# The central inequality on almost all heights

On a set of heights of density arbitrarily close to one, the crystal is already formed at every positive multiple of `1/log X`. There is an absolute `c > 0` such that, for every `κ > 0` and every `δ > 0`, all
heights `X ∈ [T, 2T]` outside a set of measure at most `δT` have the following property: for `κ ≤ t log(x/2π) ≤ 1`, any two real zeros `x < x'` of `H_t` in the unit window of `X` satisfy

`(x' − x)² ≥ c/log²x`    (`exists_central_inequality_on_almost_all_heights`).

So the central inequality holds at density-one heights down to any fixed coefficient `κ`, with a constant that does not depend on `κ`, and one set of density one serves all `κ` (`exists_densityOne_central_inequality`). At a typical height `ζ` has no zero in a box to the right of the line, and the half-Gauss transform is one exponential down to
that box: the amplitude and the two quadratures behave as above the horizon (`eventually_gap_ge_of_typicalWindow`). This is a mechanism for the density-one vanishing `Λ_X log X → 0` that sees the gaps and not only the reality of the zeros. The inequality below `κ/log X` is the open core.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-- The errors at a typical height are small, and the slope error is a small multiple of the slope. -/
theorem eventually_typical_errors_small {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∀ᶠ α : ℝ in atTop, ∀ T τ : ℝ, 8 ≤ T → 1 + Real.log (4 * T) ≤ 8 * α → 0 < τ → τ ≤ 1 / 8 →
      16 * η ≤ 2 * τ * α → 2 * τ * α ≤ 2 →
      typicalHalfGaussError η T τ α ≤ 1 / 5 ∧
      typicalHalfGaussSlopeError η T τ α ≤ α / 100 ∧
      typicalXiSlopeError η T ≤ 2 / 9 * α := by
  have hb := eventually_affineLog_le_linear (96 / η ^ 2)
    ((96 * Real.log 8 + 216) / η ^ 2 + 4) (by norm_num : (0 : ℝ) < 2 / 9)
  have hC := eventually_typicalTailLogEnvelope_le (η := η) (show 0 < η ^ 2 by positivity)
  have hM := (tendsto_typicalMainEnvelope hη).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 5))
  have hS := (tendsto_typicalSlopeNormalizedEnvelope hη).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 100))
  filter_upwards [hb, hC, hM, hS, eventually_ge_atTop (8 : ℝ)] with α hb hC hM hS hα
  intro T τ hT hscale hτ hτ8 hc hc2
  have hb' : typicalSlopeEnvelope η α ≤ 2 / 9 * α := by
    unfold typicalSlopeEnvelope
    linarith only [hb]
  obtain ⟨he, hs, -⟩ := typicalHalfGaussErrors_le_envelopes hη hη8 hT hα hscale
    hτ hτ8 hc hc2 hb' hC
  have hα0 : 0 < α := by linarith only [hα]
  refine ⟨he.trans hM, hs.trans ?_, le_trans ?_ hb'⟩
  · have := mul_le_mul_of_nonneg_left hS hα0.le
    linarith only [this]
  · unfold typicalXiSlopeError typicalSlopeEnvelope
    have hT4 : 1 ≤ 4 * T := by linarith only [hT]
    have hlog0 : 0 ≤ Real.log (4 * T) := Real.log_nonneg hT4
    have h1 : Real.log (1 + Real.log (4 * T)) ≤ Real.log (8 * α) :=
      Real.log_le_log (by linarith only [hlog0]) hscale
    rw [Real.log_mul (by norm_num) hα0.ne'] at h1
    have hη2 : 0 < η ^ 2 := by positivity
    have h2 : 24 * (4 * Real.log (1 + Real.log (4 * T)) + 9) ≤ 96 * Real.log α + (96 * Real.log 8 + 216) := by
      linarith only [h1]
    have h3 := div_le_div_of_nonneg_right h2 hη2.le
    have h4 : (96 * Real.log α + (96 * Real.log 8 + 216)) / η ^ 2 =
        96 / η ^ 2 * Real.log α + (96 * Real.log 8 + 216) / η ^ 2 := by ring
    linarith only [h3, h4]

/-- The elementary comparison with a main term. -/
theorem sub_le_norm_of_main {A Mn : ℂ} {P E e : ℝ} (h1 : ‖A - Mn‖ ≤ P * E) (h2 : ‖Mn‖ = P * e) : P * e - P * E ≤ ‖A‖ := by
  have h := norm_sub_norm_le Mn (Mn - A)
  rw [sub_sub_cancel, norm_sub_rev Mn, h2] at h
  linarith only [h, h1]

/-- **The gap from the data at one height.** Suppose the errors of the half-Gauss transform are small at all slopes near `α = Re a(x)`, and every height within `2/α` of `x` is `η`-close to a typical box. Then at a real zero `x` of `H_τ` with `17η ≤ 2τα ≤ 1`, the next real zero lies at distance at least `1/(20 e⁷ α)`. Nothing here depends on how `η` relates to `T`. -/
theorem gap_ge_of_typical_data {η T τ x x' : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hT1000 : 1002 ≤ T)
    (hTη : 2 / η ≤ T) (hxlo : T - 1 / 2 ≤ x) (hα101 : 101 ≤ (horizontalSlope x).re)
    (hαη : 1 / η + 4 ≤ (horizontalSlope x).re)
    (hA : ∀ β : ℝ, (horizontalSlope x).re - 1 ≤ β → β ≤ (horizontalSlope x).re + 1 →
      1 + Real.log (4 * T) ≤ 8 * β → 16 * η ≤ 2 * τ * β → 2 * τ * β ≤ 2 →
      typicalHalfGaussError η T τ β ≤ 1 / 5 ∧ typicalHalfGaussSlopeError η T τ β ≤ β / 100 ∧
        typicalXiSlopeError η T ≤ 2 / 9 * β)
    (hwin : ∀ ξ : ℝ, |ξ - x| ≤ 2 * (1 / (horizontalSlope x).re) → ∃ t : ℝ,
      zetaTypicalHeight η (zetaPolylogLevel T) T t ∧ |ξ - t| ≤ η)
    (hτ : 0 < τ) (hc1 : 17 * η ≤ 2 * τ * (horizontalSlope x).re) (hc2 : 2 * τ * (horizontalSlope x).re ≤ 1)
    (hxx' : x < x') (hx0 : riemannHeat τ (x : ℂ) = 0) (hx'0 : riemannHeat τ (x' : ℂ) = 0) :
    1 / (20 * Real.exp 7) / (horizontalSlope x).re ≤ x' - x := by
  have hT8 : 8 ≤ T := by linarith only [hT1000]
  have hη1 : η ≤ 1 := by linarith only [hη8]
  have hxpos : 0 < x := by linarith only [hxlo, hT1000]
  set α := (horizontalSlope x).re with hα
  have hα100 : 100 ≤ α := by linarith only [hα101]
  have hα0 : 0 < α := by linarith only [hα100]
  have hτ8 : τ ≤ 1 / 8 := by nlinarith only [hc2, hα100, hτ]
  set R := 1 / α with hR
  have hRpos : 0 < R := by positivity
  have hαR : α * R = 1 := by
    rw [hR]
    field_simp
  have hR100 : R ≤ 1 / 100 := by
    rw [hR]
    exact one_div_le_one_div_of_le (by norm_num) hα100
  have hRη : R ≤ η := by
    rw [hR, div_le_iff₀ hα0]
    have := mul_le_mul_of_nonneg_left hαη hη.le
    have h2 : η * (1 / η + 4) = 1 + 4 * η := by
      field_simp
    linarith only [this, h2, hη]
  -- the facts at each nearby height
  have hpt (ξ : ℝ) (hξ : |ξ - x| ≤ 2 * R) :
      |ξ - x| ≤ 2 * R ∧ T - 1 ≤ ξ ∧ 400 ≤ ξ ∧ |(horizontalSlope ξ).re - α| ≤ 2 * R * (2 / T) ∧
        16 * η ≤ 2 * τ * (horizontalSlope ξ).re ∧ 2 * τ * (horizontalSlope ξ).re ≤ 2 ∧
        α - 1 ≤ (horizontalSlope ξ).re ∧ (horizontalSlope ξ).re ≤ α + 1 := by
    have h2R : 2 * R ≤ 1 / 50 := by linarith only [hR100]
    have h1 := abs_le.mp hξ
    have hξlo : T - 1 ≤ ξ := by linarith only [hxlo, h1.1, h2R]
    have hξpos : 0 < ξ := by linarith only [hξlo, hT1000]
    have hslope : |(horizontalSlope ξ).re - α| ≤ 2 * R * (2 / T) := by
      have h3 := abs_horizontalSlope_re_sub_le hxpos hξpos
      refine h3.trans ?_
      have hmin : T / 2 ≤ min x ξ := le_min (by linarith only [hxlo, hT1000]) (by linarith only [hξlo, hT1000])
      have hTpos : 0 < T := by linarith only [hT1000]
      have hTinv : |ξ - x| / min x ξ ≤ 2 * R / (T / 2) :=
        div_le_div₀ (by positivity) hξ (by positivity) hmin
      refine hTinv.trans (le_of_eq ?_)
      field_simp
    have hsmall : 2 * R * (2 / T) ≤ 1 / T := by
      have hTpos : 0 < T := by linarith only [hT1000]
      have h3 : 2 * R * (2 / T) = (4 * R) * (1 / T) := by ring
      rw [h3]
      have h4 : 4 * R ≤ 1 := by linarith only [hR100]
      have h5 : 0 < 1 / T := by positivity
      nlinarith only [h4, h5]
    have hT1 : 1 / T ≤ η / 2 := by
      have hTpos : 0 < T := by linarith only [hT1000]
      rw [div_le_div_iff₀ hTpos (by norm_num)]
      have h3 := (div_le_iff₀ hη).mp hTη
      nlinarith only [h3]
    have hT2' : 1 / T ≤ 1 := by
      rw [div_le_one (by linarith only [hT1000])]
      linarith only [hT1000]
    have hs := abs_le.mp (hslope.trans hsmall)
    refine ⟨hξ, hξlo, by linarith only [hξlo, hT1000], hslope, ?_, ?_, by linarith only [hs.1, hT2'],
      by linarith only [hs.2, hT2']⟩
    · have h3 : 2 * τ * (-(η / 2)) ≤ 2 * τ * ((horizontalSlope ξ).re - α) :=
        mul_le_mul_of_nonneg_left (by linarith only [hs.1, hT1]) (by positivity)
      have h4 : 2 * τ * (η / 2) ≤ η := by nlinarith only [hτ8, hη, hτ]
      nlinarith only [h3, h4, hc1]
    · have h3 : 2 * τ * ((horizontalSlope ξ).re - α) ≤ 2 * τ * 1 :=
        mul_le_mul_of_nonneg_left (by linarith only [hs.2, hT2']) (by positivity)
      nlinarith only [h3, hc2, hτ8]
  set P := horizonAmp τ x with hPdef
  have hxX₁ : |x - x| ≤ 2 * R := by
    rw [sub_self, abs_zero]
    positivity
  -- the typical data at the point `x`
  obtain ⟨tx, htx, hxt⟩ := hwin x hxX₁
  have hpx := hpt x hxX₁
  have hx200 : 200 ≤ x := by linarith only [hpx.2.2.1]
  have hP0 : 0 < P := by
    rw [hPdef]
    unfold horizonAmp
    rw [← hα]
    refine mul_pos (norm_pos_iff.mpr (xiLine_ne_zero_of_typical htx hη hη1 hx200 hxt ?_)) (Real.exp_pos _)
    have := hpx.2.2.2.2.1
    rw [← hα] at *
    linarith only [hc1, hη]
  have hscalex : 1 + Real.log (4 * T) ≤ 8 * α :=
    dyadic_log_le_horizontalSlope hT8 (by linarith only [hxlo, hT1000]) hxpos (by rw [← hα]; linarith only [hα100])
  have hc16 : 16 * η ≤ 2 * τ * α := by linarith only [hc1, hη]
  obtain ⟨hEx, hSx, hBx⟩ := hA α (by linarith only) (by linarith only) hscalex hc16 (by linarith only [hc2])
  set B := typicalXiSlopeError η T with hB
  have hBpos : 0 < B := typicalXiSlopeError_pos (by linarith only [hT8])
  set ux := 2 * τ * α with hux
  have hux2η : 2 * η ≤ ux := by linarith only [hc16, hη]
  -- comparison along the segment of heights
  have hseg (ξ : ℝ) (hξ : |ξ - x| ≤ 2 * R) : ‖xiLine ξ ux‖ ≤ ‖xiLine x ux‖ * Real.exp 1 := by
    have hmem (s : ℝ) (hs : s ∈ uIcc x ξ) : |s - x| ≤ 2 * R := by
      have h1 := abs_le.mp hξ
      rcases le_total x ξ with h | h
      · rw [uIcc_of_le h] at hs
        rw [abs_of_nonneg (by linarith only [hs.1])]
        linarith only [hs.2, h1.2]
      · rw [uIcc_of_ge h] at hs
        rw [abs_of_nonpos (by linarith only [hs.2])]
        linarith only [hs.1, h1.1]
    have hb : ∀ s ∈ uIcc x ξ, ‖I * xiLineDeriv s ux - (I * horizontalSlope x) * xiLine s ux‖ ≤
        (B + 1) * ‖xiLine s ux‖ := by
      intro s hs
      obtain ⟨h1, -, h3, h4, -, -, -, -⟩ := hpt s (hmem s hs)
      obtain ⟨t', ht', hst⟩ := hwin s h1
      have hs200 : 200 ≤ s := by linarith only [h3]
      have hd := norm_xiLineDeriv_sub_le_of_typical ht' hη hη1 hT8 hs200 hst hux2η
        (by linarith only [hc2, hs200])
      have h2 : ‖horizontalSlope s - horizontalSlope x‖ ≤ 1 := by
        have h5 : horizontalSlope s - horizontalSlope x =
            (((horizontalSlope s).re - (horizontalSlope x).re : ℝ) : ℂ) := by
          apply Complex.ext
          · simp
          · simp [horizontalSlope_im]
        rw [h5, Complex.norm_real, Real.norm_eq_abs, ← hα]
        refine h4.trans ?_
        have hTpos : 0 < T := by linarith only [hT1000]
        have h6 : 2 * R * (2 / T) = (4 * R) * (1 / T) := by ring
        rw [h6]
        have h7 : 4 * R ≤ 1 := by linarith only [hR100]
        have h8 : 1 / T ≤ 1 := by
          rw [div_le_one hTpos]
          linarith only [hT1000]
        have h9 : 0 < 1 / T := by positivity
        nlinarith only [h7, h8, h9, hRpos]
      have h4' : I * xiLineDeriv s ux - (I * horizontalSlope x) * xiLine s ux =
          I * ((xiLineDeriv s ux - horizontalSlope s * xiLine s ux) +
            (horizontalSlope s - horizontalSlope x) * xiLine s ux) := by ring
      rw [h4', norm_mul, Complex.norm_I, one_mul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have h5 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (xiLine s ux))
      linarith only [hd, h5]
    have hm := GaloisForLFunctions.HTGeometry.norm_sub_mul_exp_le (a := I * horizontalSlope x) (η := B + 1)
      (u := x) (w := ξ) (by positivity) (fun s _ => hasDerivAt_xiLine_height' ux s) hb
    have hre : (I * horizontalSlope x).re = -(Real.pi / 4) := by
      rw [Complex.mul_re, Complex.I_re, Complex.I_im, horizontalSlope_im]
      ring
    rw [hre] at hm
    have htri := norm_add_le (xiLine ξ ux - xiLine x ux * Complex.exp (((ξ - x : ℝ) : ℂ) * (I * horizontalSlope x)))
      (xiLine x ux * Complex.exp (((ξ - x : ℝ) : ℂ) * (I * horizontalSlope x)))
    rw [sub_add_cancel, norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, hre] at htri
    have hn := norm_nonneg (xiLine x ux)
    have hexpand : ‖xiLine x ux‖ * Real.exp ((ξ - x) * -(Real.pi / 4)) * Real.exp ((B + 1) * |ξ - x|) =
        ‖xiLine x ux‖ * Real.exp ((ξ - x) * -(Real.pi / 4)) * (Real.exp ((B + 1) * |ξ - x|) - 1) +
          ‖xiLine x ux‖ * Real.exp ((ξ - x) * -(Real.pi / 4)) := by ring
    have hle : ‖xiLine ξ ux‖ ≤ ‖xiLine x ux‖ * Real.exp ((ξ - x) * -(Real.pi / 4)) * Real.exp ((B + 1) * |ξ - x|) := by
      linarith only [hm, htri, hexpand]
    refine hle.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hn
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : (ξ - x) * -(Real.pi / 4) ≤ |ξ - x| := by
      have hpi : Real.pi / 4 ≤ 1 := by linarith only [Real.pi_lt_d2]
      have hpi0 : 0 ≤ Real.pi / 4 := by positivity
      have h2 := neg_abs_le (ξ - x)
      have h3 := abs_nonneg (ξ - x)
      nlinarith only [h2, h3, hpi, hpi0]
    have h2 : (B + 2) * |ξ - x| ≤ (B + 2) * (2 * R) := mul_le_mul_of_nonneg_left hξ (by positivity)
    have h3 : B * (2 * R) ≤ 4 / 9 := by
      have h4 : B * R ≤ 2 / 9 * α * R := mul_le_mul_of_nonneg_right hBx hRpos.le
      have h5 : 2 / 9 * α * R = 2 / 9 := by
        rw [mul_assoc, hαR, mul_one]
      nlinarith only [h4, h5]
    nlinarith only [h1, h2, h3, hR100]
  -- the amplitude at nearby heights
  have hamp (ξ : ℝ) (hξ : |ξ - x| ≤ 2 * R) :
      ‖xiLine ξ (2 * τ * (horizontalSlope ξ).re)‖ * Real.exp (-(τ * (horizontalSlope ξ).re ^ 2)) ≤
        P * Real.exp 3 := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpt ξ hξ
    obtain ⟨t', ht', hξt⟩ := hwin ξ h1
    have hξ200 : 200 ≤ ξ := by linarith only [h3]
    set β := (horizontalSlope ξ).re with hβ
    have hβα : |β - α| ≤ 1 := abs_le.mpr ⟨by linarith only [h7], by linarith only [h8]⟩
    have hmodel := norm_xiLine_le_model_of_typical ht' hη hη1 hT8 hξ200 hξt (u := ux) (w := 2 * τ * β)
      ⟨hux2η, by linarith only [hc2, hξ200]⟩ ⟨by linarith only [h5, hη], by linarith only [h6, hξ200]⟩
    rw [← hβ, ← hB] at hmodel
    have hdiff : |2 * τ * β - ux| ≤ 2 * τ * |β - α| := by
      rw [hux, show 2 * τ * β - 2 * τ * α = 2 * τ * (β - α) by ring, abs_mul, abs_of_pos (by positivity : 0 < 2 * τ)]
    have hB1 : B * |2 * τ * β - ux| ≤ 1 := by
      have h9 : B * |2 * τ * β - ux| ≤ (2 / 9 * α) * (2 * τ * 1) := by
        refine mul_le_mul hBx (hdiff.trans (mul_le_mul_of_nonneg_left hβα (by positivity))) (abs_nonneg _) (by positivity)
      have h10 : (2 / 9 * α) * (2 * τ * 1) = 2 / 9 * ux := by
        rw [hux]
        ring
      rw [h10] at h9
      linarith only [h9, hc2]
    have hexpo : (2 * τ * β - ux) * β - τ * β ^ 2 ≤ -(τ * α ^ 2) + 1 := by
      have h9 : (2 * τ * β - ux) * β - τ * β ^ 2 + τ * α ^ 2 = τ * (β - α) ^ 2 := by
        rw [hux]
        ring
      have h10 : (β - α) ^ 2 ≤ 1 := by
        rw [← sq_abs]
        nlinarith only [hβα, abs_nonneg (β - α)]
      have h11 : τ * (β - α) ^ 2 ≤ τ * 1 := mul_le_mul_of_nonneg_left h10 hτ.le
      linarith only [h9, h11, hτ8]
    have hexpP : P = ‖xiLine x ux‖ * Real.exp (-(τ * α ^ 2)) := by
      rw [hPdef]
      unfold horizonAmp
      rw [← hα]
    have hsegξ := hseg ξ hξ
    have hn0 := norm_nonneg (xiLine ξ ux)
    calc ‖xiLine ξ (2 * τ * β)‖ * Real.exp (-(τ * β ^ 2))
        ≤ (‖xiLine ξ ux‖ * Real.exp ((2 * τ * β - ux) * β) * Real.exp (B * |2 * τ * β - ux|)) *
            Real.exp (-(τ * β ^ 2)) := mul_le_mul_of_nonneg_right hmodel (Real.exp_pos _).le
      _ = ‖xiLine ξ ux‖ * Real.exp ((2 * τ * β - ux) * β - τ * β ^ 2 + B * |2 * τ * β - ux|) := by
          rw [Real.exp_add, Real.exp_sub, Real.exp_neg]
          field_simp
      _ ≤ (‖xiLine x ux‖ * Real.exp 1) * Real.exp (-(τ * α ^ 2) + 1 + 1) :=
          mul_le_mul hsegξ (Real.exp_le_exp.mpr (by linarith only [hexpo, hB1])) (Real.exp_pos _).le
            (by positivity)
      _ = P * Real.exp 3 := by
          rw [hexpP, show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
          ring
  -- the amplitude and the transform at each nearby height
  have hstep (ξ v : ℝ) (hξ : |ξ - x| ≤ 2 * R) (hv : |v| ≤ 2 * R) :
      ‖halfGaussTransform τ (xiLine ξ) v‖ ≤ 6 / 5 * Real.exp 7 * P := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpt ξ hξ
    obtain ⟨t', ht', hξt⟩ := hwin ξ h1
    have hξ200 : 200 ≤ ξ := by linarith only [h3]
    have hξpos : 0 < ξ := by linarith only [hξ200]
    set β := (horizontalSlope ξ).re with hβ
    have hβ100 : 100 ≤ β := by linarith only [h7, hα101]
    have hβ8 : 8 ≤ (horizontalSlope ξ).re := by rw [← hβ]; linarith only [hβ100]
    have hscale := dyadic_log_le_horizontalSlope hT8 (by linarith only [h2, hT1000]) hξpos hβ8
    rw [← hβ] at hscale
    obtain ⟨hE, -, hB⟩ := hA β h7 h8 hscale h5 h6
    obtain ⟨hvl, hvu⟩ := abs_le.mp hv
    have hv2R : 2 * R ≤ 2 * η := by linarith only [hRη]
    have hWX := window_fits hτ8 hτ hξpos (by rw [← hβ]; linarith only [hβ100])
    have hmain := norm_halfGauss_sub_main_le_of_typical ht' hη hη8 hT8 hξ200 hξt hτ hτ8
      (by rw [← hβ]; linarith only [hβ100]) (by rw [← hβ]; exact h5) (by rw [← hβ]; exact h6)
      (y := v) (by linarith only [hvl, hv2R, hη]) (by linarith only [hvu, hR100]) hWX
    rw [← hβ] at hmain
    have hmn := norm_main_eq (t := τ) (X := ξ) (y := v) (xiLine ξ (v + 2 * τ * β))
    rw [← hβ] at hmn
    set Pv := ‖xiLine ξ (v + 2 * τ * β)‖ * Real.exp (-(τ * β ^ 2)) with hPv
    have hPv0 : 0 ≤ Pv := by positivity
    have hmn' : ‖xiLine ξ (v + 2 * τ * β) * Complex.exp (-(((v + 2 * τ * β : ℝ) : ℂ) * horizontalSlope ξ)) *
        Complex.exp (v * horizontalSlope ξ + τ * horizontalSlope ξ ^ 2)‖ ≤ Pv := by
      refine le_of_eq_of_le hmn ?_
      have hexp : Real.exp (-(τ * (Real.pi / 4) ^ 2)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have : 0 ≤ τ * (Real.pi / 4) ^ 2 := by positivity
        linarith only [this]
      have := mul_le_mul_of_nonneg_left hexp hPv0
      simpa [hPv] using this
    have hEnorm : ‖halfGaussTransform τ (xiLine ξ) v‖ ≤ 6 / 5 * Pv := by
      have htri := norm_add_le (halfGaussTransform τ (xiLine ξ) v -
        xiLine ξ (v + 2 * τ * β) * Complex.exp (-(((v + 2 * τ * β : ℝ) : ℂ) * horizontalSlope ξ)) *
          Complex.exp (v * horizontalSlope ξ + τ * horizontalSlope ξ ^ 2))
        (xiLine ξ (v + 2 * τ * β) * Complex.exp (-(((v + 2 * τ * β : ℝ) : ℂ) * horizontalSlope ξ)) *
          Complex.exp (v * horizontalSlope ξ + τ * horizontalSlope ξ ^ 2))
      rw [sub_add_cancel] at htri
      have h9 := hmain.trans (mul_le_mul_of_nonneg_left hE hPv0)
      linarith only [htri, h9, hmn', hPv0]
    -- the shift in the source
    have hmodel := norm_xiLine_le_model_of_typical ht' hη hη1 hT8 hξ200 hξt (u := 2 * τ * β) (w := v + 2 * τ * β)
      ⟨by linarith only [h5, hη], by linarith only [h6, hξ200]⟩
      ⟨by linarith only [h5, hη, hvl, hv2R], by linarith only [h6, hξ200, hvu, hR100]⟩
    rw [← hβ, add_sub_cancel_right] at hmodel
    have hexpv : Real.exp (v * β) * Real.exp (typicalXiSlopeError η T * |v|) ≤ Real.exp 4 := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hβ0 : 0 < β := by linarith only [hβ100]
      have h9 : v * β ≤ 2 * R * (α + 1) := by
        have h10 := le_abs_self v
        calc v * β ≤ |v| * β := mul_le_mul_of_nonneg_right h10 hβ0.le
          _ ≤ 2 * R * (α + 1) := mul_le_mul hv h8 hβ0.le (by positivity)
      have h10 : 2 * R * (α + 1) = 2 * (α * R) + 2 * R := by ring
      rw [h10, hαR] at h9
      have h11 : typicalXiSlopeError η T * |v| ≤ (2 / 9 * β) * (2 * R) :=
        mul_le_mul hB hv (abs_nonneg _) (by positivity)
      have h12 : (2 / 9 * β) * (2 * R) ≤ (2 / 9 * (α + 1)) * (2 * R) :=
        mul_le_mul_of_nonneg_right (by linarith only [h8]) (by positivity)
      have h13 : (2 / 9 * (α + 1)) * (2 * R) = 4 / 9 * (α * R) + 4 / 9 * R := by ring
      rw [h13, hαR] at h12
      linarith only [h9, h11, h12, hR100]
    have hPv2 : Pv ≤ (‖xiLine ξ (2 * τ * β)‖ * Real.exp (-(τ * β ^ 2))) * Real.exp 4 := by
      rw [hPv]
      calc ‖xiLine ξ (v + 2 * τ * β)‖ * Real.exp (-(τ * β ^ 2))
          ≤ (‖xiLine ξ (2 * τ * β)‖ * Real.exp (v * β) * Real.exp (typicalXiSlopeError η T * |v|)) *
              Real.exp (-(τ * β ^ 2)) := mul_le_mul_of_nonneg_right hmodel (Real.exp_pos _).le
        _ = ‖xiLine ξ (2 * τ * β)‖ * Real.exp (-(τ * β ^ 2)) *
              (Real.exp (v * β) * Real.exp (typicalXiSlopeError η T * |v|)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hexpv (by positivity)
    have hA3 := hamp ξ hξ
    rw [← hβ] at hA3
    have hfinal : Pv ≤ P * Real.exp 7 := by
      refine hPv2.trans ?_
      have h9 := mul_le_mul_of_nonneg_right hA3 (Real.exp_pos 4).le
      refine h9.trans (le_of_eq ?_)
      rw [mul_assoc, ← Real.exp_add]
      norm_num
    calc ‖halfGaussTransform τ (xiLine ξ) v‖ ≤ 6 / 5 * Pv := hEnorm
      _ ≤ 6 / 5 * (P * Real.exp 7) := mul_le_mul_of_nonneg_left hfinal (by norm_num)
      _ = _ := by ring
  set M := 12 / 5 * Real.exp 7 * P with hM
  have hMpos : 0 < M := by positivity
  have hdisc (w : ℂ) (hw : ‖w - x‖ ≤ 2 * R) : ‖riemannHeat τ w‖ ≤ M := by
    have hre : |w.re - x| ≤ 2 * R := by
      have h := Complex.abs_re_le_norm (w - x)
      rw [Complex.sub_re, Complex.ofReal_re] at h
      exact h.trans hw
    have him : |w.im| ≤ 2 * R := by
      have h := Complex.abs_im_le_norm (w - x)
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
      exact h.trans hw
    have hw' : (w.re : ℂ) + I * (w.im : ℂ) = w := by
      apply Complex.ext <;> simp
    have hsplit : riemannHeat τ ((w.re : ℂ) + I * w.im) = halfGaussTransform τ (xiLine w.re) (-w.im) +
        starRingEnd ℂ (halfGaussTransform τ (xiLine w.re) w.im) :=
      riemannHeat_eq_halfGaussAverage hτ w.re w.im
    rw [hw'] at hsplit
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [RCLike.norm_conj]
    have h1 := hstep w.re (-w.im) hre (by rwa [abs_neg])
    have h2 := hstep w.re w.im hre him
    rw [hM]
    linarith only [h1, h2]
  have hmin := gap_ge_of_disc_bound (differentiable_riemannHeat hτ.le) hRpos hMpos hxx' hx0 hx'0 hdisc
  -- the derivative at the zero
  have hWX := window_fits hτ8 hτ hxpos (by rw [← hα]; linarith only [hα100])
  have hmain := norm_halfGauss_sub_main_le_of_typical htx hη hη8 hT8 hx200 hxt hτ hτ8
    (by rw [← hα]; linarith only [hα100]) (by rw [← hα]; exact hc16) (by rw [← hα]; linarith only [hc2])
    (y := 0) (by linarith only [hη]) (by norm_num) hWX
  have hslopex := norm_halfGauss_slope_sub_le_of_typical htx hη hη8 hT8 hx200 hxt hτ hτ8
    (by rw [← hα]; linarith only [hα100]) (by rw [← hα]; exact hc16) (by rw [← hα]; linarith only [hc2])
    (y := 0) (by linarith only [hη]) (by norm_num) hWX
  have hmn := norm_main_eq (t := τ) (X := x) (y := 0) (xiLine x (0 + 2 * τ * α))
  rw [← hα, zero_add] at hmn hmain hslopex
  have hPeq : ‖xiLine x ux‖ * Real.exp (-(τ * α ^ 2)) = P := by
    rw [hPdef]
    unfold horizonAmp
    rw [← hα]
  rw [hPeq] at hmn hmain hslopex
  set Ax := halfGaussTransform τ (xiLine x) 0 with hAx
  have hAlow : 18 / 25 * P ≤ ‖Ax‖ := by
    have hphase := gaussPhase_ge hτ8 hτ
    have h1 := mul_le_mul_of_nonneg_left hphase hP0.le
    have h2 := mul_le_mul_of_nonneg_left hEx hP0.le
    have h3 := sub_le_norm_of_main hmain hmn
    linarith only [h1, h2, h3]
  have hH := riemannHeat_ofReal_eq_two_re_halfGauss hτ x
  rw [hx0] at hH
  have hAre : Ax.re = 0 := by
    have h1 : (2 * Ax.re : ℝ) = 0 := by exact_mod_cast hH.symm
    linarith only [h1]
  have hAim : 18 / 25 * P ≤ |Ax.im| := by
    have h1 := Complex.norm_le_abs_re_add_abs_im Ax
    rw [hAre, abs_zero, zero_add] at h1
    exact hAlow.trans h1
  set D' := deriv (halfGaussTransform τ (xiLine x)) 0 with hD'
  have hD'eq : D' = ∫ w in Ioi (0 : ℝ), (((w - 0) / (2 * τ) * gaussDensity τ (w - 0) : ℝ) : ℂ) * xiLine x w :=
    (hasDerivAt_halfGaussTransform hτ (continuous_xiLine x) (integrable_exp_mul_norm_xiLine hτ x) 0).deriv
  rw [← hD'eq] at hslopex
  set Ex := D' - horizontalSlope x * Ax with hEx'
  have hEn : |Ex.im| ≤ P * (α / 100) :=
    (Complex.abs_im_le_norm Ex).trans (hslopex.trans (mul_le_mul_of_nonneg_left hSx hP0.le))
  have hDim : D'.im = α * Ax.im + Ex.im := by
    have h1 : D' = horizontalSlope x * Ax + Ex := by rw [hEx']; ring
    rw [h1, Complex.add_im, Complex.mul_im, horizontalSlope_im, hAre, ← hα]
    ring
  have hDlow : α * P / 2 ≤ |D'.im| := by
    have h1 : α * Ax.im = D'.im - Ex.im := by rw [hDim]; ring
    have h2 : |α * Ax.im| = α * |Ax.im| := by rw [abs_mul, abs_of_pos hα0]
    have h3 : |α * Ax.im| ≤ |D'.im| + |Ex.im| := by
      rw [h1]
      exact abs_sub _ _
    have h4 : α * (18 / 25 * P) ≤ α * |Ax.im| := mul_le_mul_of_nonneg_left hAim hα0.le
    have h5 : 0 < α * P := by positivity
    nlinarith only [h2, h3, h4, hEn, h5]
  set D₀ := deriv (riemannHeat τ) (x : ℂ) with hD₀
  have hD₀n : α * P ≤ ‖D₀‖ := by
    have h1 : D₀ = ((-2 * D'.im : ℝ) : ℂ) := deriv_riemannHeat_ofReal_eq_neg_two_im_deriv_halfGauss hτ x
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    norm_num
    linarith only [hDlow]
  have hEpos := Real.exp_pos 7
  have hE1 : 1 ≤ Real.exp 7 := Real.one_le_exp (by norm_num)
  have hcoef : 1 / (20 * Real.exp 7) / α ≤ min R (‖D₀‖ * R ^ 2 / (2 * M)) := by
    refine le_min ?_ ?_
    · rw [hR]
      refine div_le_div_of_nonneg_right ?_ hα0.le
      rw [div_le_one (by positivity)]
      linarith only [hE1]
    · have h1 : ‖D₀‖ * R ^ 2 / (2 * M) = ‖D₀‖ / (α ^ 2 * (2 * M)) := by
        rw [hR]
        field_simp
      rw [h1, div_le_div_iff₀ hα0 (by positivity), hM]
      have hval : 1 / (20 * Real.exp 7) * (α ^ 2 * (2 * (12 / 5 * Real.exp 7 * P))) = 6 / 25 * (α * (α * P)) := by
        field_simp
        ring
      rw [hval]
      have h2 := mul_le_mul_of_nonneg_left hD₀n hα0.le
      have h3 : 0 < α * (α * P) := by positivity
      nlinarith only [h2, h3]
  exact hcoef.trans hmin

/-- **The gaps at typical heights.** In the unit window of a typical height, for every heat time with `17η ≤ 2tα ≤ 1`, real zeros `x < x'` have `x' − x ≥ c/α`, with an absolute `c`. -/
theorem eventually_gap_ge_of_typicalWindow {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∀ᶠ T : ℝ in atTop, ∀ X ∈ Icc T (2 * T), zetaPolylogTypicalWindow η T X →
      ∀ τ x x' : ℝ, 0 < τ → |x - X| ≤ 1 / 2 → 17 * η ≤ 2 * τ * (horizontalSlope x).re →
        2 * τ * (horizontalSlope x).re ≤ 1 → x < x' →
        riemannHeat τ (x : ℂ) = 0 → riemannHeat τ (x' : ℂ) = 0 →
        1 / (20 * Real.exp 7) / (horizontalSlope x).re ≤ x' - x := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp (eventually_typical_errors_small hη hη8)
  have h1η : 0 < 1 / η := by positivity
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    (tendsto_horizontalSlope_re.eventually_ge_atTop (max (A + 1) (max 101 (1 / η + 4))))
  filter_upwards [eventually_ge_atTop (max X₀ 1000 + 2 + 2 / η)] with T hTbig
  have hT2 : max X₀ 1000 + 2 ≤ T := by
    have : 0 < 2 / η := by positivity
    linarith only [hTbig, this]
  have hTη : 2 / η ≤ T := by
    have h0 : 0 ≤ max X₀ 1000 := (by norm_num : (0 : ℝ) ≤ 1000).trans (le_max_right _ _)
    linarith only [hTbig, h0]
  have hT1000 : 1002 ≤ T := by linarith only [hT2, le_max_right X₀ 1000]
  have hT8 : 8 ≤ T := by linarith only [hT1000]
  have hTX₀ : X₀ + 2 ≤ T := by linarith only [hT2, le_max_left X₀ 1000]
  intro X hXT hwin τ x x' hτ hxX hc1 hc2 hxx' hx0 hx'0
  have hxlo : T - 1 / 2 ≤ x := by linarith only [hXT.1, (abs_le.mp hxX).1]
  have hαbig := hX₀ x (by linarith only [hxlo, hTX₀])
  have hαA : A + 1 ≤ (horizontalSlope x).re := (le_max_left _ _).trans hαbig
  have hα101 : 101 ≤ (horizontalSlope x).re := (le_max_of_le_right (le_max_left _ _)).trans hαbig
  have hαη : 1 / η + 4 ≤ (horizontalSlope x).re := (le_max_of_le_right (le_max_right _ _)).trans hαbig
  refine gap_ge_of_typical_data hη hη8 hT1000 hTη hxlo hα101 hαη ?_ ?_ hτ hc1 hc2 hxx' hx0 hx'0
  · intro β hβ1 _ hscale h16 h2
    have hβ100 : 100 ≤ β := by linarith only [hα101, hβ1]
    exact hA β (by linarith only [hαA, hβ1]) T τ hT8 hscale hτ (by nlinarith only [h2, hβ100, hτ]) h16 h2
  · intro ξ hξ
    refine hwin ξ ?_
    have h1 : 2 * (1 / (horizontalSlope x).re) ≤ 1 / 2 := by
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 101) hα101
      linarith only [this]
    have h2 := abs_le.mp hξ
    have h3 := abs_le.mp hxX
    rw [abs_le]
    constructor <;> linarith only [h1, h2.1, h2.2, h3.1, h3.2]

/-- **The central inequality on almost all heights.** There is an absolute `c > 0` such that, for all `κ, δ > 0` and large `T`, outside a set of measure at most `δT` every `X ∈ [T, 2T]` has the property: for `κ ≤ t log(x/2π) ≤ 1`, any two real zeros `x < x'` of `H_t` with `|x − X| ≤ ½` satisfy `c min(t, log⁻²(2 + |x|)) ≤ (x' − x)²`. -/
theorem exists_central_inequality_on_almost_all_heights :
    ∃ c : ℝ, 0 < c ∧ ∀ κ δ : ℝ, 0 < κ → 0 < δ → ∀ᶠ T : ℝ in atTop,
      volume {X | X ∈ Icc T (2 * T) ∧ ¬ ∀ t x x' : ℝ, 0 < t → |x - X| ≤ 1 / 2 →
          κ ≤ t * Real.log (x / (2 * Real.pi)) → t * Real.log (x / (2 * Real.pi)) ≤ 1 → x < x' →
          riemannHeat t (x : ℂ) = 0 → riemannHeat t (x' : ℂ) = 0 →
          c * min t (1 / Real.log (2 + |x|) ^ 2) ≤ (x' - x) ^ 2} ≤ ENNReal.ofReal (δ * T) := by
  set c₀ := 1 / (20 * Real.exp 7) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  refine ⟨4 * c₀ ^ 2, by positivity, ?_⟩
  intro κ δ hκ hδ
  set η := min (κ / 17) (1 / 8) with hη
  have hηpos : 0 < η := lt_min (by positivity) (by norm_num)
  have hη8 : η ≤ 1 / 8 := min_le_right _ _
  have hηκ : 17 * η ≤ κ := by
    have : η ≤ κ / 17 := min_le_left _ _
    linarith only [this]
  filter_upwards [eventually_gap_ge_of_typicalWindow hηpos hη8,
    eventually_volume_not_zetaPolylogTypicalWindow_le hηpos hδ, eventually_ge_atTop (1000 : ℝ)] with T hgap hbad hT
  refine (measure_mono ?_).trans hbad
  rintro X ⟨hXT, hprop⟩
  refine ⟨hXT, fun hwin => hprop ?_⟩
  intro t x x' ht hx hκt ht1 hxx' h0 h0'
  have hxlo : T - 1 / 2 ≤ x := by linarith only [hXT.1, (abs_le.mp hx).1]
  have hxpos : 0 < x := by linarith only [hxlo, hT]
  have hslope : 2 * t * (horizontalSlope x).re = t * Real.log (x / (2 * Real.pi)) := by
    rw [horizontalSlope_re]
    ring
  have hg := hgap X hXT hwin t x x' ht hx (by rw [hslope]; linarith only [hηκ, hκt])
    (by rw [hslope]; exact ht1) hxx' h0 h0'
  have hαL : 2 * (horizontalSlope x).re ≤ Real.log x := by
    rw [horizontalSlope_re]
    have h1 : x / (2 * Real.pi) ≤ x := div_le_self hxpos.le (by nlinarith only [Real.pi_gt_three])
    have h2 := Real.log_le_log (by positivity) h1
    linarith only [h2]
  have hαpos : 0 < (horizontalSlope x).re := by
    by_contra hn
    have h1 := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * t) (not_lt.mp hn)
    rw [hslope] at h1
    linarith only [h1, hκt, hκ]
  have hL2 : Real.log x ≤ Real.log (2 + |x|) := by
    apply Real.log_le_log hxpos
    have := le_abs_self x
    linarith only [this]
  have hLpos : 0 < Real.log (2 + |x|) := by linarith only [hαL, hαpos, hL2]
  have hg2 : 2 * c₀ / Real.log (2 + |x|) ≤ x' - x := by
    refine le_trans ?_ hg
    rw [div_le_div_iff₀ hLpos hαpos]
    have := mul_le_mul_of_nonneg_left (hαL.trans hL2) hc₀pos.le
    linarith only [this]
  have hsq : (2 * c₀ / Real.log (2 + |x|)) ^ 2 ≤ (x' - x) ^ 2 := pow_le_pow_left₀ (by positivity) hg2 2
  refine le_trans ?_ hsq
  have hmin : min t (1 / Real.log (2 + |x|) ^ 2) ≤ 1 / Real.log (2 + |x|) ^ 2 := min_le_right _ _
  refine (mul_le_mul_of_nonneg_left hmin (by positivity)).trans (le_of_eq ?_)
  field_simp
  norm_num

/-- The property of a height at coefficient `κ`. -/
def CentralAtHeight (c κ X : ℝ) : Prop :=
  ∀ t x x' : ℝ, 0 < t → |x - X| ≤ 1 / 2 →
    κ ≤ t * Real.log (x / (2 * Real.pi)) → t * Real.log (x / (2 * Real.pi)) ≤ 1 → x < x' →
    riemannHeat t (x : ℂ) = 0 → riemannHeat t (x' : ℂ) = 0 →
    c * min t (1 / Real.log (2 + |x|) ^ 2) ≤ (x' - x) ^ 2

/-- **The central inequality on one set of density one.** There are an absolute `c > 0` and a measurable set `S` of density one such that for every `κ > 0`, all large `X ∈ S` have: for `κ ≤ t log(x/2π) ≤ 1`, any two real zeros `x < x'` of `H_t` with `|x − X| ≤ ½`
satisfy `c min(t, log⁻²(2 + |x|)) ≤ (x' − x)²`. -/
theorem exists_densityOne_central_inequality :
    ∃ c : ℝ, 0 < c ∧ ∃ S : Set ℝ, MeasurableSet S ∧
      (∀ δ > 0, ∀ᶠ H : ℝ in atTop, volume (Sᶜ ∩ Icc 0 H) ≤ ENNReal.ofReal (δ * H)) ∧
      ∀ κ > 0, ∀ᶠ X : ℝ in atTop ⊓ 𝓟 S, CentralAtHeight c κ X := by
  obtain ⟨c, hc, hmeasure⟩ := exists_central_inequality_on_almost_all_heights
  refine ⟨c, hc, ?_⟩
  have hmono (κ κ' X : ℝ) (h : κ ≤ κ') (hP : CentralAtHeight c κ X) : CentralAtHeight c κ' X :=
    fun t x x' h1 h2 h3 h4 h5 h6 h7 => hP t x x' h1 h2 (h.trans h3) h4 h5 h6 h7
  -- the critical coefficient of a height
  set f : ℝ → ℝ := fun X => sInf {κ | 0 ≤ κ ∧ CentralAtHeight c κ X} with hf
  have hnonempty (X : ℝ) : ({κ | 0 ≤ κ ∧ CentralAtHeight c κ X}).Nonempty :=
    ⟨2, by norm_num, fun t x x' _ _ h3 h4 => absurd (h3.trans h4) (by norm_num)⟩
  have hbdd (X : ℝ) : BddBelow {κ | 0 ≤ κ ∧ CentralAtHeight c κ X} := ⟨0, fun κ hκ => hκ.1⟩
  have hf0 (X : ℝ) : 0 ≤ f X := le_csInf (hnonempty X) fun κ hκ => hκ.1
  have hlevel : ∀ ε > 0, ∀ δ > 0, ∀ᶠ H : ℝ in atTop,
      volume ({X | ε < f X} ∩ Icc 0 H) ≤ ENNReal.ofReal (δ * H) := by
    intro ε hε δ hδ
    apply eventually_volume_inter_Icc_le_of_window (γ := 0) ?_ hδ
    intro κ hκ
    have hhalf : Tendsto (fun V : ℝ => V / 2) atTop atTop :=
      tendsto_id.atTop_div_const (by norm_num)
    filter_upwards [hhalf.eventually (hmeasure ε κ hε hκ), eventually_ge_atTop (0 : ℝ)] with V hv hV
    have hsub : {X | ε < f X} ∩ Icc ((V - 0) / 2) V ⊆
        {X | X ∈ Icc (V / 2) (2 * (V / 2)) ∧ ¬ CentralAtHeight c ε X} := by
      rintro X ⟨hX1, hX2⟩
      have hX3 : X ∈ Icc (V / 2) (2 * (V / 2)) := by
        rw [sub_zero] at hX2
        rwa [show 2 * (V / 2) = V by ring]
      refine ⟨hX3, fun hP => ?_⟩
      have h1 : f X ≤ ε := csInf_le (hbdd X) ⟨hε.le, hP⟩
      have h2 : ε < f X := hX1
      exact absurd h2 (not_lt.mpr h1)
    refine (measure_mono hsub).trans (hv.trans (ENNReal.ofReal_le_ofReal ?_))
    nlinarith only [mul_nonneg hκ.le hV]
  obtain ⟨S, hSm, hD, hlim⟩ := exists_measurable_densityOne_tendsto_zero_of_density_zero
    (fun X _ => hf0 X) hlevel
  refine ⟨S, hSm, hD, fun κ hκ => ?_⟩
  filter_upwards [hlim.eventually (eventually_lt_nhds hκ)] with X hX
  obtain ⟨κ', hκ', hlt⟩ := exists_lt_of_csInf_lt (hnonempty X) hX
  exact hmono κ' κ X hlt.le hκ'.2

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

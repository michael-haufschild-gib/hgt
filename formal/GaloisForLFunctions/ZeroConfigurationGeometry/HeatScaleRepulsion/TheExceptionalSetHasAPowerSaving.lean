import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TheHalfGaussAtAPowerLevel
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TypicalHeightLocalNewman
import GaloisForLFunctions.RHTower.XiSliceTypicalOrderPowerSaving

/-!
# The exceptional set of the heat flow has a power saving, and the sharp depth law

For every `κ > 0` the heights `X ∈ [T, 2T]` with `Λ_X log X > κ` have measure at most `T^θ`, some `θ = θ(κ) < 1`
(`exists_volume_localNewman_scaled_gt_le_rpow`).

Outside crowds, the depth falls at least at the sharp rate `log X`: near a height of depth `d`, every zero of `H_τ` has
`|Im z| ≤ max(4η, d + 12η − τ log(X/2π))` (`eventually_abs_im_le_of_depth`), and `Λ_X log X ≲ d + 16η`
(`eventually_localNewmanConstant_le_of_depthWindow`).

Polylogarithmic typical heights only give density zero. A power saving needs the level `T^E`, where `ζ′/ζ` may be as
large as `θ log T` and the real saddle of the half-Gauss transform fails. The complex saddle (`PowerSaddle`) handles this
level, and the errors are uniformly small once `E ≍ η³` (`eventually_powerRange`). The atypical heights are power-saving
rare by the Ingham–Huxley count and the second moment (`exists_volume_not_zetaTypicalHeight_le_rpow`).
-/

set_option autoImplicit false

open Complex Set Metric Filter Topology MeasureTheory
open _root_.RHTower _root_.RHTower.DeBruijn
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- All the parameters and error bounds of one heat time and one height. -/
structure PowerRange (d η E T t X τ : ℝ) : Prop where
  typ : DepthTypical d η E T t
  hη : 0 < η
  hη8 : η ≤ 1 / 8
  hT : 8 ≤ T
  hE : 0 ≤ E
  hX : 1000 ≤ X
  hα : 8 ≤ (horizontalSlope X).re
  hαη : 8 ≤ η * (horizontalSlope X).re
  hXt : |X - t| ≤ η / 2
  hτ : 0 < τ
  hτ8 : τ ≤ 1 / 8
  hc1 : 16 * η ≤ 2 * τ * (horizontalSlope X).re
  hc2 : 2 * τ * (horizontalSlope X).re ≤ 1
  hB : powerSlopeError E η T ≤ η * (horizontalSlope X).re / 400
  he0 : 8 * τ * (4 * powerSlopeError E η T / η) + 2 * Real.exp (-(η ^ 2 / (8 * τ))) +
      powerTail (powerRatio E η T) η τ *
        (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 + 1) +
      powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re ≤ 1 / 5
  he1 : 32 * Real.sqrt τ * (4 * powerSlopeError E η T / η) +
      (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 + 10) / (2 * τ) *
        powerTail (powerRatio E η T) η τ *
        (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 + 1) +
      (1 + powerSlopeError E η T) *
        powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re ≤
      (horizontalSlope X).re / 2
  he2 : powerRatio E η T * Real.exp 1 *
        Real.exp (-(8 * η * (horizontalSlope X).re) + τ * (powerSlopeError E η T + 1 / 8) ^ 2) +
      powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re ≤ 1 / 2

namespace PowerRange

variable {d η E T t X τ : ℝ}

theorem saddle (h : PowerRange d η E T t X τ) {y : ℝ} (hy1 : -(1 / 2) ≤ y) (hy2 : y ≤ 1 / 2)
    (hyc : d + 12 * η ≤ y + 2 * τ * (horizontalSlope X).re) :
    ∃ (a δ : ℝ) (ℓ : ℂ),
      PowerSaddle xi d η (powerSlopeError E η T) (powerRatio E η T) t X τ y a δ ℓ ∧
      ℓ = lineLogDeriv xi X ((a : ℂ) + (δ : ℂ) * I) :=
  exists_powerSaddle (h.typ.lineModel h.hη (by linarith only [h.hη8]) h.hT h.hE) h.hη h.hη8 h.hX h.hα
    h.hαη h.hXt h.hτ h.hτ8 h.hc1 h.hc2 hy1 hy2 hyc h.hB

/-- The saddle has positive mass: `ξ` does not vanish at it. -/
theorem mass_pos (h : PowerRange d η E T t X τ) {y a δ : ℝ} {ℓ : ℂ}
    (hs : PowerSaddle xi d η (powerSlopeError E η T) (powerRatio E η T) t X τ y a δ ℓ) : 0 < SaddleData.mass (lineF xi X) τ a δ ℓ := by
  have hη := h.hη
  have hXt := abs_le.mp h.hXt
  have hδ := abs_le.mp hs.hδ
  have hreg : (a : ℂ) + (δ : ℂ) * I ∈ saddleRegion d η t X := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
      linarith only [hs.ha1, hη]
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
      linarith only [hs.ha2]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
      exact abs_le.mpr ⟨by linarith only [hXt.1, hδ.1, hη], by linarith only [hXt.2, hδ.2, hη]⟩
  have hne := hs.model.ne_zero h.hX (h.hXt.trans (by linarith only [hη])) hreg
  exact mul_pos (norm_pos_iff.mpr hne) (Real.exp_pos _)

/-- `|Q(y)|` stays comparable to the saddle mass. -/
theorem lower (h : PowerRange d η E T t X τ) {y a δ : ℝ} {ℓ : ℂ}
    (hs : PowerSaddle xi d η (powerSlopeError E η T) (powerRatio E η T) t X τ y a δ ℓ) :
    4 / 5 * SaddleData.mass (lineF xi X) τ a δ ℓ ≤ ‖halfGaussTransform τ (lineFn xi X) y‖ := by
  have hP := h.mass_pos hs
  have hb := (hs.norm_halfGauss_sub_main_le).trans (mul_le_mul_of_nonneg_left h.he0 hP.le)
  have hM := SaddleData.norm_main (lineF xi X) τ a δ ℓ
  have hn := norm_sub_norm_le (lineF xi X ((a : ℂ) + (δ : ℂ) * I) * Complex.exp (-((τ : ℂ) * ℓ ^ 2)))
    (halfGaussTransform τ (lineFn xi X) y)
  rw [norm_sub_rev, hM] at hn
  linarith only [hb, hn]

/-- **Slope positivity near the axis.** -/
theorem re_slope_pos (h : PowerRange d η E T t X τ) {y : ℝ} (hy1 : -(1 / 2) ≤ y) (hy2 : y ≤ 1 / 2)
    (hyc : d + 12 * η ≤ y + 2 * τ * (horizontalSlope X).re) :
    0 < ((∫ w in Ioi (0 : ℝ), (((w - y) / (2 * τ) * gaussDensity τ (w - y) : ℝ) : ℂ) * lineFn xi X w) *
      starRingEnd ℂ (halfGaussTransform τ (lineFn xi X) y)).re := by
  obtain ⟨a, δ, ℓ, hs, _⟩ := h.saddle hy1 hy2 hyc
  have hP := h.mass_pos hs
  have hq := h.lower hs
  have hR := (hs.norm_halfGauss_slope_sub_le).trans (mul_le_mul_of_nonneg_left h.he1 hP.le)
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = halfGaussTransform τ (lineFn xi X) y := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = ∫ w in Ioi (0 : ℝ),
      (((w - y) / (2 * τ) * gaussDensity τ (w - y) : ℝ) : ℂ) * lineFn xi X w := ⟨_, rfl⟩
  rw [← hQ, ← hD] at hR ⊢
  rw [← hQ] at hq
  obtain ⟨P, hPdef⟩ : ∃ P, P = SaddleData.mass (lineF xi X) τ a δ ℓ := ⟨_, rfl⟩
  rw [← hPdef] at hP hq hR
  obtain ⟨α, hαdef⟩ : ∃ α, α = (horizontalSlope X).re := ⟨_, rfl⟩
  have hα : 8 ≤ α := hαdef ▸ h.hα
  rw [← hαdef] at hR
  have hA := abs_le.mp hs.data.hA
  rw [← hαdef] at hA
  have hB : powerSlopeError E η T ≤ η * α / 400 := hαdef ▸ h.hB
  have hηα : η * α ≤ 1 / 8 * α := mul_le_mul_of_nonneg_right h.hη8 (by linarith only [hα])
  have hre : 99 / 100 * α ≤ ℓ.re := by linarith only [hA.1, hB, hηα, hα]
  have hsplit : D * starRingEnd ℂ Q = ℓ * (Q * starRingEnd ℂ Q) + (D - ℓ * Q) * starRingEnd ℂ Q := by
    ring
  rw [hsplit, Complex.mul_conj, Complex.add_re, Complex.re_mul_ofReal, Complex.normSq_eq_norm_sq]
  have hn : -(‖D - ℓ * Q‖ * ‖Q‖) ≤ ((D - ℓ * Q) * starRingEnd ℂ Q).re := by
    have h1 := Complex.abs_re_le_norm ((D - ℓ * Q) * starRingEnd ℂ Q)
    rw [norm_mul, Complex.norm_conj] at h1
    exact (abs_le.mp h1).1
  have hq0 : 0 < ‖Q‖ := by linarith only [hq, hP]
  have hmul : 99 / 100 * α * (4 / 5 * P) ≤ ℓ.re * ‖Q‖ :=
    mul_le_mul hre hq (by positivity) (by linarith only [hre, hα])
  have hgap : 0 < ℓ.re * ‖Q‖ - ‖D - ℓ * Q‖ := by
    have hαP : 0 < α * P := by positivity
    have hR' : ‖D - ℓ * Q‖ ≤ α * P / 2 := by linarith only [hR]
    nlinarith only [hmul, hR', hαP]
  have hprod := mul_pos hq0 hgap
  nlinarith only [hprod, hn]

/-- **The opposite half is smaller away from the axis.** -/
theorem norm_opposite_lt (h : PowerRange d η E T t X τ) {y : ℝ} (hy1 : 4 * η ≤ y) (hy2 : y ≤ 1 / 2)
    (hyc : d + 12 * η ≤ y + 2 * τ * (horizontalSlope X).re) :
    ‖halfGaussTransform τ (lineFn xi X) (-y)‖ < ‖halfGaussTransform τ (lineFn xi X) y‖ := by
  have hη := h.hη
  obtain ⟨a, δ, ℓ, hs, _⟩ := h.saddle (y := y) (by linarith only [hy1, hη]) hy2 hyc
  have hP := h.mass_pos hs
  have hq := h.lower hs
  have hb := hs.norm_halfGauss_opposite_le (by linarith only [hy1, hη])
  have hexp : Real.exp (-(2 * y * (horizontalSlope X).re) +
      τ * (powerSlopeError E η T + 1 / 8) ^ 2) ≤
      Real.exp (-(8 * η * (horizontalSlope X).re) + τ * (powerSlopeError E η T + 1 / 8) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hα := h.hα
    nlinarith only [mul_le_mul_of_nonneg_right hy1 (show 0 ≤ (horizontalSlope X).re by linarith only [hα])]
  have hK := (powerRatio_nonneg (E := E) (η := η) (T := T) (by linarith only [h.hT]))
  have he : powerRatio E η T * Real.exp 1 * Real.exp (-(2 * y * (horizontalSlope X).re) +
        τ * (powerSlopeError E η T + 1 / 8) ^ 2) +
      powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re ≤ 1 / 2 :=
    le_trans (add_le_add (mul_le_mul_of_nonneg_left hexp
      (mul_nonneg hK (Real.exp_pos _).le)) le_rfl) h.he2
  have hb2 := hb.trans (mul_le_mul_of_nonneg_left he hP.le)
  nlinarith only [hb2, hq, hP]

/-- **Reality at this heat time, once the saddle has cleared the depth.** -/
theorem riemannHeat_ne_zero (h : PowerRange d η E T t X τ)
    (hc : d + 16 * η ≤ 2 * τ * (horizontalSlope X).re) {y : ℝ} (hy : y ≠ 0) (hy2 : |y| ≤ 1 / 2) :
    riemannHeat τ ((X : ℂ) + I * y) ≠ 0 := by
  have hη := h.hη
  have hη8 := h.hη8
  have hτ := h.hτ
  have hlt : ∀ y : ℝ, 0 < y → y ≤ 1 / 2 →
      ‖halfGaussTransform τ (lineFn xi X) (-y)‖ < ‖halfGaussTransform τ (lineFn xi X) y‖ := by
    intro y hy0 hy2
    rcases le_or_gt y (4 * η) with hnear | hfar
    · exact norm_lt_norm_of_re_mul_conj_pos (b := 4 * η)
        (fun v _ => hasDerivAt_halfGaussTransform hτ (continuous_xiLine X)
          (integrable_exp_mul_norm_xiLine hτ X) v)
        (fun v hv => h.re_slope_pos (by linarith only [hv.1, hη8]) (by linarith only [hv.2, hη8])
          (by linarith only [hv.1, hc])) hy0 hnear
    · exact h.norm_opposite_lt hfar.le hy2 (by linarith only [hy0, hc, hη])
  rw [riemannHeat_eq_halfGaussAverage hτ X y]
  apply add_conj_ne_zero_of_norm_ne
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · have hn := hlt (-y) (by linarith only [hneg]) (by linarith only [(abs_le.mp hy2).1])
    rw [neg_neg] at hn
    exact ne_of_gt hn
  · exact ne_of_lt (hlt y hpos (abs_le.mp hy2).2)

/-- **The depth of the flow at this heat time.** No zero lies at depth `|y| ≥ 4η` with `|y| + 2τα ≥ d + 12η`. -/
theorem riemannHeat_ne_zero_of_deep (h : PowerRange d η E T t X τ) {y : ℝ} (hy1 : 4 * η ≤ |y|)
    (hy2 : |y| ≤ 1 / 2) (hyc : d + 12 * η ≤ |y| + 2 * τ * (horizontalSlope X).re) :
    riemannHeat τ ((X : ℂ) + I * y) ≠ 0 := by
  have hτ := h.hτ
  rw [riemannHeat_eq_halfGaussAverage hτ X y]
  apply add_conj_ne_zero_of_norm_ne
  have hη := h.hη
  rcases le_or_gt 0 y with hpos | hneg
  · rw [abs_of_nonneg hpos] at hy1 hy2 hyc
    exact ne_of_lt (h.norm_opposite_lt hy1 hy2 hyc)
  · rw [abs_of_neg hneg] at hy1 hy2 hyc
    have hn := h.norm_opposite_lt hy1 hy2 hyc
    rw [neg_neg] at hn
    exact ne_of_gt hn

end PowerRange

/-! ## The errors are small at level `η³` -/

/-- The level of a typical height at depth `η`. -/
def powerLevel (η : ℝ) : ℝ := η ^ 3 / 40000

/-- The additive constant of the anchor exponent. -/
def powerC₁ (η : ℝ) : ℝ := 108 / η + 49

/-- The additive constant of the slope error. -/
def powerC₂ (η : ℝ) : ℝ := 216 / η ^ 2 + 6

/-- The constant of the far term. -/
def powerC₃ (η : ℝ) : ℝ :=
  4 * Real.exp 1 * (1 / (2 * (8 * η)) + 2) + 1 / (8 * η)

theorem powerSlopeError_le {η T α : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hL : Real.log T ≤ 2 * α + 15) :
    powerSlopeError (powerLevel η) η T ≤ 3 * η / 2500 * α + powerC₂ η := by
  have hid : 24 * (η ^ 3 / 40000 * Real.log T + 9) / η ^ 2 =
      3 * η / 5000 * Real.log T + 216 / η ^ 2 := by
    field_simp
    ring
  have hm := mul_le_mul_of_nonneg_left hL (show 0 ≤ 3 * η / 5000 by positivity)
  unfold powerSlopeError powerLevel powerC₂
  rw [hid]
  nlinarith only [hm, hη8]

theorem powerRatio_le {η T α : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hT : 8 ≤ T) (hα : 0 ≤ α)
    (hL : Real.log T ≤ 2 * α + 15) :
    powerRatio (powerLevel η) η T ≤ Real.exp (η ^ 2 / 1000 * α + powerC₁ η) := by
  have hT0 : 0 < T := by linarith only [hT]
  have hlog := Real.log_nonneg (show 1 ≤ T by linarith only [hT])
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log T := ⟨_, rfl⟩
  rw [← hLdef] at hlog hL
  obtain ⟨u, hu⟩ : ∃ u, u = η ^ 3 / 40000 * L := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hrpow : T ^ powerLevel η = Real.exp u := by
    rw [Real.rpow_def_of_pos hT0, hu, powerLevel, ← hLdef, mul_comm]
  have h1 : 1 ≤ Real.exp u := Real.one_le_exp hu0
  have h9 : (9 : ℝ) ≤ Real.exp 8 := by
    have := Real.add_one_le_exp (8 : ℝ)
    linarith only [this]
  have hdiv : 12 * (powerLevel η * Real.log T + 9) / η = 12 * (u / η) + 108 / η := by
    rw [powerLevel, ← hLdef, ← hu]
    field_simp
    ring
  have huη : u ≤ u / η := by
    rw [le_div_iff₀ hη]
    nlinarith only [hu0, hη8]
  have hval : u / η = η ^ 2 / 40000 * L := by
    rw [hu]
    field_simp
  have hsum : 8 + u + (12 * (u / η) + 108 / η + 40) ≤ η ^ 2 / 1000 * α + powerC₁ η := by
    have hb : u / η ≤ η ^ 2 / 40000 * (2 * α + 15) :=
      hval ▸ mul_le_mul_of_nonneg_left hL (by positivity)
    have hηsq : η ^ 2 ≤ 1 / 64 := by nlinarith only [hη, hη8]
    have hαη : 0 ≤ η ^ 2 * α := by positivity
    unfold powerC₁
    nlinarith only [hb, huη, hηsq, hαη]
  unfold powerRatio
  rw [hrpow, hdiv]
  have hup : 3 * (Real.exp u + 2) ≤ Real.exp 8 * Real.exp u := by nlinarith only [h1, h9]
  calc
    _ ≤ (Real.exp 8 * Real.exp u) * Real.exp (12 * (u / η) + 108 / η + 40) :=
      mul_le_mul_of_nonneg_right hup (Real.exp_pos _).le
    _ = Real.exp (8 + u + (12 * (u / η) + 108 / η + 40)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr hsum

/-- `(4πτ)^{−½}` is at most polynomial in the slope. -/
theorem rpow_gauss_le {η τ α : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hτ : 0 < τ) (hα : 1 ≤ α)
    (hc1 : 16 * η ≤ 2 * τ * α) : (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) ≤ 2 * α / η := by
  have hx : 0 < 4 * Real.pi * τ := by positivity
  have hmain : (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) ≤ 1 + 1 / (4 * Real.pi * τ) := by
    rcases le_total 1 (4 * Real.pi * τ) with hle | hle
    · have h1 := Real.rpow_le_one_of_one_le_of_nonpos hle (by norm_num : -(1 / 2 : ℝ) ≤ 0)
      have h2 : 0 ≤ 1 / (4 * Real.pi * τ) := by positivity
      linarith only [h1, h2]
    · have h1 := Real.rpow_le_rpow_of_exponent_ge hx hle (by norm_num : (-1 : ℝ) ≤ -(1 / 2))
      rw [Real.rpow_neg_one, ← one_div] at h1
      linarith only [h1]
  have hinv : 1 / (4 * Real.pi * τ) ≤ α / η := by
    rw [div_le_div_iff₀ hx hη]
    have hπ := Real.pi_gt_three
    have hτα : 8 * η ≤ τ * α := by linarith only [hc1]
    have hp : 0 < τ * α := by nlinarith only [hτα, hη]
    nlinarith only [hτα, hη8, hη, hp, mul_pos hp Real.pi_pos, hπ,
      mul_le_mul_of_nonneg_right hπ.le hp.le]
  have hη1 : 1 ≤ α / η := by
    rw [le_div_iff₀ hη]
    linarith only [hη8, hα]
  have he : 2 * α / η = α / η + α / η := by ring
  rw [he]
  linarith only [hmain, hinv, hη1]

/-- The tail of the saddle against the slope. -/
theorem powerTail_le {η τ α K : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hτ : 0 < τ) (hα : 1 ≤ α)
    (hc1 : 16 * η ≤ 2 * τ * α) (hc2 : 2 * τ * α ≤ 1) (_hK0 : 0 ≤ K)
    (hK : K ≤ Real.exp (η ^ 2 / 1000 * α + powerC₁ η)) :
    powerTail K η τ ≤ 2 * α / η * Real.exp (powerC₁ η) * Real.exp (-(η ^ 2 / 8 * α)) := by
  have hA := rpow_gauss_le hη hη8 hτ hα hc1
  have hexp : Real.exp (-(η ^ 2 / (8 * τ))) ≤ Real.exp (-(η ^ 2 / 4 * α)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have hsq : 0 ≤ η ^ 2 := sq_nonneg η
    nlinarith only [mul_le_mul_of_nonneg_left hc2 hsq]
  unfold powerTail
  have hA0 : 0 ≤ (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) := by positivity
  calc
    _ ≤ Real.exp (η ^ 2 / 1000 * α + powerC₁ η) *
        (2 * α / η * Real.exp (-(η ^ 2 / 4 * α))) := by gcongr
    _ = 2 * α / η * (Real.exp (powerC₁ η) *
        Real.exp (η ^ 2 / 1000 * α + -(η ^ 2 / 4 * α))) := by
      rw [Real.exp_add (η ^ 2 / 1000 * α), Real.exp_add]
      ring
    _ ≤ 2 * α / η * (Real.exp (powerC₁ η) * Real.exp (-(η ^ 2 / 8 * α))) := by
      have hαp : 0 ≤ η ^ 2 * α := by positivity
      gcongr
      nlinarith only [hαp]
    _ = _ := by ring

/-- The far term, multiplied by the slope error, is doubly small. -/
theorem powerFar_le {η τ α K B : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hτ : 0 < τ) (hτ8 : τ ≤ 1 / 8)
    (hα : 8 ≤ α) (hc1 : 16 * η ≤ 2 * τ * α) (hc2 : 2 * τ * α ≤ 1) (hK0 : 0 ≤ K)
    (hK : K ≤ Real.exp (η ^ 2 / 1000 * α + powerC₁ η)) (hB0 : 0 ≤ B) (hB : B ≤ η * α / 400) :
    (1 + B) * powerFar K B τ α ≤ powerC₃ η * Real.exp (2 * powerC₁ η) * (α ^ 2 * Real.exp (-α)) ∧
      powerFar K B τ α ≤ powerC₃ η * Real.exp (2 * powerC₁ η) * (α ^ 2 * Real.exp (-α)) := by
  have hα0 : 0 < α := by linarith only [hα]
  have hC₃ : 0 ≤ powerC₃ η := by
    unfold powerC₃
    positivity
  have hkkl : kklRC τ α ≤ powerC₃ η * α * Real.exp (-α ^ 2) := by
    have h := kklRC_add_kklRB_le_small_heat (d := 8 * η) (by positivity) hτ hτ8
      (by linarith only [hc1]) hα
    have hb := kklRB_nonneg (α := α) hτ
    unfold powerC₃
    linarith only [h, hb]
  have hkkl0 := kklRC_nonneg hτ hα0.le
  have hηα : η * α ≤ 1 / 8 * α := mul_le_mul_of_nonneg_right hη8 hα0.le
  have hτB : τ * B ^ 2 ≤ α := by
    have h2τB : 2 * τ * B ≤ η / 400 := by
      have h1 := mul_le_mul_of_nonneg_left hB (show 0 ≤ 2 * τ by positivity)
      nlinarith only [h1, mul_le_mul_of_nonneg_left hc2 hη.le]
    have hBα : B ≤ α := by linarith only [hB, hηα, hα]
    have h3 := mul_le_mul h2τB hBα hB0 (by positivity)
    nlinarith only [h3, hη8, hα0, hη]
  have hK2 : K ^ 2 ≤ Real.exp (2 * (η ^ 2 / 1000 * α + powerC₁ η)) := by
    have h := pow_le_pow_left₀ hK0 hK 2
    rwa [← Real.exp_nat_mul, Nat.cast_ofNat] at h
  have hexp : Real.exp (2 * (η ^ 2 / 1000 * α + powerC₁ η)) * Real.exp (τ * B ^ 2) *
      Real.exp (-α ^ 2) ≤ Real.exp (2 * powerC₁ η) * Real.exp (-α) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hηsq : η ^ 2 ≤ 1 / 64 := by nlinarith only [hη, hη8]
    have hsq : η ^ 2 * α ≤ 1 / 64 * α := mul_le_mul_of_nonneg_right hηsq hα0.le
    nlinarith only [hsq, hτB, hα]
  have hfar : powerFar K B τ α ≤ powerC₃ η * Real.exp (2 * powerC₁ η) * (α * Real.exp (-α)) := by
    unfold powerFar
    calc
      _ ≤ Real.exp (2 * (η ^ 2 / 1000 * α + powerC₁ η)) * Real.exp (τ * B ^ 2) *
          (powerC₃ η * α * Real.exp (-α ^ 2)) := by gcongr
      _ = powerC₃ η * α * (Real.exp (2 * (η ^ 2 / 1000 * α + powerC₁ η)) * Real.exp (τ * B ^ 2) *
          Real.exp (-α ^ 2)) := by ring
      _ ≤ powerC₃ η * α * (Real.exp (2 * powerC₁ η) * Real.exp (-α)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  have hfar0 : 0 ≤ powerFar K B τ α := by
    unfold powerFar
    positivity
  have hRHS : 0 ≤ powerC₃ η * Real.exp (2 * powerC₁ η) * (α * Real.exp (-α)) := by positivity
  have h1B : 1 + B ≤ α := by linarith only [hB, hηα, hα]
  have hstep : (1 + B) * powerFar K B τ α ≤
      powerC₃ η * Real.exp (2 * powerC₁ η) * (α ^ 2 * Real.exp (-α)) := by
    calc
      _ ≤ α * (powerC₃ η * Real.exp (2 * powerC₁ η) * (α * Real.exp (-α))) :=
        mul_le_mul h1B hfar hfar0 hα0.le
      _ = _ := by ring
  refine ⟨hstep, ?_⟩
  exact le_trans (le_mul_of_one_le_left hfar0 (by linarith only [hB0])) hstep

/-- Powers against a negative exponential. -/
theorem eventually_const_mul_pow_mul_exp_lt (c : ℝ) (n : ℕ) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ α : ℝ in atTop, c * (α ^ n * Real.exp (-(b * α))) < ε := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) b hb).const_mul c
  rw [mul_zero] at h
  filter_upwards [h.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)] with α hα hα0
  rwa [Real.rpow_natCast, neg_mul] at hα

/-- **Everything is small for large slope.** -/
theorem eventually_power_conditions {η : ℝ} (hη : 0 < η) :
    ∀ᶠ α : ℝ in atTop, 8 ≤ α ∧ 8 ≤ η * α ∧ 3 * η / 2500 * α + powerC₂ η ≤ η * α / 400 ∧
      6 / η * Real.exp (powerC₁ η) * (α ^ 3 * Real.exp (-(η ^ 2 / 8 * α))) < 1 / 50 ∧
      9 / (2 * η ^ 2) * Real.exp (powerC₁ η) * (α ^ 6 * Real.exp (-(η ^ 2 / 8 * α))) < 1 / 50 ∧
      powerC₃ η * Real.exp (2 * powerC₁ η) * (α ^ 2 * Real.exp (-(1 * α))) < 1 / 50 ∧
      Real.exp (powerC₁ η + 1) * (α ^ 0 * Real.exp (-(6 * η * α))) < 1 / 50 ∧
      2 * (α ^ 0 * Real.exp (-(η ^ 2 / 8 * α))) < 1 / 50 := by
  have hb : 0 < η ^ 2 / 8 := by positivity
  filter_upwards [eventually_ge_atTop (8 : ℝ), eventually_ge_atTop (8 / η),
    eventually_ge_atTop (powerC₂ η / (13 * η / 10000)),
    eventually_const_mul_pow_mul_exp_lt (6 / η * Real.exp (powerC₁ η)) 3 hb
      (by norm_num : (0 : ℝ) < 1 / 50),
    eventually_const_mul_pow_mul_exp_lt (9 / (2 * η ^ 2) * Real.exp (powerC₁ η)) 6 hb
      (by norm_num : (0 : ℝ) < 1 / 50),
    eventually_const_mul_pow_mul_exp_lt (powerC₃ η * Real.exp (2 * powerC₁ η)) 2
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1 / 50),
    eventually_const_mul_pow_mul_exp_lt (Real.exp (powerC₁ η + 1)) 0
      (by positivity : 0 < 6 * η) (by norm_num : (0 : ℝ) < 1 / 50),
    eventually_const_mul_pow_mul_exp_lt 2 0 hb (by norm_num : (0 : ℝ) < 1 / 50)]
    with α h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨h1, ?_, ?_, h4, h5, h6, h7, h8⟩
  · rw [div_le_iff₀ hη] at h2
    linarith only [h2]
  · rw [div_le_iff₀ (by positivity)] at h3
    linarith only [h3]

/-- **The range of the complex saddle.** Above a uniform dyadic height, at every height near a typical height of
level `η³/40000`, the half-Gauss errors are uniformly small for `16η ≤ 2τα ≤ 1`. -/
theorem eventually_powerRange {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∀ᶠ T : ℝ in atTop, ∀ d t : ℝ, DepthTypical d η (powerLevel η) T t →
      ∀ X : ℝ, |X - t| ≤ η / 2 → ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 8 →
      16 * η ≤ 2 * τ * (horizontalSlope X).re → 2 * τ * (horizontalSlope X).re ≤ 1 →
      PowerRange d η (powerLevel η) T t X τ := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp (eventually_power_conditions hη)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (tendsto_horizontalSlope_re.eventually_ge_atTop A)
  filter_upwards [eventually_ge_atTop (max X₀ 1000 + 2), eventually_ge_atTop (8 : ℝ)] with T hTbig hT
  intro d t htyp X hXt τ hτ hτ8 hc1 hc2
  have hXt' := abs_le.mp hXt
  have hTX : T - 1 ≤ X := by linarith only [htyp.mem.1, hXt'.1, hη8]
  have hXm : max X₀ 1000 ≤ X := by linarith only [hTbig, hTX]
  have hX : 1000 ≤ X := (le_max_right _ _).trans hXm
  have hX0 : 0 < X := by linarith only [hX]
  obtain ⟨α, hαdef⟩ : ∃ α, α = (horizontalSlope X).re := ⟨_, rfl⟩
  rw [← hαdef] at hc1 hc2
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hA α
    (hαdef ▸ hX₀ X ((le_max_left _ _).trans hXm))
  have hα0 : 0 < α := by linarith only [h1]
  have hL : Real.log T ≤ 2 * α + 15 := by
    have hT0 : 0 < T := by linarith only [hT]
    have hmono := Real.log_le_log hT0 (show T ≤ 2 * X by linarith only [hTX, hX])
    rw [Real.log_mul (by norm_num) hX0.ne'] at hmono
    have hh := height_eq hX0
    rw [← hαdef] at hh
    have hlogX : Real.log X = Real.log (2 * Real.pi) + 2 * α := by
      rw [hh, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith only [this]
    have hlogπ : Real.log (2 * Real.pi) ≤ 7 :=
      (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith only [Real.pi_lt_four])
    linarith only [hmono, hlogX, hlog2, hlogπ]
  have hBle := powerSlopeError_le hη hη8 hL
  have hB : powerSlopeError (powerLevel η) η T ≤ η * α / 400 := by linarith only [hBle, h3]
  have hE : 0 ≤ powerLevel η := by
    unfold powerLevel
    positivity
  have hBpos := powerSlopeError_pos (η := η) hE (by linarith only [hT] : 1 ≤ T)
  have hK0 := powerRatio_nonneg (E := powerLevel η) (η := η) (T := T) (by linarith only [hT])
  have hKle := powerRatio_le hη hη8 hT hα0.le hL
  obtain ⟨B, hBdef⟩ : ∃ B, B = powerSlopeError (powerLevel η) η T := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, K = powerRatio (powerLevel η) η T := ⟨_, rfl⟩
  rw [← hBdef] at hB hBpos
  rw [← hKdef] at hK0 hKle
  have hα1 : 1 ≤ α := by linarith only [h1]
  have htail := powerTail_le hη hη8 hτ hα1 hc1 hc2 hK0 hKle
  obtain ⟨hfar1, hfar2⟩ := powerFar_le hη hη8 hτ hτ8 h1 hc1 hc2 hK0 hKle hBpos.le hB
  have h6' : powerC₃ η * Real.exp (2 * powerC₁ η) * (α ^ 2 * Real.exp (-α)) < 1 / 50 := by
    rw [one_mul] at h6
    exact h6
  obtain ⟨W, hW⟩ : ∃ W, W = 2 * τ * α + α ^ 2 := ⟨_, rfl⟩
  have hWle : W + 1 ≤ 3 * α ^ 2 := by
    rw [hW]
    nlinarith only [hc2, hα1]
  have hW0 : 0 ≤ W + 1 := by
    rw [hW]
    have : 0 ≤ 2 * τ * α := by positivity
    nlinarith only [this, sq_nonneg α]
  have hpow0 : 0 ≤ Real.exp (powerC₁ η) := (Real.exp_pos _).le
  have hexpb : 0 < Real.exp (-(η ^ 2 / 8 * α)) := Real.exp_pos _
  have hτ0 := hτ
  have hT0le : 0 ≤ powerTail K η τ := by
    unfold powerTail
    positivity
  -- The tail against the Gaussian range.
  have hT1 : powerTail K η τ * (W + 1) < 1 / 50 := by
    have hm := mul_le_mul htail hWle hW0 (by positivity)
    have he : 2 * α / η * Real.exp (powerC₁ η) * Real.exp (-(η ^ 2 / 8 * α)) * (3 * α ^ 2) =
        6 / η * Real.exp (powerC₁ η) * (α ^ 3 * Real.exp (-(η ^ 2 / 8 * α))) := by
      ring
    rw [he] at hm
    exact hm.trans_lt h4
  -- The weighted tail against the Gaussian range.
  have hΩ : (W + 10) / (2 * τ) ≤ 3 / (4 * η) * α ^ 3 := by
    rw [div_le_iff₀ (by positivity)]
    have hWt : W + 10 ≤ 12 * α ^ 2 := by
      rw [hW]
      nlinarith only [hc2, hα1, h1]
    have hsq0 : 0 ≤ α ^ 2 := sq_nonneg α
    have hαw : (3 / (4 * η) * α ^ 3) * (2 * τ) = 3 / (4 * η) * α ^ 2 * (2 * τ * α) := by ring
    rw [hαw]
    have hc : 12 * α ^ 2 = 3 / (4 * η) * α ^ 2 * (16 * η) := by
      field_simp
      ring
    calc
      _ ≤ 12 * α ^ 2 := hWt
      _ = 3 / (4 * η) * α ^ 2 * (16 * η) := hc
      _ ≤ _ := mul_le_mul_of_nonneg_left hc1 (by positivity)
  have hΩ0 : 0 ≤ (W + 10) / (2 * τ) := by
    have : 0 ≤ W + 10 := by linarith only [hW0]
    positivity
  have hT2 : (W + 10) / (2 * τ) * powerTail K η τ * (W + 1) < 1 / 50 := by
    have hm1 := mul_le_mul hΩ htail hT0le (by positivity)
    have hm2 := mul_le_mul hm1 hWle hW0 (by positivity)
    have he : 3 / (4 * η) * α ^ 3 * (2 * α / η * Real.exp (powerC₁ η) *
        Real.exp (-(η ^ 2 / 8 * α))) * (3 * α ^ 2) =
        9 / (2 * η ^ 2) * Real.exp (powerC₁ η) * (α ^ 6 * Real.exp (-(η ^ 2 / 8 * α))) := by
      field_simp
      ring
    rw [he] at hm2
    exact hm2.trans_lt h5
  -- The window of the saddle.
  have hηα : η * α ≤ 1 / 8 * α := mul_le_mul_of_nonneg_right hη8 hα0.le
  have h2τB : 2 * τ * B ≤ η / 400 := by
    have hh := mul_le_mul_of_nonneg_left hB (show 0 ≤ 2 * τ by positivity)
    nlinarith only [hh, mul_le_mul_of_nonneg_left hc2 hη.le]
  have hwin : 8 * τ * (4 * B / η) ≤ 1 / 25 := by
    have he : 8 * τ * (4 * B / η) = 16 * (2 * τ * B) / η := by ring
    rw [he, div_le_iff₀ hη]
    linarith only [h2τB, hη]
  have hgauss : 2 * Real.exp (-(η ^ 2 / (8 * τ))) < 1 / 50 := by
    have hexp : Real.exp (-(η ^ 2 / (8 * τ))) ≤ Real.exp (-(η ^ 2 / 8 * α)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
      have hsq : 0 ≤ η ^ 2 := sq_nonneg η
      nlinarith only [mul_le_mul_of_nonneg_left hc2 hsq, mul_nonneg hsq hτ.le,
        mul_nonneg (mul_nonneg hsq hτ.le) hα0.le]
    simp only [pow_zero, one_mul] at h8
    linarith only [hexp, h8]
  have hsqrt : Real.sqrt τ ≤ 1 := by
    have hh := Real.sqrt_le_sqrt (show τ ≤ 1 by linarith only [hτ8])
    rwa [Real.sqrt_one] at hh
  have hslope : 32 * Real.sqrt τ * (4 * B / η) ≤ 8 / 25 * α := by
    have hbd : 4 * B / η ≤ α / 100 := by
      rw [div_le_iff₀ hη]
      nlinarith only [hB]
    have hq0 : 0 ≤ 4 * B / η := by positivity
    have hs0 := Real.sqrt_nonneg τ
    nlinarith only [mul_le_mul hsqrt hbd hq0 (by norm_num : (0 : ℝ) ≤ 1)]
  -- The reflection exponent.
  have hrefl : K * Real.exp 1 * Real.exp (-(8 * η * α) + τ * (B + 1 / 8) ^ 2) < 1 / 50 := by
    have hB5 : 5 ≤ B := by
      rw [hBdef]
      unfold powerSlopeError
      have hlog := Real.log_nonneg (by linarith only [hT] : (1 : ℝ) ≤ T)
      have hq : 0 ≤ 24 * (powerLevel η * Real.log T + 9) / η ^ 2 := by positivity
      linarith only [hq]
    have hτB2 : τ * (B + 1 / 8) ^ 2 ≤ η * α := by
      have hBα : B ≤ η * α / 400 := hB
      have hle : B + 1 / 8 ≤ 2 * B := by linarith only [hB5]
      have hsq := pow_le_pow_left₀ (by linarith only [hB5] : 0 ≤ B + 1 / 8) hle 2
      have hm := mul_le_mul h2τB hBα hBpos.le (by positivity)
      have hηα0 : 0 < η * α := by positivity
      nlinarith only [mul_le_mul_of_nonneg_left hsq hτ.le, hm, hη8, hηα0, hη]
    have hηsq : η ^ 2 / 1000 * α ≤ η * α := by
      have hηηα := mul_le_mul_of_nonneg_right hη8 (show 0 ≤ η * α by positivity)
      nlinarith only [hηηα, mul_pos hη hα0]
    have hKb : K ≤ Real.exp (η * α + powerC₁ η) :=
      hKle.trans (Real.exp_le_exp.mpr (by linarith only [hηsq]))
    have hexp : Real.exp (η * α + powerC₁ η) * Real.exp 1 *
        Real.exp (-(8 * η * α) + τ * (B + 1 / 8) ^ 2) ≤
        Real.exp (powerC₁ η + 1) * Real.exp (-(6 * η * α)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith only [hτB2]
    simp only [pow_zero, one_mul] at h7
    calc
      _ ≤ Real.exp (η * α + powerC₁ η) * Real.exp 1 *
          Real.exp (-(8 * η * α) + τ * (B + 1 / 8) ^ 2) := by gcongr
      _ ≤ _ := hexp
      _ < _ := h7
  have hfar1' := hfar1.trans_lt h6'
  have hfar2' := hfar2.trans_lt h6'
  have hα8 : (1 : ℝ) ≤ α / 8 := by linarith only [h1]
  subst hBdef hKdef hαdef
  refine ⟨htyp, hη, hη8, hT, hE, hX, h1, h2, hXt, hτ, hτ8, hc1, hc2, hB, ?_, ?_, ?_⟩
  · rw [hW] at hT1
    linarith only [hwin, hgauss, hT1, hfar2']
  · rw [hW] at hT2
    linarith only [hslope, hT2, hfar1', hα8]
  · linarith only [hrefl, hfar2']

/-- **Reality at every later heat time, near a height of depth `d`.** Once `2τα ≥ d + 16η`, every zero over the height is
real. -/
theorem eventually_riemannHeat_zeros_real_of_depth {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∀ᶠ T : ℝ in atTop, ∀ d t : ℝ, DepthTypical d η (powerLevel η) T t →
      ∀ X : ℝ, |X - t| ≤ η / 2 → ∀ τ : ℝ, 0 < τ →
      d + 16 * η ≤ 2 * τ * (horizontalSlope X).re →
      ∀ z : ℂ, z.re = X → riemannHeat τ z = 0 → z.im = 0 := by
  obtain ⟨X₀, hglobal⟩ := riemannHeat_zeros_real_twoThirds (ε := 1 / 3) (by norm_num)
  filter_upwards [eventually_powerRange hη hη8, eventually_ge_atTop (|X₀| + 202)] with T hrange hT
  intro d t h X hXt τ hτ hprod z hre hz
  have hXt' := (abs_le.mp hXt).1
  have hXbig : |X₀| + 200 ≤ X := by linarith only [hT, h.mem.1, hXt', hη8]
  have hX : 0 < X := by linarith only [hXbig, abs_nonneg X₀]
  have hzabs : |z.re| = X := by rw [hre, abs_of_pos hX]
  have hc1 : 16 * η ≤ 2 * τ * (horizontalSlope X).re := by linarith only [hprod, h.hd]
  rcases le_or_gt (1 / 8) τ with h8 | h8
  · exact ((mem_realRootedTimes_iff hτ.le).mpr (newmanConstant_lt_eighth.le.trans h8)).2 z hz
  by_cases hc2 : 2 * τ * (horizontalSlope X).re ≤ 1
  · by_contra him
    have hne := (hrange d t h X hXt τ hτ h8.le hc1 hc2).riemannHeat_ne_zero hprod him
      (abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg hτ.le hz)
    have hrepr : (X : ℂ) + I * z.im = z := by
      apply Complex.ext <;> simp [← hre]
    exact hne (by rw [hrepr]; exact hz)
  · apply hglobal τ hτ h8.le z hz
    · rw [hzabs]
      linarith only [hXbig, le_abs_self X₀]
    · have hexp : (2 / 3 + 1 / 3 : ℝ) / τ ≤ 2 * (horizontalSlope X).re := by
        rw [div_le_iff₀ hτ]
        nlinarith only [not_le.mp hc2]
      calc
        _ ≤ 2 * Real.pi * Real.exp (2 * (horizontalSlope X).re) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
        _ = X := (height_eq hX).symm
        _ = |z.re| := hzabs.symm

/-- **The linear depth law, lower side, with the sharp constant.** Near a height of depth `d`, every zero of `H_τ` has
`|Im z| ≤ max(4η, d + 12η − τ log(X/2π))`: outside crowds, depth falls at least at rate `log X`. -/
theorem eventually_abs_im_le_of_depth {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∀ᶠ T : ℝ in atTop, ∀ d t : ℝ, DepthTypical d η (powerLevel η) T t →
      ∀ X : ℝ, |X - t| ≤ η / 2 → ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 8 →
      16 * η ≤ τ * Real.log (X / (2 * Real.pi)) → τ * Real.log (X / (2 * Real.pi)) ≤ 1 →
      ∀ z : ℂ, z.re = X → riemannHeat τ z = 0 →
        |z.im| ≤ max (4 * η) (d + 12 * η - τ * Real.log (X / (2 * Real.pi))) := by
  filter_upwards [eventually_powerRange hη hη8] with T hrange
  intro d t h X hXt τ hτ hτ8 hc1 hc2 z hre hz
  have hslope : 2 * τ * (horizontalSlope X).re = τ * Real.log (X / (2 * Real.pi)) := by
    rw [horizontalSlope_re]
    ring
  rw [← hslope] at hc1 hc2 ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := max_lt_iff.mp hcon
  have hhalf := abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg hτ.le hz
  have hne := (hrange d t h X hXt τ hτ hτ8 hc1 hc2).riemannHeat_ne_zero_of_deep (y := z.im) h1.le hhalf
    (by linarith only [h2])
  have hrepr : (X : ℂ) + I * z.im = z := by
    apply Complex.ext <;> simp [← hre]
  exact hne (by rw [hrepr]; exact hz)

/-- Every height of the unit window is near a height of depth `d`. -/
def depthWindow (d η T X : ℝ) : Prop :=
  ∀ Y : ℝ, |Y - X| ≤ 1 → ∃ t : ℝ, DepthTypical d η (powerLevel η) T t ∧ |Y - t| ≤ η / 2

/-- **The local constant at depth `d`.** On a unit window of depth `d`, outside crowds,
`Λ_X log((X−1)/2π) ≤ d + 16η`. -/
theorem eventually_localNewmanConstant_le_of_depthWindow {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∀ᶠ T : ℝ in atTop, ∀ d X : ℝ, X ∈ Icc T (2 * T) → depthWindow d η T X → 0 ≤ d →
      localNewmanConstant X ≤ (d + 16 * η) / Real.log ((X - 1) / (2 * Real.pi)) := by
  filter_upwards [eventually_riemannHeat_zeros_real_of_depth hη hη8,
    eventually_ge_atTop (2 * Real.pi * Real.exp 1 + 2)] with T hfuture hT
  intro d X hXT hwindow hd
  let L := Real.log ((X - 1) / (2 * Real.pi))
  let s := (d + 16 * η) / L
  have hπ : 0 < 2 * Real.pi := by positivity
  have hratio : Real.exp 1 ≤ (X - 1) / (2 * Real.pi) := by
    rw [le_div_iff₀ hπ]
    linarith only [hT, hXT.1]
  have hratio0 : 0 < (X - 1) / (2 * Real.pi) := (Real.exp_pos 1).trans_le hratio
  have hL1 : 1 ≤ L := by
    have hh := Real.log_le_log (Real.exp_pos 1) hratio
    simpa only [Real.log_exp] using hh
  have hL : 0 < L := by linarith only [hL1]
  have hs : 0 < s := by dsimp only [s]; positivity
  have hsL : s * L = d + 16 * η := by dsimp only [s]; rw [div_mul_cancel₀ _ hL.ne']
  apply localNewmanConstant_le
  refine ⟨hs.le, ?_⟩
  intro τ hsτ z hz hzx
  obtain ⟨t, htyp, hnear⟩ := hwindow z.re hzx
  have hY : X - 1 ≤ z.re := by linarith only [(abs_le.mp hzx).1]
  have hα : L ≤ 2 * (horizontalSlope z.re).re := by
    have hh := Real.log_le_log hratio0 (div_le_div_of_nonneg_right hY hπ.le)
    rw [horizontalSlope_re]
    dsimp only [L] at hh ⊢
    linarith only [hh]
  have hα0 : 0 ≤ (horizontalSlope z.re).re := by linarith only [hα, hL1]
  have hstart : d + 16 * η ≤ 2 * s * (horizontalSlope z.re).re := by
    have hh := mul_le_mul_of_nonneg_left hα hs.le
    nlinarith only [hh, hsL]
  have hprod : d + 16 * η ≤ 2 * τ * (horizontalSlope z.re).re :=
    hstart.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsτ (by norm_num)) hα0)
  exact hfuture d t htyp z.re hnear τ (hs.trans_le hsτ) hprod z rfl hz

/-- Every height of the unit window is near a typical height of power level. -/
def powerTypicalWindow (η T X : ℝ) : Prop :=
  ∀ Y : ℝ, |Y - X| ≤ 1 → ∃ t : ℝ, zetaTypicalHeight η (powerLevel η) T t ∧ |Y - t| ≤ η / 2

theorem powerTypicalWindow.depthWindow {η T X : ℝ} (h : powerTypicalWindow η T X) (hT : 1 ≤ T) :
    depthWindow 0 η T X := fun Y hY => by
  obtain ⟨t, ht, hYt⟩ := h Y hY
  exact ⟨t, ht.depthTypical hT, hYt⟩

private theorem exists_unit_interval_net {η : ℝ} (hη : 0 < η) :
    ∃ s : Finset ℝ, (∀ v ∈ s, |v| ≤ 1) ∧ ∀ w : ℝ, |w| ≤ 1 → ∃ v ∈ s, |w - v| ≤ η := by
  classical
  obtain ⟨s, hs, hf, hc⟩ := finite_cover_balls_of_compact
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)) hη
  refine ⟨hf.toFinset, ?_, ?_⟩
  · intro v hv
    exact abs_le.mpr (hs (by simpa only [hf.mem_toFinset] using hv))
  · intro w hw
    obtain ⟨v, hv, hwv⟩ := Set.mem_iUnion₂.mp (hc (abs_le.mp hw))
    refine ⟨v, by simpa only [hf.mem_toFinset] using hv, ?_⟩
    exact (show |w - v| < η by simpa only [mem_ball, Real.dist_eq] using hwv).le

/-- **Atypical unit windows are power-saving rare.** -/
theorem exists_volume_not_powerTypicalWindow_le_rpow {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∃ θ : ℝ, θ < 1 ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      volume {X | X ∈ Icc T (2 * T) ∧ ¬ powerTypicalWindow η T X} ≤ ENNReal.ofReal (T ^ θ) := by
  classical
  have hE0 : 0 < powerLevel η := by
    unfold powerLevel
    positivity
  have hE1 : powerLevel η ≤ 1 := by
    unfold powerLevel
    have h1 : η ^ 3 ≤ 1 := pow_le_one₀ hη.le (by linarith only [hη8])
    rw [div_le_one (by norm_num)]
    linarith only [h1]
  obtain ⟨θ₀, hθ₀, T₁, hbad⟩ := exists_volume_not_zetaTypicalHeight_le_rpow hη (by linarith only [hη8])
    hE0 hE1
  obtain ⟨s, hs, hcover⟩ := exists_unit_interval_net (show 0 < η / 2 by positivity)
  obtain ⟨θ₁, hθ₁⟩ : ∃ θ₁, θ₁ = max θ₀ 0 := ⟨_, rfl⟩
  have hθ₁0 : 0 ≤ θ₁ := hθ₁ ▸ le_max_right _ _
  have hθ₁1 : θ₁ < 1 := hθ₁ ▸ max_lt hθ₀ one_pos
  have hgap : 0 < (1 - θ₁) / 2 := by linarith only [hθ₁1]
  -- The factor of the union bound costs half of the saving.
  have hev : ∀ᶠ T : ℝ in atTop, (s.card : ℝ) + 2 ≤ T ^ ((1 - θ₁) / 2) :=
    (tendsto_rpow_atTop hgap).eventually_ge_atTop _
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp hev
  refine ⟨θ₁ + (1 - θ₁) / 2, by linarith only [hθ₁1], max (max T₁ T₂) 1, fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hTT₂ : T₂ ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
  let E' : Set ℝ := {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight η (powerLevel η) T t}
  have hsub : {X | X ∈ Icc T (2 * T) ∧ ¬ powerTypicalWindow η T X} ⊆
      (Icc T (T + 1) ∪ Icc (2 * T - 1) (2 * T)) ∪ ⋃ v ∈ s, (fun X : ℝ => X + v) ⁻¹' E' := by
    rintro X ⟨hXT, hn⟩
    by_cases hl : X ≤ T + 1
    · exact Or.inl (Or.inl ⟨hXT.1, hl⟩)
    by_cases hu : 2 * T - 1 ≤ X
    · exact Or.inl (Or.inr ⟨hu, hXT.2⟩)
    right
    by_contra hnone
    apply hn
    intro Y hYX
    obtain ⟨v, hv, hYv⟩ := hcover (Y - X) hYX
    have hvabs := abs_le.mp (hs v hv)
    have hcenter : X + v ∈ Icc T (2 * T) := by
      constructor <;> linarith only [not_le.mp hl, not_le.mp hu, hvabs.1, hvabs.2]
    have htyp : zetaTypicalHeight η (powerLevel η) T (X + v) := by
      by_contra ht
      exact hnone (Set.mem_iUnion₂.mpr ⟨v, hv, hcenter, ht⟩)
    refine ⟨X + v, htyp, ?_⟩
    simpa only [sub_add_eq_sub_sub] using hYv
  have hT0 : 0 < T := by linarith only [hT1]
  have hTθ : T ^ θ₀ ≤ T ^ θ₁ :=
    Real.rpow_le_rpow_of_exponent_le hT1 (hθ₁ ▸ le_max_left _ _)
  have htrans : ∀ v ∈ s, volume ((fun X : ℝ => X + v) ⁻¹' E') ≤ ENNReal.ofReal (T ^ θ₁) := by
    intro v _
    rw [measure_preimage_add_right]
    exact (hbad T hTT₁).trans (ENNReal.ofReal_le_ofReal hTθ)
  have hfinite : volume (⋃ v ∈ s, (fun X : ℝ => X + v) ⁻¹' E') ≤
      ENNReal.ofReal ((s.card : ℝ) * T ^ θ₁) := by
    calc
      _ ≤ ∑ v ∈ s, volume ((fun X : ℝ => X + v) ⁻¹' E') := measure_biUnion_finset_le s _
      _ ≤ ∑ _v ∈ s, ENNReal.ofReal (T ^ θ₁) := Finset.sum_le_sum htrans
      _ = s.card * ENNReal.ofReal (T ^ θ₁) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = _ := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg s.card), ENNReal.ofReal_natCast]
  have hends : volume (Icc T (T + 1) ∪ Icc (2 * T - 1) (2 * T)) ≤ ENNReal.ofReal 2 := by
    refine (measure_union_le _ _).trans ?_
    rw [Real.volume_Icc, Real.volume_Icc]
    rw [show T + 1 - T = 1 by ring, show 2 * T - (2 * T - 1) = 1 by ring]
    norm_num
  have hTθ1 : 1 ≤ T ^ θ₁ := Real.one_le_rpow hT1 hθ₁0
  have hsum : 2 + (s.card : ℝ) * T ^ θ₁ ≤ T ^ (θ₁ + (1 - θ₁) / 2) := by
    rw [Real.rpow_add hT0]
    have hcard := hT₂ T hTT₂
    have hc0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
    nlinarith only [mul_le_mul_of_nonneg_left hcard (show 0 ≤ T ^ θ₁ by linarith only [hTθ1]),
      hTθ1, hc0]
  calc
    _ ≤ volume (Icc T (T + 1) ∪ Icc (2 * T - 1) (2 * T)) +
        volume (⋃ v ∈ s, (fun X : ℝ => X + v) ⁻¹' E') :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal 2 + ENNReal.ofReal ((s.card : ℝ) * T ^ θ₁) := add_le_add hends hfinite
    _ = ENNReal.ofReal (2 + (s.card : ℝ) * T ^ θ₁) := by
      rw [ENNReal.ofReal_add (by norm_num) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hsum

/-- A typical unit window has an all-future-time Newman bound with small coefficient. -/
theorem eventually_localNewmanConstant_le_of_powerTypicalWindow {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∀ᶠ T : ℝ in atTop, ∀ X ∈ Icc T (2 * T), powerTypicalWindow η T X →
      localNewmanConstant X ≤ 16 * η / Real.log ((X - 1) / (2 * Real.pi)) := by
  filter_upwards [eventually_localNewmanConstant_le_of_depthWindow hη hη8,
    eventually_ge_atTop (1 : ℝ)] with T hb hT
  intro X hXT hwindow
  have h := hb 0 X hXT (hwindow.depthWindow hT) le_rfl
  rwa [zero_add] at h

private theorem eventually_log_le_twice_window_log :
    ∀ᶠ X : ℝ in atTop, 0 < Real.log ((X - 1) / (2 * Real.pi)) ∧
      Real.log X ≤ 2 * Real.log ((X - 1) / (2 * Real.pi)) := by
  filter_upwards [eventually_ge_atTop (Real.exp (2 * Real.log (4 * Real.pi))),
    eventually_ge_atTop (2 : ℝ)] with X he hX
  have hX0 : 0 < X := by linarith only [hX]
  have hπ : 0 < 2 * Real.pi := by positivity
  have h4π : 0 < 4 * Real.pi := by positivity
  have hlogπ : 0 < Real.log (4 * Real.pi) := Real.log_pos (by linarith only [Real.pi_gt_three])
  have hlogX : 2 * Real.log (4 * Real.pi) ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) he
  have hdiv : X / (4 * Real.pi) ≤ (X - 1) / (2 * Real.pi) := by
    rw [div_le_div_iff₀ h4π hπ]
    nlinarith only [mul_le_mul_of_nonneg_right hX Real.pi_pos.le]
  have hlower : Real.log X - Real.log (4 * Real.pi) ≤ Real.log ((X - 1) / (2 * Real.pi)) := by
    rw [← Real.log_div hX0.ne' h4π.ne']
    exact Real.log_le_log (by positivity) hdiv
  exact ⟨by linarith only [hlogπ, hlogX, hlower], by linarith only [hlogX, hlower]⟩

/-- **The power-saving exceptional set.** For every `κ > 0` there is `θ < 1` such that the heights `X ∈ [T, 2T]` with
`Λ_X log X > κ` have measure at most `T^θ`, for all large `T`. -/
theorem exists_volume_localNewman_scaled_gt_le_rpow {κ : ℝ} (hκ : 0 < κ) :
    ∃ θ : ℝ, θ < 1 ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      volume {X | X ∈ Icc T (2 * T) ∧ κ < localNewmanConstant X * Real.log X} ≤
        ENNReal.ofReal (T ^ θ) := by
  let η := min (κ / 64) (1 / 8)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη8 : η ≤ 1 / 8 := min_le_right _ _
  have hηκ : 32 * η ≤ κ := by
    have hh : η ≤ κ / 64 := min_le_left _ _
    linarith only [hh, hκ]
  obtain ⟨θ, hθ, T₁, hrare⟩ := exists_volume_not_powerTypicalWindow_le_rpow hη hη8
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (eventually_localNewmanConstant_le_of_powerTypicalWindow hη hη8)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp eventually_log_le_twice_window_log
  refine ⟨θ, hθ, max (max T₁ T₂) (max X₀ 8), fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hTT₂ : T₂ ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hTX₀ : X₀ ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hT8 : 8 ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  refine (measure_mono ?_).trans (hrare T hTT₁)
  rintro X ⟨hXT, hlarge⟩
  refine ⟨hXT, fun hwindow => ?_⟩
  obtain ⟨hL, hlog⟩ := hX₀ X (hTX₀.trans hXT.1)
  have hb := hT₂ T hTT₂ X hXT hwindow
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith only [hT8, hXT.1])
  have hle : localNewmanConstant X * Real.log X ≤ 32 * η := by
    calc
      _ ≤ (16 * η / Real.log ((X - 1) / (2 * Real.pi))) * Real.log X :=
        mul_le_mul_of_nonneg_right hb hlog0
      _ = 16 * η * Real.log X / Real.log ((X - 1) / (2 * Real.pi)) := by ring
      _ ≤ _ := by
        rw [div_le_iff₀ hL]
        nlinarith only [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 16 * η by positivity)]
  exact (not_lt_of_ge (hle.trans hηκ)) hlarge

/-- Off the same rare set, every zero of `H_τ` over the unit window is real for `τ ≥ κ / log X`. -/
theorem exists_volume_nonreal_heat_le_rpow {κ : ℝ} (hκ : 0 < κ) :
    ∃ θ : ℝ, θ < 1 ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      volume {X | X ∈ Icc T (2 * T) ∧ ∃ τ z, κ / Real.log X ≤ τ ∧ riemannHeat τ z = 0 ∧
        |z.re - X| ≤ 1 ∧ z.im ≠ 0} ≤ ENNReal.ofReal (T ^ θ) := by
  obtain ⟨θ, hθ, T₀, hvol⟩ := exists_volume_localNewman_scaled_gt_le_rpow (κ := κ / 2) (by positivity)
  refine ⟨θ, hθ, max T₀ 8, fun T hT => ?_⟩
  refine (measure_mono ?_).trans (hvol T ((le_max_left _ _).trans hT))
  rintro X ⟨hXT, τ, z, hτ, hz, hre, him⟩
  refine ⟨hXT, ?_⟩
  have hT8 : 8 ≤ T := (le_max_right _ _).trans hT
  have hlog : 0 < Real.log X := Real.log_pos (by linarith only [hT8, hXT.1])
  have hτΛ := le_localNewmanConstant_of_nonreal hz him hre
  have hstart := (div_le_iff₀ hlog).mp hτ
  have hh := mul_le_mul_of_nonneg_right hτΛ hlog.le
  linarith only [hstart, hh, hκ]

end

end GaloisForLFunctions.ZeroConfigurationGeometry

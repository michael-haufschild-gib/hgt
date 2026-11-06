import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TheSlopeOfXiAtAPowerLevel
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TypicalHeightHalfGaussBounds
import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.SmallHeatErrorBounds

/-!
# The half-Gauss transform at a typical height of power level

Let `Q(y) = ∫_{w>0} g_τ(w − y) ξ(½ + w + iX) dw`, at a typical height of level `T^E` with `E` a small power of the
depth. Then `|ζ′/ζ|` can be as large as `θ log X`, and the phase of `ζ` turns many times across the Gaussian window.
The complex saddle `u = y + 2τℓ`, `ℓ = ξ′/ξ(½ + u + iX)`, removes the rotation. With `M = ξ(½ + u + iX) e^{−τℓ²}` and
`P = |M|`:

* `PowerSaddle.norm_halfGauss_sub_main_le`: `|Q(y) − M| ≤ e₀ P`;
* `PowerSaddle.norm_halfGauss_slope_sub_le`: `|Q′(y) − ℓ Q(y)| ≤ e₁ P`;
* `PowerSaddle.norm_halfGauss_opposite_le`: `|Q(−y)| ≤ e₂ P`, with the reflection gain `e^{−2yα}`.

Each error is explicit in `τ`, `η`, `α` and the level. The statements hold for any `Λ` with a line model, in particular
for `ξ` (`DepthTypical.lineModel`).
-/

set_option autoImplicit false

open Complex Set Metric Filter Topology MeasureTheory
open scoped Interval
open _root_.RHTower _root_.RHTower.DeBruijn

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- `Λ` in the horizontal coordinate. -/
def lineF (Λ : ℂ → ℂ) (X : ℝ) (z : ℂ) : ℂ := Λ (1 / 2 + z + I * X)

theorem lineF_ofReal (Λ : ℂ → ℂ) (X w : ℝ) : lineF Λ X (w : ℂ) = lineFn Λ X w := rfl

theorem differentiable_lineF {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ) (X : ℝ) :
    Differentiable ℂ (lineF Λ X) :=
  hΛ.comp (by fun_prop)

/-- `ξ` satisfies the line model at a height of depth `d`. -/
theorem DepthTypical.lineModel {d η E T t : ℝ} (h : DepthTypical d η E T t) (hη : 0 < η)
    (hη2 : η ≤ 1 / 2) (hT : 8 ≤ T) (hE : 0 ≤ E) :
    LineModel xi d η (powerSlopeError E η T) (powerRatio E η T) t :=
  (h.levelPair hη hT hE).lineModel hη hη2 hT hE
    (fun {_ X} hτ => integrable_exp_mul_norm_xiLine hτ X)
    (fun {_ w} hX hw hwX => by
      have hm := norm_xiLine_le_model hX (u := 9 / 2) (w := w) ⟨le_rfl, hw.trans hwX⟩ ⟨hw, hwX⟩
      rw [abs_of_nonneg (by linarith only [hw])] at hm
      exact hm)
    (fun hX hW hWw => by
      have hg := norm_xiLine_le_far hX hW hWw
      rw [← horizontalSlope_re] at hg
      exact hg)

theorem re_point (X : ℝ) (w : ℂ) : (1 / 2 + w + I * X : ℂ).re = 1 / 2 + w.re := by
  rw [line_point]
  simp

theorem im_point (X : ℝ) (w : ℂ) : (1 / 2 + w + I * X : ℂ).im = X + w.im := by
  rw [line_point]
  simp

/-- The relative size of the terms off the window. -/
def powerTail (K η τ : ℝ) : ℝ :=
  K * ((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(η ^ 2 / (8 * τ))))

/-- The relative size of the terms beyond the Gaussian range. -/
def powerFar (K B τ α : ℝ) : ℝ :=
  K ^ 2 * Real.exp (τ * B ^ 2) * kklRC τ α

/-- The parameters and the complex saddle at one base point. -/
structure PowerSaddle (Λ : ℂ → ℂ) (d η B K t X τ y a δ : ℝ) (ℓ : ℂ) : Prop where
  model : LineModel Λ d η B K t
  hη : 0 < η
  hη8 : η ≤ 1 / 8
  hX : 1000 ≤ X
  hα : 8 ≤ (horizontalSlope X).re
  hαη : 8 ≤ η * (horizontalSlope X).re
  hXt : |X - t| ≤ η / 2
  hτ : 0 < τ
  hτ8 : τ ≤ 1 / 8
  hc1 : 16 * η ≤ 2 * τ * (horizontalSlope X).re
  hc2 : 2 * τ * (horizontalSlope X).re ≤ 1
  hy1 : -(1 / 2) ≤ y
  hy2 : y ≤ 1 / 2
  hyc : d + 12 * η ≤ y + 2 * τ * (horizontalSlope X).re
  hB : B ≤ η * (horizontalSlope X).re / 400
  data : SaddleData (lineF Λ X) τ y a δ ℓ (horizontalSlope X).re B η (9 / 2) (4 * B / η) K
  hℓ : ‖ℓ - horizontalSlope X‖ ≤ B
  ha1 : d + 11 * η ≤ a
  ha2 : a ≤ 2
  hδ : |δ| ≤ η / 4

/-- The window hypothesis of the saddle, from the second-order model. -/
private theorem hwin_of_box {Λ : ℂ → ℂ} {d η B K t X a δ : ℝ} {ℓ : ℂ} (typ : LineModel Λ d η B K t)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hX : 1000 ≤ X)
    (hXt : |X - t| ≤ η / 2) (hℓ : ℓ = lineLogDeriv Λ X ((a : ℂ) + (δ : ℂ) * I))
    (ha1 : d + 4 * η ≤ a) (ha2 : a ≤ 2) (hδ : |δ| ≤ η / 4) {v : ℝ} (hv : v ∈ Icc (-η) η) :
    ‖lineF Λ X ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) -
        lineF Λ X ((a : ℂ) + (δ : ℂ) * I) * Complex.exp ((v : ℂ) * ℓ)‖ ≤
      ‖lineF Λ X ((a : ℂ) + (δ : ℂ) * I)‖ * Real.exp (v * ℓ.re) *
        (Real.exp (4 * B / η * v ^ 2) - 1) := by
  refine typ.norm_window_model_le hη hη8 hX hXt hℓ fun x hx => ?_
  have hxb : a - η ≤ x ∧ x ≤ a + η := by
    rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith only [h1, hη], by linarith only [h2, hv.2]⟩
    · exact ⟨by linarith only [h1, hv.1], by linarith only [h2, hη]⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
    linarith only [hxb.1, ha1]
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
    linarith only [hxb.2, ha2, hη8]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
    exact hδ

/-- **The saddle exists at every base point of the range.** -/
theorem exists_powerSaddle {Λ : ℂ → ℂ} {d η B K t X τ y : ℝ} (typ : LineModel Λ d η B K t)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hX : 1000 ≤ X)
    (hα : 8 ≤ (horizontalSlope X).re) (hαη : 8 ≤ η * (horizontalSlope X).re)
    (hXt : |X - t| ≤ η / 2) (hτ : 0 < τ) (hτ8 : τ ≤ 1 / 8)
    (hc1 : 16 * η ≤ 2 * τ * (horizontalSlope X).re) (hc2 : 2 * τ * (horizontalSlope X).re ≤ 1)
    (hy1 : -(1 / 2) ≤ y) (hy2 : y ≤ 1 / 2)
    (hyc : d + 12 * η ≤ y + 2 * τ * (horizontalSlope X).re)
    (hB : B ≤ η * (horizontalSlope X).re / 400) :
    ∃ (a δ : ℝ) (ℓ : ℂ), PowerSaddle Λ d η B K t X τ y a δ ℓ ∧
      ℓ = lineLogDeriv Λ X ((a : ℂ) + (δ : ℂ) * I) := by
  obtain ⟨α, hαdef⟩ : ∃ α, α = (horizontalSlope X).re := ⟨_, rfl⟩
  rw [← hαdef] at hα hαη hc1 hc2 hyc hB
  have hBpos : 0 < B := typ.hB
  have hα0 : 0 < α := by linarith only [hα]
  -- The two consequences of `2τα ≤ 1` and `ηα ≥ 8`.
  have h2τ : 2 * τ ≤ η / 8 := by
    have h1 := mul_le_mul_of_nonneg_left hαη (show 0 ≤ 2 * τ by positivity)
    nlinarith only [h1, mul_le_mul_of_nonneg_left hc2 hη.le]
  have h2τB : 2 * τ * B ≤ η / 400 := by
    have h1 := mul_le_mul_of_nonneg_left hB (show 0 ≤ 2 * τ by positivity)
    have h2 := mul_le_mul_of_nonneg_left hc2 hη.le
    nlinarith only [h1, h2]
  have hc₀re : ((y : ℂ) + 2 * (τ : ℂ) * horizontalSlope X).re = y + 2 * τ * α := by
    simp [Complex.add_re, Complex.mul_re, hαdef]
  have hc₀im : ((y : ℂ) + 2 * (τ : ℂ) * horizontalSlope X).im = 2 * τ * (Real.pi / 4) := by
    simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.mul_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, zero_mul, sub_zero, add_zero,
      horizontalSlope_im]
    ring
  have hπ := Real.pi_lt_four
  have hπ0 := Real.pi_pos
  have him0 : 2 * τ * (Real.pi / 4) ≤ η / 8 := by
    have : 2 * τ * (Real.pi / 4) ≤ 2 * τ * 1 :=
      mul_le_mul_of_nonneg_left (by linarith only [hπ]) (by positivity)
    linarith only [this, h2τ]
  have him00 : 0 ≤ 2 * τ * (Real.pi / 4) := by positivity
  -- The ball about the Euler-free saddle lies in the inner box.
  have hball : ∀ w ∈ closedBall ((y : ℂ) + 2 * (τ : ℂ) * horizontalSlope X) (2 * τ * B),
      y + 2 * τ * α - η / 400 ≤ w.re ∧ w.re ≤ y + 2 * τ * α + η / 400 ∧ |w.im| ≤ η / 8 + η / 400 := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have hre := abs_le.mp ((Complex.abs_re_le_norm _).trans (hw.trans h2τB))
    have him := abs_le.mp ((Complex.abs_im_le_norm _).trans (hw.trans h2τB))
    rw [Complex.sub_re, hc₀re] at hre
    rw [Complex.sub_im, hc₀im] at him
    refine ⟨by linarith only [hre.1], by linarith only [hre.2], abs_le.mpr ⟨?_, ?_⟩⟩
    · linarith only [him.1, him00, hη]
    · linarith only [him.2, him0]
  have hsub : closedBall ((y : ℂ) + 2 * (τ : ℂ) * horizontalSlope X) (2 * τ * B) ⊆
      innerBox d η := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hball w hw
    refine ⟨by linarith only [h1, hyc, hη], by linarith only [h2, hy2, hc2, hη8], ?_⟩
    exact h3.trans (by linarith only [hη])
  have hlip : 2 * τ * (4 * B / η) ≤ 1 / 2 := by
    have he : 2 * τ * (4 * B / η) = 4 * (2 * τ * B) / η := by ring
    rw [he, div_le_iff₀ hη]
    linarith only [h2τB, hη]
  obtain ⟨u, hu, hfix⟩ := typ.exists_saddle_fixedPoint hη hη8 hX hXt hτ hsub hlip
  obtain ⟨hu1, hu2, hu3⟩ := hball u hu
  have hu_eq : (u.re : ℂ) + (u.im : ℂ) * I = u := Complex.re_add_im u
  have hreg : u ∈ saddleRegion d η t X := by
    have h3' := abs_le.mp hu3
    have hXt'' := abs_le.mp hXt
    refine ⟨by linarith only [hu1, hyc, hη], by linarith only [hu2, hy2, hc2, hη8],
      abs_le.mpr ⟨?_, ?_⟩⟩
    · linarith only [h3'.1, hXt''.1, hη]
    · linarith only [h3'.2, hXt''.2, hη]
  have hXt' : |X - t| ≤ η := hXt.trans (by linarith only [hη])
  have hℓB : ‖lineLogDeriv Λ X u - horizontalSlope X‖ ≤ B := typ.slope hX hXt' hreg
  have ha1 : d + 11 * η ≤ u.re := by linarith only [hu1, hyc, hη]
  have ha2 : u.re ≤ 2 := by linarith only [hu2, hy2, hc2, hη8]
  have hδ : |u.im| ≤ η / 4 := hu3.trans (by linarith only [hη])
  have hℓ' : lineLogDeriv Λ X u = lineLogDeriv Λ X ((u.re : ℂ) + (u.im : ℂ) * I) := by rw [hu_eq]
  refine ⟨u.re, u.im, lineLogDeriv Λ X u, ?_, hℓ'⟩
  have hsrc : ∀ x ∈ Icc (0 : ℝ) (9 / 2), ∀ v ∈ [[(0 : ℝ), u.im]],
      ‖lineF Λ X ((x : ℂ) + (v : ℂ) * I)‖ ≤
        K * ‖lineF Λ X ((u.re : ℂ) + (u.im : ℂ) * I)‖ *
          Real.exp ((x - u.re) * (horizontalSlope X).re) := by
    intro x hx v hv
    have hvabs : |v| ≤ |u.im| := by
      rcases Set.mem_uIcc.mp hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
        exact h2
      · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]
        linarith only [h1]
    rw [hu_eq]
    have hXt'' := abs_le.mp hXt
    have hu' := abs_le.mp hδ
    have hv' := abs_le.mp (hvabs.trans hδ)
    have hval := typ.anchor (s₀ := (1 / 2 + u + I * X : ℂ))
      (s₁ := (1 / 2 + ((x : ℂ) + (v : ℂ) * I) + I * X : ℂ)) hX
      (by rw [re_point]; linarith only [ha1, hη])
      (by rw [re_point]; linarith only [ha2])
      (by
        rw [im_point]
        exact abs_le.mpr ⟨by linarith only [hXt''.1, hu'.1, hη],
          by linarith only [hXt''.2, hu'.2, hη]⟩)
      (by
        rw [re_point]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
        linarith only [hx.1])
      (by
        rw [re_point]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
        linarith only [hx.2])
      (by
        rw [im_point]
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
        exact abs_le.mpr ⟨by linarith only [hXt''.1, hv'.1, hη, hη8],
          by linarith only [hXt''.2, hv'.2, hη, hη8]⟩)
      (by
        rw [im_point, add_sub_cancel_left]
        exact abs_le.mpr ⟨by linarith only [hu'.1, hη, hη8], by linarith only [hu'.2, hη, hη8]⟩)
      (by
        rw [im_point, add_sub_cancel_left]
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
        exact abs_le.mpr ⟨by linarith only [hv'.1, hη, hη8], by linarith only [hv'.2, hη, hη8]⟩)
    rw [re_point, re_point] at hval
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_self, add_zero] at hval
    have hexpo : 1 / 2 + x - (1 / 2 + u.re) = x - u.re := by ring
    rw [hexpo] at hval
    exact hval
  refine
    { model := typ, hη := hη, hη8 := hη8, hX := hX,
      hα := hαdef ▸ hα, hαη := hαdef ▸ hαη, hXt := hXt, hτ := hτ, hτ8 := hτ8,
      hc1 := hαdef ▸ hc1, hc2 := hαdef ▸ hc2, hy1 := hy1, hy2 := hy2, hyc := hαdef ▸ hyc,
      hB := by rw [← hαdef]; exact hB, data := ?_, hℓ := hℓB,
      ha1 := ha1, ha2 := ha2, hδ := hδ }
  refine
    { hF := differentiable_lineF typ.entire X, hτ := hτ, hu := by rw [hu_eq]; exact hfix,
      hA := ?_, hΛ := ?_, hρ := hη, hlow := by linarith only [ha1, hη, typ.hd],
      hhigh := by linarith only [ha2, hη8],
      hB0 := ?_, hB := ?_, hK := typ.hK.le,
      hwin := fun v hv => hwin_of_box typ hη hη8 hX hXt hℓ'
        (by linarith only [ha1, hη]) ha2 hδ hv,
      hsrc := hsrc }
  · rw [← hαdef]
    have hre := (Complex.abs_re_le_norm (lineLogDeriv Λ X u - horizontalSlope X)).trans hℓB
    rwa [Complex.sub_re, ← hαdef] at hre
  · linarith only [h2τB, hη]
  · positivity
  · have he : 8 * τ * (4 * B / η) = 16 * (2 * τ * B) / η := by ring
    rw [he, div_le_iff₀ hη]
    linarith only [h2τB, hη]

namespace PowerSaddle

variable {Λ : ℂ → ℂ} {d η B K t X τ y a δ : ℝ} {ℓ : ℂ}

theorem hB_pos (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) : 0 < B := h.model.hB

theorem hK_pos (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) : 0 < K := h.model.hK

theorem hτ_small (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) : τ ≤ η / 16 := by
  have h1 := mul_le_mul_of_nonneg_left h.hαη (show 0 ≤ 2 * τ by linarith only [h.hτ])
  have h2 := mul_le_mul_of_nonneg_left h.hc2 h.hη.le
  nlinarith only [h1, h2]

theorem hτB (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) : 2 * τ * B ≤ η / 400 := by
  have h1 := mul_le_mul_of_nonneg_left h.hB (show 0 ≤ 2 * τ by linarith only [h.hτ])
  have h2 := mul_le_mul_of_nonneg_left h.hc2 h.hη.le
  nlinarith only [h1, h2]

theorem hy_abs (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) : |y| ≤ 1 / 2 :=
  abs_le.mpr ⟨h.hy1, h.hy2⟩

/-- The right end of the Gaussian range. -/
theorem hW (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) :
    (9 / 2 : ℝ) ≤ 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ∧
      2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2 := by
  have hα := h.hα
  have hτ0 := h.hτ
  have hc : 0 ≤ 2 * τ * (horizontalSlope X).re := by
    have : 0 ≤ (horizontalSlope X).re := by linarith only [hα]
    positivity
  refine ⟨by nlinarith only [hα, hc], ?_⟩
  exact window_fits h.hτ8 h.hτ (by linarith only [h.hX]) (by linarith only [hα])

/-- The value at `9/2`, relative to the saddle. -/
theorem norm_nine_halves_le (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) :
    ‖lineFn Λ X (9 / 2)‖ ≤ K * ‖lineF Λ X ((a : ℂ) + (δ : ℂ) * I)‖ *
      Real.exp ((9 / 2 - a) * (horizontalSlope X).re) := by
  have hs := h.data.hsrc (9 / 2) ⟨by norm_num, le_rfl⟩ 0 left_mem_uIcc
  have he : (((9 / 2 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) = ((9 / 2 : ℝ) : ℂ) := by simp
  rw [he, lineF_ofReal] at hs
  exact hs

/-- Right of `9/2`, the slope rises by at most `1/8`. -/
theorem norm_right_le (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) {w : ℝ} (hw : 9 / 2 ≤ w)
    (hwX : w ≤ X / 32 - 1 / 2) :
    ‖lineFn Λ X w‖ ≤ K * ‖lineF Λ X ((a : ℂ) + (δ : ℂ) * I)‖ *
      Real.exp ((w - a) * ((horizontalSlope X).re + 1 / 8)) := by
  have hm := h.model.model (by linarith only [h.hX] : 200 ≤ X) hw hwX
  have hn := h.norm_nine_halves_le
  have hK := h.hK_pos.le
  have hN := norm_nonneg (lineF Λ X ((a : ℂ) + (δ : ℂ) * I))
  have ha2 := h.ha2
  calc
    _ ≤ (K * ‖lineF Λ X ((a : ℂ) + (δ : ℂ) * I)‖ *
          Real.exp ((9 / 2 - a) * (horizontalSlope X).re)) *
        Real.exp ((w - 9 / 2) * (horizontalSlope X).re) * Real.exp (1 / 8 * (w - 9 / 2)) := by
      refine hm.trans ?_
      gcongr
    _ = K * ‖lineF Λ X ((a : ℂ) + (δ : ℂ) * I)‖ *
        Real.exp ((9 / 2 - a) * (horizontalSlope X).re +
          (w - 9 / 2) * (horizontalSlope X).re + 1 / 8 * (w - 9 / 2)) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK hN)
      apply Real.exp_le_exp.mpr
      nlinarith only [ha2, hw]

/-- The mass of a real point right of the saddle window, relative to the mass of the saddle. -/
theorem gauss_mul_norm_right_le (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) {w : ℝ} (hw : 9 / 2 ≤ w)
    (hwX : w ≤ X / 32 - 1 / 2) :
    gaussDensity τ (w - y) * ‖lineFn Λ X w‖ ≤
      SaddleData.mass (lineF Λ X) τ a δ ℓ * powerTail (K) η τ := by
  have hτ := h.hτ
  have hA := h.data.hA
  have hA' : |ℓ.re - ((horizontalSlope X).re + 1 / 8)| ≤ B + 1 / 8 := by
    have hh := abs_le.mp hA
    exact abs_le.mpr ⟨by linarith only [hh.1], by linarith only [hh.2]⟩
  have hsm := h.hτB
  have hτs := h.hτ_small
  have hΛ : 8 * τ * (B + 1 / 8) ≤ η := by
    nlinarith only [hsm, hτs, h.hη]
  have hxa : η ≤ |w - a| := by
    rw [abs_of_nonneg (by linarith only [hw, h.ha2])]
    linarith only [hw, h.ha2, h.hη8]
  have hexpo := gauss_source_exponent_le (v := 0) hτ h.data.re_eq h.data.im_eq hA' hΛ h.hη.le
    (by rw [zero_pow two_ne_zero]; exact sq_nonneg δ) hxa
  have hsrc := h.norm_right_le hw hwX
  have hN := norm_nonneg (lineF Λ X ((a : ℂ) + (δ : ℂ) * I))
  have hK := h.hK_pos.le
  have hc : 0 ≤ (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) := by positivity
  unfold gaussDensity powerTail SaddleData.mass
  calc
    _ ≤ ((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) * Real.exp (-((w - y) ^ 2 / (4 * τ)))) *
        (K * ‖lineF Λ X ((a : ℂ) + (δ : ℂ) * I)‖ *
          Real.exp ((w - a) * ((horizontalSlope X).re + 1 / 8))) :=
      mul_le_mul_of_nonneg_left hsrc (by positivity)
    _ = K * ‖lineF Λ X ((a : ℂ) + (δ : ℂ) * I)‖ * (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(((w - y) ^ 2 - 0 ^ 2) / (4 * τ)) +
          (w - a) * ((horizontalSlope X).re + 1 / 8)) := by
      rw [Real.exp_add, zero_pow two_ne_zero, sub_zero]
      ring
    _ ≤ K * ‖lineF Λ X ((a : ℂ) + (δ : ℂ) * I)‖ * (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(τ * (ℓ.re ^ 2 - ℓ.im ^ 2)) - η ^ 2 / (8 * τ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexpo) (mul_nonneg (mul_nonneg hK hN) hc)
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring

/-- The value at the real saddle, relative to the complex saddle. -/
theorem norm_real_saddle_le (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) :
    ‖lineFn Λ X (y + 2 * τ * (horizontalSlope X).re)‖ ≤
      K * ‖lineF Λ X ((a : ℂ) + (δ : ℂ) * I)‖ *
        Real.exp ((y + 2 * τ * (horizontalSlope X).re - a) * (horizontalSlope X).re) := by
  have hs := h.data.hsrc (y + 2 * τ * (horizontalSlope X).re)
    ⟨by linarith only [h.hyc, h.hη, h.model.hd], by linarith only [h.hy2, h.hc2]⟩ 0 left_mem_uIcc
  have he : (((y + 2 * τ * (horizontalSlope X).re : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) =
      ((y + 2 * τ * (horizontalSlope X).re : ℝ) : ℂ) := by simp
  rw [he, lineF_ofReal] at hs
  exact hs

/-- The value at the real saddle controls `9/2` against the same anchor, with the same ratio. -/
theorem norm_nine_halves_le_real (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) :
    ‖lineFn Λ X (9 / 2)‖ ≤ K * ‖lineFn Λ X (y + 2 * τ * (horizontalSlope X).re)‖ *
      Real.exp ((9 / 2 - (y + 2 * τ * (horizontalSlope X).re)) * (horizontalSlope X).re) := by
  have hXt := abs_le.mp h.hXt
  have hη := h.hη
  have hη8 := h.hη8
  have hval := h.model.anchor (s₀ := (1 / 2 + ((y + 2 * τ * (horizontalSlope X).re : ℝ) : ℂ) + I * X : ℂ))
    (s₁ := (1 / 2 + ((9 / 2 : ℝ) : ℂ) + I * X : ℂ)) h.hX
    (by rw [re_point, Complex.ofReal_re]; linarith only [h.hyc, hη])
    (by rw [re_point, Complex.ofReal_re]; linarith only [h.hy2, h.hc2])
    (by
      rw [im_point, Complex.ofReal_im, add_zero]
      exact abs_le.mpr ⟨by linarith only [hXt.1, hη], by linarith only [hXt.2, hη]⟩)
    (by rw [re_point, Complex.ofReal_re]; norm_num)
    (by rw [re_point, Complex.ofReal_re]; norm_num)
    (by
      rw [im_point, Complex.ofReal_im, add_zero]
      exact abs_le.mpr ⟨by linarith only [hXt.1, hη, hη8], by linarith only [hXt.2, hη, hη8]⟩)
    (by rw [im_point, Complex.ofReal_im, add_zero, sub_self, abs_zero]; norm_num)
    (by rw [im_point, Complex.ofReal_im, add_zero, sub_self, abs_zero]; norm_num)
  rw [re_point, re_point, Complex.ofReal_re, Complex.ofReal_re] at hval
  have hexpo : 1 / 2 + 9 / 2 - (1 / 2 + (y + 2 * τ * (horizontalSlope X).re)) =
      9 / 2 - (y + 2 * τ * (horizontalSlope X).re) := by ring
  rw [hexpo] at hval
  exact hval

/-- **The far terms.** Beyond the Gaussian range, both masses are `P K² e^{τB²}` times the corpus far term. -/
theorem far_terms_le (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) :
    (∫ w in Ioi (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
        (|(w - y) / (2 * τ)| + ‖horizontalSlope X‖) * gaussDensity τ (w - y) * ‖lineFn Λ X w‖) ≤
      SaddleData.mass (lineF Λ X) τ a δ ℓ *
        powerFar (K) (B) τ (horizontalSlope X).re ∧
    (∫ w in Ioi (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
        gaussDensity τ (w - y) * ‖lineFn Λ X w‖) ≤
      SaddleData.mass (lineF Λ X) τ a δ ℓ *
        powerFar (K) (B) τ (horizontalSlope X).re := by
  have hX200 : (200 : ℝ) ≤ X := by linarith only [h.hX]
  have hα := h.hα
  have hK := h.hK_pos
  obtain ⟨hW9, hWX⟩ := h.hW
  obtain ⟨W, hWdef⟩ : ∃ W, W = 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 := ⟨_, rfl⟩
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, u₀ = y + 2 * τ * (horizontalSlope X).re := ⟨_, rfl⟩
  have hu₀2 : u₀ ≤ 9 / 2 := by
    rw [hu₀]
    linarith only [h.hy2, h.hc2]
  have hFW : ‖lineFn Λ X (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)‖ ≤
      (K * ‖lineFn Λ X (y + 2 * τ * (horizontalSlope X).re)‖) *
        Real.exp ((2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 -
          (y + 2 * τ * (horizontalSlope X).re)) * ((horizontalSlope X).re + 1 / 8)) := by
    rw [← hWdef, ← hu₀]
    rw [← hWdef] at hW9 hWX
    have hm := h.model.model hX200 hW9 hWX
    have hn := h.norm_nine_halves_le_real
    rw [← hu₀] at hn
    have hN := norm_nonneg (lineFn Λ X u₀)
    calc
      _ ≤ (K * ‖lineFn Λ X u₀‖ *
            Real.exp ((9 / 2 - u₀) * (horizontalSlope X).re)) *
          Real.exp ((W - 9 / 2) * (horizontalSlope X).re) * Real.exp (1 / 8 * (W - 9 / 2)) := by
        refine hm.trans ?_
        gcongr
      _ = K * ‖lineFn Λ X u₀‖ *
          Real.exp ((9 / 2 - u₀) * (horizontalSlope X).re +
            (W - 9 / 2) * (horizontalSlope X).re + 1 / 8 * (W - 9 / 2)) := by
        rw [Real.exp_add, Real.exp_add]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK.le hN)
        apply Real.exp_le_exp.mpr
        nlinarith only [hu₀2, hW9]
  obtain ⟨h1, h2, _⟩ := far_terms_le_of_growth (f := lineFn Λ X)
    (N := K * ‖lineFn Λ X (y + 2 * τ * (horizontalSlope X).re)‖) h.hτ h.hτ8 hX200 h.hy_abs
    (by linarith only [hα]) (by positivity) hW9 hFW
    (fun w hw => h.model.grow hX200 hW9 hw.le)
  have hR := kklRC_nonneg h.hτ (by linarith only [hα] : 0 ≤ (horizontalSlope X).re)
  have hre := h.data.re_eq
  have hA := h.data.hA
  -- The real saddle against the complex saddle.
  have hcomp : (K * ‖lineFn Λ X (y + 2 * τ * (horizontalSlope X).re)‖) *
      Real.exp (-(τ * (horizontalSlope X).re ^ 2)) * kklRC τ (horizontalSlope X).re ≤
      SaddleData.mass (lineF Λ X) τ a δ ℓ *
        powerFar (K) (B) τ (horizontalSlope X).re := by
    have hrs := h.norm_real_saddle_le
    have hN := norm_nonneg (lineF Λ X ((a : ℂ) + (δ : ℂ) * I))
    have hexp : Real.exp ((y + 2 * τ * (horizontalSlope X).re - a) * (horizontalSlope X).re) *
        Real.exp (-(τ * (horizontalSlope X).re ^ 2)) ≤
        Real.exp (-(τ * (ℓ.re ^ 2 - ℓ.im ^ 2))) * Real.exp (τ * B ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [hre]
      have hsq : (ℓ.re - (horizontalSlope X).re) ^ 2 ≤ B ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hA 2
      have hτ0 := h.hτ.le
      nlinarith only [mul_le_mul_of_nonneg_left hsq hτ0, mul_nonneg hτ0 (sq_nonneg ℓ.im)]
    unfold SaddleData.mass powerFar
    calc
      _ ≤ (K * (K * ‖lineF Λ X ((a : ℂ) + (δ : ℂ) * I)‖ *
            Real.exp ((y + 2 * τ * (horizontalSlope X).re - a) * (horizontalSlope X).re))) *
          Real.exp (-(τ * (horizontalSlope X).re ^ 2)) * kklRC τ (horizontalSlope X).re := by
        gcongr
      _ = K ^ 2 * ‖lineF Λ X ((a : ℂ) + (δ : ℂ) * I)‖ * kklRC τ (horizontalSlope X).re *
          (Real.exp ((y + 2 * τ * (horizontalSlope X).re - a) * (horizontalSlope X).re) *
            Real.exp (-(τ * (horizontalSlope X).re ^ 2))) := by ring
      _ ≤ K ^ 2 * ‖lineF Λ X ((a : ℂ) + (δ : ℂ) * I)‖ * kklRC τ (horizontalSlope X).re *
          (Real.exp (-(τ * (ℓ.re ^ 2 - ℓ.im ^ 2))) * Real.exp (τ * B ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  exact ⟨h1.trans hcomp, h2.trans hcomp⟩

theorem gauss_integrable (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) :
    Integrable (fun w => (gaussDensity τ (w - y) : ℂ) * lineFn Λ X w) :=
  integrable_gaussDensity_sub_mul h.hτ (h.model.continuous_lineFn X) (h.model.integrable h.hτ) y

theorem integrable_slope (hL : LineModel Λ d η B K t) {τ : ℝ} (hτ : 0 < τ) (X y : ℝ) :
    Integrable (fun w => (((w - y) / (2 * τ) * gaussDensity τ (w - y) : ℝ) : ℂ) * lineFn Λ X w) := by
  have h2τ : 0 < 2 * τ := by positivity
  have hmaj := ((integrable_gaussDensity_sub_mul h2τ (hL.continuous_lineFn X)
    (hL.integrable h2τ) y).norm).const_mul (2 / Real.sqrt τ)
  refine hmaj.mono' ?_ (Eventually.of_forall fun w => ?_)
  · have hg := continuous_gaussDensity τ
    have hc : Continuous fun w : ℝ => (((w - y) / (2 * τ) * gaussDensity τ (w - y) : ℝ) : ℂ) *
        lineFn Λ X w := by
      refine (Complex.continuous_ofReal.comp ?_).mul (hL.continuous_lineFn X)
      exact (by fun_prop : Continuous fun w : ℝ => (w - y) / (2 * τ)).mul
        (hg.comp (by fun_prop))
    exact hc.aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos h2τ,
      abs_of_pos (gaussDensity_pos hτ _), norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (gaussDensity_pos h2τ _), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (abs_div_mul_gaussDensity_le hτ (w - y)) (norm_nonneg _)

theorem integrable_weight (hL : LineModel Λ d η B K t) {τ : ℝ} (hτ : 0 < τ) (X y : ℝ) (A : ℝ) :
    Integrable (fun w => (|(w - y) / (2 * τ)| + A) * gaussDensity τ (w - y) * ‖lineFn Λ X w‖) := by
  have h1 := (integrable_slope hL hτ X y).norm
  have h2 := ((integrable_gaussDensity_sub_mul hτ (hL.continuous_lineFn X)
    (hL.integrable hτ) y).norm).const_mul A
  refine (h1.add h2).congr (Eventually.of_forall fun w => ?_)
  simp only [Pi.add_apply]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (gaussDensity_pos hτ _),
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussDensity_pos hτ _)]
  ring

/-- The first piece of the half transform, in the kernel of the saddle. -/
private theorem head_eq (Λ : ℂ → ℂ) (y : ℝ) (X τ : ℝ) :
    (∫ x in (0 : ℝ)..(9 / 2), gaussKernel τ ((x : ℂ) - (y : ℂ)) * lineF Λ X (x : ℂ)) =
      ∫ w in Ioc (0 : ℝ) (9 / 2), (gaussDensity τ (w - y) : ℂ) * lineFn Λ X w := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  refine setIntegral_congr_fun measurableSet_Ioc fun w _ => ?_
  rw [← Complex.ofReal_sub, gaussKernel_ofReal, lineF_ofReal]

/-- **The saddle value of the half transform.** -/
theorem norm_halfGauss_sub_main_le (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) :
    ‖halfGaussTransform τ (lineFn Λ X) y -
        lineF Λ X ((a : ℂ) + (δ : ℂ) * I) * Complex.exp (-((τ : ℂ) * ℓ ^ 2))‖ ≤
      SaddleData.mass (lineF Λ X) τ a δ ℓ * (8 * τ * (4 * B / η) +
        2 * Real.exp (-(η ^ 2 / (8 * τ))) +
        powerTail (K) η τ *
          (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 + 1) +
        powerFar (K) (B) τ (horizontalSlope X).re) := by
  have hτ := h.hτ
  obtain ⟨hW9, hWX⟩ := h.hW
  obtain ⟨W, hWdef⟩ : ∃ W, W = 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 := ⟨_, rfl⟩
  rw [← hWdef] at hW9 hWX ⊢
  have hsplit := setIntegral_Ioi_split (by norm_num : (0 : ℝ) ≤ 9 / 2) hW9
    h.gauss_integrable.integrableOn
  obtain ⟨P, hPdef⟩ : ∃ P, P = SaddleData.mass (lineF Λ X) τ a δ ℓ := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := hPdef ▸ SaddleData.mass_nonneg _ _ _ _ _
  rw [← hPdef]
  have hhead := h.data.norm_integral_sub_main_le
  rw [head_eq Λ, ← hPdef] at hhead
  have hmid : ‖∫ w in Ioc (9 / 2 : ℝ) W, (gaussDensity τ (w - y) : ℂ) * lineFn Λ X w‖ ≤
      P * powerTail (K) η τ * (W - 9 / 2) := by
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (9 / 2 : ℝ) W)
      (f := fun w : ℝ => (gaussDensity τ (w - y) : ℂ) * lineFn Λ X w)
      (C := P * powerTail (K) η τ) measure_Ioc_lt_top (fun w hw => by
        rw [norm_gauss_mul τ y w hτ, hPdef]
        exact h.gauss_mul_norm_right_le hw.1.le (hw.2.trans hWX))
    rwa [Real.volume_real_Ioc_of_le hW9] at hb
  have hfar : ‖∫ w in Ioi W, (gaussDensity τ (w - y) : ℂ) * lineFn Λ X w‖ ≤
      P * powerFar (K) (B) τ (horizontalSlope X).re := by
    have hn : ‖∫ w in Ioi W, (gaussDensity τ (w - y) : ℂ) * lineFn Λ X w‖ ≤
        ∫ w in Ioi W, gaussDensity τ (w - y) * ‖lineFn Λ X w‖ := by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      congr 1
      funext w
      exact norm_gauss_mul τ y w hτ _
    have hfa := h.far_terms_le.2
    rw [← hWdef, ← hPdef] at hfa
    exact hn.trans hfa
  have hδ1 : 9 / 2 + 2 * |δ| + (W - 9 / 2) ≤ W + 1 := by
    have := h.hδ
    linarith only [this, h.hη8]
  have hT0 : 0 ≤ powerTail (K) η τ := by
    have := h.hK_pos.le
    unfold powerTail
    positivity
  unfold halfGaussTransform
  rw [hsplit]
  have hne : (∫ w in Ioc (0 : ℝ) (9 / 2), (gaussDensity τ (w - y) : ℂ) * lineFn Λ X w) +
        (∫ w in Ioc (9 / 2 : ℝ) W, (gaussDensity τ (w - y) : ℂ) * lineFn Λ X w) +
        (∫ w in Ioi W, (gaussDensity τ (w - y) : ℂ) * lineFn Λ X w) -
        lineF Λ X ((a : ℂ) + (δ : ℂ) * I) * Complex.exp (-((τ : ℂ) * ℓ ^ 2)) =
      ((∫ w in Ioc (0 : ℝ) (9 / 2), (gaussDensity τ (w - y) : ℂ) * lineFn Λ X w) -
        lineF Λ X ((a : ℂ) + (δ : ℂ) * I) * Complex.exp (-((τ : ℂ) * ℓ ^ 2))) +
        (∫ w in Ioc (9 / 2 : ℝ) W, (gaussDensity τ (w - y) : ℂ) * lineFn Λ X w) +
        (∫ w in Ioi W, (gaussDensity τ (w - y) : ℂ) * lineFn Λ X w) := by ring
  rw [hne]
  refine (norm_add₃_le).trans ?_
  have htail : K * ((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(η ^ 2 / (8 * τ)))) = powerTail (K) η τ := rfl
  rw [htail] at hhead
  calc
    _ ≤ P * (8 * τ * (4 * B / η) + 2 * Real.exp (-(η ^ 2 / (8 * τ))) +
          powerTail (K) η τ * (9 / 2 + 2 * |δ|)) +
        P * powerTail (K) η τ * (W - 9 / 2) +
        P * powerFar (K) (B) τ (horizontalSlope X).re :=
      add_le_add (add_le_add hhead hmid) hfar
    _ = P * (8 * τ * (4 * B / η) + 2 * Real.exp (-(η ^ 2 / (8 * τ))) +
          powerTail (K) η τ * (9 / 2 + 2 * |δ| + (W - 9 / 2)) +
          powerFar (K) (B) τ (horizontalSlope X).re) := by ring
    _ ≤ _ := by
      gcongr

/-- The first moment about the saddle is the slope of the half transform. -/
private theorem slope_sub_eq (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) :
    (∫ w in Ioi (0 : ℝ), (((w - y) / (2 * τ) * gaussDensity τ (w - y) : ℝ) : ℂ) * lineFn Λ X w) -
        ℓ * halfGaussTransform τ (lineFn Λ X) y =
      ∫ w in Ioi (0 : ℝ), ((w : ℂ) - ((a : ℂ) + (δ : ℂ) * I)) / (2 * (τ : ℂ)) *
        ((gaussDensity τ (w - y) : ℂ) * lineFn Λ X w) := by
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast h.hτ.ne'
  unfold halfGaussTransform
  rw [← integral_const_mul, ← integral_sub (integrable_slope h.model h.hτ X y).integrableOn
    (h.gauss_integrable.const_mul ℓ).integrableOn]
  refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
  rw [h.data.hu]
  push_cast
  field_simp
  ring

/-- **The slope of the half transform.** `Q′(y) − ℓ Q(y)` is small against the saddle mass. -/
theorem norm_halfGauss_slope_sub_le (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) :
    ‖(∫ w in Ioi (0 : ℝ), (((w - y) / (2 * τ) * gaussDensity τ (w - y) : ℝ) : ℂ) * lineFn Λ X w) -
        ℓ * halfGaussTransform τ (lineFn Λ X) y‖ ≤
      SaddleData.mass (lineF Λ X) τ a δ ℓ * (32 * Real.sqrt τ * (4 * B / η) +
        (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 + 10) / (2 * τ) *
          powerTail (K) η τ *
          (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 + 1) +
        (1 + B) *
          powerFar (K) (B) τ (horizontalSlope X).re) := by
  have hτ := h.hτ
  have h2τ : 0 < 2 * τ := by positivity
  obtain ⟨hW9, hWX⟩ := h.hW
  obtain ⟨W, hWdef⟩ : ∃ W, W = 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 := ⟨_, rfl⟩
  rw [← hWdef] at hW9 hWX ⊢
  rw [h.slope_sub_eq]
  obtain ⟨P, hPdef⟩ : ∃ P, P = SaddleData.mass (lineF Λ X) τ a δ ℓ := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := hPdef ▸ SaddleData.mass_nonneg _ _ _ _ _
  rw [← hPdef]
  let u : ℂ := (a : ℂ) + (δ : ℂ) * I
  let m : ℝ → ℂ := fun w => ((w : ℂ) - u) / (2 * (τ : ℂ)) *
    ((gaussDensity τ (w - y) : ℂ) * lineFn Λ X w)
  have hmint : Integrable m := by
    have hd := (integrable_slope h.model hτ X y).sub (h.gauss_integrable.const_mul ℓ)
    refine hd.congr (Eventually.of_forall fun w => ?_)
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    simp only [Pi.sub_apply, m, u]
    rw [h.data.hu]
    push_cast
    field_simp
    ring
  have hsplit := setIntegral_Ioi_split (by norm_num : (0 : ℝ) ≤ 9 / 2) hW9 hmint.integrableOn
  have hΩ0 : 0 ≤ (W + 10) / (2 * τ) := by
    have : 0 ≤ W := by linarith only [hW9]
    positivity
  have hnc : ‖(2 : ℂ) * (τ : ℂ)‖ = 2 * τ := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  have hδa := abs_le.mp h.hδ
  have hη8 := h.hη8
  have hηp := h.hη
  have ha1 : 11 * η ≤ a := by linarith only [h.ha1, h.model.hd]
  have ha2 := h.ha2
  -- The weight on the head rectangle.
  have hΩb : ∀ x ∈ Icc (0 : ℝ) (9 / 2), ∀ v ∈ [[(0 : ℝ), δ]],
      ‖((x : ℂ) + (v : ℂ) * I - ((a : ℂ) + (δ : ℂ) * I)) / (2 * (τ : ℂ))‖ ≤ (W + 10) / (2 * τ) := by
    intro x hx v hv
    rw [norm_div, hnc]
    apply div_le_div_of_nonneg_right _ h2τ.le
    have he : (x : ℂ) + (v : ℂ) * I - ((a : ℂ) + (δ : ℂ) * I) =
        ((x - a : ℝ) : ℂ) + ((v - δ : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have hv' : |v - δ| ≤ 1 := by
      rcases Set.mem_uIcc.mp hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact abs_le.mpr ⟨by linarith only [h1, h2, hδa.1, hδa.2, hη8], by linarith only [h2, hηp]⟩
      · exact abs_le.mpr ⟨by linarith only [h1, h2, hδa.1, hηp, hη8],
          by linarith only [h1, h2, hδa.1, hδa.2, hη8]⟩
    have hx' : |x - a| ≤ 9 / 2 := abs_le.mpr ⟨by linarith only [hx.1, ha2],
      by linarith only [hx.2, ha1, hηp]⟩
    linarith only [hv', hx', hW9]
  have hhead := h.data.norm_integral_moment_le hΩ0 hΩb
  have hhead_eq : (∫ x in (0 : ℝ)..(9 / 2), ((x : ℂ) - ((a : ℂ) + (δ : ℂ) * I)) / (2 * (τ : ℂ)) *
      (gaussKernel τ ((x : ℂ) - (y : ℂ)) * lineF Λ X (x : ℂ))) = ∫ w in Ioc (0 : ℝ) (9 / 2), m w := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine setIntegral_congr_fun measurableSet_Ioc fun w _ => ?_
    simp only [m, u]
    rw [← Complex.ofReal_sub, gaussKernel_ofReal, lineF_ofReal]
  rw [hhead_eq, ← hPdef] at hhead
  have hT0 : 0 ≤ powerTail (K) η τ := by
    have := h.hK_pos.le
    unfold powerTail
    positivity
  have htail : K * ((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(η ^ 2 / (8 * τ)))) = powerTail (K) η τ := rfl
  rw [htail] at hhead
  have hmid : ‖∫ w in Ioc (9 / 2 : ℝ) W, m w‖ ≤
      (W + 10) / (2 * τ) * (P * powerTail (K) η τ) * (W - 9 / 2) := by
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (9 / 2 : ℝ) W) (f := m)
      (C := (W + 10) / (2 * τ) * (P * powerTail (K) η τ)) measure_Ioc_lt_top
      (fun w hw => by
        simp only [m]
        rw [norm_mul, norm_gauss_mul τ y w hτ]
        refine mul_le_mul ?_ ?_ (by have := (gaussDensity_pos hτ (w - y)).le; positivity) hΩ0
        · rw [norm_div, hnc]
          apply div_le_div_of_nonneg_right _ h2τ.le
          have he : (w : ℂ) - u = ((w - a : ℝ) : ℂ) + ((-δ : ℝ) : ℂ) * I := by
            simp only [u]
            push_cast
            ring
          rw [he]
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
          have hx' : |w - a| ≤ W + 1 := abs_le.mpr ⟨by linarith only [hw.1, ha2, hW9],
            by linarith only [hw.2, ha1, hηp]⟩
          linarith only [hx', h.hδ, hη8]
        · rw [hPdef]
          exact h.gauss_mul_norm_right_le hw.1.le (hw.2.trans hWX))
    rwa [Real.volume_real_Ioc_of_le hW9] at hb
  have hBpos := h.hB_pos
  have hhs1 : 1 ≤ ‖horizontalSlope X‖ := by
    have := Complex.abs_re_le_norm (horizontalSlope X)
    have hab := le_abs_self (horizontalSlope X).re
    linarith only [this, hab, h.hα]
  have hfar : ‖∫ w in Ioi W, m w‖ ≤ (1 + B) *
      (P * powerFar (K) (B) τ (horizontalSlope X).re) := by
    have hint := (integrable_weight h.model hτ X y ‖horizontalSlope X‖).const_mul (1 + B)
    have hfa := h.far_terms_le.1
    rw [← hWdef, ← hPdef] at hfa
    have hle : ‖∫ w in Ioi W, m w‖ ≤ ∫ w in Ioi W, (1 + B) *
        ((|(w - y) / (2 * τ)| + ‖horizontalSlope X‖) * gaussDensity τ (w - y) * ‖lineFn Λ X w‖) := by
      refine norm_integral_le_of_norm_le hint.integrableOn (Eventually.of_forall fun w => ?_)
      simp only [m]
      rw [norm_mul, norm_gauss_mul τ y w hτ]
      have hg := (gaussDensity_pos hτ (w - y)).le
      have hN := norm_nonneg (lineFn Λ X w)
      have hweight : ‖((w : ℂ) - u) / (2 * (τ : ℂ))‖ ≤
          (1 + B) * (|(w - y) / (2 * τ)| + ‖horizontalSlope X‖) := by
        have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
        have he : ((w : ℂ) - u) / (2 * (τ : ℂ)) = (((w - y) / (2 * τ) : ℝ) : ℂ) - ℓ := by
          simp only [u]
          rw [h.data.hu]
          push_cast
          field_simp
          ring
        rw [he]
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
        have hℓn : ‖ℓ‖ ≤ ‖horizontalSlope X‖ + B := by
          have := norm_add_le (ℓ - horizontalSlope X) (horizontalSlope X)
          rw [sub_add_cancel] at this
          linarith only [this, h.hℓ]
        have ha0 := abs_nonneg ((w - y) / (2 * τ))
        nlinarith only [hℓn, hBpos, hhs1, ha0, mul_nonneg hBpos.le ha0]
      calc
        _ ≤ ((1 + B) * (|(w - y) / (2 * τ)| + ‖horizontalSlope X‖)) *
            (gaussDensity τ (w - y) * ‖lineFn Λ X w‖) :=
          mul_le_mul_of_nonneg_right hweight (mul_nonneg hg hN)
        _ = _ := by ring
    refine hle.trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hfa (by linarith only [hBpos])
  have hδ1 : 9 / 2 + 2 * |δ| + (W - 9 / 2) ≤ W + 1 := by
    have := h.hδ
    linarith only [this, hη8]
  rw [hsplit]
  refine (norm_add₃_le).trans ?_
  calc
    _ ≤ P * (32 * Real.sqrt τ * (4 * B / η) +
          (W + 10) / (2 * τ) * powerTail (K) η τ * (9 / 2 + 2 * |δ|)) +
        (W + 10) / (2 * τ) * (P * powerTail (K) η τ) * (W - 9 / 2) +
        (1 + B) *
          (P * powerFar (K) (B) τ (horizontalSlope X).re) :=
      add_le_add (add_le_add hhead hmid) hfar
    _ = P * (32 * Real.sqrt τ * (4 * B / η) +
          (W + 10) / (2 * τ) * powerTail (K) η τ * (9 / 2 + 2 * |δ| + (W - 9 / 2)) +
          (1 + B) *
            powerFar (K) (B) τ (horizontalSlope X).re) := by ring
    _ ≤ _ := by
      gcongr

/-- Inside the Gaussian range, reflection gains `e^{−2yα}`. -/
theorem opposite_range_le (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) (hy : 0 ≤ y) :
    (∫ w in Ioc (0 : ℝ) (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
        gaussDensity τ (w + y) * ‖lineFn Λ X w‖) ≤
      SaddleData.mass (lineF Λ X) τ a δ ℓ * (K * Real.exp 1 *
        Real.exp (-(2 * y * (horizontalSlope X).re) +
          τ * (B + 1 / 8) ^ 2)) := by
  have hτ := h.hτ
  obtain ⟨hW9, hWX⟩ := h.hW
  obtain ⟨W, hWdef⟩ : ∃ W, W = 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 := ⟨_, rfl⟩
  rw [← hWdef] at hW9 hWX ⊢
  obtain ⟨c, hcdef⟩ : ∃ c, c = (horizontalSlope X).re + 1 / 8 := ⟨_, rfl⟩
  have ha2 := h.ha2
  obtain ⟨N, hNdef⟩ : ∃ N, N = ‖lineF Λ X ((a : ℂ) + (δ : ℂ) * I)‖ := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := hNdef ▸ norm_nonneg _
  have hK := h.hK_pos.le
  -- The whole-line mass of the exponential majorant.
  have hint := integrable_gaussDensity_sub_mul_rexp hτ (-y) c
  have hmaj : (∫ w in Ioc (0 : ℝ) W, gaussDensity τ (w + y) * ‖lineFn Λ X w‖) ≤
      K * N * Real.exp 1 * Real.exp (-(a * c)) * Real.exp (-y * c + τ * c ^ 2) := by
    have hlow : (∫ w in Ioc (0 : ℝ) W, gaussDensity τ (w + y) * ‖lineFn Λ X w‖) ≤
        ∫ w in Ioc (0 : ℝ) W, K * N * Real.exp 1 * Real.exp (-(a * c)) *
          (gaussDensity τ (w - -y) * Real.exp (w * c)) := by
      refine setIntegral_mono_on ?_ (hint.const_mul _).integrableOn measurableSet_Ioc ?_
      · have hc : Continuous fun w => gaussDensity τ (w + y) * ‖lineFn Λ X w‖ :=
          ((continuous_gaussDensity τ).comp (by fun_prop)).mul (h.model.continuous_lineFn X).norm
        exact hc.integrableOn_Ioc
      · intro w hw
        have hsrc : ‖lineFn Λ X w‖ ≤ K * N * Real.exp 1 * Real.exp (-(a * c)) *
            Real.exp (w * c) := by
          have hexpsplit : K * N * Real.exp 1 * Real.exp (-(a * c)) *
              Real.exp (w * c) = K * N * Real.exp (1 + (w - a) * c) := by
            rw [Real.exp_add, show (w - a) * c = -(a * c) + w * c by ring, Real.exp_add]
            ring
          rw [hexpsplit]
          rcases le_or_gt w (9 / 2) with hw2 | hw2
          · have hs := h.data.hsrc w ⟨hw.1.le, hw2⟩ 0 left_mem_uIcc
            have he : ((w : ℂ) + ((0 : ℝ) : ℂ) * I) = (w : ℂ) := by simp
            rw [he, lineF_ofReal, ← hNdef] at hs
            refine hs.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg hK hN0))
            rw [hcdef]
            nlinarith only [hw.1, ha2]
          · have hs := h.norm_right_le hw2.le (hw.2.trans hWX)
            rw [← hNdef, ← hcdef] at hs
            refine hs.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg hK hN0))
            linarith only
        have hg := (gaussDensity_pos hτ (w + y)).le
        rw [sub_neg_eq_add]
        calc
          _ ≤ gaussDensity τ (w + y) * (K * N * Real.exp 1 * Real.exp (-(a * c)) *
              Real.exp (w * c)) := mul_le_mul_of_nonneg_left hsrc hg
          _ = _ := by ring
    refine hlow.trans ?_
    have hall : (∫ w in Ioc (0 : ℝ) W, K * N * Real.exp 1 * Real.exp (-(a * c)) *
        (gaussDensity τ (w - -y) * Real.exp (w * c))) ≤
        ∫ w, K * N * Real.exp 1 * Real.exp (-(a * c)) *
          (gaussDensity τ (w - -y) * Real.exp (w * c)) :=
      setIntegral_le_integral (hint.const_mul _) (Eventually.of_forall fun w => by
        have := gaussDensity_sub_mul_rexp_nonneg hτ (-y) c w
        positivity)
    refine hall.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_gaussDensity_sub_mul_rexp hτ]
  -- The exponent against the saddle mass.
  have hre := h.data.re_eq
  have hA := h.data.hA
  have hexp : Real.exp (-(a * c)) * Real.exp (-y * c + τ * c ^ 2) ≤
      Real.exp (-(τ * (ℓ.re ^ 2 - ℓ.im ^ 2))) *
        Real.exp (-(2 * y * (horizontalSlope X).re) +
          τ * (B + 1 / 8) ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hre]
    have hsq : (c - ℓ.re) ^ 2 ≤ (B + 1 / 8) ^ 2 := by
      rw [← sq_abs]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      have hh := abs_le.mp hA
      rw [hcdef]
      exact abs_le.mpr ⟨by linarith only [hh.2], by linarith only [hh.1]⟩
    have hτ0 := hτ.le
    have hyc : y * (horizontalSlope X).re ≤ y * c := by
      rw [hcdef]
      nlinarith only [hy]
    nlinarith only [mul_le_mul_of_nonneg_left hsq hτ0, mul_nonneg hτ0 (sq_nonneg ℓ.im), hyc]
  have hmass : SaddleData.mass (lineF Λ X) τ a δ ℓ = N * Real.exp (-(τ * (ℓ.re ^ 2 - ℓ.im ^ 2))) := by
    rw [hNdef]
    rfl
  rw [hmass]
  calc
    _ ≤ K * N * Real.exp 1 * Real.exp (-(a * c)) * Real.exp (-y * c + τ * c ^ 2) := hmaj
    _ = K * N * Real.exp 1 *
        (Real.exp (-(a * c)) * Real.exp (-y * c + τ * c ^ 2)) := by ring
    _ ≤ K * N * Real.exp 1 *
        (Real.exp (-(τ * (ℓ.re ^ 2 - ℓ.im ^ 2))) *
          Real.exp (-(2 * y * (horizontalSlope X).re) +
            τ * (B + 1 / 8) ^ 2)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

/-- Beyond the range, reflection does not raise the mass. -/
theorem opposite_far_le (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) (hy : 0 ≤ y) :
    (∫ w in Ioi (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
        gaussDensity τ (w + y) * ‖lineFn Λ X w‖) ≤
      SaddleData.mass (lineF Λ X) τ a δ ℓ *
        powerFar (K) (B) τ (horizontalSlope X).re := by
  have hτ := h.hτ
  obtain ⟨hW9, _⟩ := h.hW
  have hW0 : 0 ≤ 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 := by
    linarith only [hW9]
  refine le_trans ?_ h.far_terms_le.2
  have hi1 : Integrable (fun w => gaussDensity τ (w - -y) * ‖lineFn Λ X w‖) := by
    refine (integrable_gaussDensity_sub_mul hτ (h.model.continuous_lineFn X)
      (h.model.integrable hτ) (-y)).norm.congr (Eventually.of_forall fun w => ?_)
    exact norm_gauss_mul τ (-y) w hτ _
  have hi2 : Integrable (fun w => gaussDensity τ (w - y) * ‖lineFn Λ X w‖) := by
    refine (integrable_gaussDensity_sub_mul hτ (h.model.continuous_lineFn X)
      (h.model.integrable hτ) y).norm.congr (Eventually.of_forall fun w => ?_)
    exact norm_gauss_mul τ y w hτ _
  simp only [sub_neg_eq_add] at hi1
  refine setIntegral_mono_on hi1.integrableOn hi2.integrableOn measurableSet_Ioi fun w hw => ?_
  have hg := gaussDensity_add_le_of_lower_bound (b := 0) hτ hy (hW0.trans (le_of_lt hw))
  have hm := mul_le_mul_of_nonneg_right hg (norm_nonneg (lineFn Λ X w))
  simpa only [zero_mul, zero_div, neg_zero, Real.exp_zero, one_mul] using hm

/-- **The opposite half.** Reflection gains `e^{−2yα}` over the whole Gaussian range. -/
theorem norm_halfGauss_opposite_le (h : PowerSaddle Λ d η B K t X τ y a δ ℓ) (hy : 0 ≤ y) :
    ‖halfGaussTransform τ (lineFn Λ X) (-y)‖ ≤
      SaddleData.mass (lineF Λ X) τ a δ ℓ * (K * Real.exp 1 *
        Real.exp (-(2 * y * (horizontalSlope X).re) +
          τ * (B + 1 / 8) ^ 2) +
        powerFar (K) (B) τ (horizontalSlope X).re) := by
  have hτ := h.hτ
  obtain ⟨hW9, _⟩ := h.hW
  have hW0 : 0 ≤ 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 := by
    linarith only [hW9]
  have hQ := norm_halfGaussTransform_le_three_masses (h.model.continuous_lineFn X) (y := -y) hτ
    (le_refl (0 : ℝ)) hW0 (h.model.integrable hτ)
  simp only [sub_neg_eq_add, Ioc_self, Measure.restrict_empty, integral_zero_measure, zero_add] at hQ
  refine hQ.trans ?_
  rw [mul_add]
  exact add_le_add (h.opposite_range_le hy) (h.opposite_far_le hy)

end PowerSaddle

end

end GaloisForLFunctions.ZeroConfigurationGeometry

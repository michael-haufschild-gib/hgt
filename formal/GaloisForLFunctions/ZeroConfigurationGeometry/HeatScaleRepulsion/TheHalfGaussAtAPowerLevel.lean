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

Each error is explicit in `τ`, `η`, `α` and the level.
-/

set_option autoImplicit false

open Complex Set Metric Filter Topology MeasureTheory
open scoped Interval
open _root_.RHTower _root_.RHTower.DeBruijn

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- `ξ` in the horizontal coordinate. -/
def xiF (X : ℝ) (z : ℂ) : ℂ := xi (1 / 2 + z + I * X)

theorem xiF_ofReal (X w : ℝ) : xiF X (w : ℂ) = xiLine X w := rfl

theorem differentiable_xiF (X : ℝ) : Differentiable ℂ (xiF X) :=
  xi_differentiable.comp (by fun_prop)

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
structure PowerSaddle (η E T t X τ y a δ : ℝ) (ℓ : ℂ) : Prop where
  typ : zetaTypicalHeight η E T t
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
  hy1 : -(4 * η) ≤ y
  hy2 : y ≤ 1 / 2
  hB : powerSlopeError E η T ≤ η * (horizontalSlope X).re / 400
  data : SaddleData (xiF X) τ y a δ ℓ (horizontalSlope X).re (powerSlopeError E η T) η (9 / 2)
    (4 * powerSlopeError E η T / η) (powerRatio E η T)
  hℓ : ‖ℓ - horizontalSlope X‖ ≤ powerSlopeError E η T
  ha1 : 11 * η ≤ a
  ha2 : a ≤ 2
  hδ : |δ| ≤ η / 4

/-- The window hypothesis of the saddle, from the second-order model of `ξ`. -/
private theorem hwin_of_box {η E T t X a δ : ℝ} {ℓ : ℂ} (typ : zetaTypicalHeight η E T t)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hT : 8 ≤ T) (hE : 0 ≤ E) (hX : 1000 ≤ X)
    (hXt : |X - t| ≤ η / 2) (hℓ : ℓ = lineLogDeriv X ((a : ℂ) + (δ : ℂ) * I))
    (ha1 : 4 * η ≤ a) (ha2 : a ≤ 2) (hδ : |δ| ≤ η / 4) {v : ℝ} (hv : v ∈ Icc (-η) η) :
    ‖xiF X ((a : ℂ) + (δ : ℂ) * I + (v : ℂ)) -
        xiF X ((a : ℂ) + (δ : ℂ) * I) * Complex.exp ((v : ℂ) * ℓ)‖ ≤
      ‖xiF X ((a : ℂ) + (δ : ℂ) * I)‖ * Real.exp (v * ℓ.re) *
        (Real.exp (4 * powerSlopeError E η T / η * v ^ 2) - 1) := by
  refine norm_window_model_le typ hη hη8 hT hE hX hXt hℓ fun x hx => ?_
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
theorem exists_powerSaddle {η E T t X τ y : ℝ} (typ : zetaTypicalHeight η E T t)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hT : 8 ≤ T) (hE : 0 ≤ E) (hX : 1000 ≤ X)
    (hα : 8 ≤ (horizontalSlope X).re) (hαη : 8 ≤ η * (horizontalSlope X).re)
    (hXt : |X - t| ≤ η / 2) (hτ : 0 < τ) (hτ8 : τ ≤ 1 / 8)
    (hc1 : 16 * η ≤ 2 * τ * (horizontalSlope X).re) (hc2 : 2 * τ * (horizontalSlope X).re ≤ 1)
    (hy1 : -(4 * η) ≤ y) (hy2 : y ≤ 1 / 2)
    (hB : powerSlopeError E η T ≤ η * (horizontalSlope X).re / 400) :
    ∃ (a δ : ℝ) (ℓ : ℂ), PowerSaddle η E T t X τ y a δ ℓ ∧
      ℓ = lineLogDeriv X ((a : ℂ) + (δ : ℂ) * I) := by
  obtain ⟨α, hαdef⟩ : ∃ α, α = (horizontalSlope X).re := ⟨_, rfl⟩
  rw [← hαdef] at hα hαη hc1 hc2 hB
  obtain ⟨B, hBdef⟩ : ∃ B, B = powerSlopeError E η T := ⟨_, rfl⟩
  rw [← hBdef] at hB
  have hBpos : 0 < B := hBdef ▸ powerSlopeError_pos (η := η) hE (by linarith only [hT])
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
  have hsub : closedBall ((y : ℂ) + 2 * (τ : ℂ) * horizontalSlope X) (2 * τ * powerSlopeError E η T) ⊆
      innerBox η := by
    rw [← hBdef]
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hball w hw
    refine ⟨by linarith only [h1, hy1, hc1, hη], by linarith only [h2, hy2, hc2, hη8], ?_⟩
    exact h3.trans (by linarith only [hη])
  have hlip : 2 * τ * (4 * powerSlopeError E η T / η) ≤ 1 / 2 := by
    rw [← hBdef]
    have he : 2 * τ * (4 * B / η) = 4 * (2 * τ * B) / η := by ring
    rw [he, div_le_iff₀ hη]
    linarith only [h2τB, hη]
  obtain ⟨u, hu, hfix⟩ := exists_saddle_fixedPoint typ hη hη8 hT hE hX hXt hτ hsub hlip
  rw [← hBdef] at hu
  obtain ⟨hu1, hu2, hu3⟩ := hball u hu
  have hu_eq : (u.re : ℂ) + (u.im : ℂ) * I = u := Complex.re_add_im u
  have hreg : u ∈ saddleRegion η t X := by
    have h3' := abs_le.mp hu3
    have hXt'' := abs_le.mp hXt
    refine ⟨by linarith only [hu1, hy1, hc1, hη], by linarith only [hu2, hy2, hc2, hη8],
      abs_le.mpr ⟨?_, ?_⟩⟩
    · linarith only [h3'.1, hXt''.1, hη]
    · linarith only [h3'.2, hXt''.2, hη]
  have hXt' : |X - t| ≤ η := hXt.trans (by linarith only [hη])
  have hℓB : ‖lineLogDeriv X u - horizontalSlope X‖ ≤ B := by
    rw [hBdef]
    exact norm_lineLogDeriv_sub_le typ hη (by linarith only [hη8]) hT hE hX hXt' hreg
  have ha1 : 11 * η ≤ u.re := by linarith only [hu1, hy1, hc1, hη]
  have ha2 : u.re ≤ 2 := by linarith only [hu2, hy2, hc2, hη8]
  have hδ : |u.im| ≤ η / 4 := hu3.trans (by linarith only [hη])
  have hℓ' : lineLogDeriv X u = lineLogDeriv X ((u.re : ℂ) + (u.im : ℂ) * I) := by rw [hu_eq]
  refine ⟨u.re, u.im, lineLogDeriv X u, ?_, hℓ'⟩
  have hsrc : ∀ x ∈ Icc (0 : ℝ) (9 / 2), ∀ v ∈ [[(0 : ℝ), u.im]],
      ‖xiF X ((x : ℂ) + (v : ℂ) * I)‖ ≤
        powerRatio E η T * ‖xiF X ((u.re : ℂ) + (u.im : ℂ) * I)‖ *
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
    have hval := norm_xi_le_anchor (s₀ := (1 / 2 + u + I * X : ℂ))
      (s₁ := (1 / 2 + ((x : ℂ) + (v : ℂ) * I) + I * X : ℂ)) typ hη (by linarith only [hη8]) hT hE hX
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
    { typ := typ, hη := hη, hη8 := hη8, hT := hT, hE := hE, hX := hX,
      hα := hαdef ▸ hα, hαη := hαdef ▸ hαη, hXt := hXt, hτ := hτ, hτ8 := hτ8,
      hc1 := hαdef ▸ hc1, hc2 := hαdef ▸ hc2, hy1 := hy1, hy2 := hy2,
      hB := by rw [← hBdef, ← hαdef]; exact hB, data := ?_, hℓ := by rw [← hBdef]; exact hℓB,
      ha1 := ha1, ha2 := ha2, hδ := hδ }
  refine
    { hF := differentiable_xiF X, hτ := hτ, hu := by rw [hu_eq]; exact hfix,
      hA := ?_, hΛ := ?_, hρ := hη, hlow := by linarith only [ha1, hη],
      hhigh := by linarith only [ha2, hη8],
      hB0 := ?_, hB := ?_, hK := powerRatio_nonneg (by linarith only [hT]),
      hwin := fun v hv => hwin_of_box typ hη hη8 hT hE hX hXt hℓ'
        (by linarith only [ha1, hη]) ha2 hδ hv,
      hsrc := hsrc }
  · rw [← hBdef, ← hαdef]
    have hre := (Complex.abs_re_le_norm (lineLogDeriv X u - horizontalSlope X)).trans hℓB
    rwa [Complex.sub_re, ← hαdef] at hre
  · rw [← hBdef]
    linarith only [h2τB, hη]
  · rw [← hBdef]
    positivity
  · rw [← hBdef]
    have he : 8 * τ * (4 * B / η) = 16 * (2 * τ * B) / η := by ring
    rw [he, div_le_iff₀ hη]
    linarith only [h2τB, hη]

namespace PowerSaddle

variable {η E T t X τ y a δ : ℝ} {ℓ : ℂ}

theorem hB_pos (h : PowerSaddle η E T t X τ y a δ ℓ) : 0 < powerSlopeError E η T :=
  powerSlopeError_pos (η := η) h.hE (by linarith only [h.hT])

theorem hK_pos (h : PowerSaddle η E T t X τ y a δ ℓ) : 0 < powerRatio E η T := by
  have hT0 : 0 < T := by linarith only [h.hT]
  have := Real.rpow_pos_of_pos hT0 E
  unfold powerRatio
  positivity

theorem hτ_small (h : PowerSaddle η E T t X τ y a δ ℓ) : τ ≤ η / 16 := by
  have h1 := mul_le_mul_of_nonneg_left h.hαη (show 0 ≤ 2 * τ by linarith only [h.hτ])
  have h2 := mul_le_mul_of_nonneg_left h.hc2 h.hη.le
  nlinarith only [h1, h2]

theorem hτB (h : PowerSaddle η E T t X τ y a δ ℓ) : 2 * τ * powerSlopeError E η T ≤ η / 400 := by
  have h1 := mul_le_mul_of_nonneg_left h.hB (show 0 ≤ 2 * τ by linarith only [h.hτ])
  have h2 := mul_le_mul_of_nonneg_left h.hc2 h.hη.le
  nlinarith only [h1, h2]

theorem hy_abs (h : PowerSaddle η E T t X τ y a δ ℓ) : |y| ≤ 1 / 2 :=
  abs_le.mpr ⟨by linarith only [h.hy1, h.hη8], h.hy2⟩

/-- The right end of the Gaussian range. -/
theorem hW (h : PowerSaddle η E T t X τ y a δ ℓ) :
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
theorem norm_nine_halves_le (h : PowerSaddle η E T t X τ y a δ ℓ) :
    ‖xiLine X (9 / 2)‖ ≤ powerRatio E η T * ‖xiF X ((a : ℂ) + (δ : ℂ) * I)‖ *
      Real.exp ((9 / 2 - a) * (horizontalSlope X).re) := by
  have hs := h.data.hsrc (9 / 2) ⟨by norm_num, le_rfl⟩ 0 left_mem_uIcc
  have he : (((9 / 2 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) = ((9 / 2 : ℝ) : ℂ) := by simp
  rw [he, xiF_ofReal] at hs
  exact hs

/-- Right of `9/2`, the slope rises by at most `1/8`. -/
theorem norm_right_le (h : PowerSaddle η E T t X τ y a δ ℓ) {w : ℝ} (hw : 9 / 2 ≤ w)
    (hwX : w ≤ X / 32 - 1 / 2) :
    ‖xiLine X w‖ ≤ powerRatio E η T * ‖xiF X ((a : ℂ) + (δ : ℂ) * I)‖ *
      Real.exp ((w - a) * ((horizontalSlope X).re + 1 / 8)) := by
  have hm := norm_xiLine_le_model (by linarith only [h.hX] : 200 ≤ X)
    (u := 9 / 2) (w := w) ⟨le_rfl, hw.trans hwX⟩ ⟨hw, hwX⟩
  rw [abs_of_nonneg (by linarith only [hw])] at hm
  have hn := h.norm_nine_halves_le
  have hK := h.hK_pos.le
  have hN := norm_nonneg (xiF X ((a : ℂ) + (δ : ℂ) * I))
  have ha2 := h.ha2
  calc
    _ ≤ (powerRatio E η T * ‖xiF X ((a : ℂ) + (δ : ℂ) * I)‖ *
          Real.exp ((9 / 2 - a) * (horizontalSlope X).re)) *
        Real.exp ((w - 9 / 2) * (horizontalSlope X).re) * Real.exp (1 / 8 * (w - 9 / 2)) := by
      refine hm.trans ?_
      gcongr
    _ = powerRatio E η T * ‖xiF X ((a : ℂ) + (δ : ℂ) * I)‖ *
        Real.exp ((9 / 2 - a) * (horizontalSlope X).re +
          (w - 9 / 2) * (horizontalSlope X).re + 1 / 8 * (w - 9 / 2)) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK hN)
      apply Real.exp_le_exp.mpr
      nlinarith only [ha2, hw]

/-- The mass of a real point right of the saddle window, relative to the mass of the saddle. -/
theorem gauss_mul_norm_right_le (h : PowerSaddle η E T t X τ y a δ ℓ) {w : ℝ} (hw : 9 / 2 ≤ w)
    (hwX : w ≤ X / 32 - 1 / 2) :
    gaussDensity τ (w - y) * ‖xiLine X w‖ ≤
      SaddleData.mass (xiF X) τ a δ ℓ * powerTail (powerRatio E η T) η τ := by
  have hτ := h.hτ
  have hA := h.data.hA
  have hA' : |ℓ.re - ((horizontalSlope X).re + 1 / 8)| ≤ powerSlopeError E η T + 1 / 8 := by
    have hh := abs_le.mp hA
    exact abs_le.mpr ⟨by linarith only [hh.1], by linarith only [hh.2]⟩
  have hsm := h.hτB
  have hτs := h.hτ_small
  have hΛ : 8 * τ * (powerSlopeError E η T + 1 / 8) ≤ η := by
    nlinarith only [hsm, hτs, h.hη]
  have hxa : η ≤ |w - a| := by
    rw [abs_of_nonneg (by linarith only [hw, h.ha2])]
    linarith only [hw, h.ha2, h.hη8]
  have hexpo := gauss_source_exponent_le (v := 0) hτ h.data.re_eq h.data.im_eq hA' hΛ h.hη.le
    (by rw [zero_pow two_ne_zero]; exact sq_nonneg δ) hxa
  have hsrc := h.norm_right_le hw hwX
  have hN := norm_nonneg (xiF X ((a : ℂ) + (δ : ℂ) * I))
  have hK := h.hK_pos.le
  have hc : 0 ≤ (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) := by positivity
  unfold gaussDensity powerTail SaddleData.mass
  calc
    _ ≤ ((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) * Real.exp (-((w - y) ^ 2 / (4 * τ)))) *
        (powerRatio E η T * ‖xiF X ((a : ℂ) + (δ : ℂ) * I)‖ *
          Real.exp ((w - a) * ((horizontalSlope X).re + 1 / 8))) :=
      mul_le_mul_of_nonneg_left hsrc (by positivity)
    _ = powerRatio E η T * ‖xiF X ((a : ℂ) + (δ : ℂ) * I)‖ * (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(((w - y) ^ 2 - 0 ^ 2) / (4 * τ)) +
          (w - a) * ((horizontalSlope X).re + 1 / 8)) := by
      rw [Real.exp_add, zero_pow two_ne_zero, sub_zero]
      ring
    _ ≤ powerRatio E η T * ‖xiF X ((a : ℂ) + (δ : ℂ) * I)‖ * (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(τ * (ℓ.re ^ 2 - ℓ.im ^ 2)) - η ^ 2 / (8 * τ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexpo) (mul_nonneg (mul_nonneg hK hN) hc)
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring

/-- The value at the real saddle, relative to the complex saddle. -/
theorem norm_real_saddle_le (h : PowerSaddle η E T t X τ y a δ ℓ) :
    ‖xiLine X (y + 2 * τ * (horizontalSlope X).re)‖ ≤
      powerRatio E η T * ‖xiF X ((a : ℂ) + (δ : ℂ) * I)‖ *
        Real.exp ((y + 2 * τ * (horizontalSlope X).re - a) * (horizontalSlope X).re) := by
  have hs := h.data.hsrc (y + 2 * τ * (horizontalSlope X).re)
    ⟨by linarith only [h.hy1, h.hc1, h.hη], by linarith only [h.hy2, h.hc2]⟩ 0 left_mem_uIcc
  have he : (((y + 2 * τ * (horizontalSlope X).re : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) =
      ((y + 2 * τ * (horizontalSlope X).re : ℝ) : ℂ) := by simp
  rw [he, xiF_ofReal] at hs
  exact hs

/-- The value at the real saddle controls `9/2` against the same anchor, with the same ratio. -/
theorem norm_nine_halves_le_real (h : PowerSaddle η E T t X τ y a δ ℓ) :
    ‖xiLine X (9 / 2)‖ ≤ powerRatio E η T * ‖xiLine X (y + 2 * τ * (horizontalSlope X).re)‖ *
      Real.exp ((9 / 2 - (y + 2 * τ * (horizontalSlope X).re)) * (horizontalSlope X).re) := by
  have hXt := abs_le.mp h.hXt
  have hη := h.hη
  have hη8 := h.hη8
  have hval := norm_xi_le_anchor (s₀ := (1 / 2 + ((y + 2 * τ * (horizontalSlope X).re : ℝ) : ℂ) + I * X : ℂ))
    (s₁ := (1 / 2 + ((9 / 2 : ℝ) : ℂ) + I * X : ℂ)) h.typ hη (by linarith only [hη8]) h.hT h.hE h.hX
    (by rw [re_point, Complex.ofReal_re]; linarith only [h.hy1, h.hc1, hη])
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
theorem far_terms_le (h : PowerSaddle η E T t X τ y a δ ℓ) :
    (∫ w in Ioi (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
        (|(w - y) / (2 * τ)| + ‖horizontalSlope X‖) * gaussDensity τ (w - y) * ‖xiLine X w‖) ≤
      SaddleData.mass (xiF X) τ a δ ℓ *
        powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re ∧
    (∫ w in Ioi (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
        gaussDensity τ (w - y) * ‖xiLine X w‖) ≤
      SaddleData.mass (xiF X) τ a δ ℓ *
        powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re := by
  have hX200 : (200 : ℝ) ≤ X := by linarith only [h.hX]
  have hα := h.hα
  have hK := h.hK_pos
  obtain ⟨hW9, hWX⟩ := h.hW
  obtain ⟨W, hWdef⟩ : ∃ W, W = 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 := ⟨_, rfl⟩
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, u₀ = y + 2 * τ * (horizontalSlope X).re := ⟨_, rfl⟩
  have hu₀2 : u₀ ≤ 9 / 2 := by
    rw [hu₀]
    linarith only [h.hy2, h.hc2]
  have hFW : ‖xiLine X (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)‖ ≤
      (Real.exp (Real.log (powerRatio E η T)) * ‖xiLine X (y + 2 * τ * (horizontalSlope X).re)‖) *
        Real.exp ((2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 -
          (y + 2 * τ * (horizontalSlope X).re)) * ((horizontalSlope X).re + 1 / 8)) := by
    rw [Real.exp_log hK, ← hWdef, ← hu₀]
    rw [← hWdef] at hW9 hWX
    have hm := norm_xiLine_le_model hX200 (u := 9 / 2) (w := W) ⟨le_rfl, hW9.trans hWX⟩ ⟨hW9, hWX⟩
    rw [abs_of_nonneg (by linarith only [hW9])] at hm
    have hn := h.norm_nine_halves_le_real
    rw [← hu₀] at hn
    have hN := norm_nonneg (xiLine X u₀)
    calc
      _ ≤ (powerRatio E η T * ‖xiLine X u₀‖ *
            Real.exp ((9 / 2 - u₀) * (horizontalSlope X).re)) *
          Real.exp ((W - 9 / 2) * (horizontalSlope X).re) * Real.exp (1 / 8 * (W - 9 / 2)) := by
        refine hm.trans ?_
        gcongr
      _ = powerRatio E η T * ‖xiLine X u₀‖ *
          Real.exp ((9 / 2 - u₀) * (horizontalSlope X).re +
            (W - 9 / 2) * (horizontalSlope X).re + 1 / 8 * (W - 9 / 2)) := by
        rw [Real.exp_add, Real.exp_add]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK.le hN)
        apply Real.exp_le_exp.mpr
        nlinarith only [hu₀2, hW9]
  obtain ⟨h1, h2, _⟩ := far_terms_le_of_bound (b := Real.log (powerRatio E η T)) h.hτ h.hτ8 hX200
    h.hy_abs (by linarith only [hα]) hW9 hFW
  rw [Real.exp_log hK] at h1 h2
  have hR := kklRC_nonneg h.hτ (by linarith only [hα] : 0 ≤ (horizontalSlope X).re)
  have hre := h.data.re_eq
  have hA := h.data.hA
  -- The real saddle against the complex saddle.
  have hcomp : (powerRatio E η T * ‖xiLine X (y + 2 * τ * (horizontalSlope X).re)‖) *
      Real.exp (-(τ * (horizontalSlope X).re ^ 2)) * kklRC τ (horizontalSlope X).re ≤
      SaddleData.mass (xiF X) τ a δ ℓ *
        powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re := by
    have hrs := h.norm_real_saddle_le
    have hN := norm_nonneg (xiF X ((a : ℂ) + (δ : ℂ) * I))
    have hexp : Real.exp ((y + 2 * τ * (horizontalSlope X).re - a) * (horizontalSlope X).re) *
        Real.exp (-(τ * (horizontalSlope X).re ^ 2)) ≤
        Real.exp (-(τ * (ℓ.re ^ 2 - ℓ.im ^ 2))) * Real.exp (τ * powerSlopeError E η T ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [hre]
      have hsq : (ℓ.re - (horizontalSlope X).re) ^ 2 ≤ powerSlopeError E η T ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hA 2
      have hτ0 := h.hτ.le
      nlinarith only [mul_le_mul_of_nonneg_left hsq hτ0, mul_nonneg hτ0 (sq_nonneg ℓ.im)]
    unfold SaddleData.mass powerFar
    calc
      _ ≤ (powerRatio E η T * (powerRatio E η T * ‖xiF X ((a : ℂ) + (δ : ℂ) * I)‖ *
            Real.exp ((y + 2 * τ * (horizontalSlope X).re - a) * (horizontalSlope X).re))) *
          Real.exp (-(τ * (horizontalSlope X).re ^ 2)) * kklRC τ (horizontalSlope X).re := by
        gcongr
      _ = powerRatio E η T ^ 2 * ‖xiF X ((a : ℂ) + (δ : ℂ) * I)‖ * kklRC τ (horizontalSlope X).re *
          (Real.exp ((y + 2 * τ * (horizontalSlope X).re - a) * (horizontalSlope X).re) *
            Real.exp (-(τ * (horizontalSlope X).re ^ 2))) := by ring
      _ ≤ powerRatio E η T ^ 2 * ‖xiF X ((a : ℂ) + (δ : ℂ) * I)‖ * kklRC τ (horizontalSlope X).re *
          (Real.exp (-(τ * (ℓ.re ^ 2 - ℓ.im ^ 2))) * Real.exp (τ * powerSlopeError E η T ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  exact ⟨h1.trans hcomp, h2.trans hcomp⟩

theorem gauss_integrable (h : PowerSaddle η E T t X τ y a δ ℓ) :
    Integrable (fun w => (gaussDensity τ (w - y) : ℂ) * xiLine X w) :=
  integrable_gaussDensity_sub_mul h.hτ (continuous_xiLine X) (integrable_exp_mul_norm_xiLine h.hτ X) y

private theorem integrable_slope {τ : ℝ} (hτ : 0 < τ) (X y : ℝ) :
    Integrable (fun w => (((w - y) / (2 * τ) * gaussDensity τ (w - y) : ℝ) : ℂ) * xiLine X w) := by
  have h2τ : 0 < 2 * τ := by positivity
  have hmaj := ((integrable_gaussDensity_sub_mul h2τ (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine h2τ X) y).norm).const_mul (2 / Real.sqrt τ)
  refine hmaj.mono' ?_ (Eventually.of_forall fun w => ?_)
  · have hg := continuous_gaussDensity τ
    have hc : Continuous fun w : ℝ => (((w - y) / (2 * τ) * gaussDensity τ (w - y) : ℝ) : ℂ) *
        xiLine X w := by
      refine (Complex.continuous_ofReal.comp ?_).mul (continuous_xiLine X)
      exact (by fun_prop : Continuous fun w : ℝ => (w - y) / (2 * τ)).mul
        (hg.comp (by fun_prop))
    exact hc.aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos h2τ,
      abs_of_pos (gaussDensity_pos hτ _), norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (gaussDensity_pos h2τ _), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (abs_div_mul_gaussDensity_le hτ (w - y)) (norm_nonneg _)

private theorem integrable_weight {τ : ℝ} (hτ : 0 < τ) (X y : ℝ) (A : ℝ) :
    Integrable (fun w => (|(w - y) / (2 * τ)| + A) * gaussDensity τ (w - y) * ‖xiLine X w‖) := by
  have h1 := (integrable_slope hτ X y).norm
  have h2 := ((integrable_gaussDensity_sub_mul hτ (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine hτ X) y).norm).const_mul A
  refine (h1.add h2).congr (Eventually.of_forall fun w => ?_)
  simp only [Pi.add_apply]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (gaussDensity_pos hτ _),
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussDensity_pos hτ _)]
  ring

/-- The first piece of the half transform, in the kernel of the saddle. -/
private theorem head_eq (y : ℝ) (X τ : ℝ) :
    (∫ x in (0 : ℝ)..(9 / 2), gaussKernel τ ((x : ℂ) - (y : ℂ)) * xiF X (x : ℂ)) =
      ∫ w in Ioc (0 : ℝ) (9 / 2), (gaussDensity τ (w - y) : ℂ) * xiLine X w := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  refine setIntegral_congr_fun measurableSet_Ioc fun w _ => ?_
  rw [← Complex.ofReal_sub, gaussKernel_ofReal, xiF_ofReal]

/-- **The saddle value of the half transform.** -/
theorem norm_halfGauss_sub_main_le (h : PowerSaddle η E T t X τ y a δ ℓ) :
    ‖halfGaussTransform τ (xiLine X) y -
        xiF X ((a : ℂ) + (δ : ℂ) * I) * Complex.exp (-((τ : ℂ) * ℓ ^ 2))‖ ≤
      SaddleData.mass (xiF X) τ a δ ℓ * (8 * τ * (4 * powerSlopeError E η T / η) +
        2 * Real.exp (-(η ^ 2 / (8 * τ))) +
        powerTail (powerRatio E η T) η τ *
          (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 + 1) +
        powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re) := by
  have hτ := h.hτ
  obtain ⟨hW9, hWX⟩ := h.hW
  obtain ⟨W, hWdef⟩ : ∃ W, W = 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 := ⟨_, rfl⟩
  rw [← hWdef] at hW9 hWX ⊢
  have hsplit := setIntegral_Ioi_split (by norm_num : (0 : ℝ) ≤ 9 / 2) hW9
    h.gauss_integrable.integrableOn
  obtain ⟨P, hPdef⟩ : ∃ P, P = SaddleData.mass (xiF X) τ a δ ℓ := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := hPdef ▸ SaddleData.mass_nonneg _ _ _ _ _
  rw [← hPdef]
  have hhead := h.data.norm_integral_sub_main_le
  rw [head_eq, ← hPdef] at hhead
  have hmid : ‖∫ w in Ioc (9 / 2 : ℝ) W, (gaussDensity τ (w - y) : ℂ) * xiLine X w‖ ≤
      P * powerTail (powerRatio E η T) η τ * (W - 9 / 2) := by
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (9 / 2 : ℝ) W)
      (f := fun w : ℝ => (gaussDensity τ (w - y) : ℂ) * xiLine X w)
      (C := P * powerTail (powerRatio E η T) η τ) measure_Ioc_lt_top (fun w hw => by
        rw [norm_gauss_mul τ y w hτ, hPdef]
        exact h.gauss_mul_norm_right_le hw.1.le (hw.2.trans hWX))
    rwa [Real.volume_real_Ioc_of_le hW9] at hb
  have hfar : ‖∫ w in Ioi W, (gaussDensity τ (w - y) : ℂ) * xiLine X w‖ ≤
      P * powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re := by
    have hn : ‖∫ w in Ioi W, (gaussDensity τ (w - y) : ℂ) * xiLine X w‖ ≤
        ∫ w in Ioi W, gaussDensity τ (w - y) * ‖xiLine X w‖ := by
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
  have hT0 : 0 ≤ powerTail (powerRatio E η T) η τ := by
    have := h.hK_pos.le
    unfold powerTail
    positivity
  unfold halfGaussTransform
  rw [hsplit]
  have hne : (∫ w in Ioc (0 : ℝ) (9 / 2), (gaussDensity τ (w - y) : ℂ) * xiLine X w) +
        (∫ w in Ioc (9 / 2 : ℝ) W, (gaussDensity τ (w - y) : ℂ) * xiLine X w) +
        (∫ w in Ioi W, (gaussDensity τ (w - y) : ℂ) * xiLine X w) -
        xiF X ((a : ℂ) + (δ : ℂ) * I) * Complex.exp (-((τ : ℂ) * ℓ ^ 2)) =
      ((∫ w in Ioc (0 : ℝ) (9 / 2), (gaussDensity τ (w - y) : ℂ) * xiLine X w) -
        xiF X ((a : ℂ) + (δ : ℂ) * I) * Complex.exp (-((τ : ℂ) * ℓ ^ 2))) +
        (∫ w in Ioc (9 / 2 : ℝ) W, (gaussDensity τ (w - y) : ℂ) * xiLine X w) +
        (∫ w in Ioi W, (gaussDensity τ (w - y) : ℂ) * xiLine X w) := by ring
  rw [hne]
  refine (norm_add₃_le).trans ?_
  have htail : powerRatio E η T * ((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(η ^ 2 / (8 * τ)))) = powerTail (powerRatio E η T) η τ := rfl
  rw [htail] at hhead
  calc
    _ ≤ P * (8 * τ * (4 * powerSlopeError E η T / η) + 2 * Real.exp (-(η ^ 2 / (8 * τ))) +
          powerTail (powerRatio E η T) η τ * (9 / 2 + 2 * |δ|)) +
        P * powerTail (powerRatio E η T) η τ * (W - 9 / 2) +
        P * powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re :=
      add_le_add (add_le_add hhead hmid) hfar
    _ = P * (8 * τ * (4 * powerSlopeError E η T / η) + 2 * Real.exp (-(η ^ 2 / (8 * τ))) +
          powerTail (powerRatio E η T) η τ * (9 / 2 + 2 * |δ| + (W - 9 / 2)) +
          powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re) := by ring
    _ ≤ _ := by
      gcongr

/-- The first moment about the saddle is the slope of the half transform. -/
private theorem slope_sub_eq (h : PowerSaddle η E T t X τ y a δ ℓ) :
    (∫ w in Ioi (0 : ℝ), (((w - y) / (2 * τ) * gaussDensity τ (w - y) : ℝ) : ℂ) * xiLine X w) -
        ℓ * halfGaussTransform τ (xiLine X) y =
      ∫ w in Ioi (0 : ℝ), ((w : ℂ) - ((a : ℂ) + (δ : ℂ) * I)) / (2 * (τ : ℂ)) *
        ((gaussDensity τ (w - y) : ℂ) * xiLine X w) := by
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast h.hτ.ne'
  unfold halfGaussTransform
  rw [← integral_const_mul, ← integral_sub (integrable_slope h.hτ X y).integrableOn
    (h.gauss_integrable.const_mul ℓ).integrableOn]
  refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
  rw [h.data.hu]
  push_cast
  field_simp
  ring

/-- **The slope of the half transform.** `Q′(y) − ℓ Q(y)` is small against the saddle mass. -/
theorem norm_halfGauss_slope_sub_le (h : PowerSaddle η E T t X τ y a δ ℓ) :
    ‖(∫ w in Ioi (0 : ℝ), (((w - y) / (2 * τ) * gaussDensity τ (w - y) : ℝ) : ℂ) * xiLine X w) -
        ℓ * halfGaussTransform τ (xiLine X) y‖ ≤
      SaddleData.mass (xiF X) τ a δ ℓ * (32 * Real.sqrt τ * (4 * powerSlopeError E η T / η) +
        (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 + 10) / (2 * τ) *
          powerTail (powerRatio E η T) η τ *
          (2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 + 1) +
        (1 + powerSlopeError E η T) *
          powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re) := by
  have hτ := h.hτ
  have h2τ : 0 < 2 * τ := by positivity
  obtain ⟨hW9, hWX⟩ := h.hW
  obtain ⟨W, hWdef⟩ : ∃ W, W = 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 := ⟨_, rfl⟩
  rw [← hWdef] at hW9 hWX ⊢
  rw [h.slope_sub_eq]
  obtain ⟨P, hPdef⟩ : ∃ P, P = SaddleData.mass (xiF X) τ a δ ℓ := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := hPdef ▸ SaddleData.mass_nonneg _ _ _ _ _
  rw [← hPdef]
  let u : ℂ := (a : ℂ) + (δ : ℂ) * I
  let m : ℝ → ℂ := fun w => ((w : ℂ) - u) / (2 * (τ : ℂ)) *
    ((gaussDensity τ (w - y) : ℂ) * xiLine X w)
  have hmint : Integrable m := by
    have hd := (integrable_slope hτ X y).sub (h.gauss_integrable.const_mul ℓ)
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
  have ha1 := h.ha1
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
      (gaussKernel τ ((x : ℂ) - (y : ℂ)) * xiF X (x : ℂ))) = ∫ w in Ioc (0 : ℝ) (9 / 2), m w := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine setIntegral_congr_fun measurableSet_Ioc fun w _ => ?_
    simp only [m, u]
    rw [← Complex.ofReal_sub, gaussKernel_ofReal, xiF_ofReal]
  rw [hhead_eq, ← hPdef] at hhead
  have hT0 : 0 ≤ powerTail (powerRatio E η T) η τ := by
    have := h.hK_pos.le
    unfold powerTail
    positivity
  have htail : powerRatio E η T * ((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(η ^ 2 / (8 * τ)))) = powerTail (powerRatio E η T) η τ := rfl
  rw [htail] at hhead
  have hmid : ‖∫ w in Ioc (9 / 2 : ℝ) W, m w‖ ≤
      (W + 10) / (2 * τ) * (P * powerTail (powerRatio E η T) η τ) * (W - 9 / 2) := by
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (9 / 2 : ℝ) W) (f := m)
      (C := (W + 10) / (2 * τ) * (P * powerTail (powerRatio E η T) η τ)) measure_Ioc_lt_top
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
  have hfar : ‖∫ w in Ioi W, m w‖ ≤ (1 + powerSlopeError E η T) *
      (P * powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re) := by
    have hint := (integrable_weight hτ X y ‖horizontalSlope X‖).const_mul (1 + powerSlopeError E η T)
    have hfa := h.far_terms_le.1
    rw [← hWdef, ← hPdef] at hfa
    have hle : ‖∫ w in Ioi W, m w‖ ≤ ∫ w in Ioi W, (1 + powerSlopeError E η T) *
        ((|(w - y) / (2 * τ)| + ‖horizontalSlope X‖) * gaussDensity τ (w - y) * ‖xiLine X w‖) := by
      refine norm_integral_le_of_norm_le hint.integrableOn (Eventually.of_forall fun w => ?_)
      simp only [m]
      rw [norm_mul, norm_gauss_mul τ y w hτ]
      have hg := (gaussDensity_pos hτ (w - y)).le
      have hN := norm_nonneg (xiLine X w)
      have hweight : ‖((w : ℂ) - u) / (2 * (τ : ℂ))‖ ≤
          (1 + powerSlopeError E η T) * (|(w - y) / (2 * τ)| + ‖horizontalSlope X‖) := by
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
        have hℓn : ‖ℓ‖ ≤ ‖horizontalSlope X‖ + powerSlopeError E η T := by
          have := norm_add_le (ℓ - horizontalSlope X) (horizontalSlope X)
          rw [sub_add_cancel] at this
          linarith only [this, h.hℓ]
        have ha0 := abs_nonneg ((w - y) / (2 * τ))
        nlinarith only [hℓn, hBpos, hhs1, ha0, mul_nonneg hBpos.le ha0]
      calc
        _ ≤ ((1 + powerSlopeError E η T) * (|(w - y) / (2 * τ)| + ‖horizontalSlope X‖)) *
            (gaussDensity τ (w - y) * ‖xiLine X w‖) :=
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
    _ ≤ P * (32 * Real.sqrt τ * (4 * powerSlopeError E η T / η) +
          (W + 10) / (2 * τ) * powerTail (powerRatio E η T) η τ * (9 / 2 + 2 * |δ|)) +
        (W + 10) / (2 * τ) * (P * powerTail (powerRatio E η T) η τ) * (W - 9 / 2) +
        (1 + powerSlopeError E η T) *
          (P * powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re) :=
      add_le_add (add_le_add hhead hmid) hfar
    _ = P * (32 * Real.sqrt τ * (4 * powerSlopeError E η T / η) +
          (W + 10) / (2 * τ) * powerTail (powerRatio E η T) η τ * (9 / 2 + 2 * |δ| + (W - 9 / 2)) +
          (1 + powerSlopeError E η T) *
            powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re) := by ring
    _ ≤ _ := by
      gcongr

/-- **The opposite half.** Reflection gains `e^{−2yα}` over the whole Gaussian range. -/
theorem norm_halfGauss_opposite_le (h : PowerSaddle η E T t X τ y a δ ℓ) (hy : 0 ≤ y) :
    ‖halfGaussTransform τ (xiLine X) (-y)‖ ≤
      SaddleData.mass (xiF X) τ a δ ℓ * (powerRatio E η T * Real.exp 1 *
        Real.exp (-(2 * y * (horizontalSlope X).re) +
          τ * (powerSlopeError E η T + 1 / 8) ^ 2) +
        powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re) := by
  have hτ := h.hτ
  obtain ⟨hW9, hWX⟩ := h.hW
  obtain ⟨W, hWdef⟩ : ∃ W, W = 2 * τ * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 := ⟨_, rfl⟩
  rw [← hWdef] at hW9 hWX
  obtain ⟨c, hcdef⟩ : ∃ c, c = (horizontalSlope X).re + 1 / 8 := ⟨_, rfl⟩
  have hα := h.hα
  have ha1 := h.ha1
  have ha2 := h.ha2
  have hηp := h.hη
  obtain ⟨N, hNdef⟩ : ∃ N, N = ‖xiF X ((a : ℂ) + (δ : ℂ) * I)‖ := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := hNdef ▸ norm_nonneg _
  have hK := h.hK_pos.le
  have hW0 : 0 ≤ W := by linarith only [hW9]
  have hQ := norm_halfGaussTransform_le_three_masses (continuous_xiLine X) (y := -y) hτ
    (le_refl (0 : ℝ)) hW0 (integrable_exp_mul_norm_xiLine hτ X)
  simp only [sub_neg_eq_add, Ioc_self, Measure.restrict_empty, integral_zero_measure, zero_add] at hQ
  -- The whole-line mass of the exponential majorant.
  have hint := integrable_gaussDensity_sub_mul_rexp hτ (-y) c
  have hmaj : (∫ w in Ioc (0 : ℝ) W, gaussDensity τ (w + y) * ‖xiLine X w‖) ≤
      powerRatio E η T * N * Real.exp 1 * Real.exp (-(a * c)) * Real.exp (-y * c + τ * c ^ 2) := by
    have hlow : (∫ w in Ioc (0 : ℝ) W, gaussDensity τ (w + y) * ‖xiLine X w‖) ≤
        ∫ w in Ioc (0 : ℝ) W, powerRatio E η T * N * Real.exp 1 * Real.exp (-(a * c)) *
          (gaussDensity τ (w - -y) * Real.exp (w * c)) := by
      refine setIntegral_mono_on ?_ (hint.const_mul _).integrableOn measurableSet_Ioc ?_
      · have hc : Continuous fun w => gaussDensity τ (w + y) * ‖xiLine X w‖ :=
          ((continuous_gaussDensity τ).comp (by fun_prop)).mul (continuous_xiLine X).norm
        exact hc.integrableOn_Ioc
      · intro w hw
        have hsrc : ‖xiLine X w‖ ≤ powerRatio E η T * N * Real.exp 1 * Real.exp (-(a * c)) *
            Real.exp (w * c) := by
          have hexpsplit : powerRatio E η T * N * Real.exp 1 * Real.exp (-(a * c)) *
              Real.exp (w * c) = powerRatio E η T * N * Real.exp (1 + (w - a) * c) := by
            rw [Real.exp_add, show (w - a) * c = -(a * c) + w * c by ring, Real.exp_add]
            ring
          rw [hexpsplit]
          rcases le_or_gt w (9 / 2) with hw2 | hw2
          · have hs := h.data.hsrc w ⟨hw.1.le, hw2⟩ 0 left_mem_uIcc
            have he : ((w : ℂ) + ((0 : ℝ) : ℂ) * I) = (w : ℂ) := by simp
            rw [he, xiF_ofReal, ← hNdef] at hs
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
          _ ≤ gaussDensity τ (w + y) * (powerRatio E η T * N * Real.exp 1 * Real.exp (-(a * c)) *
              Real.exp (w * c)) := mul_le_mul_of_nonneg_left hsrc hg
          _ = _ := by ring
    refine hlow.trans ?_
    have hall : (∫ w in Ioc (0 : ℝ) W, powerRatio E η T * N * Real.exp 1 * Real.exp (-(a * c)) *
        (gaussDensity τ (w - -y) * Real.exp (w * c))) ≤
        ∫ w, powerRatio E η T * N * Real.exp 1 * Real.exp (-(a * c)) *
          (gaussDensity τ (w - -y) * Real.exp (w * c)) :=
      setIntegral_le_integral (hint.const_mul _) (Eventually.of_forall fun w => by
        have := gaussDensity_sub_mul_rexp_nonneg hτ (-y) c w
        positivity)
    refine hall.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_gaussDensity_sub_mul_rexp hτ]
  -- Beyond the range, reflection does not raise the mass.
  have hfar : (∫ w in Ioi W, gaussDensity τ (w + y) * ‖xiLine X w‖) ≤
      SaddleData.mass (xiF X) τ a δ ℓ *
        powerFar (powerRatio E η T) (powerSlopeError E η T) τ (horizontalSlope X).re := by
    have hfa := h.far_terms_le.2
    rw [← hWdef] at hfa
    refine le_trans ?_ hfa
    have hi1 : Integrable (fun w => gaussDensity τ (w - -y) * ‖xiLine X w‖) := by
      refine (integrable_gaussDensity_sub_mul hτ (continuous_xiLine X)
        (integrable_exp_mul_norm_xiLine hτ X) (-y)).norm.congr (Eventually.of_forall fun w => ?_)
      exact norm_gauss_mul τ (-y) w hτ _
    have hi2 : Integrable (fun w => gaussDensity τ (w - y) * ‖xiLine X w‖) := by
      refine (integrable_gaussDensity_sub_mul hτ (continuous_xiLine X)
        (integrable_exp_mul_norm_xiLine hτ X) y).norm.congr (Eventually.of_forall fun w => ?_)
      exact norm_gauss_mul τ y w hτ _
    simp only [sub_neg_eq_add] at hi1
    refine setIntegral_mono_on hi1.integrableOn hi2.integrableOn measurableSet_Ioi fun w hw => ?_
    have hg := gaussDensity_add_le_of_lower_bound (b := 0) hτ hy (hW0.trans (show W < w from hw).le)
    have hm := mul_le_mul_of_nonneg_right hg (norm_nonneg (xiLine X w))
    simpa only [zero_mul, zero_div, neg_zero, Real.exp_zero, one_mul] using hm
  -- The exponent against the saddle mass.
  have hre := h.data.re_eq
  have hA := h.data.hA
  have hexp : Real.exp (-(a * c)) * Real.exp (-y * c + τ * c ^ 2) ≤
      Real.exp (-(τ * (ℓ.re ^ 2 - ℓ.im ^ 2))) *
        Real.exp (-(2 * y * (horizontalSlope X).re) +
          τ * (powerSlopeError E η T + 1 / 8) ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hre]
    have hsq : (c - ℓ.re) ^ 2 ≤ (powerSlopeError E η T + 1 / 8) ^ 2 := by
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
  refine hQ.trans ?_
  have hmass : SaddleData.mass (xiF X) τ a δ ℓ = N * Real.exp (-(τ * (ℓ.re ^ 2 - ℓ.im ^ 2))) := by
    rw [hNdef]
    rfl
  rw [mul_add]
  refine add_le_add ?_ hfar
  rw [hmass]
  calc
    _ ≤ powerRatio E η T * N * Real.exp 1 * Real.exp (-(a * c)) * Real.exp (-y * c + τ * c ^ 2) := hmaj
    _ = powerRatio E η T * N * Real.exp 1 *
        (Real.exp (-(a * c)) * Real.exp (-y * c + τ * c ^ 2)) := by ring
    _ ≤ powerRatio E η T * N * Real.exp 1 *
        (Real.exp (-(τ * (ℓ.re ^ 2 - ℓ.im ^ 2))) *
          Real.exp (-(2 * y * (horizontalSlope X).re) +
            τ * (powerSlopeError E η T + 1 / 8) ^ 2)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

end PowerSaddle

end

end GaloisForLFunctions.ZeroConfigurationGeometry

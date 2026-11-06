import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheZerosAreRealAtTheCriticalScale

/-!
# The crystal is formed at the critical scale

On almost all heights the zeros of `H_t` form a lattice from the critical scale on. For all `δ, ε > 0` there is `κ` such that for all large `T`, outside a set of `X ∈ [T, 2T]` of measure at most `δT`: if `x` is a real zero of `H_t` with `|x − X| ≤ κ/(2 log T)` and `7κ/log T ≤ t log(x/2π) ≤ 1/8`, then the next real zero `x'` exists and

`|(x' − x) · ½ log(x/2π) − π| ≤ ε`    (`exists_crystal_law`).

So `x' − x = (2π/log(x/2π))(1 + O(ε))`: the spacing is the mean spacing of the zeros, with a relative error that tends to zero as `τ = t log²X → ∞`. This is the nonlinear relaxation of the actual source at typical heights: above the scale of the local statistics the source has forgotten them.

**Mechanism.** At a fixed saddle `u = 2τα`, with `a = a(x)` and `ρ = ξ(½ + u + ix) e^{−ua + τa²}`, one has for `0 ≤ s ≤ 4/α`

`Q_{x+s}(0) = ρ e^{ias} + r(s)`,   `‖r(s)‖ ≤ ε₂ P₀ e^{−πs/4}`    (`quadrature_model`),

since the height derivative of `ξ` is `i` times its source derivative. Then `H_t(x + s) = 2 Re Q` is `2e^{−πs/4}(Re ρ cos αs − Im ρ sin αs)` up to `r`, and at a zero `Re ρ ≈ 0`. So `H_t(x + s)` has the sign of `∓ sin αs`, away from `αs ∈ πℤ`.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-- The rotation factor: `Re(ρ e^{ias}) = e^{−s Im a}(Re ρ cos(s Re a) − Im ρ sin(s Re a))`. -/
theorem re_mul_exp_I_slope (ρ a : ℂ) (s : ℝ) :
    (ρ * Complex.exp ((s : ℂ) * (I * a))).re =
      Real.exp (-(s * a.im)) * (ρ.re * Real.cos (s * a.re) - ρ.im * Real.sin (s * a.re)) := by
  have hre : ((s : ℂ) * (I * a)).re = -(s * a.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  have him : ((s : ℂ) * (I * a)).im = s * a.re := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [Complex.mul_re, Complex.exp_re, Complex.exp_im, hre, him]
  ring

/-- The sharper form of the scale law. -/
theorem crit_sqrt_le {q L α τ : ℝ} {j : ℕ} (hq : (10 : ℝ) ^ 4 ≤ q) (hL0 : 0 < L) (hαL : L / 8 ≤ α) (hτ : 0 < τ)
    (hR16 : critR q L j ≤ 1 / 16) (hτR : 2 * τ * α ≤ 46 * critR q L j / 10) (hLq : 10 * q ^ 2 ≤ L) :
    (critB q L j + 2) * Real.sqrt τ ≤ 4 / q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  set R := critR q L j with hRdef
  set B := critB q L j with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    unfold critB
    positivity
  have ht2 : τ ≤ 92 / 5 * (R / L) := by
    have h3 : τ * α ≤ 23 * R / 10 := by linarith only [hτR]
    have h4 : τ * (L / 8) ≤ τ * α := mul_le_mul_of_nonneg_left hαL hτ.le
    have h5 : τ * L ≤ 92 / 5 * R := by linarith only [h3, h4]
    rw [mul_div_assoc', le_div_iff₀ hL0]
    exact h5
  have hB2R : B ^ 2 * (R / L) = (25 / 32) ^ j / (3 * q ^ 2) := by
    have h4 : ((5 / 8 : ℝ) ^ j) ^ 2 * 2 ^ j = (25 / 32) ^ j := by
      rw [← pow_mul, mul_comm j 2, pow_mul, ← mul_pow]
      norm_num
    rw [hBdef, hRdef, ← h4]
    unfold critB critR
    field_simp
  have h5 : (25 / 32 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hq2 : 0 < q ^ 2 := by positivity
  have h6 : B ^ 2 * τ ≤ 7 / q ^ 2 := by
    have h7 := mul_le_mul_of_nonneg_left ht2 (sq_nonneg B)
    have h8 : (25 / 32 : ℝ) ^ j / (3 * q ^ 2) ≤ 1 / (3 * q ^ 2) :=
      div_le_div_of_nonneg_right h5 (by positivity)
    have h9 : 1 / (3 * q ^ 2) = 1 / 3 * (1 / q ^ 2) := by
      field_simp
    have h10 : 7 / q ^ 2 = 7 * (1 / q ^ 2) := by ring
    have h11 : 0 < 1 / q ^ 2 := by positivity
    rw [h10]
    nlinarith only [h7, hB2R, h8, h9, h11]
  have h9 : τ ≤ 1 / (8 * q ^ 2) := by
    have h10 : R / L ≤ (1 / 16) * (1 / L) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right hR16 (by positivity)
    have h11 : 1 / L ≤ 1 / (10 * q ^ 2) := one_div_le_one_div_of_le (by positivity) hLq
    have h12 : 1 / (10 * q ^ 2) = 1 / 10 * (1 / q ^ 2) := by
      field_simp
    have h13 : 1 / (8 * q ^ 2) = 1 / 8 * (1 / q ^ 2) := by
      field_simp
    have h14 : 0 < 1 / q ^ 2 := by positivity
    rw [h13]
    nlinarith only [ht2, h10, h11, h12, h14]
  have h3 : ((B + 2) * Real.sqrt τ) ^ 2 ≤ (4 / q) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hτ.le, div_pow]
    have h4 : (4 : ℝ) ^ 2 / q ^ 2 = 16 * (1 / q ^ 2) := by ring
    have h10 : 7 / q ^ 2 = 7 * (1 / q ^ 2) := by ring
    have h13 : 1 / (8 * q ^ 2) = 1 / 8 * (1 / q ^ 2) := by
      field_simp
    rw [h4]
    rw [h10] at h6
    rw [h13] at h9
    have h14 : 0 < 1 / q ^ 2 := by positivity
    nlinarith only [h6, h9, h14, sq_nonneg (B - 2), mul_nonneg (sq_nonneg (B - 2)) hτ.le, hτ]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h3

/-! ## The model -/

/-- **The transform along the heights.** Near a good height, `Q_{x+s}(0)` rotates with the fixed slope `a(x)` at the fixed saddle. -/
theorem quadrature_model {X R₀ R B τ x ξ : ℝ} (hR₀ : 0 < R₀) (hR16 : R ≤ 1 / 16) (hR₀R : 3 * R₀ ≤ R)
    (hK : ZeroKeeping X R₀) (hdata : ZetaLogDerivScaleData X R B) (hB0 : 0 ≤ B) (hτ : 0 < τ)
    (hα : 1000 ≤ (horizontalSlope x).re) (hx : 1000 ≤ x) (hxξ : x ≤ ξ) (hξ1 : ξ ≤ x + 1) (hxX : |x - X| < R₀)
    (hξX : |ξ - X| < R₀) (hu₁ : 23 * R / 10 ≤ 2 * τ * (horizontalSlope x).re)
    (hu₂ : 2 * τ * (horizontalSlope x).re ≤ 46 * R / 10) (hB100 : 100 * (B + 2) ≤ (horizontalSlope x).re)
    (hΛ : 200 ≤ 2 * τ * (horizontalSlope x).re * (horizontalSlope x).re) :
    ‖halfGaussTransform τ (xiLine ξ) 0 - xiLine x (2 * τ * (horizontalSlope x).re) *
        (Complex.exp (-((2 * τ * (horizontalSlope x).re : ℝ) * horizontalSlope x)) *
          Complex.exp (((0 : ℝ) : ℂ) * horizontalSlope x + τ * horizontalSlope x ^ 2)) *
        Complex.exp (((ξ - x : ℝ) : ℂ) * (I * horizontalSlope x))‖ ≤
      (‖xiLine x (2 * τ * (horizontalSlope x).re)‖ * Real.exp (-(τ * (horizontalSlope x).re ^ 2))) *
        Real.exp (-((ξ - x) * (Real.pi / 4))) *
        ((1 + (Real.exp ((B + 2) * (ξ - x)) - 1)) *
            (gaussianSaddleModelError (B + 2) τ +
              8 * Real.exp (-(2 * τ * (horizontalSlope x).re * (horizontalSlope x).re / 40))) +
          (Real.exp ((B + 2) * (ξ - x)) - 1)) := by
  have hR : 0 < R := by linarith only [hR₀, hR₀R]
  set a := horizontalSlope x with ha
  set α := a.re with hαdef
  set u := 2 * τ * α with hu
  have hα0 : 0 < α := by linarith only [hα]
  have hu0 : 0 < u := by rw [hu]; positivity
  have hxpos : 0 < x := by linarith only [hx]
  -- the slope against `a` on the box at nearby heights
  have hslope (Y : ℝ) (hY1 : x ≤ Y) (hY2 : Y ≤ ξ) (w : ℝ) (hw1 : 3 * R / 4 ≤ w) (hw2 : w ≤ 6 * R) :
      ‖xiLineDeriv Y w - a * xiLine Y w‖ ≤ (B + 2) * ‖xiLine Y w‖ := by
    have hYpos : 0 < Y := by linarith only [hY1, hxpos]
    have hYX : |Y - X| < R₀ := by
      have h1 := abs_lt.mp hxX
      have h2 := abs_lt.mp hξX
      rw [abs_lt]
      constructor <;> linarith only [h1.1, h2.2, hY1, hY2]
    have h1 := norm_xiLineDeriv_sub_le_of_data hR hR16 hdata (by linarith only [hYX, hR₀R, hR₀])
      (by linarith only [hY1, hx]) hw1 hw2
    have h2 : ‖horizontalSlope Y - a‖ ≤ 1 := by
      have h5 : horizontalSlope Y - a = (((horizontalSlope Y).re - a.re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simp [ha, horizontalSlope_im]
      rw [h5, Complex.norm_real, Real.norm_eq_abs]
      refine (abs_horizontalSlope_re_sub_le hxpos hYpos).trans ?_
      rw [div_le_one (lt_min hxpos hYpos)]
      refine le_min ?_ ?_
      · rw [abs_of_nonneg (by linarith only [hY1])]
        linarith only [hY2, hξ1, hx]
      · rw [abs_of_nonneg (by linarith only [hY1])]
        linarith only [hY2, hξ1, hx, hY1]
    have h3 : xiLineDeriv Y w - a * xiLine Y w =
        (xiLineDeriv Y w - horizontalSlope Y * xiLine Y w) + (horizontalSlope Y - a) * xiLine Y w := by ring
    rw [h3]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have h4 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (xiLine Y w))
    linarith only [h1, h4]
  have huI1 : 3 * R / 4 ≤ u := by linarith only [hu₁, hR]
  have huI2 : u ≤ 6 * R := by linarith only [hu₂, hR]
  -- the height comparison at the fixed saddle
  have hBpos : 0 < B + 2 := by linarith only [hB0]
  have hheight := GaloisForLFunctions.HTGeometry.norm_sub_mul_exp_le (a := I * a) (η := B + 2) (u := x) (w := ξ)
    hBpos (fun s _ => hasDerivAt_xiLine_height' u s) (by
      intro s hs
      rw [uIcc_of_le hxξ] at hs
      have h4' : I * xiLineDeriv s u - (I * a) * xiLine s u = I * (xiLineDeriv s u - a * xiLine s u) := by ring
      rw [h4', norm_mul, Complex.norm_I, one_mul]
      exact hslope s hs.1 hs.2 u huI1 huI2)
  have hre : (I * a).re = -(Real.pi / 4) := by
    rw [Complex.mul_re, Complex.I_re, Complex.I_im, ha, horizontalSlope_im]
    ring
  rw [hre, abs_of_nonneg (sub_nonneg.mpr hxξ)] at hheight
  set N₀ := xiLine x u with hN₀
  set e := Real.exp ((B + 2) * (ξ - x)) - 1 with he
  have he0 : 0 ≤ e := by
    have h1 : 0 ≤ (B + 2) * (ξ - x) := mul_nonneg hBpos.le (sub_nonneg.mpr hxξ)
    have h2 := Real.add_one_le_exp ((B + 2) * (ξ - x))
    rw [he]
    linarith only [h1, h2]
  set E₀ := Real.exp ((ξ - x) * -(Real.pi / 4)) with hE₀
  have hE₀eq : E₀ = Real.exp (-((ξ - x) * (Real.pi / 4))) := by
    rw [hE₀]
    congr 1
    ring
  -- the size of the source at the height
  have hZ : ‖xiLine ξ u‖ ≤ ‖N₀‖ * E₀ * (1 + e) := by
    have h1 := norm_sub_norm_le (xiLine ξ u) (N₀ * Complex.exp (((ξ - x : ℝ) : ℂ) * (I * a)))
    rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, hre] at h1
    nlinarith only [h1, hheight]
  -- the core at the height `ξ`
  have hβ1 : 1 ≤ a.re := by linarith only [hα]
  have hξ200 : 200 ≤ ξ := by linarith only [hxξ, hx]
  have hξX6 : |ξ - X| ≤ 6 * R := by linarith only [hξX, hR₀R, hR₀]
  have hbox (w : ℝ) (hw : w ∈ Icc (u / 3) (5 * u / 4)) : 3 * R / 4 ≤ w ∧ w ≤ 6 * R :=
    ⟨by linarith only [hw.1, hu₁, hR], by linarith only [hw.2, hu₂, hR]⟩
  have h2R₀ : 2 * R₀ ≤ u / 3 := by linarith only [hu₁, hR₀R, hR₀, hR]
  have hcore := source_core (Y := ξ) (v := 0) (u := u) (B := B + 2) (a := a) hτ hβ1 hu0 (by rw [zero_add]) (by
      rw [neg_le_iff_add_nonneg]
      positivity) hBpos hB100 (by rw [sub_zero]; exact hΛ)
    (fun w hw => hslope ξ hxξ le_rfl w (hbox w hw).1 (hbox w hw).2)
    (fun w hw => norm_xiLine_le_of_keeping hR₀ hK hξX hw.1 hw.2 h2R₀)
    (fun w hw => by
      refine norm_xiLine_le_growth hR₀ (hK.keepsAway hξX.le) (by linarith only [h2R₀, hu0]) hw ?_
      have hb := hbox (5 * u / 4) ⟨by linarith only [hu0], le_rfl⟩
      obtain ⟨-, hd⟩ := norm_logDeriv_xi_sub_le_of_data hR hR16 hdata hξX6 hξ200 hb.1 hb.2
      have h1 := Complex.re_le_norm (logDeriv xi (linePt ξ (5 * u / 4)) - horizontalSlope ξ)
      rw [Complex.sub_re] at h1
      have hξpos : 0 < ξ := by linarith only [hξ200]
      have h2 := abs_le.mp ((abs_horizontalSlope_re_sub_le hxpos hξpos).trans (by
        rw [div_le_one (lt_min hxpos hξpos)]
        refine le_min ?_ ?_
        · rw [abs_of_nonneg (by linarith only [hxξ])]
          linarith only [hξ1, hx]
        · rw [abs_of_nonneg (by linarith only [hxξ])]
          linarith only [hξ1, hx, hxξ]))
      linarith only [h1, hd, h2.2])
  obtain ⟨-, -, -, -, -, -, hmain⟩ := hcore
  set c := Complex.exp (-(u * a)) * Complex.exp (((0 : ℝ) : ℂ) * a + τ * a ^ 2) with hc
  have hcnorm : ‖c‖ ≤ Real.exp (-(τ * α ^ 2)) := by
    rw [hc, norm_mul, Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : (-(↑u * a)).re = -(u * α) := by
      rw [Complex.neg_re, Complex.re_ofReal_mul]
    have h2 : (((0 : ℝ) : ℂ) * a + τ * a ^ 2).re = τ * (α ^ 2 - a.im ^ 2) := by
      have h3 : (((0 : ℝ) : ℂ) * a).re = 0 := by simp
      rw [Complex.add_re, h3, zero_add, Complex.re_ofReal_mul, pow_two, Complex.mul_re]
      ring
    rw [h1, h2, hu]
    nlinarith only [mul_nonneg hτ.le (sq_nonneg a.im)]
  have hmain' : ‖halfGaussTransform τ (xiLine ξ) 0 - xiLine ξ u * c‖ ≤
      (‖xiLine ξ u‖ * Real.exp (-(τ * α ^ 2))) * (gaussianSaddleModelError (B + 2) τ +
        8 * Real.exp (-(u * α / 40))) := by
    have h1 : xiLine ξ u * c = xiLine ξ u * Complex.exp (-(u * a)) *
        Complex.exp (((0 : ℝ) : ℂ) * a + τ * a ^ 2) := by
      rw [hc]
      ring
    rw [h1]
    exact hmain
  set ε₀ := gaussianSaddleModelError (B + 2) τ + 8 * Real.exp (-(u * α / 40)) with hε₀
  have hε₀0 : 0 ≤ ε₀ := by
    have := gaussianSaddleModelError_nonneg (t := τ) hBpos.le
    positivity
  set P₀ := ‖N₀‖ * Real.exp (-(τ * α ^ 2)) with hP₀
  have hdecomp : halfGaussTransform τ (xiLine ξ) 0 - N₀ * c * Complex.exp (((ξ - x : ℝ) : ℂ) * (I * a)) =
      (halfGaussTransform τ (xiLine ξ) 0 - xiLine ξ u * c) +
        (xiLine ξ u - N₀ * Complex.exp (((ξ - x : ℝ) : ℂ) * (I * a))) * c := by ring
  rw [hdecomp, ← hE₀eq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have h1 : (‖xiLine ξ u‖ * Real.exp (-(τ * α ^ 2))) * ε₀ ≤ P₀ * E₀ * ((1 + e) * ε₀) := by
    have h2 := mul_le_mul_of_nonneg_right hZ (by positivity : 0 ≤ Real.exp (-(τ * α ^ 2)) * ε₀)
    calc _ = ‖xiLine ξ u‖ * (Real.exp (-(τ * α ^ 2)) * ε₀) := by ring
      _ ≤ _ := h2
      _ = _ := by rw [hP₀]; ring
  have h3 : ‖xiLine ξ u - N₀ * Complex.exp (((ξ - x : ℝ) : ℂ) * (I * a))‖ * ‖c‖ ≤ P₀ * E₀ * e := by
    have h4 := mul_le_mul hheight hcnorm (norm_nonneg _) (by positivity)
    refine h4.trans (le_of_eq ?_)
    rw [hP₀]
    ring
  have h5 := hmain'.trans h1
  calc _ ≤ P₀ * E₀ * ((1 + e) * ε₀) + P₀ * E₀ * e := add_le_add h5 h3
    _ = _ := by ring

/-! ## The next zero -/

/-- The sine away from its zeros. -/
theorem sin_ge_of_mem {y ε : ℝ} (hε : 0 ≤ ε) (h1 : ε ≤ y) (h2 : y ≤ Real.pi - ε) : 63 / 100 * ε ≤ Real.sin y := by
  have hpi := Real.pi_gt_three
  have hpi2 := Real.pi_lt_d2
  have hjordan {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) : 63 / 100 * x ≤ Real.sin x := by
    have h3 := Real.mul_le_sin hx0 hx
    refine le_trans ?_ h3
    refine mul_le_mul_of_nonneg_right ?_ hx0
    rw [le_div_iff₀ Real.pi_pos]
    linarith only [hpi2]
  rcases le_total y (Real.pi / 2) with h | h
  · have h3 := hjordan (hε.trans h1) h
    nlinarith only [h3, h1]
  · have h3 := hjordan (x := Real.pi - y) (by linarith only [h2, hε]) (by linarith only [h])
    rw [Real.sin_pi_sub] at h3
    nlinarith only [h3, h2]

/-- **The next zero at a good height.** -/
theorem exists_next_zero_of_data {X R₀ R B τ x e ε : ℝ} (hR₀ : 0 < R₀) (hR16 : R ≤ 1 / 16) (hR₀R : 3 * R₀ ≤ R)
    (hK : ZeroKeeping X R₀) (hdata : ZetaLogDerivScaleData X R B) (hB0 : 0 ≤ B) (hτ : 0 < τ)
    (hα : 1000 ≤ (horizontalSlope x).re) (hx : 1000 ≤ x) (hxX : |x - X| ≤ R₀ / 2)
    (hR₀α : 16 ≤ R₀ * (horizontalSlope x).re) (hu₁ : 23 * R / 10 ≤ 2 * τ * (horizontalSlope x).re)
    (hu₂ : 2 * τ * (horizontalSlope x).re ≤ 46 * R / 10) (hB100 : 100 * (B + 2) ≤ (horizontalSlope x).re)
    (hΛ : 200 ≤ 2 * τ * (horizontalSlope x).re * (horizontalSlope x).re) (hτ8 : τ ≤ 1 / 8)
    (hE : gaussianSaddleModelError (B + 2) τ +
      8 * Real.exp (-(2 * τ * (horizontalSlope x).re * (horizontalSlope x).re / 40)) ≤ e)
    (hν : Real.exp ((B + 2) * (4 / (horizontalSlope x).re)) - 1 ≤ e) (he : e ≤ 1 / 100) (hε : 8 * e ≤ ε)
    (hε1 : ε ≤ 1 / 2)
    (hgap : ∀ y : ℝ, x < y → riemannHeat τ (y : ℂ) = 0 → ε / (horizontalSlope x).re ≤ y - x)
    (hx0 : riemannHeat τ (x : ℂ) = 0) :
    ∃ x' : ℝ, x < x' ∧ riemannHeat τ (x' : ℂ) = 0 ∧ |(x' - x) * (horizontalSlope x).re - Real.pi| ≤ ε ∧
      ∀ y : ℝ, x < y → y < x' → riemannHeat τ (y : ℂ) ≠ 0 := by
  classical
  set a := horizontalSlope x with ha
  set α := a.re with hαdef
  have hα0 : 0 < α := by linarith only [hα]
  set u := 2 * τ * α with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  set N₀ := xiLine x u with hN₀
  set c := Complex.exp (-((u : ℝ) * a)) * Complex.exp (((0 : ℝ) : ℂ) * a + τ * a ^ 2) with hc
  set ρ := N₀ * c with hρ
  set P₀ := ‖N₀‖ * Real.exp (-(τ * α ^ 2)) with hP₀
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have h4α : 4 / α ≤ R₀ / 4 := by
    rw [div_le_iff₀ hα0]
    linarith only [hR₀α]
  have h4α1 : 4 / α ≤ 1 / 250 := by
    rw [div_le_div_iff₀ hα0 (by norm_num)]
    linarith only [hα]
  have hxX' := abs_le.mp hxX
  have he0 : 0 ≤ e := by
    have h1 := gaussianSaddleModelError_nonneg (t := τ) (show 0 ≤ B + 2 by linarith only [hB0])
    have h2 : 0 ≤ 8 * Real.exp (-(2 * τ * α * α / 40)) := by positivity
    linarith only [hE, h1, h2]
  -- the model at a height
  have hmodel (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 4 / α) :
      ‖halfGaussTransform τ (xiLine (x + s)) 0 - ρ * Complex.exp ((s : ℂ) * (I * a))‖ ≤
        P₀ * Real.exp (-(s * (Real.pi / 4))) * (3 * e) := by
    have hξX : |x + s - X| < R₀ := by
      rw [abs_lt]
      constructor <;> linarith only [hxX'.1, hxX'.2, hs0, hs, h4α, hR₀]
    have hxXlt : |x - X| < R₀ := by linarith only [hxX, hR₀]
    have h := quadrature_model hR₀ hR16 hR₀R hK hdata hB0 hτ hα hx (show x ≤ x + s by linarith only [hs0])
      (by linarith only [hs, h4α1]) hxXlt hξX hu₁ hu₂ hB100 hΛ
    rw [add_sub_cancel_left] at h
    refine h.trans ?_
    have hν' : Real.exp ((B + 2) * s) - 1 ≤ e := by
      refine le_trans ?_ hν
      have h3 : (B + 2) * s ≤ (B + 2) * (4 / α) :=
        mul_le_mul_of_nonneg_left hs (by linarith only [hB0])
      linarith only [Real.exp_le_exp.mpr h3]
    have hν0 : 0 ≤ Real.exp ((B + 2) * s) - 1 := by
      have h1 : 0 ≤ (B + 2) * s := mul_nonneg (by linarith only [hB0]) hs0
      have h2 := Real.add_one_le_exp ((B + 2) * s)
      linarith only [h1, h2]
    have hε₀0 : 0 ≤ gaussianSaddleModelError (B + 2) τ + 8 * Real.exp (-(2 * τ * α * α / 40)) := by
      have h1 := gaussianSaddleModelError_nonneg (t := τ) (show 0 ≤ B + 2 by linarith only [hB0])
      positivity
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h4 := mul_le_mul (show 1 + (Real.exp ((B + 2) * s) - 1) ≤ 1 + e by linarith only [hν']) hE hε₀0
      (by linarith only [he0])
    nlinarith only [h4, hν', he, he0]
  -- at the zero
  have hP₀nonneg : 0 ≤ P₀ := by positivity
  have hQ0 : ‖halfGaussTransform τ (xiLine x) 0 - ρ‖ ≤ P₀ * e := by
    have hxXlt : |x - X| < R₀ := by linarith only [hxX, hR₀]
    have h : ‖halfGaussTransform τ (xiLine x) 0 - N₀ * c * Complex.exp (((x - x : ℝ) : ℂ) * (I * a))‖ ≤
        P₀ * Real.exp (-((x - x) * (Real.pi / 4))) *
          ((1 + (Real.exp ((B + 2) * (x - x)) - 1)) *
              (gaussianSaddleModelError (B + 2) τ + 8 * Real.exp (-(u * α / 40))) +
            (Real.exp ((B + 2) * (x - x)) - 1)) :=
      quadrature_model hR₀ hR16 hR₀R hK hdata hB0 hτ hα hx le_rfl (by linarith only) hxXlt hxXlt hu₁ hu₂ hB100 hΛ
    simp only [sub_self, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, neg_zero, Real.exp_zero, mul_zero,
      add_zero, one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left hE hP₀nonneg)
  have hH (y : ℝ) : (riemannHeat τ (y : ℂ)).re = 2 * (halfGaussTransform τ (xiLine y) 0).re := by
    rw [riemannHeat_ofReal_eq_two_re_halfGauss hτ y, Complex.ofReal_re]
  have hHzero (y : ℝ) : riemannHeat τ (y : ℂ) = 0 ↔ (halfGaussTransform τ (xiLine y) 0).re = 0 := by
    rw [riemannHeat_ofReal_eq_two_re_halfGauss hτ y]
    constructor
    · intro h
      have h1 : (2 * (halfGaussTransform τ (xiLine y) 0).re : ℝ) = 0 := by exact_mod_cast h
      linarith only [h1]
    · intro h
      rw [h, mul_zero, Complex.ofReal_zero]
  have hA0 := (hHzero x).mp hx0
  have hρre : |ρ.re| ≤ P₀ * e := by
    have h1 := Complex.abs_re_le_norm (halfGaussTransform τ (xiLine x) 0 - ρ)
    rw [Complex.sub_re, hA0, zero_sub, abs_neg] at h1
    exact h1.trans hQ0
  have hP₀pos : 0 < P₀ := by
    refine mul_pos (norm_pos_iff.mpr ?_) (Real.exp_pos _)
    have h2R₀ : 2 * R₀ ≤ u := by linarith only [hu₁, hR₀R, hR₀, hR₀R]
    exact xiLine_ne_zero_of_keepsAway hR₀ (hK.keepsAway (by linarith only [hxX, hR₀, abs_nonneg (x - X)])) h2R₀
  have hρnorm : 23 / 25 * P₀ ≤ ‖ρ‖ := by
    have h1 := norm_main_eq (t := τ) (X := x) (y := 0) N₀
    rw [zero_add, ← ha, ← hαdef, ← hu] at h1
    have h2 : ρ = N₀ * Complex.exp (-(((u : ℝ) : ℂ) * a)) * Complex.exp (((0 : ℝ) : ℂ) * a + τ * a ^ 2) := by
      rw [hρ, hc]
      ring
    rw [h2, h1]
    have h3 := gaussPhase_ge hτ8 hτ
    nlinarith only [mul_le_mul_of_nonneg_left h3 hP₀pos.le]
  set m := ρ.im with hm
  have hmabs : 9 / 10 * P₀ ≤ |m| := by
    have h1 := Complex.norm_le_abs_re_add_abs_im ρ
    have h2 := mul_le_mul_of_nonneg_left he hP₀pos.le
    linarith only [h1, h2, hρre, hρnorm, hP₀pos]
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, abs_zero] at hmabs
    linarith only [hmabs, hP₀pos]
  -- the value along the heights
  have hvalue (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 4 / α) :
      |(halfGaussTransform τ (xiLine (x + s)) 0).re + Real.exp (-(s * (Real.pi / 4))) * (m * Real.sin (s * α))| ≤
        4 * e * (P₀ * Real.exp (-(s * (Real.pi / 4)))) := by
    have h1 := Complex.abs_re_le_norm (halfGaussTransform τ (xiLine (x + s)) 0 - ρ * Complex.exp ((s : ℂ) * (I * a)))
    have h2 := re_mul_exp_I_slope ρ a s
    rw [Complex.sub_re, h2, ← hαdef, ha, horizontalSlope_im, ← ha] at h1
    have hE₀ := Real.exp_pos (-(s * (Real.pi / 4)))
    have h3 : |ρ.re * Real.cos (s * α)| ≤ P₀ * e := by
      rw [abs_mul]
      have h4 := Real.abs_cos_le_one (s * α)
      have h5 : 0 ≤ P₀ * e := by positivity
      calc |ρ.re| * |Real.cos (s * α)| ≤ (P₀ * e) * 1 := mul_le_mul hρre h4 (abs_nonneg _) h5
        _ = _ := mul_one _
    have h6 := hmodel s hs0 hs
    have h7 := abs_le.mp h3
    have h8 := abs_le.mp (h1.trans h6)
    set E₀ := Real.exp (-(s * (Real.pi / 4))) with hE₀def
    have h9 : E₀ * (ρ.re * Real.cos (s * α)) ≤ E₀ * (P₀ * e) := mul_le_mul_of_nonneg_left h7.2 hE₀.le
    have h10 : E₀ * (-(P₀ * e)) ≤ E₀ * (ρ.re * Real.cos (s * α)) := mul_le_mul_of_nonneg_left h7.1 hE₀.le
    rw [abs_le]
    constructor <;> nlinarith only [h8.1, h8.2, h9, h10]
  -- the sign of `m Q` where the sine is large
  have hsign (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 4 / α) (κ : ℝ) (hκ : κ = 1 ∨ κ = -1) (hsin : 5 * e < κ * Real.sin (s * α))
      (he' : 0 < e) : κ * (m * (halfGaussTransform τ (xiLine (x + s)) 0).re) < 0 := by
    have hv := abs_le.mp (hvalue s hs0 hs)
    set V := (halfGaussTransform τ (xiLine (x + s)) 0).re with hV
    set E₀ := Real.exp (-(s * (Real.pi / 4))) with hE₀def
    have hE₀ : 0 < E₀ := Real.exp_pos _
    set S := Real.sin (s * α) with hS
    have hmsq : m ^ 2 = |m| ^ 2 := (sq_abs m).symm
    have hmP : m * (P₀ * E₀) ≤ |m| * (P₀ * E₀) := mul_le_mul_of_nonneg_right (le_abs_self m) (by positivity)
    have hmP2 : -m * (P₀ * E₀) ≤ |m| * (P₀ * E₀) := mul_le_mul_of_nonneg_right (neg_le_abs m) (by positivity)
    have hkey : κ * (m * V) ≤ -(E₀ * m ^ 2 * (κ * S)) + 4 * e * (|m| * (P₀ * E₀)) := by
      have hsplit : κ * (m * V) = -(E₀ * m ^ 2 * (κ * S)) + κ * m * (V + E₀ * (m * S)) := by ring
      rw [hsplit]
      have h4 : κ * m * (V + E₀ * (m * S)) ≤ |m| * (4 * e * (P₀ * E₀)) := by
        have h5 : |κ * m * (V + E₀ * (m * S))| ≤ |m| * (4 * e * (P₀ * E₀)) := by
          rw [abs_mul, abs_mul]
          have h6 : |κ| = 1 := by
            rcases hκ with rfl | rfl <;> simp
          rw [h6, one_mul]
          exact mul_le_mul_of_nonneg_left (abs_le.mpr hv) (abs_nonneg _)
        exact (le_abs_self _).trans h5
      linarith only [h4]
    have hm1 : 0 < |m| := abs_pos.mpr hm0
    have h7 : E₀ * m ^ 2 * (5 * e) < E₀ * m ^ 2 * (κ * S) :=
      mul_lt_mul_of_pos_left hsin (by rw [hmsq]; positivity)
    have h8 : 4 * e * (|m| * (P₀ * E₀)) ≤ E₀ * m ^ 2 * (5 * e) := by
      rw [hmsq]
      have h9 : P₀ ≤ 10 / 9 * |m| := by linarith only [hmabs]
      have h10 : 0 ≤ e * E₀ * |m| := by positivity
      nlinarith only [mul_le_mul_of_nonneg_left h9 h10, h10, hm1]
    linarith only [hkey, h7, h8]
  -- the case `e = 0` is excluded by positivity of the slope error, so work with a positive margin
  have he' : 0 < e := by
    by_contra hcon
    have h0 : e = 0 := le_antisymm (not_lt.mp hcon) he0
    have h1 := hν
    rw [h0] at h1
    have h2 : 0 < (B + 2) * (4 / α) := by
      have : 0 < B + 2 := by linarith only [hB0]
      positivity
    have h3 := Real.add_one_lt_exp h2.ne'
    linarith only [h1, h2, h3]
  have hε0 : 0 < ε := by linarith only [hε, he']
  -- the interval
  set y₁ := x + (Real.pi - ε) / α with hy₁
  set y₂ := x + (Real.pi + ε) / α with hy₂
  have hs₁ : 0 ≤ (Real.pi - ε) / α := div_nonneg (by linarith only [hε1, hpi]) hα0.le
  have hs₂ : (Real.pi + ε) / α ≤ 4 / α := div_le_div_of_nonneg_right (by linarith only [hε1, hpi4, Real.pi_lt_d2]) hα0.le
  have hs₁₂ : (Real.pi - ε) / α ≤ (Real.pi + ε) / α := div_le_div_of_nonneg_right (by linarith only [hε0]) hα0.le
  have hsα (r : ℝ) : r / α * α = r := div_mul_cancel₀ r hα0.ne'
  set f : ℝ → ℝ := fun y => m * (riemannHeat τ (y : ℂ)).re with hf
  have hfc : Continuous f :=
    continuous_const.mul (Complex.continuous_re.comp
      ((differentiable_riemannHeat hτ.le).continuous.comp Complex.continuous_ofReal))
  have hfval (y : ℝ) : f y = 2 * (m * (halfGaussTransform τ (xiLine y) 0).re) := by
    simp only [hf]
    rw [hH y]
    ring
  have hsin1 : 5 * e < Real.sin (Real.pi - ε) := by
    rw [Real.sin_pi_sub]
    have h1 := sin_ge_of_mem hε0.le le_rfl (by linarith only [hε1, hpi])
    linarith only [h1, hε, he']
  have hfy₁ : f y₁ < 0 := by
    have h1 := hsign _ hs₁ (hs₁₂.trans hs₂) 1 (Or.inl rfl) (by rw [one_mul, hsα]; exact hsin1) he'
    rw [hfval, hy₁]
    linarith only [h1]
  have hfy₂ : 0 < f y₂ := by
    have h1 := hsign _ ((hs₁.trans hs₁₂)) hs₂ (-1) (Or.inr rfl) (by
      rw [hsα, show Real.pi + ε = ε + Real.pi by ring, Real.sin_add_pi]
      have h2 := sin_ge_of_mem hε0.le le_rfl (by linarith only [hε1, hpi])
      linarith only [h2, hε, he']) he'
    rw [hfval, hy₂]
    linarith only [h1]
  have hy₁₂ : y₁ ≤ y₂ := by rw [hy₁, hy₂]; linarith only [hs₁₂]
  obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc hy₁₂ hfc.continuousOn ⟨hfy₁.le, hfy₂.le⟩
  have hzero_iff (y : ℝ) : f y = 0 ↔ riemannHeat τ (y : ℂ) = 0 := by
    rw [hfval, hHzero]
    constructor
    · intro h
      have h1 : m * (halfGaussTransform τ (xiLine y) 0).re = 0 := by linarith only [h]
      exact (mul_eq_zero.mp h1).resolve_left hm0
    · intro h
      rw [h, mul_zero, mul_zero]
  set S : Set ℝ := Icc y₁ y₂ ∩ f ⁻¹' {0} with hS
  have hSc : IsCompact S := isCompact_Icc.inter_right (isClosed_singleton.preimage hfc)
  obtain ⟨x', hx'S, hx'least⟩ := hSc.exists_isLeast ⟨z, hz, hfz⟩
  have hx'I : x' ∈ Icc y₁ y₂ := hx'S.1
  have hx'f : f x' = 0 := hx'S.2
  have hxy₁ : x < y₁ := by
    have : 0 < (Real.pi - ε) / α := div_pos (by linarith only [hε1, hpi]) hα0
    rw [hy₁]
    linarith only [this]
  refine ⟨x', hxy₁.trans_le hx'I.1, (hzero_iff x').mp hx'f, ?_, ?_⟩
  · have h1 := hx'I.1
    have h2 := hx'I.2
    rw [hy₁] at h1
    rw [hy₂] at h2
    have h3 := mul_le_mul_of_nonneg_right (show (Real.pi - ε) / α ≤ x' - x by linarith only [h1]) hα0.le
    have h4 := mul_le_mul_of_nonneg_right (show x' - x ≤ (Real.pi + ε) / α by linarith only [h2]) hα0.le
    rw [hsα] at h3 h4
    rw [abs_le]
    constructor <;> linarith only [h3, h4]
  · intro y hxy hyx' hy0
    rcases lt_or_ge y y₁ with hlt | hge
    · have hg := hgap y hxy hy0
      set s := y - x with hs
      have hs0 : 0 ≤ s := by rw [hs]; linarith only [hxy]
      have hsy : x + s = y := by rw [hs]; ring
      have hsα1 : ε ≤ s * α := by
        rw [div_le_iff₀ hα0] at hg
        exact hg
      have hsα2 : s * α ≤ Real.pi - ε := by
        have h1 : s ≤ (Real.pi - ε) / α := by
          rw [hs]
          rw [hy₁] at hlt
          linarith only [hlt]
        have h2 := mul_le_mul_of_nonneg_right h1 hα0.le
        rwa [hsα] at h2
      have hsle : s ≤ 4 / α := by
        have h1 : s ≤ (Real.pi - ε) / α := by
          rw [hs]
          rw [hy₁] at hlt
          linarith only [hlt]
        exact h1.trans (hs₁₂.trans hs₂)
      have h1 := hsign s hs0 hsle 1 (Or.inl rfl) (by
        rw [one_mul]
        have h2 := sin_ge_of_mem hε0.le hsα1 hsα2
        linarith only [h2, hε, he']) he'
      rw [hsy, one_mul] at h1
      have h2 := (hzero_iff y).mpr hy0
      rw [hfval] at h2
      linarith only [h1, h2]
    · have h1 : y ∈ S := ⟨⟨hge, (le_of_lt hyx').trans hx'I.2⟩, (hzero_iff y).mpr hy0⟩
      exact absurd (hx'least h1) (not_le.mpr hyx')

/-- **The crystal law.** For all `δ, ε > 0` there is `κ > 0` such that for all large `T`, outside a set of `X ∈ [T, 2T]` of measure at most `δT`: if `x` is a real zero of `H_t` with `|x − X| ≤ κ/(2 log T)` and `7κ/log T ≤ t log(x/2π) ≤ 1/8`, the next real zero `x'` satisfies `|(x' − x) · ½ log(x/2π) − π| ≤ ε`. -/
theorem exists_crystal_law :
    ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ T : ℝ in atTop,
      volume {X | X ∈ Icc T (2 * T) ∧ ¬ ∀ t x : ℝ, 0 < t → |x - X| ≤ κ / (2 * Real.log T) →
          7 * κ / Real.log T ≤ t * Real.log (x / (2 * Real.pi)) → t * Real.log (x / (2 * Real.pi)) ≤ 1 / 8 →
          riemannHeat t (x : ℂ) = 0 →
          ∃ x' : ℝ, x < x' ∧ riemannHeat t (x' : ℂ) = 0 ∧
            |(x' - x) * (Real.log (x / (2 * Real.pi)) / 2) - Real.pi| ≤ ε ∧
            ∀ y : ℝ, x < y → y < x' → riemannHeat t (y : ℂ) ≠ 0} ≤ ENNReal.ofReal (δ * T) := by
  obtain ⟨A, hA, hbad⟩ := exists_volume_not_criticalGood_le
  intro δ ε hδ hε
  set c₀ := 1 / (20 * Real.exp 7) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  set ε' := min ε (min c₀ (1 / 2)) with hε'
  have hε'0 : 0 < ε' := lt_min hε (lt_min hc₀pos (by norm_num))
  have hε'1 : ε' ≤ ε := min_le_left _ _
  have hε'2 : ε' ≤ c₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hε'3 : ε' ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set q : ℝ := max ((10 : ℝ) ^ 4) (max (A / δ + 1) (800 / ε' + 1)) with hq
  have hq1 : (10 : ℝ) ^ 4 ≤ q := le_max_left _ _
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq1
  have hq11 : (1 : ℝ) ≤ q := le_trans (by norm_num) hq1
  have hqA : A ≤ δ * q ^ 2 := by
    have h1 : A / δ + 1 ≤ q := (le_max_of_le_right (le_max_left _ _))
    have h2 : A / δ ≤ q := by linarith only [h1]
    rw [div_le_iff₀ hδ] at h2
    have h3 : q ≤ q ^ 2 := le_self_pow₀ hq11 (by norm_num)
    nlinarith only [h2, h3, hδ]
  have hqε : 800 / q ≤ ε' := by
    have h1 : 800 / ε' + 1 ≤ q := (le_max_of_le_right (le_max_right _ _))
    have h2 : 800 / ε' ≤ q := by linarith only [h1]
    rw [div_le_iff₀ hε'0] at h2
    rw [div_le_iff₀ hq0]
    linarith only [h2]
  refine ⟨q ^ 4, by positivity, ?_⟩
  filter_upwards [hbad q hq1, eventually_ge_atTop (1100 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (10 ^ 6 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1000 * q ^ 2)] with T hvol hT hlog hlogq
  refine (measure_mono ?_).trans (hvol.trans (ENNReal.ofReal_le_ofReal ?_))
  swap
  · rw [div_le_iff₀ (by positivity)]
    have hT0 : 0 < T := by linarith only [hT]
    nlinarith only [mul_le_mul_of_nonneg_right hqA hT0.le]
  rintro X ⟨hXT, hprop⟩
  refine ⟨hXT, fun hgood => hprop ?_⟩
  intro t x ht hx hκt ht1 hx0
  obtain ⟨hK, hdata⟩ := hgood
  set L := Real.log T with hL
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hlog
  set R₀ := q ^ 4 / L with hR₀
  have hR₀pos : 0 < R₀ := by positivity
  have hq4 : ((10 : ℝ) ^ 4) ^ 4 ≤ q ^ 4 := pow_le_pow_left₀ (by positivity) hq1 4
  have hq16 : (10 : ℝ) ^ 16 ≤ q ^ 4 := by
    norm_num at hq4 ⊢
    exact hq4
  have hx' : |x - X| ≤ R₀ / 2 := by
    refine hx.trans (le_of_eq ?_)
    rw [hR₀]
    field_simp
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
  have hre : (horizontalSlope x).re = Real.log (x / (2 * Real.pi)) / 2 := horizontalSlope_re x
  have hT0 : 0 < T := by linarith only [hT]
  have hscale : L ≤ scaleLog T := by
    unfold scaleLog
    have := Real.log_le_log hT0 (show T ≤ 4 * T by linarith only [hT])
    linarith only [this]
  obtain ⟨hα1, -⟩ := slope_bounds (by linarith only [hT]) (by linarith only [hscale, hlog]) hxlo hxhi
  rw [← hre]
  set α := (horizontalSlope x).re with hα
  have hαL : L / 8 ≤ α := by linarith only [hα1, hscale]
  have hα0 : 0 < α := by linarith only [hαL, hL0]
  have hα1000 : 1000 ≤ α := by linarith only [hαL, hlog]
  have h69 : 69 / 10 * (q ^ 4 / L) ≤ u₀ := by
    rw [← hR₀]
    linarith only [h7R₀, hR₀pos]
  obtain ⟨j, hR16, hR₀R, hu₁, hu₂, hB0, hB400, hq', hRα⟩ := exists_scale_of_saddle (τ := t) (u := u₀) hq1 hlog hαL ht
    (by rw [hslope]) h69 (by linarith only [ht1])
  rw [← hR₀] at hR₀R
  rw [← hslope] at hu₁ hu₂
  set R := critR q L j with hRdef
  set B := critB q L j with hBdef
  have hR₀α : q ^ 4 / 8 ≤ R₀ * α := by
    have h3 := mul_le_mul_of_nonneg_left hαL hR₀pos.le
    refine le_trans (le_of_eq ?_) h3
    rw [hR₀]
    field_simp
  have hu₀α : 7 * (q ^ 4 / 8) ≤ 2 * t * α * α := by
    rw [hslope]
    have h3 := mul_le_mul_of_nonneg_right h7R₀ hα0.le
    nlinarith only [h3, hR₀α]
  have hBpos2 : 0 ≤ B + 2 := by linarith only [hB0]
  set e := 100 / q with he
  have he1 : e ≤ 1 / 100 := by
    rw [he, div_le_div_iff₀ hq0 (by norm_num)]
    linarith only [hq1]
  have hE : gaussianSaddleModelError (B + 2) t + 8 * Real.exp (-(2 * t * α * α / 40)) ≤ e := by
    have hs := crit_sqrt_le (j := j) hq1 hL0 hαL ht hR16 (by rw [← hRdef]; exact hu₂)
      (by linarith only [hlogq, sq_nonneg q])
    have h1 := gaussianSaddleModelError_le_of_sqrt_le ht hBpos2 hs
    have h4q : 4 / q ≤ 1 / 100 := by
      rw [div_le_div_iff₀ hq0 (by norm_num)]
      linarith only [hq1]
    have h4q0 : 0 < 4 / q := by positivity
    have h2 : Real.exp ((1 + 4 / q) ^ 2) ≤ 9 := by
      have h3 : (1 + 4 / q) ^ 2 ≤ 2 := by nlinarith only [h4q, h4q0]
      have h4 : Real.exp 2 = Real.exp 1 ^ 2 := by
        rw [← Real.exp_nat_mul]
        norm_num
      have h5 := Real.exp_one_lt_d9
      have h6 : Real.exp 1 ^ 2 ≤ 3 ^ 2 := pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith only [h5]) 2
      have h7 := Real.exp_le_exp.mpr h3
      rw [h4] at h7
      linarith only [h6, h7]
    have h3 : gaussianSaddleModelError (B + 2) t ≤ 72 / q := by
      refine h1.trans ?_
      have h4 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * (4 / q) by positivity)
      refine h4.trans (le_of_eq ?_)
      ring
    have h5 : Real.exp (-(2 * t * α * α / 40)) ≤ 1 / q := by
      refine exp_neg_le_of_le hq0 ?_
      have h6 : q ≤ q ^ 4 / 1000 := by
        rw [le_div_iff₀ (by norm_num)]
        have h7 : (1000 : ℝ) ≤ q ^ 3 := le_trans (le_trans (by norm_num) hq1) (le_self_pow₀ hq11 (by norm_num))
        have h8 : q ^ 4 = q * q ^ 3 := by ring
        rw [h8]
        exact mul_le_mul_of_nonneg_left h7 hq0.le
      have h9 : 0 ≤ q ^ 4 := by positivity
      linarith only [h6, hu₀α, h9]
    have h6 : 8 * Real.exp (-(2 * t * α * α / 40)) ≤ 8 / q := by
      have := mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ 8)
      calc _ ≤ 8 * (1 / q) := this
        _ = 8 / q := by ring
    have h7 : 72 / q + 8 / q ≤ 100 / q := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) hq0.le
    linarith only [h3, h6, h7]
  have hν : Real.exp ((B + 2) * (4 / α)) - 1 ≤ e := by
    have hBle : B ≤ L / (3 * q ^ 3) := by
      rw [hBdef]
      unfold critB
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have h3 : (5 / 8 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith only [h3, hL0]
    have hz : (B + 2) * (4 / α) ≤ 1 / q := by
      have h1 : 4 / α ≤ 32 / L := by
        rw [div_le_div_iff₀ hα0 hL0]
        linarith only [hαL]
      have h2 := mul_le_mul_of_nonneg_left h1 hBpos2
      refine h2.trans ?_
      have h3 : (B + 2) * (32 / L) ≤ (L / (3 * q ^ 3) + 2) * (32 / L) :=
        mul_le_mul_of_nonneg_right (by linarith only [hBle]) (by positivity)
      refine h3.trans ?_
      have h4 : (L / (3 * q ^ 3) + 2) * (32 / L) = 32 / (3 * q ^ 3) + 64 / L := by
        field_simp
        ring
      rw [h4]
      have h5 : 32 / (3 * q ^ 3) ≤ 1 / (2 * q) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h6 : (64 : ℝ) ≤ q ^ 2 := by nlinarith only [hq1]
        have h7 : q ^ 3 = q * q ^ 2 := by ring
        rw [h7]
        nlinarith only [mul_le_mul_of_nonneg_left h6 hq0.le, hq0]
      have h6 : 64 / L ≤ 1 / (2 * q) := by
        rw [div_le_div_iff₀ hL0 (by positivity)]
        have h7 : q ≤ q ^ 2 := le_self_pow₀ hq11 (by norm_num)
        linarith only [hlogq, h7, hq0]
      have h8 : 1 / (2 * q) + 1 / (2 * q) = 1 / q := by
        field_simp
        norm_num
      linarith only [h5, h6, h8]
    set z := (B + 2) * (4 / α) with hzdef
    have hz0 : 0 ≤ z := by positivity
    have hq12 : 1 / q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (le_trans (by norm_num) hq1)
    have h1 : Real.exp z ≤ 1 + 2 * z := by
      have h2 := Real.add_one_le_exp (-z)
      rw [Real.exp_neg] at h2
      have hzpos := Real.exp_pos z
      have h3 : (1 - z) * Real.exp z ≤ 1 := by
        have h4 := mul_le_mul_of_nonneg_right h2 hzpos.le
        rw [inv_mul_cancel₀ hzpos.ne'] at h4
        linarith only [h4]
      have h5 : z ≤ 1 / 2 := hz.trans hq12
      nlinarith only [h3, h5, hz0, hzpos, mul_nonneg hz0 hz0, mul_nonneg (by linarith only [h5] : 0 ≤ 1 / 2 - z) hz0,
        Real.add_one_le_exp z]
    have h2 : 2 / q ≤ 100 / q := div_le_div_of_nonneg_right (by norm_num) hq0.le
    have h3 : 2 * (1 / q) = 2 / q := by ring
    rw [he]
    linarith only [h1, hz, h2, h3]
  have hε8 : 8 * e ≤ ε' := by
    rw [he]
    have h1 : 8 * (100 / q) = 800 / q := by ring
    rw [h1]
    exact hqε
  have hgap (y : ℝ) (hy : x < y) (hy0 : riemannHeat t (y : ℂ) = 0) : ε' / α ≤ y - x := by
    have h1 := gap_ge_of_critical_data hR₀pos hR16 hR₀R hK (hdata j hR16) hB0 (hT.trans hXT.1) hx'
      hα1000 ht hu₁ hu₂ hRα (by linarith only [hR₀α, hq16]) hB400 hq' hy hx0 hy0
    refine le_trans ?_ h1
    exact div_le_div_of_nonneg_right hε'2 hα0.le
  obtain ⟨x', h1, h2, h3, h4⟩ := exists_next_zero_of_data hR₀pos hR16 hR₀R hK (hdata j hR16) hB0 ht hα1000
    (by linarith only [hxlo, hT]) hx' (by linarith only [hR₀α, hq16]) hu₁ hu₂ (by linarith only [hB400, hα1000])
    (by linarith only [hu₀α, hq16]) (by nlinarith only [hslope, ht1, hα1000, ht]) hE hν he1 hε8 hε'3 hgap hx0
  exact ⟨x', h1, h2, h3.trans hε'1, h4⟩

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

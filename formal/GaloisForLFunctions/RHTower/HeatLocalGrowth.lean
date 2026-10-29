import GaloisForLFunctions.RHTower.KiKimLeeRelativeBounds
import GaloisForLFunctions.RHTower.XiSliceKKLScaleOffLineDetection

/-!
# Local growth of the de Bruijn–Newman heat flow

The global horizontal envelope for `ξ`, integrated against the heat
Gaussian, bounds `H_t` relative to an Euler-region value at the same
height. On fixed disks this ratio grows polynomially with height when
`t log X` stays bounded.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- The squared slice envelope gives a norm envelope at the fixed Euler point. -/
theorem norm_xiLine_le_sixteen_exp {X : ℝ} (hX : 16 ≤ X) (w : ℝ) :
    ‖xiLine X w‖ ≤ ‖xiLine X 16‖ *
      Real.exp (((Real.log X + xiSliceGlobalConstant) / 2) * |w| + w ^ 2 / 2) := by
  have hg := xiSliceReal_le_global hX w
  have hm := xiSliceReal_mono (t := X) (y := 3 / 2) (z := 16) (by norm_num) (by norm_num)
  have hsq : ‖xiLine X w‖ ^ 2 ≤ ‖xiLine X 16‖ ^ 2 *
      Real.exp ((Real.log X + xiSliceGlobalConstant) * |w| + w ^ 2) := by
    have h := hg.trans (mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le)
    have heq (v : ℝ) : xiSliceReal X v = ‖xiLine X v‖ ^ 2 := by
      have hp : (((1 / 2 + v : ℝ) : ℂ) + (X : ℂ) * I) = 1 / 2 + v + I * X := by
        push_cast
        ring
      exact congrArg (fun z : ℂ => ‖xi z‖ ^ 2) hp
    simpa only [heq] using h
  have heq : (‖xiLine X 16‖ *
      Real.exp (((Real.log X + xiSliceGlobalConstant) / 2) * |w| + w ^ 2 / 2)) ^ 2 =
      ‖xiLine X 16‖ ^ 2 * Real.exp ((Real.log X + xiSliceGlobalConstant) * |w| + w ^ 2) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hn : 0 ≤ ‖xiLine X 16‖ *
      Real.exp (((Real.log X + xiSliceGlobalConstant) / 2) * |w| + w ^ 2 / 2) := by positivity
  rw [← heq] at hsq
  nlinarith only [hsq, hn, norm_nonneg (xiLine X w)]

private theorem exp_abs_le_sum (B v : ℝ) :
    Real.exp (B * |v|) ≤ Real.exp (B * v) + Real.exp (-B * v) := by
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]
    linarith only [Real.exp_pos (-B * v)]
  · rw [abs_of_nonpos hv, mul_neg]
    have heq : -(B * v) = -B * v := by ring
    rw [heq]
    linarith only [Real.exp_pos (B * v)]

private theorem gauss_shift_quadratic_majorant {t B : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hB : 0 ≤ B) (y w : ℝ) :
    gaussDensity t (w - y) * Real.exp (B * |w| + w ^ 2 / 2) ≤
      (2 * Real.exp (B * |y| + y ^ 2)) *
        (gaussDensity (2 * t) (w - y) * Real.exp (B * (w - y)) +
          gaussDensity (2 * t) (w - y) * Real.exp (-B * (w - y))) := by
  set v := w - y
  have habs : |w| ≤ |v| + |y| := by
    simpa [v] using abs_add_le (w - y) y
  have hsq : w ^ 2 / 2 ≤ v ^ 2 + y ^ 2 := by dsimp [v]; nlinarith only [sq_nonneg (w - 2 * y)]
  have hv : v ^ 2 ≤ v ^ 2 / (8 * t) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [mul_nonneg (sq_nonneg v) (show 0 ≤ 1 - 8 * t by linarith)]
  have hexp : B * |w| + w ^ 2 / 2 ≤ (B * |y| + y ^ 2) + v ^ 2 / (8 * t) + B * |v| := by
    linarith only [mul_le_mul_of_nonneg_left habs hB, hsq, hv]
  calc
    _ ≤ gaussDensity t v * Real.exp ((B * |y| + y ^ 2) + v ^ 2 / (8 * t) + B * |v|) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (gaussDensity_pos ht _).le
    _ = Real.exp (B * |y| + y ^ 2) *
        (gaussDensity t v * Real.exp (v ^ 2 / (8 * t))) * Real.exp (B * |v|) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ ≤ Real.exp (B * |y| + y ^ 2) * (2 * gaussDensity (2 * t) v) *
        (Real.exp (B * v) + Real.exp (-B * v)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (gaussDensity_mul_exp_le ht v) (Real.exp_pos _).le)
        (exp_abs_le_sum B v) (Real.exp_pos _).le
        (mul_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num) (gaussDensity_pos (by positivity) _).le))
    _ = _ := by dsimp [v]; ring

private theorem integrable_gauss_centered_exp {t : ℝ} (ht : 0 < t) (y B : ℝ) :
    Integrable (fun w => gaussDensity t (w - y) * Real.exp (B * (w - y))) := by
  have h := integrable_gaussDensity_sub_mul_rexp_mul_rexp ht y 0 B y
  simpa only [mul_zero, Real.exp_zero, mul_one, mul_comm B] using h

private theorem integral_gauss_centered_exp {t : ℝ} (ht : 0 < t) (y B : ℝ) :
    (∫ w, gaussDensity t (w - y) * Real.exp (B * (w - y))) = Real.exp (t * B ^ 2) := by
  have h := integral_gaussDensity_sub_mul_rexp_mul_rexp_centre ht y 0 B
  simpa only [mul_zero, Real.exp_zero, mul_one, one_mul, zero_add, add_zero, zero_pow (by norm_num : 2 ≠ 0),
    mul_comm B] using h

/-- Integrating a quadratic norm envelope costs only `exp(2tB²)` in the slope. -/
theorem integral_gauss_shift_norm_le {t B C : ℝ} {F : ℝ → ℂ}
    (ht : 0 < t) (ht8 : t ≤ 1 / 8) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hF : ∀ w, ‖F w‖ ≤ C * Real.exp (B * |w| + w ^ 2 / 2)) (y : ℝ) :
    (∫ w, gaussDensity t (w - y) * ‖F w‖) ≤
      4 * C * Real.exp (B * |y| + y ^ 2 + 2 * t * B ^ 2) := by
  have ht2 : 0 < 2 * t := by positivity
  have hip := integrable_gauss_centered_exp ht2 y B
  have hin := integrable_gauss_centered_exp ht2 y (-B)
  have hi := (hip.add hin).const_mul (C * (2 * Real.exp (B * |y| + y ^ 2)))
  have hpoint : ∀ w, gaussDensity t (w - y) * ‖F w‖ ≤
      (C * (2 * Real.exp (B * |y| + y ^ 2))) *
        (gaussDensity (2 * t) (w - y) * Real.exp (B * (w - y)) +
          gaussDensity (2 * t) (w - y) * Real.exp (-B * (w - y))) := by
    intro w
    have h := mul_le_mul_of_nonneg_left (hF w) (gaussDensity_pos ht (w - y)).le
    have hg := mul_le_mul_of_nonneg_left (gauss_shift_quadratic_majorant ht ht8 hB y w) hC
    nlinarith only [h, hg]
  calc
    _ ≤ ∫ w, (C * (2 * Real.exp (B * |y| + y ^ 2))) *
        (gaussDensity (2 * t) (w - y) * Real.exp (B * (w - y)) +
          gaussDensity (2 * t) (w - y) * Real.exp (-B * (w - y))) :=
      integral_mono_of_nonneg (Eventually.of_forall fun w =>
        mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _)) hi (Eventually.of_forall hpoint)
    _ = _ := by
      rw [integral_const_mul, integral_add hip hin, integral_gauss_centered_exp ht2,
        integral_gauss_centered_exp ht2, neg_sq]
      simp only [Real.exp_add]
      ring

/-- The whole-line Gaussian representation in horizontal `ξ` coordinates. -/
theorem riemannHeat_eq_integral_xiLine {t : ℝ} (ht : 0 < t) (X y : ℝ) :
    riemannHeat t ((X : ℂ) + I * y) =
      ∫ w, (gaussDensity t (w + y) : ℂ) * xiLine X w := by
  rw [riemannHeat_eq_integral_gaussian_xi ht, ← integral_add_right_eq_self _ y]
  congr 1
  funext w
  unfold xiLine
  congr 2
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- An explicit upper bound relative to `ξ(33/2+iX)`, valid down to arbitrarily small heat. -/
theorem norm_riemannHeat_le_sixteen_exp {t X : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX : 16 ≤ X) (y : ℝ) :
    ‖riemannHeat t ((X : ℂ) + I * y)‖ ≤ 4 * ‖xiLine X 16‖ *
      Real.exp (((Real.log X + xiSliceGlobalConstant) / 2) * |y| + y ^ 2 +
        2 * t * ((Real.log X + xiSliceGlobalConstant) / 2) ^ 2) := by
  set B := (Real.log X + xiSliceGlobalConstant) / 2
  have hB : 0 ≤ B := by
    have hl := Real.log_nonneg (show 1 ≤ X by linarith)
    have hk := xiSliceGlobalConstant_pos
    dsimp [B]
    linarith
  rw [riemannHeat_eq_integral_xiLine ht]
  have hn : ‖∫ w, (gaussDensity t (w + y) : ℂ) * xiLine X w‖ ≤
      ∫ w, gaussDensity t (w + y) * ‖xiLine X w‖ := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    congr 1
    funext w
    simpa only [sub_neg_eq_add] using norm_gauss_mul t (-y) w ht (xiLine X w)
  have h := integral_gauss_shift_norm_le ht ht8 hB (norm_nonneg (xiLine X 16))
    (norm_xiLine_le_sixteen_exp hX) (-y)
  simp only [sub_neg_eq_add, abs_neg, neg_sq] at h
  exact hn.trans h

private theorem heatWindow_log_bounds {X x : ℝ} (hX : 4096 ≤ X) (hL : 20 ≤ Real.log X)
    (hx : |x - X| ≤ 64) :
    2048 ≤ x ∧ Real.log x ≤ 2 * Real.log X ∧
      (horizontalSlope x).re ≤ Real.log X ∧
      (Real.log x + xiSliceGlobalConstant) / 2 ≤ 2 * Real.log X := by
  have hxlo : X - 64 ≤ x := by linarith [(abs_le.mp hx).1]
  have hxhi : x ≤ X + 64 := by linarith [(abs_le.mp hx).2]
  have hx0 : 0 < x := by linarith
  have hxpow : x ≤ X ^ 2 := by nlinarith only [hxhi, hX]
  have hlx := Real.log_le_log hx0 hxpow
  rw [Real.log_pow] at hlx
  norm_num only [Nat.cast_ofNat] at hlx
  have hratio : Real.log (x / (2 * Real.pi)) ≤ Real.log x :=
    Real.log_le_log (by positivity) (div_le_self hx0.le (by nlinarith only [Real.pi_gt_three]))
  have hslope : (horizontalSlope x).re ≤ Real.log X := by
    rw [horizontalSlope_re]
    linarith only [hratio, hlx]
  refine ⟨by linarith, hlx, hslope, ?_⟩
  linarith only [hlx, hL, xiSliceGlobalConstant_le_sixteen]

private theorem hasDerivAt_xiLine_height (x : ℝ) :
    HasDerivAt (fun v : ℝ => xiLine v 16) (I * xiLineDeriv x 16) x := by
  have hin : HasDerivAt (fun v : ℂ => (1 / 2 : ℂ) + 16 + I * v) I (x : ℂ) := by
    have h := ((hasDerivAt_id' (x : ℂ)).const_mul I).const_add ((1 / 2 : ℂ) + 16)
    simpa only [mul_one] using h
  have h := (xi_differentiable ((1 / 2 : ℂ) + 16 + I * x)).hasDerivAt.comp (x : ℂ) hin
  simpa only [xiLine, xiLineDeriv, Complex.ofReal_ofNat, Function.comp_def, mul_comm I] using h.comp_ofReal

/-- Euler values at nearby heights differ by at most a fixed power of the height. -/
theorem norm_xiLine_sixteen_near_le {X x : ℝ} (hX : 4096 ≤ X) (hL : 20 ≤ Real.log X)
    (hx : |x - X| ≤ 64) :
    ‖xiLine x 16‖ ≤ ‖xiLine X 16‖ * Real.exp (128 * Real.log X) := by
  have hL0 : 0 < 2 * Real.log X := by linarith
  have hxlo : X - 64 ≤ x := by linarith [(abs_le.mp hx).1]
  have hxhi : x ≤ X + 64 := by linarith [(abs_le.mp hx).2]
  have hsub : uIcc X x ⊆ Icc (X - 64) (X + 64) :=
    uIcc_subset_Icc ⟨by linarith, by linarith⟩ ⟨hxlo, hxhi⟩
  have hb : ∀ s ∈ uIcc X x, ‖I * xiLineDeriv s 16 - (0 : ℂ) * xiLine s 16‖ ≤
      (2 * Real.log X) * ‖xiLine s 16‖ := by
    intro s hs
    have hs' := hsub hs
    have habs : |s - X| ≤ 64 := abs_le.mpr ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
    obtain ⟨hslo, -, hsl, -⟩ := heatWindow_log_bounds hX hL habs
    have hd := norm_xiLineDeriv_le (by linarith : 200 ≤ s) (by norm_num : (9 / 2 : ℝ) ≤ 16)
    have hfrac : (16 + 1 / 2 : ℝ) / (2 * s) ≤ 1 := by
      rw [div_le_one (by linarith : 0 < 2 * s)]
      linarith
    rw [zero_mul, sub_zero, norm_mul, norm_I, one_mul]
    refine hd.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [← horizontalSlope_re]
    linarith only [hsl, hfrac, hL]
  have hm := GaloisForLFunctions.HTGeometry.norm_sub_mul_exp_le (a := (0 : ℂ)) hL0
    (u := X) (w := x) (fun s _ => hasDerivAt_xiLine_height s) hb
  simp only [mul_zero, Complex.exp_zero, mul_one, Complex.zero_re, Real.exp_zero] at hm
  have hn := norm_sub_norm_le (xiLine x 16) (xiLine X 16)
  calc
    _ ≤ ‖xiLine X 16‖ * Real.exp ((2 * Real.log X) * |x - X|) := by nlinarith only [hn, hm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      nlinarith only [mul_le_mul_of_nonneg_left hx hL0.le]

/-- Uniform polynomial relative growth on a fixed rectangle when `t log X ≤ 1`. -/
theorem norm_riemannHeat_near_le {t X x y : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX : 4096 ≤ X) (hL : 20 ≤ Real.log X) (htL : t * Real.log X ≤ 1)
    (hx : |x - X| ≤ 64) (hy : |y| ≤ 64) :
    ‖riemannHeat t ((x : ℂ) + I * y)‖ ≤
      4 * ‖xiLine X 16‖ * Real.exp (4096 + 264 * Real.log X) := by
  obtain ⟨hxlo, -, -, hBhi⟩ := heatWindow_log_bounds hX hL hx
  set B := (Real.log x + xiSliceGlobalConstant) / 2
  have hB0 : 0 ≤ B := by
    have hl := Real.log_nonneg (show 1 ≤ x by linarith)
    have hk := xiSliceGlobalConstant_pos
    dsimp [B]
    linarith
  have hL0 : 0 ≤ Real.log X := by linarith
  have hBsq : B ^ 2 ≤ 4 * (Real.log X) ^ 2 := by
    nlinarith only [hB0, hBhi, mul_nonneg (sub_nonneg.mpr hBhi) (add_nonneg hB0 (by positivity : 0 ≤ 2 * Real.log X))]
  have hheat : 2 * t * B ^ 2 ≤ 8 * Real.log X := by
    have h1 := mul_le_mul_of_nonneg_left hBsq (show 0 ≤ 2 * t by positivity)
    have h2 := mul_le_mul_of_nonneg_right htL hL0
    nlinarith only [h1, h2]
  have hlin : B * |y| ≤ 128 * Real.log X := by
    have h := mul_le_mul hBhi hy (abs_nonneg y) (show 0 ≤ 2 * Real.log X by positivity)
    nlinarith only [h]
  have hysq : y ^ 2 ≤ 4096 := by
    have h := mul_nonneg (show 0 ≤ 64 - |y| by linarith) (show 0 ≤ 64 + |y| by positivity)
    nlinarith only [h, sq_abs y]
  have he : B * |y| + y ^ 2 + 2 * t * B ^ 2 ≤ 4096 + 136 * Real.log X := by
    linarith only [hheat, hlin, hysq]
  have hg := norm_riemannHeat_le_sixteen_exp ht ht8 (by linarith : 16 ≤ x) y
  have hv := norm_xiLine_sixteen_near_le hX hL hx
  calc
    _ ≤ 4 * ‖xiLine x 16‖ * Real.exp (B * |y| + y ^ 2 + 2 * t * B ^ 2) := hg
    _ ≤ 4 * (‖xiLine X 16‖ * Real.exp (128 * Real.log X)) *
        Real.exp (4096 + 136 * Real.log X) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hv (by norm_num)) (Real.exp_le_exp.mpr he)
        (Real.exp_pos _).le (by positivity)
    _ = _ := by
      have heq : Real.exp (128 * Real.log X) * Real.exp (4096 + 136 * Real.log X) =
          Real.exp (4096 + 264 * Real.log X) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc _ = (4 * ‖xiLine X 16‖) *
          (Real.exp (128 * Real.log X) * Real.exp (4096 + 136 * Real.log X)) := by ring
        _ = _ := by rw [heq]

/-- The same rectangle estimate includes the unheated function. -/
theorem norm_riemannHeat_near_le_of_nonneg {t X x y : ℝ} (ht : 0 ≤ t) (ht8 : t ≤ 1 / 8)
    (hX : 4096 ≤ X) (hL : 20 ≤ Real.log X) (htL : t * Real.log X ≤ 1)
    (hx : |x - X| ≤ 64) (hy : |y| ≤ 64) :
    ‖riemannHeat t ((x : ℂ) + I * y)‖ ≤
      4 * ‖xiLine X 16‖ * Real.exp (4096 + 264 * Real.log X) := by
  rcases ht.eq_or_lt with hzero | hpos
  · subst t
    obtain ⟨hxlo, -, -, hBhi⟩ := heatWindow_log_bounds hX hL hx
    set B := (Real.log x + xiSliceGlobalConstant) / 2
    have hB0 : 0 ≤ B := by
      have hl := Real.log_nonneg (show 1 ≤ x by linarith)
      have hk := xiSliceGlobalConstant_pos
      dsimp [B]
      linarith
    have hlin : B * |y| ≤ 128 * Real.log X := by
      have h := mul_le_mul hBhi hy (abs_nonneg y) (show 0 ≤ 2 * Real.log X by linarith)
      nlinarith only [h]
    have hysq : y ^ 2 ≤ 4096 := by
      have h := mul_nonneg (show 0 ≤ 64 - |y| by linarith) (show 0 ≤ 64 + |y| by positivity)
      nlinarith only [h, sq_abs y]
    have he : B * |y| + y ^ 2 / 2 ≤ 4096 + 136 * Real.log X := by
      nlinarith only [hlin, hysq, hL]
    have hg := norm_xiLine_le_sixteen_exp (by linarith : 16 ≤ x) (-y)
    simp only [abs_neg, neg_sq] at hg
    have hv := norm_xiLine_sixteen_near_le hX hL hx
    have hpt : riemannHeat 0 ((x : ℂ) + I * y) = xiLine x (-y) := by
      rw [riemannHeat_zero, xiLine]
      congr 1
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [hpt]
    calc
      _ ≤ ‖xiLine x 16‖ * Real.exp (B * |y| + y ^ 2 / 2) := hg
      _ ≤ (‖xiLine X 16‖ * Real.exp (128 * Real.log X)) *
          Real.exp (4096 + 136 * Real.log X) :=
        mul_le_mul hv (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)
      _ = ‖xiLine X 16‖ * Real.exp (4096 + 264 * Real.log X) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := by nlinarith only [norm_nonneg (xiLine X 16), Real.exp_pos (4096 + 264 * Real.log X)]
  · exact norm_riemannHeat_near_le hpos ht8 hX hL htL hx hy

end

end RHTower.DeBruijn

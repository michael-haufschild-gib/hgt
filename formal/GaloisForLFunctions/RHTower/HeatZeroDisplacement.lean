import GaloisForLFunctions.RHTower.HeatShrinkingWindow
import GaloisForLFunctions.RHTower.HeatRelativeGlobalBounds
import GaloisForLFunctions.RHTower.HeatGaussianQuadraticError

/-!
# Uniform displacement of zeros under small positive heat

An unheated zero has a heat zero within distance `d` whenever
`t log X ≤ c d²`, with absolute constants and a height threshold
independent of `d`. Centering each local zero factor controls the reverse
Gaussian on a fixed interval, so shrinking depths cause no tail loss.
-/

open Complex MeasureTheory Set Metric Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

private theorem normalized_heat_global_envelope {t X A B G : ℝ} {s a : ℂ}
    (hL : 1 ≤ Real.log X) (hG : 0 ≤ G)
    (hsre : |s.re - X| ≤ 1) (hsim : |s.im| ≤ 1)
    (hs : ‖xiLine X 16‖ / 8 * Real.exp (-(A * Real.log X)) ≤ ‖riemannHeat t s‖)
    (ha : ‖a‖ ≤ B * Real.log X)
    (hg : ∀ x y : ℝ, |y| ≤ 1 → ‖riemannHeat t ((x : ℂ) + I * y)‖ ≤
      ‖xiLine X 16‖ * Real.exp (G * Real.log X * (1 + |x - X|))) (u : ℝ) :
    ‖Complex.exp (-(u : ℂ) * a) * riemannHeat t (s + u) / riemannHeat t s‖ ≤
      Real.exp ((8 + 2 * G + A) * Real.log X + (B + G) * Real.log X * |u|) := by
  let N := ‖xiLine X 16‖
  have hN : 0 < N := by
    apply norm_pos_iff.mpr
    apply xi_ne_zero_of_one_lt_re
    norm_num [xiLine]
  have hmin : 0 < N / 8 * Real.exp (-(A * Real.log X)) := by positivity
  have hnorm : 0 < ‖riemannHeat t s‖ := hmin.trans_le hs
  have hL0 : 0 ≤ Real.log X := by linarith only [hL]
  have hphase : ‖Complex.exp (-(u : ℂ) * a)‖ ≤ Real.exp (B * Real.log X * |u|) := by
    have hneg : -(u * a.re) ≤ |u| * (B * Real.log X) := by
      calc
        _ ≤ |u * a.re| := neg_le_abs _
        _ = |u| * |a.re| := abs_mul _ _
        _ ≤ |u| * ‖a‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm a) (abs_nonneg u)
        _ ≤ _ := mul_le_mul_of_nonneg_left ha (abs_nonneg u)
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (-(u : ℂ) * a).re = -(u * a.re) := by simp
    rw [hre]
    nlinarith only [hneg]
  have hshift : |(s + (u : ℂ)).re - X| ≤ 1 + |u| := by
    rw [Complex.add_re, Complex.ofReal_re,
      show s.re + u - X = (s.re - X) + u by ring]
    exact (abs_add_le _ _).trans (add_le_add hsre le_rfl)
  have hpoint : ((s + (u : ℂ)).re : ℂ) + I * (s + (u : ℂ)).im = s + u := by
    simpa only [mul_comm I] using Complex.re_add_im (s + (u : ℂ))
  have hheat : ‖riemannHeat t (s + u)‖ ≤ N * Real.exp (G * Real.log X * (2 + |u|)) := by
    have h := hg (s + (u : ℂ)).re (s + (u : ℂ)).im (by simpa using hsim)
    rw [hpoint] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    have hb := mul_le_mul_of_nonneg_left hshift (mul_nonneg hG hL0)
    nlinarith only [hb]
  have height : (8 : ℝ) ≤ Real.exp (8 * Real.log X) := by
    linarith only [Real.add_one_le_exp (8 * Real.log X), hL]
  rw [norm_div, norm_mul]
  calc
    _ ≤ (Real.exp (B * Real.log X * |u|) *
        (N * Real.exp (G * Real.log X * (2 + |u|)))) / ‖riemannHeat t s‖ :=
      div_le_div_of_nonneg_right (mul_le_mul hphase hheat (norm_nonneg _) (Real.exp_pos _).le)
        hnorm.le
    _ ≤ (Real.exp (B * Real.log X * |u|) *
        (N * Real.exp (G * Real.log X * (2 + |u|)))) /
          (N / 8 * Real.exp (-(A * Real.log X))) :=
      div_le_div_of_nonneg_left (by positivity) hmin hs
    _ = 8 * Real.exp (B * Real.log X * |u| + G * Real.log X * (2 + |u|) + A * Real.log X) := by
      rw [Real.exp_neg, Real.exp_add, Real.exp_add]
      field_simp [hN.ne']
    _ ≤ Real.exp (8 * Real.log X) *
        Real.exp (B * Real.log X * |u| + G * Real.log X * (2 + |u|) + A * Real.log X) :=
      mul_le_mul_of_nonneg_right height (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Zero displacement is at most the square-root scale of `t log X`, uniformly
over shrinking disks and without a zero-separation or multiplicity assumption. -/
theorem exists_riemannHeat_zero_in_shrinking_ball :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ d : ℝ, 0 < d → d ≤ 1 / 2 →
        ∀ t : ℝ, 0 < t → t * Real.log X ≤ c * d ^ 2 →
          ∀ z : ℂ, z.re = X → |z.im| ≤ 1 / 2 → riemannHeat 0 z = 0 →
            ∃ ζ : ℂ, riemannHeat t ζ = 0 ∧ ‖ζ - z‖ ≤ d := by
  obtain ⟨G, hG, X₁, hX₁, hglobal⟩ := exists_riemannHeat_global_relative_bound
  obtain ⟨C, hC, X₂, hX₂, hwindow⟩ := exists_riemannHeat_shrinking_window_bounds
  let R : ℝ := 1 / 32
  let M := 8 + 2 * G + C + Real.log 32
  let D₀ := C + G
  have hR : 0 < R := by norm_num [R]
  have hlog32 : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  have hM : 0 < M := by dsimp [M]; positivity
  have hD₀ : 0 < D₀ := by dsimp [D₀]; positivity
  let c := min 1 (min (1 / (64 * C)) (min (R / (8 * D₀)) (R ^ 2 / (8 * M))))
  have hc : 0 < c := by dsimp [c]; positivity
  have hc_all : c ≤ min 1 (min (1 / (64 * C)) (min (R / (8 * D₀)) (R ^ 2 / (8 * M)))) := le_rfl
  simp only [le_min_iff] at hc_all
  obtain ⟨hc1, hcs, hct, hce⟩ := hc_all
  refine ⟨c, hc, X₁ + X₂ + Real.exp 20, ?_, ?_⟩
  · linarith only [hX₁, hX₂, Real.exp_pos 20]
  intro X hX₀ d hd hd2 t ht htc z hzre hzim hz0
  have hX1 : X₁ ≤ X := by linarith only [hX₀, hX₂, Real.exp_pos 20]
  have hX2 : X₂ ≤ X := by linarith only [hX₀, hX₁, Real.exp_pos 20]
  have hL : 20 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 20)
      (show Real.exp 20 ≤ X by linarith only [hX₀, hX₁, hX₂])
    simpa only [Real.log_exp] using h
  have hL0 : 0 < Real.log X := by linarith only [hL]
  have hd1 : d ≤ 1 := by linarith only [hd2]
  have hd21 : d ^ 2 ≤ 1 := by nlinarith only [hd1, hd]
  have htL : t * Real.log X ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hd21 hc.le
    nlinarith only [htc, h, hc1]
  have ht8 : t ≤ 1 / 8 := by
    have h := mul_le_mul_of_nonneg_left hL ht.le
    nlinarith only [h, htL]
  rcases hwindow X hX2 t ht.le ht8 htL d hd hd2 z hzre hzim with hzero | hb
  · exact hzero
  exfalso
  let r := d / 32
  have hr : 0 < r := by dsimp [r]; positivity
  have hpaid : t * C * Real.log X ≤ d ^ 2 / 64 := by
    have h1 := mul_le_mul_of_nonneg_left htc hC.le
    have h2 := (le_div_iff₀ (by positivity : 0 < 64 * C)).mp hcs
    have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg d)
    nlinarith only [h1, h3]
  have htK : t * (C * Real.log X / d ^ 2) ≤ 1 / 64 := by
    rw [show t * (C * Real.log X / d ^ 2) = (t * C * Real.log X) / d ^ 2 by ring]
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith only [hpaid]
  have hsaddle : 2 * t * (C * Real.log X / d) ≤ r := by
    rw [show 2 * t * (C * Real.log X / d) = (2 * t * C * Real.log X) / d by ring]
    apply (div_le_iff₀ hd).mpr
    dsimp [r]
    nlinarith only [hpaid]
  have hdiff := differentiable_riemannHeat ht.le
  obtain ⟨s, hs, hseq⟩ := exists_logDeriv_saddle (f := riemannHeat t) (z := z)
    hr ht.le hsaddle hdiff.differentiableOn
    (fun w hw => (hb w (by
      have h := mem_ball_iff_norm.mp hw
      dsimp [r] at h
      linarith only [h, hd])).1)
    (fun w hw => (hb w (by
      have h := mem_ball_iff_norm.mp hw
      dsimp [r] at h
      linarith only [h, hd])).2.1)
  have hs8 : ‖s - z‖ ≤ d / 8 := by dsimp [r] at hs; linarith only [hs, hd]
  obtain ⟨hsne, ha₀, hfloor, hlocal₀⟩ := hb s hs8
  let a := deriv (riemannHeat t) s / riemannHeat t s
  have hsa : s = z + 2 * (t : ℂ) * a := hseq
  let F : ℝ → ℂ := fun u =>
    Complex.exp (-(u : ℂ) * a) * riemannHeat t (s + u) / riemannHeat t s
  have hF : Continuous F := by
    have hcont := hdiff.continuous
    dsimp [F]
    fun_prop
  let E := 8 + 2 * G + C / d
  let D := C / d + G
  have hE : 0 < E := by dsimp [E]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hCd : C * d ≤ C := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hd1 hC.le
  have hGd : G * d ^ 2 ≤ G := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hd21 hG.le
  have hDscale : d ^ 2 * D ≤ D₀ := by
    have he : d ^ 2 * D = C * d + G * d ^ 2 := by dsimp [D]; field_simp
    rw [he]
    exact add_le_add hCd hGd
  have hEscale : d ^ 2 * (E + Real.log 32) ≤ M := by
    have hB : 0 ≤ 8 + 2 * G + Real.log 32 := by positivity
    have hBpaid := mul_le_mul_of_nonneg_left hd21 hB
    have he : d ^ 2 * (E + Real.log 32) =
        (8 + 2 * G + Real.log 32) * d ^ 2 + C * d := by
      dsimp [E]
      field_simp
      ring
    rw [he]
    dsimp [M]
    nlinarith only [hBpaid, hCd]
  have htD : t * (D * Real.log X) ≤ R / 8 := by
    have h1 := mul_le_mul_of_nonneg_right htc hD.le
    have h2 := mul_le_mul_of_nonneg_left hDscale hc.le
    have h3 := (le_div_iff₀ (by positivity : 0 < 8 * D₀)).mp hct
    calc
      _ = (t * Real.log X) * D := by ring
      _ ≤ (c * d ^ 2) * D := h1
      _ = c * (d ^ 2 * D) := by ring
      _ ≤ c * D₀ := h2
      _ ≤ R / 8 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
        calc
          _ = c * (8 * D₀) := by ring
          _ ≤ R := h3
  have htE : t * Real.log X * (E + Real.log 32) ≤ R ^ 2 / 8 := by
    have h1 := mul_le_mul_of_nonneg_right htc (show 0 ≤ E + Real.log 32 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hEscale hc.le
    have h3 := (le_div_iff₀ (by positivity : 0 < 8 * M)).mp hce
    calc
      _ ≤ (c * d ^ 2) * (E + Real.log 32) := h1
      _ = c * (d ^ 2 * (E + Real.log 32)) := by ring
      _ ≤ c * M := h2
      _ ≤ R ^ 2 / 8 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
        calc
          _ = c * (8 * M) := by ring
          _ ≤ R ^ 2 := h3
  have hsre : |s.re - X| ≤ 1 := by
    have h := Complex.abs_re_le_norm (s - z)
    rw [Complex.sub_re, hzre] at h
    linarith only [h, hs8, hd2]
  have hsim : |s.im| ≤ 1 := by
    have h := Complex.abs_im_le_norm (s - z)
    rw [Complex.sub_im] at h
    have htri : |s.im| ≤ |s.im - z.im| + |z.im| := by
      simpa only [sub_add_cancel] using abs_add_le (s.im - z.im) z.im
    linarith only [h, hs8, htri, hzim, hd2]
  have hA : (C / d) * Real.log X = C * Real.log X / d := by ring
  have henv : ∀ u : ℝ, ‖F u‖ ≤ Real.exp (E * Real.log X + (D * Real.log X) * |u|) := by
    intro u
    exact normalized_heat_global_envelope (A := C / d) (B := C / d)
      (by linarith only [hL]) hG.le hsre hsim
      (by rw [hA]; exact hfloor) (by rw [hA]; exact ha₀)
      (hglobal X hX1 t ht.le ht8 htL) u
  obtain ⟨_, herr⟩ := integral_gaussDensity_quadratic_error_le ht hR
    (show 0 ≤ C * Real.log X / d ^ 2 by positivity)
    (mul_nonneg hE.le hL0.le) (mul_nonneg hD.le hL0.le)
    (by linarith only [htK]) htD hF hlocal₀ henv
  have htail : Real.exp (E * Real.log X - R ^ 2 / (8 * t)) ≤ (1 / 32 : ℝ) := by
    have hpaid : Real.log X * (E + Real.log 32) ≤ R ^ 2 / (8 * t) := by
      rw [le_div_iff₀ (by positivity : 0 < 8 * t)]
      calc
        _ = (t * Real.log X * (E + Real.log 32)) * 8 := by ring
        _ ≤ (R ^ 2 / 8) * 8 := mul_le_mul_of_nonneg_right htE (by norm_num)
        _ = _ := by ring
    have hlog := mul_le_mul_of_nonneg_left (show 1 ≤ Real.log X by linarith only [hL]) hlog32
    calc
      _ ≤ Real.exp (-Real.log 32) := Real.exp_le_exp.mpr (by nlinarith only [hpaid, hlog])
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hsmall : ‖(∫ u : ℝ, (gaussDensity t u : ℂ) * F u) - 1‖ ≤ 1 / 2 := by
    nlinarith only [herr, htK, htail]
  have hI : (∫ u : ℝ, (gaussDensity t u : ℂ) * F u) ≠ 0 := by
    intro hzero
    rw [hzero, zero_sub, norm_neg, norm_one] at hsmall
    norm_num at hsmall
  have hreverse := riemannHeat_zero_eq_reverse_saddle ht z a
  rw [← hsa] at hreverse
  have hint : (∫ u : ℝ, (gaussDensity t u : ℂ) * Complex.exp (-(u : ℂ) * a) *
      riemannHeat t (s + u)) =
      (∫ u : ℝ, (gaussDensity t u : ℂ) * F u) * riemannHeat t s := by
    rw [← integral_mul_const]
    congr 1
    funext u
    dsimp [F]
    field_simp [hsne]
  rw [hint, hz0] at hreverse
  exact (mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero hI hsne)) hreverse.symm

/-- Nonreal heat zeros persist uniformly down to shrinking positive depths. -/
theorem exists_nonreal_riemannHeat_zero_at_uniform_depth_scale :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ d : ℝ, 0 < d → d ≤ 1 / 2 →
        ∀ t : ℝ, 0 < t → t * Real.log X ≤ c * d ^ 2 →
          ∀ z : ℂ, z.re = X → d ≤ |z.im| → |z.im| ≤ 1 / 2 → riemannHeat 0 z = 0 →
            ∃ ζ : ℂ, riemannHeat t ζ = 0 ∧ ζ.im ≠ 0 ∧ ‖ζ - z‖ ≤ d / 2 := by
  obtain ⟨c, hc, X₀, hX₀, hnear⟩ := exists_riemannHeat_zero_in_shrinking_ball
  refine ⟨c / 4, by positivity, X₀, hX₀, ?_⟩
  intro X hX d hd hd2 t ht htd z hzre hzdepth hzim hz0
  obtain ⟨ζ, hζ, hdist⟩ := hnear X hX (d / 2) (by positivity)
    (by linarith only [hd2]) t ht (by nlinarith only [htd]) z hzre hzim hz0
  refine ⟨ζ, hζ, ?_, hdist⟩
  intro him
  have h := Complex.abs_im_le_norm (ζ - z)
  rw [Complex.sub_im, him, zero_sub, abs_neg] at h
  linarith only [h, hdist, hzdepth, hd]

end

end RHTower.DeBruijn

import GaloisForLFunctions.RHTower.HeatRelativeGlobalBounds
import GaloisForLFunctions.RHTower.HeatZeroFreeWindow
import GaloisForLFunctions.RHTower.HeatGaussianQuadraticError
import GaloisForLFunctions.HTGeometry.LogDerivativeSaddle

/-!
# Persistence of deep zeros at inverse-logarithmic heat

An unheated zero at fixed positive depth forces a nearby nonreal heat
zero for times of order `1 / log X`. If a height window contained only
real heat zeros, its minimum modulus and logarithmic derivatives would
give a complex saddle. The translated reverse Gaussian would then be
nonzero, contradicting the unheated zero.
-/

open Complex MeasureTheory Set Metric Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

private theorem norm_heat_saddle_profile_le {t X A B C : ℝ} {s a : ℂ}
    (hL : 1 ≤ Real.log X) (hC : 0 ≤ C)
    (hsre : |s.re - X| ≤ 1) (hsim : |s.im| ≤ 1)
    (hs : ‖xiLine X 16‖ / 8 * Real.exp (-(A * Real.log X)) ≤ ‖riemannHeat t s‖)
    (ha : ‖a‖ ≤ B * Real.log X)
    (hg : ∀ x y : ℝ, |y| ≤ 1 → ‖riemannHeat t ((x : ℂ) + I * y)‖ ≤
      ‖xiLine X 16‖ * Real.exp (C * Real.log X * (1 + |x - X|))) (u : ℝ) :
    ‖Complex.exp (-(u : ℂ) * a) * riemannHeat t (s + u) / riemannHeat t s‖ ≤
      Real.exp ((8 + 2 * C + A) * Real.log X + (B + C) * Real.log X * |u|) := by
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
  have hheat : ‖riemannHeat t (s + u)‖ ≤ N * Real.exp (C * Real.log X * (2 + |u|)) := by
    have h := hg (s + (u : ℂ)).re (s + (u : ℂ)).im (by simpa using hsim)
    rw [hpoint] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    have hb := mul_le_mul_of_nonneg_left hshift (mul_nonneg hC hL0)
    nlinarith only [hb]
  have height : (8 : ℝ) ≤ Real.exp (8 * Real.log X) := by
    linarith only [Real.add_one_le_exp (8 * Real.log X), hL]
  rw [norm_div, norm_mul]
  calc
    _ ≤ (Real.exp (B * Real.log X * |u|) *
        (N * Real.exp (C * Real.log X * (2 + |u|)))) / ‖riemannHeat t s‖ :=
      div_le_div_of_nonneg_right (mul_le_mul hphase hheat (norm_nonneg _) (Real.exp_pos _).le)
        hnorm.le
    _ ≤ (Real.exp (B * Real.log X * |u|) *
        (N * Real.exp (C * Real.log X * (2 + |u|)))) /
          (N / 8 * Real.exp (-(A * Real.log X))) :=
      div_le_div_of_nonneg_left (by positivity) hmin hs
    _ = 8 * Real.exp (B * Real.log X * |u| + C * Real.log X * (2 + |u|) + A * Real.log X) := by
      rw [Real.exp_neg, Real.exp_add, Real.exp_add]
      field_simp [hN.ne']
    _ ≤ Real.exp (8 * Real.log X) *
        Real.exp (B * Real.log X * |u| + C * Real.log X * (2 + |u|) + A * Real.log X) :=
      mul_le_mul_of_nonneg_right height (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- At every fixed positive depth, an unheated zero forces a nearby nonreal heat
zero for all sufficiently small inverse-logarithmic times. -/
theorem exists_nonreal_riemannHeat_zero_at_inverse_log_scale {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ t : ℝ, 0 < t → t * Real.log X ≤ c →
        ∀ z : ℂ, z.re = X → δ ≤ |z.im| → |z.im| ≤ 1 / 2 → riemannHeat 0 z = 0 →
          ∃ ζ : ℂ, riemannHeat t ζ = 0 ∧ ζ.im ≠ 0 ∧ |ζ.re - X| ≤ 1 := by
  obtain ⟨C, hC, X₁, hX₁, hglobal⟩ := exists_riemannHeat_global_relative_bound
  obtain ⟨A, B, hA, hB, X₂, hX₂, hwindow⟩ := exists_riemannHeat_window_bounds hδ hδ2
  let r := δ / 32
  let E := 8 + 2 * C + A
  let D := B + C
  have hr : 0 < r := by dsimp [r]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hlog32 : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  let c := min 1 (min (δ / (64 * B)) (min (1 / (32 * B))
    (min (r / (8 * D)) (r ^ 2 / (8 * (E + Real.log 32))))))
  have hc : 0 < c := by dsimp [c]; positivity
  have hc_all : c ≤ min 1 (min (δ / (64 * B)) (min (1 / (32 * B))
      (min (r / (8 * D)) (r ^ 2 / (8 * (E + Real.log 32)))))) := le_rfl
  simp only [le_min_iff] at hc_all
  obtain ⟨hc1, hcs, hcl, hct, hce⟩ := hc_all
  refine ⟨c, hc, X₁ + X₂ + Real.exp 20, ?_, ?_⟩
  · linarith only [hX₁, hX₂, Real.exp_pos 20]
  intro X hX₀ t ht htc z hzre hzδ hzim hz0
  have hX1 : X₁ ≤ X := by linarith only [hX₀, hX₂, Real.exp_pos 20]
  have hX2 : X₂ ≤ X := by linarith only [hX₀, hX₁, Real.exp_pos 20]
  have hL : 20 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 20)
      (show Real.exp 20 ≤ X by linarith only [hX₀, hX₁, hX₂])
    simpa only [Real.log_exp] using h
  have hL0 : 0 < Real.log X := by linarith only [hL]
  have htL : t * Real.log X ≤ 1 := htc.trans hc1
  have ht8 : t ≤ 1 / 8 := by
    have h := mul_le_mul_of_nonneg_left hL ht.le
    nlinarith only [h, htL]
  rcases hwindow X hX2 t ht.le ht8 htL z hzre hzδ hzim with hzero | ⟨hfloor, hq, hq'⟩
  · exact hzero
  exfalso
  have hN : 0 < ‖xiLine X 16‖ := by
    apply norm_pos_iff.mpr
    apply xi_ne_zero_of_one_lt_re
    norm_num [xiLine]
  have hfree : ∀ w : ℂ, ‖w - z‖ ≤ δ / 2 → riemannHeat t w ≠ 0 := by
    intro w hw
    exact norm_pos_iff.mp ((show 0 < ‖xiLine X 16‖ / 8 *
      Real.exp (-(A * Real.log X)) by positivity).trans_le (hfloor w hw))
  have htB : t * (B * Real.log X) ≤ δ / 64 := by
    have h := (le_div_iff₀ (by positivity : 0 < 64 * B)).mp (htc.trans hcs)
    nlinarith only [h]
  have htK : t * (B * Real.log X) ≤ 1 / 32 := by
    have h := (le_div_iff₀ (by positivity : 0 < 32 * B)).mp (htc.trans hcl)
    nlinarith only [h]
  have htD : t * (D * Real.log X) ≤ r / 8 := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * D)).mp (htc.trans hct)
    nlinarith only [h]
  have hdiff := differentiable_riemannHeat ht.le
  obtain ⟨s, hs, hseq⟩ := exists_logDeriv_saddle (f := riemannHeat t) (z := z)
    (K := B * Real.log X) hr ht.le
    (by dsimp [r]; nlinarith only [htB]) hdiff.differentiableOn
    (fun w hw => hfree w (by
      have h := mem_ball_iff_norm.mp hw
      dsimp [r] at h
      linarith only [h, hδ]))
    (fun w hw => hq w (by
      have h := mem_ball_iff_norm.mp hw
      dsimp [r] at h
      linarith only [h, hδ]))
  let a := deriv (riemannHeat t) s / riemannHeat t s
  have hsa : s = z + 2 * (t : ℂ) * a := hseq
  have hsδ : ‖s - z‖ ≤ δ / 2 := by dsimp [r] at hs; linarith only [hs, hδ]
  have hsne : riemannHeat t s ≠ 0 := hfree s hsδ
  have ha : ‖a‖ ≤ B * Real.log X := hq s (by dsimp [r] at hs; linarith only [hs, hδ])
  let F : ℝ → ℂ := fun u =>
    Complex.exp (-(u : ℂ) * a) * riemannHeat t (s + u) / riemannHeat t s
  have hF : Continuous F := by
    have hcont := hdiff.continuous
    dsimp [F]
    fun_prop
  have hlocal : ∀ u : ℝ, |u| ≤ r → ‖F u - 1‖ ≤ Real.exp ((B * Real.log X) * u ^ 2) - 1 := by
    intro u hu
    exact norm_exp_logDeriv_normalized_sub_one_le hr (mul_pos hB hL0) hdiff
      (fun w hw => hfree w (by dsimp [r] at hw; linarith only [hw, hδ]))
      (fun w hw => hq' w (by dsimp [r] at hw; linarith only [hw])) hs hu
  have hsre : |s.re - X| ≤ 1 := by
    have h := Complex.abs_re_le_norm (s - z)
    rw [Complex.sub_re, hzre] at h
    dsimp [r] at hs
    linarith only [h, hs, hδ2]
  have hsim : |s.im| ≤ 1 := by
    have h := Complex.abs_im_le_norm (s - z)
    rw [Complex.sub_im] at h
    have htri : |s.im| ≤ |s.im - z.im| + |z.im| := by
      simpa only [sub_add_cancel] using abs_add_le (s.im - z.im) z.im
    dsimp [r] at hs
    linarith only [h, hs, htri, hzim, hδ2]
  have henv : ∀ u : ℝ, ‖F u‖ ≤ Real.exp (E * Real.log X + (D * Real.log X) * |u|) := by
    intro u
    exact norm_heat_saddle_profile_le (by linarith only [hL]) hC.le hsre hsim
      (hfloor s hsδ) ha (hglobal X hX1 t ht.le ht8 htL) u
  obtain ⟨_, herr⟩ := integral_gaussDensity_quadratic_error_le ht hr
    (mul_nonneg hB.le hL0.le) (mul_nonneg hE.le hL0.le) (mul_nonneg hD.le hL0.le)
    (by linarith only [htK]) htD hF hlocal henv
  have htail : Real.exp (E * Real.log X - r ^ 2 / (8 * t)) ≤ (1 / 32 : ℝ) := by
    have hcap := (le_div_iff₀ (by positivity : 0 < 8 * (E + Real.log 32))).mp (htc.trans hce)
    have hpaid : Real.log X * (E + Real.log 32) ≤ r ^ 2 / (8 * t) := by
      rw [le_div_iff₀ (by positivity : 0 < 8 * t)]
      nlinarith only [hcap]
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

end

end RHTower.DeBruijn

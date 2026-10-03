import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovLogDeriv
import GaloisForLFunctions.RHTower.Sieve.VinogradovZetaGrowth
import GaloisForLFunctions.RHTower.ArgumentVariation
import GaloisForLFunctions.RHTower.Sieve.InvZetaEdgeBounds
import GaloisForLFunctions.RHTower.Sieve.InvZetaUniformStrip

/-!
# `1/ζ` on the Vinogradov–Korobov strip

Write `w = vkHadamardWidth(t + 1)`, `r = w/2`, `c₀ = 1 + r + it`.  The disc `|z - c₀| < 2r` lies in
the Vinogradov–Korobov zero-free region and in the growth region `‖ζ‖ ≤ C log(t+1)`, so `ζ` has an
analytic logarithm `g` there with `Re g ≤ log(C log(t+1))`, normalised by `g(c₀) = log ζ(c₀)`.
Since `‖1/ζ(c₀)‖ ≤ e^{11/2}(1 + 1/r)`, Borel–Carathéodory on `|z - c₀| ≤ 3r/2` gives

```text
‖1/ζ(σ + it)‖ ≤ e^{49} (C log(t+1))^7 (1 + 2/w)^7,      σ ≥ 1 - w/4,
```

a power of `log t`: the bound the Möbius contour needs.
-/

namespace RHTower.Sieve

open Complex Metric

noncomputable section

/-- The zero-free width is below the growth width. -/
theorem vkHadamardWidth_le_growthWidth {t : ℝ} (ht : Real.exp (Real.exp 30) ≤ t) :
    RHTower.vkHadamardWidth t ≤ vinogradovKorobovWidth (Real.log t) := by
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht
  have hL : Real.exp 30 ≤ Real.log t := by
    rw [← Real.log_exp (Real.exp 30)]; exact Real.log_le_log (Real.exp_pos _) ht
  have hl := one_le_log_of_exp_thirty_le hL
  have hL0 : 0 < Real.log t := lt_of_lt_of_le (Real.exp_pos _) hL
  have h1 : Real.log (Real.log t) ^ (-(5 : ℝ) / 3) ≤ Real.log (Real.log t) ^ (-(2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hA : 0 ≤ Real.log t ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg hL0.le _
  have hB : 0 ≤ Real.log (Real.log t) ^ (-(5 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  unfold RHTower.vkHadamardWidth vinogradovKorobovWidth
  have h2 := mul_le_mul_of_nonneg_left h1 hA
  have h3 : Real.log t ^ (-(2 : ℝ) / 3) * Real.log (Real.log t) ^ (-(2 : ℝ) / 3) / 10 ^ 8
      ≤ 1 / 100 * Real.log t ^ (-(2 : ℝ) / 3) * Real.log (Real.log t) ^ (-(2 : ℝ) / 3) := by
    have h0 : 0 ≤ Real.log t ^ (-(2 : ℝ) / 3) * Real.log (Real.log t) ^ (-(2 : ℝ) / 3) :=
      mul_nonneg hA (Real.rpow_nonneg (by linarith) _)
    linarith
  calc Real.log t ^ (-(2 : ℝ) / 3) * Real.log (Real.log t) ^ (-(5 : ℝ) / 3) / 10 ^ 8
      ≤ Real.log t ^ (-(2 : ℝ) / 3) * Real.log (Real.log t) ^ (-(2 : ℝ) / 3) / 10 ^ 8 :=
        div_le_div_of_nonneg_right h2 (by norm_num)
    _ ≤ _ := h3

/-- The zero-free width is at most `10⁻⁸`. -/
theorem vkHadamardWidth_le_inv {t : ℝ} (ht : Real.exp (Real.exp 1) ≤ t) :
    RHTower.vkHadamardWidth t ≤ 1 / 10 ^ 8 := by
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht
  have hL : Real.exp 1 ≤ Real.log t := by
    rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) ht
  have hL1 : 1 ≤ Real.log t := le_trans (by have := Real.add_one_le_exp 1; linarith) hL
  have hl : 1 ≤ Real.log (Real.log t) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hL
  unfold RHTower.vkHadamardWidth
  have h1 : Real.log t ^ (-(2 : ℝ) / 3) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have h2 : Real.log (Real.log t) ^ (-(5 : ℝ) / 3) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hl (by norm_num)
  have h3 := mul_le_mul h1 h2 (Real.rpow_nonneg (by linarith) _) zero_le_one
  exact div_le_div_of_nonneg_right (by linarith) (by norm_num)

/-- The positive constant of the growth bound. -/
theorem vinogradovKorobovGrowthConstant_ge : 11 ≤ vinogradovKorobovGrowthConstant := by
  unfold vinogradovKorobovGrowthConstant vinogradovKorobovBlockConstant
  have := Real.exp_pos 21
  linarith

/-- The disc estimate behind the `1/ζ` bound, at one centre.  All hypotheses concern the disc
`|z - c₀| < 2r` with `c₀ = 1 + r + it`. -/
theorem norm_inv_riemannZeta_le_of_disc {t r Λ : ℝ} {z₀ : ℂ} (hr : 0 < r)
    (hz0 : ∀ z ∈ ball (((1 + r : ℝ) : ℂ) + (t : ℂ) * I) (2 * r), z ≠ 1 ∧ riemannZeta z ≠ 0)
    (hgrowth : ∀ z ∈ ball (((1 + r : ℝ) : ℂ) + (t : ℂ) * I) (2 * r), ‖riemannZeta z‖ ≤ Λ)
    (hΛ : 1 ≤ Λ)
    (hz₀ : ‖z₀ - (((1 + r : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ 3 * r / 2) :
    ‖(riemannZeta z₀)⁻¹‖ ≤ Real.exp 49 * Λ ^ 7 * (1 + 1 / r) ^ 7 := by
  set c₀ : ℂ := ((1 + r : ℝ) : ℂ) + (t : ℂ) * I with hc₀
  have hR : 0 < 2 * r := by linarith
  have hc₀mem : c₀ ∈ ball c₀ (2 * r) := mem_ball_self hR
  have hz₀mem : z₀ ∈ ball c₀ (2 * r) := by
    rw [mem_ball, dist_eq_norm]; linarith
  -- an analytic logarithm
  have hdiff : DifferentiableOn ℂ riemannZeta (ball c₀ (2 * r)) := fun z hz =>
    (differentiableAt_riemannZeta (hz0 z hz).1).differentiableWithinAt
  obtain ⟨g, hg, hexp⟩ := exists_analyticOnNhd_exp_eq_ball hR (hdiff.analyticOnNhd isOpen_ball)
    (fun z hz => (hz0 z hz).2)
  have hζc₀ : riemannZeta c₀ ≠ 0 := (hz0 c₀ hc₀mem).2
  set g₁ : ℂ → ℂ := fun z => g z - g c₀ + Complex.log (riemannZeta c₀) with hg₁
  have hexp₁ : ∀ z ∈ ball c₀ (2 * r), Complex.exp (g₁ z) = riemannZeta z := by
    intro z hz
    simp only [hg₁, Complex.exp_add, Complex.exp_sub, Complex.exp_log hζc₀, hexp z hz,
      hexp c₀ hc₀mem]
    field_simp
  have hre : ∀ z ∈ ball c₀ (2 * r), (g₁ z).re = Real.log ‖riemannZeta z‖ := by
    intro z hz
    rw [← hexp₁ z hz, Complex.norm_exp, Real.log_exp]
  have hg₁diff : DifferentiableOn ℂ g₁ (ball c₀ (2 * r)) :=
    ((hg.differentiableOn.sub (differentiableOn_const _)).add (differentiableOn_const _))
  have hΛ0 : 0 < Λ := by linarith
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hReA : ∀ z ∈ ball c₀ (2 * r), (g₁ z).re ≤ Real.log Λ + 1 := by
    intro z hz
    rw [hre z hz]
    have := Real.log_le_log (norm_pos_iff.mpr (hz0 z hz).2) (hgrowth z hz)
    linarith
  have hReA' : (g₁ c₀).re < Real.log Λ + 1 := by
    have := hReA c₀ hc₀mem
    rw [hre c₀ hc₀mem]
    have h2 := Real.log_le_log (norm_pos_iff.mpr hζc₀) (hgrowth c₀ hc₀mem)
    linarith
  have hbc := RHTower.borel_caratheodory hg₁diff hReA hReA' hz₀mem
  -- the size at the centre
  have hgc : g₁ c₀ = Complex.log (riemannZeta c₀) := by simp [hg₁]
  have hc₀ne : c₀ ≠ 1 := (hz0 c₀ hc₀mem).1
  have hinv : ‖(riemannZeta c₀)⁻¹‖ ≤ Real.exp (22 / 4) * (1 + 1 / r) := by
    have h := norm_invZeta_right_le (d := 1 + r) (y := t) (by linarith)
    rw [show (1 + r - 1 : ℝ) = r by ring] at h
    rw [← invZeta_eq_inv hc₀ne]
    exact h
  have hP0 : 0 < Real.exp (22 / 4) * (1 + 1 / r) := by positivity
  have hlow : -Real.log ‖riemannZeta c₀‖ ≤ 22 / 4 + Real.log (1 + 1 / r) := by
    rw [norm_inv] at hinv
    have h1 := Real.log_le_log (by positivity) hinv
    have h1r' : (1 + 1 / r) ≠ 0 := by positivity
    rw [Real.log_inv, Real.log_mul (Real.exp_pos _).ne' h1r', Real.log_exp] at h1
    linarith
  have hup : Real.log ‖riemannZeta c₀‖ ≤ Real.log Λ :=
    Real.log_le_log (norm_pos_iff.mpr hζc₀) (hgrowth c₀ hc₀mem)
  have h1r : 0 < 1 / r := by positivity
  have hlog1r : 0 ≤ Real.log (1 + 1 / r) := Real.log_nonneg (by linarith)
  have hcentre : ‖g₁ c₀‖ ≤ Real.log Λ + (22 / 4 + Real.log (1 + 1 / r)) + Real.pi := by
    rw [hgc]
    refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
    rw [Complex.log_re, Complex.log_im]
    have harg := Complex.abs_arg_le_pi (riemannZeta c₀)
    have habs : |Real.log ‖riemannZeta c₀‖| ≤ Real.log Λ + (22 / 4 + Real.log (1 + 1 / r)) := by
      rw [abs_le]; constructor <;> linarith
    linarith
  -- the Borel–Carathéodory factor
  have hρ : ‖z₀ - c₀‖ ≤ 3 * r / 2 := hz₀
  have hfac : 2 * ‖z₀ - c₀‖ / (2 * r - ‖z₀ - c₀‖) ≤ 6 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hdef : 0 ≤ Real.log Λ + 1 - (g₁ c₀).re := by linarith
  have hdef' : Real.log Λ + 1 - (g₁ c₀).re ≤ Real.log Λ + 1 + (22 / 4 + Real.log (1 + 1 / r)) := by
    rw [hre c₀ hc₀mem]; linarith
  have hbc6 : ‖g₁ z₀ - g₁ c₀‖ ≤ 6 * (Real.log Λ + 1 + (22 / 4 + Real.log (1 + 1 / r))) := by
    refine le_trans hbc ?_
    calc 2 * ‖z₀ - c₀‖ / (2 * r - ‖z₀ - c₀‖) * (Real.log Λ + 1 - (g₁ c₀).re)
        ≤ 6 * (Real.log Λ + 1 - (g₁ c₀).re) := mul_le_mul_of_nonneg_right hfac hdef
      _ ≤ _ := mul_le_mul_of_nonneg_left hdef' (by norm_num)
  have hgz : ‖g₁ z₀‖
      ≤ 7 * Real.log Λ + 7 * Real.log (1 + 1 / r) + (6 + 7 * (22 / 4) + Real.pi) := by
    have := norm_sub_norm_le (g₁ z₀) (g₁ c₀)
    linarith
  -- exponentiate
  have hinvz : ‖(riemannZeta z₀)⁻¹‖ = Real.exp (-(g₁ z₀).re) := by
    rw [← hexp₁ z₀ hz₀mem, ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
  have hre_le : -(g₁ z₀).re ≤ ‖g₁ z₀‖ := by
    have := Complex.abs_re_le_norm (g₁ z₀)
    linarith [neg_abs_le (g₁ z₀).re]
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  rw [hinvz]
  calc Real.exp (-(g₁ z₀).re)
      ≤ Real.exp (7 * Real.log Λ + 7 * Real.log (1 + 1 / r) + 49) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp 49 * Λ ^ 7 * (1 + 1 / r) ^ 7 := by
        rw [Real.exp_add, Real.exp_add]
        have h1 : Real.exp (7 * Real.log Λ) = Λ ^ 7 := by
          rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hΛ0]
        have h2 : Real.exp (7 * Real.log (1 + 1 / r)) = (1 + 1 / r) ^ 7 := by
          rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul,
            Real.exp_log (by positivity)]
        rw [h1, h2]; ring


/-- **`1/ζ` on the Vinogradov–Korobov strip.**  For `t ≥ T₀` and `σ ≥ 1 - w(t+1)/4`,
`‖1/ζ(σ+it)‖ ≤ e^{49}(C log(t+1))^7(1 + 2/w(t+1))^7`. -/
theorem exists_norm_inv_riemannZeta_le_vk :
    ∃ T₀ : ℝ, Real.exp (Real.exp 30) + 1 ≤ T₀ ∧ ∀ σ t : ℝ, T₀ ≤ t →
      1 - RHTower.vkHadamardWidth (t + 1) / 4 ≤ σ →
      ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤
        Real.exp 49 * (vinogradovKorobovGrowthConstant * Real.log (t + 1)) ^ 7
          * (1 + 2 / RHTower.vkHadamardWidth (t + 1)) ^ 7 := by
  obtain ⟨T₁, hT₁e, hreg⟩ := exists_vk_zero_free_region_abs
  refine ⟨max (T₁ + 1) (Real.exp (Real.exp 30) + 1), le_max_right _ _, ?_⟩
  intro σ t ht hσ
  have hT₁t : T₁ + 1 ≤ t := le_trans (le_max_left _ _) ht
  have hEt : Real.exp (Real.exp 30) + 1 ≤ t := le_trans (le_max_right _ _) ht
  have he1 : Real.exp (Real.exp 1) ≤ Real.exp (Real.exp 30) :=
    Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by norm_num))
  have hE0 := Real.exp_pos (Real.exp 30)
  set w := RHTower.vkHadamardWidth (t + 1) with hw
  have hw0 : 0 < w := RHTower.vkHadamardWidth_pos (by linarith)
  have hwle : w ≤ 1 / 10 ^ 8 := vkHadamardWidth_le_inv (by linarith)
  set r := w / 2 with hr
  have hr0 : 0 < r := by positivity
  have h1r : 1 / r = 2 / w := by rw [hr]; field_simp
  have hL1 : 1 ≤ Real.log (t + 1) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h1 : Real.exp 1 ≤ Real.exp (Real.exp 30) :=
      Real.exp_le_exp.mpr (le_trans (by norm_num) (Real.add_one_le_exp 30))
    linarith
  have hC1 : 1 ≤ vinogradovKorobovGrowthConstant * Real.log (t + 1) := by
    have := vinogradovKorobovGrowthConstant_ge
    nlinarith
  rcases le_or_gt (1 + 5 * r / 2) σ with hbig | hsmall
  · have hne : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      have h' := congrArg Complex.re h
      simp at h'
      linarith
    rw [← invZeta_eq_inv hne]
    refine le_trans (norm_invZeta_right_le (d := σ) (y := t) (by linarith)) ?_
    have hσ1 : 1 / (σ - 1) ≤ 2 / w := by
      rw [div_le_div_iff₀ (by linarith) hw0]; linarith
    have h2w : 0 < 2 / w := by positivity
    have hY : 1 + 2 / w ≤ (1 + 2 / w) ^ 7 := le_self_pow₀ (by linarith) (by norm_num)
    have hX : 1 ≤ (vinogradovKorobovGrowthConstant * Real.log (t + 1)) ^ 7 := one_le_pow₀ hC1
    have he : Real.exp (22 / 4) ≤ Real.exp 49 := Real.exp_le_exp.mpr (by norm_num)
    have hY0 : 0 ≤ (1 + 2 / w) ^ 7 := by positivity
    have hσpos : 0 < 1 / (σ - 1) := one_div_pos.mpr (by linarith)
    calc Real.exp (22 / 4) * (1 + 1 / (σ - 1)) ≤ Real.exp 49 * (1 + 2 / w) :=
          mul_le_mul he (by linarith) (by linarith) (by positivity)
      _ ≤ Real.exp 49 * ((1 + 2 / w) ^ 7) := mul_le_mul_of_nonneg_left hY (by positivity)
      _ = Real.exp 49 * 1 * (1 + 2 / w) ^ 7 := by ring
      _ ≤ Real.exp 49 * (vinogradovKorobovGrowthConstant * Real.log (t + 1)) ^ 7
            * (1 + 2 / w) ^ 7 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX (by positivity)) hY0
  · have hcentre : ∀ z ∈ ball (((1 + r : ℝ) : ℂ) + (t : ℂ) * I) (2 * r),
        |z.re - (1 + r)| < 2 * r ∧ |z.im - t| < 2 * r := by
      intro z hz
      rw [mem_ball, dist_eq_norm] at hz
      have h1 := Complex.abs_re_le_norm (z - (((1 + r : ℝ) : ℂ) + (t : ℂ) * I))
      have h2 := Complex.abs_im_le_norm (z - (((1 + r : ℝ) : ℂ) + (t : ℂ) * I))
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im,
        Complex.mul_im, mul_zero, mul_one, sub_zero, add_zero, zero_add] at h1 h2
      exact ⟨by linarith, by linarith⟩
    have hr1 : r ≤ 1 / 4 := by rw [hr]; linarith
    have himbd : ∀ z ∈ ball (((1 + r : ℝ) : ℂ) + (t : ℂ) * I) (2 * r),
        Real.exp (Real.exp 30) ≤ z.im ∧ z.im ≤ t + 1 ∧ 1 - r < z.re ∧ z.re ≤ 2 ∧ t - 1 ≤ z.im := by
      intro z hz
      obtain ⟨h1, h2⟩ := hcentre z hz
      rw [abs_lt] at h1 h2
      exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
    refine (norm_inv_riemannZeta_le_of_disc (t := t) (r := r) hr0 ?_ ?_ hC1 ?_).trans
      (le_of_eq (by rw [h1r]))
    · intro z hz
      obtain ⟨him1, him2, hre1, -, him3⟩ := himbd z hz
      have him0 : 0 < z.im := by linarith
      refine ⟨fun h => by rw [h] at him0; simp at him0, ?_⟩
      rcases le_or_gt 1 z.re with hre | hre
      · exact riemannZeta_ne_zero_of_one_le_re hre
      · have habs : |z.im| = z.im := abs_of_pos him0
        have hv : w ≤ RHTower.vkHadamardWidth |z.im| := by
          rw [habs, hw]; exact RHTower.vkHadamardWidth_anti (by linarith) him2
        have hsplit : z = ((z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I := (Complex.re_add_im z).symm
        rw [hsplit]
        exact hreg z.re z.im (by rw [habs]; linarith) hre.le (by rw [hr] at hre1; linarith)
    · intro z hz
      obtain ⟨him1, him2, hre1, hre2, -⟩ := himbd z hz
      have him0 : 0 < z.im := by linarith
      have hlogim : Real.exp 30 ≤ Real.log z.im := by
        rw [← Real.log_exp (Real.exp 30)]; exact Real.log_le_log (Real.exp_pos _) him1
      have hθ1 : vinogradovKorobovWidth (Real.log (t + 1))
          ≤ vinogradovKorobovWidth (Real.log z.im) :=
        vinogradovKorobovWidth_anti hlogim (Real.log_le_log him0 him2)
      have hθ2 : w ≤ vinogradovKorobovWidth (Real.log (t + 1)) :=
        vkHadamardWidth_le_growthWidth (by linarith)
      have hg := norm_riemannZeta_le_vinogradovKorobov (τ := z.im) (σ := z.re) him1
        (by rw [hr] at hre1; linarith) hre2
      have hz : riemannZeta z = riemannZeta (((z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I) := by
        rw [Complex.re_add_im]
      rw [hz]
      refine le_trans hg ?_
      exact mul_le_mul_of_nonneg_left (Real.log_le_log him0 him2)
        (by linarith [vinogradovKorobovGrowthConstant_ge])
    · have heq : ((σ : ℂ) + (t : ℂ) * I) - (((1 + r : ℝ) : ℂ) + (t : ℂ) * I)
          = (((σ - (1 + r)) : ℝ) : ℂ) := by push_cast; ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith


/-- **`1/ζ` on Vinogradov–Korobov rectangles, uniformly in the height.**  On `|Im s| ≤ K`,
`1 - min(δ, w(K+1))/4 ≤ Re s ≤ 2`: `ζ` has no zeros and
`‖1/ζ(s)‖ ≤ C (log(K+1))^7 (1 + 2/w(K+1))^7`. -/
theorem exists_bound_invZeta_vk_uniform :
    ∃ C δ K₀ : ℝ, 0 < C ∧ 0 < δ ∧ 3 ≤ K₀ ∧ Real.exp (Real.exp 30) ≤ K₀ ∧
      (∀ (s : ℂ) (K : ℝ), K₀ ≤ K → |s.im| ≤ K →
          1 - min δ (RHTower.vkHadamardWidth (K + 1)) / 4 ≤ s.re → s ≠ 1 →
          riemannZeta s ≠ 0) ∧
      (∀ (s : ℂ) (K : ℝ), K₀ ≤ K → |s.im| ≤ K →
          1 - min δ (RHTower.vkHadamardWidth (K + 1)) / 4 ≤ s.re → s.re ≤ 2 →
          ‖invZeta s‖ ≤ C * Real.log (K + 1) ^ 7
            * (1 + 2 / RHTower.vkHadamardWidth (K + 1)) ^ 7) := by
  obtain ⟨T₀, hT₀, hbd⟩ := exists_norm_inv_riemannZeta_le_vk
  obtain ⟨T₁, hT₁e, hreg⟩ := exists_vk_zero_free_region_abs
  set Θ := max T₀ T₁ with hΘ
  have hΘ0 : T₀ ≤ Θ := le_max_left _ _
  have hΘ1 : T₁ ≤ Θ := le_max_right _ _
  have hE0 := Real.exp_pos (Real.exp 30)
  have he1 : Real.exp (Real.exp 1) ≤ Real.exp (Real.exp 30) :=
    Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by norm_num))
  obtain ⟨δ₁, hδ₁, M₀, hM₀, hbox⟩ := exists_bound_invZeta_box 2 Θ (by norm_num) (by linarith)
  obtain ⟨δ₂, hδ₂, hzfbox⟩ := exists_zero_free_box Θ
  set Cg := vinogradovKorobovGrowthConstant with hCg
  have hCg : 11 ≤ Cg := vinogradovKorobovGrowthConstant_ge
  refine ⟨Real.exp 49 * Cg ^ 7 + M₀ + 1, min δ₁ δ₂, Θ + 3, by positivity, lt_min hδ₁ hδ₂,
    by linarith, by linarith, ?_, ?_⟩
  · intro s K hK him hre hs1
    have hwK : 0 < RHTower.vkHadamardWidth (K + 1) := RHTower.vkHadamardWidth_pos (by linarith)
    have hmin4 : min (min δ₁ δ₂) (RHTower.vkHadamardWidth (K + 1)) / 4
        < RHTower.vkHadamardWidth (K + 1) := by
      have := min_le_right (min δ₁ δ₂) (RHTower.vkHadamardWidth (K + 1)); linarith
    rcases le_or_gt 1 s.re with hre1 | hre1
    · exact riemannZeta_ne_zero_of_one_le_re hre1
    rcases le_or_gt Θ |s.im| with hbig | hsmall
    · have hv : RHTower.vkHadamardWidth (K + 1) ≤ RHTower.vkHadamardWidth |s.im| :=
        RHTower.vkHadamardWidth_anti (by linarith) (by linarith)
      have hsplit : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I := (Complex.re_add_im s).symm
      rw [hsplit]
      exact hreg s.re s.im (by linarith) hre1.le (by linarith)
    · have hδ : min (min δ₁ δ₂) (RHTower.vkHadamardWidth (K + 1)) / 4 ≤ δ₂ := by
        have h1 := min_le_left (min δ₁ δ₂) (RHTower.vkHadamardWidth (K + 1))
        have h2 := min_le_right δ₁ δ₂
        have h3 : 0 ≤ min δ₁ δ₂ := (lt_min hδ₁ hδ₂).le
        linarith
      exact hzfbox s (by linarith) hre1.le hsmall.le hs1
  · intro s K hK him hre hre2
    have hwK : 0 < RHTower.vkHadamardWidth (K + 1) := RHTower.vkHadamardWidth_pos (by linarith)
    have hlogK : 1 ≤ Real.log (K + 1) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have hX1 : 1 ≤ Real.log (K + 1) ^ 7 := one_le_pow₀ hlogK
    have h2w : 0 < 2 / RHTower.vkHadamardWidth (K + 1) := by positivity
    have hY1 : 1 ≤ (1 + 2 / RHTower.vkHadamardWidth (K + 1)) ^ 7 := one_le_pow₀ (by linarith)
    have hXY : 1 ≤ Real.log (K + 1) ^ 7 * (1 + 2 / RHTower.vkHadamardWidth (K + 1)) ^ 7 := by
      nlinarith
    rcases le_or_gt Θ |s.im| with hbig | hsmall
    · set t := |s.im| with ht
      have ht0 : T₀ ≤ t := le_trans hΘ0 hbig
      have hs1 : s ≠ 1 := by
        intro h
        have h0 : t = 0 := by rw [ht, h]; simp
        linarith
      have hconj : ‖invZeta s‖ = ‖(riemannZeta (((s.re : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I))⁻¹‖ := by
        rw [invZeta_eq_inv hs1]
        rcases le_or_gt 0 s.im with hpos | hneg
        · rw [ht, abs_of_nonneg hpos, Complex.re_add_im]
        · have hc : ((s.re : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I = (starRingEnd ℂ) s := by
            rw [ht, abs_of_neg hneg]; apply Complex.ext <;> simp
          rw [hc, riemannZeta_conj, ← map_inv₀, Complex.norm_conj]
      have hv : RHTower.vkHadamardWidth (K + 1) ≤ RHTower.vkHadamardWidth (t + 1) :=
        RHTower.vkHadamardWidth_anti (by linarith) (by linarith)
      have hσ : 1 - RHTower.vkHadamardWidth (t + 1) / 4 ≤ s.re := by
        have := min_le_right (min δ₁ δ₂) (RHTower.vkHadamardWidth (K + 1)); linarith
      rw [hconj]
      refine le_trans (hbd s.re t ht0 hσ) ?_
      have hlog : Real.log (t + 1) ≤ Real.log (K + 1) :=
        Real.log_le_log (by linarith) (by linarith)
      have hlog0 : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith)
      have hwt : 0 < RHTower.vkHadamardWidth (t + 1) := by linarith
      have hinvw : 2 / RHTower.vkHadamardWidth (t + 1) ≤ 2 / RHTower.vkHadamardWidth (K + 1) :=
        div_le_div_of_nonneg_left (by norm_num) hwK hv
      have h1 : (Cg * Real.log (t + 1)) ^ 7 ≤ Cg ^ 7 * Real.log (K + 1) ^ 7 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog 7) (by positivity)
      have h2 : (1 + 2 / RHTower.vkHadamardWidth (t + 1)) ^ 7
          ≤ (1 + 2 / RHTower.vkHadamardWidth (K + 1)) ^ 7 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 7
      have hM : 0 ≤ M₀ + 1 := by linarith
      calc Real.exp 49 * (Cg * Real.log (t + 1)) ^ 7 * (1 + 2 / RHTower.vkHadamardWidth (t + 1)) ^ 7
          ≤ Real.exp 49 * (Cg ^ 7 * Real.log (K + 1) ^ 7)
              * (1 + 2 / RHTower.vkHadamardWidth (K + 1)) ^ 7 :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (by positivity)
              (by positivity)
        _ = Real.exp 49 * Cg ^ 7 * (Real.log (K + 1) ^ 7
              * (1 + 2 / RHTower.vkHadamardWidth (K + 1)) ^ 7) := by ring
        _ ≤ (Real.exp 49 * Cg ^ 7 + M₀ + 1) * (Real.log (K + 1) ^ 7
              * (1 + 2 / RHTower.vkHadamardWidth (K + 1)) ^ 7) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring
    · have hδ : min (min δ₁ δ₂) (RHTower.vkHadamardWidth (K + 1)) / 4 ≤ δ₁ := by
        have h1 := min_le_left (min δ₁ δ₂) (RHTower.vkHadamardWidth (K + 1))
        have h2 := min_le_left δ₁ δ₂
        have h3 : 0 ≤ min δ₁ δ₂ := (lt_min hδ₁ hδ₂).le
        linarith
      refine le_trans (hbox s (by linarith) hre2 hsmall.le) ?_
      have hE : 0 ≤ Real.exp 49 * Cg ^ 7 := by positivity
      calc M₀ ≤ (Real.exp 49 * Cg ^ 7 + M₀ + 1) * 1 := by linarith
        _ ≤ (Real.exp 49 * Cg ^ 7 + M₀ + 1) * (Real.log (K + 1) ^ 7
              * (1 + 2 / RHTower.vkHadamardWidth (K + 1)) ^ 7) :=
            mul_le_mul_of_nonneg_left hXY (by linarith)
        _ = _ := by ring

end

end RHTower.Sieve

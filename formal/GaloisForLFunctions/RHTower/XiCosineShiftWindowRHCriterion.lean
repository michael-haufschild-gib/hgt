import GaloisForLFunctions.RHTower.XiCosineShiftExceptionalPointWindow

/-!
# RH in a window, read off the PTR producer

Fix shadow-free heights `T₁ < T₂`. A zero of `ξ` with ordinate outside `[T₁, T₂]` has its
shadow `[γ − |β − ½|, γ + |β − ½|]` outside `[T₁, T₂]` too, because the shadow cannot contain
`T₁` or `T₂`. Defects and exceptional points of `cos(hD)Ξ` live in shadows. So the window sees
exactly the zeros with ordinate in it.

**Theorem** (`windowRH_iff_no_exceptionalPoint`, `windowRH_iff_no_defect`). The following are
equivalent:
* `Ξ` has no non-real zero with real part in `[T₁, T₂]`, i.e. `ξ` has no zero off the critical line
  with ordinate there;
* for every `0 < h < ½`, every real zero of `cos(hD)Ξ` in `[T₁, T₂]` is simple;
* for every `h > 0`, `cos(hD)Ξ` has no non-real zero with real part in `[T₁, T₂]`.

This is RH window by window. Shadow-free heights have density at least `86.6%`
(`volume_shadowBad_le` with Selberg's moment bound), so these windows cover every height.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- A zero of `Ξ` with real part outside a shadow-free window has its shadow outside the window. -/
theorem sq_im_lt_of_shadowFree_outside {T₁ T₂ x : ℝ}
    (hg₁ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₁ - v.re) ^ 2)
    (hg₂ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₂ - v.re) ^ 2)
    (hx : x ∈ Icc T₁ T₂) {w : ℂ} (hw : XiC w = 0) (hwout : w.re ∉ Icc T₁ T₂) :
    w.im ^ 2 < (x - w.re) ^ 2 := by
  have hside : w.re < T₁ ∨ T₂ < w.re := by
    by_contra h; push Not at h; exact hwout ⟨h.1, h.2⟩
  rcases hside with hlt | hgt
  · have h1 := hg₁ w hw
    have h2 : (T₁ - w.re) ^ 2 ≤ (x - w.re) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith [hx.1]) 2
    linarith
  · have h1 := hg₂ w hw
    have h2 : (T₂ - w.re) ^ 2 ≤ (x - w.re) ^ 2 := by
      have := pow_le_pow_left₀ (by linarith : 0 ≤ w.re - T₂) (by linarith [hx.2] :
        w.re - T₂ ≤ w.re - x) 2
      nlinarith
    linarith

/-- **RH in a window ⇔ no exceptional point in the window.** -/
theorem windowRH_iff_no_exceptionalPoint {T₁ T₂ : ℝ}
    (hg₁ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₁ - v.re) ^ 2)
    (hg₂ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₂ - v.re) ^ 2) :
    (∀ w, XiC w = 0 → w.re ∈ Icc T₁ T₂ → w.im = 0) ↔
      ∀ h : ℝ, 0 < h → h < 1 / 2 → ∀ x ∈ Icc T₁ T₂, cosProducer h x = 0 →
        deriv (cosProducer h) x ≠ 0 := by
  constructor
  · intro hRH h hh _ x hx h0
    refine deriv_cosineShiftXi_ne_zero_of_local hh (fun w hw => ?_) h0
    by_cases hwin : w.re ∈ Icc T₁ T₂
    · rw [hRH w hw hwin]; nlinarith [sq_nonneg (x - w.re), sq_pos_of_pos hh]
    · have := sq_im_lt_of_shadowFree_outside hg₁ hg₂ hx hw hwin
      nlinarith [sq_nonneg h]
  · intro hno w hw hwin
    by_contra hwim
    have hne₁ : w.re ≠ T₁ := by
      intro h; have := hg₁ w hw; rw [h, sub_self] at this; nlinarith [sq_nonneg w.im]
    have hne₂ : w.re ≠ T₂ := by
      intro h; have := hg₂ w hw; rw [h, sub_self] at this; nlinarith [sq_nonneg w.im]
    obtain ⟨h, hh, hh2, x, hx, h0, hd⟩ := exists_exceptionalPoint_of_shadowFree_window hg₁ hg₂ hw
      hwim ⟨lt_of_le_of_ne hwin.1 (Ne.symm hne₁), lt_of_le_of_ne hwin.2 hne₂⟩
    exact hno h hh hh2 x (Ioo_subset_Icc_self hx) h0 hd

/-- **RH in a window ⇔ no defect in the window at any depth.** -/
theorem windowRH_iff_no_defect {T₁ T₂ : ℝ}
    (hg₁ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₁ - v.re) ^ 2)
    (hg₂ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₂ - v.re) ^ 2) :
    (∀ w, XiC w = 0 → w.re ∈ Icc T₁ T₂ → w.im = 0) ↔
      ∀ h : ℝ, 0 < h → ∀ z : ℂ, z.re ∈ Icc T₁ T₂ → cosProducer h z = 0 → z.im = 0 := by
  constructor
  · intro hRH h hh z hz h0
    by_contra hzim
    obtain ⟨w, hw, hdisk⟩ := DeBruijn.cosineShift_nonreal_zero_mem_defectDisk hh hzim h0
    have hzsq : 0 < z.im ^ 2 := by positivity
    have hshadow : (z.re - w.re) ^ 2 < w.im ^ 2 := by nlinarith [sq_nonneg (w.re - z.re)]
    by_cases hwin : w.re ∈ Icc T₁ T₂
    · rw [hRH w hw hwin] at hshadow; nlinarith [sq_nonneg (z.re - w.re)]
    · have := sq_im_lt_of_shadowFree_outside hg₁ hg₂ hz hw hwin
      linarith
  · intro hno w hw hwin
    by_contra hwim
    have hconv0 : TendstoLocallyUniformly (fun (n : ℕ) => cosProducer (1 / ((n : ℝ) + 1))) XiC
        atTop := tendstoLocallyUniformly_cosineShift_XiC
    have hne₁ : w.re ≠ T₁ := by
      intro h; have := hg₁ w hw; rw [h, sub_self] at this; nlinarith [sq_nonneg w.im]
    have hne₂ : w.re ≠ T₂ := by
      intro h; have := hg₂ w hw; rw [h, sub_self] at this; nlinarith [sq_nonneg w.im]
    have hin₁ : T₁ < w.re := lt_of_le_of_ne hwin.1 (Ne.symm hne₁)
    have hin₂ : w.re < T₂ := lt_of_le_of_ne hwin.2 hne₂
    set r : ℝ := min (|w.im| / 2) (min (w.re - T₁) (T₂ - w.re)) with hrdef
    have hr : 0 < r := lt_min (by have := abs_pos.mpr hwim; positivity)
      (lt_min (by linarith) (by linarith))
    obtain ⟨n, z, hzb, hz0⟩ := (eventually_exists_zero_mem_ball
      (fun n => differentiable_cosProducer _) differentiable_XiC analyticOrderAt_XiC_ne_top hconv0
      hw hr).exists
    have hzd := mem_ball.mp hzb
    have himz : |z.im - w.im| ≤ dist z w := by
      rw [dist_eq_norm]; have := Complex.abs_im_le_norm (z - w); simpa using this
    have hrez : |z.re - w.re| ≤ dist z w := by
      rw [dist_eq_norm]; have := Complex.abs_re_le_norm (z - w); simpa using this
    have h1 := min_le_left (|w.im| / 2) (min (w.re - T₁) (T₂ - w.re))
    have h2 := min_le_right (|w.im| / 2) (min (w.re - T₁) (T₂ - w.re))
    have h3 := min_le_left (w.re - T₁) (T₂ - w.re)
    have h4 := min_le_right (w.re - T₁) (T₂ - w.re)
    have hzim : z.im ≠ 0 := by
      intro h0; rw [h0, zero_sub, abs_neg] at himz; linarith
    have hzre : z.re ∈ Icc T₁ T₂ := by
      constructor <;> linarith [(abs_le.mp hrez).1, (abs_le.mp hrez).2]
    exact hzim (hno _ (by positivity) z hzre hz0)

end

end RHTower

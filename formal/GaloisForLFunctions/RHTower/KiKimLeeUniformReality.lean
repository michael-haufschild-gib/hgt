import GaloisForLFunctions.RHTower.KiKimLeeLargeHeightReality

/-!
# Ki–Kim–Lee large-height reality, uniformly in the heat time

For `0 < t₀ ≤ t ≤ 1/8` the relative error `kklError t α` of the Ki–Kim–Lee comparison is bounded
by a function `kklErrorUniform t₀ α` of `t₀` alone (`kklError_le_uniform`), which tends to `0` as
`α → ∞`. Hence one height `X₀` works for the whole time interval: every zero of `H_t` with
`|Re z| ≥ X₀` is real, for every `t ∈ [t₀, 1/8]` (`exists_riemannHeat_zeros_real_uniform`).
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- A bound for `kklError t α` valid for all `t ∈ [t₀, 1/8]`. -/
def kklErrorUniform (t₀ α : ℝ) : ℝ :=
  Real.exp (5 / 2 * α - 3 / 4 * t₀ * α ^ 2) + Real.exp (-α ^ 2 + 1 / 2 + 1 / 8) +
    2 * (9 / 2 * (5 / (2 * t₀) + α + 1) * (4 * Real.pi * t₀) ^ (-(1 / 2 : ℝ)) * 200 *
      (6 + 2 * Real.pi * Real.exp (2 * α)) *
      Real.exp (5 * α - t₀ * α ^ 2 + (1 / 2 + α / 4) / 8)) +
    2 * (2 * Real.exp 1 * 2 * (1 / (2 * t₀) + α + 1) *
      Real.exp (-(15 / 8) * α ^ 2 + α ^ 2 / 8 + 15 / 16 + α + 18 / 8)) +
    (4 * Real.pi * t₀) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(2 * (α ^ 2 - 1 / 2) ^ 2) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + α ^ 2 / 8)

theorem rpow_neg_half_le {t₀ t : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) ≤ (4 * Real.pi * t₀) ^ (-(1 / 2 : ℝ)) :=
  Real.rpow_le_rpow_of_nonpos (by positivity) (by gcongr) (by norm_num)

theorem kklError_le_uniform {t₀ t α : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (ht8 : t ≤ 1 / 8)
    (hα : 0 ≤ α) : kklError t α ≤ kklErrorUniform t₀ α := by
  have htpos : 0 < t := ht₀.trans_le ht
  have hinv : 1 / t ≤ 1 / t₀ := one_div_le_one_div_of_le ht₀ ht
  have hr := rpow_neg_half_le ht₀ ht
  have hr0 : 0 ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := by positivity
  have hα2 : 0 ≤ α ^ 2 := sq_nonneg α
  unfold kklError kklErrorUniform kklR1 kklR2 kklRA kklRC kklRB
  have h1 : Real.exp (5 / 2 * α - 3 / 4 * t * α ^ 2) ≤
      Real.exp (5 / 2 * α - 3 / 4 * t₀ * α ^ 2) := by
    gcongr
  have h2 : Real.exp (-α ^ 2 + 1 / 2 + t) ≤ Real.exp (-α ^ 2 + 1 / 2 + 1 / 8) := by
    gcongr
  have h3 : 9 / 2 * (5 / (2 * t) + α + 1) * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * 200 *
      (6 + 2 * Real.pi * Real.exp (2 * α)) *
      Real.exp (5 * α - t * α ^ 2 + (1 / 2 + 2 * t * α) / 8) ≤
      9 / 2 * (5 / (2 * t₀) + α + 1) * (4 * Real.pi * t₀) ^ (-(1 / 2 : ℝ)) * 200 *
      (6 + 2 * Real.pi * Real.exp (2 * α)) *
      Real.exp (5 * α - t₀ * α ^ 2 + (1 / 2 + α / 4) / 8) := by
    have e1 : 5 / (2 * t) ≤ 5 / (2 * t₀) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have e2 : 5 * α - t * α ^ 2 + (1 / 2 + 2 * t * α) / 8 ≤
        5 * α - t₀ * α ^ 2 + (1 / 2 + α / 4) / 8 := by nlinarith
    gcongr
  have h4 : 2 * Real.exp 1 * 2 * (1 / (2 * t) + α + 1) *
      Real.exp (-(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t) ≤
      2 * Real.exp 1 * 2 * (1 / (2 * t₀) + α + 1) *
      Real.exp (-(15 / 8) * α ^ 2 + α ^ 2 / 8 + 15 / 16 + α + 18 / 8) := by
    have e1 : 1 / (2 * t) ≤ 1 / (2 * t₀) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have e2 : -(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t ≤
        -(15 / 8) * α ^ 2 + α ^ 2 / 8 + 15 / 16 + α + 18 / 8 := by nlinarith
    gcongr
  have h5 : (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-((α ^ 2 - 1 / 2) ^ 2 / (4 * t)) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + t * α ^ 2) ≤
      (4 * Real.pi * t₀) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(2 * (α ^ 2 - 1 / 2) ^ 2) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + α ^ 2 / 8) := by
    have e1 : 2 * (α ^ 2 - 1 / 2) ^ 2 ≤ (α ^ 2 - 1 / 2) ^ 2 / (4 * t) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (α ^ 2 - 1 / 2)]
    have e2 : t * α ^ 2 ≤ α ^ 2 / 8 := by nlinarith
    gcongr
  linarith

theorem tendsto_kklErrorUniform {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto (kklErrorUniform t₀) atTop (𝓝 0) := by
  have h0 : ∀ᶠ α : ℝ in atTop, 0 ≤ α := eventually_ge_atTop 0
  have hR1 : Tendsto (fun α => Real.exp (5 / 2 * α - 3 / 4 * t₀ * α ^ 2)) atTop (𝓝 0) := by
    refine tendsto_of_le_mul_exp_quadratic 1 (c := 3 / 4 * t₀) (by positivity) (5 / 2) 0
      (Eventually.of_forall fun α => (Real.exp_pos _).le) (Eventually.of_forall fun α => ?_)
    rw [one_mul]; ring_nf; exact le_rfl
  have hR2 : Tendsto (fun α => Real.exp (-α ^ 2 + 1 / 2 + 1 / 8)) atTop (𝓝 0) := by
    refine tendsto_of_le_mul_exp_quadratic 1 (c := 1) one_pos 0 (1 / 2 + 1 / 8)
      (Eventually.of_forall fun α => (Real.exp_pos _).le) (Eventually.of_forall fun α => ?_)
    rw [one_mul]; ring_nf; exact le_rfl
  have hRA : Tendsto (fun α => 9 / 2 * (5 / (2 * t₀) + α + 1) *
      (4 * Real.pi * t₀) ^ (-(1 / 2 : ℝ)) * 200 * (6 + 2 * Real.pi * Real.exp (2 * α)) *
      Real.exp (5 * α - t₀ * α ^ 2 + (1 / 2 + α / 4) / 8)) atTop (𝓝 0) := by
    refine tendsto_of_le_mul_exp_quadratic
      (9 / 2 * (4 * Real.pi * t₀) ^ (-(1 / 2 : ℝ)) * 200 * 13)
      (c := t₀) ht₀ (8 + 1 / 32) (5 / (2 * t₀) + 1 / 16)
      (h0.mono fun α hα => by positivity) (h0.mono fun α hα => ?_)
    have hx : 5 / (2 * t₀) + α + 1 ≤ Real.exp (5 / (2 * t₀) + α) := Real.add_one_le_exp _
    have hy : 6 + 2 * Real.pi * Real.exp (2 * α) ≤ 13 * Real.exp (2 * α) := by
      have := Real.one_le_exp (by linarith : (0 : ℝ) ≤ 2 * α)
      have := Real.pi_lt_d2
      nlinarith
    have hc : 0 ≤ (4 * Real.pi * t₀) ^ (-(1 / 2 : ℝ)) := by positivity
    have hp1 : 0 ≤ 5 / (2 * t₀) + α + 1 := by positivity
    have e : Real.exp (5 / (2 * t₀) + α) * Real.exp (2 * α) *
        Real.exp (5 * α - t₀ * α ^ 2 + (1 / 2 + α / 4) / 8) =
        Real.exp (5 / (2 * t₀) + 1 / 16 + (8 + 1 / 32) * α - t₀ * α ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    calc 9 / 2 * (5 / (2 * t₀) + α + 1) * (4 * Real.pi * t₀) ^ (-(1 / 2 : ℝ)) * 200 *
          (6 + 2 * Real.pi * Real.exp (2 * α)) *
          Real.exp (5 * α - t₀ * α ^ 2 + (1 / 2 + α / 4) / 8)
        = 9 / 2 * (4 * Real.pi * t₀) ^ (-(1 / 2 : ℝ)) * 200 * ((5 / (2 * t₀) + α + 1) *
            (6 + 2 * Real.pi * Real.exp (2 * α)) *
            Real.exp (5 * α - t₀ * α ^ 2 + (1 / 2 + α / 4) / 8)) := by ring
      _ ≤ 9 / 2 * (4 * Real.pi * t₀) ^ (-(1 / 2 : ℝ)) * 200 * (Real.exp (5 / (2 * t₀) + α) *
            (13 * Real.exp (2 * α)) *
            Real.exp (5 * α - t₀ * α ^ 2 + (1 / 2 + α / 4) / 8)) := by gcongr
      _ = 9 / 2 * (4 * Real.pi * t₀) ^ (-(1 / 2 : ℝ)) * 200 * 13 *
            (Real.exp (5 / (2 * t₀) + α) * Real.exp (2 * α) *
              Real.exp (5 * α - t₀ * α ^ 2 + (1 / 2 + α / 4) / 8)) := by ring
      _ = _ := by rw [e]
  have hRC : Tendsto (fun α => 2 * Real.exp 1 * 2 * (1 / (2 * t₀) + α + 1) *
      Real.exp (-(15 / 8) * α ^ 2 + α ^ 2 / 8 + 15 / 16 + α + 18 / 8)) atTop (𝓝 0) := by
    refine tendsto_of_le_mul_exp_quadratic (2 * Real.exp 1 * 2) (c := 7 / 4) (by norm_num)
      2 (1 / (2 * t₀) + 15 / 16 + 18 / 8)
      (h0.mono fun α hα => by positivity) (h0.mono fun α hα => ?_)
    have hx : 1 / (2 * t₀) + α + 1 ≤ Real.exp (1 / (2 * t₀) + α) := Real.add_one_le_exp _
    calc 2 * Real.exp 1 * 2 * (1 / (2 * t₀) + α + 1) *
          Real.exp (-(15 / 8) * α ^ 2 + α ^ 2 / 8 + 15 / 16 + α + 18 / 8)
        ≤ 2 * Real.exp 1 * 2 * Real.exp (1 / (2 * t₀) + α) *
          Real.exp (-(15 / 8) * α ^ 2 + α ^ 2 / 8 + 15 / 16 + α + 18 / 8) := by gcongr
      _ = _ := by rw [mul_assoc (2 * Real.exp 1 * 2), ← Real.exp_add]; ring_nf
  have hRB : Tendsto (fun α => (4 * Real.pi * t₀) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(2 * (α ^ 2 - 1 / 2) ^ 2) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + α ^ 2 / 8))
      atTop (𝓝 0) := by
    refine tendsto_of_le_mul_exp_quadratic ((4 * Real.pi * t₀) ^ (-(1 / 2 : ℝ))) (c := 1)
      one_pos 0 0 (Eventually.of_forall fun α => by positivity)
      ((eventually_ge_atTop (3 : ℝ)).mono fun α hα => ?_)
    gcongr
    have ha1 : 3 * α ≤ α ^ 2 := by nlinarith
    have ha2 : 3 * α ^ 2 ≤ α ^ 3 := by nlinarith
    have ha3 : 3 * α ^ 3 ≤ α ^ 4 := by nlinarith
    have hexp : (α ^ 2 - 1 / 2) ^ 2 = α ^ 4 - α ^ 2 + 1 / 4 := by ring
    have hprod : (α ^ 2 + 1 / 2) * (α + 1 / 8) = α ^ 3 + α ^ 2 / 8 + α / 2 + 1 / 16 := by ring
    rw [hexp, hprod]
    nlinarith
  have := (((hR1.add hR2).add (hRA.const_mul 2)).add (hRC.const_mul 2)).add hRB
  rw [show (0 : ℝ) = 0 + 0 + 2 * 0 + 2 * 0 + 0 by norm_num]
  exact this

/-- `H_t(X + iy) ≠ 0` for `0 < |y| ≤ ½` once `Re(Q'Q̄) > 0` on `[−½, ½]`. -/
theorem riemannHeat_ne_zero_of_re_slope_pos {t X : ℝ} (ht : 0 < t)
    (hpos : ∀ y : ℝ, |y| ≤ 1 / 2 →
      0 < ((∫ w in Ioi (0 : ℝ), (((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) *
          xiLine X w) * starRingEnd ℂ (halfGaussTransform t (xiLine X) y)).re)
    {y : ℝ} (hy0 : y ≠ 0) (hy : |y| ≤ 1 / 2) : riemannHeat t ((X : ℂ) + I * y) ≠ 0 := by
  set Q := halfGaussTransform t (xiLine X) with hQ
  have hQd : ∀ v ∈ Icc (-(1 / 2) : ℝ) (1 / 2), HasDerivAt Q
      (∫ w in Ioi (0 : ℝ), (((w - v) / (2 * t) * gaussDensity t (w - v) : ℝ) : ℂ) * xiLine X w) v :=
    fun v _ => hasDerivAt_halfGaussTransform ht (continuous_xiLine X)
      (integrable_exp_mul_norm_xiLine ht X) v
  have hpos' : ∀ v ∈ Icc (-(1 / 2) : ℝ) (1 / 2), 0 < ((∫ w in Ioi (0 : ℝ),
      (((w - v) / (2 * t) * gaussDensity t (w - v) : ℝ) : ℂ) * xiLine X w) *
        starRingEnd ℂ (Q v)).re := fun v hv => hpos v (abs_le.mpr hv)
  rw [riemannHeat_eq_halfGaussAverage ht X y]
  apply add_conj_ne_zero_of_norm_ne
  have hy' := abs_le.mp hy
  rcases lt_or_gt_of_ne hy0 with hneg | hpos0
  · have h := norm_lt_norm_of_re_mul_conj_pos hQd hpos' (y := -y) (by linarith) (by linarith)
    rw [neg_neg] at h
    exact ne_of_gt h
  · exact ne_of_lt (norm_lt_norm_of_re_mul_conj_pos hQd hpos' hpos0 hy'.2)

/-- **Uniform large-height nonvanishing.** For `0 < t₀ ≤ 1/8`, eventually in `X`,
`H_t(X + iy) ≠ 0` for all `t ∈ [t₀, 1/8]` and `0 < |y| ≤ ½`. -/
theorem eventually_riemannHeat_ne_zero_uniform {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∀ᶠ X : ℝ in atTop, ∀ t ∈ Icc t₀ (1 / 8), ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 / 2 →
      riemannHeat t ((X : ℂ) + I * y) ≠ 0 := by
  have hα := tendsto_horizontalSlope_re
  have hδ := ((tendsto_kklErrorUniform ht₀).comp hα).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  filter_upwards [eventually_ge_atTop 200, hα.eventually_ge_atTop 5,
    hα.eventually_ge_atTop (5 / (2 * t₀)), hδ] with X hX h5 h5t hδX
  intro t ht y hy0 hy
  have htpos : 0 < t := ht₀.trans_le ht.1
  refine riemannHeat_ne_zero_of_re_slope_pos htpos (fun v hv => ?_) hy0 hy
  have hu9 : 5 ≤ 2 * t * (horizontalSlope X).re := by
    have h1 := mul_le_mul_of_nonneg_left h5t (by positivity : (0 : ℝ) ≤ 2 * t₀)
    rw [mul_div_cancel₀ _ (by positivity)] at h1
    have h2 : 2 * t₀ * (horizontalSlope X).re ≤ 2 * t * (horizontalSlope X).re := by
      have : 0 ≤ (horizontalSlope X).re := by linarith
      nlinarith [ht.1]
    linarith
  exact re_slope_mul_conj_pos htpos ht.2 hX hv (by linarith) hu9
    (window_fits ht.2 htpos (by linarith) h5)
    ((kklError_le_uniform ht₀ ht.1 ht.2 (by linarith)).trans hδX)

/-- **Uniform large-height reality.** For `0 < t₀ ≤ 1/8` there is `X₀` such that for every
`t ∈ [t₀, 1/8]` every zero of `H_t` with `|Re z| ≥ X₀` is real. -/
theorem exists_riemannHeat_zeros_real_uniform {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ X₀ : ℝ, ∀ t ∈ Icc t₀ (1 / 8), ∀ z : ℂ, riemannHeat t z = 0 → X₀ ≤ |z.re| →
      z.im = 0 := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (eventually_riemannHeat_ne_zero_uniform ht₀)
  refine ⟨max X₀ 0, fun t ht z hz hre => ?_⟩
  have htpos : 0 < t := ht₀.trans_le ht.1
  have him := riemannHeat_zeros_im_sq_le htpos hz
  have him2 : z.im ^ 2 ≤ 1 / 4 := him.trans (max_le (by linarith [ht.1]) (by norm_num))
  have him' : |z.im| ≤ 1 / 2 := by
    rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
  by_contra hne
  rcases le_or_gt 0 z.re with h0 | h0
  · rw [abs_of_nonneg h0] at hre
    apply hX₀ z.re (le_of_max_le_left hre) t ht z.im hne him'
    rw [← hz]
    congr 1
    apply Complex.ext <;> simp
  · rw [abs_of_neg h0] at hre
    apply hX₀ (-z).re (by simp; exact le_of_max_le_left hre) t ht (-z).im (by simpa using hne)
      (by simpa using him')
    rw [← hz, ← riemannHeat_neg htpos.le]
    congr 1
    apply Complex.ext <;> simp

end

end RHTower.DeBruijn

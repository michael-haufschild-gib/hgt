import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheWidthCenteredCameraSeesNearTopClusters

/-!
# Paying the Turán loss with exterior decay

At logarithmic width and positive logarithmic lag margin, the exterior
norm mass is bounded by an explicit constant divided by `log T`. Thus
any fixed Turán loss can be paid by increasing the height. Only the
ordinate gap for comparably deep exterior zeros is required.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Real
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

open SquareRootThreshold (zetaZeroWidth)

private theorem exp_neg_le_four_div_sq {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 4 / x ^ 2 := by
  have h : x / 2 ≤ Real.exp (x / 2) := by
    linarith only [Real.add_one_le_exp (x / 2)]
  have hh := mul_le_mul h h (by positivity : 0 ≤ x / 2) (Real.exp_pos _).le
  rw [← Real.exp_add, show x / 2 + x / 2 = x by ring] at hh
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos x) (sq_pos_of_pos hx)]
  nlinarith only [hh]

/-- An explicit inverse-logarithmic bound for the entire exterior, including
shallow zeros at arbitrarily small ordinate distance. -/
theorem sum_widthCenteredCamera_deep_exterior_le_inv_log
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {c a d g T y t : ℝ} (hc : 0 < c) (ha : 0 < a) (hd : 0 < d) (hg : 0 < g)
    (hT : 4 ≤ T) (hL : 1 ≤ Real.log T) (hδ : 1 ≤ c * Real.log T)
    (hy : a * Real.log T ≤ y - c * Real.log T) (ht : t ∈ Ioc T (2 * T))
    (F : Finset zetaZeroConfig.carrier)
    (hgap : ∀ ρ ∈ F, zetaZeroWidth - d ≤ (ρ : ℂ).re - 1 / 2 →
      g ≤ |(ρ : ℂ).im - t|) :
    (∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) *
      ‖paperFT (depthCenteredCamera v zetaZeroWidth (c * Real.log T) y) (gammaOf ρ - t)‖) ≤
      (8 * profileMass v * (xiLineTwoLogDerivConstant + 2) *
        ((1 + g ^ 2) / (c ^ 2 * g ^ 2) + 4 / (d * a) ^ 2)) / Real.log T := by
  have hL0 : 0 < Real.log T := one_pos.trans_le hL
  have hyδ : c * Real.log T ≤ y := by
    have h := mul_pos ha hL0
    linarith only [hy, h]
  have hnoise := sum_widthCenteredCamera_exterior_le_deep_gap hv hsupp hδ hyδ hg hd.le F hgap
  have hdecay : Real.exp (-(d * (y - c * Real.log T))) ≤
      4 / ((d * a) * Real.log T) ^ 2 := by
    apply le_trans _ (exp_neg_le_four_div_sq (mul_pos (mul_pos hd ha) hL0))
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hy hd.le
    nlinarith only [h]
  have ht0 : 0 ≤ t := by linarith only [ht.1, hT]
  have hlog : Real.log (t + 4) ≤ 2 * Real.log T := by
    calc
      _ ≤ Real.log (T ^ 2) := Real.log_le_log (by positivity)
        (by nlinarith only [ht.2, hT])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hunit : lorentzMass t ≤ 8 * (xiLineTwoLogDerivConstant + 2) * Real.log T := by
    have h := lorentzMass_le_log t
    rw [abs_of_nonneg ht0] at h
    have hC := le_mul_of_one_le_right xiLineTwoLogDerivConstant_nonneg hL
    nlinarith only [h, hlog, hC]
  have hmass0 : 0 ≤ lorentzMass t := by
    simpa only [Finset.sum_empty] using sum_mult_unit_le_lorentzMass t ∅ (by simp)
  calc
    _ ≤ profileMass v * ((1 + g ^ 2) / ((c * Real.log T) ^ 2 * g ^ 2) +
        Real.exp (-(d * (y - c * Real.log T)))) * lorentzMass t := hnoise
    _ ≤ profileMass v * ((1 + g ^ 2) / ((c * Real.log T) ^ 2 * g ^ 2) +
        4 / ((d * a) * Real.log T) ^ 2) *
        (8 * (xiLineTwoLogDerivConstant + 2) * Real.log T) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add_left hdecay _)
        (profileMass_nonneg v)) hunit hmass0
        (mul_nonneg (profileMass_nonneg v) (by positivity))
    _ = _ := by field_simp [hc.ne', ha.ne', hd.ne', hg.ne', hL0.ne'] <;> ring

/-- Every prescribed positive noise tolerance is eventually satisfied,
uniformly over the camera centres and exterior finite sets. -/
theorem eventually_sum_widthCenteredCamera_deep_exterior_le
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {c a d g ε : ℝ} (hc : 0 < c) (ha : 0 < a) (hd : 0 < d) (hg : 0 < g)
    (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ y t : ℝ,
      a * Real.log T ≤ y - c * Real.log T → t ∈ Ioc T (2 * T) →
      ∀ F : Finset zetaZeroConfig.carrier,
      (∀ ρ ∈ F, zetaZeroWidth - d ≤ (ρ : ℂ).re - 1 / 2 →
        g ≤ |(ρ : ℂ).im - t|) →
      (∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (depthCenteredCamera v zetaZeroWidth (c * Real.log T) y) (gammaOf ρ - t)‖) ≤ ε := by
  let C := 8 * profileMass v * (xiLineTwoLogDerivConstant + 2) *
    ((1 + g ^ 2) / (c ^ 2 * g ^ 2) + 4 / (d * a) ^ 2)
  filter_upwards [eventually_ge_atTop 4,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 / c),
    Real.tendsto_log_atTop.eventually_ge_atTop (C / ε)] with T hT hL hLc hLε y t hy ht F hgap
  have hδ : 1 ≤ c * Real.log T := by
    have h := (div_le_iff₀ hc).mp hLc
    simpa only [mul_comm] using h
  apply (sum_widthCenteredCamera_deep_exterior_le_inv_log hv hsupp hc ha hd hg
    hT hL hδ hy ht F hgap).trans
  change C / Real.log T ≤ ε
  rw [div_le_iff₀ (one_pos.trans_le hL)]
  exact (div_le_iff₀ hε).mp hLε |>.trans_eq (mul_comm _ _)

/-- A bounded near-top sector cluster is eventually visible without an
exterior-mass premise. The fixed gap for comparably deep exterior zeros
pays the full Turán constant, however small that constant is. -/
theorem eventually_exists_nu_widthCenteredZeroField_ge
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u)
    {M N : ℕ} (hN : 1 ≤ N) {c A d g E : ℝ}
    (hc : 0 < c) (hA : 0 < A) (hd : 0 < d) (hg : 0 < g) (hE : 0 ≤ E)
    (hlag : c < ((M : ℝ) + 1) * A) :
    ∀ᶠ T : ℝ in atTop, ∀ t : ℝ, t ∈ Ioc T (2 * T) →
      ∀ s : Finset zetaZeroConfig.carrier, s.card ≤ N →
      (∀ ρ ∈ s, |(ρ : ℂ).im - t| * (c * Real.log T) ≤ 1 / 10) →
      (∀ q : zetaZeroConfig.carrier, q ∉ s →
        zetaZeroWidth - d ≤ (q : ℂ).re - 1 / 2 → g ≤ |(q : ℂ).im - t|) →
      ∀ ρ ∈ s, zetaZeroWidth - E / Real.log T ≤ (ρ : ℂ).re - 1 / 2 →
      ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + N ∧
        1 / 4 * (∫ u, v u) * turanConstant N M *
          Real.exp (-(E * (((M : ℝ) + N) * A + c))) ≤
        ‖widthCenteredZeroField v (c * Real.log T) ((ν : ℝ) * (A * Real.log T)) t‖ := by
  let a := ((M : ℝ) + 1) * A - c
  have ha : 0 < a := sub_pos.mpr hlag
  let B := 1 / 4 * (∫ u, v u) * turanConstant N M *
    Real.exp (-(E * (((M : ℝ) + N) * A + c)))
  have hB : 0 < B := by
    have hκ := turanConstant_pos hN M
    dsimp only [B]
    positivity
  have hsmall := eventually_sum_widthCenteredCamera_deep_exterior_le hv hsupp hc ha hd hg hB
  filter_upwards [hsmall, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 / c)]
    with T htail hL hLc t ht s hcard hsec hgap ρ hρ hnear
  have hL0 : 0 < Real.log T := one_pos.trans_le hL
  have hδ : 1 ≤ c * Real.log T := by
    have h := (div_le_iff₀ hc).mp hLc
    simpa only [mul_comm] using h
  have hh : 0 < A * Real.log T := mul_pos hA hL0
  obtain ⟨ν, hν1, hνN, hsignal⟩ := exists_nu_widthCentered_cluster_signal hv hsupp hv0 hI
    (one_pos.trans_le hδ) hh (div_nonneg hE hL0.le) hN hcard hsec hρ hnear
  have hexp : -(E / Real.log T *
      (((M : ℝ) + N) * (A * Real.log T) + c * Real.log T)) =
      -(E * (((M : ℝ) + N) * A + c)) := by
    field_simp [hL0.ne'] <;> ring
  rw [hexp] at hsignal
  have hmargin : a * Real.log T ≤ (ν : ℝ) * (A * Real.log T) - c * Real.log T := by
    have hn : (M : ℝ) + 1 ≤ (ν : ℝ) := by exact_mod_cast hν1
    have h := mul_le_mul_of_nonneg_right hn hh.le
    dsimp only [a]
    nlinarith only [h]
  have hy : c * Real.log T ≤ (ν : ℝ) * (A * Real.log T) := by
    have h := mul_pos ha hL0
    linarith only [hmargin, h]
  have hs := summable_widthCenteredCamera hv hsupp hδ hy (t := t)
  have herr := norm_tsum_sub_sum_le hs s (c := B) (fun F hF => by
    have h := htail ((ν : ℝ) * (A * Real.log T)) t hmargin ht F
      (fun q hq hdeep => hgap q (fun hqs => Finset.disjoint_left.mp hF hq hqs) hdeep)
    simpa only [norm_mul, Complex.norm_natCast] using h)
  have htri := norm_sub_norm_le
    (∑ q ∈ s, (zetaZeroConfig.mult q : ℂ) *
      paperFT (depthCenteredCamera v zetaZeroWidth (c * Real.log T)
        ((ν : ℝ) * (A * Real.log T))) (gammaOf q - t))
    (widthCenteredZeroField v (c * Real.log T) ((ν : ℝ) * (A * Real.log T)) t)
  rw [norm_sub_rev] at htri
  change ‖widthCenteredZeroField v (c * Real.log T) ((ν : ℝ) * (A * Real.log T)) t - _‖ ≤ B at herr
  refine ⟨ν, hν1, hνN, ?_⟩
  dsimp only [B] at herr
  linarith only [hsignal, herr, htri]

end GaloisForLFunctions.MultiscaleMollifiedZetaField

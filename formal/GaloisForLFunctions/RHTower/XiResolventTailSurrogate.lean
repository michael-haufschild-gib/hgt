import GaloisForLFunctions.RHTower.XiResolventMassBudget

/-!
# The zero-density surrogate: certified tail decay from ray jets

The budget identity `Σ' massAt(c) = 2·Re(logDeriv ξ(1/2 + c))` holds at every probe point
`c ≥ 1/2`, and a probe at large `c` weights high zeros more heavily: on the tail `γ² ≥ T` the
resolvent norm is dominated by `(T + (c+1/2)²)/(2c(T − 1/4))` times the budget mass at `c`.
Consequently

  `Σ'_{γ² ≥ T} ‖u_q(X)‖ ≤ (T + (c+1/2)²)/(2c(T − 1/4)) · 2·Re(logDeriv ξ(1/2 + c))`,

uniformly in the shift `X ≥ 0`.  Choosing `c ≍ √T` makes the prefactor `≍ 1/√T` while the ray
jet grows only logarithmically — certified tail decay at the true zero-density rate, with the
counting function replaced by a single logarithmic-derivative value of `ξ` on the real ray.

Since `‖u_q(X)‖ < δ` forces `γ² > 1/δ − X − 1/4`, the sub-`δ` tail of the two-scale supply
obeys the same bound: the tail-mass input of the supply theorems is dischargeable by ray-jet
data, and the first rational-nodal data rest on line placement and ξ-jets alone.
-/

open Complex

namespace RHTower

noncomputable section

/-- The resolvent norm against the floor-shifted squared height. -/
theorem norm_xiResolventPoint_le_inv_floor {X : ℝ} (hX : 0 ≤ X) (q : XiZeroCopy) :
    ‖xiResolventPoint X q‖ ≤ 1 / ((xiSpectralPoint q).re ^ 2 - 1 / 4) := by
  have hg := xiSpectral_re_sq_gt_thirtytwo q
  have hs := xiSpectralPoint_im_sq_lt_quarter q
  have hApos : (0 : ℝ) < (xiSpectralPoint q).re ^ 2 - 1 / 4 := by linarith
  have h1 : ‖xiResolventPoint X q‖ = ‖xiSpectralPoint q ^ 2 + (X : ℂ)‖⁻¹ := by
    rw [xiResolventPoint, norm_inv]
  have hre_le : (xiSpectralPoint q).re ^ 2 - 1 / 4 ≤
      ‖xiSpectralPoint q ^ 2 + (X : ℂ)‖ := by
    have hle := Complex.re_le_norm (xiSpectralPoint q ^ 2 + (X : ℂ))
    have heq := xiSpectralSq_add_ofReal_re_eq X q
    linarith
  rw [h1, inv_eq_one_div]
  exact one_div_le_one_div_of_le hApos hre_le

/-- The resolvent norm is at least the reciprocal of the strip-shifted squared height, so
small resolvent norms force large heights. -/
theorem lt_re_sq_of_norm_xiResolventPoint_lt {X δ : ℝ} (hX : 0 ≤ X) (hδ : 0 < δ)
    (q : XiZeroCopy) (h : ‖xiResolventPoint X q‖ < δ) :
    1 / δ - X - 1 / 4 < (xiSpectralPoint q).re ^ 2 := by
  have hs := xiSpectralPoint_im_sq_lt_quarter q
  have hzne : xiSpectralPoint q ^ 2 + (X : ℂ) ≠ 0 :=
    xiSpectralSq_add_ofReal_ne_zero hX q
  have hnorm_ge : 1 / ((xiSpectralPoint q).re ^ 2 + 1 / 4 + X) ≤
      ‖xiResolventPoint X q‖ := by
    have hub : ‖xiSpectralPoint q ^ 2 + (X : ℂ)‖ ≤
        (xiSpectralPoint q).re ^ 2 + 1 / 4 + X := by
      calc ‖xiSpectralPoint q ^ 2 + (X : ℂ)‖
          ≤ ‖xiSpectralPoint q ^ 2‖ + ‖((X : ℝ) : ℂ)‖ := norm_add_le _ _
        _ ≤ (xiSpectralPoint q).re ^ 2 + 1 / 4 + X := by
            rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX]
            have hsq : ‖xiSpectralPoint q‖ ^ 2 =
                (xiSpectralPoint q).re ^ 2 + (xiSpectralPoint q).im ^ 2 := by
              rw [Complex.sq_norm, Complex.normSq_apply]
              ring
            linarith
    have hg := xiSpectral_re_sq_gt_thirtytwo q
    have hpos : (0 : ℝ) < (xiSpectralPoint q).re ^ 2 + 1 / 4 + X := by linarith
    have hnpos : (0 : ℝ) < ‖xiSpectralPoint q ^ 2 + (X : ℂ)‖ :=
      norm_pos_iff.mpr hzne
    rw [show ‖xiResolventPoint X q‖ = ‖xiSpectralPoint q ^ 2 + (X : ℂ)‖⁻¹ by
      rw [xiResolventPoint, norm_inv], inv_eq_one_div]
    exact one_div_le_one_div_of_le hnpos hub
  have hlt : 1 / ((xiSpectralPoint q).re ^ 2 + 1 / 4 + X) < δ := lt_of_le_of_lt hnorm_ge h
  have hg := xiSpectral_re_sq_gt_thirtytwo q
  have hpos : (0 : ℝ) < (xiSpectralPoint q).re ^ 2 + 1 / 4 + X := by linarith
  rw [div_lt_iff₀ hpos] at hlt
  have hδ' : 1 / δ < (xiSpectralPoint q).re ^ 2 + 1 / 4 + X := by
    rw [div_lt_iff₀ hδ]
    linarith [mul_comm δ ((xiSpectralPoint q).re ^ 2 + 1 / 4 + X)]
  linarith

/-- **Tail domination by the probe budget**: on the tail `γ² ≥ T` the resolvent norm is
dominated by `(T + (c+1/2)²)/(2c(T − 1/4))` times the budget mass at probe `c`. -/
theorem norm_xiResolventPoint_le_budgetMass_of_tail {X c T : ℝ} (hX : 0 ≤ X)
    (hc : 1 / 2 ≤ c) (hT : 1 / 2 ≤ T) (q : XiZeroCopy)
    (hq : T ≤ (xiSpectralPoint q).re ^ 2) :
    ‖xiResolventPoint X q‖ ≤
      (T + (c + 1 / 2) ^ 2) / (2 * c * (T - 1 / 4)) * xiBudgetMassAt c q := by
  have hg := xiSpectral_re_sq_gt_thirtytwo q
  have hApos : (0 : ℝ) < (xiSpectralPoint q).re ^ 2 - 1 / 4 := by linarith
  have hKpos : (0 : ℝ) < (c + 1 / 2) ^ 2 := by positivity
  have hBpos : (0 : ℝ) < (xiSpectralPoint q).re ^ 2 + (c + 1 / 2) ^ 2 := by nlinarith
  have hcpos : (0 : ℝ) < 2 * c := by linarith
  have hTpos : (0 : ℝ) < T - 1 / 4 := by linarith
  have hmono : 1 / ((xiSpectralPoint q).re ^ 2 - 1 / 4) ≤
      (T + (c + 1 / 2) ^ 2) / (2 * c * (T - 1 / 4)) *
        (2 * c / ((xiSpectralPoint q).re ^ 2 + (c + 1 / 2) ^ 2)) := by
    rw [show (T + (c + 1 / 2) ^ 2) / (2 * c * (T - 1 / 4)) *
        (2 * c / ((xiSpectralPoint q).re ^ 2 + (c + 1 / 2) ^ 2)) =
        ((T + (c + 1 / 2) ^ 2) * (2 * c)) /
          ((2 * c * (T - 1 / 4)) * ((xiSpectralPoint q).re ^ 2 + (c + 1 / 2) ^ 2)) from
        div_mul_div_comm _ _ _ _,
      div_le_div_iff₀ hApos (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (le_of_lt hKpos), hcpos.le,
      mul_nonneg (mul_nonneg hcpos.le (sub_nonneg.mpr hq)) hKpos.le]
  calc ‖xiResolventPoint X q‖ ≤ 1 / ((xiSpectralPoint q).re ^ 2 - 1 / 4) :=
        norm_xiResolventPoint_le_inv_floor hX q
    _ ≤ (T + (c + 1 / 2) ^ 2) / (2 * c * (T - 1 / 4)) *
          (2 * c / ((xiSpectralPoint q).re ^ 2 + (c + 1 / 2) ^ 2)) := hmono
    _ ≤ (T + (c + 1 / 2) ^ 2) / (2 * c * (T - 1 / 4)) * xiBudgetMassAt c q :=
        mul_le_mul_of_nonneg_left (xiBudgetMassAt_ge hc q) (by positivity)

/-- **The zero-density surrogate**: the tail norm mass beyond squared height `T` is bounded by
an explicit multiple of one logarithmic-derivative value of `ξ` on the real ray — no counting
function appears. -/
theorem tsum_norm_xiResolventPoint_tail_le_logDeriv {X c T : ℝ} (hX : 0 ≤ X)
    (hc : 1 / 2 ≤ c) (hT : 1 / 2 ≤ T) :
    (∑' q : {q : XiZeroCopy | T ≤ (xiSpectralPoint q).re ^ 2},
      ‖xiResolventPoint X (q : XiZeroCopy)‖) ≤
    (T + (c + 1 / 2) ^ 2) / (2 * c * (T - 1 / 4)) *
      (2 * (logDeriv xi ((1 / 2 : ℂ) + (c : ℂ))).re) := by
  have hne : XiC (xiBudgetProbeAt c) ≠ 0 := XiC_probeAt_ne_zero_of_half_le hc
  have hmsum : Summable (xiBudgetMassAt c) := summable_xiBudgetMassAt hne
  have hpre : (0 : ℝ) ≤ (T + (c + 1 / 2) ^ 2) / (2 * c * (T - 1 / 4)) := by
    have h1 : (0 : ℝ) < 2 * c * (T - 1 / 4) := by nlinarith
    positivity
  have hsub : Summable (fun q : {q : XiZeroCopy | T ≤ (xiSpectralPoint q).re ^ 2} =>
      ‖xiResolventPoint X (q : XiZeroCopy)‖) :=
    (summable_norm_xiResolventPoint hX).subtype _
  have hsubmass : Summable (fun q : {q : XiZeroCopy | T ≤ (xiSpectralPoint q).re ^ 2} =>
      xiBudgetMassAt c (q : XiZeroCopy)) := hmsum.subtype _
  calc (∑' q : {q : XiZeroCopy | T ≤ (xiSpectralPoint q).re ^ 2},
        ‖xiResolventPoint X (q : XiZeroCopy)‖)
      ≤ ∑' q : {q : XiZeroCopy | T ≤ (xiSpectralPoint q).re ^ 2},
          (T + (c + 1 / 2) ^ 2) / (2 * c * (T - 1 / 4)) *
            xiBudgetMassAt c (q : XiZeroCopy) := by
        refine Summable.tsum_le_tsum (fun q => ?_) hsub (hsubmass.mul_left _)
        exact norm_xiResolventPoint_le_budgetMass_of_tail hX hc hT _ q.2
    _ = (T + (c + 1 / 2) ^ 2) / (2 * c * (T - 1 / 4)) *
          ∑' q : {q : XiZeroCopy | T ≤ (xiSpectralPoint q).re ^ 2},
            xiBudgetMassAt c (q : XiZeroCopy) := tsum_mul_left
    _ ≤ (T + (c + 1 / 2) ^ 2) / (2 * c * (T - 1 / 4)) *
          ∑' q : XiZeroCopy, xiBudgetMassAt c q := by
        refine mul_le_mul_of_nonneg_left ?_ hpre
        exact Summable.tsum_subtype_le (fun q => xiBudgetMassAt c q) _
          (fun q => xiBudgetMassAt_nonneg hc q) hmsum
    _ = (T + (c + 1 / 2) ^ 2) / (2 * c * (T - 1 / 4)) *
          (2 * (logDeriv xi ((1 / 2 : ℂ) + (c : ℂ))).re) := by
        rw [tsum_xiBudgetMassAt_eq hne]

/-- **The sub-`δ` tail on ray jets**: the tail-mass input of the two-scale supply is bounded by
one logarithmic-derivative value of `ξ` on the real ray, for any threshold below the scale
forced by `δ`. -/
theorem tsum_norm_xiResolventPoint_subdelta_le_logDeriv {X δ c T : ℝ} (hX : 0 ≤ X)
    (hδ : 0 < δ) (hc : 1 / 2 ≤ c) (hT : 1 / 2 ≤ T) (hTδ : T ≤ 1 / δ - X - 1 / 4) :
    (∑' q : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ},
      ‖xiResolventPoint X (q : XiZeroCopy)‖) ≤
    (T + (c + 1 / 2) ^ 2) / (2 * c * (T - 1 / 4)) *
      (2 * (logDeriv xi ((1 / 2 : ℂ) + (c : ℂ))).re) := by
  have hincl : ∀ q : XiZeroCopy, ‖xiResolventPoint X q‖ < δ →
      T ≤ (xiSpectralPoint q).re ^ 2 := by
    intro q hq
    have h := lt_re_sq_of_norm_xiResolventPoint_lt hX hδ q hq
    linarith
  have hsub1 : Summable (fun q : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ} =>
      ‖xiResolventPoint X (q : XiZeroCopy)‖) :=
    (summable_norm_xiResolventPoint hX).subtype _
  have hsub2 : Summable (fun q : {q : XiZeroCopy | T ≤ (xiSpectralPoint q).re ^ 2} =>
      ‖xiResolventPoint X (q : XiZeroCopy)‖) :=
    (summable_norm_xiResolventPoint hX).subtype _
  refine le_trans ?_ (tsum_norm_xiResolventPoint_tail_le_logDeriv hX hc hT)
  have hsubset : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ} ⊆
      {q : XiZeroCopy | T ≤ (xiSpectralPoint q).re ^ 2} := fun q hq => hincl q hq
  exact Summable.tsum_le_tsum_of_inj (Set.inclusion hsubset)
    (Set.inclusion_injective hsubset) (fun q _ => norm_nonneg _)
    (fun q => le_refl _) hsub1 hsub2

/-- The numeric instance at the critical probe: the sub-`δ` tail never exceeds
`(T+1)/(T−1/4) · 3/50`. -/
theorem tsum_norm_xiResolventPoint_subdelta_le_numeric {X δ T : ℝ} (hX : 0 ≤ X)
    (hδ : 0 < δ) (hT : 1 / 2 ≤ T) (hTδ : T ≤ 1 / δ - X - 1 / 4) :
    (∑' q : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ},
      ‖xiResolventPoint X (q : XiZeroCopy)‖) ≤
    (T + 1) / (T - 1 / 4) * (3 / 50) := by
  have h := tsum_norm_xiResolventPoint_subdelta_le_logDeriv (c := 1 / 2) hX hδ
    (le_refl _) hT hTδ
  have harg : ((1 / 2 : ℂ)) + ((1 / 2 : ℝ) : ℂ) = 1 := by
    norm_num
  rw [harg, logDeriv_xi_one] at h
  have hre : (completedRiemannZeta₀ 1).re ≤ ‖completedRiemannZeta₀ 1‖ :=
    Complex.re_le_norm _
  have hval := norm_completedRiemannZeta₀_one_le
  have hpre : (0 : ℝ) ≤ (T + 1) / (2 * (1 / 2) * (T - 1 / 4)) := by
    have h1 : (0 : ℝ) < 2 * (1 / 2) * (T - 1 / 4) := by nlinarith
    positivity
  calc (∑' q : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ},
        ‖xiResolventPoint X (q : XiZeroCopy)‖)
      ≤ (T + (1 / 2 + 1 / 2) ^ 2) / (2 * (1 / 2) * (T - 1 / 4)) *
          (2 * (completedRiemannZeta₀ 1).re) := h
    _ ≤ (T + 1) / (T - 1 / 4) * (3 / 50) := by
        have hT4 : (0 : ℝ) < T - 1 / 4 := by linarith
        have hpre' : (T + (1 / 2 + 1 / 2) ^ 2) / (2 * (1 / 2) * (T - 1 / 4)) =
            (T + 1) / (T - 1 / 4) := by
          norm_num
        rw [hpre']
        have hfac : (0 : ℝ) ≤ (T + 1) / (T - 1 / 4) := by positivity
        have hjet : 2 * (completedRiemannZeta₀ 1).re ≤ 3 / 50 := by linarith
        exact mul_le_mul_of_nonneg_left hjet hfac

end

end RHTower
namespace RHTower

noncomputable section

/-- **Supply from line placement and ray jets alone**: every rational-nodal single-minor datum
follows from partial line placement above one scale together with one explicit inequality whose
spectral inputs are the unconditional mass budget `198/3175` and one logarithmic-derivative
value of `ξ` on the real ray — no counting function, no tail hypothesis. -/
theorem rational_nodal_datum_of_partial_line_rayJet {X δ c T : ℝ} (hX : 0 ≤ X) (hδ : 0 < δ)
    (hc : 1 / 2 ≤ c) (hT : 1 / 2 ≤ T) (hTδ : T ≤ 1 / δ - X - 1 / 4)
    (hline : ∀ q : XiZeroCopy, δ ≤ ‖xiResolventPoint X q‖ → (xiSpectralPoint q).im = 0)
    {j : ℕ} (cn : Fin j → ℝ) (hcn : ∀ i, 0 ≤ cn i ∧ cn i ≤ 1) (m : ℕ)
    {q₁ q₂ : XiZeroCopy}
    (h1 : δ ≤ ‖xiResolventPoint X q₁‖) (h2 : δ ≤ ‖xiResolventPoint X q₂‖)
    (hne : ‖xiResolventPoint X q₁‖ ≠ ‖xiResolventPoint X q₂‖)
    (hmass : 8 * 2 ^ (4 * j) *
        ((T + (c + 1 / 2) ^ 2) / (2 * c * (T - 1 / 4)) *
          (2 * (logDeriv xi ((1 / 2 : ℂ) + (c : ℂ))).re)) * (198 / 3175) ≤
      2 * ((‖xiResolventPoint X q₁‖ * ‖xiResolventPoint X q₂‖) ^ (2 * m + 1) *
        ((∏ i, (‖xiResolventPoint X q₁‖ - cn i)) ^ 2 *
          (∏ i, (‖xiResolventPoint X q₂‖ - cn i)) ^ 2) *
        (‖xiResolventPoint X q₁‖ - ‖xiResolventPoint X q₂‖) ^ 2)) :
    0 ≤ (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial cn) 0 X *
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial cn) 2 X -
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial cn) 1 X ^ 2).re :=
  rational_nodal_datum_of_partial_line_budget hX hδ hline cn hcn m h1 h2 hne
    (tsum_norm_xiResolventPoint_subdelta_le_logDeriv hX hδ hc hT hTδ) hmass

end

end RHTower

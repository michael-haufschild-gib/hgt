import GaloisForLFunctions.RHTower.XiHeightSelection
import GaloisForLFunctions.RHTower.GammaVerticalRatioUniform
import GaloisForLFunctions.RHTower.DeningerZetaLowerBound

/-!
# Burnol's Proposition 5.1

Titchmarsh's input for the residue series: there is an absolute `A` and a sequence of heights
`T_n > n` with `|ζ(σ + iT_n)|^{-1} ≤ T_n^A` uniformly for `-1 ≤ σ ≤ 2`.

The chain is: the height `T` chosen in `XiHeightSelection` makes the whole one-zero sum `O(log n)`;
the segment estimate then bounds the movement of `log‖xi‖` from the line `Re s = 2` to any
`σ ∈ [-1,2]` by `O(log n)`; and the conversion `xi = s(s-1)/2·Γ_ℝ·ζ` costs only `O(log T)`, because
the Gamma quotient across the strip at a fixed height is *bounded* (the corpus's uniform two-sided
vertical ratio law, plus one Gamma recurrence for the negative abscissae).

## Main results

* `tsum_logKernel_reflect`
* `exists_gamma_half_ratio_bound`, `exists_gammaR_ratio_bound`
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Reflection `ρ ↦ 1 − ρ` identifies the two one-zero families. -/
theorem tsum_logKernel_reflect (T : ℝ) :
    (∑' q : XiZeroCopy, Real.log (1 + 9 / (T + (q.1 : ℂ).im) ^ 2))
      = ∑' q : XiZeroCopy, Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2) := by
  rw [← (xiZeroCopyReflectEquiv).tsum_eq
    (fun q : XiZeroCopy => Real.log (1 + 9 / (T + (q.1 : ℂ).im) ^ 2))]
  refine tsum_congr fun q => ?_
  have him : ((xiZeroCopyReflectEquiv q).1 : ℂ).im = -((q.1 : ℂ).im) := by
    rw [xiZeroCopyReflect_coe]
    simp
  rw [him]
  congr 2

/-! ## The Gamma quotient across the strip -/

theorem exists_gamma_half_ratio_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ u : ℝ, -1 ≤ σ → σ ≤ 2 → 1 ≤ u →
      ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖
        ≤ C * ‖Complex.Gamma (((1 : ℝ) : ℂ) + (u : ℂ) * I)‖ := by
  obtain ⟨c, C, hc0, hC0, hlaw⟩ :=
    GaloisForLFunctions.RHTower.exists_twoSided_gamma_vertical_ratio
      (a₁ := 1) (δ₁ := 1) (by norm_num) (by norm_num)
  refine ⟨C, hC0, ?_⟩
  intro σ u hσ1 hσ2 hu
  have hΓne : ‖Complex.Gamma (((1 : ℝ) : ℂ) + (u : ℂ) * I)‖ ≠ 0 := by
    refine norm_ne_zero_iff.2 (Complex.Gamma_ne_zero ?_)
    intro m hm
    have him := congrArg Complex.im hm
    simp at him
    linarith
  have hΓpos : 0 < ‖Complex.Gamma (((1 : ℝ) : ℂ) + (u : ℂ) * I)‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hΓne)
  rcases le_or_gt 0 σ with hpos | hneg
  · -- the abscissa is already nonnegative
    have hδ : (0 : ℝ) ≤ 1 - σ / 2 := by linarith
    have hδ1 : (1 : ℝ) - σ / 2 ≤ 1 := by linarith
    have hsum : σ / 2 + (1 - σ / 2) = (1 : ℝ) := by ring
    have h := (hlaw (σ / 2) (1 - σ / 2) u (by linarith) (by linarith) hδ hδ1 hu).2
    rw [hsum] at h
    rw [div_le_iff₀ hΓpos] at h
    have hpow : u ^ (-(1 - σ / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith)
    calc ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖
        ≤ C * u ^ (-(1 - σ / 2)) * ‖Complex.Gamma (((1 : ℝ) : ℂ) + (u : ℂ) * I)‖ := h
      _ ≤ C * 1 * ‖Complex.Gamma (((1 : ℝ) : ℂ) + (u : ℂ) * I)‖ := by gcongr
      _ = C * ‖Complex.Gamma (((1 : ℝ) : ℂ) + (u : ℂ) * I)‖ := by ring
  · -- shift the negative abscissa by one Gamma recurrence
    have hz : (((σ / 2 : ℝ) : ℂ) + (u : ℂ) * I) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    have hrec : Complex.Gamma ((((σ / 2 : ℝ) : ℂ) + (u : ℂ) * I) + 1)
        = (((σ / 2 : ℝ) : ℂ) + (u : ℂ) * I) * Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (u : ℂ) * I) :=
      Complex.Gamma_add_one _ hz
    have hnormz : (1 : ℝ) ≤ ‖((σ / 2 : ℝ) : ℂ) + (u : ℂ) * I‖ := by
      have him : (((σ / 2 : ℝ) : ℂ) + (u : ℂ) * I).im = u := by simp
      have := Complex.abs_im_le_norm (((σ / 2 : ℝ) : ℂ) + (u : ℂ) * I)
      rw [him] at this
      calc (1 : ℝ) ≤ u := hu
        _ = |u| := (abs_of_nonneg (by linarith)).symm
        _ ≤ _ := this
    have hshift : ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖
        ≤ ‖Complex.Gamma ((((σ / 2 + 1 : ℝ)) : ℂ) + (u : ℂ) * I)‖ := by
      have hcast : (((σ / 2 : ℝ) : ℂ) + (u : ℂ) * I) + 1
          = (((σ / 2 + 1 : ℝ)) : ℂ) + (u : ℂ) * I := by
        push_cast
        ring
      rw [hcast] at hrec
      rw [hrec, norm_mul]
      nlinarith [norm_nonneg (Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (u : ℂ) * I)), hnormz]
    have hδ : (0 : ℝ) ≤ -(σ / 2) := by linarith
    have hδ1 : -(σ / 2) ≤ 1 := by linarith
    have hsum : (σ / 2 + 1) + (-(σ / 2)) = (1 : ℝ) := by ring
    have h := (hlaw (σ / 2 + 1) (-(σ / 2)) u (by linarith) (by linarith) hδ hδ1 hu).2
    rw [hsum] at h
    rw [div_le_iff₀ hΓpos] at h
    have hpow : u ^ (-(-(σ / 2))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith)
    calc ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖
        ≤ ‖Complex.Gamma ((((σ / 2 + 1 : ℝ)) : ℂ) + (u : ℂ) * I)‖ := hshift
      _ ≤ C * u ^ (-(-(σ / 2))) * ‖Complex.Gamma (((1 : ℝ) : ℂ) + (u : ℂ) * I)‖ := h
      _ ≤ C * 1 * ‖Complex.Gamma (((1 : ℝ) : ℂ) + (u : ℂ) * I)‖ := by gcongr
      _ = C * ‖Complex.Gamma (((1 : ℝ) : ℂ) + (u : ℂ) * I)‖ := by ring

theorem exists_gammaR_ratio_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ τ : ℝ, -1 ≤ σ → σ ≤ 2 → 2 ≤ τ →
      ‖Complex.Gammaℝ ((σ : ℂ) + (τ : ℂ) * I)‖
        ≤ C * ‖Complex.Gammaℝ ((2 : ℂ) + (τ : ℂ) * I)‖ := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_gamma_half_ratio_bound
  refine ⟨C₁ * Real.pi ^ (3 / 2 : ℝ), by positivity, ?_⟩
  intro σ τ hσ1 hσ2 hτ
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsplit : ∀ x : ℝ, ‖Complex.Gammaℝ ((x : ℂ) + (τ : ℂ) * I)‖
      = Real.pi ^ (-x / 2) * ‖Complex.Gamma (((x / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖ := by
    intro x
    rw [Complex.Gammaℝ_def, norm_mul]
    congr 1
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos hπ]
      congr 1
      simp
    · congr 1
      push_cast
      ring
  have hc2 : ((2 : ℂ) + (τ : ℂ) * I) = (((2 : ℝ) : ℂ) + (τ : ℂ) * I) := by norm_num
  rw [hc2, hsplit σ, hsplit 2]
  have hτ2 : (1 : ℝ) ≤ τ / 2 := by linarith
  have hΓ := hC₁ σ (τ / 2) hσ1 hσ2 hτ2
  have hcast : ((1 : ℝ) : ℂ) = (2 / 2 : ℝ) := by norm_num
  have hΓ2 : ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖
      ≤ C₁ * ‖Complex.Gamma ((((2 : ℝ) / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖ := by
    have : (((2 : ℝ) / 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by norm_num
    rw [this]
    exact hΓ
  have hpow1 : Real.pi ^ (-σ / 2) ≤ Real.pi ^ (3 / 2 : ℝ) * Real.pi ^ (-(2 : ℝ) / 2) := by
    rw [← Real.rpow_add hπ]
    refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
    have := Real.pi_gt_three
    linarith
  have hnn : (0 : ℝ) ≤ ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖ :=
    norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ ‖Complex.Gamma ((((2 : ℝ) / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖ :=
    norm_nonneg _
  have hp1 : (0 : ℝ) < Real.pi ^ (-σ / 2) := Real.rpow_pos_of_pos hπ _
  have hp2 : (0 : ℝ) < Real.pi ^ (-(2 : ℝ) / 2) := Real.rpow_pos_of_pos hπ _
  have hp3 : (0 : ℝ) < Real.pi ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hπ _
  calc Real.pi ^ (-σ / 2) * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖
      ≤ Real.pi ^ (-σ / 2)
        * (C₁ * ‖Complex.Gamma ((((2 : ℝ) / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖) := by
        exact mul_le_mul_of_nonneg_left hΓ2 hp1.le
    _ ≤ (Real.pi ^ (3 / 2 : ℝ) * Real.pi ^ (-(2 : ℝ) / 2))
        * (C₁ * ‖Complex.Gamma ((((2 : ℝ) / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖) := by
        refine mul_le_mul_of_nonneg_right hpow1 ?_
        positivity
    _ = C₁ * Real.pi ^ (3 / 2 : ℝ)
        * (Real.pi ^ (-(2 : ℝ) / 2)
          * ‖Complex.Gamma ((((2 : ℝ) / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖) := by
        ring

/-- The movement of `log‖xi‖` from the line `Re s = 2` across the strip. -/
theorem log_norm_xi_lower {T : ℝ} (hne : ∀ u : ℝ, xi ((u : ℂ) + (T : ℂ) * I) ≠ 0)
    (h1 : ∀ q : XiZeroCopy, T - (q.1 : ℂ).im ≠ 0)
    (h2 : ∀ q : XiZeroCopy, T + (q.1 : ℂ).im ≠ 0)
    {B : ℝ} (hB : (∑' q : XiZeroCopy, Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2)) ≤ B)
    {σ : ℝ} (hσ1 : -1 ≤ σ) (hσ2 : σ ≤ 2) :
    Real.log ‖xi ((2 : ℂ) + (T : ℂ) * I)‖ - B
      ≤ Real.log ‖xi ((σ : ℂ) + (T : ℂ) * I)‖ := by
  have hmod := log_norm_xi_horizontal hne 2 σ
  have hcast2 : (((2 : ℝ) : ℂ) + (T : ℂ) * I) = ((2 : ℂ) + (T : ℂ) * I) := by norm_num
  rw [hcast2] at hmod
  have hseg := abs_two_mul_integral_re_logDeriv_xi_le hne h1 h2 hσ1 hσ2
  have hrefl := tsum_logKernel_reflect T
  have hsum : (∑' q : XiZeroCopy, (Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2)
      + Real.log (1 + 9 / (T + (q.1 : ℂ).im) ^ 2)))
      = 2 * ∑' q : XiZeroCopy, Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2) := by
    have hsummable2 : Summable
        (fun q : XiZeroCopy => Real.log (1 + 9 / (T + (q.1 : ℂ).im) ^ 2)) := by
      refine (summable_logKernel (-T)).congr fun q => ?_
      rw [show (-T - (q.1 : ℂ).im) ^ 2 = (T + (q.1 : ℂ).im) ^ 2 by ring]
    rw [(summable_logKernel T).tsum_add hsummable2, hrefl]
    ring
  rw [hsum] at hseg
  have habs : |(∫ u in σ..2, logDeriv xi ((u : ℂ) + (T : ℂ) * I)).re| ≤ B := by
    have h2abs : |2 * (∫ u in σ..2, logDeriv xi ((u : ℂ) + (T : ℂ) * I)).re|
        = 2 * |(∫ u in σ..2, logDeriv xi ((u : ℂ) + (T : ℂ) * I)).re| := by
      rw [abs_mul]
      norm_num
    rw [h2abs] at hseg
    linarith
  have hswap : (∫ u in (2 : ℝ)..σ, logDeriv xi ((u : ℂ) + (T : ℂ) * I))
      = -∫ u in σ..(2 : ℝ), logDeriv xi ((u : ℂ) + (T : ℂ) * I) :=
    intervalIntegral.integral_symm _ _
  rw [hswap] at hmod
  have hneg : (-(∫ u in σ..(2 : ℝ), logDeriv xi ((u : ℂ) + (T : ℂ) * I))).re
      = -((∫ u in σ..(2 : ℝ), logDeriv xi ((u : ℂ) + (T : ℂ) * I)).re) := Complex.neg_re _
  rw [hneg] at hmod
  have hle := abs_le.1 habs
  linarith [hmod, hle.1, hle.2]

/-! ## The factorisation of `xi` -/

theorem gammaR_ne_zero_of_im_ne {s : ℂ} (hs : s.im ≠ 0) : Complex.Gammaℝ s ≠ 0 := by
  rw [Complex.Gammaℝ_def]
  refine mul_ne_zero ?_ ?_
  · refine Complex.cpow_ne_zero_iff_of_exponent_ne_zero ?_ |>.2 ?_
    · intro h
      have := congrArg Complex.re h
      simp at this
      exact hs (by simpa using congrArg Complex.im h)
    · exact Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  · refine Complex.Gamma_ne_zero ?_
    intro m hm
    have him := congrArg Complex.im hm
    simp at him
    exact hs (by linarith [him])

theorem xi_eq_factor {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hΓ : Complex.Gammaℝ s ≠ 0) :
    xi s = s * (s - 1) / 2 * Complex.Gammaℝ s * riemannZeta s := by
  rw [xi_eq_half_mul h0 h1]
  have hz := riemannZeta_def_of_ne_zero h0
  have : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
    rw [hz]
    field_simp
  rw [this]
  ring

theorem log_norm_xi_factor {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hΓ : Complex.Gammaℝ s ≠ 0)
    (hζ : riemannZeta s ≠ 0) :
    Real.log ‖xi s‖
      = Real.log ‖s * (s - 1) / 2‖ + Real.log ‖Complex.Gammaℝ s‖
        + Real.log ‖riemannZeta s‖ := by
  rw [xi_eq_factor h0 h1 hΓ, norm_mul, norm_mul]
  have hA : ‖s * (s - 1) / 2‖ ≠ 0 := by
    refine norm_ne_zero_iff.2 ?_
    refine div_ne_zero (mul_ne_zero h0 ?_) (by norm_num)
    exact sub_ne_zero.2 h1
  have hB : ‖Complex.Gammaℝ s‖ ≠ 0 := norm_ne_zero_iff.2 hΓ
  have hC : ‖riemannZeta s‖ ≠ 0 := norm_ne_zero_iff.2 hζ
  rw [Real.log_mul (by positivity) hC, Real.log_mul hA hB]

/-! ## Proposition 5.1 -/

/-- **Burnol's Proposition 5.1** (Titchmarsh IX.7).  There is an absolute exponent `A` and, in every
unit interval far enough out, a height `T` at which `|ζ(σ+iT)|^{-1} ≤ T^A` uniformly on
`-1 ≤ σ ≤ 2`. -/
theorem exists_zeta_inv_horizontal_bound :
    ∃ A : ℝ, 0 < A ∧ ∃ n₀ : ℝ, ∀ n : ℝ, n₀ ≤ n → ∃ T : ℝ, n ≤ T ∧ T ≤ n + 1 ∧
      ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
        (T : ℝ) ^ (-A) ≤ ‖riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖ := by
  obtain ⟨C, hC0, m₀, hgood⟩ := exists_good_height
  obtain ⟨CΓ, hCΓ0, hCΓ⟩ := exists_gammaR_ratio_bound
  refine ⟨2 * Real.log 4 + |Real.log CΓ| + C + Real.log 4 + 1, by positivity,
    max m₀ 10, ?_⟩
  intro n hn
  have hn10 : (10 : ℝ) ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨T, hTlow, hThigh, hT1, hT2, hTsum⟩ := hgood n (le_trans (le_max_left _ _) hn)
  refine ⟨T, hTlow, hThigh, ?_⟩
  have hT10 : (10 : ℝ) ≤ T := le_trans hn10 hTlow
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogn : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hlognT : Real.log n ≤ Real.log T := Real.log_le_log (by linarith) hTlow
  -- the line carries no zero of `xi`
  have hne : ∀ u : ℝ, xi ((u : ℂ) + (T : ℂ) * I) ≠ 0 := by
    intro u hzero
    have hmem := mem_xi_divisor_support_of_eq_zero hzero
    set ρ : XiDivisorSupport := ⟨(u : ℂ) + (T : ℂ) * I, hmem⟩ with hρ
    have hpos := xi_divisor_pos_on_support ρ
    have hnpos : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by omega
    have him : ((ρ : XiDivisorSupport) : ℂ).im = T := by rw [hρ]; simp
    exact hT1 (⟨ρ, ⟨0, hnpos⟩⟩ : XiZeroCopy) (by rw [him]; ring)
  intro σ hσ1 hσ2
  set s : ℂ := (σ : ℂ) + (T : ℂ) * I with hs
  set s₂ : ℂ := (2 : ℂ) + (T : ℂ) * I with hs₂
  have hsim : s.im = T := by rw [hs]; simp
  have hs₂im : s₂.im = T := by rw [hs₂]; simp
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hsim
    simp at hsim
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hsim
    simp at hsim
    linarith
  have hs₂0 : s₂ ≠ 0 := by
    intro h
    rw [h] at hs₂im
    simp at hs₂im
    linarith
  have hs₂1 : s₂ ≠ 1 := by
    intro h
    rw [h] at hs₂im
    simp at hs₂im
    linarith
  have hΓs : Complex.Gammaℝ s ≠ 0 := gammaR_ne_zero_of_im_ne (by rw [hsim]; linarith)
  have hΓs₂ : Complex.Gammaℝ s₂ ≠ 0 := gammaR_ne_zero_of_im_ne (by rw [hs₂im]; linarith)
  have hxis : xi s ≠ 0 := hne σ
  have hxis₂ : xi s₂ ≠ 0 := by
    have := hne 2
    rw [hs₂]
    simpa using this
  have hζs : riemannZeta s ≠ 0 := by
    intro h
    apply hxis
    rw [xi_eq_factor hs0 hs1 hΓs, h, mul_zero]
  have hζs₂ : riemannZeta s₂ ≠ 0 := by
    intro h
    apply hxis₂
    rw [xi_eq_factor hs₂0 hs₂1 hΓs₂, h, mul_zero]
  -- the two factorisations
  have hfac := log_norm_xi_factor hs0 hs1 hΓs hζs
  have hfac₂ := log_norm_xi_factor hs₂0 hs₂1 hΓs₂ hζs₂
  -- the segment estimate
  have hseg := log_norm_xi_lower hne hT1 hT2 hTsum hσ1 hσ2
  rw [← hs, ← hs₂] at hseg
  -- the Gamma quotient
  have hΓratio : Real.log ‖Complex.Gammaℝ s‖ ≤ Real.log CΓ + Real.log ‖Complex.Gammaℝ s₂‖ := by
    have hb := hCΓ σ T hσ1 hσ2 (by linarith)
    rw [← hs, ← hs₂] at hb
    have hpos₂ : (0 : ℝ) < ‖Complex.Gammaℝ s₂‖ := norm_pos_iff.2 hΓs₂
    have hpos : (0 : ℝ) < ‖Complex.Gammaℝ s‖ := norm_pos_iff.2 hΓs
    calc Real.log ‖Complex.Gammaℝ s‖
        ≤ Real.log (CΓ * ‖Complex.Gammaℝ s₂‖) := Real.log_le_log hpos hb
      _ = Real.log CΓ + Real.log ‖Complex.Gammaℝ s₂‖ := Real.log_mul hCΓ0.ne' hpos₂.ne'
  -- the rational factors
  have hnormT : ∀ x : ℝ, T ≤ ‖(x : ℂ) + (T : ℂ) * I‖ := by
    intro x
    have him : ((x : ℂ) + (T : ℂ) * I).im = T := by simp
    have := Complex.abs_im_le_norm ((x : ℂ) + (T : ℂ) * I)
    rw [him, abs_of_nonneg hT0.le] at this
    exact this
  have hrat₂ : Real.log (T ^ 2 / 2) ≤ Real.log ‖s₂ * (s₂ - 1) / 2‖ := by
    have h1 : T ≤ ‖s₂‖ := hnormT 2
    have h2 : T ≤ ‖s₂ - 1‖ := by
      have hsub : s₂ - 1 = ((1 : ℝ) : ℂ) + (T : ℂ) * I := by rw [hs₂]; push_cast; ring
      rw [hsub]
      exact hnormT 1
    have hval : ‖s₂ * (s₂ - 1) / 2‖ = ‖s₂‖ * ‖s₂ - 1‖ / 2 := by
      rw [norm_div, norm_mul]
      norm_num
    rw [hval]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith [norm_nonneg s₂, norm_nonneg (s₂ - 1)]
  have hrat : Real.log ‖s * (s - 1) / 2‖ ≤ Real.log (2 * T ^ 2) := by
    have h1 : ‖s‖ ≤ 2 * T := by
      have hre : s.re = σ := by rw [hs]; simp
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ = |σ| + T := by rw [hre, hsim, abs_of_nonneg hT0.le]
        _ ≤ 2 * T := by
            have : |σ| ≤ 2 := abs_le.2 ⟨by linarith, hσ2⟩
            linarith
    have h2 : ‖s - 1‖ ≤ 2 * T := by
      have hsub : s - 1 = ((σ - 1 : ℝ) : ℂ) + (T : ℂ) * I := by rw [hs]; push_cast; ring
      rw [hsub]
      have hre : (((σ - 1 : ℝ) : ℂ) + (T : ℂ) * I).re = σ - 1 := by simp
      have him : (((σ - 1 : ℝ) : ℂ) + (T : ℂ) * I).im = T := by simp
      calc ‖((σ - 1 : ℝ) : ℂ) + (T : ℂ) * I‖
          ≤ |(((σ - 1 : ℝ) : ℂ) + (T : ℂ) * I).re| + |(((σ - 1 : ℝ) : ℂ) + (T : ℂ) * I).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = |σ - 1| + T := by rw [hre, him, abs_of_nonneg hT0.le]
        _ ≤ 2 * T := by
            have : |σ - 1| ≤ 3 := abs_le.2 ⟨by linarith, by linarith⟩
            linarith
    have hval : ‖s * (s - 1) / 2‖ = ‖s‖ * ‖s - 1‖ / 2 := by
      rw [norm_div, norm_mul]
      norm_num
    rw [hval]
    have h3 : (0 : ℝ) < ‖s‖ := norm_pos_iff.2 hs0
    have h4 : (0 : ℝ) < ‖s - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hs1)
    refine Real.log_le_log (by positivity) ?_
    nlinarith [norm_nonneg s, norm_nonneg (s - 1)]
  have hlogdiff : Real.log (T ^ 2 / 2) - Real.log (2 * T ^ 2) = -Real.log 4 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by norm_num) (by positivity)]
    have : Real.log 4 = Real.log 2 + Real.log 2 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    linarith
  -- the zeta value at abscissa two
  have hζ₂ : Real.log (1 / 4) ≤ Real.log ‖riemannZeta s₂‖ := by
    refine Real.log_le_log (by norm_num) ?_
    refine norm_riemannZeta_ge_of_two_le_re ?_
    rw [hs₂]
    simp
  have hlog4 : Real.log (1 / 4) = -Real.log 4 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    simp
  -- assemble the lower bound for `log ‖ζ‖`
  have hlower : -((2 * Real.log 4 + |Real.log CΓ| + C + Real.log 4 + 1) * Real.log T)
      ≤ Real.log ‖riemannZeta s‖ := by
    have hCΓabs : Real.log CΓ ≤ |Real.log CΓ| := le_abs_self _
    have hlog4nn : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hCabs : (0 : ℝ) ≤ |Real.log CΓ| := abs_nonneg _
    have hkey : Real.log ‖riemannZeta s‖
        ≥ -Real.log 4 + (-Real.log CΓ) + (-Real.log 4) - C * Real.log n := by
      have e1 : Real.log ‖riemannZeta s‖
          = Real.log ‖xi s‖ - Real.log ‖s * (s - 1) / 2‖ - Real.log ‖Complex.Gammaℝ s‖ := by
        rw [hfac]; ring
      have e2 : Real.log ‖xi s₂‖
          = Real.log ‖s₂ * (s₂ - 1) / 2‖ + Real.log ‖Complex.Gammaℝ s₂‖
            + Real.log ‖riemannZeta s₂‖ := hfac₂
      rw [e1]
      rw [hlog4] at hζ₂
      linarith [hseg, hΓratio, hrat, hrat₂, hlogdiff, hζ₂]
    have hbound : C * Real.log n ≤ C * Real.log T := by
      exact mul_le_mul_of_nonneg_left hlognT hC0.le
    have hlogT1 : 1 ≤ Real.log T := le_trans hlogn hlognT
    nlinarith [hkey, hbound, hlogT1, hlog4nn, hCabs, hCΓabs, hC0]
  -- exponentiate
  have hζpos : (0 : ℝ) < ‖riemannZeta s‖ := norm_pos_iff.2 hζs
  have hrpow : (T : ℝ) ^ (-(2 * Real.log 4 + |Real.log CΓ| + C + Real.log 4 + 1))
      = Real.exp (Real.log T * (-(2 * Real.log 4 + |Real.log CΓ| + C + Real.log 4 + 1))) :=
    Real.rpow_def_of_pos hT0 _
  rw [hrpow, ← Real.exp_log hζpos]
  refine Real.exp_le_exp.2 ?_
  nlinarith [hlower]

end

end RHTower



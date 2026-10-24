import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhatAGramFunctionalCertifiesWithoutEffectivity
import GaloisForLFunctions.TransThresholdPairCorrelation.NarrowStripClosePairEnergyAndExchangeRate
import GaloisForLFunctions.TransThresholdPairCorrelation.SmoothWeightedCertificateAtFourThirds

/-!
# Coalescent-Band Localization, Universal `N₀*` Moment Transfer, and the Separation of `HD(1)` from `3/4`

This module resolves Open Problem 6 of `ArithmeticCastelnuovoSeveri` (*Beyond `2/3` and `HD(1)`*)
by proving the exact structural and quantitative laws governing both routes beyond `2/3` and
`HD(1)` to `3/4`, together with their unconditional downstream upgrades to the off-line moment and
critical-line census across `RHTower`:

1. **Universal `N₀*` Reflection Bound and Off-Line Moment Transfer Without Simplicity
   (`zeta23_N0star_zero_eq_card_and_le_xiPosCriticalZeroCount`, `zeta23_N0star_window_eq`,
   `two_mul_sum_right_add_N0star_le`, `cumulative_N0star_of_dyadic_N0star`,
   `eventually_dyadicWindowTail_le_selberg_upper_of_N0star`,
   `eventually_offLineMoment_le_of_zetaGateFrom_N0star`,
   `eventually_offLineMoment_le_sixtySix_thousandths`):**
   - On every window `(T₁, T₂]` (`0 ≤ T₁`), the distinct critical-line zero count
     `Zeta23.N0star T₁ T₂` and the right-half zero multiplicity `R(T₁, T₂)` satisfy the
     reflection bound `2 R(T₁, T₂) + N₀*(T₁, T₂) ≤ N(T₁, T₂)` (`two_mul_sum_right_add_N0star_le`),
     requiring no simplicity hypothesis.
   - Consequently, **any** dyadic lower bound `(p₀ − ε) N(T, 2T) ≤ N₀*(T, 2T)` (`0 < p₀ ≤ 7/8`)
     transfers immediately to the cumulative critical-line count `(p₀ − ε) N(0, T) ≤ N₀*(0, T)`,
     the dyadic right-zero ceiling `R(T, 2T) ≤ ((1 − p₀)/2 + ε) N(T, 2T)`, the dyadic window
     off-line moment `4π windowTail 0 (T + 1) (2T − 1) ≤ (log c_R − (1 + p₀) R + η) T`, and the
     cumulative off-line moment `4π offLineMoment V ≤ (log c_R − (1 + p₀) R + η) V`.
   - **Unconditional cumulative off-line moment upgrade (`66/1000`):** Feeding the unconditional
     Montgomery–Taylor simple-critical density `HD(1) ≥ 1681/2500` into the cumulative gate
     upgrades `RHTower.offLineMoment V ≤ (66/1000) V` unconditionally (`R = 3/2`), matching the
     dyadic window bound of `WhatAGramFunctionalCertifiesWithoutEffectivity`.

2. **Route I (Zero-Side Spectral Slack): Exact `HD(1)` Thresholds and `57/1000` Moment Upgrade
   (`not_zeroSideSlack_of_lt_target`, `not_HD_one_zeroSideSlack_of_lt_HD_one`,
   `zeta_N0star_and_offLineMoment_of_spectralSlack`,
   `hyperbolic_displacedPair_general_target_iff`):**
   - For any target proportion `q` and any sub-threshold bandwidth `λ ∈ (0, min q 1)`, the grid
     dimension ceiling forces `zeroSideSlack(λ, T) < (q − H(λ)) N(T, 2T)` eventually. In
     particular, the spectral-slack route to `HD(1)` is unconditionally refuted for all
     `λ ∈ (0, HD(1))` (including all `λ ≤ 1681/2500`), whereas for `λ ∈ [254/375, 1)` it is
     unobstructed by the grid ceiling even for `λ < 3/4`.
   - Whenever `λ ∈ [3/4, 1)` and `zeroSideSlack(λ, T) ≥ (3/4 − H(λ)) N(T, 2T)` eventually, the
     universal `N₀*` transfer upgrades **both** the dyadic window tail and the cumulative
     `offLineMoment V` to `(57/1000)`.
   - In the hyperbolic displaced-pair model `2p(1 + 2η)² = (1/3)N`, the full spectral slack
     satisfies `(2/3)N + 4pη(1 + 2η) = N(1 − 1/(3(1 + 2η)))`, reaching any target `q < 1` iff
     `3(1 − q)(1 + 2η) ≥ 1` (`η ≥ 2/121` for `q = 254/375 > HD(1)` vs. `η ≥ 1/6` for `q = 3/4`).

3. **Route II (Smooth-Window Coalescent Localization at `λ = 4/3`) and the Five-Model Sieve
   Separation of `HD(1)` from `3/4` (`CoalescentSurplusAtMost`,
   `zeta_N0star_and_offLineMoment_of_coalescentSurplus`,
   `coalescent_budget_thresholds_for_two_thirds_HD_one_and_three_quarters`,
   `five_model_separation_of_HD_one_and_three_quarters`):**
   - By `TransThresholdPairCorrelation.zeta_coalescent_certificate`, smooth grid weighting at
     `λ = 4/3` unconditionally eliminates the archimedean end effect, prime–pole cross channel,
     sum frequencies, and all far prime pairs `|log(n/m)| > T^{−1+η}`, reducing the critical-line
     proportion to `29/36 − β` where `β` is the normalized `coalescentSurplus` on
     `0 < |log(n/m)| ≤ T^{−1+η}` alone:
     * `29/36 − β > 2/3 ↔ β < 5/36` (`2.5` times the `1/18` budget);
     * `29/36 − β ≥ 254/375 (> HD(1)) ↔ β ≤ 577/4500`;
     * `29/36 − β ≥ 3/4 ↔ β ≤ 1/18` (which upgrades both dyadic and cumulative off-line moments to
       `57/1000`).
   - **Sieve-theoretic separation of `HD(1)` from `3/4`:** In the unsigned additive sieve model
     `F(α) = α + Υ` on `[1, 4/3]`, the prime surplus is `Υ/16`. While reaching `3/4` requires
     `Υ ≤ 8/9 < 1` (impossible without signed cancellation), **the factor-two sieve parity limit
     `Υ = 2` has surplus `1/8 < 577/4500` and certifies `29/36 − 1/8 = 49/72 > 254/375 > HD(1) > 2/3`**!
     In the spectral sieve model `F(α) = Υ` (after Frullani cancellation of the Poisson continuum
     `abs_integral_dyadic_frullani_le`), `Υ = 2` reaches `3/4` exactly and `Υ = 3` certifies
     `11/16 > 254/375 > HD(1)`.

4. **Exact Variational Two-Window Mixture Envelope (`mixOpt`, `mixOptWeight`,
   `mixOpt_sub_two_sub_mixQ`, `mixOpt_values_and_three_quarters_criterion`):**
   - Completing the square in `ε` for `RHTower.mixQ B ε` yields the exact optimal mixing weight
     `mixOptWeight B = (1 + 36B)/(2(91 + 9B))` and maximum certified proportion
     `mixOpt B = 2/3 + (181 − 18B)² / (1728(91 + 9B))`.
   - For all `B > −91/9`, `(∃ ε, 3/4 ≤ 2 − mixQ B ε) ↔ 3/4 ≤ mixOpt B ↔ 27432 ≤ (18B − 217)²`
     (which holds up to `B = 2954/1035 > 117/41` at `ε = 4/9`), while `mixOpt 7 ≥ 254/375 > HD(1)`
     (so the two-window mixture strictly beats `HD(1)` all the way up to `B = 7`).
-/

open Complex Real Set Filter MeasureTheory intervalIntegral
open scoped BigOperators Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open _root_.RHTower GaloisForLFunctions.RHTower GaloisForLFunctions.HTGeometry
  GaloisForLFunctions.TransThresholdPairCorrelation

/-! ## 1. Universal `N₀*` Reflection Bound and Off-Line Moment Transfer Without Simplicity -/

/-- `Zeta23.N0star 0 T` (distinct critical-line zeros in `(0, T]`) equals the cardinality of
`(stripFinsetPos T).filter (fun z => z.re = 1/2)` and is bounded above by the critical-line
multiplicity sum `RHTower.xiPosCriticalZeroCount T`. -/
theorem zeta23_N0star_zero_eq_card_and_le_xiPosCriticalZeroCount (T : ℝ) :
    Zeta23.N0star 0 T = ((RHTower.stripFinsetPos T).filter (fun z => z.re = 1 / 2)).card ∧
    Zeta23.N0star 0 T ≤ RHTower.xiPosCriticalZeroCount T := by
  classical
  have hcard : Zeta23.N0star 0 T =
      ((RHTower.stripFinsetPos T).filter (fun z => z.re = 1 / 2)).card := by
    unfold Zeta23.N0star
    rw [← Set.ncard_coe_finset]
    congr 1
    ext z
    have hw := congrArg (fun s : Finset ℂ => z ∈ s)
      (RHTower.zeta23_zerosIn_zero_toFinset_eq_stripFinsetPos T)
    simp only [Set.Finite.mem_toFinset, eq_iff_iff] at hw
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, hw]
  refine ⟨hcard, ?_⟩
  rw [hcard]
  unfold RHTower.xiPosCriticalZeroCount
  calc ((RHTower.stripFinsetPos T).filter (fun z => z.re = 1 / 2)).card
      = ∑ _z ∈ (RHTower.stripFinsetPos T).filter (fun z => z.re = 1 / 2), 1 := by
        rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ z ∈ (RHTower.stripFinsetPos T).filter (fun z => z.re = 1 / 2),
          (analyticOrderAt RHTower.xi z).toNat := by
        refine Finset.sum_le_sum fun z hz => ?_
        have hzero : RHTower.xi z = 0 :=
          (RHTower.mem_stripFinsetPos.mp (Finset.mem_filter.mp hz).1).2.2.2.2
        exact Nat.one_le_iff_ne_zero.mpr (RHTower.xi_order_toNat_ne_zero hzero)

/-- On any window `(T₁, T₂]` with `0 ≤ T₁`, `Zeta23.N0star T₁ T₂` equals the cardinality of the
distinct completed-`ξ` zeros on the critical line `Re z = 1/2`. -/
theorem zeta23_N0star_window_eq {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) :
    Zeta23.N0star T₁ T₂ =
      ((RHTower.stripFinsetPos T₂ \ RHTower.stripFinsetPos T₁).filter
        (fun z => z.re = 1 / 2)).card := by
  classical
  unfold Zeta23.N0star
  rw [← Set.ncard_coe_finset]
  congr 1
  ext z
  have hw := congrArg (fun s : Finset ℂ => z ∈ s)
    (RHTower.zeta23_zerosIn_toFinset_eq_window (T₂ := T₂) hT₁)
  simp only [Set.Finite.mem_toFinset, eq_iff_iff] at hw
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, hw]

/-- **Window Reflection Inequality for `N₀*` (`2 R(T₁, T₂) + N₀*(T₁, T₂) ≤ N(T₁, T₂)`).**
For every `0 ≤ T₁` and `T₂ : ℝ`, twice the right-half zero multiplicity plus the distinct
critical-line zero count `N₀*(T₁, T₂)` is at most the total zero multiplicity `N(T₁, T₂)`. -/
theorem two_mul_sum_right_add_N0star_le {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) :
    2 * ∑ z ∈ RHTower.stripFinsetPos T₂ \ RHTower.stripFinsetPos T₁,
        ((analyticOrderAt RHTower.xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0) +
      (Zeta23.N0star T₁ T₂ : ℝ) ≤
      (Zeta23.Ncount T₁ T₂ : ℝ) := by
  classical
  rw [RHTower.zeta23_Ncount_window_eq hT₁, zeta23_N0star_window_eq hT₁]
  set S := RHTower.stripFinsetPos T₂ \ RHTower.stripFinsetPos T₁
  set m : ℂ → ℝ := fun z => ((analyticOrderAt RHTower.xi z).toNat : ℝ)
  have hmr : ∀ z, m (RHTower.lineReflect z) = m z := fun z => by
    simp only [m, RHTower.xi_orderAt_lineReflect]
  have hrefl := RHTower.sum_lineReflect_eq (fun z hz => RHTower.lineReflect_mem_window hz)
    (t := S) (fun z => m z * (if 1 / 2 < z.re then 1 else 0))
  simp only [hmr, RHTower.lineReflect_re] at hrefl
  have hcard : (((S.filter (fun z => z.re = 1 / 2)).card : ℕ) : ℝ) =
      ∑ z ∈ S, (if z.re = 1 / 2 then (1 : ℝ) else 0) := by
    rw [Finset.sum_boole]
  rw [hcard, two_mul]
  nth_rewrite 1 [← hrefl]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z hz => ?_
  have hm0 : 0 ≤ m z := Nat.cast_nonneg _
  rcases lt_trichotomy z.re (1 / 2) with hlt | heq | hgt
  · have h1 : 1 / 2 < 1 - z.re := by linarith
    have h2 : ¬ (1 / 2 < z.re) := by linarith
    have h3 : z.re ≠ 1 / 2 := ne_of_lt hlt
    rw [if_pos h1, if_neg h2, if_neg h3]; linarith
  · have h1 : ¬ (1 / 2 < 1 - z.re) := by linarith
    have h2 : ¬ (1 / 2 < z.re) := by linarith
    rw [if_neg h1, if_neg h2, if_pos heq]
    have hzero : RHTower.xi z = 0 :=
      (RHTower.mem_stripFinsetPos.mp (Finset.mem_sdiff.mp hz).1).2.2.2.2
    have h1m : (1 : ℝ) ≤ m z := by
      dsimp only [m]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (RHTower.xi_order_toNat_ne_zero hzero)
    linarith
  · have h1 : ¬ (1 / 2 < 1 - z.re) := by linarith
    have h3 : z.re ≠ 1 / 2 := ne_of_gt hgt
    rw [if_neg h1, if_pos hgt, if_neg h3]; linarith

/-- **Universal Dyadic-to-Cumulative Transfer for `N₀*`.**
Any dyadic critical-line proportion `p₀` for `Zeta23.N0star T (2 * T)` transfers to the cumulative
census `Zeta23.N0star 0 T` and `RHTower.xiPosCriticalZeroCount T`. -/
theorem cumulative_N0star_of_dyadic_N0star {p₀ : ℝ}
    (hdy : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (p₀ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Zeta23.N0star T (2 * T) : ℝ)) :
    (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (p₀ - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ (Zeta23.N0star 0 T : ℝ)) ∧
    (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (p₀ - ε) * (RHTower.xiPosZeroCount T : ℝ) ≤ (RHTower.xiPosCriticalZeroCount T : ℝ)) := by
  have hcum := Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) hdy
  refine ⟨hcum, fun ε hε => ?_⟩
  obtain ⟨T₀, hT₀⟩ := hcum ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  rw [RHTower.zeta23_Ncount_zero_eq_xiPosZeroCount] at h1
  have h2 : (Zeta23.N0star 0 T : ℝ) ≤ (RHTower.xiPosCriticalZeroCount T : ℝ) := by
    exact_mod_cast (zeta23_N0star_zero_eq_card_and_le_xiPosCriticalZeroCount T).2
  exact h1.trans h2

/-- **Universal Dyadic Window Off-Line Moment Transfer from `N₀*` (Without Simplicity).**
If `(p₀ − ε) N(T, 2T) ≤ N₀*(T, 2T)` eventually for every `ε > 0` (`0 < p₀ ≤ 1`), then for every
`R, η > 0`, eventually
`4π windowTail 0 (T + 1) (2T − 1) ≤ (log c_R − (1 + p₀) R + η) T`. -/
theorem eventually_dyadicWindowTail_le_selberg_upper_of_N0star {p₀ R η : ℝ}
    (hp₀0 : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hR : 0 < R) (hη : 0 < η)
    (hprop : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (p₀ - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Zeta23.N0star T (2 * T) : ℝ)) :
    ∀ᶠ T in atTop,
      4 * Real.pi * RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤
        (Real.log (ZetaGateProductAFE.selbergBlockConstUpper R) - (1 + p₀) * R + η) * T := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ZetaGateProductAFE.selbergBlockConstUpper R := ⟨_, rfl⟩
  rw [← hcdef]
  have hc1 : 1 ≤ c := hcdef ▸ ZetaGateProductAFE.one_le_selbergBlockConstUpper hR
  have hc0 : 0 < c := by linarith
  have hlogc : 2 * R ≤ Real.log c := hcdef ▸ RHTower.two_mul_le_log_selbergBlockConstUpper hR
  obtain ⟨η', hη'⟩ : ∃ η' : ℝ, η' = η / 2 := ⟨_, rfl⟩
  have hη'0 : 0 < η' := by rw [hη']; positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (η / (4 * R)) p₀ := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; exact lt_min (by positivity) hp₀0
  have hεp : ε ≤ p₀ := by rw [hεdef]; exact min_le_right _ _
  have hεR : ε * R ≤ η / 4 := by
    have h1 : ε ≤ η / (4 * R) := by rw [hεdef]; exact min_le_left _ _
    calc ε * R ≤ η / (4 * R) * R := mul_le_mul_of_nonneg_right h1 hR.le
      _ = η / 4 := by field_simp
  obtain ⟨TZ, hZ⟩ := hprop ε hε0
  obtain ⟨Cc, hCc, Tc, hTc, hceil⟩ := RHTower.exists_xiZeroCount_window_le
  obtain ⟨C, K, hC, hK, hwide⟩ := RHTower.exists_zetaWideMoment_le_of_mollified_meanSquare
  obtain ⟨CR, hCR, TR, hTR, hrvm⟩ := RHTower.exists_xiPosZeroCount_window_bounds
  have hεc : 0 < c * (η' / 8) := mul_pos hc0 (div_pos hη'0 (by norm_num))
  obtain ⟨U₀, hU₀⟩ := Filter.eventually_atTop.mp
    (ZetaGateProductAFE.eventually_window_meanSquare_selberg_upper hR hεc)
  rw [← hcdef] at hU₀
  have hbb1 : 1 ≤ RHTower.routeKRVMBase := by
    rw [RHTower.routeKRVMBase]
    have h1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    nlinarith
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ,
      L₀ = 8 * R + 16 * R * (Real.log 2 + Real.log RHTower.routeKRVMBase) / η' := ⟨_, rfl⟩
  have hp1_nn : 0 ≤ 16 * R * (Real.log 2 + Real.log RHTower.routeKRVMBase) / η' := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have : 0 ≤ Real.log RHTower.routeKRVMBase := Real.log_nonneg hbb1
    exact div_nonneg (by positivity) hη'0.le
  have hL₀a : 8 * R ≤ L₀ := by linarith
  have hL₀b : 16 * R * (Real.log 2 + Real.log RHTower.routeKRVMBase) / η' ≤ L₀ := by linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 12 * Real.pi * R * CR + 2 * C + 14 * K * Real.log 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 4 * Real.pi * R * (8 * (1 / (2 * Real.pi) + 2 * Cc)) := ⟨_, rfl⟩
  have hη64 : 0 < η' / 64 := div_pos hη'0 (by norm_num)
  filter_upwards [eventually_ge_atTop (max (max U₀ (TR + 1)) (max ((2 : ℝ) ^ 50) (Real.exp L₀))),
    eventually_ge_atTop (max (TZ + 1) (Tc + 1)),
    RHTower.eventually_const_mul_rpow_neg_le 8 ((1 : ℝ) / 100) (by norm_num)
      (show 0 < η' / 8 from div_pos hη'0 (by norm_num)),
    RHTower.eventually_const_mul_rpow_neg_mul_log_pow_le A ((24 : ℝ) / 25) (by norm_num) 0 hη64,
    RHTower.eventually_const_mul_rpow_neg_mul_log_pow_le (8 * K) ((24 : ℝ) / 25) (by norm_num) 1 hη64,
    RHTower.eventually_const_mul_rpow_neg_mul_log_pow_le B ((24 : ℝ) / 25) (by norm_num) 0 hη64]
    with T hTbig hTbig2 hratio hadd1 hadd2 hadd3
  have hTU₀ : U₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hTbig
  have hTTR : TR + 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTbig
  have hT50 : (2 : ℝ) ^ 50 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hTbig
  have hTL : Real.exp L₀ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hTbig
  have hTZ : TZ ≤ T := by linarith [le_max_left (TZ + 1) (Tc + 1)]
  have hTc' : Tc ≤ T := by linarith [le_max_right (TZ + 1) (Tc + 1)]
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT50
  have hT2 : 2 ≤ T := le_trans (by norm_num) hT50
  have hlogTL : L₀ ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos L₀) hTL
    rwa [Real.log_exp] at this
  have hT2425 : (4 : ℝ) ≤ T ^ ((24 : ℝ) / 25) :=
    RHTower.four_le_rpow_twentyfour_div_twentyfive (le_trans (by norm_num) hT50)
  have hH1 : T ^ ((24 : ℝ) / 25) ≤ T := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ T)
      (show (24 : ℝ) / 25 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have hH4 : 4 ≤ T := le_trans hT2425 hH1
  have hpos2425 : 0 < T ^ ((24 : ℝ) / 25) := Real.rpow_pos_of_pos hT0 _
  have hA' : A ≤ η' / 64 * T ^ ((24 : ℝ) / 25) := by
    have h := hadd1
    rw [pow_zero, mul_one, Real.rpow_neg hT0.le, ← div_eq_mul_inv, div_le_iff₀ hpos2425] at h
    exact h
  have hK' : 8 * K * Real.log T ≤ η' / 64 * T ^ ((24 : ℝ) / 25) := by
    have h := hadd2
    rw [pow_one, Real.rpow_neg hT0.le, ← mul_assoc, mul_comm (8 * K), mul_assoc,
      ← div_eq_inv_mul, div_le_iff₀ hpos2425] at h
    linarith only [h]
  have hB' : B ≤ η' / 64 * T ^ ((24 : ℝ) / 25) := by
    have h := hadd3
    rw [pow_zero, mul_one, Real.rpow_neg hT0.le, ← div_eq_mul_inv, div_le_iff₀ hpos2425] at h
    exact h
  have hms := hU₀ (T + T) (by linarith)
  obtain ⟨T₁, T₂, hT₁lo, hT₁hi, hT₂lo, hT₂hi, hlit₀⟩ :=
    RHTower.exists_window_littlewood_upper hR hwide hT50 hH4 le_rfl (le_trans hL₀a hlogTL) hms
  obtain ⟨hNlo, -⟩ := hrvm T₁ T₂ (by linarith) (by linarith)
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = p₀ - ε := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by rw [hpdef]; linarith only [hεp]
  have hp1 : p ≤ 1 := by rw [hpdef]; linarith only [hε0, hp₀1]
  have hT₁₂ : T₁ ≤ T₂ := by linarith
  have hsub :
      RHTower.stripFinsetPos T₂ \ RHTower.stripFinsetPos T₁ ⊆
        RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T := by
    intro z hz
    rw [Finset.mem_sdiff] at hz ⊢
    exact ⟨RHTower.stripFinsetPos_mono (by linarith) hz.1,
      fun h => hz.2 (RHTower.stripFinsetPos_mono hT₁lo.le h)⟩
  have hRmono : ∑ z ∈ RHTower.stripFinsetPos T₂ \ RHTower.stripFinsetPos T₁,
        ((analyticOrderAt RHTower.xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0)
      ≤ ∑ z ∈ RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T,
        ((analyticOrderAt RHTower.xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ =>
      mul_nonneg (Nat.cast_nonneg _) (by split_ifs <;> norm_num)
  have hrefl := two_mul_sum_right_add_N0star_le (T₁ := T) (T₂ := 2 * T) hT0.le
  have hZT := hZ T hTZ
  rw [RHTower.zeta23_Ncount_window_eq hT0.le,
    RHTower.window_mult_sum_eq (T₁ := T) (T₂ := 2 * T) (by linarith)] at hrefl hZT
  have hcast : ∀ t : ℝ, 0 ≤ t →
      ((RHTower.xiPosZeroCount t : ℕ) : ℝ) = ((RHTower.xiZeroCount t : ℤ) : ℝ) := by
    intro t ht
    have := RHTower.xiPosZeroCount_eq_xiZeroCount ht
    exact_mod_cast this
  have hE₁ : (RHTower.xiPosZeroCount T₁ : ℝ) - RHTower.xiPosZeroCount T
      ≤ 1 / (2 * Real.pi) * Real.log (T + 1) + 2 * Cc * Real.log (T + 1) := by
    have h := hceil T hTc' 1 (by norm_num)
    rw [← hcast (T + 1) (by linarith), ← hcast T hT0.le] at h
    have hmono : (RHTower.xiPosZeroCount T₁ : ℝ) ≤ RHTower.xiPosZeroCount (T + 1) := by
      exact_mod_cast Finset.sum_le_sum_of_subset (RHTower.stripFinsetPos_mono hT₁hi.le)
    linarith
  have hE₂ : (RHTower.xiPosZeroCount (2 * T) : ℝ) - RHTower.xiPosZeroCount T₂
      ≤ 1 / (2 * Real.pi) * Real.log (2 * T) + 2 * Cc * Real.log (2 * T) := by
    have h := hceil (2 * T - 1) (by linarith) 1 (by norm_num)
    rw [show 2 * T - 1 + 1 = 2 * T by ring, ← hcast (2 * T) (by linarith),
      ← hcast (2 * T - 1) (by linarith)] at h
    have hmono : (RHTower.xiPosZeroCount (2 * T - 1) : ℝ) ≤ RHTower.xiPosZeroCount T₂ := by
      exact_mod_cast Finset.sum_le_sum_of_subset (RHTower.stripFinsetPos_mono (by linarith))
    linarith
  have hlog1 : Real.log (T + 1) ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
  have hlog2T : Real.log (2 * T) ≤ 2 * Real.log T := by
    have h2T : 2 * T ≤ T ^ 2 := by
      have := mul_le_mul_of_nonneg_left hT2 hT0.le
      nlinarith only [this]
    have := Real.log_le_log (by linarith) h2T
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  obtain ⟨Ec, hEc⟩ : ∃ Ec : ℝ, Ec = (1 / (2 * Real.pi) + 2 * Cc) * (2 * Real.log (2 * T)) :=
    ⟨_, rfl⟩
  have hright : ∑ z ∈ RHTower.stripFinsetPos T₂ \ RHTower.stripFinsetPos T₁,
        ((analyticOrderAt RHTower.xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0)
      ≤ (1 - p) / 2 * ((RHTower.xiPosZeroCount T₂ : ℝ) - RHTower.xiPosZeroCount T₁) + Ec := by
    have hNw : (RHTower.xiPosZeroCount (2 * T) : ℝ) - RHTower.xiPosZeroCount T
        ≤ ((RHTower.xiPosZeroCount T₂ : ℝ) - RHTower.xiPosZeroCount T₁) + Ec := by
      rw [hEc]
      have hc4 : 0 ≤ 1 / (2 * Real.pi) + 2 * Cc := by positivity
      have h1 := mul_le_mul_of_nonneg_left hlog1 hc4
      linarith
    have hq : 0 ≤ (1 - p) / 2 := by linarith only [hp1]
    have hq1 : (1 - p) / 2 ≤ 1 := by linarith only [hp0]
    have hRdy : ∑ z ∈ RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T,
          ((analyticOrderAt RHTower.xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0)
        ≤ (1 - p) / 2 * ((RHTower.xiPosZeroCount (2 * T) : ℝ) - RHTower.xiPosZeroCount T) := by
      rw [hpdef]; linarith only [hrefl, hZT]
    have h3 := mul_le_mul_of_nonneg_left hNw hq
    have hEc0 : 0 ≤ Ec := by
      rw [hEc]
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith only [hT2])
      positivity
    have h4 : (1 - p) / 2 * Ec ≤ Ec := by
      have := mul_le_mul_of_nonneg_right hq1 hEc0
      linarith only [this]
    linarith
  have hX : 4 * Real.pi * (R / Real.log T₂ * Ec) ≤ η' / 64 * T ^ ((24 : ℝ) / 25) := by
    have hlogT₂ : Real.log T ≤ Real.log T₂ :=
      Real.log_le_log hT0 (by linarith only [hT₁lo, hT₁₂])
    have hlogTpos : 0 < Real.log T := Real.log_pos (by linarith only [hT2])
    have h1 : R / Real.log T₂ * Ec ≤ R * (8 * (1 / (2 * Real.pi) + 2 * Cc)) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith only [hlogT₂, hlogTpos])]
      rw [hEc]
      have hc4 : 0 ≤ 1 / (2 * Real.pi) + 2 * Cc := by positivity
      have hl : 2 * Real.log (2 * T) ≤ 8 * Real.log T₂ := by
        linarith only [hlog2T, hlogT₂, hlogTpos]
      have h5 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl hc4) hR.le
      calc R * ((1 / (2 * Real.pi) + 2 * Cc) * (2 * Real.log (2 * T)))
          ≤ R * ((1 / (2 * Real.pi) + 2 * Cc) * (8 * Real.log T₂)) := h5
        _ = R * (8 * (1 / (2 * Real.pi) + 2 * Cc)) * Real.log T₂ := by ring
    calc 4 * Real.pi * (R / Real.log T₂ * Ec) ≤ 4 * Real.pi * (R * (8 * (1 / (2 * Real.pi) +
          2 * Cc))) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = B := by rw [hB]; ring
      _ ≤ η' / 64 * T ^ ((24 : ℝ) / 25) := hB'
  have hN2 := ZetaGateProductAFE.two_le_mollUpper (show (2 : ℝ) ^ 50 ≤ T + T by linarith)
  have h := RHTower.window_moment_of_littlewood_dyadic hp0 hp1 hR hη'0 hc0 hlogc hK hCR hC hbb1
    hL₀a hL₀b hA hT0 hlogTL hratio hA' hK' hX hT2425 hH1 le_rfl hT₁lo hT₁hi hT₂lo hT₂hi
    (by omega) (ZetaGateProductAFE.mollUpper_le (by linarith only [hT0])) hlit₀ hNlo hright
  rw [show T + T - 1 = 2 * T - 1 by ring] at h
  refine h.trans ?_
  have : Real.log c - (1 + p) * R + η' ≤ Real.log c - (1 + p₀) * R + η := by
    rw [hpdef, hη']
    have e : (1 + (p₀ - ε)) * R = (1 + p₀) * R - ε * R := by ring
    linarith only [e, hεR, hη]
  exact mul_le_mul_of_nonneg_right this hT0.le

/-- **Universal Cumulative Off-Line Moment Transfer from `N₀*` (Without Simplicity).**
If `(p − ε) xiPosZeroCount T ≤ xiPosCriticalZeroCount T` eventually for every `ε > 0`
(`0 < p ≤ 7/8`), then for any upper-range gate `ZetaMollifiedMeanSquareGateFrom α R c₁`,
`4π offLineMoment V ≤ (log c₁ − (1 + p) R + η) V` eventually. -/
theorem eventually_offLineMoment_le_of_zetaGateFrom_N0star {α R c₁ η p : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (hR : 0 < R) (hc₁ : 1 ≤ c₁) (hη : 0 < η) (hp0 : 0 < p) (hp1 : p ≤ 7 / 8)
    (hprop : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (p - ε) * (RHTower.xiPosZeroCount T : ℝ) ≤ (RHTower.xiPosCriticalZeroCount T : ℝ))
    (hg₁ : RHTower.ZetaMollifiedMeanSquareGateFrom α R c₁) :
    ∀ᶠ V in atTop,
      4 * Real.pi * RHTower.offLineMoment V ≤ (Real.log c₁ - (1 + p) * R + η) * V := by
  classical
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨C, K, hC, hK, hceil⟩ :=
    RHTower.exists_zetaOffLineFirstMoment_add_lineCount_le_of_mollified_meanSquare
  obtain ⟨ε₀, hε₀0, hε₀p, hε₀R⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ p ∧ ε₀ * R ≤ η / 16 := by
    refine ⟨min p (η / (16 * R)), lt_min hp0 (by positivity), min_le_left _ _, ?_⟩
    have h1 : min p (η / (16 * R)) ≤ η / (16 * R) := min_le_right _ _
    have h2 : η / (16 * R) * R = η / 16 := by field_simp
    calc min p (η / (16 * R)) * R ≤ η / (16 * R) * R :=
          mul_le_mul_of_nonneg_right h1 hR.le
      _ = η / 16 := h2
  have hκ₀ : (0 : ℝ) ≤ p - ε₀ := by linarith
  have hε0 : 0 < c₁ * (η / 8) := by positivity
  have hlogε := RHTower.log_gate_slack_le hc₁ hη
  have hε'0 : 0 < η / (60 * Real.pi * R) := by positivity
  have hε'bound := RHTower.proportion_eps'_bound (ε₀ := ε₀) hR hη hε₀0 hp1
  obtain ⟨T₀, _, hrvm⟩ := RHTower.exists_xiZeroCount_close (η / (60 * Real.pi * R)) hε'0
  obtain ⟨U₁, hU₁⟩ := hprop ε₀ hε₀0
  have hev : ∀ᶠ U : ℝ in atTop,
      4 * Real.pi * RHTower.offLineMoment (U - 1) ≤ (Real.log c₁ - (1 + p) * R + η) * (U - 1) := by
    filter_upwards [hg₁ (c₁ * (η / 8)) hε0, eventually_ge_atTop (max (T₀ + 1) (max (U₁ + 1) 23)),
      RHTower.eventually_mul_log_le_quarter hK hη,
      RHTower.eventually_const_le_quarter_sub_one (|Real.log c₁ - (1 + p) * R + η / 4| + 2 * C)
        (show 0 < η / 2 by positivity),
      RHTower.eventually_count_upper_le hα0 hα1 (2 * Real.pi + 4 * Real.pi * R / Real.log 20)
        (show 0 < η / 8 by positivity)]
      with U hU hUbig hlogU hDU₀ hcountU
    obtain ⟨T₁, T₂, σ₀, Mb, b, N, hT₁, hT₂, hN, hb1, hbn, hbreal, hMb1, hmass, hlogMb,
      hσ₀a, hσ₀b, hσ₀R, hG1, hG2, hP1, hP2, hMsq⟩ := hU
    have hU23 : 23 ≤ U := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hUbig
    have hUT₀ : T₀ + 1 ≤ U := le_trans (le_max_left _ _) hUbig
    have hUU₁ : U₁ + 1 ≤ U := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hUbig
    have hT₂big : U - 1 < T₂ := hT₂.1
    have hT₂U : T₂ ≤ U := hT₂.2
    have hT₁20 : 20 ≤ T₁ := hT₁.1
    have hT₁21 : T₁ ≤ U ^ α + 1 := hT₁.2
    have hUα := hcountU.2
    have hT12 : T₁ < T₂ := by linarith [hUα.2.1]
    have hT₂T₀ : T₀ ≤ T₂ := by linarith
    have hT₂U₁ : U₁ ≤ T₂ := by linarith
    have hlogT₂ : 0 < Real.log T₂ := Real.log_pos (by linarith)
    obtain ⟨Z, hZ⟩ := RHTower.exists_zetaRectangleZeros_finset hT₁20 hT12
    have hc := hceil b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂
      ((c₁ + c₁ * (η / 8)) * (T₂ - T₁)) hσ₀a hσ₀b hT₁20 hT12 hG1 hG2 hP1 hP2 hMsq Z hZ
    have hlogMsq : Real.log ((c₁ + c₁ * (η / 8)) * (T₂ - T₁) / (T₂ - T₁))
        = Real.log (c₁ + c₁ * (η / 8)) := by
      rw [mul_div_assoc, div_self (by linarith : T₂ - T₁ ≠ 0), mul_one]
    rw [hlogMsq] at hc
    have hbridge1 := RHTower.rightHalfOrderSum_sub_le_zetaZeroSum hT12.le Z hZ
    have hbridge2 := RHTower.offLineMoment_le_add_zetaZeroMoment hT12.le Z hZ
    have hrefl₂ : (2 * RHTower.rightHalfOrderSum T₂ : ℝ)
        = (RHTower.xiPosZeroCount T₂ : ℝ) + (RHTower.xiPosCriticalZeroCount T₂ : ℝ) := by
      exact_mod_cast RHTower.two_mul_rightHalfOrderSum T₂
    have hR₁nat : RHTower.rightHalfOrderSum T₁ ≤ RHTower.xiPosZeroCount T₁ :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hR₁ : (RHTower.rightHalfOrderSum T₁ : ℝ) ≤ (RHTower.xiPosZeroCount T₁ : ℝ) := by
      exact_mod_cast hR₁nat
    have hprop₂ : (p - ε₀) * (RHTower.xiPosZeroCount T₂ : ℝ) ≤
        (RHTower.xiPosCriticalZeroCount T₂ : ℝ) := hU₁ T₂ hT₂U₁
    have hS : (1 + (p - ε₀) + 0) * (RHTower.xiPosZeroCount T₂ : ℝ) / 2 -
        (RHTower.xiPosZeroCount T₁ : ℝ)
        ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
      linarith only [hbridge1, hrefl₂, hR₁, hprop₂]
    have hN₂ : (1 / (2 * Real.pi) - η / (60 * Real.pi * R)) * (T₂ * Real.log T₂)
        ≤ (RHTower.xiPosZeroCount T₂ : ℝ) := by
      have h := hrvm T₂ hT₂T₀
      have hcast : ((RHTower.xiZeroCount T₂ : ℤ) : ℝ) = (RHTower.xiPosZeroCount T₂ : ℝ) := by
        rw [← RHTower.xiPosZeroCount_eq_xiZeroCount (by linarith)]
        simp
      rw [hcast] at h
      have h1 := (abs_le.mp h).1
      have hid : (1 / (2 * Real.pi) - η / (60 * Real.pi * R)) * (T₂ * Real.log T₂)
          = 1 / (2 * Real.pi) * (T₂ * Real.log T₂)
            - η / (60 * Real.pi * R) * (T₂ * Real.log T₂) := by
        ring
      linarith only [h1, hid]
    have harith := RHTower.offLineMoment_window_arith hR hlogT₂ hσ₀R (by linarith) hT12.le hK.le
      hlogMb (Real.log_nonneg (by linarith)) hκ₀ (le_refl (0 : ℝ)) hε'0.le (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) hc hS hbridge2 hN₂
    have hmono := RHTower.offLineMoment_mono (le_of_lt hT₂big)
    have hbr : Real.log (c₁ + c₁ * (η / 8))
        - R * (1 + (p - ε₀) + 0) * (1 - 2 * Real.pi * (η / (60 * Real.pi * R)))
        ≤ Real.log c₁ - (1 + p) * R + η / 4 := by
      have hid : R * (1 + (p - ε₀) + 0) * (1 - 2 * Real.pi * (η / (60 * Real.pi * R)))
          = (1 + p) * R - ε₀ * R
            - 2 * Real.pi * (η / (60 * Real.pi * R)) * R * (1 + (p - ε₀) + 0) := by ring
      linarith only [hlogε, hε'bound, hid, hε₀R]
    have hN₁nat : RHTower.xiPosZeroCount T₁ ≤ RHTower.xiPosZeroCount (U ^ α + 1) :=
      Finset.sum_le_sum_of_subset (RHTower.stripFinsetPos_mono hT₁21)
    have hN₁ : (RHTower.xiPosZeroCount T₁ : ℝ) ≤ (RHTower.xiPosZeroCount (U ^ α + 1) : ℝ) := by
      exact_mod_cast hN₁nat
    have hM₁ : 4 * Real.pi * RHTower.offLineMoment T₁
        ≤ 4 * Real.pi * (1 / 2 * (RHTower.xiPosZeroCount (U ^ α + 1) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (RHTower.offLineMoment_le_half_xiPosZeroCount T₁).trans (by linarith only [hN₁])
    have hlog20 : Real.log 20 ≤ Real.log T₂ := Real.log_le_log (by norm_num) (by linarith)
    have hlog20pos : 0 < Real.log 20 := Real.log_pos (by norm_num)
    have hlast : 4 * Real.pi * R * (RHTower.xiPosZeroCount T₁ : ℝ) / Real.log T₂
        ≤ 4 * Real.pi * R * (RHTower.xiPosZeroCount (U ^ α + 1) : ℝ) / Real.log 20 := by
      apply div_le_div₀ (by positivity) _ hlog20pos hlog20
      exact mul_le_mul_of_nonneg_left hN₁ (by positivity)
    have hlogT₂U : Real.log T₂ ≤ Real.log U := Real.log_le_log (by linarith) hT₂U
    have hKlog : 12 * K * Real.log T₂ ≤ η / 4 * U :=
      le_trans (mul_le_mul_of_nonneg_left hlogT₂U (by positivity)) hlogU
    have hmono' : 4 * Real.pi * RHTower.offLineMoment (U - 1) ≤
        4 * Real.pi * RHTower.offLineMoment T₂ :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    have hfinal := RHTower.twoThirds_tail_arith (by linarith) hT₂big hT₂U harith hbr hM₁ hlast hKlog
      hmono'
    have hηU : η / 4 * U = η / 4 * (U - 1) + η / 4 := by ring
    have hη1 : η / 4 ≤ η / 4 * (U - 1) := by
      have h0 : 0 ≤ η / 4 * (U - 2) := mul_nonneg (by positivity) (by linarith only [hU23])
      have hid : η / 4 * (U - 1) = η / 4 + η / 4 * (U - 2) := by ring
      linarith only [h0, hid]
    have hBη : (Real.log c₁ - (1 + p) * R + η) * (U - 1)
        = (U - 1) * (Real.log c₁ - (1 + p) * R + η / 4) + 3 * (η / 4 * (U - 1)) := by
      ring
    have hDU : |Real.log c₁ - (1 + p) * R + η / 4| + 2 * C
        + 4 * Real.pi * (1 / 2 * (RHTower.xiPosZeroCount (U ^ α + 1) : ℝ))
        + 4 * Real.pi * R * (RHTower.xiPosZeroCount (U ^ α + 1) : ℝ) / Real.log 20 ≤
        η / 4 * (U - 1) := by
      have h1 := hcountU.1
      have hid : 4 * Real.pi * (1 / 2 * (RHTower.xiPosZeroCount (U ^ α + 1) : ℝ))
          + 4 * Real.pi * R * (RHTower.xiPosZeroCount (U ^ α + 1) : ℝ) / Real.log 20
          = (2 * Real.pi + 4 * Real.pi * R / Real.log 20) *
            (RHTower.xiPosZeroCount (U ^ α + 1) : ℝ) := by
        ring
      have hηsplit : η / 2 / 4 * (U - 1) + η / 8 * (U - 1) = η / 4 * (U - 1) := by ring
      linarith only [hDU₀, h1, hid, hηsplit]
    rw [hBη]
    linarith only [hfinal, hDU, hηU, hη1]
  have hshift : Tendsto (fun V : ℝ => V + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id
  simpa using hshift.eventually hev

/-- **Unconditional Montgomery–Taylor Upgrade of the Cumulative Off-Line Moment (`66/1000`).**
Using `HD(1) ≥ 1681/2500` (`RHTower.lamzouri_montgomeryTaylor_simpleCritical_epsilon`), the
cumulative off-line moment `RHTower.offLineMoment V` satisfies
`4π offLineMoment V ≤ (log c_R − (1 + HD(1)) R + η) V` for every `R, η > 0`, and at `R = 3/2`
improves unconditionally from `(67/1000) V` to `(66/1000) V`. -/
theorem eventually_offLineMoment_le_sixtySix_thousandths :
    (∀ {R η : ℝ}, 0 < R → 0 < η → ∀ᶠ V in atTop,
      4 * Real.pi * RHTower.offLineMoment V ≤
        (Real.log (ZetaGateProductAFE.selbergBlockConstUpper R) -
          (1 + Zeta23.ThmD.HD 1) * R + η) * V) ∧
    (∀ᶠ V in atTop, RHTower.offLineMoment V ≤ 66 / 1000 * V) := by
  have hHD_pos : 0 < Zeta23.ThmD.HD 1 := lt_of_lt_of_le (by norm_num) RHTower.HD_one_ge
  have hHD_le78 : Zeta23.ThmD.HD 1 ≤ 7 / 8 := le_trans HD_one_lt_three_quarters.le (by norm_num)
  have hgen : ∀ {R η : ℝ}, 0 < R → 0 < η → ∀ᶠ V in atTop,
      4 * Real.pi * RHTower.offLineMoment V ≤
        (Real.log (ZetaGateProductAFE.selbergBlockConstUpper R) -
          (1 + Zeta23.ThmD.HD 1) * R + η) * V :=
    fun hR hη => RHTower.eventually_offLineMoment_le_of_zetaGateFrom_proportion
      (α := (49 : ℝ) / 50) (by norm_num) (by norm_num) hR
      (ZetaGateProductAFE.one_le_selbergBlockConstUpper hR) hη hHD_pos hHD_le78
      RHTower.lamzouri_montgomeryTaylor_simpleCritical_epsilon
      (ZetaGateProductAFE.zetaMollifiedMeanSquareGateFrom_selberg_upper hR)
  refine ⟨hgen, ?_⟩
  filter_upwards [hgen (R := 3 / 2) (η := 1 / 1000) (by norm_num) (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with V hV hV0
  have hc := RHTower.log_selbergBlockConstUpper_three_halves_le_montgomeryTaylor
  have hHD := RHTower.HD_one_ge
  have hπ : 0 < 4 * Real.pi := by positivity
  have hcoef : Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 2)) -
      (1 + Zeta23.ThmD.HD 1) * (3 / 2) + 1 / 1000 ≤ 4 * Real.pi * (66 / 1000) := by linarith
  have h1 : 4 * Real.pi * RHTower.offLineMoment V ≤ 4 * Real.pi * (66 / 1000 * V) := by
    calc 4 * Real.pi * RHTower.offLineMoment V
        ≤ (Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 2)) -
            (1 + Zeta23.ThmD.HD 1) * (3 / 2) + 1 / 1000) * V := hV
      _ ≤ (4 * Real.pi * (66 / 1000)) * V := mul_le_mul_of_nonneg_right hcoef hV0
      _ = 4 * Real.pi * (66 / 1000 * V) := by ring
  exact le_of_mul_le_mul_left h1 hπ

/-! ## 2. Route I (Zero-Side Spectral Slack): Exact `HD(1)` Thresholds and `57/1000` Moment Upgrade -/

/-- **General Grid-Dimension Refutation of Sub-Threshold Spectral Slack (`λ < q`).**
For any target proportion `q : ℝ` and any sub-threshold bandwidth `λ ∈ (0, 1)` with `λ < q`,
there exists `T₀` such that for all `T ≥ T₀`,
`zeroSideSlack(λ, T) < (q − H(λ)) N(T, 2T)`. -/
theorem not_zeroSideSlack_of_lt_target {lam q : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (hq : lam < q) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      RHTower.zeroSideSlack Zeta23.zetaZeroConfig (Zeta23.paramsOf Zeta23.stdProfile lam) T <
        (q - Zeta23.Hfun lam) * (Zeta23.Ncount T (2 * T) : ℝ) := by
  have hε : 0 < (q - lam) / 2 := by linarith
  obtain ⟨T₁, hT₁⟩ := zeroSideSlack_eventually_le_lam_sub_Hfun h0 h1 hε
  have hNtop := Zeta23.Assembly.tendsto_N_atTop Zeta23.zetaZeroConfig Zeta23.riemannVonMangoldt_zeta
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp (hNtop.eventually_gt_atTop (0 : ℝ))
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have hslack := (hT₁ T ((le_max_left _ _).trans hT)).2.2
  have hNpos : 0 < (Zeta23.Ncount T (2 * T) : ℝ) := by
    have := hT₂ T ((le_max_right _ _).trans hT)
    simpa [Zeta23.zetaZeroConfig] using this
  have hgap : (lam - Zeta23.Hfun lam + (q - lam) / 2) * (Zeta23.Ncount T (2 * T) : ℝ) <
      (q - Zeta23.Hfun lam) * (Zeta23.Ncount T (2 * T) : ℝ) := by
    nlinarith
  linarith

/-- `C − (617/750)·S ≥ 1/500` for the two rational Taylor sums at `s² = 1/2`. -/
theorem taylor_sums_upper_gap :
    (1 / 500 : ℝ) ≤
      ∑ j ∈ Finset.range 10, (-1 : ℝ) ^ j * (1 / 2) ^ j / ((2 * j).factorial : ℝ) -
        617 / 750 * ∑ j ∈ Finset.range 10, (-1 : ℝ) ^ j * (1 / 2) ^ j /
          ((2 * j + 1).factorial : ℝ) := by
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- `HD(1) < 254 / 375 = 0.67733…`. -/
theorem HD_one_lt_twoHundredFiftyFour_div_threeHundredSeventyFive :
    Zeta23.ThmD.HD 1 < 254 / 375 := by
  rw [Zeta23.ThmD.HD_one]
  set s : ℝ := (Real.sqrt 2)⁻¹ with hs
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < s := inv_pos.mpr hsqrt0
  have hs2 : s ^ 2 = 1 / 2 := by rw [hs, inv_pow, hsq, one_div]
  have hsqrt_le : Real.sqrt 2 ≤ 71 / 50 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hs7 : 7 / 10 ≤ s := by
    rw [hs, le_inv_comm₀ (by norm_num) hsqrt0]
    linarith
  have hs1 : s < 1 := by nlinarith
  have hsabs : |s| ≤ 10 := by rw [abs_of_pos hs0]; linarith
  set C : ℝ := ∑ j ∈ Finset.range 10, (-1 : ℝ) ^ j * (1 / 2) ^ j / ((2 * j).factorial : ℝ) with hC
  set S : ℝ := ∑ j ∈ Finset.range 10, (-1 : ℝ) ^ j * (1 / 2) ^ j
    / ((2 * j + 1).factorial : ℝ) with hS
  set r : ℝ := |s| ^ 20 / (Nat.factorial 20 : ℝ) * 2 with hr
  have hr_eq : r = (1 / 2) ^ 10 / (Nat.factorial 20 : ℝ) * 2 := by
    rw [hr, abs_of_pos hs0, show (20 : ℕ) = 2 * 10 by norm_num, pow_mul, hs2]
  have hr_small : r ≤ 1 / 10 ^ 20 := by
    rw [hr_eq]
    norm_num [Nat.factorial]
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hcos := Encl.ge_of_holds (encl_cos s hsabs)
  have hsin := Encl.le_of_holds (encl_sin s hsabs)
  simp only at hcos hsin
  rw [RHTower.cosTaylor_ten_of_sq hs2, ← hC, ← hr] at hcos
  rw [RHTower.sinTaylor_ten_of_sq hs2, ← hS, ← hr] at hsin
  have hgap := taylor_sums_upper_gap
  rw [← hC, ← hS] at hgap
  have hsinpos : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0 (by linarith [Real.pi_gt_three])
  clear_value r S C s
  have hr' : r ≤ 1 / 100000 := le_trans hr_small (by norm_num)
  have hD : 0 < C - 617 / 750 * S - r := by linarith
  have hkey : 617 / 750 * Real.sin s < s * Real.cos s := by
    have h1 : s * (C - r) ≤ s * Real.cos s := mul_le_mul_of_nonneg_left hcos hs0.le
    have h2 : 7 / 10 * (C - 617 / 750 * S - r) ≤ s * (C - 617 / 750 * S - r) :=
      mul_le_mul_of_nonneg_right hs7 hD.le
    have e1 : s * (C - r) = s * C - s * r := by ring
    have e2 : s * (C - 617 / 750 * S - r) = s * C - 617 / 750 * (s * S) - s * r := by ring
    have h3 : 617 / 750 * Real.sin s ≤ 617 / 750 * (s * S + r) :=
      mul_le_mul_of_nonneg_left hsin (by norm_num)
    linarith
  have hdiv : 617 / 750 < s * (Real.cos s / Real.sin s) := by
    rw [← mul_div_assoc, lt_div_iff₀ hsinpos]
    linarith
  linarith

/-- **Unconditional Refutation of the `HD(1)` Spectral-Slack Route for All `λ ∈ (0, HD(1))`.**
For every `0 < λ < HD(1)` (in particular for all `0 < λ ≤ 1681/2500`),
`zeroSideSlack(λ, T) < (HD(1) − H(λ)) N(T, 2T)` for all sufficiently large `T`, whereas for
`λ ∈ [254/375, 1)` the grid ceiling `(λ + ε) N(T, 2T)` lies strictly above `HD(1) N(T, 2T)`. -/
theorem not_HD_one_zeroSideSlack_of_lt_HD_one {lam : ℝ} (h0 : 0 < lam)
    (hHD : lam < Zeta23.ThmD.HD 1) :
    (∃ T₀ : ℝ, ∀ T ≥ T₀,
      RHTower.zeroSideSlack Zeta23.zetaZeroConfig (Zeta23.paramsOf Zeta23.stdProfile lam) T <
        (Zeta23.ThmD.HD 1 - Zeta23.Hfun lam) * (Zeta23.Ncount T (2 * T) : ℝ)) ∧
    Zeta23.ThmD.HD 1 < 254 / 375 := by
  have h1 : lam < 1 := lt_trans hHD (lt_trans HD_one_lt_three_quarters (by norm_num))
  exact ⟨not_zeroSideSlack_of_lt_target h0 h1 hHD,
    HD_one_lt_twoHundredFiftyFour_div_threeHundredSeventyFive⟩

/-- **Route I (`zeroSideSlack`) Upgrades Both Dyadic and Cumulative `N₀*` and Off-Line Moments to `57/1000`.**
If `λ ∈ (0, 1)` satisfies `zeroSideSlack(λ, T) ≥ (3/4 − H(λ)) N(T, 2T)` eventually (which requires
`λ ∈ [3/4, 1)` by `not_three_quarters_zeroSideSlack_of_lt_three_quarters`), then:
1. `(3/4 − ε) N(T, 2T) ≤ N₀*(T, 2T)` and `(3/4 − ε) N(0, T) ≤ N₀*(0, T)` for all large `T`;
2. `4π windowTail 0 (T + 1) (2T − 1) ≤ (log c_R − (7/4) R + η) T` and
   `windowTail 0 (T + 1) (2T − 1) ≤ (57/1000) T` eventually;
3. `offLineMoment V ≤ (57/1000) V` eventually. -/
theorem zeta_N0star_and_offLineMoment_of_spectralSlack {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hslack : ∀ᶠ T in atTop,
      (3 / 4 - Zeta23.Hfun lam) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        RHTower.zeroSideSlack Zeta23.zetaZeroConfig (Zeta23.paramsOf Zeta23.stdProfile lam) T) :
    (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 4 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Zeta23.N0star T (2 * T) : ℝ)) ∧
    (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 4 - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ (Zeta23.N0star 0 T : ℝ)) ∧
    (∀ {R η : ℝ}, 0 < R → 0 < η → ∀ᶠ T in atTop,
      4 * Real.pi * RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤
        (Real.log (ZetaGateProductAFE.selbergBlockConstUpper R) - 7 / 4 * R + η) * T) ∧
    (∀ᶠ T in atTop, RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤ 57 / 1000 * T) ∧
    (∀ᶠ V in atTop, RHTower.offLineMoment V ≤ 57 / 1000 * V) := by
  have hdy : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 4 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Zeta23.N0star T (2 * T) : ℝ) := by
    intro ε hε
    obtain ⟨T₁, hT₁⟩ := zeta_three_quarters_of_spectralSlack.2.2 h0 h1 ε hε
    obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp hslack
    exact ⟨max T₁ T₂, fun T hT =>
      hT₁ T ((le_max_left _ _).trans hT) (hT₂ T ((le_max_right _ _).trans hT))⟩
  obtain ⟨hcum, hcum_xi⟩ := cumulative_N0star_of_dyadic_N0star hdy
  have hgen : ∀ {R η : ℝ}, 0 < R → 0 < η → ∀ᶠ T in atTop,
      4 * Real.pi * RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤
        (Real.log (ZetaGateProductAFE.selbergBlockConstUpper R) - 7 / 4 * R + η) * T := by
    intro R η hR hη
    have := eventually_dyadicWindowTail_le_selberg_upper_of_N0star
      (p₀ := 3 / 4) (by norm_num) (by norm_num) hR hη hdy
    simpa [show (1 + 3 / 4 : ℝ) = 7 / 4 by norm_num] using this
  refine ⟨hdy, hcum, hgen, ?_, ?_⟩
  · filter_upwards [hgen (R := 3 / 2) (η := 1 / 1000) (by norm_num) (by norm_num),
      eventually_ge_atTop (0 : ℝ)] with T hT hT0
    have hc := log_selbergBlockConstUpper_three_halves_le_three_quarters
    have hπ : 0 < 4 * Real.pi := by positivity
    have h1' : 4 * Real.pi * RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤
        4 * Real.pi * (57 / 1000 * T) := by
      calc 4 * Real.pi * RHTower.windowTail 0 (T + 1) (2 * T - 1)
          ≤ (Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 2)) -
              (7 / 4) * (3 / 2) + 1 / 1000) * T := hT
        _ ≤ (4 * Real.pi * (57 / 1000)) * T := mul_le_mul_of_nonneg_right hc hT0
        _ = 4 * Real.pi * (57 / 1000 * T) := by ring
    exact le_of_mul_le_mul_left h1' hπ
  · have hcum_mom := eventually_offLineMoment_le_of_zetaGateFrom_N0star (α := (49 : ℝ) / 50)
      (R := 3 / 2) (η := 1 / 1000) (p := 3 / 4) (by norm_num) (by norm_num) (by norm_num)
      (ZetaGateProductAFE.one_le_selbergBlockConstUpper (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num) hcum_xi (ZetaGateProductAFE.zetaMollifiedMeanSquareGateFrom_selberg_upper
        (by norm_num))
    filter_upwards [hcum_mom, eventually_ge_atTop (0 : ℝ)] with V hV hV0
    have hc := log_selbergBlockConstUpper_three_halves_le_three_quarters
    have hπ : 0 < 4 * Real.pi := by positivity
    have h1' : 4 * Real.pi * RHTower.offLineMoment V ≤ 4 * Real.pi * (57 / 1000 * V) := by
      calc 4 * Real.pi * RHTower.offLineMoment V
          ≤ (Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 2)) -
              (1 + 3 / 4) * (3 / 2) + 1 / 1000) * V := hV
        _ = (Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 2)) -
              (7 / 4) * (3 / 2) + 1 / 1000) * V := by ring
        _ ≤ (4 * Real.pi * (57 / 1000)) * V := mul_le_mul_of_nonneg_right hc hV0
        _ = 4 * Real.pi * (57 / 1000 * V) := by ring
    exact le_of_mul_le_mul_left h1' hπ

/-- **General Target Displacement Law in the Hyperbolic Displaced-Pair Model at `κ = 4/3`.**
When `2p(1 + 2η)² = (1/3)N` (`N > 0, η ≥ 0`), the slack-augmented rank–trace functional equals
`N(1 − 1/(3(1 + 2η)))` identically, and reaches any target proportion `q` if and only if
`1 ≤ 3(1 − q)(1 + 2η)`. In particular, reaching `q = 254/375 > HD(1)` requires `η ≥ 2/121`
(`1 + 2η ≥ 125/121`), whereas reaching `q = 3/4` requires `η ≥ 1/6` (`1 + 2η ≥ 4/3`). -/
theorem hyperbolic_displacedPair_general_target_iff {N p η : ℝ} (hN : 0 < N) (hη : 0 ≤ η)
    (hfrob : 2 * p * (1 + 2 * η) ^ 2 = (1 / 3 : ℝ) * N) :
    (2 / 3 : ℝ) * N + 4 * p * η * (1 + 2 * η) = N * (1 - 1 / (3 * (1 + 2 * η))) ∧
    (∀ q : ℝ, q * N ≤ (2 / 3 : ℝ) * N + 4 * p * η * (1 + 2 * η) ↔
      1 ≤ 3 * (1 - q) * (1 + 2 * η)) ∧
    ((254 / 375 : ℝ) * N ≤ (2 / 3 : ℝ) * N + 4 * p * η * (1 + 2 * η) ↔ (2 / 121 : ℝ) ≤ η) ∧
    ((3 / 4 : ℝ) * N ≤ (2 / 3 : ℝ) * N + 4 * p * η * (1 + 2 * η) ↔ (1 / 6 : ℝ) ≤ η) := by
  have h12 : 0 < 1 + 2 * η := by linarith
  have h3 : 0 < 3 * (1 + 2 * η) := by positivity
  have hN_eq : N = 6 * p * (1 + 2 * η) ^ 2 := by linarith
  have hid : (2 / 3 : ℝ) * N + 4 * p * η * (1 + 2 * η) = N * (1 - 1 / (3 * (1 + 2 * η))) := by
    rw [hN_eq]; field_simp; ring
  have hgen : ∀ q : ℝ, q * N ≤ (2 / 3 : ℝ) * N + 4 * p * η * (1 + 2 * η) ↔
      1 ≤ 3 * (1 - q) * (1 + 2 * η) := by
    intro q
    rw [hid]
    have hdiff : N * (1 - 1 / (3 * (1 + 2 * η))) - q * N =
        N * (3 * (1 - q) * (1 + 2 * η) - 1) / (3 * (1 + 2 * η)) := by
      field_simp; ring
    constructor
    · intro hle
      have hnn : 0 ≤ N * (3 * (1 - q) * (1 + 2 * η) - 1) / (3 * (1 + 2 * η)) := by linarith
      have hnum : 0 ≤ N * (3 * (1 - q) * (1 + 2 * η) - 1) := by
        have hmul := mul_nonneg hnn h3.le
        rwa [div_mul_cancel₀ _ h3.ne'] at hmul
      nlinarith
    · intro h1
      have hnn : 0 ≤ N * (3 * (1 - q) * (1 + 2 * η) - 1) / (3 * (1 + 2 * η)) :=
        div_nonneg (mul_nonneg hN.le (by linarith)) h3.le
      linarith
  refine ⟨hid, hgen, ?_, ?_⟩
  · rw [hgen (254 / 375)]
    constructor <;> intro h <;> linarith
  · rw [hgen (3 / 4)]
    constructor <;> intro h <;> linarith

/-! ## 3. Route II (Smooth-Window Coalescent Localization at `λ = 4/3`) and the Five-Model Separation of `HD(1)` from `3/4` -/

/-- **The Smooth-Window Coalescent Surplus Hypothesis at Budget `β`.**
By `TransThresholdPairCorrelation.zeta_coalescent_certificate`, every non-coalescent channel at
bandwidth `λ = 4/3` is unconditionally `o(N(T, 2T))`. `CoalescentSurplusAtMost β` states that for
every `ε > 0`, there is a coalescent exponent `η > 0` and a smooth window profile `u` for which
both the smooth-window certificate and the coalescent bound `coalescentSurplus u η T ≤ (β + ε) N(T, 2T)`
hold eventually. -/
def CoalescentSurplusAtMost (β : ℝ) : Prop :=
  ∀ ε > 0, ∃ (η : ℝ) (u : ℝ → ℝ) (ε₁ : ℝ),
    0 < η ∧ WindowProfile ε₁ u ∧
    ∀ᶠ T in atTop,
      (29 / 36 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) - coalescentSurplus u η T ≤
        (Zeta23.N0star T (2 * T) : ℝ) ∧
      coalescentSurplus u η T ≤ (β + ε) * (Zeta23.Ncount T (2 * T) : ℝ)

/-- **Unconditional Reduction of `CoalescentSurplusAtMost β` to the Coalescent Band Alone.**
Because `zeta_coalescent_certificate` holds unconditionally for every `η > 0` and `ε > 0`, a
uniform bound `coalescentSurplus u η T ≤ (β + ε) N(T, 2T)` on smooth window profiles `u`
immediately implies `CoalescentSurplusAtMost β`. -/
theorem coalescentSurplusAtMost_of_profile_bound (β : ℝ)
    (hcoal : ∀ ε > 0, ∃ η > 0, ∀ (u : ℝ → ℝ) (ε₁ : ℝ), WindowProfile ε₁ u →
      ∀ᶠ T in atTop, coalescentSurplus u η T ≤ (β + ε) * (Zeta23.Ncount T (2 * T) : ℝ)) :
    CoalescentSurplusAtMost β := by
  intro ε hε
  obtain ⟨η, hη, hbound⟩ := hcoal ε hε
  obtain ⟨u, ε₁, hu, hcert⟩ := zeta_coalescent_certificate hη hε
  exact ⟨η, u, ε₁, hη, hu, hcert.and (hbound u ε₁ hu)⟩

/-- **Proportion and Off-Line Moment Transfer from `CoalescentSurplusAtMost β`.**
Under `CoalescentSurplusAtMost β`:
1. At least `(29/36 − β − ε) N(T, 2T)` zeros in `(T, 2T]` and `(29/36 − β − ε) N(0, T)` zeros in
   `(0, T]` lie on the critical line (`N₀*`);
2. Whenever `β ≤ 1/18` (`29/36 − β ≥ 3/4`), at least `(3/4 − ε)` of the zeros lie on the critical
   line both dyadically and cumulatively, and **both** `windowTail 0 (T + 1) (2T − 1) ≤ (57/1000) T`
   and `offLineMoment V ≤ (57/1000) V` hold eventually. -/
theorem zeta_N0star_and_offLineMoment_of_coalescentSurplus {β : ℝ}
    (hβ : CoalescentSurplusAtMost β) :
    (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (29 / 36 - β - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Zeta23.N0star T (2 * T) : ℝ)) ∧
    (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (29 / 36 - β - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ (Zeta23.N0star 0 T : ℝ)) ∧
    (β ≤ 1 / 18 →
      (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
        (3 / 4 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Zeta23.N0star T (2 * T) : ℝ)) ∧
      (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
        (3 / 4 - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ (Zeta23.N0star 0 T : ℝ)) ∧
      (∀ᶠ T in atTop, RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤ 57 / 1000 * T) ∧
      (∀ᶠ V in atTop, RHTower.offLineMoment V ≤ 57 / 1000 * V)) := by
  have hdy : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (29 / 36 - β - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Zeta23.N0star T (2 * T) : ℝ) := by
    intro ε hε
    obtain ⟨η, u, ε₁, _, _, hev⟩ := hβ (ε / 2) (by linarith)
    obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hev
    refine ⟨T₀, fun T hT => ?_⟩
    obtain ⟨h1, h2⟩ := hT₀ T hT
    linarith
  obtain ⟨hcum, _⟩ := cumulative_N0star_of_dyadic_N0star hdy
  refine ⟨hdy, hcum, fun h18 => ?_⟩
  have hdy34 : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 4 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Zeta23.N0star T (2 * T) : ℝ) := by
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := hdy ε hε
    refine ⟨T₀, fun T hT => ?_⟩
    have hN0 : 0 ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
    have hle : (3 / 4 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        (29 / 36 - β - ε) * (Zeta23.Ncount T (2 * T) : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hN0
    exact hle.trans (hT₀ T hT)
  obtain ⟨hcum34, hcum_xi34⟩ := cumulative_N0star_of_dyadic_N0star hdy34
  refine ⟨hdy34, hcum34, ?_, ?_⟩
  · have hgen := eventually_dyadicWindowTail_le_selberg_upper_of_N0star
      (p₀ := 3 / 4) (R := 3 / 2) (η := 1 / 1000) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hdy34
    filter_upwards [hgen, eventually_ge_atTop (0 : ℝ)] with T hT hT0
    have hc := log_selbergBlockConstUpper_three_halves_le_three_quarters
    have hπ : 0 < 4 * Real.pi := by positivity
    have h1' : 4 * Real.pi * RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤
        4 * Real.pi * (57 / 1000 * T) := by
      calc 4 * Real.pi * RHTower.windowTail 0 (T + 1) (2 * T - 1)
          ≤ (Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 2)) -
              (1 + 3 / 4) * (3 / 2) + 1 / 1000) * T := hT
        _ = (Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 2)) -
              (7 / 4) * (3 / 2) + 1 / 1000) * T := by ring
        _ ≤ (4 * Real.pi * (57 / 1000)) * T := mul_le_mul_of_nonneg_right hc hT0
        _ = 4 * Real.pi * (57 / 1000 * T) := by ring
    exact le_of_mul_le_mul_left h1' hπ
  · have hcum_mom := eventually_offLineMoment_le_of_zetaGateFrom_N0star (α := (49 : ℝ) / 50)
      (R := 3 / 2) (η := 1 / 1000) (p := 3 / 4) (by norm_num) (by norm_num) (by norm_num)
      (ZetaGateProductAFE.one_le_selbergBlockConstUpper (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num) hcum_xi34 (ZetaGateProductAFE.zetaMollifiedMeanSquareGateFrom_selberg_upper
        (by norm_num))
    filter_upwards [hcum_mom, eventually_ge_atTop (0 : ℝ)] with V hV hV0
    have hc := log_selbergBlockConstUpper_three_halves_le_three_quarters
    have hπ : 0 < 4 * Real.pi := by positivity
    have h1' : 4 * Real.pi * RHTower.offLineMoment V ≤ 4 * Real.pi * (57 / 1000 * V) := by
      calc 4 * Real.pi * RHTower.offLineMoment V
          ≤ (Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 2)) -
              (1 + 3 / 4) * (3 / 2) + 1 / 1000) * V := hV
        _ = (Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 2)) -
              (7 / 4) * (3 / 2) + 1 / 1000) * V := by ring
        _ ≤ (4 * Real.pi * (57 / 1000)) * V := mul_le_mul_of_nonneg_right hc hV0
        _ = 4 * Real.pi * (57 / 1000 * V) := by ring
    exact le_of_mul_le_mul_left h1' hπ

/-- **Exact Coalescent Surplus Budget Thresholds for `2/3`, `HD(1)`, `3/4`, and GUE (`13/16`).**
In the smooth-window certificate `29/36 − β` at bandwidth `λ = 4/3`:
1. `2/3 < 29/36 − β ↔ β < 5/36` (`5/36 = (5/2) · (1/18)`);
2. `254/375 ≤ 29/36 − β ↔ β ≤ 577/4500`, and any `β ≤ 577/4500` strictly beats `HD(1)`
   (`HD(1) < 254/375 ≤ 29/36 − β`);
3. `3/4 ≤ 29/36 − β ↔ β ≤ 1/18`;
4. At the Hardy–Littlewood / GUE coalescent deficit `β = −1/144`, `29/36 − (−1/144) = 13/16 > 3/4`. -/
theorem coalescent_budget_thresholds_for_two_thirds_HD_one_and_three_quarters (β : ℝ) :
    (2 / 3 < 29 / 36 - β ↔ β < 5 / 36) ∧
    (254 / 375 ≤ 29 / 36 - β ↔ β ≤ 577 / 4500) ∧
    (β ≤ 577 / 4500 → Zeta23.ThmD.HD 1 < 29 / 36 - β) ∧
    (3 / 4 ≤ 29 / 36 - β ↔ β ≤ 1 / 18) ∧
    ((29 / 36 : ℝ) - -(1 / 144) = 13 / 16) := by
  have hHD := HD_one_lt_twoHundredFiftyFour_div_threeHundredSeventyFive
  refine ⟨by constructor <;> intro h <;> linarith,
    by constructor <;> intro h <;> linarith,
    fun h => by linarith,
    by constructor <;> intro h <;> linarith,
    by norm_num⟩

/-- **Sieve-Theoretic Separation of `HD(1)` from `3/4` at Bandwidth `λ = 4/3`.**
Evaluating the bandwidth-`4/3` certified proportion `29/36 − generalPrimeSurplusRatio F (4/3)`
across the affine trans-threshold models `affineTransModel β γ` separates **beating `HD(1)`** from
**reaching `3/4`**:
1. **Unsigned Additive Sieve (`F(α) = α + Υ` on `[1, 4/3]`):** surplus is `Υ/16`, proportion is
   `29/36 − Υ/16`:
   - Beats `2/3` iff `Υ < 20/9`;
   - Beats `254/375 > HD(1)` iff `Υ ≤ 2308/1125 = 2.0515…`, so **at the factor-two sieve parity
     limit `Υ = 2`**, the certified proportion is `49/72 = 0.68055… > 254/375 > HD(1) > 2/3`!
   - Reaches `3/4` iff `Υ ≤ 8/9 < 1` (impossible without signed cancellation).
2. **Spectral Sieve (`F(α) = Υ`, after Frullani cancellation of the Poisson continuum):** surplus
   is `(9Υ − 10)/144`, proportion is `7/8 − Υ/16`:
   - Beats `2/3` iff `Υ < 10/3`;
   - Beats `254/375 > HD(1)` iff `Υ ≤ 1186/375 = 3.1626…` (at `Υ = 3`, proportion is
     `11/16 = 0.6875 > 254/375 > HD(1)`);
   - Reaches `3/4` iff `Υ ≤ 2` (the exact factor-two sieve parity limit).
3. **Hardy–Littlewood / Function-Field / GUE (`F(α) = 1`):** surplus is `−1/144 < 0` from the
   singular-series logarithmic deficit, certifying `13/16 = 0.8125 > 3/4`. -/
theorem five_model_separation_of_HD_one_and_three_quarters (Υ : ℝ) :
    -- 1. Unsigned additive sieve at factor-two parity limit Υ = 2 strictly beats HD(1):
    (29 / 36 - generalPrimeSurplusRatio (affineTransModel (1 + 2) 1) (4 / 3) = 49 / 72 ∧
      Zeta23.ThmD.HD 1 < 254 / 375 ∧ (254 / 375 : ℝ) < 49 / 72) ∧
    -- 2. Exact thresholds for the unsigned additive sieve F(α) = α + Υ:
    ((2 / 3 < 29 / 36 - generalPrimeSurplusRatio (affineTransModel (1 + Υ) 1) (4 / 3) ↔
        Υ < 20 / 9) ∧
      (254 / 375 ≤ 29 / 36 - generalPrimeSurplusRatio (affineTransModel (1 + Υ) 1) (4 / 3) ↔
        Υ ≤ 2308 / 1125) ∧
      (3 / 4 ≤ 29 / 36 - generalPrimeSurplusRatio (affineTransModel (1 + Υ) 1) (4 / 3) ↔
        Υ ≤ 8 / 9)) ∧
    -- 3. Exact thresholds for the spectral sieve F(α) = Υ:
    (29 / 36 - generalPrimeSurplusRatio (affineTransModel 3 0) (4 / 3) = 11 / 16 ∧
      (254 / 375 : ℝ) < 11 / 16 ∧
      (2 / 3 < 29 / 36 - generalPrimeSurplusRatio (affineTransModel Υ 0) (4 / 3) ↔
        Υ < 10 / 3) ∧
      (254 / 375 ≤ 29 / 36 - generalPrimeSurplusRatio (affineTransModel Υ 0) (4 / 3) ↔
        Υ ≤ 1186 / 375) ∧
      (3 / 4 ≤ 29 / 36 - generalPrimeSurplusRatio (affineTransModel Υ 0) (4 / 3) ↔
        Υ ≤ 2)) ∧
    -- 4. Hardy–Littlewood / GUE model (β = 1, γ = 0):
    (29 / 36 - generalPrimeSurplusRatio (affineTransModel 1 0) (4 / 3) = 13 / 16) := by
  have hHD := HD_one_lt_twoHundredFiftyFour_div_threeHundredSeventyFive
  have h_add := (calibration_five_models_four_thirds Υ).2.2.2.2.2.2.1
  have h_add2 := (calibration_five_models_four_thirds 2).2.2.2.2.2.2.1
  have h_spec := (calibration_five_models_four_thirds Υ).2.2.2.2.1
  have h_spec3 := (calibration_five_models_four_thirds 3).2.2.2.2.1
  have h_gue := (calibration_five_models_four_thirds Υ).1
  refine ⟨⟨by linarith, hHD, by norm_num⟩,
    ⟨by rw [h_add]; constructor <;> intro h <;> linarith,
      by rw [h_add]; constructor <;> intro h <;> linarith,
      by rw [h_add]; constructor <;> intro h <;> linarith⟩,
    ⟨by linarith, by norm_num,
      by rw [h_spec]; constructor <;> intro h <;> linarith,
      by rw [h_spec]; constructor <;> intro h <;> linarith,
      by rw [h_spec]; constructor <;> intro h <;> linarith⟩,
    by linarith⟩

/-! ## 4. Exact Variational Two-Window Mixture Envelope (`mixOpt`) and Narrow-Strip `2`-Adic Collar -/

/-- The unique optimal mixing weight `ε*(B) = (1 + 36B) / (2(91 + 9B))` minimizing the two-window
pair-correlation quadratic form `RHTower.mixQ B ε`. -/
def mixOptWeight (B : ℝ) : ℝ :=
  (1 + 36 * B) / (2 * (91 + 9 * B))

/-- The maximum certified critical-line proportion `mixOpt B = 2/3 + (181 − 18B)² / (1728(91 + 9B))`
of the two-window mixture `2 − RHTower.mixQ B ε` over all mixing weights `ε ∈ ℝ`. -/
def mixOpt (B : ℝ) : ℝ :=
  2 / 3 + (181 - 18 * B) ^ 2 / (1728 * (91 + 9 * B))

/-- **Exact Square-Completion Identity for the Two-Window Mixture (`mixOpt − (2 − mixQ)`).**
For every `B` with `91 + 9B ≠ 0` and every mixing weight `ε : ℝ`,
`mixOpt B − (2 − RHTower.mixQ B ε) = ((91 + 9B) / 432) * (ε − mixOptWeight B)²`. -/
theorem mixOpt_sub_two_sub_mixQ {B : ℝ} (hB : 91 + 9 * B ≠ 0) (ε : ℝ) :
    mixOpt B - (2 - RHTower.mixQ B ε) =
      (91 + 9 * B) / 432 * (ε - mixOptWeight B) ^ 2 := by
  apply mul_right_cancel₀ hB
  unfold mixOpt mixOptWeight RHTower.mixQ
  have h1 : (181 - 18 * B) ^ 2 / (1728 * (91 + 9 * B)) * (91 + 9 * B) =
      (181 - 18 * B) ^ 2 / 1728 := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hB]
  have h2 : (1 + 36 * B) / (2 * (91 + 9 * B)) * (91 + 9 * B) = (1 + 36 * B) / 2 := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hB]
  have h3 : (91 + 9 * B) / 432 * (ε - (1 + 36 * B) / (2 * (91 + 9 * B))) ^ 2 * (91 + 9 * B) =
      1 / 432 * (ε * (91 + 9 * B) - (1 + 36 * B) / (2 * (91 + 9 * B)) * (91 + 9 * B)) ^ 2 := by
    ring
  have h4 : (2 / 3 + (181 - 18 * B) ^ 2 / (1728 * (91 + 9 * B)) -
      (2 - ((1 - ε) ^ 2 * (9 / 8 + B / 16) + 2 * ε * (1 - ε) * (971 / 864 + B / 48) +
        ε ^ 2 * (4 / 3)))) * (91 + 9 * B) =
      (2 / 3 - (2 - ((1 - ε) ^ 2 * (9 / 8 + B / 16) + 2 * ε * (1 - ε) * (971 / 864 + B / 48) +
        ε ^ 2 * (4 / 3)))) * (91 + 9 * B) +
        (181 - 18 * B) ^ 2 / (1728 * (91 + 9 * B)) * (91 + 9 * B) := by
    ring
  rw [h4, h1, h3, h2]
  ring

/-- **Global Optimality of `mixOpt B` and Strict Convexity of `mixOptWeight B`.**
For every `B > −91/9`:
1. `2 − RHTower.mixQ B ε ≤ mixOpt B` for all `ε : ℝ`, with equality at `ε = mixOptWeight B`;
2. Whenever `−1/36 < B < 181/18`, the optimal mixing weight satisfies `0 < mixOptWeight B < 1`,
   and `2/3 < mixOpt B`. -/
theorem two_sub_mixQ_le_mixOpt_and_eq_at_weight {B : ℝ} (hB : -91 / 9 < B) :
    (∀ ε : ℝ, 2 - RHTower.mixQ B ε ≤ mixOpt B) ∧
    2 - RHTower.mixQ B (mixOptWeight B) = mixOpt B ∧
    (-1 / 36 < B → B < 181 / 18 →
      0 < mixOptWeight B ∧ mixOptWeight B < 1 ∧ 2 / 3 < mixOpt B) := by
  have hden : 0 < 91 + 9 * B := by linarith
  refine ⟨fun ε => ?_, ?_, fun hlo hhi => ?_⟩
  · have hid := mixOpt_sub_two_sub_mixQ hden.ne' ε
    have hnn : 0 ≤ (91 + 9 * B) / 432 * (ε - mixOptWeight B) ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    linarith
  · have hid := mixOpt_sub_two_sub_mixQ hden.ne' (mixOptWeight B)
    rw [sub_self] at hid
    norm_num at hid
    linarith
  · unfold mixOptWeight mixOpt
    have hnum1 : 0 < 1 + 36 * B := by linarith
    have hnum2 : 0 < 181 - 18 * B := by linarith
    refine ⟨div_pos hnum1 (by positivity), ?_, ?_⟩
    · rw [div_lt_one (by positivity)]
      linarith
    · have : 0 < (181 - 18 * B) ^ 2 / (1728 * (91 + 9 * B)) :=
        div_pos (sq_pos_of_pos hnum2) (by positivity)
      linarith

/-- **Exact Variational Two-Window Thresholds for `3/4` and `HD(1)`.**
1. For every `B > −91/9`, `(∃ ε : ℝ, 3/4 ≤ 2 − RHTower.mixQ B ε) ↔ 3/4 ≤ mixOpt B ↔ 27432 ≤ (18B − 217)²`;
2. At `ε = 4/9`, `3/4 ≤ 2 − RHTower.mixQ B (4/9) ↔ B ≤ 2954 / 1035` (where `2954/1035 > 117/41`,
   strictly extending the `ε = 7/16` threshold `B ≤ 117/41`);
3. At `B = 1` (`ε* = 37/200`), `mixOpt 1 = 141769 / 172800 > 13 / 16`;
   at `B = 2` (`ε* = 73/218`), `mixOpt 2 = 146593 / 188352 > 1513 / 1944 > 3 / 4`;
4. At `B = 7` (`ε* = 253/308`), `mixOpt 7 = 180433 / 266112 > 254 / 375 > HD(1)`, so the
   two-window mixture strictly beats `HD(1)` all the way up to `B = 7`. -/
theorem mixOpt_values_and_three_quarters_criterion :
    (∀ B : ℝ, -91 / 9 < B →
      ((∃ ε : ℝ, 3 / 4 ≤ 2 - RHTower.mixQ B ε) ↔ 3 / 4 ≤ mixOpt B) ∧
      (3 / 4 ≤ mixOpt B ↔ 27432 ≤ (18 * B - 217) ^ 2)) ∧
    (∀ B : ℝ, (3 / 4 ≤ 2 - RHTower.mixQ B (4 / 9) ↔ B ≤ 2954 / 1035)) ∧
    ((117 / 41 : ℝ) < 2954 / 1035) ∧
    (mixOpt 1 = 141769 / 172800 ∧ (13 / 16 : ℝ) < 141769 / 172800) ∧
    (mixOpt 2 = 146593 / 188352 ∧ (1513 / 1944 : ℝ) < 146593 / 188352) ∧
    (mixOpt 7 = 180433 / 266112 ∧ Zeta23.ThmD.HD 1 < 254 / 375 ∧
      (254 / 375 : ℝ) < 180433 / 266112) := by
  refine ⟨fun B hB => ?_, fun B => ?_, by norm_num, ?_, ?_, ?_⟩
  · obtain ⟨hle, heq, -⟩ := two_sub_mixQ_le_mixOpt_and_eq_at_weight hB
    have hiff1 : (∃ ε : ℝ, 3 / 4 ≤ 2 - RHTower.mixQ B ε) ↔ 3 / 4 ≤ mixOpt B :=
      ⟨fun ⟨ε, hε⟩ => hε.trans (hle ε), fun h => ⟨mixOptWeight B, h.trans_eq heq.symm⟩⟩
    refine ⟨hiff1, ?_⟩
    unfold mixOpt
    have hden : 0 < 1728 * (91 + 9 * B) := by linarith
    have hden_ne : 1728 * (91 + 9 * B) ≠ 0 := hden.ne'
    have hid : 2 / 3 + (181 - 18 * B) ^ 2 / (1728 * (91 + 9 * B)) - 3 / 4 =
        ((18 * B - 217) ^ 2 - 27432) / (1728 * (91 + 9 * B)) := by
      apply mul_right_cancel₀ hden_ne
      have h1 : (2 / 3 + (181 - 18 * B) ^ 2 / (1728 * (91 + 9 * B)) - 3 / 4) *
          (1728 * (91 + 9 * B)) =
          (2 / 3 - 3 / 4) * (1728 * (91 + 9 * B)) +
            (181 - 18 * B) ^ 2 / (1728 * (91 + 9 * B)) * (1728 * (91 + 9 * B)) := by ring
      rw [h1, div_mul_cancel₀ _ hden_ne, div_mul_cancel₀ _ hden_ne]
      ring
    constructor
    · intro h
      have hnn : 0 ≤ ((18 * B - 217) ^ 2 - 27432) / (1728 * (91 + 9 * B)) := by linarith
      have hnum : 0 ≤ (18 * B - 217) ^ 2 - 27432 := by
        have hmul := mul_nonneg hnn hden.le
        rwa [div_mul_cancel₀ _ hden_ne] at hmul
      linarith
    · intro h
      have hnn : 0 ≤ ((18 * B - 217) ^ 2 - 27432) / (1728 * (91 + 9 * B)) :=
        div_nonneg (by linarith) hden.le
      linarith
  · unfold RHTower.mixQ
    constructor <;> intro h <;> linarith
  · unfold mixOpt; exact ⟨by norm_num, by norm_num⟩
  · unfold mixOpt; exact ⟨by norm_num, by norm_num⟩
  · unfold mixOpt
    exact ⟨by norm_num, HD_one_lt_twoHundredFiftyFour_div_threeHundredSeventyFive, by norm_num⟩

/-- **Narrow-Strip Cesàro Energy Criterion for Beating `HD(1)` and `2`-Adic Parity Collar Summary.**
For any continuous form factor `F` with `F(α) = α` on `[0, 1]` and any strip width `δ > 0`:
1. `2 − frobeniusFormFactor F (1 + δ) > 2/3 ↔ narrowStripCesaroEnergy F δ < 2 / (3δ) + 4 / 3`;
2. `254 / 375 ≤ 2 − frobeniusFormFactor F (1 + δ)` (which strictly beats `HD(1)`) holds iff
   `375 δ² narrowStripCesaroEnergy F δ ≤ 242 δ + 496 δ² − 4`;
3. On the discrete prime side, `2`-adic parity forces all odd-odd off-diagonal Fejér close-pair
   terms to vanish across the doubled range `b X ≤ 2` (`odd_offDiag_fejer_sum_eq_zero_of_le_two_div_b`). -/
theorem narrowStrip_HD_one_and_twoAdic_parity_collar {F : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hF_cont : Continuous F) (hF_sub : ∀ α ∈ Icc (0 : ℝ) 1, F α = α) :
    (2 / 3 < 2 - frobeniusFormFactor F (1 + δ) ↔
      narrowStripCesaroEnergy F δ < 2 / (3 * δ) + 4 / 3) ∧
    (254 / 375 ≤ 2 - frobeniusFormFactor F (1 + δ) ↔
      375 * δ ^ 2 * narrowStripCesaroEnergy F δ ≤ 242 * δ + 496 * δ ^ 2 - 4) ∧
    (254 / 375 ≤ 2 - frobeniusFormFactor F (1 + δ) →
      Zeta23.ThmD.HD 1 < 2 - frobeniusFormFactor F (1 + δ)) ∧
    (∀ b X : ℝ, 0 < b → 0 ≤ X → b * X ≤ 2 →
      (∑ n ∈ (Zeta23.PrimeSide.primeRange X).filter Odd,
        ∑ m ∈ (Zeta23.PrimeSide.primeRange X).filter Odd,
          if n = m then (0 : ℝ)
          else Zeta23.PrimeSide.acoef n * Zeta23.PrimeSide.acoef m *
            FejerWeight.triangleFn b (Real.log n - Real.log m)) = 0) := by
  have h1δ : 0 < 1 + δ := by linarith
  have hfrob := narrowStrip_frobeniusFormFactor_eq hδ.ne' h1δ.ne' hF_cont hF_sub
  have hden : 0 < 375 * (1 + δ) ^ 2 := by positivity
  have hid : (2 - frobeniusFormFactor F (1 + δ)) - 254 / 375 =
      (242 * δ + 496 * δ ^ 2 - 4 - 375 * δ ^ 2 * narrowStripCesaroEnergy F δ) /
        (375 * (1 + δ) ^ 2) := by
    rw [hfrob]
    have h3 : 3 * (1 + δ) ^ 2 ≠ 0 := by positivity
    field_simp [h3, hden.ne']
    ring
  have hHD := HD_one_lt_twoHundredFiftyFour_div_threeHundredSeventyFive
  refine ⟨(narrowStrip_beats_two_thirds_iff hδ hF_cont hF_sub).1, ?_,
    fun h => lt_of_lt_of_le hHD h,
    fun b X hb hX hbX => odd_offDiag_fejer_sum_eq_zero_of_le_two_div_b hb hX hbX⟩
  constructor
  · intro h
    have hnn : 0 ≤ (242 * δ + 496 * δ ^ 2 - 4 - 375 * δ ^ 2 * narrowStripCesaroEnergy F δ) /
        (375 * (1 + δ) ^ 2) := by linarith
    have hnum : 0 ≤ 242 * δ + 496 * δ ^ 2 - 4 - 375 * δ ^ 2 * narrowStripCesaroEnergy F δ := by
      have hmul := mul_nonneg hnn hden.le
      rwa [div_mul_cancel₀ _ hden.ne'] at hmul
    linarith
  · intro h
    have hnn : 0 ≤ (242 * δ + 496 * δ ^ 2 - 4 - 375 * δ ^ 2 * narrowStripCesaroEnergy F δ) /
        (375 * (1 + δ) ^ 2) := div_nonneg (by linarith) hden.le
    linarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end

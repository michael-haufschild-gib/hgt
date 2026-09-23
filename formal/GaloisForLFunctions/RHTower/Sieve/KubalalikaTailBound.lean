import GaloisForLFunctions.RHTower.Sieve.KubalalikaLargeScale

/-!
# The parity-weighted near-diagonal tail

The card's `E_Λ(T)` is `O(T^{15/16} (log T)^(6 : ℕ))`.  The three ingredients are the mixed hybrid
Vaughan block estimate at `U ≍ T^{1/2}`, `V ≍ T^{1/8}`, the dyadic assembly of the `m`-range, and
the harmonic total over the shift `r`.
-/

namespace RHTower.Sieve

open Filter Finset ArithmeticFunction RHTower

noncomputable section

/-- The harmonic sum over a shift range. -/
theorem sum_inv_Icc_le_one_add_log {rLo rHi : ℕ} (hrLo : 1 ≤ rLo) (hrHi : 1 ≤ rHi) :
    ∑ r ∈ Finset.Icc rLo rHi, (1 / (r : ℝ)) ≤ 1 + Real.log rHi := by
  have hsub : Finset.Icc rLo rHi ⊆ Finset.Icc 1 rHi := by
    intro r hr
    rw [Finset.mem_Icc] at hr ⊢
    exact ⟨le_trans hrLo hr.1, hr.2⟩
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun r : ℕ => (1 : ℝ) / (r : ℝ)) hsub (fun r _ _ => by positivity)
  refine le_trans h ?_
  have := invSum_le_one_add_log hrHi
  rw [invSum] at this
  exact this

set_option maxHeartbeats 1200000 in
/-- **The parity-weighted near-diagonal tail is `O(T^{15/16} (log T)^(6 : ℕ))`.** -/
theorem exists_norm_kubalalikaWeightedTail_le :
    ∃ D : ℝ, 0 < D ∧ ∀ {T : ℝ}, KubalalikaLarge T →
      ‖kubalalikaWeightedTail T‖ ≤ D * T ^ (15 / 16 : ℝ) * (1 + Real.log T) ^ 6 := by
  classical
  obtain ⟨D₀, hD₀, hblock⟩ := exists_norm_sum_vonMangoldt_ndPhaseExp_le_kubalalika_power'
  refine ⟨116640 * D₀ + 6, by positivity, ?_⟩
  intro T hL
  have hT0 := hL.pos
  have hT1 := hL.one_le
  have hlog0 := hL.log_nonneg
  have hepspos := hL.eps_pos
  have hepsle := hL.eps_le_one
  set s : ℝ := 1 + Real.log T with hsdef
  have hs : (1 : ℝ) ≤ s := by rw [hsdef]; linarith
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs
  have hT15 : (0 : ℝ) < T ^ (15 / 16 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hT15one : (1 : ℝ) ≤ T ^ (15 / 16 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
  -- the localization parameters
  set mLo : ℕ := ⌈T / ((1 + kubalalikaEps T) * (Real.log T) ^ 2)⌉₊ with hmLodef
  set mHi : ℕ := ⌊T * (1 + kubalalikaEps T)⌋₊ with hmHidef
  set rLo : ℕ := ⌈Real.sqrt (Real.sqrt T)⌉₊ with hrLodef
  set rHi : ℕ := ⌊(mHi : ℝ) * kubalalikaEps T⌋₊ with hrHidef
  set U : ℕ := ⌈T ^ (1 / 2 : ℝ)⌉₊ with hUdef
  set V : ℕ := ⌈T ^ (1 / 8 : ℝ)⌉₊ with hVdef
  have hmLo1 : 1 ≤ mLo := hL.one_le_mLo
  have hmHi1 : 1 ≤ mHi := hL.one_le_mHi
  have hmLoge : T / (2 * s ^ 2) ≤ (mLo : ℝ) := by rw [hsdef]; exact hL.mLo_ge
  have hmHile : (mHi : ℝ) ≤ 2 * T := hL.mHi_le
  have hrLo1 : 1 ≤ rLo := hL.one_le_rLo
  have hrLoge : T ^ (1 / 4 : ℝ) ≤ (rLo : ℝ) := hL.rLo_ge
  have hrHile : (rHi : ℝ) ≤ 2 * T ^ (3 / 4 : ℝ) := hL.rHi_le hmHile
  obtain ⟨hUge, hUle, hU1⟩ := hL.ceil_bounds (1 / 2 : ℝ) (by norm_num)
  obtain ⟨hVge, hVle, hV1⟩ := hL.ceil_bounds (1 / 8 : ℝ) (by norm_num)
  -- the block constant
  set K : ℝ := 2 * (1 + Real.log ((mHi + 1 : ℕ) : ℝ)) * (8 * D₀ * (1 + Real.log (4 * T)) ^ 4)
    with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hKdef]
    have h1 : (0 : ℝ) ≤ Real.log ((mHi + 1 : ℕ) : ℝ) := by
      refine Real.log_nonneg ?_
      have : (1 : ℕ) ≤ mHi + 1 := by omega
      exact_mod_cast this
    have h2 : (0 : ℝ) ≤ Real.log (4 * T) := by
      refine Real.log_nonneg ?_
      linarith
    positivity
  set G : ℕ → ℝ := fun r => K * kubalalikaScalePower T r with hGdef
  have hG0 : ∀ r : ℕ, 0 ≤ G r := by
    intro r
    rw [hGdef]
    exact mul_nonneg hK0 (kubalalikaScalePower_nonneg hT0.le (Nat.cast_nonneg r))
  -- the inner sum bound
  have hGbound : ∀ r ∈ Finset.Icc rLo rHi,
      ‖∑ m ∈ (Finset.Icc mLo mHi).filter (fun m : ℕ => r ≤ ⌊(m : ℝ) * kubalalikaEps T⌋₊),
          ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T r m‖ ≤ G r := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hr1 : T ^ (1 / 4 : ℝ) ≤ (r : ℝ) := by
      have : (rLo : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.1
      linarith
    have hr2 : (r : ℝ) ≤ 2 * T ^ (3 / 4 : ℝ) := by
      have : (r : ℝ) ≤ (rHi : ℝ) := by exact_mod_cast hr.2
      linarith
    have hrpos : (0 : ℝ) < (r : ℝ) := by
      have := Real.rpow_pos_of_pos hT0 (1 / 4 : ℝ)
      linarith
    by_cases hne : ((Finset.Icc mLo mHi).filter
        (fun m : ℕ => r ≤ ⌊(m : ℝ) * kubalalikaEps T⌋₊)).Nonempty
    · set A₀ : ℕ := ((Finset.Icc mLo mHi).filter
        (fun m : ℕ => r ≤ ⌊(m : ℝ) * kubalalikaEps T⌋₊)).min' hne with hA₀def
      have hA₀mem := Finset.min'_mem _ hne
      rw [← hA₀def, Finset.mem_filter, Finset.mem_Icc] at hA₀mem
      have hA₀lo : mLo ≤ A₀ := hA₀mem.1.1
      have hA₀hi : A₀ ≤ mHi := hA₀mem.1.2
      rw [filter_shiftCeil_eq_Ico hepspos.le mLo mHi r hne, ← hA₀def]
      refine le_trans (norm_sum_Ico_le_of_blocks
        (f := fun m : ℕ => ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T r m)
        (G := 8 * D₀ * (1 + Real.log (4 * T)) ^ 4 * kubalalikaScalePower T r)
        (by omega) (le_trans hmLo1 hA₀lo) ?_ ?_) ?_
      · have h2 : (0 : ℝ) ≤ Real.log (4 * T) := by
          refine Real.log_nonneg ?_
          linarith
        have := kubalalikaScalePower_nonneg hT0.le (le_of_lt hrpos)
        positivity
      · intro A B hA1 hAB hBA hA₀A hBmHi
        have hAlow : T / (2 * s ^ 2) ≤ (A : ℝ) := by
          have h1 : (mLo : ℝ) ≤ (A : ℝ) := by
            exact_mod_cast le_trans hA₀lo hA₀A
          linarith
        have hB3 : (B : ℝ) ≤ 3 * T := by
          have h1 : (B : ℝ) ≤ ((mHi + 1 : ℕ) : ℝ) := by exact_mod_cast hBmHi
          have h2 : ((mHi + 1 : ℕ) : ℝ) = (mHi : ℝ) + 1 := by push_cast; ring
          rw [h2] at h1
          linarith
        obtain ⟨hUA, hUVA, h8r, hcurv, hAX⟩ :=
          hL.block_conditions hr1 hr2 hAB hAlow hB3 hUle hVle
        have hpow := hblock hT0 hrpos hA1 hAB hBA hU1 hV1 hUA hUVA h8r hcurv hAX
        refine le_trans hpow ?_
        exact kubalalikaBlockPower_le_scale hD₀.le hT1 hrpos hA1 hAB (by linarith)
          hUge hUle hVge hVle
      · rw [hGdef, hKdef]
        exact le_of_eq (by ring)
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty, norm_zero]
      exact hG0 r
  -- assemble the tail
  refine le_trans (norm_weightedTail_le_of_blockBound hepspos.le hmLo1 hmHi1 G hGbound) ?_
  rcases lt_or_ge rHi rLo with hempty | hrne
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  have hrHi1 : 1 ≤ rHi := le_trans hrLo1 hrne
  -- split the harmonic total
  have hcongr : ∑ r ∈ Finset.Icc rLo rHi, (G r + Real.log (mHi : ℝ)) / (r : ℝ)
      = K * (∑ r ∈ Finset.Icc rLo rHi, kubalalikaScalePower T r / (r : ℝ))
        + Real.log (mHi : ℝ) * (∑ r ∈ Finset.Icc rLo rHi, (1 / (r : ℝ))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [hGdef]
    field_simp
  -- the two totals
  have hsum1 := sum_kubalalikaScalePower_div_le hT1 hrLo1 hrLoge hrHile
  have hsum2 := sum_inv_Icc_le_one_add_log hrLo1 hrHi1
  -- the logarithmic factors
  have hlogmHi : Real.log (mHi : ℝ) ≤ s := by
    have h1 : Real.log (mHi : ℝ) ≤ Real.log (2 * T) := by
      refine Real.log_le_log ?_ hmHile
      have : (1 : ℝ) ≤ (mHi : ℝ) := by exact_mod_cast hmHi1
      linarith
    have h2 : Real.log (2 * T) = Real.log 2 + Real.log T :=
      Real.log_mul (by norm_num) (ne_of_gt hT0)
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    rw [hsdef]
    linarith
  have hlogmHi0 : (0 : ℝ) ≤ Real.log (mHi : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast hmHi1
  have hlogrHi : 1 + Real.log (rHi : ℝ) ≤ 2 * s := by
    have hrHi0 : (0 : ℝ) < (rHi : ℝ) := by exact_mod_cast hrHi1
    have h1 : Real.log (rHi : ℝ) ≤ Real.log (2 * T ^ (3 / 4 : ℝ)) :=
      Real.log_le_log hrHi0 hrHile
    have h2 : Real.log (2 * T ^ (3 / 4 : ℝ)) = Real.log 2 + (3 / 4) * Real.log T := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hT0]
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    rw [hsdef]
    linarith
  have hKle : K ≤ 3888 * D₀ * s ^ 5 := by
    have hmHiplus : 1 + Real.log ((mHi + 1 : ℕ) : ℝ) ≤ 3 * s := by
      have hcast : ((mHi + 1 : ℕ) : ℝ) = (mHi : ℝ) + 1 := by push_cast; ring
      have h1 : ((mHi + 1 : ℕ) : ℝ) ≤ 3 * T := by rw [hcast]; linarith
      have h2 : Real.log ((mHi + 1 : ℕ) : ℝ) ≤ Real.log (3 * T) := by
        refine Real.log_le_log ?_ h1
        rw [hcast]
        have : (1 : ℝ) ≤ (mHi : ℝ) := by exact_mod_cast hmHi1
        linarith
      have h3 : Real.log (3 * T) = Real.log 3 + Real.log T :=
        Real.log_mul (by norm_num) (ne_of_gt hT0)
      have h4 : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
        linarith
      rw [hsdef]
      linarith
    have hfour : (1 + Real.log (4 * T)) ^ 4 ≤ 81 * s ^ 4 := by
      have h1 : Real.log (4 * T) = Real.log 4 + Real.log T :=
        Real.log_mul (by norm_num) (ne_of_gt hT0)
      have h2 : Real.log 4 ≤ 2 := by
        have hl2 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          linarith
        have : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num
        linarith
      have h3 : 1 + Real.log (4 * T) ≤ 3 * s := by rw [hsdef]; linarith
      have h4 : (0 : ℝ) ≤ 1 + Real.log (4 * T) := by
        have : (0 : ℝ) ≤ Real.log (4 * T) := by
          refine Real.log_nonneg ?_
          linarith
        linarith
      calc (1 + Real.log (4 * T)) ^ 4 ≤ (3 * s) ^ 4 := pow_le_pow_left₀ h4 h3 4
        _ = 81 * s ^ 4 := by ring
    have hm0 : (0 : ℝ) ≤ 1 + Real.log ((mHi + 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ Real.log ((mHi + 1 : ℕ) : ℝ) := by
        refine Real.log_nonneg ?_
        have : (1 : ℕ) ≤ mHi + 1 := by omega
        exact_mod_cast this
      linarith
    have hf0 : (0 : ℝ) ≤ (1 + Real.log (4 * T)) ^ 4 := by positivity
    rw [hKdef]
    calc 2 * (1 + Real.log ((mHi + 1 : ℕ) : ℝ)) * (8 * D₀ * (1 + Real.log (4 * T)) ^ 4)
        ≤ 2 * (3 * s) * (8 * D₀ * (81 * s ^ 4)) := by
          have hstep1 : 2 * (1 + Real.log ((mHi + 1 : ℕ) : ℝ)) ≤ 2 * (3 * s) := by linarith
          have hD8 : (0 : ℝ) ≤ 8 * D₀ := by linarith
          have hstep2 : 8 * D₀ * (1 + Real.log (4 * T)) ^ 4 ≤ 8 * D₀ * (81 * s ^ 4) :=
            mul_le_mul_of_nonneg_left hfour hD8
          have hnn : (0 : ℝ) ≤ 8 * D₀ * (1 + Real.log (4 * T)) ^ 4 := mul_nonneg hD8 hf0
          exact mul_le_mul hstep1 hstep2 hnn (by linarith)
      _ = 3888 * D₀ * s ^ 5 := by ring
  -- the two contributions
  have hsp0 : (0 : ℝ) ≤ ∑ r ∈ Finset.Icc rLo rHi, kubalalikaScalePower T r / (r : ℝ) := by
    refine Finset.sum_nonneg fun r hr => ?_
    exact div_nonneg (kubalalikaScalePower_nonneg hT0.le (Nat.cast_nonneg r))
      (Nat.cast_nonneg r)
  have hinv0 : (0 : ℝ) ≤ ∑ r ∈ Finset.Icc rLo rHi, (1 / (r : ℝ)) := by
    refine Finset.sum_nonneg fun r hr => ?_
    positivity
  have hfirst : K * (∑ r ∈ Finset.Icc rLo rHi, kubalalikaScalePower T r / (r : ℝ))
      ≤ 116640 * D₀ * T ^ (15 / 16 : ℝ) * s ^ 6 := by
    have h1 : K * (∑ r ∈ Finset.Icc rLo rHi, kubalalikaScalePower T r / (r : ℝ))
        ≤ (3888 * D₀ * s ^ 5) * (30 * T ^ (15 / 16 : ℝ) * s) := by
      refine mul_le_mul hKle ?_ hsp0 (by positivity)
      rw [hsdef]
      exact hsum1
    calc K * (∑ r ∈ Finset.Icc rLo rHi, kubalalikaScalePower T r / (r : ℝ))
        ≤ (3888 * D₀ * s ^ 5) * (30 * T ^ (15 / 16 : ℝ) * s) := h1
      _ = 116640 * D₀ * T ^ (15 / 16 : ℝ) * s ^ 6 := by ring
  have hsecond : Real.log (mHi : ℝ) * (∑ r ∈ Finset.Icc rLo rHi, (1 / (r : ℝ)))
      ≤ 6 * T ^ (15 / 16 : ℝ) * s ^ 6 := by
    have h1 : Real.log (mHi : ℝ) * (∑ r ∈ Finset.Icc rLo rHi, (1 / (r : ℝ)))
        ≤ s * (2 * s) := by
      refine mul_le_mul hlogmHi (le_trans hsum2 hlogrHi) hinv0 (by linarith)
    have h2 : s * (2 * s) ≤ 6 * T ^ (15 / 16 : ℝ) * s ^ 6 := by
      have hs6 : s ^ 2 ≤ s ^ 6 := by
        have := pow_le_pow_right₀ hs (by norm_num : 2 ≤ 6)
        linarith
      have hs60 : (0 : ℝ) ≤ s ^ 6 := by positivity
      nlinarith only [hs6, hs60, hT15one, hT15]
    linarith
  have hDsplit : (116640 * D₀ + 6) * T ^ (15 / 16 : ℝ) * s ^ 6
      = 116640 * D₀ * T ^ (15 / 16 : ℝ) * s ^ 6 + 6 * T ^ (15 / 16 : ℝ) * s ^ 6 := by ring
  linarith

/-- The tail bound in eventual form. -/
theorem exists_eventually_norm_kubalalikaWeightedTail_le :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ T : ℝ in atTop,
      ‖kubalalikaWeightedTail T‖ ≤ D * T ^ (15 / 16 : ℝ) * (1 + Real.log T) ^ 6 := by
  obtain ⟨D, hD0, hbound⟩ := exists_norm_kubalalikaWeightedTail_le
  refine ⟨D, hD0, ?_⟩
  filter_upwards [eventually_kubalalikaLarge] with T hT
  exact hbound hT

/-- **Equation (5) of the card.**  The parity-weighted near-diagonal tail is
`O(T^{53/54} (log T)^(6 : ℕ))`. -/
theorem kubalalikaWeightedTail_isBigO :
    (fun T : ℝ => kubalalikaWeightedTail T) =O[atTop]
      (fun T : ℝ => T ^ (53 / 54 : ℝ) * Real.log T ^ 6) := by
  obtain ⟨D, hD0, hbound⟩ := exists_norm_kubalalikaWeightedTail_le
  rw [Asymptotics.isBigO_iff]
  refine ⟨64 * D, ?_⟩
  filter_upwards [eventually_kubalalikaLarge] with T hT
  have hT0 := hT.pos
  have hT1 := hT.one_le
  have hlog1 := hT.one_le_log
  have hstep := hbound hT
  have hpow : T ^ (15 / 16 : ℝ) ≤ T ^ (53 / 54 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have hlogpow : (1 + Real.log T) ^ 6 ≤ 64 * Real.log T ^ 6 := by
    have h1 : 1 + Real.log T ≤ 2 * Real.log T := by linarith
    calc (1 + Real.log T) ^ 6 ≤ (2 * Real.log T) ^ 6 :=
          pow_le_pow_left₀ (by linarith) h1 6
      _ = 64 * Real.log T ^ 6 := by ring
  have hnorm : ‖T ^ (53 / 54 : ℝ) * Real.log T ^ 6‖
      = T ^ (53 / 54 : ℝ) * Real.log T ^ 6 := by
    refine Real.norm_of_nonneg ?_
    have h1 : (0 : ℝ) ≤ T ^ (53 / 54 : ℝ) := (Real.rpow_pos_of_pos hT0 _).le
    have h2 : (0 : ℝ) ≤ Real.log T ^ 6 := by positivity
    positivity
  rw [hnorm]
  have hL0 : (0 : ℝ) ≤ (1 + Real.log T) ^ 6 := by positivity
  have hP0 : (0 : ℝ) < T ^ (15 / 16 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hchain : D * T ^ (15 / 16 : ℝ) * (1 + Real.log T) ^ 6
      ≤ 64 * D * (T ^ (53 / 54 : ℝ) * Real.log T ^ 6) := by
    have h1 : D * T ^ (15 / 16 : ℝ) * (1 + Real.log T) ^ 6
        ≤ D * T ^ (53 / 54 : ℝ) * (1 + Real.log T) ^ 6 := by
      have hDp : (0 : ℝ) ≤ D * (1 + Real.log T) ^ 6 := by positivity
      nlinarith only [hpow, hDp, hD0, hL0]
    have h2 : D * T ^ (53 / 54 : ℝ) * (1 + Real.log T) ^ 6
        ≤ D * T ^ (53 / 54 : ℝ) * (64 * Real.log T ^ 6) := by
      have hDp : (0 : ℝ) ≤ D * T ^ (53 / 54 : ℝ) := by
        have := (Real.rpow_pos_of_pos hT0 (53 / 54 : ℝ)).le
        positivity
      exact mul_le_mul_of_nonneg_left hlogpow hDp
    have h3 : D * T ^ (53 / 54 : ℝ) * (64 * Real.log T ^ 6)
        = 64 * D * (T ^ (53 / 54 : ℝ) * Real.log T ^ 6) := by ring
    linarith
  linarith

/-- **The tail is `o(T)`.** -/
theorem kubalalikaWeightedTail_isLittleO :
    (fun T : ℝ => kubalalikaWeightedTail T) =o[atTop] (fun T : ℝ => T) := by
  refine kubalalikaWeightedTail_isBigO.trans_isLittleO ?_
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_const_mul_one_add_log_pow_le_rpow (δ := 1 / 54) (c := 1 / c)
      (by norm_num) (by positivity) 6] with T hT1 hTlog
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT1
  have hlog0 : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT1
  have hcpow : (1 + Real.log T) ^ 6 ≤ c * T ^ (1 / 54 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hTlog hc.le
    have hid : c * (1 / c * (1 + Real.log T) ^ 6) = (1 + Real.log T) ^ 6 := by
      field_simp
    rw [hid] at h
    exact h
  have hsplit : T ^ (53 / 54 : ℝ) * T ^ (1 / 54 : ℝ) = T := by
    rw [← Real.rpow_add hT0]
    norm_num
  have hnorm1 : ‖T ^ (53 / 54 : ℝ) * Real.log T ^ 6‖
      = T ^ (53 / 54 : ℝ) * Real.log T ^ 6 := by
    refine Real.norm_of_nonneg ?_
    have h1 : (0 : ℝ) ≤ T ^ (53 / 54 : ℝ) := (Real.rpow_pos_of_pos hT0 _).le
    positivity
  have hnorm2 : ‖T‖ = T := Real.norm_of_nonneg hT0.le
  rw [hnorm1, hnorm2]
  have hle : Real.log T ^ 6 ≤ (1 + Real.log T) ^ 6 :=
    pow_le_pow_left₀ hlog0 (by linarith) 6
  have hP0 : (0 : ℝ) < T ^ (53 / 54 : ℝ) := Real.rpow_pos_of_pos hT0 _
  calc T ^ (53 / 54 : ℝ) * Real.log T ^ 6
      ≤ T ^ (53 / 54 : ℝ) * (1 + Real.log T) ^ 6 := mul_le_mul_of_nonneg_left hle hP0.le
    _ ≤ T ^ (53 / 54 : ℝ) * (c * T ^ (1 / 54 : ℝ)) := mul_le_mul_of_nonneg_left hcpow hP0.le
    _ = c * (T ^ (53 / 54 : ℝ) * T ^ (1 / 54 : ℝ)) := by ring
    _ = c * T := by rw [hsplit]

end

end RHTower.Sieve

import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.OnlyTheBoundaryStarEntersAtTouching
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.OverlapLengthControlsTheTouchingCrossError

/-!
# The boundary prime star has a vanishing norm budget

The divisor identity pays every weight in the single non-ratio boundary star.
The overlap left at its lag is quadratic in the atom width, so normalization
leaves a prime-source error tending to zero.
-/

noncomputable section

open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticEffectivityTheory
  RenormalizedArithmeticPotentialTheory
open _root_.RHTower (vonMangoldtAtom)

private theorem boundary_weight_mass_le (N : ℕ) :
    (∑ k ∈ Icc 2 (N + 1), ∑ m ∈ Icc 1 N,
      if k * m = N + 1 then vonMangoldtAtom k else 0) ≤ Real.log (N + 1 : ℕ) := by
  classical
  have hpoint : ∀ k ∈ Icc 2 (N + 1), vonMangoldtAtom k ≤ ArithmeticFunction.vonMangoldt k := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k from (by have := (mem_Icc.mp hk).1; omega))
    have hs : 1 ≤ Real.sqrt k := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hk1
    rw [vonMangoldtAtom_eq (mem_Icc.mp hk).1]
    exact div_le_self ArithmeticFunction.vonMangoldt_nonneg hs
  have hfirst : (∑ k ∈ Icc 2 (N + 1), ∑ m ∈ Icc 1 N,
      if k * m = N + 1 then vonMangoldtAtom k else 0) ≤
      ∑ k ∈ Icc 2 (N + 1), ∑ m ∈ Icc 1 N,
        if k * m = N + 1 then ArithmeticFunction.vonMangoldt k else 0 := by
    apply sum_le_sum
    intro k hk
    apply sum_le_sum
    intro m hm
    split_ifs <;> [exact hpoint k hk; exact le_rfl]
  have h := sum_sum_vonMangoldt_le (Icc 2 (N + 1)) (Icc 1 N)
    (fun k hk => by have := (mem_Icc.mp hk).1; omega)
    (fun m hm => (mem_Icc.mp hm).1) (fun l => l = N + 1)
  have hsub : (((Icc 2 (N + 1) ×ˢ Icc 1 N).image fun p : ℕ × ℕ => p.1 * p.2).filter
      fun l => l = N + 1) ⊆ {N + 1} := by
    intro l hl
    exact mem_singleton.mpr (mem_filter.mp hl).2
  have hlast := sum_le_sum_of_subset_of_nonneg (f := fun l : ℕ => Real.log l) hsub
    (fun l _ _ => Real.log_natCast_nonneg l)
  simpa only [sum_singleton] using hfirst.trans (h.trans hlast)

/-- The actual boundary correction is controlled by one divisor logarithm. -/
theorem abs_nonRatioForm_at_touching_le {g : ℝ → ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hsupp : ∀ u, u ∉ Set.Icc 0 (1 / (N : ℝ)) → g u = 0) (x : ℕ → ℝ) :
    |nonRatioForm g N x| ≤
      2 * |bumpCorr g (Real.log (N + 1 : ℕ) - Real.log N)| * Real.log (N + 1 : ℕ) *
        ∑ m ∈ Icc 1 N, x m ^ 2 := by
  let S : ℝ := ∑ m ∈ Icc 1 N, x m ^ 2
  have hS : 0 ≤ S := sum_nonneg fun m _ => sq_nonneg _
  have hNmem : N ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hxN : x N ^ 2 ≤ S := single_le_sum (fun m _ => sq_nonneg _) hNmem
  have hpair : ∀ m ∈ Icc 1 N, |x N * x m| ≤ S := by
    intro m hm
    have hxm : x m ^ 2 ≤ S := single_le_sum (fun n _ => sq_nonneg _) hm
    rw [abs_mul]
    nlinarith only [sq_nonneg (|x N| - |x m|), sq_abs (x N), sq_abs (x m), hxN, hxm]
  have hsum : |∑ k ∈ Icc 2 (N + 1), ∑ m ∈ Icc 1 N,
      if k * m = N + 1 then vonMangoldtAtom k * (x N * x m) else 0| ≤
      Real.log (N + 1 : ℕ) * S := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ k ∈ Icc 2 (N + 1), ∑ m ∈ Icc 1 N,
          (if k * m = N + 1 then vonMangoldtAtom k else 0) * S := by
        apply sum_le_sum
        intro k hk
        apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro m hm
        split_ifs
        · rw [abs_mul, abs_of_nonneg (_root_.RHTower.vonMangoldtAtom_nonneg' k)]
          exact mul_le_mul_of_nonneg_left (hpair m hm) (_root_.RHTower.vonMangoldtAtom_nonneg' k)
        · simp only [abs_zero, zero_mul, le_refl]
      _ = (∑ k ∈ Icc 2 (N + 1), ∑ m ∈ Icc 1 N,
          if k * m = N + 1 then vonMangoldtAtom k else 0) * S := by
        simp only [sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (boundary_weight_mass_le N) hS
  rw [nonRatioForm_eq_boundary_star hN hsupp x, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by dsimp only [S]; ring)

private theorem touching_log_lag_bounds {N : ℕ} (hN : 1 ≤ N) :
    0 < Real.log (N + 1 : ℕ) - Real.log N ∧
    Real.log (N + 1 : ℕ) - Real.log N < 1 / (N : ℝ) ∧
    1 / (N : ℝ) - (Real.log (N + 1 : ℕ) - Real.log N) ≤ (1 / (N : ℝ)) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hpos : 0 < Real.log (N + 1 : ℕ) - Real.log N :=
    sub_pos.mpr (Real.log_lt_log hN0 (by exact_mod_cast Nat.lt_succ_self N))
  have hloRatio : (N : ℝ) / (N + 1) < 1 := (div_lt_one hN1).mpr (by linarith)
  have hlo := Real.log_lt_sub_one_of_pos (div_pos hN0 hN1) (ne_of_lt hloRatio)
  rw [Real.log_div hN0.ne' hN1.ne'] at hlo
  have hhiRatio : 1 < ((N : ℝ) + 1) / N := (one_lt_div hN0).mpr (by linarith)
  have hhi := Real.log_lt_sub_one_of_pos (div_pos hN1 hN0) (ne_of_gt hhiRatio)
  rw [Real.log_div hN1.ne' hN0.ne'] at hhi
  have e1 : 1 - (N : ℝ) / (N + 1) = 1 / ((N : ℝ) + 1) := by field_simp; ring
  have e2 : ((N : ℝ) + 1) / N - 1 = 1 / (N : ℝ) := by field_simp; ring
  have hlower : 1 / ((N : ℝ) + 1) < Real.log (N + 1 : ℕ) - Real.log N := by
    push_cast
    rw [← e1]
    linarith only [hlo]
  have hupper : Real.log (N + 1 : ℕ) - Real.log N < 1 / (N : ℝ) := by
    push_cast
    rwa [e2] at hhi
  refine ⟨hpos, hupper, ?_⟩
  calc
    _ ≤ 1 / (N : ℝ) - 1 / ((N : ℝ) + 1) := sub_le_sub_left hlower.le _
    _ = 1 / ((N : ℝ) * (N + 1)) := by field_simp; ring
    _ ≤ 1 / (N : ℝ) ^ 2 := one_div_le_one_div_of_le (sq_pos_of_pos hN0)
      (by nlinarith only [hN0])
    _ = _ := by ring

/-- Every coefficient vector has a vanishing normalized prime correction at touching. -/
theorem abs_normalized_nonRatioForm_at_touching_le {φ : ℝ → ℝ} {B : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (hB : 0 ≤ B) (hheight : ∀ u, |φ u| ≤ B)
    {N : ℕ} (hN : 2 ≤ N) (x : ℕ → ℝ) :
    |nonRatioForm (atomDilate φ (1 / (N : ℝ))) N x| /
        (∫ u, atomDilate φ (1 / (N : ℝ)) u ^ 2) ≤
      ((2 * B ^ 2 / (∫ u, φ u ^ 2)) * Real.log (N + 1 : ℕ) / N) *
        ∑ m ∈ Icc 1 N, x m ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let w : ℝ := 1 / N
  let d : ℝ := Real.log (N + 1 : ℕ) - Real.log N
  have hw : 0 < w := one_div_pos.mpr hN0
  obtain ⟨hg, hgsupp, _hgc⟩ := atomDilate_facts hφ hsupp hw
  obtain ⟨hd, hdw, hrem⟩ := touching_log_lag_bounds (show 1 ≤ N by omega)
  have hheightg : ∀ u, |atomDilate φ w u| ≤ B := fun u => hheight (u / w)
  have hG : 0 < ∫ u, atomDilate φ w u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  have hcorr : |bumpCorr (atomDilate φ w) d| ≤ B ^ 2 * w ^ 2 := by
    change |bumpAutocorr (atomDilate φ w) d| ≤ _
    have h := abs_bumpAutocorr_le_overlap_length hg.continuous hgsupp hB hheightg
      (show |d| ≤ w by rw [abs_of_pos hd]; exact hdw.le)
    rw [abs_of_pos hd] at h
    exact h.trans (mul_le_mul_of_nonneg_left hrem (sq_nonneg B))
  have hraw := abs_nonRatioForm_at_touching_le hN hgsupp x
  have hS : 0 ≤ ∑ m ∈ Icc 1 N, x m ^ 2 := sum_nonneg fun m _ => sq_nonneg _
  have hl : 0 ≤ Real.log (N + 1 : ℕ) := Real.log_natCast_nonneg _
  calc
    _ ≤ (2 * |bumpCorr (atomDilate φ w) d| * Real.log (N + 1 : ℕ) *
        ∑ m ∈ Icc 1 N, x m ^ 2) / (∫ u, atomDilate φ w u ^ 2) :=
      div_le_div_of_nonneg_right hraw hG.le
    _ ≤ (2 * (B ^ 2 * w ^ 2) * Real.log (N + 1 : ℕ) *
        ∑ m ∈ Icc 1 N, x m ^ 2) / (∫ u, atomDilate φ w u ^ 2) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcorr (by norm_num)) hl) hS) hG.le
    _ = _ := by
      rw [integral_atomDilate_sq hw]
      dsimp only [w]
      field_simp [hN0.ne', hM.ne']

/-- The non-ratio prime correction has one vanishing budget for every ratio up to one. -/
theorem abs_normalized_nonRatioForm_uniform_up_to_touching {φ : ℝ → ℝ} {B : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (hB : 0 ≤ B) (hheight : ∀ u, |φ u| ≤ B)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {N : ℕ} (hN : 2 ≤ N) (x : ℕ → ℝ) :
    |nonRatioForm (atomDilate φ (c / N)) N x| / (∫ u, atomDilate φ (c / N) u ^ 2) ≤
      ((4 * B ^ 2 / (∫ u, φ u ^ 2)) * Real.log (N + 1 : ℕ) / N) *
        ∑ m ∈ Icc 1 N, x m ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  let w : ℝ := c / N
  let d : ℝ := Real.log (N + 1 : ℕ) - Real.log N
  have hw : 0 < w := div_pos hc0 hN0
  have hwN : w ≤ 1 / (N : ℝ) := div_le_div_of_nonneg_right hc1 hN0.le
  obtain ⟨hg, hgsupp, _hgc⟩ := atomDilate_facts hφ hsupp hw
  have hbig : ∀ u, u ∉ Set.Icc 0 (1 / (N : ℝ)) → atomDilate φ w u = 0 := by
    intro u hu
    exact hgsupp u (fun h => hu ⟨h.1, h.2.trans hwN⟩)
  obtain ⟨hd, _hdw, hrem⟩ := touching_log_lag_bounds (show 1 ≤ N by omega)
  have hlower : 1 / ((N : ℝ) + 1) < d := by
    have h := inv_horizon_lt_integer_log_gap
      (N := N + 1) (n := N) (j := N + 1)
      (mem_Icc.mpr ⟨by omega, by omega⟩) (mem_Icc.mpr ⟨by omega, le_rfl⟩) (by omega)
    rw [abs_of_pos hd] at h
    simpa only [d, Nat.cast_add, Nat.cast_one] using h
  have hG : 0 < ∫ u, atomDilate φ w u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  have hS : 0 ≤ ∑ m ∈ Icc 1 N, x m ^ 2 := sum_nonneg fun m _ => sq_nonneg _
  have hl : 0 ≤ Real.log (N + 1 : ℕ) := Real.log_natCast_nonneg _
  by_cases hcHalf : c ≤ 1 / 2
  · have hwlow : w ≤ 1 / ((N : ℝ) + 1) := by
      apply (div_le_div_iff₀ hN0 hN1).mpr
      have hcmul := mul_le_mul_of_nonneg_right hcHalf hN1.le
      have hNge : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      nlinarith only [hcmul, hNge]
    have hcorr : bumpCorr (atomDilate φ w) d = 0 :=
      bumpCorr_eq_zero hgsupp (by rw [abs_of_pos hd]; exact hwlow.trans_lt hlower)
    have hzero : nonRatioForm (atomDilate φ w) N x = 0 := by
      rw [nonRatioForm_eq_boundary_star hN hbig x, hcorr, mul_zero, zero_mul]
    change |nonRatioForm (atomDilate φ w) N x| / _ ≤ _
    rw [hzero, abs_zero, zero_div]
    positivity
  · have hcorr : |bumpCorr (atomDilate φ w) d| ≤ B ^ 2 * (1 / (N : ℝ)) ^ 2 := by
      by_cases hdw : d ≤ w
      · change |bumpAutocorr (atomDilate φ w) d| ≤ _
        have h := abs_bumpAutocorr_le_overlap_length hg.continuous hgsupp hB
          (fun u => hheight (u / w)) (by rw [abs_of_pos hd]; exact hdw)
        rw [abs_of_pos hd] at h
        exact h.trans (mul_le_mul_of_nonneg_left
          ((sub_le_sub_right hwN d).trans hrem) (sq_nonneg B))
      · rw [bumpCorr_eq_zero hgsupp (by rw [abs_of_pos hd]; exact lt_of_not_ge hdw), abs_zero]
        positivity
    have hraw := abs_nonRatioForm_at_touching_le hN hbig x
    have hcinv : 1 / c ≤ 2 := (div_le_iff₀ hc0).mpr (by linarith only [lt_of_not_ge hcHalf])
    let A : ℝ := ((2 * B ^ 2 / (∫ u, φ u ^ 2)) * Real.log (N + 1 : ℕ) / N) *
      ∑ m ∈ Icc 1 N, x m ^ 2
    have hA : 0 ≤ A := by dsimp only [A]; positivity
    calc
      _ ≤ (2 * |bumpCorr (atomDilate φ w) d| * Real.log (N + 1 : ℕ) *
          ∑ m ∈ Icc 1 N, x m ^ 2) / (∫ u, atomDilate φ w u ^ 2) :=
        div_le_div_of_nonneg_right hraw hG.le
      _ ≤ (2 * (B ^ 2 * (1 / (N : ℝ)) ^ 2) * Real.log (N + 1 : ℕ) *
          ∑ m ∈ Icc 1 N, x m ^ 2) / (∫ u, atomDilate φ w u ^ 2) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcorr (by norm_num)) hl) hS) hG.le
      _ = A * (1 / c) := by
        rw [integral_atomDilate_sq hw]
        dsimp only [w, A]
        field_simp [hN0.ne', hc0.ne', hM.ne'] <;> ring
      _ ≤ A * 2 := mul_le_mul_of_nonneg_left hcinv hA
      _ = _ := by dsimp only [A]; ring

/-- Every actual smooth nonzero profile supplies its own uniform boundary-source budget. -/
theorem exists_uniform_nonRatio_budget {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ N : ℕ, 2 ≤ N → ∀ x : ℕ → ℝ,
      |nonRatioForm (atomDilate φ (c / N)) N x| / (∫ u, atomDilate φ (c / N) u ^ 2) ≤
        (D * Real.log (N + 1 : ℕ) / N) * ∑ m ∈ Icc 1 N, x m ^ 2 := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hsupp
  obtain ⟨L, hL, hLip⟩ := ArithmeticCriticalityTheory.exists_lipschitz_bound_of_compactSupport
    (hφ.of_le (by norm_num)) hφc
  let B : ℝ := 1 + 2 * L
  have hB : 0 < B := by dsimp only [B]; positivity
  have hm : φ (-1) = 0 := hsupp (-1) (by norm_num)
  have hheight : ∀ u, |φ u| ≤ B := by
    intro u
    by_cases hu : u ∈ Set.Icc 0 1
    · have h := hLip (-1) u
      have hu0 : 0 ≤ u + 1 := by linarith only [hu.1]
      simp only [hm, sub_zero, sub_neg_eq_add, abs_of_nonneg hu0] at h
      calc
        _ ≤ L * (u + 1) := h
        _ ≤ L * 2 := mul_le_mul_of_nonneg_left (by linarith only [hu.2]) hL
        _ ≤ B := by dsimp only [B]; linarith
    · rw [hsupp u hu, abs_zero]
      exact hB.le
  refine ⟨4 * B ^ 2 / (∫ u, φ u ^ 2), by positivity, ?_⟩
  intro c hc0 hc1 N hN x
  exact abs_normalized_nonRatioForm_uniform_up_to_touching hφ hsupp hM hB.le hheight hc0 hc1 hN x

private theorem tendsto_log_succ_div_horizon :
    Tendsto (fun N : ℕ => Real.log (N + 1 : ℕ) / (N : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun N : ℕ => Real.log 2 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => Real.log 2 / (N : ℝ) + Real.log N / N) atTop (𝓝 0) := by
    simpa only [zero_add] using hc.add hlog
  have hbound : ∀ᶠ N : ℕ in atTop,
      Real.log (N + 1 : ℕ) / (N : ℝ) ≤ Real.log 2 / N + Real.log N / N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h := Real.log_le_log (show 0 < ((N + 1 : ℕ) : ℝ) by positivity)
      (show ((N + 1 : ℕ) : ℝ) ≤ 2 * N by push_cast; linarith only [hN1])
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne'] at h
    simpa only [add_div] using div_le_div_of_nonneg_right h hN0.le
  exact squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg N)) hbound hlim

/-- The actual boundary prime operator tends to zero uniformly in the width ratio. -/
theorem eventually_normalized_nonRatioForm_small_uniformly {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ x : ℕ → ℝ,
      |nonRatioForm (atomDilate φ (c / N)) N x| / (∫ u, atomDilate φ (c / N) u ^ 2) ≤
        ε * ∑ m ∈ Icc 1 N, x m ^ 2 := by
  obtain ⟨D, _hD, hbound⟩ := exists_uniform_nonRatio_budget hφ hsupp hM
  have hlim : Tendsto (fun N : ℕ => D * Real.log (N + 1 : ℕ) / N) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using tendsto_log_succ_div_horizon.const_mul D
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_ge_atTop 2] with N hsmall hN
  intro c hc0 hc1 x
  exact (hbound c hc0 hc1 N hN x).trans (mul_le_mul_of_nonneg_right hsmall.le
    (sum_nonneg fun m _ => sq_nonneg _))

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_nonRatioForm_at_touching_le

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_normalized_nonRatioForm_at_touching_le

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_normalized_nonRatioForm_uniform_up_to_touching

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_uniform_nonRatio_budget

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_normalized_nonRatioForm_small_uniformly

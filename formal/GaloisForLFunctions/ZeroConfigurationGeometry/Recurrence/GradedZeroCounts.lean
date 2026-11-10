import GaloisForLFunctions.RHTower.XiRightDiscSeamContractionInghamHuxley
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardTheoremOneOne
import GaloisForLFunctions.RHTower.ZetaZeroDensityThirtyThirteenths

/-!
# Cumulative zero counts at the Guth–Maynard exponent

Dyadic zero counts give cumulative counts with one extra logarithm. Any
strictly larger power absorbs all logarithms, giving a count suitable for
separated self-return arguments.
-/

open Complex Filter Topology RHTower

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry.Recurrence

/-- Summing dyadic boxes costs at most one logarithm in a nonnegative power bound. -/
theorem ncard_zeroCopyRange_le_of_dyadic {σ D E T₀ Y : ℝ} {B : ℕ}
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hT₀ : 1 ≤ T₀)
    (hbox : ∀ T : ℝ, T₀ ≤ T → ((zeroHeightBox σ T).ncard : ℝ) ≤
      D * (1 + Real.log T) ^ B * T ^ E) (hY : T₀ ≤ Y) :
    ((zeroCopyRange σ T₀ Y).ncard : ℝ) ≤
      2 * D * (1 + Real.log Y) ^ (B + 1) * Y ^ E := by
  classical
  have hT₀0 : 0 < T₀ := by linarith only [hT₀]
  have hY1 : 1 ≤ Y := hT₀.trans hY
  set J : ℕ := Nat.log 2 ⌊Y / T₀⌋₊ with hJ
  have hparam : ∀ j ∈ Finset.range (J + 1), T₀ ≤ T₀ * 2 ^ j ∧ T₀ * 2 ^ j ≤ Y := by
    intro j hj
    have hjJ : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    refine ⟨le_mul_of_one_le_right hT₀0.le (one_le_pow₀ (by norm_num)), ?_⟩
    have hfl : 1 ≤ ⌊Y / T₀⌋₊ := Nat.one_le_floor_iff _ |>.mpr ((one_le_div hT₀0).mpr hY)
    have h2J : 2 ^ J ≤ ⌊Y / T₀⌋₊ := Nat.pow_log_le_self 2 (by omega)
    have h2j : (2 : ℝ) ^ j ≤ Y / T₀ := by
      calc (2 : ℝ) ^ j ≤ (2 : ℝ) ^ J := pow_le_pow_right₀ (by norm_num) hjJ
        _ = ((2 ^ J : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (⌊Y / T₀⌋₊ : ℝ) := by exact_mod_cast h2J
        _ ≤ Y / T₀ := Nat.floor_le (div_nonneg (by linarith only [hY1]) hT₀0.le)
    rw [mul_comm]
    exact (le_div_iff₀ hT₀0).mp h2j
  have hJlog : (J : ℝ) ≤ 2 * Real.log Y := by
    have hfl : 1 ≤ ⌊Y / T₀⌋₊ := Nat.one_le_floor_iff _ |>.mpr ((one_le_div hT₀0).mpr hY)
    have h2J : 2 ^ J ≤ ⌊Y / T₀⌋₊ := Nat.pow_log_le_self 2 (by omega)
    have h2JY : (2 : ℝ) ^ J ≤ Y := by
      calc (2 : ℝ) ^ J = ((2 ^ J : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (⌊Y / T₀⌋₊ : ℝ) := by exact_mod_cast h2J
        _ ≤ Y / T₀ := Nat.floor_le (div_nonneg (by linarith only [hY1]) hT₀0.le)
        _ ≤ Y := div_le_self (by linarith only [hY1]) hT₀
    have hlog := Real.log_le_log (by positivity) h2JY
    rw [Real.log_pow] at hlog
    have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    nlinarith only [hlog, hl2, hJ0]
  have hsub := zeroCopyRange_subset_iUnion (σ := σ) (Y := Y) hT₀0
  rw [← hJ] at hsub
  have hfin : ∀ j, (zeroHeightBox σ (T₀ * 2 ^ j)).Finite := fun j => zeroHeightBox_finite σ _
  set F : Finset XiZeroCopy :=
    (Finset.range (J + 1)).biUnion (fun j => (hfin j).toFinset) with hF
  have hsubF : zeroCopyRange σ T₀ Y ⊆ (F : Set XiZeroCopy) := by
    intro q hq
    obtain ⟨j, hj, hqj⟩ := Set.mem_iUnion₂.mp (hsub hq)
    rw [hF, Finset.coe_biUnion]
    exact Set.mem_iUnion₂.mpr ⟨j, hj, (hfin j).mem_toFinset.mpr hqj⟩
  have hncard : (zeroCopyRange σ T₀ Y).ncard ≤ F.card := by
    have h := Set.ncard_le_ncard hsubF F.finite_toSet
    rwa [Set.ncard_coe_finset] at h
  have hFcard : (F.card : ℝ) ≤
      ∑ j ∈ Finset.range (J + 1), ((zeroHeightBox σ (T₀ * 2 ^ j)).ncard : ℝ) := by
    have h := Finset.card_biUnion_le (s := Finset.range (J + 1)) (t := fun j => (hfin j).toFinset)
    have h' : (F.card : ℝ) ≤ ∑ j ∈ Finset.range (J + 1), (((hfin j).toFinset.card : ℕ) : ℝ) := by
      rw [hF]
      exact_mod_cast h
    refine h'.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [Set.ncard_eq_toFinset_card _ (hfin j)]
  set P : ℝ := D * (1 + Real.log Y) ^ B * Y ^ E with hP
  have hP0 : 0 ≤ P := by
    rw [hP]
    have := Real.log_nonneg hY1
    positivity
  have hterm : ∀ j ∈ Finset.range (J + 1),
      ((zeroHeightBox σ (T₀ * 2 ^ j)).ncard : ℝ) ≤ P := by
    intro j hj
    obtain ⟨hlo, hhi⟩ := hparam j hj
    have hx0 : 0 < T₀ * 2 ^ j := by positivity
    have hlog : Real.log (T₀ * 2 ^ j) ≤ Real.log Y := Real.log_le_log hx0 hhi
    have hlog0 : 0 ≤ Real.log (T₀ * 2 ^ j) := Real.log_nonneg (hT₀.trans hlo)
    have hlogY0 : 0 ≤ Real.log Y := Real.log_nonneg hY1
    calc ((zeroHeightBox σ (T₀ * 2 ^ j)).ncard : ℝ)
        ≤ D * (1 + Real.log (T₀ * 2 ^ j)) ^ B * (T₀ * 2 ^ j) ^ E := hbox _ hlo
      _ ≤ D * (1 + Real.log Y) ^ B * Y ^ E := by gcongr
  have hsum : ∑ j ∈ Finset.range (J + 1), ((zeroHeightBox σ (T₀ * 2 ^ j)).ncard : ℝ) ≤
      (J + 1 : ℝ) * P := by
    calc ∑ j ∈ Finset.range (J + 1), ((zeroHeightBox σ (T₀ * 2 ^ j)).ncard : ℝ)
        ≤ ∑ _j ∈ Finset.range (J + 1), P := Finset.sum_le_sum hterm
      _ = (J + 1 : ℝ) * P := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
  have hJ1 : (J + 1 : ℝ) ≤ 2 * (1 + Real.log Y) := by
    linarith only [hJlog]
  calc ((zeroCopyRange σ T₀ Y).ncard : ℝ) ≤ F.card := by exact_mod_cast hncard
    _ ≤ (J + 1 : ℝ) * P := hFcard.trans hsum
    _ ≤ 2 * (1 + Real.log Y) * P := mul_le_mul_of_nonneg_right hJ1 hP0
    _ = 2 * D * (1 + Real.log Y) ^ (B + 1) * Y ^ E := by rw [hP]; ring

/-- Every exponent strictly above the Guth–Maynard exponent bounds a cumulative tail census. -/
theorem exists_zeroCopyRange_le_rpow_guthMaynard {σ c : ℝ}
    (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 5 / 6) (hc : (30 / 13) * (1 - σ) < c) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ᶠ Y : ℝ in atTop,
      ((zeroCopyRange σ T₀ Y).ncard : ℝ) ≤ Y ^ c := by
  set a : ℝ := (30 / 13) * (1 - σ) with ha
  change a < c at hc
  have ha0 : 0 ≤ a := by rw [ha]; linarith only [hσ1]
  set ε : ℝ := min 1 ((c - a) / 2) with hε
  have hε0 : 0 < ε := lt_min one_pos (by linarith only [hc])
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεc : a + ε < c := by
    have hsmall : ε ≤ (c - a) / 2 := min_le_right _ _
    linarith only [hc, hsmall]
  obtain ⟨D, hD, B, T₁, hbox⟩ := exists_zeroHeightBox_ncard_le_fixed_thirty_thirteenths
    GuthMaynard.guthMaynardLargeValuesBound_holds hσ0 hσ1 hε0 hε1
  refine ⟨max 1 T₁, le_max_left _ _, ?_⟩
  have hpoly := eventually_const_mul_polylog_le_rpow (B + 1)
    (c := c - (a + ε)) (by linarith only [hεc]) (2 * D)
  filter_upwards [hpoly, eventually_ge_atTop (max 1 T₁)] with Y hpolyY hY
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hY0 : 0 < Y := by linarith only [hY1]
  have hcount := ncard_zeroCopyRange_le_of_dyadic hD
    (show 0 ≤ a + ε by linarith only [ha0, hε0]) (le_max_left 1 T₁)
    (fun T hT => hbox T ((le_max_right _ _).trans hT)) hY
  calc ((zeroCopyRange σ (max 1 T₁) Y).ncard : ℝ)
      ≤ 2 * D * (1 + Real.log Y) ^ (B + 1) * Y ^ (a + ε) := hcount
    _ ≤ Y ^ (c - (a + ε)) * Y ^ (a + ε) :=
      mul_le_mul_of_nonneg_right hpolyY (Real.rpow_nonneg hY0.le _)
    _ = Y ^ c := by rw [← Real.rpow_add hY0]; congr 1; ring

#print axioms ncard_zeroCopyRange_le_of_dyadic
#print axioms exists_zeroCopyRange_le_rpow_guthMaynard

end GaloisForLFunctions.ZeroConfigurationGeometry.Recurrence

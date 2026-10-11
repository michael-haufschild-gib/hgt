import GaloisForLFunctions.RHTower.ZetaZeroAntiCrystalCritical
import GaloisForLFunctions.RHTower.XiZeroCountLocalCeiling
import GaloisForLFunctions.RHTower.XiLocalZeroDensity

/-!
# The critical-scale inputs hold for large `T`

Each hypothesis of `false_of_critical_facts` other than rigidity holds for all large `T`:

* `eventually_card_zeroWindow_le`: `#{0 < γ ≤ T} ≤ TL/5`, from `N(T) ≤ (T/2π)L + O(L)`;
* `eventually_lowPairs_le`: the low pairs are `O(T^{11/16}L²) ≤ TL/1000`;
* `eventually_edges_le`: the edge rows are `O(L²) ≤ TL/1000`, from `N(t + 1) − N(t) = O(log t)`;
* `eventually_selbergLength_le`: the mean-square length `T + 8N_x(1 + log N_x) ≤ 2T`, where
  `x = T^{1/20}`;
* `eventually_lorentzMassW_le`: `Σ_ρ 1/((p/2)² + (p − γ)²) ≤ 1/4` for `p ≥ 3T^{1/2} − 1`;
* `eventually_narrowMass_bound`: under RH on `[T^{1/2}, T³]`, the explicit-formula bound holds at
  every `p ∈ [3T^{1/2} − 1, T + 1]`.
-/

noncomputable section

open Complex Filter Topology Finset

namespace RHTower

/-- `K T^a L² ≤ TL/1000` for large `T`, when `0 ≤ a < 1`. -/
theorem eventually_mul_rpow_mul_log_sq_le {a K : ℝ} (ha : a < 1) (hK : 0 ≤ K) :
    ∀ᶠ T : ℝ in atTop, K * T ^ a * Real.log T ^ 2 ≤ T * Real.log T / 1000 := by
  set ε := (1 - a) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  filter_upwards [(tendsto_rpow_atTop hε).eventually_ge_atTop (1000 * K / ε),
    eventually_ge_atTop (1 : ℝ)] with T hT hT1
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog : Real.log T ≤ T ^ ε / ε := Real.log_le_rpow_div hT0.le hε
  have hTa : 0 ≤ T ^ a := Real.rpow_nonneg hT0.le _
  have e : T = T ^ (a + ε) * T ^ ε := by
    rw [← Real.rpow_add hT0, show a + ε + ε = 1 by rw [hεdef]; ring, Real.rpow_one]
  have h1 : K * T ^ a * Real.log T ≤ T / 1000 := by
    calc K * T ^ a * Real.log T ≤ K * T ^ a * (T ^ ε / ε) := by gcongr
      _ = K / ε * T ^ (a + ε) := by rw [Real.rpow_add hT0]; field_simp
      _ ≤ T ^ ε / 1000 * T ^ (a + ε) := by
          have h : K / ε ≤ T ^ ε / 1000 := by
            rw [div_le_div_iff₀ hε (by norm_num)]
            rw [div_le_iff₀ hε] at hT
            linarith
          exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hT0.le _)
      _ = T / 1000 := by
          conv_rhs => rw [e]
          ring
  calc K * T ^ a * Real.log T ^ 2 = (K * T ^ a * Real.log T) * Real.log T := by ring
    _ ≤ T / 1000 * Real.log T := mul_le_mul_of_nonneg_right h1 hlog0
    _ = T * Real.log T / 1000 := by ring

/-- `N(T) ≤ K + (T/2π)L + 2CL`. -/
theorem exists_card_zeroWindow_le :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 < C ∧ ∃ T₀ : ℝ, 4 ≤ T₀ ∧ ∀ T, T₀ ≤ T →
      ((zeroWindow T).card : ℝ) ≤ K + T / (2 * Real.pi) * Real.log T + 2 * C * Real.log T := by
  classical
  obtain ⟨C, hC, T₀, hT₀, hcard⟩ := exists_card_window_le
  refine ⟨((zeroWindow T₀).card : ℝ), C, Nat.cast_nonneg _, hC, T₀, hT₀, fun T hT => ?_⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := zeroWindow T)
    (fun q : XiZeroCopy => (q.1 : ℂ).im ≤ T₀)
  have h1 : ((zeroWindow T).filter (fun q : XiZeroCopy => (q.1 : ℂ).im ≤ T₀)).card ≤
      (zeroWindow T₀).card := by
    refine Finset.card_le_card fun q hq => ?_
    rw [Finset.mem_filter, mem_zeroWindow] at hq
    rw [mem_zeroWindow]; exact ⟨hq.1.1, hq.2⟩
  have h2 := hcard T₀ le_rfl (T - T₀) (by linarith)
    ((zeroWindow T).filter (fun q : XiZeroCopy => ¬ (q.1 : ℂ).im ≤ T₀)) (by
      intro q hq
      rw [Finset.mem_filter, mem_zeroWindow] at hq
      push Not at hq
      exact ⟨hq.2, by linarith [hq.1.2]⟩)
  rw [show T₀ + (T - T₀) = T by ring] at h2
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have h3 : (T - T₀) / (2 * Real.pi) * Real.log T ≤ T / (2 * Real.pi) * Real.log T := by
    gcongr; linarith
  have h4 : ((zeroWindow T).card : ℝ) =
      ((zeroWindow T).filter (fun q : XiZeroCopy => (q.1 : ℂ).im ≤ T₀)).card +
        ((zeroWindow T).filter (fun q : XiZeroCopy => ¬ (q.1 : ℂ).im ≤ T₀)).card := by
    exact_mod_cast hsplit.symm
  have h1' : (((zeroWindow T).filter (fun q : XiZeroCopy => (q.1 : ℂ).im ≤ T₀)).card : ℝ) ≤
      (zeroWindow T₀).card := by exact_mod_cast h1
  linarith

/-- **`#{0 < γ ≤ T} ≤ TL/5` for large `T`.** -/
theorem eventually_card_zeroWindow_le :
    ∀ᶠ T : ℝ in atTop, ((zeroWindow T).card : ℝ) ≤ T * Real.log T / 5 := by
  obtain ⟨K, C, hK, hC, T₀, hT₀, hcount⟩ := exists_card_zeroWindow_le
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (120 * C + 60 * K + 3)] with T hT hT2
  have hT1 : 1 ≤ T := by linarith
  have hlog1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hπ := Real.pi_gt_three
  have h1 : T / (2 * Real.pi) * Real.log T ≤ T / 6 * Real.log T := by
    gcongr; linarith
  have h2 : 2 * C * Real.log T ≤ T / 60 * Real.log T := by
    have : 2 * C ≤ T / 60 := by linarith
    exact mul_le_mul_of_nonneg_right this (by linarith)
  have h3 : K ≤ T / 60 * Real.log T := by
    have : K ≤ T / 60 := by linarith
    nlinarith
  have := hcount T hT
  nlinarith


/-- `C₀ + log(T + 4) ≤ (|C₀| + 2) log T` for `T ≥ 4`. -/
theorem const_add_log_le {C₀ T : ℝ} (hT : 4 ≤ T) :
    C₀ + Real.log (T + 4) ≤ (|C₀| + 2) * Real.log T := by
  have hlog1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have h1 : Real.log (T + 4) ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
  have h2 : Real.log (2 * T) = Real.log 2 + Real.log T :=
    Real.log_mul (by norm_num) (by linarith)
  have h3 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith)
  have h4 : C₀ ≤ |C₀| * Real.log T := by
    calc C₀ ≤ |C₀| := le_abs_self _
      _ = |C₀| * 1 := (mul_one _).symm
      _ ≤ |C₀| * Real.log T := mul_le_mul_of_nonneg_left hlog1 (abs_nonneg _)
  nlinarith

/-- `exp(log T/16) = T^{1/16}`. -/
theorem exp_log_div_sixteen {T : ℝ} (hT : 0 < T) :
    Real.exp (Real.log T / 16) = T ^ (1 / 16 : ℝ) := by
  rw [Real.rpow_def_of_pos hT]; ring_nf

/-- **The low pairs are small.** -/
theorem eventually_lowPairs_le :
    ∀ᶠ T : ℝ in atTop, 2 * ((lowCopies T).card : ℝ) *
      (8 * T ^ (1 / 8 : ℝ) * Real.exp (Real.log T / 16) *
        (8 * (xiLineTwoLogDerivConstant + Real.log (T + 4)))) ≤ T * Real.log T / 1000 := by
  obtain ⟨K, C, hK, hC, T₀, hT₀, hcount⟩ := exists_card_zeroWindow_le
  set C₀ := xiLineTwoLogDerivConstant
  set K₁ := 128 * (K + 1 + 2 * C) * (|C₀| + 2) with hK₁
  filter_upwards [eventually_mul_rpow_mul_log_sq_le (a := 11 / 16) (K := K₁) (by norm_num)
      (by positivity),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop T₀,
    eventually_ge_atTop (16 : ℝ)] with T hmain hsT hT16
  have hT0 : 0 < T := by linarith
  have hlog1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set s := T ^ (1 / 2 : ℝ) with hs
  have hs1 : 4 ≤ s := by
    rw [hs, show (4 : ℝ) = 16 ^ (1 / 2 : ℝ) by
      rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num]
    exact Real.rpow_le_rpow (by norm_num) hT16 (by norm_num)
  have hsq : s * s = T := by rw [hs, ← Real.rpow_add hT0]; norm_num
  have hYT : 3 * s ≤ T := by nlinarith
  -- the low count
  have hsub : lowCopies T ⊆ zeroWindow (3 * s) := by
    intro q hq
    rw [lowCopies, Finset.mem_filter, mem_zeroWindow] at hq
    rw [mem_zeroWindow]
    exact ⟨hq.1.1, by push Not at hq; linarith [hq.2]⟩
  have hlo := hcount (3 * s) (by linarith)
  have hlogY : Real.log (3 * s) ≤ Real.log T := Real.log_le_log (by positivity) hYT
  have hlogY0 : 0 ≤ Real.log (3 * s) := Real.log_nonneg (by linarith)
  have hπ := Real.pi_gt_three
  have hcard : ((lowCopies T).card : ℝ) ≤ (K + 1 + 2 * C) * (s * Real.log T) := by
    have h1 : ((lowCopies T).card : ℝ) ≤ (zeroWindow (3 * s)).card := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 : 3 * s / (2 * Real.pi) * Real.log (3 * s) ≤ s * Real.log T := by
      have : 3 * s / (2 * Real.pi) ≤ s := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      exact mul_le_mul this hlogY hlogY0 (by linarith)
    have h3 : 2 * C * Real.log (3 * s) ≤ 2 * C * (s * Real.log T) := by
      have : Real.log T ≤ s * Real.log T := by nlinarith
      nlinarith
    have h4 : K ≤ K * (s * Real.log T) := by
      have : 1 ≤ s * Real.log T := by nlinarith
      nlinarith
    nlinarith
  have hlogC := const_add_log_le (C₀ := C₀) (show 4 ≤ T by linarith)
  have hpow : s * (T ^ (1 / 8 : ℝ) * T ^ (1 / 16 : ℝ)) = T ^ (11 / 16 : ℝ) := by
    rw [hs, ← Real.rpow_add hT0, ← Real.rpow_add hT0]; norm_num
  rw [exp_log_div_sixteen hT0]
  have hA : 0 ≤ T ^ (1 / 8 : ℝ) * T ^ (1 / 16 : ℝ) := by positivity
  calc 2 * ((lowCopies T).card : ℝ) * (8 * T ^ (1 / 8 : ℝ) * T ^ (1 / 16 : ℝ) *
        (8 * (C₀ + Real.log (T + 4))))
      ≤ 2 * ((K + 1 + 2 * C) * (s * Real.log T)) * (8 * T ^ (1 / 8 : ℝ) * T ^ (1 / 16 : ℝ) *
        (8 * ((|C₀| + 2) * Real.log T))) := by
        have h0 : 0 ≤ C₀ + Real.log (T + 4) ∨ C₀ + Real.log (T + 4) < 0 := le_or_gt _ _
        rcases h0 with h0 | h0
        · gcongr
        · have : 2 * ((lowCopies T).card : ℝ) * (8 * T ^ (1 / 8 : ℝ) * T ^ (1 / 16 : ℝ) *
              (8 * (C₀ + Real.log (T + 4)))) ≤ 0 := by
            have : 0 ≤ 2 * ((lowCopies T).card : ℝ) * (8 * T ^ (1 / 8 : ℝ) * T ^ (1 / 16 : ℝ)) := by
              positivity
            nlinarith
          refine this.trans ?_
          positivity
    _ = K₁ * (s * (T ^ (1 / 8 : ℝ) * T ^ (1 / 16 : ℝ))) * Real.log T ^ 2 := by rw [hK₁]; ring
    _ = K₁ * T ^ (11 / 16 : ℝ) * Real.log T ^ 2 := by rw [hpow]
    _ ≤ T * Real.log T / 1000 := hmain


/-- A unit window of ordered indices has `O(log t)` members. -/
theorem card_indices_near_le {C t : ℝ}
    (hC : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, |(q.1 : ℂ).im - t| ≤ 1) → (F.card : ℝ) ≤ C * Real.log t)
    (S : Finset ℕ) (hS : ∀ n ∈ S, |xiOrderedPositiveOrdinate n - t| ≤ 1) :
    (S.card : ℝ) ≤ C * Real.log t := by
  have h := hC (S.map ⟨xiOrderedPositiveZeroCopy, xiOrderedPositiveZeroCopy_injective⟩) (by
    intro q hq
    rw [Finset.mem_map] at hq
    obtain ⟨n, hn, rfl⟩ := hq
    simp only [Function.Embedding.coeFn_mk, xiOrderedPositiveZeroCopy_im_eq]
    exact hS n hn)
  rwa [Finset.card_map] at h

/-- **The edge rows are small.** -/
theorem eventually_edges_le :
    ∀ᶠ T : ℝ in atTop, ((edgeIndices T).card : ℝ) *
      (4 * (8 * (xiLineTwoLogDerivConstant + Real.log (T + 4)))) ≤ T * Real.log T / 1000 := by
  classical
  obtain ⟨C, hC, hev⟩ := exists_card_near_xi_zeros_le
  obtain ⟨t₁, ht₁⟩ := Filter.eventually_atTop.mp hev
  set C₀ := xiLineTwoLogDerivConstant
  set K₂ := 64 * C * (|C₀| + 2) with hK₂
  filter_upwards [eventually_mul_rpow_mul_log_sq_le (a := 0) (K := K₂) (by norm_num)
      (by positivity),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop t₁,
    eventually_ge_atTop (16 : ℝ), eventually_ge_atTop (t₁ + 1)] with T hmain hsT hT16 hTt
  have hT0 : 0 < T := by linarith
  set s := T ^ (1 / 2 : ℝ) with hs
  have hs1 : 4 ≤ s := by
    rw [hs, show (4 : ℝ) = 16 ^ (1 / 2 : ℝ) by
      rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num]
    exact Real.rpow_le_rpow (by norm_num) hT16 (by norm_num)
  have hsq : s * s = T := by rw [hs, ← Real.rpow_add hT0]; norm_num
  set L₁ := (edgeIndices T).filter (fun n => xiOrderedPositiveOrdinate n < 3 * s + 1) with hL₁
  set L₂ := (edgeIndices T).filter (fun n => ¬ xiOrderedPositiveOrdinate n < 3 * s + 1) with hL₂
  have hmem : ∀ n ∈ edgeIndices T, 3 * s ≤ xiOrderedPositiveOrdinate n ∧
      xiOrderedPositiveOrdinate n ≤ T ∧
      (xiOrderedPositiveOrdinate n < 3 * s + 1 ∨ T - 1 < xiOrderedPositiveOrdinate n) := by
    intro n hn
    rw [edgeIndices, Finset.mem_sdiff, interiorIndices, Finset.mem_filter] at hn
    have h1 := hn.1
    rw [mem_bulkIndices] at h1
    refine ⟨h1.1, h1.2, ?_⟩
    by_contra hc
    push Not at hc
    exact hn.2 ⟨hn.1, hc.1, by linarith [hc.2]⟩
  have hc1 : (L₁.card : ℝ) ≤ C * Real.log (3 * s + 1 / 2) := by
    refine card_indices_near_le (ht₁ _ (by linarith)) L₁ fun n hn => ?_
    rw [hL₁, Finset.mem_filter] at hn
    obtain ⟨h1, -, -⟩ := hmem n hn.1
    rw [abs_le]; constructor <;> linarith [hn.2]
  have hc2 : (L₂.card : ℝ) ≤ C * Real.log (T - 1 / 2) := by
    refine card_indices_near_le (ht₁ _ (by linarith)) L₂ fun n hn => ?_
    rw [hL₂, Finset.mem_filter] at hn
    obtain ⟨-, h2, h3⟩ := hmem n hn.1
    have h4 : T - 1 < xiOrderedPositiveOrdinate n := h3.resolve_left hn.2
    rw [abs_le]; constructor <;> linarith
  have hlog1 : Real.log (3 * s + 1 / 2) ≤ Real.log T := Real.log_le_log (by positivity) (by nlinarith)
  have hlog2 : Real.log (T - 1 / 2) ≤ Real.log T := Real.log_le_log (by linarith) (by linarith)
  have hcard : ((edgeIndices T).card : ℝ) ≤ 2 * C * Real.log T := by
    have h := Finset.card_filter_add_card_filter_not (s := edgeIndices T)
      (fun n => xiOrderedPositiveOrdinate n < 3 * s + 1)
    have h' : ((edgeIndices T).card : ℝ) = L₁.card + L₂.card := by exact_mod_cast h.symm
    rw [h']
    nlinarith
  have hlogC := const_add_log_le (C₀ := C₀) (show 4 ≤ T by linarith)
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  calc ((edgeIndices T).card : ℝ) * (4 * (8 * (C₀ + Real.log (T + 4))))
      ≤ (2 * C * Real.log T) * (4 * (8 * ((|C₀| + 2) * Real.log T))) := by
        rcases le_or_gt 0 (C₀ + Real.log (T + 4)) with h0 | h0
        · gcongr
        · have : ((edgeIndices T).card : ℝ) * (4 * (8 * (C₀ + Real.log (T + 4)))) ≤ 0 := by
            have : (0 : ℝ) ≤ (edgeIndices T).card := Nat.cast_nonneg _
            nlinarith
          refine this.trans ?_
          positivity
    _ = K₂ * T ^ (0 : ℝ) * Real.log T ^ 2 := by rw [Real.rpow_zero, hK₂]; ring
    _ ≤ T * Real.log T / 1000 := hmain

/-- **The mean-square length.** -/
theorem eventually_selbergLength_le :
    ∀ᶠ T : ℝ in atTop, (T - 1 / 2) - (3 * T ^ (1 / 2 : ℝ) + 1 / 2) +
      8 * selbergPolyLength (T ^ (1 / 20 : ℝ)) *
        (1 + Real.log (selbergPolyLength (T ^ (1 / 20 : ℝ)))) ≤ 2 * T := by
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).eventually_ge_atTop 48,
    eventually_ge_atTop (1 : ℝ)] with T hT45 hT1
  have hT0 : 0 < T := by linarith
  set N := selbergPolyLength (T ^ (1 / 20 : ℝ)) with hN
  set v := T ^ (1 / 10 : ℝ) with hv
  have hv1 : 1 ≤ v := Real.one_le_rpow hT1 (by norm_num)
  have hx2 : (T ^ (1 / 20 : ℝ)) ^ 2 = v := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
  have hN1 : (N : ℝ) ≤ v + 1 := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (T ^ (1 / 20 : ℝ)) ^ 2 by positivity)
    rw [hx2] at this
    rw [hN, selbergPolyLength, hx2]
    linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hlogN : Real.log N ≤ N := Real.log_le_self hN0
  have hlogN0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have h1 : 8 * (N : ℝ) * (1 + Real.log N) ≤ 48 * v ^ 2 := by nlinarith
  have hv2 : v ^ 2 = T ^ (1 / 5 : ℝ) := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
  have hT : T = T ^ (1 / 5 : ℝ) * T ^ (4 / 5 : ℝ) := by
    rw [← Real.rpow_add hT0]; norm_num
  have h2 : 48 * T ^ (1 / 5 : ℝ) ≤ T := by
    calc 48 * T ^ (1 / 5 : ℝ) ≤ T ^ (4 / 5 : ℝ) * T ^ (1 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_right hT45 (by positivity)
      _ = T := by rw [mul_comm, ← hT]
  have h3 : 0 ≤ T ^ (1 / 2 : ℝ) := by positivity
  nlinarith


/-- **The width-`p/2` Lorentz mass is `≤ 1/4` for large `p`.** -/
theorem exists_lorentzMassW_le_quarter :
    ∃ p₁ : ℝ, ∀ p, p₁ ≤ p → lorentzMassW (p / 2) p ≤ 1 / 4 := by
  set C₀ := xiLineTwoLogDerivConstant
  refine ⟨65536 + 128 * (|C₀| + 1), fun p hp => ?_⟩
  have hC0 : 0 ≤ |C₀| := abs_nonneg _
  have hp8 : 65536 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  refine (lorentzMassW_le_log (by linarith) p).trans ?_
  rw [abs_of_pos hp0]
  set s := p ^ (1 / 2 : ℝ) with hs
  have hss : s * s = p := by rw [hs, ← Real.rpow_add hp0]; norm_num
  have hs256 : 256 ≤ s := by
    rw [hs, show (256 : ℝ) = 65536 ^ (1 / 2 : ℝ) by
      rw [show (65536 : ℝ) = 256 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num]
    exact Real.rpow_le_rpow (by norm_num) hp8 (by norm_num)
  have hlog1 : Real.log (p / 2 + p + 4) ≤ Real.log (2 * p) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog2 : Real.log (2 * p) = Real.log 2 + Real.log p := Real.log_mul (by norm_num) hp0.ne'
  have hlog3 : Real.log p ≤ s / (1 / 2) := Real.log_le_rpow_div hp0.le (by norm_num)
  have hlog4 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hbound : C₀ + Real.log (p / 2 + p + 4) ≤ (|C₀| + 1) + 2 * s := by
    have := le_abs_self C₀
    linarith
  have h8 : (8 : ℝ) / (p / 2) = 16 / p := by field_simp; norm_num
  rw [h8]
  calc 16 / p * (C₀ + Real.log (p / 2 + p + 4)) ≤ 16 / p * ((|C₀| + 1) + 2 * s) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 16 * (|C₀| + 1) / p + 32 / s := by
        rw [← hss]; field_simp; ring
    _ ≤ 1 / 8 + 1 / 8 := by
        have ha : 16 * (|C₀| + 1) / p ≤ 1 / 8 := by rw [div_le_iff₀ hp0]; linarith
        have hb : 32 / s ≤ 1 / 8 := by rw [div_le_iff₀ (by linarith)]; linarith
        linarith
    _ = 1 / 4 := by norm_num

theorem eventually_lorentzMassW_le :
    ∀ᶠ T : ℝ in atTop, ∀ p, 3 * T ^ (1 / 2 : ℝ) - 1 ≤ p → lorentzMassW (p / 2) p ≤ 1 / 4 := by
  obtain ⟨p₁, hp₁⟩ := exists_lorentzMassW_le_quarter
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop
    (|p₁| + 1)] with T hT p hp
  exact hp₁ p (by linarith [le_abs_self p₁, abs_nonneg p₁])

/-- `(2 log T)⁴⁰ ≤ T^{1/20}` for large `T`. -/
theorem eventually_two_log_pow_le :
    ∀ᶠ T : ℝ in atTop, (2 * Real.log T) ^ (40 : ℕ) ≤ T ^ (1 / 20 : ℝ) := by
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).eventually_ge_atTop
    ((2000 : ℝ) ^ (40 : ℕ)), eventually_ge_atTop (1 : ℝ)] with T hT hT1
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog : Real.log T ≤ T ^ (1 / 1000 : ℝ) / (1 / 1000) :=
    Real.log_le_rpow_div hT0.le (by norm_num)
  have h1 : 2 * Real.log T ≤ 2000 * T ^ (1 / 1000 : ℝ) := by
    have : T ^ (1 / 1000 : ℝ) / (1 / 1000) = 1000 * T ^ (1 / 1000 : ℝ) := by field_simp
    linarith
  have h2 : (2 * Real.log T) ^ (40 : ℕ) ≤ (2000 * T ^ (1 / 1000 : ℝ)) ^ (40 : ℕ) :=
    pow_le_pow_left₀ (by positivity) h1 40
  have h3 : (2000 * T ^ (1 / 1000 : ℝ)) ^ (40 : ℕ) = (2000 : ℝ) ^ (40 : ℕ) * T ^ (1 / 25 : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast (T ^ (1 / 1000 : ℝ)), ← Real.rpow_mul hT0.le]; norm_num
  have h4 : T ^ (1 / 20 : ℝ) = T ^ (1 / 100 : ℝ) * T ^ (1 / 25 : ℝ) := by
    rw [← Real.rpow_add hT0]; norm_num
  rw [h4]
  calc (2 * Real.log T) ^ (40 : ℕ) ≤ (2000 : ℝ) ^ (40 : ℕ) * T ^ (1 / 25 : ℝ) := h2.trans h3.le
    _ ≤ T ^ (1 / 100 : ℝ) * T ^ (1 / 25 : ℝ) := mul_le_mul_of_nonneg_right hT (by positivity)

/-- **The explicit-formula bound on the whole range, under RH on the rigid window.** -/
theorem eventually_narrowMass_bound :
    ∀ᶠ T : ℝ in atTop,
      (∀ q : XiZeroCopy, T ^ (1 / 2 : ℝ) ≤ (q.1 : ℂ).im → (q.1 : ℂ).im ≤ T ^ 3 →
        (q.1 : ℂ).re = 1 / 2) →
      ∀ p, 3 * T ^ (1 / 2 : ℝ) - 1 ≤ p → p ≤ T + 1 → ∀ τ, 0 < τ → τ ≤ 1 / 2 →
        |narrowMass τ p - τ * Real.log (p / (2 * Real.pi)) / 2| ≤
          τ * ‖selbergVonMangoldtPoly (T ^ (1 / 20 : ℝ)) (narrowPoint τ p)‖ +
            2 * Real.exp (-(τ * Real.log (T ^ (1 / 20 : ℝ)))) /
              (Real.log (T ^ (1 / 20 : ℝ)) * τ) * narrowMass τ p + 2 * τ +
            4 * τ * lorentzMassW (p / 2) p := by
  obtain ⟨t₀, hV3⟩ := exists_abs_narrowMass_sub_le
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop
      (|t₀| + 10), eventually_two_log_pow_le, eventually_ge_atTop (2 : ℝ)]
    with T hsT hlogT hT2 hRH p hp1 hp2 τ hτ0 hτ1
  have hT0 : 0 < T := by linarith
  set s := T ^ (1 / 2 : ℝ) with hs
  have hs0 : 0 ≤ s := by positivity
  have hp : s ≤ p := by linarith [abs_nonneg t₀]
  have hp0 : 0 < p := by linarith [abs_nonneg t₀]
  refine hV3 p (by linarith [le_abs_self t₀]) (T ^ (1 / 20 : ℝ)) ?_ ?_ τ hτ0 hτ1 ?_
  · -- `(log p)⁴⁰ ≤ x`
    have hlp0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith [abs_nonneg t₀])
    have hlp : Real.log p ≤ 2 * Real.log T := by
      have h1 : Real.log p ≤ Real.log (T * T) := Real.log_le_log hp0 (by nlinarith)
      rw [Real.log_mul hT0.ne' hT0.ne'] at h1
      linarith
    exact (pow_le_pow_left₀ hlp0 hlp 40).trans hlogT
  · -- `x ≤ p^{1/8}`
    have h1 : T ^ (1 / 20 : ℝ) ≤ T ^ (1 / 16 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h2 : T ^ (1 / 16 : ℝ) = s ^ ((1 : ℝ) / 8) := by
      rw [hs, ← Real.rpow_mul hT0.le]; norm_num
    have h3 : s ^ ((1 : ℝ) / 8) ≤ p ^ ((1 : ℝ) / 8) := Real.rpow_le_rpow hs0 hp (by norm_num)
    linarith
  · -- local RH around `p`
    intro q hq
    rw [abs_le] at hq
    have hT3 : 2 * T + 4 ≤ T ^ 3 := by
      have : 4 ≤ T * T := by nlinarith
      nlinarith
    have hs10 : 10 ≤ s := by linarith [abs_nonneg t₀]
    exact hRH q (by linarith) (by linarith)

end RHTower

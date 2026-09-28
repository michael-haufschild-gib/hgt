import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryRateLower
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryRateUpper
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryMoments
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.VacuumWeightBound

/-!
# The exact exponential rate of the recovery gaps

With `θ ∈ (0, π/2)` the solution of `2(π - θ) = 3π sin θ`, `b = cos θ` and
`ρ = (b²/16) exp((2/π)∫_0^{π/2} log(1 - b cos s) ds) ∈ (0, 1/16)`:

* the weighted Chebyshev norms satisfy `t_m^{1/m} → ρ`
  (from `ρ^m ≤ t_m ≤ 2^K 4^{⌊m/K⌋+1} ρ^m`);
* eventually `1/8 < S_m < m/4` for the root sums, since `4^m t_m ≥ 1 - 4 S_m`;
* **the recovery gaps satisfy `δ_k^{1/k} → ρ`**, from `δ_k = t_{k+1}/S_{k+1}`.

Consequences: if the gap ratios `w_k = δ_{k+1}/δ_k` are nondecreasing, then `w_k ≤ ρ` for every
`k` and `w_k → ρ`; if `γ_n = (δ_n/δ_0)²` are the moments of a probability measure `ν` on `ℝ`, then
`ρ²` is the largest point of the support of `ν`, and if moreover `ν` lives on `[0, ∞)`, the scaled
sequence `γ_n/ρ^{2n}` satisfies every Hausdorff finite-difference inequality.
-/

open MeasureTheory Set Filter Polynomial
open scoped Real Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-! ### A limit lemma -/

/-- Two-sided bounds `ρ^m ≤ x_m ≤ 2^K 4^{⌊m/K⌋+1} ρ^m` (all `1 ≤ K ≤ m`) force
`log x_m / m → log ρ`. -/
theorem tendsto_log_div_of_rate_bounds {x : ℕ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hlow : ∀ m, 1 ≤ m → ρ ^ m ≤ x m)
    (hup : ∀ K m, 1 ≤ K → K ≤ m → x m ≤ 2 ^ K * 4 ^ (m / K + 1) * ρ ^ m) :
    Tendsto (fun m : ℕ => Real.log (x m) / m) atTop (𝓝 (Real.log ρ)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have h := Real.log_le_log (pow_pos hρ m) (hlow m hm)
    rw [Real.log_pow] at h
    rw [lt_div_iff₀ hmR]
    nlinarith
  · intro a ha
    set η := a - Real.log ρ with hη
    have hηpos : 0 < η := by rw [hη]; linarith
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    obtain ⟨K, hK⟩ := exists_nat_gt (2 * Real.log 4 / η)
    have hKpos : (0 : ℝ) < K := lt_trans (by positivity) hK
    have hK1 : 1 ≤ K := by exact_mod_cast hKpos
    have hK4 : Real.log 4 / K < η / 2 := by
      rw [div_lt_iff₀ hKpos]
      rw [div_lt_iff₀ hηpos] at hK
      linarith
    have hlim := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (K * Real.log 2 + Real.log 4)
    filter_upwards [eventually_ge_atTop K, hlim.eventually (gt_mem_nhds (half_pos hηpos))]
      with m hKm hsmall
    have hm1 : 1 ≤ m := hK1.trans hKm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
    have hxpos : 0 < x m := lt_of_lt_of_le (pow_pos hρ m) (hlow m hm1)
    have hup' := Real.log_le_log hxpos (hup K m hK1 hKm)
    rw [Real.log_mul (by positivity) (pow_pos hρ m).ne', Real.log_mul (by positivity)
      (by positivity), Real.log_pow, Real.log_pow, Real.log_pow] at hup'
    have hdiv : ((m / K : ℕ) : ℝ) ≤ (m : ℝ) / K := Nat.cast_div_le
    have hsmall' : K * Real.log 2 + Real.log 4 < η / 2 * m := by
      rwa [div_lt_iff₀ hmR] at hsmall
    have hK4' : (m : ℝ) / K * Real.log 4 < η / 2 * m := by
      have := mul_lt_mul_of_pos_left hK4 hmR
      calc (m : ℝ) / K * Real.log 4 = m * (Real.log 4 / K) := by ring
        _ < m * (η / 2) := this
        _ = η / 2 * m := by ring
    rw [div_lt_iff₀ hmR]
    push_cast at hup'
    have h4 : ((m / K : ℕ) : ℝ) * Real.log 4 ≤ (m : ℝ) / K * Real.log 4 :=
      mul_le_mul_of_nonneg_right hdiv hlog4.le
    nlinarith

/-! ### The optimizer norms -/

theorem cubicChebyshev_norm_pos {m : ℕ} {T : Polynomial ℝ} (hT : IsCubicChebyshev m T) :
    0 < cubicWeightedIntervalNorm m T := by
  obtain ⟨T₀, hT₀, hT₀pos⟩ := exists_isCubicChebyshev m
  exact lt_of_lt_of_le hT₀pos (hT₀.2.2 T hT.1 hT.2.1)

/-- **`t_m^{1/m} → ρ`** for any choice of optimizers. -/
theorem tendsto_log_cubicChebyshev_norm {T : ℕ → Polynomial ℝ}
    (hT : ∀ m, IsCubicChebyshev m (T m)) :
    Tendsto (fun m : ℕ => Real.log (cubicWeightedIntervalNorm m (T m)) / m) atTop
      (𝓝 (Real.log recoveryRate)) :=
  tendsto_log_div_of_rate_bounds recoveryRate_bounds.1
    (fun m hm => recoveryRate_pow_le hm (hT m))
    (fun _ _ hK hKm => cubicChebyshev_norm_le (hT _) hK hKm)

theorem tendsto_cubicChebyshev_norm_rate {T : ℕ → Polynomial ℝ}
    (hT : ∀ m, IsCubicChebyshev m (T m)) :
    Tendsto (fun m : ℕ => cubicWeightedIntervalNorm m (T m) ^ (1 / (m : ℝ))) atTop
      (𝓝 recoveryRate) := by
  have h := (Real.continuous_exp.tendsto _).comp (tendsto_log_cubicChebyshev_norm hT)
  rw [Function.comp_def, Real.exp_log recoveryRate_bounds.1] at h
  refine h.congr fun m => ?_
  rw [Real.rpow_def_of_pos (cubicChebyshev_norm_pos (hT m))]
  ring_nf

/-! ### The root sums -/

/-- **`4^m ‖T‖_m ≥ 1 - 4 S`** for `T = ∏ (X - r_i)` with `m` roots in `(0, 1/4)` summing to `S`,
from `‖T‖_m ≥ |T(1/4)| = 4^{-m} ∏(1 - 4 r_i)`. -/
theorem one_sub_four_rootSum_le {m : ℕ} {T : Polynomial ℝ} {s : Finset ℝ} (hcard : s.card = m) (hroots : ∀ r ∈ s, 0 < r ∧ r < 1 / 4)
    (hprod : T = ∏ r ∈ s, (X - C r)) :
    1 - 4 * ∑ r ∈ s, r ≤ 4 ^ m * cubicWeightedIntervalNorm m T := by
  have hbdd : BddAbove ((fun r : ℝ => cubicRadialWeight r ^ m * |T.eval r|) '' Icc 0 (1 / 4)) :=
    (isCompact_Icc.image_of_continuousOn ((cubicRadialWeight_continuous.pow m).mul
      (T.continuous.abs)).continuousOn).bddAbove
  have hle := le_csSup hbdd ⟨1 / 4, ⟨by norm_num, le_rfl⟩, rfl⟩
  have hW : cubicRadialWeight (1 / 4) = 1 := by
    simp [cubicRadialWeight]
  simp only [hW, one_pow, one_mul] at hle
  have hval : 4 ^ m * |T.eval (1 / 4)| = ∏ r ∈ s, (1 - 4 * r) := by
    rw [hprod, eval_prod, Finset.abs_prod, ← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r hr => ?_
    simp only [eval_sub, eval_X, eval_C]
    rw [abs_of_pos (by linarith [(hroots r hr).2])]
    ring
  have hW' := GaloisForLFunctions.HTGeometry.one_sub_sum_le_prod_one_sub s (fun r => 4 * r)
    (fun r hr => by linarith [(hroots r hr).1]) (fun r hr => by linarith [(hroots r hr).2])
  rw [← Finset.mul_sum] at hW'
  calc 1 - 4 * ∑ r ∈ s, r ≤ ∏ r ∈ s, (1 - 4 * r) := hW'
    _ = 4 ^ m * |T.eval (1 / 4)| := hval.symm
    _ ≤ 4 ^ m * cubicWeightedIntervalNorm m T :=
        mul_le_mul_of_nonneg_left hle (by positivity)

/-- `4^m t_m → 0`. -/
theorem tendsto_four_pow_mul_cubicChebyshev_norm {T : ℕ → Polynomial ℝ}
    (hT : ∀ m, IsCubicChebyshev m (T m)) :
    Tendsto (fun m : ℕ => 4 ^ m * cubicWeightedIntervalNorm m (T m)) atTop (𝓝 0) := by
  have hρ := recoveryRate_bounds
  have hlim : Tendsto (fun m : ℕ => 32 * (16 * recoveryRate) ^ m) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith [hρ.1] : 0 ≤ 16 * recoveryRate)
      (by linarith [hρ.2])).const_mul 32
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun m =>
    mul_nonneg (by positivity) (cubicChebyshev_norm_pos (hT m)).le) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with m hm
  have h := cubicChebyshev_norm_le (hT m) le_rfl hm
  simp only [pow_one, Nat.div_one] at h
  calc (4 : ℝ) ^ m * cubicWeightedIntervalNorm m (T m)
      ≤ 4 ^ m * (2 * 4 ^ (m + 1) * recoveryRate ^ m) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 8 * (16 * recoveryRate) ^ m := by
        rw [mul_pow, pow_succ, show (16 : ℝ) ^ m = 4 ^ m * 4 ^ m by rw [← mul_pow]; norm_num]
        ring
    _ ≤ 32 * (16 * recoveryRate) ^ m := by
        have : 0 ≤ (16 * recoveryRate) ^ m := pow_nonneg (by linarith [hρ.1]) m
        linarith

/-- **Eventually `1/8 < S_m`** for the root sums of the optimizers. -/
theorem eventually_rootSum_gt {T : ℕ → Polynomial ℝ} (hT : ∀ m, IsCubicChebyshev m (T m)) :
    ∀ᶠ m in atTop, ∀ s : Finset ℝ, s.card = m → (∀ r ∈ s, 0 < r ∧ r < 1 / 4) →
      T m = ∏ r ∈ s, (X - C r) → 1 / 8 < ∑ r ∈ s, r := by
  filter_upwards [(tendsto_four_pow_mul_cubicChebyshev_norm hT).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with m hm s hcard hroots hprod
  have := one_sub_four_rootSum_le hcard hroots hprod
  linarith

/-! ### The recovery gaps -/

/-- **The exponential rate** `log δ_k / k → log ρ`. -/
theorem tendsto_log_cubicGradedRecoveryGap :
    Tendsto (fun k : ℕ => Real.log (cubicGradedRecoveryGap k) / k) atTop
      (𝓝 (Real.log recoveryRate)) := by
  choose T s hT hTpos hcard hroots hprod hSpos hgap _ using cubicGradedRecoveryGap_eq_rootSum
  -- a full optimizer family, agreeing with `T` in degrees `k + 1`
  set U : ℕ → Polynomial ℝ := fun m => if h : m = 0 then Classical.choose
    (exists_isCubicChebyshev 0) else T (m - 1) with hU
  have hUopt : ∀ m, IsCubicChebyshev m (U m) := fun m => by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [hU, dif_pos rfl]; exact (Classical.choose_spec (exists_isCubicChebyshev 0)).1
    · simp only [hU, dif_neg hm.ne']
      have := hT (m - 1); rwa [Nat.sub_add_cancel hm] at this
  have hUk : ∀ k, U (k + 1) = T k := fun k => by simp [hU]
  -- `log t_{k+1} / k → log ρ`
  have ht : Tendsto (fun k : ℕ => Real.log (cubicWeightedIntervalNorm (k + 1) (T k)) / k) atTop
      (𝓝 (Real.log recoveryRate)) := by
    have h1 := (tendsto_add_atTop_iff_nat 1).mpr (tendsto_log_cubicChebyshev_norm hUopt)
    have h2 : Tendsto (fun k : ℕ => (k : ℝ) / (k + 1)) atTop (𝓝 1) :=
      tendsto_natCast_div_add_atTop (1 : ℝ)
    have h3 := h1.div h2 one_ne_zero
    rw [div_one] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk)
    simp only [Pi.div_apply, hUk]
    push_cast
    field_simp
  -- `log S / k → 0`
  have hS : Tendsto (fun k : ℕ => Real.log (∑ r ∈ s k, r) / k) atTop (𝓝 0) := by
    have hlow : Tendsto (fun k : ℕ => Real.log (1 / 8) / (k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have hup : Tendsto (fun k : ℕ => (Real.log ((k : ℝ) + 1) - Real.log 4) / k) atTop (𝓝 0) := by
      have hl : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) / k) atTop (𝓝 0) := by
        have := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
          (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
        refine this.congr fun k => ?_
        simp
      have := hl.sub (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (Real.log 4))
      rw [sub_zero] at this
      exact this.congr fun k => by ring
    have hev := (tendsto_add_atTop_nat 1).eventually (eventually_rootSum_gt hUopt)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
      have hk' := hk (s k) (hcard k) (hroots k) (by rw [hUk]; exact hprod k)
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
      exact div_le_div_of_nonneg_right (Real.log_le_log (by norm_num) hk'.le) hkR.le
    · filter_upwards [eventually_ge_atTop 1] with k hk1
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
      have hlt : ∑ r ∈ s k, r ≤ ((k : ℝ) + 1) / 4 := by
        calc ∑ r ∈ s k, r ≤ ∑ _r ∈ s k, (1 / 4 : ℝ) :=
              Finset.sum_le_sum fun r hr => (hroots k r hr).2.le
          _ = ((k : ℝ) + 1) / 4 := by rw [Finset.sum_const, hcard k]; simp; ring
      refine div_le_div_of_nonneg_right ?_ hkR.le
      rw [← Real.log_div (by positivity) (by norm_num)]
      exact Real.log_le_log (hSpos k) hlt
  have h := ht.sub hS
  rw [sub_zero] at h
  refine h.congr fun k => ?_
  rw [hgap k, Real.log_div (hTpos k).ne' (hSpos k).ne', sub_div]

/-- **`lim δ_k^{1/k} = ρ`.** -/
theorem tendsto_cubicGradedRecoveryGap_rate :
    Tendsto (fun k : ℕ => cubicGradedRecoveryGap k ^ (1 / (k : ℝ))) atTop (𝓝 recoveryRate) := by
  have h := (Real.continuous_exp.tendsto _).comp tendsto_log_cubicGradedRecoveryGap
  rw [Function.comp_def, Real.exp_log recoveryRate_bounds.1] at h
  refine h.congr fun k => ?_
  rw [Real.rpow_def_of_pos (cubicGradedRecoveryGap_positive k)]
  ring_nf

/-! ### Consequences -/

/-- **Log-convex gaps.**  If the ratios `w_k = δ_{k+1}/δ_k` are nondecreasing, then every
`w_k ≤ ρ` and `w_k → ρ`. -/
theorem cubicGradedRecoveryGap_ratio_of_monotone
    (hmono : Monotone fun k => cubicGradedRecoveryGap (k + 1) / cubicGradedRecoveryGap k) :
    (∀ k, cubicGradedRecoveryGap (k + 1) / cubicGradedRecoveryGap k ≤ recoveryRate) ∧
      Tendsto (fun k => cubicGradedRecoveryGap (k + 1) / cubicGradedRecoveryGap k) atTop
        (𝓝 recoveryRate) := by
  set δ := cubicGradedRecoveryGap with hδ
  set w : ℕ → ℝ := fun k => δ (k + 1) / δ k with hw
  have hδpos : ∀ k, 0 < δ k := cubicGradedRecoveryGap_positive
  have hwpos : ∀ k, 0 < w k := fun k => div_pos (hδpos _) (hδpos _)
  have hprodw : ∀ k, δ k = δ 0 * ∏ i ∈ Finset.range k, w i := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ← ih, hw]
      field_simp [(hδpos k).ne']
  -- every ratio is at most `ρ`
  have hle : ∀ j, w j ≤ recoveryRate := by
    intro j
    rw [← Real.log_le_log_iff (hwpos j) recoveryRate_bounds.1]
    have hlow : ∀ k, j ≤ k → Real.log (δ j) + (k - j) * Real.log (w j) ≤ Real.log (δ k) := by
      intro k hjk
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjk
      clear hjk
      have hδjn : δ j * w j ^ n ≤ δ (j + n) := by
        induction n with
        | zero => simp
        | succ n ih =>
          have hstep : δ (j + n + 1) = δ (j + n) * w (j + n) := by
            simp only [hw]; field_simp [(hδpos (j + n)).ne']
          rw [← add_assoc, hstep, pow_succ, ← mul_assoc]
          exact mul_le_mul ih (hmono (Nat.le_add_right j n)) (hwpos j).le (hδpos _).le
      have := Real.log_le_log (by have := hwpos j; have := hδpos j; positivity) hδjn
      rw [Real.log_mul (hδpos j).ne' (pow_pos (hwpos j) n).ne', Real.log_pow] at this
      push_cast
      linarith
    have hlim : Tendsto (fun k : ℕ => (Real.log (δ j) + (k - j) * Real.log (w j)) / k) atTop
        (𝓝 (Real.log (w j))) := by
      have h1 := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ)
        (Real.log (δ j) - j * Real.log (w j))
      have h2 := h1.add_const (Real.log (w j))
      rw [zero_add] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk)
      field_simp
      ring
    refine le_of_tendsto_of_tendsto hlim tendsto_log_cubicGradedRecoveryGap ?_
    filter_upwards [eventually_ge_atTop (max j 1)] with k hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast (le_of_max_le_right hk)
    exact div_le_div_of_nonneg_right (hlow k (le_of_max_le_left hk)) hkR.le
  refine ⟨hle, ?_⟩
  -- the limit
  have hbdd : BddAbove (Set.range w) := ⟨recoveryRate, by rintro _ ⟨k, rfl⟩; exact hle k⟩
  have hconv := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ k, w k with hL
  have hLle : L ≤ recoveryRate := ciSup_le hle
  have hLpos : 0 < L := lt_of_lt_of_le (hwpos 0) (le_ciSup hbdd 0)
  have hge : recoveryRate ≤ L := by
    rw [← Real.log_le_log_iff recoveryRate_bounds.1 hLpos]
    have hup : ∀ k, Real.log (δ k) ≤ Real.log (δ 0) + k * Real.log L := fun k => by
      have hδk : δ k ≤ δ 0 * L ^ k := by
        rw [hprodw k]
        refine mul_le_mul_of_nonneg_left ?_ (hδpos 0).le
        calc ∏ i ∈ Finset.range k, w i ≤ ∏ _i ∈ Finset.range k, L :=
              Finset.prod_le_prod (fun i _ => (hwpos i).le) fun i _ => le_ciSup hbdd i
          _ = L ^ k := by rw [Finset.prod_const, Finset.card_range]
      have := Real.log_le_log (hδpos k) hδk
      rwa [Real.log_mul (hδpos 0).ne' (pow_pos hLpos k).ne', Real.log_pow] at this
    have hlim : Tendsto (fun k : ℕ => (Real.log (δ 0) + k * Real.log L) / k) atTop
        (𝓝 (Real.log L)) := by
      have h2 := (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (Real.log (δ 0))).add_const
        (Real.log L)
      rw [zero_add] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk)
      field_simp
    refine le_of_tendsto_of_tendsto tendsto_log_cubicGradedRecoveryGap hlim ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    exact div_le_div_of_nonneg_right (hup k) hkR.le
  rwa [le_antisymm hLle hge] at hconv

/-- `log γ_n / n → 2 log ρ` for the normalized squared gaps `γ_n = (δ_n/δ_0)²`. -/
theorem tendsto_log_cubicRecoveryMoment :
    Tendsto (fun n : ℕ => Real.log (cubicRecoveryMoment n) / n) atTop
      (𝓝 (Real.log (recoveryRate ^ 2))) := by
  have h := (tendsto_log_cubicGradedRecoveryGap.sub (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    (Real.log (cubicGradedRecoveryGap 0)))).const_mul 2
  rw [sub_zero] at h
  rw [Real.log_pow]
  push_cast
  refine h.congr fun n => ?_
  rw [cubicRecoveryMoment, Real.log_pow, Real.log_div (cubicGradedRecoveryGap_positive n).ne'
    (cubicGradedRecoveryGap_positive 0).ne']
  push_cast
  ring

/-- **The largest support point of a representing measure is `ρ²`.**  If a probability measure
`ν` on `ℝ` has moments `∫ x^n dν = γ_n = (δ_n/δ_0)²`, then `ν(ρ², ∞) = 0` and every neighbourhood
of `ρ²` has positive `ν`-measure. -/
theorem cubicRecoveryMoment_support_max (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmom : ∀ n : ℕ, ∫ x, x ^ n ∂ν = cubicRecoveryMoment n) :
    ν (Ioi (recoveryRate ^ 2)) = 0 ∧
      ∀ ε > 0, 0 < ν (Ioo (recoveryRate ^ 2 - ε) (recoveryRate ^ 2 + ε)) := by
  set M := recoveryRate ^ 2 with hM
  have hMpos : 0 < M := by have := recoveryRate_bounds.1; positivity
  have hγpos : ∀ n, 0 < cubicRecoveryMoment n := fun n => by
    rw [cubicRecoveryMoment]
    exact pow_pos (div_pos (cubicGradedRecoveryGap_positive n)
      (cubicGradedRecoveryGap_positive 0)) 2
  have hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) ν := fun n => by
    by_contra h
    have := integral_undef h
    rw [hmom n] at this
    exact (hγpos n).ne' this
  have hlim := tendsto_log_cubicRecoveryMoment
  -- no mass above `M`
  have hnull : ν (Ioi M) = 0 := by
    by_contra hne
    have hunion : Ioi M = ⋃ j : ℕ, Ioi (M + 1 / ((j : ℝ) + 1)) := by
      ext x
      simp only [mem_Ioi, mem_iUnion]
      constructor
      · intro hx
        obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
        exact ⟨j, by linarith⟩
      · rintro ⟨j, hj⟩
        have : 0 < 1 / ((j : ℝ) + 1) := by positivity
        linarith
    obtain ⟨j, hj⟩ : ∃ j : ℕ, ν (Ioi (M + 1 / ((j : ℝ) + 1))) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (by rw [hunion]; exact measure_iUnion_null hall)
    set η := 1 / ((j : ℝ) + 1) with hη
    have hηpos : 0 < η := by positivity
    set c := ν.real (Ioi (M + η)) with hc
    have hcpos : 0 < c := by
      rw [hc, measureReal_def]
      exact ENNReal.toReal_pos hj (measure_ne_top _ _)
    -- even moments: `γ_{2n} ≥ c (M + η)^{2n}`
    have hev : ∀ n : ℕ, c * (M + η) ^ (2 * n) ≤ cubicRecoveryMoment (2 * n) := fun n => by
      rw [← hmom]
      calc c * (M + η) ^ (2 * n) = ∫ x in Ioi (M + η), (M + η) ^ (2 * n) ∂ν := by
            rw [setIntegral_const, smul_eq_mul, hc]
        _ ≤ ∫ x in Ioi (M + η), x ^ (2 * n) ∂ν := by
            refine setIntegral_mono_on (integrableOn_const (measure_ne_top _ _))
              (hint (2 * n)).integrableOn measurableSet_Ioi fun x hx => ?_
            exact pow_le_pow_left₀ (by positivity) (le_of_lt hx) _
        _ ≤ ∫ x, x ^ (2 * n) ∂ν := by
            refine setIntegral_le_integral (hint (2 * n)) (Eventually.of_forall fun x => ?_)
            show (0 : ℝ) ≤ x ^ (2 * n)
            rw [pow_mul]; positivity
    have hsub : Tendsto (fun n : ℕ => Real.log (cubicRecoveryMoment (2 * (n + 1))) /
        ((2 * (n + 1) : ℕ) : ℝ)) atTop (𝓝 (Real.log M)) :=
      hlim.comp ((tendsto_add_atTop_nat 1).const_mul_atTop' (by norm_num : 0 < 2) |>.congr
        fun n => rfl)
    have hlow : Tendsto (fun n : ℕ => (Real.log c + ((2 * (n + 1) : ℕ) : ℝ) * Real.log (M + η)) /
        ((2 * (n + 1) : ℕ) : ℝ)) atTop (𝓝 (Real.log (M + η))) := by
      have h1 := (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (Real.log c / 2)).comp
        (tendsto_add_atTop_nat 1)
      have h2 := h1.add_const (Real.log (M + η))
      rw [zero_add] at h2
      refine h2.congr fun n => ?_
      simp only [Function.comp_apply]
      push_cast
      field_simp
    have hle : Real.log (M + η) ≤ Real.log M := by
      refine le_of_tendsto_of_tendsto hlow hsub (Eventually.of_forall fun n => ?_)
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have := Real.log_le_log (by positivity) (hev (n + 1))
      rw [Real.log_mul hcpos.ne' (by positivity), Real.log_pow] at this
      exact this
    have := Real.log_lt_log hMpos (by linarith : M < M + η)
    linarith
  refine ⟨hnull, fun ε hε => ?_⟩
  by_contra hzero
  push Not at hzero
  have hzero' : ν (Ioo (M - ε) (M + ε)) = 0 := nonpos_iff_eq_zero.mp hzero
  -- all mass lies in `(-∞, M - ε]`
  have hae : ∀ᵐ x ∂ν, x ≤ M - ε := by
    have hnull' : ν (Ioi (M - ε)) = 0 := by
      refine measure_mono_null (fun x hx => ?_) (measure_union_null hzero' hnull)
      simp only [mem_Ioi] at hx
      by_cases h : x < M + ε
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (by simp only [mem_Ioi]; linarith)
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) hnull'
    simp only [mem_setOf_eq, not_le] at hx
    exact hx
  rcases le_or_gt M ε with hMε | hMε
  · -- then all odd moments are nonpositive
    have hodd : cubicRecoveryMoment 1 ≤ 0 := by
      rw [← hmom 1]
      refine integral_nonpos_of_ae ?_
      filter_upwards [hae] with x hx
      simp only [pow_one, Pi.zero_apply]
      linarith
    exact absurd hodd (not_le.mpr (hγpos 1))
  -- odd moments: `γ_{2n+1} ≤ (M - ε)^{2n+1}`
  have hodd : ∀ n : ℕ, cubicRecoveryMoment (2 * n + 1) ≤ (M - ε) ^ (2 * n + 1) := fun n => by
    rw [← hmom]
    have hc : ∫ x, (M - ε) ^ (2 * n + 1) ∂ν = (M - ε) ^ (2 * n + 1) := by
      rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
    rw [← hc]
    refine integral_mono_ae (hint _) (integrable_const _) ?_
    filter_upwards [hae] with x hx
    exact (Odd.pow_le_pow ⟨n, rfl⟩).mpr hx
  have hsub : Tendsto (fun n : ℕ => Real.log (cubicRecoveryMoment (2 * n + 1)) /
      ((2 * n + 1 : ℕ) : ℝ)) atTop (𝓝 (Real.log M)) :=
    hlim.comp (tendsto_atTop_mono (fun n => show id n ≤ 2 * n + 1 by simp only [id]; omega)
      tendsto_id)
  have hle : Real.log M ≤ Real.log (M - ε) := by
    refine le_of_tendsto_of_tendsto hsub tendsto_const_nhds (Eventually.of_forall fun n => ?_)
    rw [div_le_iff₀ (by positivity)]
    have := Real.log_le_log (hγpos _) (hodd n)
    rw [Real.log_pow] at this
    linarith
  have := Real.log_lt_log (by linarith) (by linarith : M - ε < M)
  linarith

/-- **Hausdorff inequalities.**  If moreover `ν` lives on `[0, ∞)`, the scaled sequence
`γ_n/ρ^{2n}` satisfies every Hausdorff finite-difference inequality:
`Σ_{j ≤ k} (-1)^j C(k,j) γ_{n+j}/ρ^{2(n+j)} ≥ 0`. -/
theorem cubicRecoveryMoment_hausdorff (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmom : ∀ n : ℕ, ∫ x, x ^ n ∂ν = cubicRecoveryMoment n) (hpos : ν (Iio 0) = 0) (n k : ℕ) :
    0 ≤ ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * (k.choose j : ℝ) *
      (cubicRecoveryMoment (n + j) / (recoveryRate ^ 2) ^ (n + j)) := by
  set M := recoveryRate ^ 2 with hM
  have hMpos : 0 < M := by have := recoveryRate_bounds.1; positivity
  have hγpos : ∀ n, 0 < cubicRecoveryMoment n := fun n => by
    rw [cubicRecoveryMoment]
    exact pow_pos (div_pos (cubicGradedRecoveryGap_positive n)
      (cubicGradedRecoveryGap_positive 0)) 2
  have hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) ν := fun n => by
    by_contra h
    have := integral_undef h
    rw [hmom n] at this
    exact (hγpos n).ne' this
  have hsupp := (cubicRecoveryMoment_support_max ν hmom).1
  have hae : ∀ᵐ x ∂ν, 0 ≤ x ∧ x ≤ M := by
    have h1 : ∀ᵐ x ∂ν, x ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.mp hpos
    have h2 : ∀ᵐ x ∂ν, x ∉ Ioi M := measure_eq_zero_iff_ae_notMem.mp hsupp
    filter_upwards [h1, h2] with x hx1 hx2
    simp only [mem_Iio, not_lt, mem_Ioi, not_lt] at hx1 hx2
    exact ⟨hx1, hx2⟩
  have hexp : ∀ x : ℝ, (x / M) ^ n * (1 - x / M) ^ k =
      ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * (k.choose j : ℝ) * (x ^ (n + j) / M ^ (n + j)) :=
      fun x => by
    rw [show 1 - x / M = -(x / M) + 1 by ring, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_pow, mul_one, neg_pow]
    ring
  have hval : ∫ x, (x / M) ^ n * (1 - x / M) ^ k ∂ν =
      ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * (k.choose j : ℝ) *
        (cubicRecoveryMoment (n + j) / M ^ (n + j)) := by
    simp_rw [hexp]
    rw [integral_finsetSum _ fun j _ => ((hint (n + j)).div_const _).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_div, hmom]
  rw [← hval]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hae] with x hx
  have h1 : 0 ≤ x / M := div_nonneg hx.1 hMpos.le
  have h2 : 0 ≤ 1 - x / M := by rw [sub_nonneg, div_le_one hMpos]; exact hx.2
  simp only [Pi.zero_apply]
  positivity

end GaloisForLFunctions.HTGeometry.ChronologicalTensor

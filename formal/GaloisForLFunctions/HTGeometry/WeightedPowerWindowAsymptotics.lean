import GaloisForLFunctions.HTGeometry.WeightedPowerWindowCompression

/-!
# Sublinear loud rank absorbs the Turán loss

An amplitude budget `m W` at level `m^δ` gives rank at most `W m^(1-δ)`.
Its Turán cost is subexponential in `m`, uniformly over every admissible rank.
The resulting observation window has length at most `m / log(m+1)`.
-/

open Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem weightedTuranLoss_le_quadratic_base {m n : ℕ} (hm : 1 ≤ m) (hn : n ≤ m) :
    weightedTuranLoss m n ≤
      2 * Real.exp 1 * m * (60 * (m : ℝ) ^ 2) ^ n := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (n : ℝ) ≤ m := by exact_mod_cast hn
  have hb : 6 * ((n : ℝ) + 1) * ((m : ℝ) + 2 * n + 2) ≤ 60 * (m : ℝ) ^ 2 := by
    calc
      _ ≤ 6 * (2 * (m : ℝ)) * (5 * m) := by gcongr <;> linarith
      _ = _ := by ring
  unfold weightedTuranLoss
  calc
    _ ≤ 2 * (Real.exp 1 * m * (60 * (m : ℝ) ^ 2) ^ n) := by gcongr
    _ = _ := by ring

/-- Both the exponential loss and the logarithmically short window are paid for by the
same loud-rank mass bound, uniformly in the rank. -/
theorem eventually_weightedTuran_budget {W δ : ℝ} (hW : 0 < W) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, 1 ≤ m ∧
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) * (m : ℝ) ^ δ ≤ (m : ℝ) * W →
        (n : ℝ) ≤ (m : ℝ) / Real.log ((m : ℝ) + 1) ∧
        8 * W * m * weightedTuranLoss m n ≤ (2 : ℝ) ^ (m + 1) := by
  have hx : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_atTop hδ).comp hx
  have hi : Tendsto (fun m : ℕ => 1 / (m : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Pi.inv_def] using hx.inv_tendsto_atTop
  have hpi : Tendsto (fun m : ℕ => 1 / (m : ℝ) ^ δ) atTop (𝓝 0) := by
    simpa only [one_div, Pi.inv_def, Function.comp_def] using hp.inv_tendsto_atTop
  have hl : Tendsto (fun m : ℕ => Real.log (m : ℝ) / (m : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero.comp hx
  have hld : Tendsto (fun m : ℕ => Real.log (m : ℝ) / (m : ℝ) ^ δ) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero.comp hx
  let C : ℝ := 16 * Real.exp 1 * W
  have hC : 0 < C := by dsimp [C]; positivity
  have he : Tendsto (fun m : ℕ =>
      (Real.log C + 2 * Real.log m) / (m : ℝ) +
        W * (Real.log 60 + 2 * Real.log m) / (m : ℝ) ^ δ) atTop (𝓝 0) := by
    convert ((hi.const_mul (Real.log C)).add (hl.const_mul 2)).add
      (((hpi.const_mul (Real.log 60)).add (hld.const_mul 2)).const_mul W) using 1 <;>
      try simp only [mul_zero, add_zero]
    funext m
    ring
  have hf : Tendsto (fun m : ℕ =>
      W * (Real.log 2 + Real.log m) / (m : ℝ) ^ δ) atTop (𝓝 0) := by
    convert ((hpi.const_mul (Real.log 2)).add hld).const_mul W using 1 <;>
      try simp only [mul_zero, add_zero]
    funext m
    ring
  filter_upwards [he.eventually (gt_mem_nhds (Real.log_pos (by norm_num : (1 : ℝ) < 2))),
    hf.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hp.eventually (eventually_ge_atTop W), eventually_ge_atTop 2] with m he hf hp hm
  have hm1 : 1 ≤ m := by omega
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hm0 : (0 : ℝ) < m := by linarith
  have hmp : 0 < (m : ℝ) ^ δ := Real.rpow_pos_of_pos hm0 _
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm'
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog60 : 0 < Real.log (60 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨hm1, fun n hn hcard => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  change W ≤ (m : ℝ) ^ δ at hp
  have hnm : (n : ℝ) ≤ m := by
    nlinarith [mul_le_mul_of_nonneg_left hp hn0]
  have hnmNat : n ≤ m := by exact_mod_cast hnm
  have hnr : (n : ℝ) ≤ (m : ℝ) * W / (m : ℝ) ^ δ := (le_div_iff₀ hmp).2 hcard
  constructor
  · have hlogm1 : 0 < Real.log ((m : ℝ) + 1) := Real.log_pos (by linarith)
    have hlogup : Real.log ((m : ℝ) + 1) ≤ Real.log 2 + Real.log m := by
      calc
        _ ≤ Real.log (2 * (m : ℝ)) := Real.log_le_log (by positivity) (by linarith)
        _ = _ := Real.log_mul (by norm_num) hm0.ne'
    rw [le_div_iff₀ hlogm1]
    calc
      (n : ℝ) * Real.log ((m : ℝ) + 1) ≤
          ((m : ℝ) * W / (m : ℝ) ^ δ) * (Real.log 2 + Real.log m) :=
        mul_le_mul hnr hlogup hlogm1.le (by positivity)
      _ = (W * (Real.log 2 + Real.log m) / (m : ℝ) ^ δ) * m := by ring
      _ ≤ 1 * (m : ℝ) := mul_le_mul_of_nonneg_right hf.le hm0.le
      _ = _ := one_mul _
  · have hbase : 0 < 60 * (m : ℝ) ^ 2 := by positivity
    have hmajor : 0 < C * (m : ℝ) ^ 2 * (60 * (m : ℝ) ^ 2) ^ n := by positivity
    have hlogBase : Real.log (60 * (m : ℝ) ^ 2) = Real.log 60 + 2 * Real.log m := by
      rw [Real.log_mul (by norm_num : (60 : ℝ) ≠ 0) (pow_ne_zero 2 hm0.ne'),
        Real.log_pow]
      norm_num
    have hlogMajor : Real.log (C * (m : ℝ) ^ 2 * (60 * (m : ℝ) ^ 2) ^ n) =
        Real.log C + 2 * Real.log m + (n : ℝ) * (Real.log 60 + 2 * Real.log m) := by
      rw [Real.log_mul (mul_ne_zero hC.ne' (pow_ne_zero 2 hm0.ne'))
          (pow_ne_zero n hbase.ne'),
        Real.log_mul hC.ne' (pow_ne_zero 2 hm0.ne'), Real.log_pow, Real.log_pow, hlogBase]
      norm_num
    have hlogBound : Real.log (C * (m : ℝ) ^ 2 * (60 * (m : ℝ) ^ 2) ^ n) ≤
        (m : ℝ) * Real.log 2 := by
      rw [hlogMajor]
      calc
        _ ≤ Real.log C + 2 * Real.log m +
            ((m : ℝ) * W / (m : ℝ) ^ δ) * (Real.log 60 + 2 * Real.log m) := by
          gcongr
        _ = ((Real.log C + 2 * Real.log m) / (m : ℝ) +
            W * (Real.log 60 + 2 * Real.log m) / (m : ℝ) ^ δ) * m := by
          field_simp
        _ ≤ Real.log 2 * (m : ℝ) := mul_le_mul_of_nonneg_right he.le hm0.le
        _ = _ := mul_comm _ _
    have hmajorBound : C * (m : ℝ) ^ 2 * (60 * (m : ℝ) ^ 2) ^ n ≤
        (2 : ℝ) ^ (m + 1) := by
      apply (Real.log_le_log_iff hmajor (by positivity)).mp
      refine hlogBound.trans ?_
      rw [Real.log_pow]
      push_cast
      nlinarith
    calc
      8 * W * m * weightedTuranLoss m n ≤
          8 * W * m * (2 * Real.exp 1 * m * (60 * (m : ℝ) ^ 2) ^ n) :=
        mul_le_mul_of_nonneg_left (weightedTuranLoss_le_quadratic_base hm1 hnmNat)
          (by positivity)
      _ = C * (m : ℝ) ^ 2 * (60 * (m : ℝ) ^ 2) ^ n := by dsimp [C]; ring
      _ ≤ _ := hmajorBound

/-- A polynomially loud mode is detected in a logarithmically short moving power window.
Summability and a fixed weight cone discharge the full complementary tail. -/
theorem eventually_exists_short_weighted_power_window {ι : Type*}
    (b : ℕ → ι → ℂ) (w : ι → ℂ) (hw : Summable fun i => ‖w i‖)
    (hW : 0 < ∑' i, ‖w i‖) (hcone : ∀ i, ‖w i‖ / 2 ≤ (w i).re)
    (hdom : ∀ m : ℕ, 1 ≤ m → ∀ i, ‖b m i‖ ≤ (m : ℝ) * ‖w i‖)
    {δ : ℝ} (hδ : 0 < δ)
    (hbig : ∀ᶠ m : ℕ in atTop, ∃ i, 2 * (m : ℝ) ^ δ ≤ ‖b m i‖) :
    ∀ᶠ m : ℕ in atTop, ∃ k : ℕ, m < k ∧
      (k : ℝ) ≤ (m : ℝ) + (m : ℝ) / Real.log ((m : ℝ) + 1) ∧
      2 * (∑' i, ‖w i‖) * ((m : ℝ) ^ δ) ^ k ≤ ‖∑' i, w i * b m i ^ k‖ := by
  filter_upwards [eventually_weightedTuran_budget hW hδ, hbig] with m hm hbig
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
  obtain ⟨n, k, hn, hncard, hk0, hk1, hk2⟩ :=
    exists_weighted_power_window_of_budget (b m) w hw hcone hm0
      (Real.one_le_rpow hm1 hδ.le) (hdom m hm.1) hbig m
      (fun n hn hc => (hm.2 n hn hc).2)
  have hnr := (hm.2 n hn hncard).1
  have hkr : (k : ℝ) ≤ (m : ℝ) + n := by exact_mod_cast hk1
  exact ⟨k, hk0, by linarith, hk2⟩

end

end GaloisForLFunctions.HTGeometry

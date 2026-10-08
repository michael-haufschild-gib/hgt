import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticLogMoment
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# An actual energy limit from the logarithmic moment ceiling

The decreasing primitive and a finite secant inequality pay the density
step. No existence of the energy limit is assumed.
-/

open Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic.LogMoment

private theorem floor_power_limits {q : ℝ} (hq : 0 < q) :
    Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ q⌋₊) atTop atTop ∧
      Tendsto (fun N : ℕ => Real.log ⌊(N : ℝ) ^ q⌋₊ / Real.log N) atTop (𝓝 q) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ q) atTop atTop :=
    (tendsto_rpow_atTop hq).comp tendsto_natCast_atTop_atTop
  have hm : Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ q⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hp
  have hr := tendsto_nat_floor_div_atTop.comp hp
  have hl : Tendsto (fun N : ℕ => Real.log ((⌊(N : ℝ) ^ q⌋₊ : ℝ) / (N : ℝ) ^ q))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨hm, ?_⟩
  have ht := (tendsto_const_nhds.add (hl.div_atTop hlog) :
    Tendsto (fun N : ℕ => q + Real.log ((⌊(N : ℝ) ^ q⌋₊ : ℝ) / (N : ℝ) ^ q) / Real.log N)
      atTop (𝓝 (q + 0)))
  simp only [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [hm.eventually_ge_atTop 1, eventually_ge_atTop (2 : ℕ)] with N hM hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hM0 : (⌊(N : ℝ) ^ q⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (show ⌊(N : ℝ) ^ q⌋₊ ≠ 0 by omega)
  have hln : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
  rw [Real.log_div hM0 (ne_of_gt (Real.rpow_pos_of_pos hn q)), Real.log_rpow hn]
  field_simp
  ring

private theorem floor_power_le {q : ℝ} (hq : q ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    ⌊(N : ℝ) ^ q⌋₊ ≤ N := by
  have h := (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) q)).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hq)
  rw [Real.rpow_one] at h
  exact_mod_cast h

/-- The exact moment ceiling forces convergence of the normalized square mass. -/
theorem exists_mass_limit {w : ℕ → ℝ} {C : ℝ}
    (hw : ∀ n, 0 ≤ w n)
    (hbound : ∀ N : ℕ, 1 ≤ N → 2 * moment w N ≤ (Real.log N + C) * mass w N) :
    ∃ K : ℝ, 0 ≤ K ∧ Tendsto (fun N : ℕ => mass w N / Real.log N) atTop (𝓝 K) := by
  obtain ⟨k, hk0, _, hk⟩ := exists_primitive_limit hw hbound
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hC : Tendsto (fun N : ℕ => C / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  let upper : ℕ → ℝ := fun N =>
    (2 * (primitive w N / (Real.log N) ^ 2)) / (1 - C / Real.log N)
  have hu : Tendsto upper atTop (𝓝 (2 * k)) := by
    convert
      (hk.const_mul 2).div (tendsto_const_nhds.sub hC) (by norm_num : (1 : ℝ) - 0 ≠ 0)
      using 1
    · funext N
      rfl
    · norm_num
  have hupper : ∀ᶠ N : ℕ in atTop, mass w N / Real.log N ≤ upper N := by
    filter_upwards [hlog.eventually_gt_atTop (max C 0), eventually_ge_atTop (1 : ℕ)] with N hN hN1
    have hln : 0 < Real.log N := lt_of_le_of_lt (le_max_right _ _) hN
    have hNC : 0 < Real.log N - C := sub_pos.mpr (lt_of_le_of_lt (le_max_left _ _) hN)
    have hb : (Real.log N - C) * mass w N ≤ 2 * primitive w N := by
      have hh := hbound N hN1
      dsimp [primitive]
      linarith
    have he : upper N = 2 * primitive w N / ((Real.log N - C) * Real.log N) := by
      dsimp [upper]
      field_simp
    rw [he]
    apply (le_div_iff₀ (mul_pos hNC hln)).mpr
    calc
      _ = (Real.log N - C) * mass w N := by field_simp
      _ ≤ 2 * primitive w N := hb
  have hlower (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
      ∃ lower : ℕ → ℝ, Tendsto lower atTop (𝓝 (k * (1 + q))) ∧
        ∀ᶠ N : ℕ in atTop, lower N ≤ mass w N / Real.log N := by
    let M : ℕ → ℕ := fun N => ⌊(N : ℝ) ^ q⌋₊
    obtain ⟨hm, hr⟩ := floor_power_limits hq
    have hMlim : Tendsto (fun N : ℕ => primitive w (M N) / (Real.log N) ^ 2)
        atTop (𝓝 (k * q ^ 2)) := by
      have ht := (hk.comp hm).mul (hr.pow 2)
      refine ht.congr' ?_
      filter_upwards [hm.eventually_ge_atTop 2, eventually_ge_atTop (2 : ℕ)] with N hM hN
      have hmn : Real.log (M N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < M N by dsimp [M]; omega)))
      have hnn : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
      change primitive w (M N) / (Real.log (M N)) ^ 2 *
        (Real.log (M N) / Real.log N) ^ 2 = _
      field_simp
    let lower : ℕ → ℝ := fun N =>
      (primitive w N / (Real.log N) ^ 2 - primitive w (M N) / (Real.log N) ^ 2) /
        (1 - Real.log (M N) / Real.log N)
    have hl : Tendsto lower atTop (𝓝 (k * (1 + q))) := by
      have ht := (hk.sub hMlim).div (tendsto_const_nhds.sub hr) (by linarith : (1 : ℝ) - q ≠ 0)
      have he : (k - k * q ^ 2) / (1 - q) = k * (1 + q) := by
        field_simp [ne_of_gt (sub_pos.mpr hq1)]
        ring
      rw [he] at ht
      convert ht using 1
      funext N
      rfl
    refine ⟨lower, hl, ?_⟩
    filter_upwards [hm.eventually_ge_atTop 1, eventually_ge_atTop (2 : ℕ),
      hr.eventually (eventually_lt_nhds hq1)] with N hM hN hrN
    have hln : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hden : 0 < 1 - Real.log (M N) / Real.log N := by change _ at hrN; linarith
    have hb := primitive_sub_le hw hM (floor_power_le hq1.le (show 1 ≤ N by omega))
    have hb' : (primitive w N - primitive w (M N)) / (Real.log N) ^ 2 ≤
        (1 - Real.log (M N) / Real.log N) * (mass w N / Real.log N) := by
      apply (div_le_iff₀ (sq_pos_of_pos hln)).mpr
      calc
        _ ≤ (Real.log N - Real.log (M N)) * mass w N := hb
        _ = _ := by field_simp
    change _ / _ ≤ _
    rw [← sub_div]
    exact (div_le_iff₀ hden).mpr (by simpa [mul_comm] using hb')
  refine ⟨2 * k, by positivity, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro a ha
    by_cases hk : 0 < k
    · have hm : max 0 (a / k - 1) < 1 := by
        apply max_lt_iff.mpr
        refine ⟨by norm_num, ?_⟩
        have : a / k < 2 := (div_lt_iff₀ hk).mpr (by linarith)
        linarith
      obtain ⟨q, hq, hq1⟩ := exists_between hm
      have hq0 : 0 < q := lt_of_le_of_lt (le_max_left _ _) hq
      have haq : a < k * (1 + q) := by
        have : a / k - 1 < q := lt_of_le_of_lt (le_max_right _ _) hq
        have : a / k < 1 + q := by linarith
        have hh := (div_lt_iff₀ hk).mp this
        linarith
      obtain ⟨lower, hl, hb⟩ := hlower q hq0 hq1
      filter_upwards [hl.eventually (eventually_gt_nhds haq), hb] with N hlN hbN
      exact hlN.trans_le hbN
    · have hkz : k = 0 := le_antisymm (le_of_not_gt hk) hk0
      filter_upwards [hlog.eventually_gt_atTop 0] with N hN
      have hz := div_nonneg (mass_nonneg hw N) hN.le
      simp only [hkz, mul_zero] at ha
      exact ha.trans_le hz
  · intro b hb
    filter_upwards [hu.eventually (eventually_lt_nhds hb), hupper] with N huN hbN
    exact hbN.trans_lt huN

end RHTower.WeilSingularArithmetic.LogMoment

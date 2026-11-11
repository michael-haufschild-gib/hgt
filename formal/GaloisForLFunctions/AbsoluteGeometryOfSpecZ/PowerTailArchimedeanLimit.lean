import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailArchimedeanProfile
import GaloisForLFunctions.RHTower.CCM.CCMFirstClockWoldXiDepthCapacityNoGo

/-!
# The archimedean limit of a power comb

The newest jet row has a limiting regular part. Weighted Cesàro summation
converts this row limit into the normalized archimedean form.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HodgeTheoryOfAFixedPart

/-- The limiting finite part of the newest archimedean row. -/
def powerTailArchimedeanRowLimit (a : ℝ) : ℝ :=
  -Real.log (2 * Real.pi) - Real.eulerMascheroniConstant -
    ∫ t in (0 : ℝ)..1, powerTailJetProfile a t

/-- Finite part of the archimedean increment at the newest degree point. -/
def powerTailArchimedeanRow (a : ℝ) (N : ℕ) : ℝ :=
  counterterm (N + 1) - harm N -
    (∑ m ∈ Icc 1 N, powerTailJetProfile a ((m : ℝ) / (N + 1))) / (N + 1)

theorem powerTailArchimedeanRow_eq (a : ℝ) (N : ℕ) :
    powerTailArchimedeanRow a N =
      -Real.log (2 * Real.pi) - (harm (N + 1) - Real.log (N + 1)) -
        tailRiemannSum (powerTailJetProfile a) (N + 1) +
          (1 + powerTailJetProfile a 1) / (N + 1) := by
  have hn : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [powerTailArchimedeanRow, tailRiemannSum, sum_Icc_succ_top (by omega), counterterm,
    Real.log_div (by positivity) (by positivity), harm_succ]
  simp only [Nat.cast_add, Nat.cast_one, div_self hn.ne']
  ring

/-- The newest archimedean row has a finite limit for every subunit power. -/
theorem tendsto_powerTailArchimedeanRow {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (powerTailArchimedeanRow a) atTop (𝓝 (powerTailArchimedeanRowLimit a)) := by
  have hshift := tendsto_add_atTop_nat 1
  have hh := tendsto_harm_sub_log.comp hshift
  have hp := (tendsto_powerTailJetProfile_mesh ha ha1).comp hshift
  have hz := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hshift
  have hc : Tendsto (fun _ : ℕ => -Real.log (2 * Real.pi)) atTop
      (𝓝 (-Real.log (2 * Real.pi))) := tendsto_const_nhds
  have h := ((hc.sub hh).sub hp).add
    (hz.const_mul (1 + powerTailJetProfile a 1))
  have h' : Tendsto (fun N : ℕ =>
      -Real.log (2 * Real.pi) - (harm (N + 1) - Real.log ((N + 1 : ℕ) : ℝ)) -
        tailRiemannSum (powerTailJetProfile a) (N + 1) +
          (1 + powerTailJetProfile a 1) * (1 / ((N + 1 : ℕ) : ℝ)))
      atTop (𝓝 (powerTailArchimedeanRowLimit a)) := by
    simpa only [Function.comp_apply, mul_zero, add_zero, powerTailArchimedeanRowLimit] using h
  refine h'.congr fun N => ?_
  rw [powerTailArchimedeanRow_eq]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- Exact leading term of a subunit power sum. -/
theorem tendsto_normalized_powerTailPrefix {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (a - 1) * powerTailPrefix a N) atTop
      (𝓝 (1 / (1 - a))) := by
  have hb : 0 < 1 - a := by linarith only [ha1]
  have hzero : Tendsto (fun N : ℕ => (N : ℝ) ^ (a - 1) * (1 / (1 - a)))
      atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop hb).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).mul_const (1 / (1 - a))
    simpa only [Function.comp_apply, show -(1 - a) = a - 1 by ring, zero_mul] using h
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm' _ hzero
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hp := powerTailPrefix_sub_integral_bounds ha ha1 hNp.le
  have habs : |powerTailPrefix a N - (N : ℝ) ^ (1 - a) / (1 - a)| ≤ 1 / (1 - a) :=
    abs_le.mpr ⟨hp.1, hp.2.trans (by positivity)⟩
  have hmain : (N : ℝ) ^ (a - 1) * ((N : ℝ) ^ (1 - a) / (1 - a)) = 1 / (1 - a) := by
    rw [← mul_div_assoc, ← Real.rpow_add hNp, show a - 1 + (1 - a) = 0 by ring,
      Real.rpow_zero]
  rw [Real.norm_eq_abs]
  calc
    _ = (N : ℝ) ^ (a - 1) *
        |powerTailPrefix a N - (N : ℝ) ^ (1 - a) / (1 - a)| := by
      conv_lhs => rw [← hmain, ← mul_sub, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hNp.le _)]
    _ ≤ _ := mul_le_mul_of_nonneg_left habs (Real.rpow_nonneg hNp.le _)

theorem tendsto_powerTailPrefix_atTop {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun N : ℕ => powerTailPrefix a N) atTop atTop := by
  have hb : 0 < 1 - a := by linarith only [ha1]
  have hp := (tendsto_rpow_atTop hb).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [hp.eventually_ge_atTop ((1 - a) * B + 1)] with N hN
  have hprefix := (powerTailPrefix_sub_integral_bounds ha ha1 (Nat.cast_nonneg N)).1
  have hmain : B ≤ (N : ℝ) ^ (1 - a) / (1 - a) - 1 / (1 - a) := by
    rw [← sub_div, le_div_iff₀ hb]
    dsimp only [Function.comp_apply] at hN
    nlinarith only [hN]
  linarith only [hprefix, hmain]

/-- The complete archimedean part has its expected finite power-tail limit. -/
theorem tendsto_normalized_powerTailArchimedean {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (2 * a - 1) * powerTailArchimedean a N)
      atTop (𝓝 (powerTailArchimedeanRowLimit a / (1 - 2 * a))) := by
  have ha1 : a < 1 := by linarith only [ha2]
  have h2a : 0 < 2 * a := by linarith only [ha]
  have h2a1 : 2 * a < 1 := by linarith only [ha2]
  let w := fun n : ℕ => powerTailWeight a (n + 1) ^ 2
  let W := fun N : ℕ => ∑ n ∈ range N, w n
  have hw (n : ℕ) : w n = powerTailWeight (2 * a) (n + 1) := by
    dsimp only [w, powerTailWeight]
    rw [sq, ← Real.rpow_add (by positivity)]
    congr 1
    ring
  have hW (N : ℕ) : W N = powerTailPrefix (2 * a) N := by
    dsimp only [W]
    simp_rw [hw]
    rw [RHTower.sum_range_succ_eq_sourcePartialSum]
    simp only [RHTower.sourcePartialSum, powerTailPrefix, Nat.floor_natCast]
  have hWlim : Tendsto W atTop atTop :=
    (tendsto_powerTailPrefix_atTop h2a h2a1).congr fun N => (hW N).symm
  have hsum (N : ℕ) : (∑ n ∈ range N, w n * powerTailArchimedeanRow a n) =
      powerTailArchimedean a N := by
    have hinc (n : ℕ) : w n * powerTailArchimedeanRow a n =
        powerTailArchimedean a (n + 1) - powerTailArchimedean a n :=
      (powerTailArchimedean_increment_profile a n).symm
    rw [sum_congr rfl (fun n _ => hinc n), sum_range_sub]
    simp [powerTailArchimedean]
  have hy := RHTower.weightedCesaro_smul (tendsto_powerTailArchimedeanRow ha ha1)
    w (fun n => sq_nonneg _) hWlim
  simp only [smul_eq_mul, hsum] at hy
  have hs : Tendsto (fun N : ℕ => (N : ℝ) ^ (2 * a - 1) * W N) atTop
      (𝓝 (1 / (1 - 2 * a))) := by
    simpa only [hW] using tendsto_normalized_powerTailPrefix h2a h2a1
  have h := hy.mul hs
  rw [mul_one_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hWpos : 0 < W N := by
    apply sum_pos' (fun n _ => sq_nonneg _)
    refine ⟨0, mem_range.mpr (by omega), ?_⟩
    simp [w, powerTailWeight]
  change (W N)⁻¹ * powerTailArchimedean a N * ((N : ℝ) ^ (2 * a - 1) * W N) = _
  calc
    _ = ((W N)⁻¹ * W N) * ((N : ℝ) ^ (2 * a - 1) * powerTailArchimedean a N) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hWpos.ne', one_mul]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ

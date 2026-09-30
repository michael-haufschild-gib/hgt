import GaloisForLFunctions.RHTower.LiClockPairedEtaContiguousSource
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Complete contiguous clock decay on moving windows

The full quarter-circle source envelope yields decay for moving complex
clocks bounded by `c * log (2 * N + 1)`, for every `0 < c < 1/16`.
No clock-divergence or clock-reality premise is used. The actual finite
interval-union source is not substituted by this contiguous model.
-/

open Complex Filter Topology
namespace RHTower
noncomputable section


private theorem log_odd_endpoint_le {N : ℕ} (hN : 0 < N) :
    Real.log (2 * (N : ℝ) + 1) ≤ Real.log (2 * (N : ℝ)) + Real.log (3 / 2) := by
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : 0 < 2 * (N : ℝ) := by linarith
  calc
    _ ≤ Real.log ((2 * (N : ℝ)) * (3 / 2)) :=
      Real.log_le_log (by linarith) (by nlinarith)
    _ = _ := Real.log_mul (ne_of_gt hpos) (by norm_num)

private theorem norm_contiguousClock_le_movingEnvelope {N : ℕ} (hN : 0 < N)
    {c : ℝ} (hc : 0 < c) {t : ℂ}
    (ht : ‖t‖ ≤ c * Real.log (2 * (N : ℝ) + 1)) :
    ‖liClockPairedEtaContiguousClock (Real.log (2 * (N : ℝ))) t‖ ≤
      Real.exp (4 * c * Real.log (3 / 2)) * Real.log (2 * (N : ℝ)) *
        Real.exp (-(1 / 4 - 4 * c) * Real.log (2 * (N : ℝ))) /
          (1 - Real.exp (-Real.log (2 * (N : ℝ)) / 4)) := by
  let L : ℝ := Real.log (2 * (N : ℝ))
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hL : 0 < L := Real.log_pos (by linarith)
  have he : Real.exp (-L / 4) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hB : 0 ≤ liClockPairedEtaContiguousSourceEnvelope L := by
    unfold liClockPairedEtaContiguousSourceEnvelope
    exact div_nonneg (mul_nonneg hL.le (Real.exp_pos _).le) (by linarith)
  have ht' : 4 * ‖t‖ ≤ 4 * c * (L + Real.log (3 / 2)) := by
    have hh := mul_le_mul_of_nonneg_left (log_odd_endpoint_le hN) hc.le
    dsimp only [L] at *
    nlinarith
  have hsinh : Real.sinh (4 * ‖t‖) ≤ Real.exp (4 * ‖t‖) := by
    rw [Real.sinh_eq]
    linarith [Real.exp_pos (4 * ‖t‖), Real.exp_pos (-(4 * ‖t‖))]
  have hexp : Real.exp (-L / 4) * Real.exp (4 * c * (L + Real.log (3 / 2))) =
      Real.exp (4 * c * Real.log (3 / 2)) * Real.exp (-(1 / 4 - 4 * c) * L) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ liClockPairedEtaContiguousSourceEnvelope L * Real.sinh (4 * ‖t‖) :=
      norm_liClockPairedEtaContiguousClock_le_sourceEnvelope hL t
    _ ≤ liClockPairedEtaContiguousSourceEnvelope L *
        Real.exp (4 * c * (L + Real.log (3 / 2))) :=
      mul_le_mul_of_nonneg_left (hsinh.trans (Real.exp_le_exp.mpr ht')) hB
    _ = L * (Real.exp (-L / 4) * Real.exp (4 * c * (L + Real.log (3 / 2)))) /
        (1 - Real.exp (-L / 4)) := by
      unfold liClockPairedEtaContiguousSourceEnvelope
      ring
    _ = _ := by rw [hexp]; dsimp only [L]; ring

private theorem contiguousMovingEnvelope_tendsto_zero {c : ℝ} (hc : c < 1 / 16) :
    Tendsto (fun L : ℝ => Real.exp (4 * c * Real.log (3 / 2)) * L *
      Real.exp (-(1 / 4 - 4 * c) * L) / (1 - Real.exp (-L / 4)))
      atTop (𝓝 0) := by
  have hε : 0 < 1 / 4 - 4 * c := by linarith
  have hn : Tendsto (fun L : ℝ => Real.exp (4 * c * Real.log (3 / 2)) * L *
      Real.exp (-(1 / 4 - 4 * c) * L)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, mul_zero, mul_assoc] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 4 - 4 * c) hε).const_mul
        (Real.exp (4 * c * Real.log (3 / 2)))
  have hs : Tendsto (fun L : ℝ => L / 4) atTop atTop := by
    simpa only [div_eq_mul_inv, mul_comm, id_eq, one_mul] using
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 4))
  have he : Tendsto (fun L : ℝ => Real.exp (-L / 4)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hs
  have hd : Tendsto (fun L : ℝ => 1 - Real.exp (-L / 4)) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub he
  convert hn.div hd (by norm_num : (1 : ℝ) ≠ 0) using 1
  · funext L
    rfl
  · simp

/-- Complete contiguous clock decay on moving complex logarithmic windows.
No divergence or reality assumption on the clock sequence is required. -/
theorem liClockPairedEtaContiguousClock_moving_logWindow_tendsto_zero
    {c : ℝ} (hc : 0 < c) (hcsmall : c < 1 / 16)
    (ν : ℕ → ℕ) (τ : ℕ → ℂ) (hν : Tendsto ν atTop atTop)
    (hτ : ∀ᶠ l : ℕ in atTop, ‖τ l‖ ≤ c * Real.log (2 * (ν l : ℝ) + 1)) :
    Tendsto (fun l : ℕ => liClockPairedEtaContiguousClock (Real.log (2 * (ν l : ℝ)))
      (τ l)) atTop (𝓝 0) := by
  have hL : Tendsto (fun l : ℕ => Real.log (2 * (ν l : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      ((Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
        tendsto_natCast_atTop_atTop).comp hν)
  have hbound := (contiguousMovingEnvelope_tendsto_zero hcsmall).comp hL
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
  filter_upwards [hτ, hν.eventually_gt_atTop (0 : ℕ)] with l ht hn
  exact norm_contiguousClock_le_movingEnvelope hn hc ht


end
end RHTower

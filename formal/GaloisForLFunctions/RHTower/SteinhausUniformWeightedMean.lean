import GaloisForLFunctions.RHTower.SteinhausWeightedSummatoryAbel
import GaloisForLFunctions.RHTower.SteinhausAbelSqrtCost
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace RHTower
open SteinhausModel

/-- Original arithmetic low-moment decay transfers uniformly over all admissible monotone weights. -/
theorem eventually_integral_norm_steinhausWeightedSummatory_div_rpow_le
    {β : ℝ} (hβ : 0 < β) (hβhalf : β < 1 / 2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ w : ℕ → ℝ,
      (∀ n, 1 ≤ n → 0 ≤ w n) →
      (∀ n, 1 ≤ n → w (n + 1) ≤ w n) →
      (∀ n, 1 ≤ n → w n ≤ (n : ℝ) ^ (-β)) →
      (∫ ω, ‖∑ n ∈ Finset.Icc 1 N, (w n : ℂ) * X n ω‖ ∂steinhausMeasure) /
        (N : ℝ) ^ (1 / 2 - β) ≤ δ := by
  let d : ℝ := 1 / 2 - β
  have hd : 0 < d := by dsimp [d]; linarith
  let ε : ℝ := δ * d / 2
  have hε : 0 < ε := div_pos (mul_pos hδ hd) (by norm_num)
  obtain ⟨C, hC, hmean⟩ := exists_steinhausSummatoryMean_sqrt_envelope hε
  have htail : Tendsto (fun N : ℕ => C / (N : ℝ) ^ d) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop)
  filter_upwards [htail.eventually (gt_mem_nhds (half_pos hδ)), eventually_ge_atTop (1 : ℕ)]
    with N htailN hN
  intro w hw hanti hbound
  have hp : 0 < (N : ℝ) ^ d := Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  have hw1 : w 1 ≤ 1 := by simpa using hbound 1 le_rfl
  have hcost := steinhausAbelSqrtCost_le w hβ hβhalf hw hbound N
  have hupper : (∫ ω, ‖∑ n ∈ Finset.Icc 1 N, (w n : ℂ) * X n ω‖ ∂steinhausMeasure) ≤
      C + ε * ((N : ℝ) ^ d / d) := by
    refine (integral_norm_steinhausWeightedSummatory_le_envelope w N hw hanti hmean).trans ?_
    exact add_le_add (by nlinarith) (mul_le_mul_of_nonneg_left hcost hε.le)
  have halgebra : (C + ε * ((N : ℝ) ^ d / d)) / (N : ℝ) ^ d =
      C / (N : ℝ) ^ d + δ / 2 := by
    dsimp [ε]
    field_simp [hp.ne', hd.ne']
  change _ / (N : ℝ) ^ d ≤ δ
  have h := div_le_div_of_nonneg_right hupper hp.le
  rw [halgebra] at h
  linarith

/-- The uniform estimate allows weights to vary arbitrarily with the cutoff within the admissible class. -/
theorem tendsto_integral_norm_steinhausWeightedSummatory_div_rpow
    {β : ℝ} (hβ : 0 < β) (hβhalf : β < 1 / 2) (w : ℕ → ℕ → ℝ)
    (hw : ∀ N n, 1 ≤ n → 0 ≤ w N n)
    (hanti : ∀ N n, 1 ≤ n → w N (n + 1) ≤ w N n)
    (hbound : ∀ N n, 1 ≤ n → w N n ≤ (n : ℝ) ^ (-β)) :
    Tendsto (fun N : ℕ =>
      (∫ ω, ‖∑ n ∈ Finset.Icc 1 N, (w N n : ℂ) * X n ω‖ ∂steinhausMeasure) /
        (N : ℝ) ^ (1 / 2 - β)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_integral_norm_steinhausWeightedSummatory_div_rpow_le hβ hβhalf (half_pos hε))
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right, Real.norm_of_nonneg (div_nonneg
    (integral_nonneg (fun _ => norm_nonneg _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _))]
  exact (hN n hn (w n) (hw n) (hanti n) (hbound n)).trans_lt (by linarith)

end RHTower

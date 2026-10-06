import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeEdges
import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeMoments
import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeHole

/-!
# Complete cancellation of the actual ordered hyperbolic prime packet

The source physical window pays every truncated edge. The actual prime-pair
sieve then pays all reciprocal-square gaps and all ordering holes. No small-gap
deletion, edge-prime estimate, or auxiliary double limit remains.
-/

noncomputable section

namespace RHTower

open Finset Filter Topology MeasureTheory

/-- Sum of the norms of EVERY original ordered pair integral. -/
def chiCubicHyperbolicPrimeIntegralMass (N : ℝ) (M : ℕ) : ℝ :=
  ∑ pr ∈ ((primeProfileBand N).product (primeProfileBand N)).filter (fun pr => pr.1 ≠ pr.2),
    ‖chiCubicHyperbolicPrimePairIntegral N M pr‖

private theorem integral_mass_eq_active (N : ℝ) (M : ℕ) :
    chiCubicHyperbolicPrimeIntegralMass N M =
      ∑ pr ∈ chiCubicHyperbolicPrimeHolePairs N M, ‖chiCubicHyperbolicPrimePairIntegral N M pr‖ := by
  classical
  unfold chiCubicHyperbolicPrimeIntegralMass chiCubicHyperbolicPrimeHolePairs
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro pr _
  by_cases hne : pr.1 ≠ pr.2
  · by_cases hactive : |(pr.1 : ℝ) - pr.2| ^ 2 ≤ (M : ℝ) * pr.2
    · simp only [hactive, and_true]
    · simp only [hactive, and_false, ite_false]
      rw [chiCubicHyperbolicPrimePairIntegral_zero_of_inactive N M hne
        (lt_of_not_ge hactive), norm_zero]
      simp
  · simp only [hne, false_and, ite_false]

private theorem gap_le_floor {p r : ℕ} {x : ℝ} (h : |(p : ℝ) - r| ≤ x) :
    |(p : ℝ) - r| ≤ (⌊x⌋₊ : ℝ) := by
  rcases le_total p r with hpr | hrp
  · have he : |(p : ℝ) - r| = ((r - p : ℕ) : ℝ) := by
      rw [Nat.cast_sub hpr, abs_of_nonpos (sub_nonpos.2 (by exact_mod_cast hpr))]
      ring
    rw [he] at h ⊢
    exact_mod_cast Nat.le_floor h
  · have he : |(p : ℝ) - r| = ((p - r : ℕ) : ℝ) := by
      rw [Nat.cast_sub hrp, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hrp))]
    rw [he] at h ⊢
    exact_mod_cast Nat.le_floor h

/-- Every actual pair integral cancels in aggregate at a full extra logarithm,
including all small gaps, both gap signs, central holes and truncated edges. -/
theorem exists_chiCubicHyperbolicPrimeIntegralMass_bound (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℝ in atTop,
      chiCubicHyperbolicPrimeIntegralMass N M ≤ C * N / Real.log N ^ 3 := by
  obtain ⟨B, hB, hpair⟩ := exists_chiCubicHyperbolicPrimePairIntegral_all_bound
  obtain ⟨A, hA, hmom⟩ := exists_chiCubicPrimeGapCount_moment_bounds
  refine ⟨2 * B * A * ((M : ℝ) + 1) ^ 2 * (1 + 2 * M), by positivity, ?_⟩
  filter_upwards [hmom, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with N hmomN hN hlog
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := by linarith
  let D := ⌊Real.sqrt (2 * (M : ℝ) * N)⌋₊
  have hY : 0 ≤ 2 * (M : ℝ) * N := by positivity
  have hDsq : (D : ℝ) ^ 2 ≤ 2 * M * N := by
    have hDle : (D : ℝ) ≤ Real.sqrt (2 * (M : ℝ) * N) := Nat.floor_le (Real.sqrt_nonneg _)
    exact (pow_le_pow_left₀ (Nat.cast_nonneg D) hDle 2).trans_eq (Real.sq_sqrt hY)
  have hsub : chiCubicHyperbolicPrimeHolePairs N M ⊆ chiCubicPrimeGapPairs N D := by
    intro pr hpr
    obtain ⟨hmem, hne, hactive⟩ := Finset.mem_filter.1 hpr
    have hr := (Finset.mem_product.1 hmem).2
    have hrN := (primeProfileBand_mem hN0.le hr).2.2
    have hsquare : |(pr.1 : ℝ) - pr.2| ^ 2 ≤ 2 * M * N := by
      calc
        _ ≤ (M : ℝ) * pr.2 := hactive
        _ ≤ (M : ℝ) * (2 * N) := by gcongr
        _ = _ := by ring
    have hrad : |(pr.1 : ℝ) - pr.2| ≤ Real.sqrt (2 * (M : ℝ) * N) := by
      have hroot := Real.sq_sqrt hY
      have hroot0 := Real.sqrt_nonneg (2 * (M : ℝ) * N)
      nlinarith [abs_nonneg ((pr.1 : ℝ) - pr.2)]
    exact Finset.mem_filter.2 ⟨hmem, hne, gap_le_floor hrad⟩
  let f := fun d : ℝ => 1 / (d ^ 2 * Real.log N) + d / (N * Real.log N)
  have hsum : (∑ pr ∈ chiCubicPrimeGapPairs N D, f |(pr.1 : ℝ) - pr.2|) =
      (2 / Real.log N) * (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d / (d : ℝ) ^ 2) +
        (2 / (N * Real.log N)) * (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d * (d : ℝ)) := by
    rw [chiCubicPrimeGapPairs_sum]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    dsimp [f]
    ring
  calc
    _ = _ := integral_mass_eq_active N M
    _ ≤ ∑ pr ∈ chiCubicHyperbolicPrimeHolePairs N M,
        B * ((M : ℝ) + 1) ^ 2 * f |(pr.1 : ℝ) - pr.2| := by
      apply Finset.sum_le_sum
      intro pr hpr
      obtain ⟨hmem, hne, _⟩ := Finset.mem_filter.1 hpr
      obtain ⟨hp, hr⟩ := Finset.mem_product.1 hmem
      exact hpair N hN hlog M pr.1 hp pr.2 hr hne
    _ = B * ((M : ℝ) + 1) ^ 2 *
        (∑ pr ∈ chiCubicHyperbolicPrimeHolePairs N M, f |(pr.1 : ℝ) - pr.2|) :=
      (Finset.mul_sum ..).symm
    _ ≤ B * ((M : ℝ) + 1) ^ 2 * (∑ pr ∈ chiCubicPrimeGapPairs N D, f |(pr.1 : ℝ) - pr.2|) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro pr _ _
      dsimp [f]
      positivity
    _ = B * ((M : ℝ) + 1) ^ 2 *
        ((2 / Real.log N) * (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d / (d : ℝ) ^ 2) +
          (2 / (N * Real.log N)) * (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d * (d : ℝ))) := by rw [hsum]
    _ ≤ B * ((M : ℝ) + 1) ^ 2 *
        ((2 / Real.log N) * (A * N / Real.log N ^ 2) +
          (2 / (N * Real.log N)) * (A * (D : ℝ) ^ 2 * N / Real.log N ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left (hmomN D).1 (by positivity))
        (mul_le_mul_of_nonneg_left (hmomN D).2 (by positivity))
    _ ≤ B * ((M : ℝ) + 1) ^ 2 *
        ((2 / Real.log N) * (A * N / Real.log N ^ 2) +
          (2 / (N * Real.log N)) * (A * (2 * M * N) * N / Real.log N ^ 2)) := by gcongr
    _ = _ := by field_simp

/-- The entire sum of actual pair-integral norms is negligible at the cubic scale. -/
theorem chiCubicHyperbolicPrimeIntegralMass_tendsto (M : ℕ) :
    Tendsto (fun N : ℝ => Real.log N ^ 2 / N * chiCubicHyperbolicPrimeIntegralMass N M)
      atTop (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := exists_chiCubicHyperbolicPrimeIntegralMass_bound M
  have hlim : Tendsto (fun N : ℝ => C / Real.log N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  · filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with N hboundN hN
    have hN0 : 0 < N := by linarith
    have hL : 0 < Real.log N := Real.log_pos hN
    calc
      _ ≤ (Real.log N ^ 2 / N) * (C * N / Real.log N ^ 3) :=
        mul_le_mul_of_nonneg_left hboundN (by positivity)
      _ = _ := by field_simp

/-- Unconditional cancellation of the complete literal continuous kernel. -/
theorem chiCubicHyperbolicPrimeKernel_integral_tendsto (M : ℕ) :
    Tendsto (fun N : ℝ => Real.log N ^ 2 / N *
      ‖∫ x in Set.Icc N (2 * N), chiCubicHyperbolicPrimeKernel N M x‖)
      atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (chiCubicHyperbolicPrimeIntegralMass_tendsto M) ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    positivity
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    rw [chiCubicHyperbolicPrimeKernel_integral_eq hN M]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

/-- The ORIGINAL ordered hyperbolic triple-prime packet cancels for every fixed
natural radius. All physical weights, phases, sharp boundaries and exclusions remain. -/
theorem chiCubicHyperbolicPrimePacket_tendsto (M : ℕ) :
    Tendsto (fun N : ℝ => Real.log N ^ 2 / N * ‖chiCubicHyperbolicPrimePacket N M‖)
      atTop (𝓝 0) := by
  have hlim := (chiCubicHyperbolicPrimePacket_integral_tendsto M).add
    (chiCubicHyperbolicPrimeKernel_integral_tendsto M)
  simp only [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    positivity
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    let P := chiCubicHyperbolicPrimePacket N M
    let J := ∫ x in Set.Icc N (2 * N), chiCubicHyperbolicPrimeKernel N M x
    have hh : ‖P‖ ≤ ‖P - J‖ + ‖J‖ := by
      calc
        _ = ‖(P - J) + J‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    exact (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ Real.log N ^ 2 / N)).trans_eq (by ring)

end RHTower

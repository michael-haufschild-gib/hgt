import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeGapIntegrals

/-!
# The complete actual ordering-hole mass

Every active prime pair is retained, including holes clipped by the original
band endpoints. The averaged prime-pair prefix pays their total norm through
its first gap moment, without a separate estimate at each prime anchor.
-/

noncomputable section

namespace RHTower

open Finset Filter Topology MeasureTheory

/-- The actual central ordering hole, clipped only to the original band. -/
def chiCubicHyperbolicPrimeHoleIntegral (N : ℝ) (pr : ℕ × ℕ) : ℂ :=
  ∫ x in Set.Icc ((pr.2 : ℝ) - |(pr.1 : ℝ) - pr.2|)
      ((pr.2 : ℝ) + |(pr.1 : ℝ) - pr.2|) ∩ Set.Icc N (2 * N),
    chiCubicHyperbolicPrimeAmplitude N pr x

/-- Every original active pair contributing to the ordering-hole budget. -/
def chiCubicHyperbolicPrimeHolePairs (N : ℝ) (M : ℕ) : Finset (ℕ × ℕ) :=
  ((primeProfileBand N).product (primeProfileBand N)).filter
    (fun pr => pr.1 ≠ pr.2 ∧ |(pr.1 : ℝ) - pr.2| ^ 2 ≤ (M : ℝ) * pr.2)

/-- Complete nonnegative mass of the actual ordering holes. -/
def chiCubicHyperbolicPrimeHoleMass (N : ℝ) (M : ℕ) : ℝ :=
  ∑ pr ∈ chiCubicHyperbolicPrimeHolePairs N M, ‖chiCubicHyperbolicPrimeHoleIntegral N pr‖

/-- Actual hole integrals are integrable even when they cross a band endpoint. -/
theorem integrableOn_chiCubicHyperbolicPrimeHole {N : ℝ} (hN : 1 < N) (pr : ℕ × ℕ) :
    IntegrableOn (chiCubicHyperbolicPrimeAmplitude N pr)
      (Set.Icc ((pr.2 : ℝ) - |(pr.1 : ℝ) - pr.2|)
        ((pr.2 : ℝ) + |(pr.1 : ℝ) - pr.2|) ∩ Set.Icc N (2 * N)) volume :=
  (chiCubicHyperbolicPrimeAmplitude_continuousOn hN pr).integrableOn_Icc.mono_set
    (fun _ hx => hx.2)

/-- The actual hole cost is linear in the gap, with the physical and logarithmic
normalizations retained. -/
theorem norm_chiCubicHyperbolicPrimeHoleIntegral_le {N : ℝ} (hN : 1 < N)
    {p r : ℕ} (hp : p ∈ primeProfileBand N) (hr : r ∈ primeProfileBand N) :
    ‖chiCubicHyperbolicPrimeHoleIntegral N (p, r)‖ ≤
      4 * Real.pi * |(p : ℝ) - r| / (N * Real.log N) := by
  let d := |(p : ℝ) - r|
  let S := Set.Icc ((r : ℝ) - d) ((r : ℝ) + d) ∩ Set.Icc N (2 * N)
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos hN
  have hd : 0 ≤ d := abs_nonneg _
  have hsub : S ⊆ Set.Icc ((r : ℝ) - d) ((r : ℝ) + d) := fun _ hx => hx.1
  have hfinite : volume S < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) isCompact_Icc.measure_lt_top
  have hvol : volume.real (Set.Icc ((r : ℝ) - d) ((r : ℝ) + d)) = 2 * d := by
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  calc
    _ ≤ (2 * Real.pi / (N * Real.log N)) * volume.real S :=
      norm_setIntegral_le_of_norm_le_const hfinite (fun x hx =>
        norm_chiCubicHyperbolicPrimeAmplitude_le hN hp hr hx.2)
    _ ≤ (2 * Real.pi / (N * Real.log N)) *
        volume.real (Set.Icc ((r : ℝ) - d) ((r : ℝ) + d)) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsub isCompact_Icc.measure_lt_top.ne)
        (by positivity)
    _ = _ := by rw [hvol]; dsimp [d]; ring

private theorem nat_gap_le_floor {p r : ℕ} {x : ℝ} (h : |(p : ℝ) - r| ≤ x) :
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

/-- The ENTIRE actual ordering-hole mass is negligible at the cubic scale.
The averaged pair sieve pays both gap orientations, including edge-clipped holes. -/
theorem chiCubicHyperbolicPrimeHoleMass_tendsto (M : ℕ) :
    Tendsto (fun N : ℝ => Real.log N ^ 2 / N * chiCubicHyperbolicPrimeHoleMass N M)
      atTop (𝓝 0) := by
  obtain ⟨A, hA, hpre⟩ := exists_chiCubicPrimeGapCount_prefix_bound
  have hlim : Tendsto (fun N : ℝ => 16 * Real.pi * A * M / Real.log N) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (16 * Real.pi * A * M)
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  · filter_upwards [hpre, eventually_gt_atTop (1 : ℝ)] with N hpreN hN
    have hN0 : 0 < N := by linarith
    have hL : 0 < Real.log N := Real.log_pos hN
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
      exact Finset.mem_filter.2 ⟨hmem, hne, nat_gap_le_floor hrad⟩
    have hfirst : (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d * (d : ℝ)) ≤
        (D : ℝ) * (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d hd
      have hdD : (d : ℝ) ≤ D := by exact_mod_cast (Finset.mem_Icc.1 hd).2
      have hP : 0 ≤ chiCubicPrimeGapCount N d := Nat.cast_nonneg _
      calc
        _ ≤ chiCubicPrimeGapCount N d * D := mul_le_mul_of_nonneg_left hdD hP
        _ = _ := mul_comm _ _
    have hmass : chiCubicHyperbolicPrimeHoleMass N M ≤
        16 * Real.pi * A * M * N / Real.log N ^ 3 := by
      calc
        _ ≤ ∑ pr ∈ chiCubicHyperbolicPrimeHolePairs N M,
            4 * Real.pi * |(pr.1 : ℝ) - pr.2| / (N * Real.log N) := by
          apply Finset.sum_le_sum
          intro pr hpr
          obtain ⟨hp, hr⟩ := Finset.mem_product.1 (Finset.mem_filter.1 hpr).1
          exact norm_chiCubicHyperbolicPrimeHoleIntegral_le hN hp hr
        _ = (4 * Real.pi / (N * Real.log N)) *
            (∑ pr ∈ chiCubicHyperbolicPrimeHolePairs N M, |(pr.1 : ℝ) - pr.2|) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro pr _
          ring
        _ ≤ (4 * Real.pi / (N * Real.log N)) *
            (∑ pr ∈ chiCubicPrimeGapPairs N D, |(pr.1 : ℝ) - pr.2|) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)) (by positivity)
        _ = (8 * Real.pi / (N * Real.log N)) *
            (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d * (d : ℝ)) := by
          rw [chiCubicPrimeGapPairs_sum N D (fun x => x)]
          ring
        _ ≤ (8 * Real.pi / (N * Real.log N)) *
            ((D : ℝ) * (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d)) := by gcongr
        _ ≤ (8 * Real.pi / (N * Real.log N)) *
            ((D : ℝ) * (A * D * N / Real.log N ^ 2)) := by gcongr; exact hpreN D
        _ = (8 * Real.pi * A / Real.log N ^ 3) * (D : ℝ) ^ 2 := by field_simp
        _ ≤ (8 * Real.pi * A / Real.log N ^ 3) * (2 * M * N) := by gcongr
        _ = _ := by ring
    calc
      _ ≤ (Real.log N ^ 2 / N) * (16 * Real.pi * A * M * N / Real.log N ^ 3) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := by field_simp

end RHTower

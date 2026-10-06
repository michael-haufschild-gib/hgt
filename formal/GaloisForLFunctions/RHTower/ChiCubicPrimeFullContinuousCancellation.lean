import GaloisForLFunctions.RHTower.ChiCubicPrimeFullPairIntegral
import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeMoments
import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeGapIntegrals

/-!
# Complete continuous middle-coordinate cancellation

Every original noncontracting prime pair and the ENTIRE middle-coordinate
band are retained. The actual pair sieve sums both the moving-boundary term
and the inverse-square gap term. Full arithmetic prime sampling is separate.
-/

noncomputable section

namespace RHTower

open Finset Filter MeasureTheory Set
open scoped Topology

/-- Sum of norms of ALL full-band continuous rows, with the original p≠r mask. -/
def chiCubicPrimeFullIntegralMass (N : ℝ) : ℝ :=
  ∑ pr ∈ ((primeProfileBand N).product (primeProfileBand N)).filter (fun pr => pr.1 ≠ pr.2),
    ‖chiCubicPrimeFullPairIntegral N pr.1 pr.2‖

/-- The complete continuous q-density model with EVERY original prime pair. -/
def chiCubicPrimeFullContinuousCubic (N : ℝ) : ℂ :=
  ∫ x in N..(2 * N),
    ∑ pr ∈ ((primeProfileBand N).product (primeProfileBand N)).filter (fun pr => pr.1 ≠ pr.2),
      chiCubicHyperbolicPrimeAmplitude N pr x

/-- The ENTIRE full-band row-norm sum has a full logarithm to spare at the
cubic scale. No gap cutoff, hyperbolic radius or arithmetic premise remains. -/
theorem exists_chiCubicPrimeFullIntegralMass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℝ in atTop,
      chiCubicPrimeFullIntegralMass N ≤ C * N / Real.log N ^ 3 := by
  obtain ⟨B, hB, hpair⟩ := exists_chiCubicPrimeFullPairIntegral_bound
  obtain ⟨A, hA, hmom⟩ := exists_chiCubicPrimeGapCount_moment_bounds
  obtain ⟨E, hE, hpre⟩ := exists_chiCubicPrimeGapCount_prefix_bound
  let C := B * (2 * A + 4 * E)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hmom, hpre, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with N hmomN hpreN hN hlog
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos hN
  let P := ((primeProfileBand N).product (primeProfileBand N)).filter (fun pr => pr.1 ≠ pr.2)
  let D := ⌊2 * N⌋₊
  have hD : (D : ℝ) ≤ 2 * N := Nat.floor_le (by positivity)
  have hsub : P ⊆ chiCubicPrimeGapPairs N D := by
    intro pr hpr
    obtain ⟨hmem, hne⟩ := Finset.mem_filter.1 hpr
    obtain ⟨hp, hr⟩ := Finset.mem_product.1 hmem
    have hpD : pr.1 ≤ D := Nat.le_floor (primeProfileBand_mem hN0.le hp).2.2
    have hrD : pr.2 ≤ D := Nat.le_floor (primeProfileBand_mem hN0.le hr).2.2
    have hpD' : (pr.1 : ℝ) ≤ D := by exact_mod_cast hpD
    have hrD' : (pr.2 : ℝ) ≤ D := by exact_mod_cast hrD
    have hgap : |(pr.1 : ℝ) - pr.2| ≤ (D : ℝ) := by
      apply abs_le.2
      constructor <;> linarith [show (0 : ℝ) ≤ pr.1 from Nat.cast_nonneg _,
        show (0 : ℝ) ≤ pr.2 from Nat.cast_nonneg _]
    exact Finset.mem_filter.2 ⟨hmem, hne, hgap⟩
  let f := fun d : ℝ => 1 / (d ^ 2 * Real.log N) + 1 / (N * Real.log N)
  have hsum : (∑ pr ∈ chiCubicPrimeGapPairs N D, f |(pr.1 : ℝ) - pr.2|) =
      (2 / Real.log N) * (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d / (d : ℝ) ^ 2) +
        (2 / (N * Real.log N)) * (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d) := by
    rw [chiCubicPrimeGapPairs_sum]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    dsimp [f]
    ring
  calc
    _ ≤ ∑ pr ∈ P, B * f |(pr.1 : ℝ) - pr.2| := by
      apply Finset.sum_le_sum
      intro pr hpr
      obtain ⟨hmem, hne⟩ := Finset.mem_filter.1 hpr
      obtain ⟨hp, hr⟩ := Finset.mem_product.1 hmem
      exact hpair N hN hlog pr.1 hp pr.2 hr hne
    _ = B * (∑ pr ∈ P, f |(pr.1 : ℝ) - pr.2|) := (Finset.mul_sum ..).symm
    _ ≤ B * (∑ pr ∈ chiCubicPrimeGapPairs N D, f |(pr.1 : ℝ) - pr.2|) := by
      apply mul_le_mul_of_nonneg_left _ hB.le
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun pr _ _ => by dsimp [f]; positivity)
    _ = B * ((2 / Real.log N) *
        (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d / (d : ℝ) ^ 2) +
          (2 / (N * Real.log N)) * (∑ d ∈ Finset.Icc 1 D, chiCubicPrimeGapCount N d)) := by rw [hsum]
    _ ≤ B * ((2 / Real.log N) * (A * N / Real.log N ^ 2) +
        (2 / (N * Real.log N)) * (E * D * N / Real.log N ^ 2)) := by
      gcongr
      · exact (hmomN D).1
      · exact hpreN D
    _ ≤ B * ((2 / Real.log N) * (A * N / Real.log N ^ 2) +
        (2 / (N * Real.log N)) * (E * (2 * N) * N / Real.log N ^ 2)) := by gcongr
    _ = C * N / Real.log N ^ 3 := by dsimp [C]; field_simp; ring

/-- Complete row-norm cancellation at the original cubic normalization. -/
theorem chiCubicPrimeFullIntegralMass_tendsto :
    Tendsto (fun N : ℝ => Real.log N ^ 2 / N * chiCubicPrimeFullIntegralMass N)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hmass⟩ := exists_chiCubicPrimeFullIntegralMass_bound
  have hlim : Tendsto (fun N : ℝ => C / Real.log N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  · filter_upwards [hmass, eventually_gt_atTop (1 : ℝ)] with N hb hN
    have hN0 : 0 < N := by linarith
    have hL : 0 < Real.log N := Real.log_pos hN
    calc
      _ ≤ (Real.log N ^ 2 / N) * (C * N / Real.log N ^ 3) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C / Real.log N := by field_simp

/-- Unconditional cancellation of the COMPLETE continuous middle-coordinate
cubic, across every original prime pair. Prime-sampling transfer is separate. -/
theorem chiCubicPrimeFullContinuousCubic_tendsto :
    Tendsto (fun N : ℝ => Real.log N ^ 2 / N * ‖chiCubicPrimeFullContinuousCubic N‖)
      atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    chiCubicPrimeFullIntegralMass_tendsto ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    positivity
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hi (pr : ℕ × ℕ) : IntervalIntegrable (chiCubicHyperbolicPrimeAmplitude N pr) volume N (2 * N) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2
        (chiCubicHyperbolicPrimeAmplitude_continuousOn hN pr).integrableOn_Icc
    unfold chiCubicPrimeFullContinuousCubic
    rw [intervalIntegral.integral_finsetSum (fun pr _ => hi pr)]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

end RHTower

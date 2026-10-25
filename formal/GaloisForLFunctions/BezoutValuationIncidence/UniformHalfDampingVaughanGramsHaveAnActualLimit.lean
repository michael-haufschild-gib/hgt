import GaloisForLFunctions.BezoutValuationIncidence.PositiveFloorMajorantsControlPronicEnergy
import GaloisForLFunctions.BezoutValuationIncidence.UniformHarmonicVaughanGramsAtHalfDamping
import GaloisForLFunctions.BezoutValuationIncidence.MovingVaughanRowsConvergeCellByCell
import GaloisForLFunctions.HTGeometry.MovingTruncationsPreserveDominatedLimits

/-!
The common endpoint envelope makes every limiting Vaughan pairing absolutely
summable. Moving remainders converge in pronic norm, and removing the harmonic
rank-one term recovers their actual infinite Gram at independent horizons.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- Every endpoint remainder pairing has one common absolutely summable cell envelope. -/
theorem exists_summable_pmPronicVaughanSmoothRemainder_half_pair_envelope :
    ∃ g : ℕ → ℝ, Summable g ∧ (∀ n, 0 ≤ g n) ∧ ∀ U V n : ℕ, ∀ i j : Fin 5,
      |pmPronicVaughanSmoothRemainder (1 / 2) U V n i *
        pmPronicVaughanSmoothRemainder (1 / 2) U V n j / (pronicSeq n : ℝ)| ≤ g n := by
  obtain ⟨g, hg, hg0, hbound⟩ := exists_summable_pmPronicVaughanSmoothRemainder_half_envelope
  refine ⟨g, hg, hg0, fun U V n i j => ?_⟩
  have hsq (k : Fin 5) :
      pmPronicVaughanSmoothRemainder (1 / 2) U V n k ^ 2 / (pronicSeq n : ℝ) ≤ g n := by
    simp only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact (div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity))
      (by positivity)).trans (hbound U V n k)
  exact abs_pair_div_le_common_square_bound (Nat.cast_nonneg _) (hsq i) (hsq j)

/-- The endpoint limiting Gram is the actual infinite pronic pairing of its five limiting rows. -/
abbrev pmPronicVaughanHalfLimitGram : Matrix (Fin 5) (Fin 5) ℝ := pmPronicVaughanLimitGram (1 / 2)

/-- All limiting endpoint pairings are absolutely summable. -/
theorem summable_pmPronicVaughanHalfLimitGram_terms (i j : Fin 5) :
    Summable (fun n : ℕ => pmPronicVaughanLimitFrame (1 / 2) i n *
      pmPronicVaughanLimitFrame (1 / 2) j n / (pronicSeq n : ℝ)) := by
  obtain ⟨g, hg, _hg0, hbound⟩ := exists_summable_pmPronicVaughanSmoothRemainder_half_pair_envelope
  apply hg.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs]
  have hpoint := ((tendsto_pmPronicVaughanSmoothRemainder_moving_cell
    (ε := (1 / 2 : ℝ)) (by norm_num) tendsto_id tendsto_id n i).mul
      (tendsto_pmPronicVaughanSmoothRemainder_moving_cell
        (ε := (1 / 2 : ℝ)) (by norm_num) tendsto_id tendsto_id n j)).div_const (pronicSeq n : ℝ)
  exact le_of_tendsto' hpoint.abs (fun t => hbound t t n i j)

/-- Growing horizons and both growing cutoffs recover the same infinite remainder Gram. -/
theorem tendsto_pmPronicVaughanSmoothRemainder_half_pairing
    {H U V : ℕ → ℕ} (hH : Tendsto H atTop atTop)
    (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop) (i j : Fin 5) :
    Tendsto (fun t => ∑ n ∈ Icc 1 (H t),
      pmPronicVaughanSmoothRemainder (1 / 2) (U t) (V t) n i *
        pmPronicVaughanSmoothRemainder (1 / 2) (U t) (V t) n j / (pronicSeq n : ℝ))
      atTop (𝓝 (pmPronicVaughanHalfLimitGram i j)) := by
  obtain ⟨g, hg, hg0, hbound⟩ := exists_summable_pmPronicVaughanSmoothRemainder_half_pair_envelope
  apply HTGeometry.tendsto_sum_Icc_at_moving_horizon_of_summable_bound hH hg hg0
    (by simp only [pronicSeq, Nat.cast_zero, zero_mul, div_zero])
    (fun t n => hbound (U t) (V t) n i j)
  intro n
  exact ((tendsto_pmPronicVaughanSmoothRemainder_moving_cell
    (ε := (1 / 2 : ℝ)) (by norm_num) hU hV n i).mul
      (tendsto_pmPronicVaughanSmoothRemainder_moving_cell
        (ε := (1 / 2 : ℝ)) (by norm_num) hU hV n j)).div_const (pronicSeq n : ℝ)

/-- The moving endpoint remainders converge in the full infinite pronic square norm. -/
theorem tendsto_tsum_pmPronicVaughanSmoothRemainder_half_sub_limit_sq
    {U V : ℕ → ℕ} (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop) (i : Fin 5) :
    Tendsto (fun t => ∑' n : ℕ,
      (pmPronicVaughanSmoothRemainder (1 / 2) (U t) (V t) n i -
        pmPronicVaughanLimitFrame (1 / 2) i n) ^ 2 / (pronicSeq n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨g, hg, _hg0, hbound⟩ := exists_summable_pmPronicVaughanSmoothRemainder_half_pair_envelope
  refine tendsto_tsum_pronic_square_sub_of_summable_envelope hg
    (fun n => tendsto_pmPronicVaughanSmoothRemainder_moving_cell
      (ε := (1 / 2 : ℝ)) (by norm_num) hU hV n i) (fun t n => ?_)
  have h := hbound (U t) (V t) n i i
  simpa only [← pow_two, abs_of_nonneg (by positivity : 0 ≤
    pmPronicVaughanSmoothRemainder (1 / 2) (U t) (V t) n i ^ 2 / (pronicSeq n : ℝ))] using h

/-- The same endpoint convergence holds at any moving finite horizon, including bounded horizons. -/
theorem tendsto_pronicNorm_pmPronicVaughanSmoothRemainder_half_sub_limit
    {U V : ℕ → ℕ} (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop)
    (H : ℕ → ℕ) (i : Fin 5) :
    Tendsto (fun t => pronicNorm (fun n =>
      pmPronicVaughanSmoothRemainder (1 / 2) (U t) (V t) n i -
        pmPronicVaughanLimitFrame (1 / 2) i n) (H t)) atTop (𝓝 0) := by
  obtain ⟨g, hg, _hg0, hbound⟩ := exists_summable_pmPronicVaughanSmoothRemainder_half_pair_envelope
  refine tendsto_pronicNorm_sub_at_moving_horizon_of_summable_envelope hg
    (fun n => tendsto_pmPronicVaughanSmoothRemainder_moving_cell
      (ε := (1 / 2 : ℝ)) (by norm_num) hU hV n i) (fun t n => ?_) H
  have h := hbound (U t) (V t) n i i
  simpa only [← pow_two, abs_of_nonneg (by positivity : 0 ≤
    pmPronicVaughanSmoothRemainder (1 / 2) (U t) (V t) n i ^ 2 / (pronicSeq n : ℝ))] using h

/-- Independently growing cutoffs and horizon recover the actual endpoint Gram after harmonic renormalization. -/
theorem tendsto_pmPronicVaughanCentredGram_half_sub_harmonic
    {H U V : ℕ → ℕ} (hH : Tendsto H atTop atTop)
    (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop) (i j : Fin 5) :
    Tendsto (fun t => pmPronicVaughanCentredGram (1 / 2) (U t) (V t) (H t) i j -
      (subHalfZetaCoeff (1 / 2) * deningerHarmonicPartial (U t) * deningerHarmonicPartial (V t)) ^ 2 *
        pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j *
          (∑ n ∈ Icc 1 (H t), 1 / ((n : ℝ) + 1)))
      atTop (𝓝 (pmPronicVaughanHalfLimitGram i j)) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_pmPronicVaughanSmoothRemainder_half_mixed_and_energy_bound
  let a : Fin 5 → ℕ → ℝ := fun k t => subHalfZetaCoeff (1 / 2) * deningerHarmonicPartial (U t) *
    deningerHarmonicPartial (V t) * pmPronicVaughanSmoothSigns k
  let r : Fin 5 → ℕ → ℕ → ℝ := fun k t n => pmPronicVaughanSmoothRemainder (1 / 2) (U t) (V t) n k
  let M : Fin 5 → ℕ → ℝ := fun k t => ∑ n ∈ Icc 1 (H t),
    Real.sqrt (n : ℝ) * r k t n / ((n : ℝ) * ((n : ℝ) + 1))
  have hHarmonic : Tendsto deningerHarmonicPartial atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using Sieve.tendsto_log_pow_mul_deningerHarmonicPartial_zero 0
  have ha (k : Fin 5) : Tendsto (a k) atTop (𝓝 0) := by
    simpa only [a, Function.comp_def, mul_zero, zero_mul] using
      (((hHarmonic.comp hU).const_mul (subHalfZetaCoeff (1 / 2))).mul
        (hHarmonic.comp hV)).mul_const (pmPronicVaughanSmoothSigns k)
  have hM (k : Fin 5) (t : ℕ) : |M k t| ≤ C := by
    calc
      _ ≤ ∑ n ∈ Icc 1 (H t),
          |Real.sqrt (n : ℝ) * r k t n / ((n : ℝ) * ((n : ℝ) + 1))| := abs_sum_le_sum_abs _ _
      _ = ∑ n ∈ Icc 1 (H t),
          Real.sqrt (n : ℝ) * |r k t n| / ((n : ℝ) * ((n : ℝ) + 1)) := by
        apply sum_congr rfl
        intro n _
        rw [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1))]
      _ ≤ C := (hbound (U t) (V t) (H t) k).1
  have hproduct (k l : Fin 5) : Tendsto (fun t => a k t * M l t) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (Eventually.of_forall fun t => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM l t) (abs_nonneg _)
    · simpa only [abs_zero, zero_mul] using (ha k).abs.mul_const C
  have heq (t : ℕ) : pmPronicVaughanCentredGram (1 / 2) (U t) (V t) (H t) i j -
      (subHalfZetaCoeff (1 / 2) * deningerHarmonicPartial (U t) * deningerHarmonicPartial (V t)) ^ 2 *
        pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j *
          (∑ n ∈ Icc 1 (H t), 1 / ((n : ℝ) + 1)) =
      a i t * M j t + a j t * M i t +
        ∑ n ∈ Icc 1 (H t), r i t n * r j t n / (pronicSeq n : ℝ) := by
    have haa : a i t * a j t =
        (subHalfZetaCoeff (1 / 2) * deningerHarmonicPartial (U t) * deningerHarmonicPartial (V t)) ^ 2 *
          pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j := by
      dsimp only [a]
      ring
    rw [← haa]
    have hrow (k : Fin 5) (n : ℕ) : pmPronicVaughanCentredPiece (1 / 2) (U t) (V t) n k =
        a k t * Real.sqrt (n : ℝ) + r k t n := by
      dsimp only [a, r, pmPronicVaughanSmoothRemainder]
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring, ← Real.sqrt_eq_rpow]
      ring
    simp only [M, pmPronicVaughanCentredGram, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    simp only [hrow, pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hprod : (a i t * Real.sqrt (n : ℝ) + r i t n) *
        (a j t * Real.sqrt (n : ℝ) + r j t n) =
          a i t * a j t * n + a i t * Real.sqrt (n : ℝ) * r j t n +
            a j t * Real.sqrt (n : ℝ) * r i t n + r i t n * r j t n := by
      calc
        _ = a i t * a j t * Real.sqrt (n : ℝ) ^ 2 +
            a i t * Real.sqrt (n : ℝ) * r j t n +
              a j t * Real.sqrt (n : ℝ) * r i t n + r i t n * r j t n := by ring
        _ = _ := by rw [Real.sq_sqrt hn0.le]
    rw [hprod]
    field_simp [hn0.ne', (show (n : ℝ) + 1 ≠ 0 by positivity)] <;> ring
  have hlim := ((hproduct i j).add (hproduct j i)).add
    (tendsto_pmPronicVaughanSmoothRemainder_half_pairing hH hU hV i j)
  simpa only [zero_add, ← heq] using hlim

#print axioms exists_summable_pmPronicVaughanSmoothRemainder_half_pair_envelope
#print axioms summable_pmPronicVaughanHalfLimitGram_terms
#print axioms tendsto_pmPronicVaughanSmoothRemainder_half_pairing
#print axioms tendsto_tsum_pmPronicVaughanSmoothRemainder_half_sub_limit_sq
#print axioms tendsto_pronicNorm_pmPronicVaughanSmoothRemainder_half_sub_limit
#print axioms tendsto_pmPronicVaughanCentredGram_half_sub_harmonic
end GaloisForLFunctions.BezoutValuationIncidence

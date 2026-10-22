import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarCovarianceHardCore
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# The literal first SP-E covariance-gap coefficient is unbounded

The matched--quantile covariance hard core rewrites the strict-cross source as an adjacent-gap
Abel sum.  This file isolates its first coefficient.  At the cutoff ending at a prime `p`, that
coefficient contains the prime atom with a positive centroid displacement and is at least
`criticalMellinAtomWeight 2 * log p`.  Along the prime cutoffs it therefore tends to `+∞`.

This is a no-go for any proposed cutoff-uniform control which treats the Abel coefficients as
fixed or local.  It does not estimate the signed covariance sum, the displacement debt, the
terminal interaction, or either gauge residue: a proof of the full SP-E bound must still exhibit
their literal collective cancellation.
-/

open Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

private theorem ccmActualHeadMatchedPolarCentroid_ge_two_mul_sqrt
    {n : ℕ} (hn : 0 < n) :
    2 * Real.sqrt (n : ℝ) ≤ ccmActualHeadMatchedPolarCentroid n := by
  have hsq := ccmActualHeadMatchedPolarCentroid_sq n hn
  have hcent : 0 < ccmActualHeadMatchedPolarCentroid n :=
    ccmActualHeadMatchedPolarCentroid_pos n
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (criticalMellinAtomWeight n)]

private theorem ccmActualHeadMatchedPolarCentroid_two_le_three :
    ccmActualHeadMatchedPolarCentroid 2 ≤ 3 := by
  have hsq := ccmActualHeadMatchedPolarCentroid_sq 2 (by omega)
  have hcent : 0 < ccmActualHeadMatchedPolarCentroid 2 :=
    ccmActualHeadMatchedPolarCentroid_pos 2
  have hweight : criticalMellinAtomWeight 2 ≤ 2 :=
    criticalMellinAtomWeight_le_two_of_pos (by omega)
  have hweight0 : 0 ≤ criticalMellinAtomWeight 2 :=
    criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
  nlinarith [sq_nonneg (criticalMellinAtomWeight 2)]

private theorem sqrt_le_ccmActualHeadMatchedPolarCentroid_sub_two
    {n : ℕ} (hn : 9 ≤ n) :
    Real.sqrt (n : ℝ) ≤
      ccmActualHeadMatchedPolarCentroid n - ccmActualHeadMatchedPolarCentroid 2 := by
  have hnpos : 0 < n := by omega
  have hcent := ccmActualHeadMatchedPolarCentroid_ge_two_mul_sqrt hnpos
  have htwo := ccmActualHeadMatchedPolarCentroid_two_le_three
  have hsqrt : (3 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have hsq : Real.sqrt (9 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast hn
    norm_num at hsq ⊢
    exact hsq
  linarith

private theorem criticalMellinAtomWeight_mul_sqrt_prime
    (p : Nat.Primes) :
    criticalMellinAtomWeight (p : ℕ) * Real.sqrt (p : ℝ) = Real.log (p : ℝ) := by
  unfold criticalMellinAtomWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime p.2]
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow]
  field_simp [Real.sqrt_ne_zero'.mpr hp]

private theorem ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_zero_eq
    (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel K 0 =
      criticalMellinAtomWeight 2 *
        ∑ i ∈ Finset.range (K + 1), criticalMellinAtomWeight (i + 2) *
          (ccmActualHeadMatchedPolarCentroid (i + 2) -
            ccmActualHeadMatchedPolarCentroid 2) := by
  unfold ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel
    ccmActualHeadParabolicMass
  have hzero_weight :
      (∑ i ∈ Finset.range (0 + 1), criticalMellinAtomWeight (i + 2)) =
        criticalMellinAtomWeight 2 := by
    norm_num
  have hzero_centroid :
      (∑ i ∈ Finset.range (0 + 1),
        criticalMellinAtomWeight (i + 2) * ccmActualHeadMatchedPolarCentroid (i + 2)) =
        criticalMellinAtomWeight 2 * ccmActualHeadMatchedPolarCentroid 2 := by
    norm_num
  rw [hzero_weight, hzero_centroid]
  calc
    (∑ i ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (i + 2) * ccmActualHeadMatchedPolarCentroid (i + 2)) *
        criticalMellinAtomWeight 2 -
      (∑ i ∈ Finset.range (K + 1), criticalMellinAtomWeight (i + 2)) *
        (criticalMellinAtomWeight 2 * ccmActualHeadMatchedPolarCentroid 2) =
      criticalMellinAtomWeight 2 *
        ((∑ i ∈ Finset.range (K + 1),
          criticalMellinAtomWeight (i + 2) * ccmActualHeadMatchedPolarCentroid (i + 2)) -
          (∑ i ∈ Finset.range (K + 1), criticalMellinAtomWeight (i + 2)) *
            ccmActualHeadMatchedPolarCentroid 2) := by ring
    _ = criticalMellinAtomWeight 2 *
        (∑ i ∈ Finset.range (K + 1),
          (criticalMellinAtomWeight (i + 2) * ccmActualHeadMatchedPolarCentroid (i + 2) -
            criticalMellinAtomWeight (i + 2) * ccmActualHeadMatchedPolarCentroid 2)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = _ := by
      apply congrArg (fun x : ℝ => criticalMellinAtomWeight 2 * x)
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- At every prime cutoff at least nine, the first literal Abel coefficient contains a positive
prime contribution of size `criticalMellinAtomWeight 2 * log p`. -/
theorem criticalMellinAtomWeight_two_mul_log_le_ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_zero
    (p : Nat.Primes) (hp9 : 9 ≤ (p : ℕ)) :
    criticalMellinAtomWeight 2 * Real.log (p : ℝ) ≤
      ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel ((p : ℕ) - 2) 0 := by
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hw2 : 0 ≤ criticalMellinAtomWeight 2 := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
  have hgap := sqrt_le_ccmActualHeadMatchedPolarCentroid_sub_two hp9
  have hterms : ∀ i ∈ Finset.range ((p : ℕ) - 2 + 1),
      0 ≤ criticalMellinAtomWeight (i + 2) *
        (ccmActualHeadMatchedPolarCentroid (i + 2) -
          ccmActualHeadMatchedPolarCentroid 2) := by
    intro i hi
    apply mul_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _)
    by_cases hi0 : i = 0
    · subst i
      simp
    · apply sub_nonneg.mpr
      have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
      simpa [Nat.add_comm] using
        (strictMono_ccmActualHeadMatchedPolarCentroid_shift_two hi_pos).le
  have hmem : (p : ℕ) - 2 ∈ Finset.range ((p : ℕ) - 2 + 1) :=
    Finset.mem_range.mpr (by omega)
  have hterm :
      criticalMellinAtomWeight (p : ℕ) *
        (ccmActualHeadMatchedPolarCentroid (p : ℕ) -
          ccmActualHeadMatchedPolarCentroid 2) ≤
        ∑ i ∈ Finset.range ((p : ℕ) - 2 + 1),
          criticalMellinAtomWeight (i + 2) *
            (ccmActualHeadMatchedPolarCentroid (i + 2) -
              ccmActualHeadMatchedPolarCentroid 2) := by
    simpa [Nat.sub_add_cancel hp2] using
      (Finset.single_le_sum hterms hmem)
  rw [ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_zero_eq]
  calc
    criticalMellinAtomWeight 2 * Real.log (p : ℝ) =
        criticalMellinAtomWeight 2 *
          (criticalMellinAtomWeight (p : ℕ) * Real.sqrt (p : ℝ)) := by
            rw [criticalMellinAtomWeight_mul_sqrt_prime]
    _ ≤ criticalMellinAtomWeight 2 *
        (criticalMellinAtomWeight (p : ℕ) *
          (ccmActualHeadMatchedPolarCentroid (p : ℕ) -
            ccmActualHeadMatchedPolarCentroid 2)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hgap (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _)) hw2
    _ ≤ _ := mul_le_mul_of_nonneg_left hterm hw2

/-- **First-coefficient growth no-go.** The first literal global Abel coefficient diverges along
the cutoffs ending at the successive primes.  Therefore it cannot be replaced by a fixed or
cutoff-local coefficient in a cutoff-uniform SP-E estimate. -/
theorem tendsto_ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_nthPrime_zero_atTop :
    Tendsto (fun j : ℕ =>
      ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel (nth_prime j - 2) 0)
      atTop atTop := by
  have hw2 : 0 < criticalMellinAtomWeight 2 :=
    criticalMellinAtomWeight_pos Nat.prime_two.isPrimePow
  have hprimeCast : Tendsto (fun j : ℕ => (nth_prime j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nth_prime_atTop
  have hlog : Tendsto (fun j : ℕ => Real.log (nth_prime j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hprimeCast
  have hscaled : Tendsto (fun j : ℕ =>
      criticalMellinAtomWeight 2 * Real.log (nth_prime j : ℝ)) atTop atTop :=
    hlog.const_mul_atTop hw2
  refine tendsto_atTop.2 fun R => ?_
  filter_upwards [hscaled.eventually_ge_atTop R,
    tendsto_nth_prime_atTop.eventually_ge_atTop 9] with j hR hj9
  let p : Nat.Primes := ⟨nth_prime j,
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j⟩
  have hp9 : 9 ≤ (p : ℕ) := hj9
  have hbound :=
    criticalMellinAtomWeight_two_mul_log_le_ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_zero
      p hp9
  exact hR.trans (by simpa [p] using hbound)

end RHTower

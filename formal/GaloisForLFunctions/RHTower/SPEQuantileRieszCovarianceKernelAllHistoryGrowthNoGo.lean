import GaloisForLFunctions.RHTower.SPEQuantileRieszCovarianceKernelGrowthNoGo
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicCenteredBoundary

/-!
# All-history growth of the literal SP-E covariance kernel

The existing first-coordinate no-go shows that the literal global Abel coefficient at history
index zero diverges along prime cutoffs.  This file closes the stronger source fact: every fixed
history index has the same unbounded prime-cutoff growth, with the positive finite-prefix mass as
its logarithmic coefficient.  Thus no finite stationary family of local history coordinates can
carry the literal SP-E covariance into a cofinal Route-P transport.  Any viable transport must
retain a growing two-history datum and cancel it jointly with the displacement debt, terminal, and
physical-wall gauges.

No bound for that completed cancellation, nor an RH consequence, is claimed here.
-/

open Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

private theorem centroid_prefix_le_terminal (r : ℕ) :
    (∑ i ∈ Finset.range (r + 1),
      criticalMellinAtomWeight (i + 2) *
        ccmActualHeadMatchedPolarCentroid (i + 2)) ≤
      ccmActualHeadMatchedPolarCentroid (r + 2) * ccmActualHeadParabolicMass r := by
  unfold ccmActualHeadParabolicMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hir : i ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hcent : ccmActualHeadMatchedPolarCentroid (i + 2) ≤
      ccmActualHeadMatchedPolarCentroid (r + 2) :=
    strictMono_ccmActualHeadMatchedPolarCentroid_shift_two.monotone hir
  calc
    criticalMellinAtomWeight (i + 2) * ccmActualHeadMatchedPolarCentroid (i + 2) ≤
        criticalMellinAtomWeight (i + 2) * ccmActualHeadMatchedPolarCentroid (r + 2) :=
      mul_le_mul_of_nonneg_left hcent (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _)
    _ = _ := mul_comm _ _

private theorem centroid_ge_two_mul_sqrt {n : ℕ} (hn : 0 < n) :
    2 * Real.sqrt (n : ℝ) ≤ ccmActualHeadMatchedPolarCentroid n := by
  have hsq := ccmActualHeadMatchedPolarCentroid_sq n hn
  have hcent : 0 < ccmActualHeadMatchedPolarCentroid n :=
    ccmActualHeadMatchedPolarCentroid_pos n
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (criticalMellinAtomWeight n)]

private theorem atomWeight_mul_sqrt_prime (p : Nat.Primes) :
    criticalMellinAtomWeight (p : ℕ) * Real.sqrt (p : ℝ) = Real.log (p : ℝ) := by
  unfold criticalMellinAtomWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime p.2]
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow]
  field_simp [Real.sqrt_ne_zero'.mpr hp]

private theorem mass_mul_log_le_covarianceGapKernel_of_centroid_lt_sqrt
    (r : ℕ) (p : Nat.Primes) (hp : r + 3 ≤ (p : ℕ))
    (hsep : ccmActualHeadMatchedPolarCentroid (r + 2) < Real.sqrt (p : ℝ)) :
    ccmActualHeadParabolicMass r * Real.log (p : ℝ) ≤
      ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel ((p : ℕ) - 2) r := by
  have hp3 : 3 ≤ (p : ℕ) := by omega
  have hpr : r ≤ (p : ℕ) - 3 := by omega
  have hprev := ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_nonneg ((p : ℕ) - 3) r hpr
  have hdelta := ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_succ_sub ((p : ℕ) - 3) r
  have hsub_one : (p : ℕ) - 3 + 1 = (p : ℕ) - 2 := by omega
  have hsub_three : (p : ℕ) - 3 + 3 = (p : ℕ) := Nat.sub_add_cancel hp3
  have hdelta' :
      ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel ((p : ℕ) - 2) r -
          ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel ((p : ℕ) - 3) r =
        criticalMellinAtomWeight (p : ℕ) *
          (ccmActualHeadMatchedPolarCentroid (p : ℕ) * ccmActualHeadParabolicMass r -
            ∑ i ∈ Finset.range (r + 1), criticalMellinAtomWeight (i + 2) *
              ccmActualHeadMatchedPolarCentroid (i + 2)) := by
    simpa only [hsub_one, hsub_three, ccmActualHeadParabolicMass] using hdelta
  have hcentp : 2 * Real.sqrt (p : ℝ) ≤ ccmActualHeadMatchedPolarCentroid (p : ℕ) :=
    centroid_ge_two_mul_sqrt (by exact_mod_cast p.2.pos)
  have hcentgap : Real.sqrt (p : ℝ) ≤
      ccmActualHeadMatchedPolarCentroid (p : ℕ) -
        ccmActualHeadMatchedPolarCentroid (r + 2) := by
    nlinarith
  have hprefix := centroid_prefix_le_terminal r
  have hmass : 0 ≤ ccmActualHeadParabolicMass r :=
    (ccmActualHeadParabolicMass_pos r).le
  have hinner : ccmActualHeadParabolicMass r * Real.sqrt (p : ℝ) ≤
      ccmActualHeadMatchedPolarCentroid (p : ℕ) * ccmActualHeadParabolicMass r -
        ∑ i ∈ Finset.range (r + 1), criticalMellinAtomWeight (i + 2) *
          ccmActualHeadMatchedPolarCentroid (i + 2) := by
    have hmul := mul_le_mul_of_nonneg_left hcentgap hmass
    nlinarith
  have hweight : 0 ≤ criticalMellinAtomWeight (p : ℕ) := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
  have hscaled := mul_le_mul_of_nonneg_left hinner hweight
  calc
    ccmActualHeadParabolicMass r * Real.log (p : ℝ) =
        ccmActualHeadParabolicMass r *
          (criticalMellinAtomWeight (p : ℕ) * Real.sqrt (p : ℝ)) := by
      rw [atomWeight_mul_sqrt_prime]
    _ = criticalMellinAtomWeight (p : ℕ) *
          (ccmActualHeadParabolicMass r * Real.sqrt (p : ℝ)) := by
      ring
    _ ≤ criticalMellinAtomWeight (p : ℕ) *
        (ccmActualHeadMatchedPolarCentroid (p : ℕ) * ccmActualHeadParabolicMass r -
          ∑ i ∈ Finset.range (r + 1), criticalMellinAtomWeight (i + 2) *
            ccmActualHeadMatchedPolarCentroid (i + 2)) := hscaled
    _ = ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel ((p : ℕ) - 2) r -
          ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel ((p : ℕ) - 3) r := hdelta'.symm
    _ ≤ _ := by linarith

/-- **All-history covariance growth no-go.** For every fixed literal adjacent-history index,
the cutoff-dependent SP-E covariance coefficient diverges to `+∞` along the successive prime
cutoffs.  Its source lower bound is the positive mass of that retained history prefix times
`log p`; consequently no finite stationary or cutoff-local history representation can carry the
literal covariance kernel cofinally. -/
theorem tendsto_ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_nthPrime_atTop
    (r : ℕ) :
    Tendsto (fun j : ℕ =>
      ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel (nth_prime j - 2) r)
      atTop atTop := by
  have hmass : 0 < ccmActualHeadParabolicMass r := ccmActualHeadParabolicMass_pos r
  have hprimeCast : Tendsto (fun j : ℕ => (nth_prime j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nth_prime_atTop
  have hlog : Tendsto (fun j : ℕ => Real.log (nth_prime j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hprimeCast
  have hscaled : Tendsto (fun j : ℕ =>
      ccmActualHeadParabolicMass r * Real.log (nth_prime j : ℝ)) atTop atTop :=
    hlog.const_mul_atTop hmass
  obtain ⟨N, hN⟩ := exists_nat_gt (ccmActualHeadMatchedPolarCentroid (r + 2) ^ 2)
  let N0 := max N (r + 3)
  refine tendsto_atTop.2 fun R => ?_
  filter_upwards [hscaled.eventually_ge_atTop R,
    tendsto_nth_prime_atTop.eventually_ge_atTop N0] with j hR hj
  let p : Nat.Primes := ⟨nth_prime j,
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j⟩
  have hpbound : r + 3 ≤ (p : ℕ) := by
    dsimp only [p]
    exact (le_max_right N (r + 3)).trans hj
  have hNbound : N ≤ (p : ℕ) := by
    dsimp only [p]
    exact (le_max_left N (r + 3)).trans hj
  have hsq : ccmActualHeadMatchedPolarCentroid (r + 2) ^ 2 < (p : ℝ) := by
    exact lt_of_lt_of_le hN (by exact_mod_cast hNbound)
  have hcent : 0 < ccmActualHeadMatchedPolarCentroid (r + 2) :=
    ccmActualHeadMatchedPolarCentroid_pos _
  have hsqrt0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hroot_sq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsep : ccmActualHeadMatchedPolarCentroid (r + 2) < Real.sqrt (p : ℝ) := by
    nlinarith
  have hlower := mass_mul_log_le_covarianceGapKernel_of_centroid_lt_sqrt r p hpbound hsep
  exact hR.trans (by simpa [p] using hlower)

end RHTower

end

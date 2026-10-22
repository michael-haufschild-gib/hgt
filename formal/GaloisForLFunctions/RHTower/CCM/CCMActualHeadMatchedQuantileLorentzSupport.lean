import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileLorentzGraphWall
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePTerminalCoefficientSourceEnvelope

/-!
# Prime-power support of the literal Lorentz graph current

The matched--quantile Lorentz cone escape compares unweighted adjacent centroid slopes. The
literal strict-cross source, however, contains the product of two critical-Mellin atom weights.
This module proves its exact support restriction: an edge can carry nonzero source current only
when both endpoints are prime powers.

Consequently the unweighted cone-escape theorem alone does not refute a support-sensitive
nonlocal graph wall. Such a wall still needs a cofinal bound for resistance on the retained
prime-power-pair support; this module supplies no such bound.
-/

noncomputable section

namespace RHTower

open Filter

/-- A zero left von-Mangoldt atom kills complete coupled Lorentz current. -/
theorem ccmActualHeadMatchedQuantileLorentzEdgeCurrent_eq_zero_of_not_isPrimePow_left
    (m n : ℕ) (hm : ¬ IsPrimePow (m + 2)) :
    ccmActualHeadMatchedQuantileLorentzEdgeCurrent m n = 0 := by
  unfold ccmActualHeadMatchedQuantileLorentzEdgeCurrent
  rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge]
  unfold criticalMellinAtomWeight
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hm]
  ring

/-- A zero right von-Mangoldt atom kills complete coupled Lorentz current. -/
theorem ccmActualHeadMatchedQuantileLorentzEdgeCurrent_eq_zero_of_not_isPrimePow_right
    (m n : ℕ) (hn : ¬ IsPrimePow (n + 2)) :
    ccmActualHeadMatchedQuantileLorentzEdgeCurrent m n = 0 := by
  unfold ccmActualHeadMatchedQuantileLorentzEdgeCurrent
  rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge]
  unfold criticalMellinAtomWeight
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
  ring

/-- Every nonzero literal Lorentz edge is supported on a pair of genuine prime-power source
atoms. Hence a resistance obstruction must be proved on weighted support, not merely ambient
successor graph. -/
theorem ccmActualHeadMatchedQuantileLorentzEdgeCurrent_nonzero_support
    (m n : ℕ) (hcurrent : ccmActualHeadMatchedQuantileLorentzEdgeCurrent m n ≠ 0) :
    IsPrimePow (m + 2) ∧ IsPrimePow (n + 2) := by
  constructor
  · by_contra hm
    exact hcurrent
      (ccmActualHeadMatchedQuantileLorentzEdgeCurrent_eq_zero_of_not_isPrimePow_left m n hm)
  · by_contra hn
    exact hcurrent
      (ccmActualHeadMatchedQuantileLorentzEdgeCurrent_eq_zero_of_not_isPrimePow_right m n hn)

/-- A prime-successor cone edge is absent from literal source whenever its right endpoint is not
prime power. -/
theorem ccmActualHeadMatchedQuantilePrimeSuccessorLorentzEdgeCurrent_eq_zero
    (p : Nat.Primes) (hnext : ¬ IsPrimePow ((p : ℕ) + 1)) :
    ccmActualHeadMatchedQuantileLorentzEdgeCurrent ((p : ℕ) - 2) ((p : ℕ) - 1) = 0 := by
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hindex : (p : ℕ) - 1 + 2 = (p : ℕ) + 1 := by omega
  have hright : ¬ IsPrimePow ((p : ℕ) - 1 + 2) := by
    simpa only [hindex] using hnext
  exact
    ccmActualHeadMatchedQuantileLorentzEdgeCurrent_eq_zero_of_not_isPrimePow_right
      ((p : ℕ) - 2) ((p : ℕ) - 1) hright

/-- A zero left von-Mangoldt atom also removes the complementary resistance. -/
theorem ccmActualHeadMatchedQuantileLorentzEdgeResistance_eq_zero_of_not_isPrimePow_left
    (m n : ℕ) (hm : ¬ IsPrimePow (m + 2)) :
    ccmActualHeadMatchedQuantileLorentzEdgeResistance m n = 0 := by
  unfold ccmActualHeadMatchedQuantileLorentzEdgeResistance
  unfold criticalMellinAtomWeight
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hm]
  ring

/-- A zero right von-Mangoldt atom also removes the complementary resistance. -/
theorem ccmActualHeadMatchedQuantileLorentzEdgeResistance_eq_zero_of_not_isPrimePow_right
    (m n : ℕ) (hn : ¬ IsPrimePow (n + 2)) :
    ccmActualHeadMatchedQuantileLorentzEdgeResistance m n = 0 := by
  unfold ccmActualHeadMatchedQuantileLorentzEdgeResistance
  unfold criticalMellinAtomWeight
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
  ring

/-- Literal finite edges retained by the completed source: both endpoints carry a nonzero
von-Mangoldt atom. -/
def ccmActualHeadMatchedQuantileLorentzActiveEdgeSet (K : ℕ) :=
  (ccmActualHeadMatchedQuantileLorentzEdgeSet K).filter fun e =>
    IsPrimePow (e.1 + 2) ∧ IsPrimePow (e.2 + 2)

/-- **Exact active resistance reduction.** The finite resistance in the coupled graph wall is
already supported on prime-power pairs. This removes all zero-atom geometric edges before the
open cofinal estimate, without changing the literal wall. -/
theorem ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance_eq_active_sum (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance K =
      ∑ e ∈ ccmActualHeadMatchedQuantileLorentzActiveEdgeSet K,
        ccmActualHeadMatchedQuantileLorentzEdgeResistance e.1 e.2 := by
  unfold ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance
    ccmActualHeadMatchedQuantileLorentzActiveEdgeSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  rintro ⟨m, n⟩ hmem
  by_cases hm : IsPrimePow (m + 2)
  · by_cases hn : IsPrimePow (n + 2)
    · simp [hm, hn]
    · simp [hm, hn, ccmActualHeadMatchedQuantileLorentzEdgeResistance_eq_zero_of_not_isPrimePow_right]
  · simp [hm, ccmActualHeadMatchedQuantileLorentzEdgeResistance_eq_zero_of_not_isPrimePow_left]

/-- Every literal Lorentz edge has resistance at least its bare positive pair mass.  This is a
source identity plus the common orientation of matched and quantile centroids. -/
theorem ccmActualHeadMatchedQuantileLorentzEdgeResistance_ge_weight_product_half
    {m n : ℕ} (hmn : m ≠ n) :
    criticalMellinAtomWeight (m + 2) * criticalMellinAtomWeight (n + 2) / 2 ≤
      ccmActualHeadMatchedQuantileLorentzEdgeResistance m n := by
  let c := ccmActualHeadMatchedPolarCentroid (n + 2) -
    ccmActualHeadMatchedPolarCentroid (m + 2)
  let q := ccmActualHeadQuantilePolarCentroid (n + 2) -
    ccmActualHeadQuantilePolarCentroid (m + 2)
  let w := criticalMellinAtomWeight (m + 2) * criticalMellinAtomWeight (n + 2)
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact ccmActualHeadMatchedPolarCentroid_shift_two_gap_ne_zero hmn
  have hcq : 0 ≤ c * q := by
    dsimp only [c, q]
    exact ccmActualHeadMatchedQuantileCentroidPair_comonotone m n
  have hqdiv : 0 ≤ q / c := by
    rw [show q / c = (c * q) / (c * c) by field_simp [hc]]
    exact div_nonneg hcq (mul_self_nonneg c)
  have hratio : 1 ≤ (c + q) / c := by
    rw [show (c + q) / c = 1 + q / c by field_simp [hc]]
    linarith
  have hw : 0 ≤ w := by
    dsimp only [w]
    exact mul_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _) (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _)
  have hwdiv : 0 ≤ w / 2 := div_nonneg hw (by norm_num)
  change w / 2 ≤ w / 2 * ((c + q) / c)
  simpa using mul_le_mul_of_nonneg_left hratio hwdiv

/-- Removing the base prime `2` from a finite physical head subtracts exactly its one atom
weight. -/
theorem ccmActualHeadParabolicBaseOffDiagonalMass_eq_mass_sub_weightTwo (K : ℕ) :
    ∑ n ∈ (Finset.range (K + 1)).erase 0,
      criticalMellinAtomWeight (n + 2) =
        ccmActualHeadParabolicMass K - criticalMellinAtomWeight 2 := by
  have hmem : 0 ∈ Finset.range (K + 1) := by simp
  unfold ccmActualHeadParabolicMass
  rw [← Finset.sum_erase_add _ _ hmem]
  norm_num

/-- Fixed-prime lower envelope for literal finite Lorentz resistance.  It exposes the exact
critical-Mellin mass which raw Cauchy resistance must carry. -/
theorem ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance_ge_baseOffDiagonalMass
    (K : ℕ) :
    (criticalMellinAtomWeight 2 / 2) *
        (∑ n ∈ (Finset.range (K + 1)).erase 0,
          criticalMellinAtomWeight (n + 2)) ≤
      ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance K := by
  calc
    (criticalMellinAtomWeight 2 / 2) *
        (∑ n ∈ (Finset.range (K + 1)).erase 0,
          criticalMellinAtomWeight (n + 2)) =
        ∑ n ∈ (Finset.range (K + 1)).erase 0,
          criticalMellinAtomWeight 2 * criticalMellinAtomWeight (n + 2) / 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ ∑ n ∈ (Finset.range (K + 1)).erase 0,
        ccmActualHeadMatchedQuantileLorentzEdgeResistance 0 n := by
      apply Finset.sum_le_sum
      intro n hn
      simpa using ccmActualHeadMatchedQuantileLorentzEdgeResistance_ge_weight_product_half
        (Ne.symm (Finset.mem_erase.mp hn).1)
    _ ≤ ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance K := by
      have houter :
          (∑ n ∈ (Finset.range (K + 1)).erase 0,
            ccmActualHeadMatchedQuantileLorentzEdgeResistance 0 n) ≤
          ∑ m ∈ Finset.range (K + 1),
            ∑ n ∈ (Finset.range (K + 1)).erase m,
              ccmActualHeadMatchedQuantileLorentzEdgeResistance m n := by
        exact Finset.single_le_sum
          (s := Finset.range (K + 1))
          (f := fun m => ∑ n ∈ (Finset.range (K + 1)).erase m,
            ccmActualHeadMatchedQuantileLorentzEdgeResistance m n)
          (fun m hm => Finset.sum_nonneg fun n hn =>
            ccmActualHeadMatchedQuantileLorentzEdgeResistance_nonneg
              (Ne.symm (Finset.mem_erase.mp hn).1))
          (Finset.mem_range.mpr (Nat.succ_pos K))
      simpa [ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance,
        ccmActualHeadMatchedQuantileLorentzEdgeSet, Finset.sum_sigma] using houter

/-- **Raw-resistance no-go.** Literal finite Lorentz resistance diverges cofinally. Thus no
uniform bound for this unnormalized Cauchy resistance can close the signed source wall. This
does not decide a wall which first removes dissipation-null edges exactly. -/
theorem ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance_tendsto_atTop :
    Tendsto ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance atTop atTop := by
  have hweightTwo : 0 < criticalMellinAtomWeight 2 :=
    criticalMellinAtomWeight_pos Nat.prime_two.isPrimePow
  have hcoefficient : 0 < criticalMellinAtomWeight 2 / 2 :=
    div_pos hweightTwo (by norm_num)
  apply tendsto_atTop.2
  intro B
  filter_upwards [ccmActualHeadParabolicMass_tendsto_atTop.eventually_ge_atTop
      (B / (criticalMellinAtomWeight 2 / 2) + criticalMellinAtomWeight 2)] with K hK
  have hlower := ccmActualHeadMatchedQuantileParabolicLorentzGraphResistance_ge_baseOffDiagonalMass K
  rw [ccmActualHeadParabolicBaseOffDiagonalMass_eq_mass_sub_weightTwo] at hlower
  have hsub : B / (criticalMellinAtomWeight 2 / 2) ≤
      ccmActualHeadParabolicMass K - criticalMellinAtomWeight 2 := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_right hsub hcoefficient.le
  have htarget : B ≤ (criticalMellinAtomWeight 2 / 2) *
      (ccmActualHeadParabolicMass K - criticalMellinAtomWeight 2) := by
    calc
      B = (B / (criticalMellinAtomWeight 2 / 2)) *
          (criticalMellinAtomWeight 2 / 2) := by field_simp [hcoefficient.ne']
      _ ≤ _ := by simpa [mul_comm] using hscaled
  exact htarget.trans hlower

end RHTower

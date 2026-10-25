import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ThePronicPairingHasExactDilationBlocks
import GaloisForLFunctions.ArithmeticDefectRigidity.ReceiverEnergyCrossingsHaveUnitOvershoot
import GaloisForLFunctions.ArithmeticCompensationTheory.TheNormalizedReceiverBlowUpProfile
import GaloisForLFunctions.ArithmeticDefectRigidity.TheAdmittedCofactorKernelIsUnique

/-!
# Actual cofactor diagonals are contracted-horizon energy ratios

Complete dilation blocks and the bounded final cell identify p*K(p,p)
with the limiting receiver energy ratio E(floor(T/p))/E(T). Numeric
horizon order makes this profile nonincreasing for every actual limit.
-/

section

noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- At a complete block endpoint, self-pairings scale exactly. -/
theorem pronicNorm_rowDilate_complete_blocks {p : ℕ} (hp : 1 ≤ p)
    (N : ℕ) (u : ℕ → ℝ) (hu0 : u 0 = 0) :
    pronicNorm (p * (N + 1) - 1) (rowDilate p u) ^ 2 =
      (1 / (p : ℝ)) * pronicNorm N u ^ 2 := by
  simp_rw [pronicNorm_sq]
  simpa only [pronicPairing, pow_two] using
    pronicPairing_rowDilate_complete_blocks hp N u u hu0

/-- The incomplete final dilation block changes actual energy by at most `1/p`. -/
theorem receiver_dilated_energy_horizon_error (ε : SubcriticalDamping)
    (p : ℕ+) (T : ℕ) :
    0 ≤ (1 / (p : ℝ)) * dampedMobiusEnergy ε (T / p) -
      pronicNorm T (rowDilate p (pmPowerDampedCenteredDivisorPrefix ε)) ^ 2 ∧
    (1 / (p : ℝ)) * dampedMobiusEnergy ε (T / p) -
      pronicNorm T (rowDilate p (pmPowerDampedCenteredDivisorPrefix ε)) ^ 2 ≤
        1 / (p : ℝ) := by
  let N := T / (p : ℕ)
  let A := pmPowerDampedCenteredDivisorPrefix (ε : ℝ)
  have hsandwich := pronicEnergy_rowDilate_sandwich p.property T A
    (ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero ε)
  have hupper : pronicNorm T (rowDilate p A) ^ 2 ≤
      (1 / (p : ℝ)) * dampedMobiusEnergy ε N := by
    rw [pronicNorm_sq]
    exact hsandwich.2
  refine ⟨sub_nonneg.mpr hupper, ?_⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · have hz : dampedMobiusEnergy ε N = 0 := by
      rw [hN]
      change (∑ n ∈ Icc 1 0, A n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) = 0
      simp
    change (1 / (p : ℝ)) * dampedMobiusEnergy ε N - pronicNorm T (rowDilate p A) ^ 2 ≤ _
    rw [hz, mul_zero]
    exact (sub_nonpos.mpr (sq_nonneg _)).trans (by positivity)
  · have hlower : (1 / (p : ℝ)) * dampedMobiusEnergy ε (N - 1) ≤
        pronicNorm T (rowDilate p A) ^ 2 := by
      rw [pronicNorm_sq]
      exact hsandwich.1
    have hstep := receiverEnergy_succ_le ε (N - 1)
    rw [Nat.sub_add_cancel hN] at hstep
    have hp0 : 0 ≤ 1 / (p : ℝ) := by positivity
    have hstep' := mul_le_mul_of_nonneg_left hstep hp0
    nlinarith only [hlower, hstep']

namespace ActualCofactorLimit

/-- Admission gives the exact critical diagonal, independent of subsequence. -/
theorem kernel_diag_of_admits {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (hpaid : Admits dampedMobiusEnergy ε) (p : ℕ+) :
    kernel L p p = 1 / (p : ℝ) := by
  obtain ⟨e, he, hE⟩ := exists_positive_receiverEnergy_limit_of_admits ε hpaid
  obtain ⟨K, hK⟩ := exists_cofactorGram_full_limit_of_admits ε hpaid
  have hKactual : K p p = L.kernel p p :=
    tendsto_nhds_unique ((hK p p).comp L.strictMono.tendsto_atTop) (L.converges p p)
  let U (N : ℕ) := (p : ℕ) * (N + 2) - 2
  have hU : Tendsto U atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with N hN
    dsimp only [U]
    have hmul : N + 2 ≤ (p : ℕ) * (N + 2) :=
      Nat.le_mul_of_pos_left _ p.property
    omega
  have hendpoint (N : ℕ) : U N + 1 = (p : ℕ) * ((N + 1) + 1) - 1 := by
    dsimp only [U]
    have hmul : N + 2 ≤ (p : ℕ) * (N + 2) :=
      Nat.le_mul_of_pos_left _ p.property
    rw [show N + 1 + 1 = N + 2 by omega]
    omega
  have hpair (N : ℕ) : cofactorGram ε (U N) p p =
      ((1 / (p : ℝ)) * dampedMobiusEnergy ε (N + 1)) /
        dampedMobiusEnergy ε (U N + 1) := by
    rw [cofactorGram, hendpoint]
    have hself (T : ℕ) (f : ℕ → ℝ) : pronicPairing T f f = pronicNorm T f ^ 2 := by
      rw [pronicNorm_sq]
      simp only [pronicPairing, pow_two]
    rw [hself, pronicNorm_rowDilate_complete_blocks (p := (p : ℕ)) p.property (N + 1) (pmPowerDampedCenteredDivisorPrefix (ε : ℝ))
      (ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero ε),
      pronicNorm_centeredPrefix, Real.sq_sqrt (dampedMobiusEnergy_nonneg _ _)]
  have hnum := (hE.comp (tendsto_add_atTop_nat 1)).const_mul (1 / (p : ℝ))
  have hden := hE.comp ((tendsto_add_atTop_nat 1).comp hU)
  have hlim := hnum.div hden he.ne'
  have hratio : (1 / (p : ℝ)) * e / e = 1 / (p : ℝ) := mul_div_cancel_right₀ _ he.ne'
  rw [hratio] at hlim
  have hlim' : Tendsto (fun N => cofactorGram ε (U N) p p) atTop (𝓝 (1 / (p : ℝ))) := by
    apply hlim.congr
    intro N
    exact (hpair N).symm
  exact hKactual.symm.trans (tendsto_nhds_unique ((hK p p).comp hU) hlim')

/-- Every actual diagonal reads the receiver's contracted-horizon energy ratio. -/
theorem contracted_energy_ratio_tendsto {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (p : ℕ+) :
    Tendsto (fun m => dampedMobiusEnergy ε ((L.subsequence m + 1) / p) /
      dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 ((p : ℝ) * L.kernel p p)) := by
  have hT := (tendsto_add_atTop_nat 1).comp L.strictMono.tendsto_atTop
  rcases admits_or_tendsto_atTop (ε : ℝ) with hpaid | hescape
  · obtain ⟨e, he, hE⟩ := exists_positive_receiverEnergy_limit_of_admits ε hpaid
    have hdiv : Tendsto (fun m => (L.subsequence m + 1) / (p : ℕ)) atTop atTop := by
      refine tendsto_atTop.2 fun N => ?_
      filter_upwards [hT.eventually_ge_atTop (N * (p : ℕ))] with m hm
      exact (Nat.le_div_iff_mul_le p.property).mpr hm
    have hlim := (hE.comp hdiv).div (hE.comp hT) he.ne'
    rw [div_self he.ne'] at hlim
    rw [kernel_diag_of_admits L hpaid p, mul_one_div_cancel (by positivity : (p : ℝ) ≠ 0)]
    exact hlim.congr (fun m => rfl)
  · have hE := hescape.comp hT
    have herror : Tendsto (fun m =>
        (1 / (p : ℝ)) * (dampedMobiusEnergy ε ((L.subsequence m + 1) / p) /
          dampedMobiusEnergy ε (L.subsequence m + 1)) -
        cofactorGram ε (L.subsequence m) p p) atTop (𝓝 0) := by
      have hzero : Tendsto (fun m => (1 / (p : ℝ)) /
          dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hE
      refine squeeze_zero (fun m => ?_) (fun m => ?_) hzero
      all_goals
        have h := receiver_dilated_energy_horizon_error ε p (L.subsequence m + 1)
        have hE0 := (receiverEnergy_succ_pos ε (L.subsequence m)).le
        have hself : pronicPairing (L.subsequence m + 1)
            (rowDilate p (pmPowerDampedCenteredDivisorPrefix ε))
            (rowDilate p (pmPowerDampedCenteredDivisorPrefix ε)) =
              pronicNorm (L.subsequence m + 1)
                (rowDilate p (pmPowerDampedCenteredDivisorPrefix ε)) ^ 2 := by
          rw [pronicNorm_sq]
          simp only [pronicPairing, pow_two]
        rw [cofactorGram, hself, ← mul_div_assoc, ← sub_div]
      · exact div_nonneg h.1 hE0
      · exact div_le_div_of_nonneg_right h.2 hE0
    have hsum := herror.add (L.converges p p)
    simp only [zero_add, sub_add_cancel] at hsum
    have hmul := hsum.const_mul (p : ℝ)
    apply hmul.congr
    intro m
    have hpne : (p : ℝ) ≠ 0 := by positivity
    field_simp

/-- The contracted-energy profile is nonincreasing in the integer scale. -/
theorem scaled_diagonal_antitone {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    Antitone (fun p : ℕ+ => (p : ℝ) * L.kernel p p) := by
  intro p q hpq
  apply le_of_tendsto_of_tendsto' (contracted_energy_ratio_tendsto L q)
    (contracted_energy_ratio_tendsto L p)
  intro m
  apply div_le_div_of_nonneg_right ?_ (receiverEnergy_succ_pos ε (L.subsequence m)).le
  apply dampedMobiusEnergy_mono
  exact Nat.div_le_div_left hpq p.property

end ActualCofactorLimit
end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.contracted_energy_ratio_tendsto
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.scaled_diagonal_antitone
end
end

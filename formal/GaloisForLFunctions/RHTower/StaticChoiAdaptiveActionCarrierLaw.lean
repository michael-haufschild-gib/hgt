import GaloisForLFunctions.RHTower.StaticChoiCentralizerCommutatorBridge

open scoped BigOperators Matrix ComplexConjugate
open Set Matrix

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

noncomputable section

/-- Endpoint-adaptive transverse factor forced by a requested normalized
commutator activation energy.  Truncation at zero makes the law uniform even
when the requested activation exceeds the full spectral speed budget. -/
def staticChoiAdaptiveReplicaBase
    {d : ℕ} (energy : Fin d → ℝ) (activation : ℝ) : ℝ :=
  max 0 (1 - activation / (2 * staticChoiSpeed energy) ^ (2 : ℕ))

/-- **Exact action--carrier dichotomy.** At every finite dimension, every
unitary endpoint and every replica order, near-action mass has only two
possible sources: the endpoint lies in the requested commutator-action tube,
or it pays the endpoint-adaptive transverse replica factor.  No minimum
spectral gap and no worst-spectrum threshold enter. -/
theorem directStaticChoiTargetNearActionMass_choiVector_le_adaptiveAction_add_carrier
    {d : ℕ} (hd : 0 < d)
    (energy : Fin d → ℝ)
    {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (r : ℕ) (δ activation : ℝ) :
    directStaticChoiTargetNearActionMass (choiVector W) energy r δ ≤
      staticChoiAdaptiveReplicaBase energy activation ^ r +
        if normalizedSpectralCommutatorEnergy energy W ≤ activation then 1 else 0 := by
  have hnear := directStaticChoiTargetNearActionMass_choiVector_le hd W energy r δ
  have hmass0 := unitaryDiagonalCentralizerMass_nonneg W
  have hmass1 := unitaryDiagonalCentralizerMass_le_one hd hW
  by_cases htube : normalizedSpectralCommutatorEnergy energy W ≤ activation
  · rw [if_pos htube]
    have hnearOne :
        directStaticChoiTargetNearActionMass (choiVector W) energy r δ ≤ 1 :=
      hnear.trans (pow_le_one₀ hmass0 hmass1)
    have hbase0 : 0 ≤ staticChoiAdaptiveReplicaBase energy activation := by
      exact le_max_left _ _
    nlinarith [pow_nonneg hbase0 r]
  · rw [if_neg htube, add_zero]
    have hspeed : 0 < (2 * staticChoiSpeed energy) ^ (2 : ℕ) := by
      exact pow_pos (mul_pos (by norm_num) (staticChoiSpeed_pos energy)) 2
    have hcomm :
        normalizedSpectralCommutatorEnergy energy W ≤
          (2 * staticChoiSpeed energy) ^ (2 : ℕ) *
            (1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ)) := by
      calc
        normalizedSpectralCommutatorEnergy energy W ≤
            (2 * staticChoiSpeed energy) ^ (2 : ℕ) *
              normalizedSpectralOffDiagonalMass W :=
          normalizedSpectralCommutatorEnergy_le_speed_sq_mul_offDiagonal energy W
        _ ≤ (2 * staticChoiSpeed energy) ^ (2 : ℕ) *
              (1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left
            (normalizedSpectralOffDiagonalMass_le_one_sub_centralizerMass_sq hd hW)
            (sq_nonneg _)
    have hstrict :
        unitaryDiagonalCentralizerMass W ^ (2 : ℕ) <
          1 - activation / (2 * staticChoiSpeed energy) ^ (2 : ℕ) := by
      have hactlt : activation < normalizedSpectralCommutatorEnergy energy W :=
        lt_of_not_ge htube
      have hratio :
          activation / (2 * staticChoiSpeed energy) ^ (2 : ℕ) <
            1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ) :=
        (div_lt_iff₀ hspeed).2 (by
          simpa [mul_comm] using hactlt.trans_le hcomm)
      linarith
    have hbaseEq :
        staticChoiAdaptiveReplicaBase energy activation =
          1 - activation / (2 * staticChoiSpeed energy) ^ (2 : ℕ) := by
      rw [staticChoiAdaptiveReplicaBase, max_eq_right]
      exact le_trans (sq_nonneg (unitaryDiagonalCentralizerMass W)) hstrict.le
    have hpow :
        unitaryDiagonalCentralizerMass W ^ (2 * r) ≤
          staticChoiAdaptiveReplicaBase energy activation ^ r := by
      calc
        unitaryDiagonalCentralizerMass W ^ (2 * r) =
            (unitaryDiagonalCentralizerMass W ^ (2 : ℕ)) ^ r := by rw [pow_mul]
        _ ≤ (1 - activation / (2 * staticChoiSpeed energy) ^ (2 : ℕ)) ^ r :=
          pow_le_pow_left₀ (sq_nonneg _) hstrict.le r
        _ = staticChoiAdaptiveReplicaBase energy activation ^ r := by rw [hbaseEq]
    exact hnear.trans hpow

/-- Probability-design form of the exact action--carrier dichotomy.  Circuit
cardinality disappears: transverse loss is averaged against the design and
the only residual is literal design mass in the endpoint-specific action
tubes. -/
theorem weighted_unitaryChoiNearActionMass_le_adaptiveAction_add_carrier
    {d : ℕ} (hd : 0 < d)
    {C : Type*} [Fintype C]
    (W : C → Matrix (Fin d) (Fin d) ℂ)
    (hW : ∀ c, W c ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (energy : Fin d → ℝ) (r : ℕ) (δ : ℝ)
    (activation : C → ℝ)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C) :
    (∑ c, w c * directStaticChoiTargetNearActionMass
        (choiVector (W c)) energy r δ) ≤
      (∑ c, w c * staticChoiAdaptiveReplicaBase energy (activation c) ^ r) +
        ∑ c, if normalizedSpectralCommutatorEnergy energy (W c) ≤ activation c
          then w c else 0 := by
  calc
    (∑ c, w c * directStaticChoiTargetNearActionMass
        (choiVector (W c)) energy r δ) ≤
        ∑ c, w c *
          (staticChoiAdaptiveReplicaBase energy (activation c) ^ r +
            if normalizedSpectralCommutatorEnergy energy (W c) ≤ activation c
              then 1 else 0) := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left
        (directStaticChoiTargetNearActionMass_choiVector_le_adaptiveAction_add_carrier
          hd energy (hW c) r δ (activation c))
        (hw.1 c)
    _ = (∑ c, w c * staticChoiAdaptiveReplicaBase energy (activation c) ^ r) +
        ∑ c, if normalizedSpectralCommutatorEnergy energy (W c) ≤ activation c
          then w c else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : normalizedSpectralCommutatorEnergy energy (W c) ≤ activation c
      · rw [if_pos hc, if_pos hc]
        ring
      · rw [if_neg hc, if_neg hc]
        ring

end

end RHTower

import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenSupportedPieceData
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanCellCoefficients

/-!
# Harman cell coefficients on exact geometric blocks

The natural aligned support lemmas use shifted integer endpoints.  Type-II blocks instead use the
literal geometric scales.  These coefficient-level lemmas recover exact pair and triple product
support directly from tuple membership.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

theorem mtHarmanPairCellCoefficient_realSupport
    {S1 S2 : Finset ℕ} {L1 U1 L2 U2 : ℝ}
    (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hS1 : ∀ q ∈ S1, L1 < (q : ℝ) ∧ (q : ℝ) ≤ U1)
    (hS2 : ∀ q ∈ S2, L2 < (q : ℝ) ∧ (q : ℝ) ≤ U2) :
    ∀ {m : ℕ}, mtHarmanPairCellCoefficient S1 S2 m ≠ 0 →
      0 < m ∧ L1 * L2 < (m : ℝ) ∧ (m : ℝ) ≤ U1 * U2 := by
  intro m hm
  have hcard : (mtHarmanPairCellTuples S1 S2 m).card ≠ 0 := by
    intro hzero
    apply hm
    simp [mtHarmanPairCellCoefficient, hzero]
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcard)
  have htuple := mem_mtHarmanPairCellTuples.mp hq
  have hq1 := hS1 q.1 htuple.1
  have hq2 := hS2 q.2 htuple.2.1
  have hq1Pos : 0 < q.1 := by exact_mod_cast hL1.trans hq1.1
  have hq2Pos : 0 < q.2 := by exact_mod_cast hL2.trans hq2.1
  have hmPos : 0 < m := by rw [← htuple.2.2]; exact Nat.mul_pos hq1Pos hq2Pos
  have hcast : (m : ℝ) = (q.1 : ℝ) * (q.2 : ℝ) := by
    exact_mod_cast htuple.2.2.symm
  rw [hcast]
  constructor
  · exact hmPos
  constructor
  · calc
      L1 * L2 < (q.1 : ℝ) * L2 := mul_lt_mul_of_pos_right hq1.1 hL2
      _ < (q.1 : ℝ) * (q.2 : ℝ) :=
        mul_lt_mul_of_pos_left hq2.1 (by exact_mod_cast hq1Pos)
  · exact mul_le_mul hq1.2 hq2.2 (Nat.cast_nonneg _)
      ((Nat.cast_nonneg _).trans hq1.2)

theorem mtHarmanTripleCellCoefficient_realSupport
    {S1 S2 S3 : Finset ℕ} {L1 U1 L2 U2 L3 U3 : ℝ}
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hL3 : 0 < L3)
    (hS1 : ∀ q ∈ S1, L1 < (q : ℝ) ∧ (q : ℝ) ≤ U1)
    (hS2 : ∀ q ∈ S2, L2 < (q : ℝ) ∧ (q : ℝ) ≤ U2)
    (hS3 : ∀ q ∈ S3, L3 < (q : ℝ) ∧ (q : ℝ) ≤ U3) :
    ∀ {m : ℕ}, mtHarmanTripleCellCoefficient S1 S2 S3 m ≠ 0 →
      0 < m ∧ L1 * L2 * L3 < (m : ℝ) ∧ (m : ℝ) ≤ U1 * U2 * U3 := by
  intro m hm
  have hcard : (mtHarmanTripleCellTuples S1 S2 S3 m).card ≠ 0 := by
    intro hzero
    apply hm
    simp [mtHarmanTripleCellCoefficient, hzero]
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcard)
  have htuple := mem_mtHarmanTripleCellTuples.mp hq
  have hq1 := hS1 q.1.1 htuple.1
  have hq2 := hS2 q.1.2 htuple.2.1
  have hq3 := hS3 q.2 htuple.2.2.1
  have hq1Pos : 0 < q.1.1 := by exact_mod_cast hL1.trans hq1.1
  have hq2Pos : 0 < q.1.2 := by exact_mod_cast hL2.trans hq2.1
  have hq3Pos : 0 < q.2 := by exact_mod_cast hL3.trans hq3.1
  have hmPos : 0 < m := by
    rw [← htuple.2.2.2]
    exact Nat.mul_pos (Nat.mul_pos hq1Pos hq2Pos) hq3Pos
  have hcast : (m : ℝ) = (q.1.1 : ℝ) * (q.1.2 : ℝ) * (q.2 : ℝ) := by
    exact_mod_cast htuple.2.2.2.symm
  rw [hcast]
  constructor
  · exact hmPos
  constructor
  · calc
      L1 * L2 * L3 < ((q.1.1 : ℝ) * (q.1.2 : ℝ)) * L3 := by
        apply mul_lt_mul_of_pos_right _ hL3
        calc
          L1 * L2 < (q.1.1 : ℝ) * L2 := mul_lt_mul_of_pos_right hq1.1 hL2
          _ < (q.1.1 : ℝ) * (q.1.2 : ℝ) :=
            mul_lt_mul_of_pos_left hq2.1 (by exact_mod_cast hq1Pos)
      _ < (q.1.1 : ℝ) * (q.1.2 : ℝ) * (q.2 : ℝ) :=
        mul_lt_mul_of_pos_left hq3.1
          (mul_pos (by exact_mod_cast hq1Pos) (by exact_mod_cast hq2Pos))
  · have h12 : (q.1.1 : ℝ) * (q.1.2 : ℝ) ≤ U1 * U2 :=
      mul_le_mul hq1.2 hq2.2 (Nat.cast_nonneg _)
        ((Nat.cast_nonneg _).trans hq1.2)
    exact mul_le_mul h12 hq3.2 (Nat.cast_nonneg _)
      (mul_nonneg ((Nat.cast_nonneg _).trans hq1.2)
        ((Nat.cast_nonneg _).trans hq2.2))

theorem mtMinimalGeometricBlock_scaleSupported
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i : Fin (mtMinimalGeometricDepth delta start z hdelta)) :
    MTRealScaleSupported
      (mtPrimeBlockAF
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i))
      (mtGeometricLevel delta start i.1)
      (mtGeometricLevel delta start i.1 * (1 + delta)) := by
  apply mtPrimeBlockAF_scaleSupported
  intro q hq
  exact ((mem_ofMinimalGeometricSchedule_block_iff
    z0 D start hdelta hz0 hroot i q).mp hq).2

theorem mtMinimalGeometricPairCell_scaleSupported
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 : Fin (mtMinimalGeometricDepth delta start z hdelta)) :
    MTRealScaleSupported
      (mtCoefficientAF (mtHarmanPairCellCoefficient
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i1)
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i2)))
      (mtGeometricLevel delta start i1.1 * mtGeometricLevel delta start i2.1)
      ((mtGeometricLevel delta start i1.1 * (1 + delta)) *
        (mtGeometricLevel delta start i2.1 * (1 + delta))) := by
  apply mtCoefficientAF_scaleSupported
  apply mtHarmanPairCellCoefficient_realSupport
  · exact mtGeometricLevel_pos hdelta start i1.1
  · exact mtGeometricLevel_pos hdelta start i2.1
  · intro q hq
    exact ((mem_ofMinimalGeometricSchedule_block_iff
      z0 D start hdelta hz0 hroot i1 q).mp hq).2
  · intro q hq
    exact ((mem_ofMinimalGeometricSchedule_block_iff
      z0 D start hdelta hz0 hroot i2 q).mp hq).2

theorem mtMinimalGeometricTripleCell_scaleSupported
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 i3 : Fin (mtMinimalGeometricDepth delta start z hdelta)) :
    MTRealScaleSupported
      (mtCoefficientAF (mtHarmanTripleCellCoefficient
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i1)
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i2)
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i3)))
      (mtGeometricLevel delta start i1.1 * mtGeometricLevel delta start i2.1 *
        mtGeometricLevel delta start i3.1)
      ((mtGeometricLevel delta start i1.1 * (1 + delta)) *
        (mtGeometricLevel delta start i2.1 * (1 + delta)) *
        (mtGeometricLevel delta start i3.1 * (1 + delta))) := by
  apply mtCoefficientAF_scaleSupported
  apply mtHarmanTripleCellCoefficient_realSupport
  · exact mtGeometricLevel_pos hdelta start i1.1
  · exact mtGeometricLevel_pos hdelta start i2.1
  · exact mtGeometricLevel_pos hdelta start i3.1
  · intro q hq
    exact ((mem_ofMinimalGeometricSchedule_block_iff
      z0 D start hdelta hz0 hroot i1 q).mp hq).2
  · intro q hq
    exact ((mem_ofMinimalGeometricSchedule_block_iff
      z0 D start hdelta hz0 hroot i2 q).mp hq).2
  · intro q hq
    exact ((mem_ofMinimalGeometricSchedule_block_iff
      z0 D start hdelta hz0 hroot i3 q).mp hq).2

end

end RHTower.Sieve

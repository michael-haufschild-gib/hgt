import GaloisForLFunctions.RHTower.Sieve.GeneralizedDivisorTupleEnvelope
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBoxFamilyEnvelope
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanRectangularSums

/-!
# Joint envelopes for every good Harman cell

Good cells are disjoint tuple rectangles.  Aggregating their coefficient norms therefore counts
each ordered pair or triple factorization at most once, giving the exact `ζ²` and `ζ³`
coefficient envelopes rather than a cell-cardinality loss.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

noncomputable section

/-- Every active good pair cell, aggregated before taking moments, has the `ζ²` envelope. -/
theorem sum_norm_mtHarmanPairCellFamilyCoefficientAF_le_zeta_sq
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (m : ℕ) :
    ∑ cell ∈ mtHarmanActiveGoodPairCells (t := t) endpoint E,
        ‖mtCoefficientAF (mtHarmanPairCellCoefficient
          (mtHarmanSourceBlock endpoint P cell.1)
          (mtHarmanSourceBlock endpoint P cell.2)) m‖ ≤
      (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (2 : ℕ)) m : ℝ) := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simp [mtCoefficientAF]
  let cells := mtHarmanActiveGoodPairCells (t := t) endpoint E
  let tuples := fun cell : Fin t × Fin t =>
    mtHarmanPairCellSourceTuples endpoint P cell
  let fibres := fun cell => (tuples cell).filter fun q => q.1 * q.2 = m
  let R := (mtHarmanPairRectangularTuples (t := t) endpoint P E).filter
    fun q => q.1 * q.2 = m
  have hpair : (↑cells : Set (Fin t × Fin t)).PairwiseDisjoint fibres := by
    apply (pairwiseDisjoint_mtHarmanPairCellSourceTuples
      (t := t) hmono P E).mono
    intro cell
    exact Finset.filter_subset _ _
  have hUnion : cells.biUnion fibres = R := by
    simpa [cells, fibres, R, tuples, mtHarmanPairRectangularTuples] using
      (Finset.filter_biUnion
        (mtHarmanActiveGoodPairCells (t := t) endpoint E)
        (mtHarmanPairCellSourceTuples (t := t) endpoint P)
        (fun q : ℕ × ℕ => q.1 * q.2 = m)).symm
  let v : (ℕ × ℕ) → Fin 2 → ℕ := fun q => ![q.1, q.2]
  have hRcard : R.card ≤
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (2 : ℕ)) m := by
    apply card_le_zeta_pow_of_injective_factorVectors 1 m hm R v
    · intro q hq r hr hqr
      apply Prod.ext
      · simpa [v] using congrFun hqr (0 : Fin 2)
      · simpa [v] using congrFun hqr (1 : Fin 2)
    · intro q hq i
      have hqRect := (Finset.mem_filter.mp hq).1
      change q ∈ mtHarmanPairRectangularTuples (t := t) endpoint P E at hqRect
      rw [mtHarmanPairRectangularTuples] at hqRect
      obtain ⟨cell, hcell, hqCell⟩ := Finset.mem_biUnion.mp hqRect
      have hqData := Finset.mem_product.mp hqCell
      induction i using Fin.cases with
      | zero =>
          simpa [v] using
            (mem_primesIco.mp (Finset.mem_inter.mp hqData.1).1).2.2.pos
      | succ i =>
          fin_cases i
          simpa [v] using
            (mem_primesIco.mp (Finset.mem_inter.mp hqData.2).1).2.2.pos
    · intro q hq
      have hprod := (Finset.mem_filter.mp hq).2
      simpa [v, Fin.prod_univ_succ] using hprod
  calc
    ∑ cell ∈ mtHarmanActiveGoodPairCells (t := t) endpoint E,
        ‖mtCoefficientAF (mtHarmanPairCellCoefficient
          (mtHarmanSourceBlock endpoint P cell.1)
          (mtHarmanSourceBlock endpoint P cell.2)) m‖ =
        ∑ cell ∈ cells, ((fibres cell).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro cell hcell
      rw [mtCoefficientAF_apply_of_pos _ hm]
      simp [mtHarmanPairCellCoefficient, fibres, tuples,
        mtHarmanPairCellSourceTuples, mtHarmanPairCellTuples]
    _ = ((R.card : ℕ) : ℝ) := by
      rw [← Nat.cast_sum, ← Finset.card_biUnion hpair, hUnion]
    _ ≤ (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (2 : ℕ)) m : ℝ) := by
      exact_mod_cast hRcard

/-- Every active good triple cell, aggregated before taking moments, has the `ζ³` envelope. -/
theorem sum_norm_mtHarmanTripleCellFamilyCoefficientAF_le_zeta_cube
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (m : ℕ) :
    ∑ cell ∈ mtHarmanActiveGoodTripleCells (t := t) endpoint E,
        ‖mtCoefficientAF (mtHarmanTripleCellCoefficient
          (mtHarmanSourceBlock endpoint P cell.1.1)
          (mtHarmanSourceBlock endpoint P cell.1.2)
          (mtHarmanSourceBlock endpoint P cell.2)) m‖ ≤
      (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (3 : ℕ)) m : ℝ) := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simp [mtCoefficientAF]
  let cells := mtHarmanActiveGoodTripleCells (t := t) endpoint E
  let tuples := fun cell : (Fin t × Fin t) × Fin t =>
    mtHarmanTripleCellSourceTuples endpoint P cell
  let fibres := fun cell => (tuples cell).filter fun q => q.1.1 * q.1.2 * q.2 = m
  let R := (mtHarmanTripleRectangularTuples (t := t) endpoint P E).filter
    fun q => q.1.1 * q.1.2 * q.2 = m
  have hpair : (↑cells : Set ((Fin t × Fin t) × Fin t)).PairwiseDisjoint fibres := by
    apply (pairwiseDisjoint_mtHarmanTripleCellSourceTuples
      (t := t) hmono P E).mono
    intro cell
    exact Finset.filter_subset _ _
  have hUnion : cells.biUnion fibres = R := by
    simpa [cells, fibres, R, tuples, mtHarmanTripleRectangularTuples] using
      (Finset.filter_biUnion
        (mtHarmanActiveGoodTripleCells (t := t) endpoint E)
        (mtHarmanTripleCellSourceTuples (t := t) endpoint P)
        (fun q : (ℕ × ℕ) × ℕ => q.1.1 * q.1.2 * q.2 = m)).symm
  let v : ((ℕ × ℕ) × ℕ) → Fin 3 → ℕ := fun q =>
    ![q.1.1, q.1.2, q.2]
  have hRcard : R.card ≤
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (3 : ℕ)) m := by
    apply card_le_zeta_pow_of_injective_factorVectors 2 m hm R v
    · intro q hq r hr hqr
      apply Prod.ext
      · apply Prod.ext
        · simpa [v] using congrFun hqr (0 : Fin 3)
        · simpa [v] using congrFun hqr (1 : Fin 3)
      · simpa [v] using congrFun hqr (2 : Fin 3)
    · intro q hq i
      have hqRect := (Finset.mem_filter.mp hq).1
      change q ∈ mtHarmanTripleRectangularTuples (t := t) endpoint P E at hqRect
      rw [mtHarmanTripleRectangularTuples] at hqRect
      obtain ⟨cell, hcell, hqCell⟩ := Finset.mem_biUnion.mp hqRect
      have hqData := Finset.mem_product.mp hqCell
      have hqPair := Finset.mem_product.mp hqData.1
      fin_cases i
      · exact (mem_primesIco.mp (Finset.mem_inter.mp hqPair.1).1).2.2.pos
      · exact (mem_primesIco.mp (Finset.mem_inter.mp hqPair.2).1).2.2.pos
      · exact (mem_primesIco.mp (Finset.mem_inter.mp hqData.2).1).2.2.pos
    · intro q hq
      have hprod := (Finset.mem_filter.mp hq).2
      simpa [v, Fin.prod_univ_succ, Nat.mul_assoc] using hprod
  calc
    ∑ cell ∈ mtHarmanActiveGoodTripleCells (t := t) endpoint E,
        ‖mtCoefficientAF (mtHarmanTripleCellCoefficient
          (mtHarmanSourceBlock endpoint P cell.1.1)
          (mtHarmanSourceBlock endpoint P cell.1.2)
          (mtHarmanSourceBlock endpoint P cell.2)) m‖ =
        ∑ cell ∈ cells, ((fibres cell).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro cell hcell
      rw [mtCoefficientAF_apply_of_pos _ hm]
      simp [mtHarmanTripleCellCoefficient, fibres, tuples,
        mtHarmanTripleCellSourceTuples, mtHarmanTripleCellTuples]
    _ = ((R.card : ℕ) : ℝ) := by
      rw [← Nat.cast_sum, ← Finset.card_biUnion hpair, hUnion]
    _ ≤ (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (3 : ℕ)) m : ℝ) := by
      exact_mod_cast hRcard

end

end RHTower.Sieve

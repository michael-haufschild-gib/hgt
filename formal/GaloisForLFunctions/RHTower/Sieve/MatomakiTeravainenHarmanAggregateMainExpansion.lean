import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanAggregateError
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMainBoxExpansion
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenFullBoxEnvelope

/-!
# Exact box expansion of aggregate Harman mains

Linearity is used only after the repaired iteration.  Thus accumulated errors stay aggregated,
while each main becomes the literal finite family of base, one-prime, pair, and triple boxes.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

def mtFiniteMainBoxFamilyAF {t : ℕ} (data : MTFiniteIterationSourceData t)
    (alpha : ℕ → ℂ) (depth : ℕ) (j : Fin (t + 1))
    (delta : ℝ) (N : ℕ) : ArithmeticFunction ℂ :=
  ∑ layer ∈ Finset.range (depth + 1),
    ∑ chain ∈ mtActiveBlockChains data.block layer j,
      ∑ eIndex ∈ Finset.range (mtUpperAdicIndex delta data.D + 1),
        ∑ kIndex ∈ Finset.range (mtUpperAdicIndex delta N + 1),
          mtSignedBlockChainAdicBoxAF alpha data.block chain
            data.z₀ data.D delta eIndex kIndex

theorem coefficient_mul_finiteIterationMain_apply_eq_boxFamilyAF
    {t : ℕ} {delta : ℝ} (hdelta : 0 < delta)
    (data : MTFiniteIterationSourceData t) (alpha : ℕ → ℂ)
    (depth : ℕ) (j : Fin (t + 1)) {n N : ℕ}
    (hn : 0 < n) (hnN : n ≤ N) :
    (mtCoefficientAF alpha *
        mtFiniteIterationMain data.truncation data.block data.cutoff depth j) n =
      mtFiniteMainBoxFamilyAF data alpha depth j delta N n := by
  rw [coefficient_mul_finiteIterationMain_apply_eq_sum_adicBoxes
    hdelta data alpha depth j hn hnN]
  simp only [mtFiniteMainBoxFamilyAF, arithmeticFunction_finset_sum_apply]

/-- Reindex nested depth/chain sums by the disjoint tagged active-chain family. -/
theorem mtFiniteMainBoxFamilyAF_eq_sum_allActiveBlockChains
    {t : ℕ} (data : MTFiniteIterationSourceData t) (alpha : ℕ → ℂ)
    (depth : ℕ) (j : Fin (t + 1)) (delta : ℝ) (N : ℕ) :
    mtFiniteMainBoxFamilyAF data alpha depth j delta N =
      ∑ dc ∈ mtAllActiveBlockChains data depth j,
        ∑ eIndex ∈ Finset.range (mtUpperAdicIndex delta data.D + 1),
          ∑ kIndex ∈ Finset.range (mtUpperAdicIndex delta N + 1),
            mtSignedBlockChainAdicBoxAF alpha data.block dc.2
              data.z₀ data.D delta eIndex kIndex := by
  classical
  have hpair :
      (↑(Finset.range (depth + 1)) : Set ℕ).PairwiseDisjoint fun layer =>
        (mtActiveBlockChains data.block layer j).image fun chain => (layer, chain) := by
    intro a ha b hb hab
    change Disjoint
      ((mtActiveBlockChains data.block a j).image fun chain => (a, chain))
      ((mtActiveBlockChains data.block b j).image fun chain => (b, chain))
    rw [Finset.disjoint_left]
    intro dc hda hdb
    obtain ⟨chainA, hchainA, rfl⟩ := Finset.mem_image.mp hda
    obtain ⟨chainB, hchainB, heq⟩ := Finset.mem_image.mp hdb
    exact hab (Prod.mk.inj heq.symm).1
  unfold mtFiniteMainBoxFamilyAF mtAllActiveBlockChains
  rw [Finset.sum_biUnion hpair]
  apply Finset.sum_congr rfl
  intro layer hlayer
  rw [Finset.sum_image]
  intro chainA hchainA chainB hchainB heq
  exact (Prod.mk.inj heq).2

theorem mtCoefficientAF_finset_sum_eq
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (alpha : ι → ℕ → ℂ) :
    mtCoefficientAF (fun n => ∑ i ∈ S, alpha i n) =
      ∑ i ∈ S, mtCoefficientAF (alpha i) := by
  ext n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [mtCoefficientAF]
  · rw [mtCoefficientAF_apply_of_pos _ hn,
      arithmeticFunction_finset_sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mtCoefficientAF_apply_of_pos _ hn]

theorem finsetCoefficient_mul_finiteIterationMain_apply_eq_sum_boxFamilyAF
    {ι : Type*} [DecidableEq ι] {t : ℕ} {delta : ℝ}
    (hdelta : 0 < delta) (S : Finset ι) (alpha : ι → ℕ → ℂ)
    (data : MTFiniteIterationSourceData t) (depth : ℕ) (j : Fin (t + 1))
    {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (mtCoefficientAF (fun m => ∑ i ∈ S, alpha i m) *
        mtFiniteIterationMain data.truncation data.block data.cutoff depth j) n =
      ∑ i ∈ S, mtFiniteMainBoxFamilyAF data (alpha i) depth j delta N n := by
  rw [mtCoefficientAF_finset_sum_eq S alpha, Finset.sum_mul,
    arithmeticFunction_finset_sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact coefficient_mul_finiteIterationMain_apply_eq_boxFamilyAF
    hdelta data (alpha i) depth j hn hnN

def mtHarmanBaseBoxFamilyAF {t : ℕ} (data : MTFiniteIterationSourceData t)
    (depth : ℕ) (j : Fin (t + 1)) (delta : ℝ) (N : ℕ) :
    ArithmeticFunction ℂ :=
  mtFiniteMainBoxFamilyAF data mtUnitCoefficient depth j delta N

def mtHarmanOnePrimeBoxFamilyAF {outerDepth recDepth : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (data : MTFiniteIterationSourceData recDepth) (depth : ℕ)
    (j : Fin (recDepth + 1)) (delta : ℝ) (N : ℕ) : ArithmeticFunction ℂ :=
  ∑ i : Fin outerDepth,
    mtFiniteMainBoxFamilyAF data
      (mtFinsetIndicatorCoefficient (mtHarmanSourceBlock endpoint P i))
      depth j delta N

def mtHarmanPairBoxFamilyAF {outerDepth recDepth : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData recDepth) (depth : ℕ)
    (j : Fin (recDepth + 1)) (delta : ℝ) (N : ℕ) : ArithmeticFunction ℂ :=
  ∑ cell ∈ mtHarmanActiveGoodPairCells (t := outerDepth) endpoint E,
    mtFiniteMainBoxFamilyAF data
      (mtHarmanPairCellCoefficient
        (mtHarmanSourceBlock endpoint P cell.1)
        (mtHarmanSourceBlock endpoint P cell.2)) depth j delta N

def mtHarmanTripleBoxFamilyAF {outerDepth recDepth : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData recDepth) (depth : ℕ)
    (j : Fin (recDepth + 1)) (delta : ℝ) (N : ℕ) : ArithmeticFunction ℂ :=
  ∑ cell ∈ mtHarmanActiveGoodTripleCells (t := outerDepth) endpoint E,
    mtFiniteMainBoxFamilyAF data
      (mtHarmanTripleCellCoefficient
        (mtHarmanSourceBlock endpoint P cell.1.1)
        (mtHarmanSourceBlock endpoint P cell.1.2)
        (mtHarmanSourceBlock endpoint P cell.2)) depth j delta N

theorem mtCoefficientAF_baseOne_eq_sub (P : Finset ℕ) :
    mtCoefficientAF (mtHarmanBaseOneCoefficient P) =
      mtCoefficientAF mtUnitCoefficient -
        mtCoefficientAF (mtFinsetIndicatorCoefficient P) := by
  ext n
  by_cases hn : n = 0 <;>
    simp [sub_eq_add_neg, ArithmeticFunction.add_apply, mtCoefficientAF,
      mtHarmanBaseOneCoefficient, hn]

/-- Exact post-iteration expansion into all literal Harman box families. -/
theorem mtHarmanAggregateIterationMainAF_apply_eq_boxFamilies
    {outerQ outerD recDepth : ℕ}
    (endpointQ endpointD : ℕ → ℕ)
    (z Q D : ℕ) (E : ℝ)
    (hmonoQ : Monotone endpointQ)
    (hsourceQ : primesIco z Q ⊆ primesIco (endpointQ 0) (endpointQ outerQ))
    (data : MTFiniteIterationSourceData recDepth) (depth : ℕ)
    (j : Fin (recDepth + 1)) {delta : ℝ} (hdelta : 0 < delta)
    {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    mtHarmanAggregateIterationMainAF (outerDepth := outerD)
        endpointD z Q D E data depth j n =
      (mtHarmanBaseBoxFamilyAF data depth j delta N -
        mtHarmanOnePrimeBoxFamilyAF (outerDepth := outerQ)
          endpointQ (primesIco z Q) data depth j delta N +
        mtHarmanPairBoxFamilyAF (outerDepth := outerD)
          endpointD (primesIco z D) E data depth j delta N -
        mtHarmanTripleBoxFamilyAF (outerDepth := outerD)
          endpointD (primesIco z D) E data depth j delta N) n := by
  let main := mtFiniteIterationMain
    data.truncation data.block data.cutoff depth j
  have hbase : (mtCoefficientAF mtUnitCoefficient * main) n =
      mtHarmanBaseBoxFamilyAF data depth j delta N n := by
    exact coefficient_mul_finiteIterationMain_apply_eq_boxFamilyAF
      hdelta data mtUnitCoefficient depth j hn hnN
  have honePartition : mtFinsetIndicatorCoefficient (primesIco z Q) =
      fun m => ∑ i ∈ (Finset.univ : Finset (Fin outerQ)),
        mtFinsetIndicatorCoefficient
          (mtHarmanSourceBlock endpointQ (primesIco z Q) i) m := by
    funext m
    exact mtFinsetIndicatorCoefficient_eq_sum_sourceBlocks
      hmonoQ hsourceQ m
  have hone :
      (mtCoefficientAF (mtFinsetIndicatorCoefficient (primesIco z Q)) * main) n =
        mtHarmanOnePrimeBoxFamilyAF (outerDepth := outerQ)
          endpointQ (primesIco z Q) data depth j delta N n := by
    rw [honePartition]
    simpa only [mtHarmanOnePrimeBoxFamilyAF,
      arithmeticFunction_finset_sum_apply] using
      finsetCoefficient_mul_finiteIterationMain_apply_eq_sum_boxFamilyAF
        hdelta (Finset.univ : Finset (Fin outerQ))
        (fun i => mtFinsetIndicatorCoefficient
          (mtHarmanSourceBlock endpointQ (primesIco z Q) i))
        data depth j hn hnN
  have hbaseOne :
      (mtCoefficientAF (mtHarmanBaseOneCoefficient (primesIco z Q)) * main) n =
        (mtHarmanBaseBoxFamilyAF data depth j delta N -
          mtHarmanOnePrimeBoxFamilyAF (outerDepth := outerQ)
            endpointQ (primesIco z Q) data depth j delta N) n := by
    rw [mtCoefficientAF_baseOne_eq_sub, sub_mul]
    change (mtCoefficientAF mtUnitCoefficient * main) n -
        (mtCoefficientAF (mtFinsetIndicatorCoefficient (primesIco z Q)) * main) n = _
    rw [hbase, hone]
    rfl
  have hpair :
      (mtCoefficientAF
          (mtHarmanPairFamilyCoefficient (t := outerD)
            endpointD (primesIco z D) E) * main) n =
        mtHarmanPairBoxFamilyAF (outerDepth := outerD)
          endpointD (primesIco z D) E data depth j delta N n := by
    unfold mtHarmanPairFamilyCoefficient
    simpa only [mtHarmanPairBoxFamilyAF,
      arithmeticFunction_finset_sum_apply] using
      finsetCoefficient_mul_finiteIterationMain_apply_eq_sum_boxFamilyAF
        hdelta (mtHarmanActiveGoodPairCells (t := outerD) endpointD E)
        (fun cell => mtHarmanPairCellCoefficient
          (mtHarmanSourceBlock endpointD (primesIco z D) cell.1)
          (mtHarmanSourceBlock endpointD (primesIco z D) cell.2))
        data depth j hn hnN
  have htriple :
      (mtCoefficientAF
          (mtHarmanTripleFamilyCoefficient (t := outerD)
            endpointD (primesIco z D) E) * main) n =
        mtHarmanTripleBoxFamilyAF (outerDepth := outerD)
          endpointD (primesIco z D) E data depth j delta N n := by
    unfold mtHarmanTripleFamilyCoefficient
    simpa only [mtHarmanTripleBoxFamilyAF,
      arithmeticFunction_finset_sum_apply] using
      finsetCoefficient_mul_finiteIterationMain_apply_eq_sum_boxFamilyAF
        hdelta (mtHarmanActiveGoodTripleCells (t := outerD) endpointD E)
        (fun cell => mtHarmanTripleCellCoefficient
          (mtHarmanSourceBlock endpointD (primesIco z D) cell.1.1)
          (mtHarmanSourceBlock endpointD (primesIco z D) cell.1.2)
          (mtHarmanSourceBlock endpointD (primesIco z D) cell.2))
        data depth j hn hnN
  unfold mtHarmanAggregateIterationMainAF
  change
    (mtCoefficientAF (mtHarmanBaseOneCoefficient (primesIco z Q)) * main) n +
        (mtCoefficientAF
          (mtHarmanPairFamilyCoefficient (t := outerD)
            endpointD (primesIco z D) E) * main) n -
      (mtCoefficientAF
        (mtHarmanTripleFamilyCoefficient (t := outerD)
          endpointD (primesIco z D) E) * main) n = _
  rw [hbaseOne, hpair, htriple]
  rfl

end

end RHTower.Sieve

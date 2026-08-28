import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRetainedBoxFamily
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAlignedScheduleCount

/-!
# Compressed retained-box family

The paper-aligned outer schedule is deliberately padded by `Q - z₀` formal indices.  Only its
nonempty adjacent prime blocks can contribute.  This file removes the padded zero boxes from the
tagged retained family without changing its exact arithmetic-function sum.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

local instance instDecidableEqMTHarmanCompressedRetainedBoxIndex
    (outerQ outerD recDepth : ℕ) :
    DecidableEq (MTHarmanRetainedBoxIndex outerQ outerD recDepth) := Classical.decEq _

local instance instDecidableEqMTTripleSeparatedBoxIndexCompressedFamily
    (outerD recDepth : ℕ) :
    DecidableEq (MTTripleSeparatedBoxIndex outerD recDepth) := Classical.decEq _

/-- Retained family with the one-prime outer coordinate restricted to genuine aligned blocks. -/
def mtHarmanCompressedRetainedBoxIndexSet {outerQ outerD recDepth : ℕ}
    (outerActive : Finset (Fin outerQ))
    (endpointQ endpointD : ℕ → ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData recDepth) (maxDepth : ℕ)
    (j : Fin (recDepth + 1)) (delta : ℝ) (N recStart : ℕ) (Y : ℝ) :
    Finset (MTHarmanRetainedBoxIndex outerQ outerD recDepth) :=
  (mtProductScaleIndices
      (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin 1))
        data maxDepth j (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
      (mtOuterSeparatedBoxScale (mtBaseOuterScale delta) delta recStart) Y).disjSum
  ((mtProductScaleIndices
      (mtOuterSeparatedBoxIndexSet outerActive
        data maxDepth j (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
      (mtOuterSeparatedBoxScale (mtOnePrimeOuterScale endpointQ) delta recStart) Y).disjSum
  ((mtProductScaleIndices
      (mtSeparatedPairBoxIndexSet (u := outerD) endpointD E data maxDepth j
        (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
      (mtSeparatedPairBoxScale endpointD delta recStart) Y).disjSum
    (mtProductScaleIndices
      (mtSeparatedTripleBoxIndexSet (u := outerD) endpointD E data maxDepth j
        (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
      (mtSeparatedTripleBoxScale endpointD delta recStart) Y)))

/-- Compression only deletes tagged indices. -/
theorem mtHarmanCompressedRetainedBoxIndexSet_subset
    {outerQ outerD recDepth : ℕ} (outerActive : Finset (Fin outerQ))
    (endpointQ endpointD : ℕ → ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData recDepth) (maxDepth : ℕ)
    (j : Fin (recDepth + 1)) (delta : ℝ) (N recStart : ℕ) (Y : ℝ) :
    mtHarmanCompressedRetainedBoxIndexSet (outerD := outerD)
        outerActive endpointQ endpointD E
        data maxDepth j delta N recStart Y ⊆
      mtHarmanRetainedBoxIndexSet (outerD := outerD) endpointQ endpointD E
        data maxDepth j delta N recStart Y := by
  intro idx hidx
  cases idx with
  | inl idx =>
      simpa [mtHarmanCompressedRetainedBoxIndexSet,
        mtHarmanRetainedBoxIndexSet] using hidx
  | inr rest =>
      cases rest with
      | inl idx =>
          simp [mtHarmanCompressedRetainedBoxIndexSet,
            mtHarmanRetainedBoxIndexSet, mtProductScaleIndices,
            mtOuterSeparatedBoxIndexSet] at hidx ⊢
          exact ⟨⟨⟨hidx.1.1.1.2, hidx.1.1.2⟩, hidx.1.2⟩, hidx.2⟩
      | inr tail =>
          cases tail with
          | inl idx =>
              simpa [mtHarmanCompressedRetainedBoxIndexSet,
                mtHarmanRetainedBoxIndexSet] using hidx
          | inr idx =>
              simpa [mtHarmanCompressedRetainedBoxIndexSet,
                mtHarmanRetainedBoxIndexSet] using hidx

/-- A zero outer coefficient produces the zero separated box. -/
theorem mtOuterSeparatedBoxAF_eq_zero_of_outerCoefficient_eq_zero
    {ι : Type*} {t : ℕ} (alpha : ι → ℕ → ℂ)
    (data : MTFiniteIterationSourceData t) (z₀ D : ℕ) (delta : ℝ)
    (idx : MTOuterSeparatedBoxIndex ι t)
    (halpha : alpha idx.1.1.1 = 0) :
    mtOuterSeparatedBoxAF alpha data z₀ D delta idx = 0 := by
  unfold mtOuterSeparatedBoxAF
  rw [halpha]
  ext n
  simp [mtSignedBlockChainAdicBoxAF, mtBlockChainAdicBoxAF, mtCoefficientAF,
    ArithmeticFunction.mul_apply]

/-- An inactive aligned block has identically zero one-prime outer coefficient. -/
theorem mtOnePrimeOuterAlpha_eq_zero_of_not_mem_active
    {t z₀ z₁ : ℕ} {delta : ℝ} (P : Finset ℕ) (i : Fin t)
    (hi : i ∉ mtPaperAlignedActiveBlockIndices t z₀ z₁ delta) :
    mtOnePrimeOuterAlpha (mtPaperAlignedEndpoint z₀ z₁ delta) P i = 0 := by
  have hnot : ¬(mtAdjacentPrimeBlock
      (mtPaperAlignedEndpoint z₀ z₁ delta) i).Nonempty := by
    simpa [mtPaperAlignedActiveBlockIndices] using hi
  have hempty : mtAdjacentPrimeBlock
      (mtPaperAlignedEndpoint z₀ z₁ delta) i = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnot
  funext n
  simp [mtOnePrimeOuterAlpha, mtHarmanSourceBlock,
    mtFinsetIndicatorCoefficient, hempty]

/-- Removing padded empty one-prime boxes preserves the exact retained main. -/
theorem sum_mtHarmanCompressedRetainedBoxAF_eq_main
    {outerQ outerD recDepth outerStart Qouter : ℕ}
    (endpointD : ℕ → ℕ) (z Q D : ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData recDepth) (maxDepth : ℕ)
    (j : Fin (recDepth + 1)) (delta : ℝ) (N recStart : ℕ) (Y : ℝ) :
    ∑ idx ∈ mtHarmanCompressedRetainedBoxIndexSet (outerD := outerD)
        (mtPaperAlignedActiveBlockIndices outerQ outerStart Qouter delta)
        (mtPaperAlignedEndpoint outerStart Qouter delta) endpointD E
        data maxDepth j delta N recStart Y,
      mtHarmanRetainedBoxAF
        (mtPaperAlignedEndpoint outerStart Qouter delta) endpointD z Q D data delta idx =
    mtHarmanRetainedBoxMainAF (outerQ := outerQ) (outerD := outerD)
      (mtPaperAlignedEndpoint outerStart Qouter delta) endpointD z Q D E
      data maxDepth j delta N recStart Y := by
  let endpointQ := mtPaperAlignedEndpoint outerStart Qouter delta
  let active := mtPaperAlignedActiveBlockIndices outerQ outerStart Qouter delta
  let compressed := mtHarmanCompressedRetainedBoxIndexSet (outerD := outerD)
    active endpointQ endpointD E
    data maxDepth j delta N recStart Y
  let full := mtHarmanRetainedBoxIndexSet (outerQ := outerQ) (outerD := outerD)
    endpointQ endpointD E
    data maxDepth j delta N recStart Y
  have hsubset : compressed ⊆ full := by
    exact mtHarmanCompressedRetainedBoxIndexSet_subset (outerD := outerD)
      active endpointQ endpointD E
      data maxDepth j delta N recStart Y
  calc
    ∑ idx ∈ compressed,
        mtHarmanRetainedBoxAF endpointQ endpointD z Q D data delta idx =
        ∑ idx ∈ full,
          mtHarmanRetainedBoxAF endpointQ endpointD z Q D data delta idx := by
      apply Finset.sum_subset hsubset
      intro idx hidxFull hidxCompressed
      cases idx with
      | inl idx =>
          exfalso
          exact hidxCompressed (by
            simpa [compressed, full, mtHarmanCompressedRetainedBoxIndexSet,
              mtHarmanRetainedBoxIndexSet] using hidxFull)
      | inr rest =>
          cases rest with
          | inl idx =>
              have hidxFull' : idx ∈ mtProductScaleIndices
                  (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin outerQ))
                    data maxDepth j (mtUpperAdicIndex delta data.D)
                      (mtUpperAdicIndex delta N))
                  (mtOuterSeparatedBoxScale (mtOnePrimeOuterScale endpointQ)
                    delta recStart) Y := by
                simpa [full, mtHarmanRetainedBoxIndexSet] using hidxFull
              have hi : idx.1.1.1 ∉ active := by
                intro hiActive
                apply hidxCompressed
                have hindexFull := (Finset.mem_filter.mp hidxFull').1
                have hindexActive : idx ∈ mtOuterSeparatedBoxIndexSet active
                    data maxDepth j (mtUpperAdicIndex delta data.D)
                      (mtUpperAdicIndex delta N) := by
                  rw [mtOuterSeparatedBoxIndexSet] at hindexFull ⊢
                  have hk := Finset.mem_product.mp hindexFull
                  have he := Finset.mem_product.mp hk.1
                  have hic := Finset.mem_product.mp he.1
                  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
                    ⟨Finset.mem_product.mpr ⟨hiActive, hic.2⟩, he.2⟩, hk.2⟩
                have hcompressedOne : idx ∈ mtProductScaleIndices
                    (mtOuterSeparatedBoxIndexSet active data maxDepth j
                      (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
                    (mtOuterSeparatedBoxScale (mtOnePrimeOuterScale endpointQ)
                      delta recStart) Y :=
                  Finset.mem_filter.mpr
                    ⟨hindexActive, (Finset.mem_filter.mp hidxFull').2⟩
                simpa [compressed, mtHarmanCompressedRetainedBoxIndexSet] using hcompressedOne
              have halpha : mtOnePrimeOuterAlpha endpointQ (primesIco z Q)
                  idx.1.1.1 = 0 := by
                apply mtOnePrimeOuterAlpha_eq_zero_of_not_mem_active
                simpa [active] using hi
              simp only [mtHarmanRetainedBoxAF]
              rw [mtOuterSeparatedBoxAF_eq_zero_of_outerCoefficient_eq_zero
                (mtOnePrimeOuterAlpha endpointQ (primesIco z Q)) data
                data.z₀ data.D delta idx halpha]
              simp
          | inr tail =>
              cases tail with
              | inl idx =>
                  exfalso
                  exact hidxCompressed (by
                    simpa [compressed, full, mtHarmanCompressedRetainedBoxIndexSet,
                      mtHarmanRetainedBoxIndexSet] using hidxFull)
              | inr idx =>
                  exfalso
                  exact hidxCompressed (by
                    simpa [compressed, full, mtHarmanCompressedRetainedBoxIndexSet,
                      mtHarmanRetainedBoxIndexSet] using hidxFull)
    _ = mtHarmanRetainedBoxMainAF (outerQ := outerQ) (outerD := outerD)
        endpointQ endpointD z Q D E data maxDepth j delta N recStart Y :=
      sum_mtHarmanRetainedBoxAF_eq_main endpointQ endpointD z Q D E
        data maxDepth j delta N recStart Y
    _ = _ := by simp only [endpointQ]

/-- Exact cardinality of the compressed disjoint tagged family. -/
theorem card_mtHarmanCompressedRetainedBoxIndexSet
    {outerQ outerD recDepth : ℕ} (outerActive : Finset (Fin outerQ))
    (endpointQ endpointD : ℕ → ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData recDepth) (maxDepth : ℕ)
    (j : Fin (recDepth + 1)) (delta : ℝ) (N recStart : ℕ) (Y : ℝ) :
    (mtHarmanCompressedRetainedBoxIndexSet (outerD := outerD)
      outerActive endpointQ endpointD E
      data maxDepth j delta N recStart Y).card =
      (mtProductScaleIndices
        (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin 1))
          data maxDepth j (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
        (mtOuterSeparatedBoxScale (mtBaseOuterScale delta) delta recStart) Y).card +
      (mtProductScaleIndices
        (mtOuterSeparatedBoxIndexSet outerActive
          data maxDepth j (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
        (mtOuterSeparatedBoxScale (mtOnePrimeOuterScale endpointQ) delta recStart) Y).card +
      (mtProductScaleIndices
        (mtSeparatedPairBoxIndexSet (u := outerD) endpointD E data maxDepth j
          (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
        (mtSeparatedPairBoxScale endpointD delta recStart) Y).card +
      (mtProductScaleIndices
        (mtSeparatedTripleBoxIndexSet (u := outerD) endpointD E data maxDepth j
          (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
        (mtSeparatedTripleBoxScale endpointD delta recStart) Y).card := by
  simp [mtHarmanCompressedRetainedBoxIndexSet, Finset.card_disjSum, add_assoc]

/-- Product-scale filtering leaves the compressed family below its explicit Cartesian count. -/
theorem card_mtHarmanCompressedRetainedBoxIndexSet_le
    {outerQ outerD recDepth : ℕ} (outerActive : Finset (Fin outerQ))
    (endpointQ endpointD : ℕ → ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData recDepth) (maxDepth : ℕ)
    (j : Fin (recDepth + 1)) (delta : ℝ) (N recStart : ℕ) (Y : ℝ) :
    (mtHarmanCompressedRetainedBoxIndexSet (outerD := outerD)
      outerActive endpointQ endpointD E
      data maxDepth j delta N recStart Y).card ≤
      (1 + outerActive.card +
          (mtHarmanActiveGoodPairCells (t := outerD) endpointD E).card +
          (mtHarmanActiveGoodTripleCells (t := outerD) endpointD E).card) *
        (mtAllActiveBlockChains data maxDepth j).card *
        (mtUpperAdicIndex delta data.D + 1) *
        (mtUpperAdicIndex delta N + 1) := by
  rw [card_mtHarmanCompressedRetainedBoxIndexSet]
  have hbase :
      (mtProductScaleIndices
        (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin 1))
          data maxDepth j (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
        (mtOuterSeparatedBoxScale (mtBaseOuterScale delta) delta recStart) Y).card ≤
      (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin 1))
        data maxDepth j (mtUpperAdicIndex delta data.D)
          (mtUpperAdicIndex delta N)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hone :
      (mtProductScaleIndices
        (mtOuterSeparatedBoxIndexSet outerActive data maxDepth j
          (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
        (mtOuterSeparatedBoxScale (mtOnePrimeOuterScale endpointQ) delta recStart) Y).card ≤
      (mtOuterSeparatedBoxIndexSet outerActive data maxDepth j
        (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hpair :
      (mtProductScaleIndices
        (mtSeparatedPairBoxIndexSet (u := outerD) endpointD E data maxDepth j
          (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
        (mtSeparatedPairBoxScale endpointD delta recStart) Y).card ≤
      (mtSeparatedPairBoxIndexSet (u := outerD) endpointD E data maxDepth j
        (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have htriple :
      (mtProductScaleIndices
        (mtSeparatedTripleBoxIndexSet (u := outerD) endpointD E data maxDepth j
          (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
        (mtSeparatedTripleBoxScale endpointD delta recStart) Y).card ≤
      (mtSeparatedTripleBoxIndexSet (u := outerD) endpointD E data maxDepth j
        (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  calc
    _ ≤
        (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin 1))
          data maxDepth j (mtUpperAdicIndex delta data.D)
            (mtUpperAdicIndex delta N)).card +
        (mtOuterSeparatedBoxIndexSet outerActive data maxDepth j
          (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N)).card +
        (mtSeparatedPairBoxIndexSet (u := outerD) endpointD E data maxDepth j
          (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N)).card +
        (mtSeparatedTripleBoxIndexSet (u := outerD) endpointD E data maxDepth j
          (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N)).card := by
      omega
    _ = _ := by
      simp [mtOuterSeparatedBoxIndexSet, mtSeparatedPairBoxIndexSet,
        mtSeparatedTripleBoxIndexSet, Finset.card_product]
      ring

end

end RHTower.Sieve

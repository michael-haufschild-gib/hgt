import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenActiveChainEnvelope
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBoxFamilyEnvelope
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanCellFamilyEnvelope

/-!
# Joint generalized-divisor envelopes for complete box families

Outer Harman cells, every recursive chain and depth, the truncated-Möbius adic partition, and the
terminal-cofactor adic partition are aggregated before taking moments.  Pair boxes cost `ζ⁵` and
triple boxes cost `ζ⁶`, with no family-cardinality factor.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

noncomputable section

abbrev MTPairSeparatedBoxIndex (u t : ℕ) :=
  (((Fin u × Fin u) × (ℕ × List (Fin t))) × ℕ) × ℕ

abbrev MTTripleSeparatedBoxIndex (u t : ℕ) :=
  ((((Fin u × Fin u) × Fin u) × (ℕ × List (Fin t))) × ℕ) × ℕ

/-- All active recursive chains through a bounded depth, tagged by their depth. -/
def mtAllActiveBlockChains {t : ℕ} (data : MTFiniteIterationSourceData t)
    (maxDepth : ℕ) (j : Fin (t + 1)) : Finset (ℕ × List (Fin t)) :=
  (Finset.range (maxDepth + 1)).biUnion fun depth =>
    (mtActiveBlockChains data.block depth j).image fun chain => (depth, chain)

theorem mem_mtAllActiveBlockChains {t : ℕ} {data : MTFiniteIterationSourceData t}
    {maxDepth : ℕ} {j : Fin (t + 1)} {dc : ℕ × List (Fin t)} :
    dc ∈ mtAllActiveBlockChains data maxDepth j ↔
      dc.1 ∈ Finset.range (maxDepth + 1) ∧
        dc.2 ∈ mtActiveBlockChains data.block dc.1 j := by
  rw [mtAllActiveBlockChains]
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨depth, hdepth, chain, hchain, heq⟩
    subst dc
    exact ⟨hdepth, hchain⟩
  · rintro ⟨hdepth, hchain⟩
    exact ⟨dc.1, hdepth, dc.2, hchain, rfl⟩

theorem sum_norm_mtPrimeBlockFamilyAF_allActiveChainTags_le_one
    {t : ℕ} (data : MTFiniteIterationSourceData t)
    (maxDepth : ℕ) (j : Fin (t + 1)) (n : ℕ) :
    ∑ dc ∈ mtAllActiveBlockChains data maxDepth j,
        ‖mtPrimeBlockFamilyAF data.block dc.2.toFinset n‖ ≤ 1 := by
  have hpair :
      (↑(Finset.range (maxDepth + 1)) : Set ℕ).PairwiseDisjoint fun depth =>
        (mtActiveBlockChains data.block depth j).image fun chain => (depth, chain) := by
    intro a ha b hb hab
    change Disjoint
      ((mtActiveBlockChains data.block a j).image fun chain => (a, chain))
      ((mtActiveBlockChains data.block b j).image fun chain => (b, chain))
    rw [Finset.disjoint_left]
    intro dc hda hdb
    obtain ⟨chainA, hchainA, rfl⟩ := Finset.mem_image.mp hda
    obtain ⟨chainB, hchainB, heq⟩ := Finset.mem_image.mp hdb
    exact hab (Prod.mk.inj heq.symm).1
  rw [mtAllActiveBlockChains, Finset.sum_biUnion hpair]
  calc
    ∑ depth ∈ Finset.range (maxDepth + 1),
        ∑ dc ∈ (mtActiveBlockChains data.block depth j).image
          (fun chain => (depth, chain)),
          ‖mtPrimeBlockFamilyAF data.block dc.2.toFinset n‖ =
        ∑ depth ∈ Finset.range (maxDepth + 1),
          ∑ chain ∈ mtActiveBlockChains data.block depth j,
            ‖mtPrimeBlockFamilyAF data.block chain.toFinset n‖ := by
      apply Finset.sum_congr rfl
      intro depth hdepth
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact (Prod.mk.inj hab).2
    _ ≤ 1 := sum_norm_mtPrimeBlockFamilyAF_allActiveChains_le_one
      data maxDepth j n

/-- Generic composition of an outer `ζ^r` family with all chains and both adic partitions. -/
theorem sum_norm_outer_active_adic_boxFamily_le_zeta_pow
    {ι : Type*} [DecidableEq ι] {t : ℕ}
    (S : Finset ι) (outer : ι → ArithmeticFunction ℂ)
    (data : MTFiniteIterationSourceData t) (maxDepth : ℕ) (j : Fin (t + 1))
    {δ : ℝ} (hδ : 0 < δ) (z D eMax kMax r : ℕ)
    (houter : ∀ n, ∑ i ∈ S, ‖outer i n‖ ≤
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ r) n : ℕ) : ℝ))
    (n : ℕ) :
    ∑ idx ∈ (((S.product (mtAllActiveBlockChains data maxDepth j)).product
        (Finset.range (eMax + 1))).product (Finset.range (kMax + 1))),
      ‖(((outer idx.1.1.1 *
          mtPrimeBlockFamilyAF data.block idx.1.1.2.2.toFinset) *
          mtUpperAdicCoefficientAF (mtTruncLegendreCoefficient z D) δ idx.1.2) *
          mtUpperAdicOneAF δ idx.2) n‖ ≤
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (r + 3)) n : ℕ) : ℝ) := by
  let H := mtAllActiveBlockChains data maxDepth j
  let E := Finset.range (eMax + 1)
  let K := Finset.range (kMax + 1)
  let Z := (ArithmeticFunction.zeta : ArithmeticFunction ℕ)
  let chainAF : (ℕ × List (Fin t)) → ArithmeticFunction ℂ := fun dc =>
    mtPrimeBlockFamilyAF data.block dc.2.toFinset
  let eAF : ℕ → ArithmeticFunction ℂ := fun e =>
    mtUpperAdicCoefficientAF (mtTruncLegendreCoefficient z D) δ e
  let kAF : ℕ → ArithmeticFunction ℂ := fun k => mtUpperAdicOneAF δ k
  have hchain : ∀ m, ∑ dc ∈ H, ‖chainAF dc m‖ ≤ (Z m : ℝ) := by
    intro m
    rcases m.eq_zero_or_pos with rfl | hm
    · simp [H, chainAF, Z, mtPrimeBlockFamilyAF]
    · simpa [H, chainAF, Z, hm.ne'] using
        sum_norm_mtPrimeBlockFamilyAF_allActiveChainTags_le_one data maxDepth j m
  have he : ∀ m, ∑ e ∈ E, ‖eAF e m‖ ≤ (Z m : ℝ) := by
    intro m
    rcases m.eq_zero_or_pos with rfl | hm
    · simp [E, eAF, Z, mtUpperAdicCoefficientAF, mtRealIntervalAF]
    · simpa [E, eAF, Z, hm.ne'] using
        sum_norm_mtUpperAdicTruncLegendre_le_one hδ z D eMax m
  have hk : ∀ m, ∑ k ∈ K, ‖kAF k m‖ ≤ (Z m : ℝ) := by
    intro m
    rcases m.eq_zero_or_pos with rfl | hm
    · simp [K, kAF, Z, mtUpperAdicOneAF, mtRealIntervalAF]
    · simpa [K, kAF, Z, hm.ne'] using sum_norm_mtUpperAdicOneAF_le_one hδ kMax m
  have hOuterChain := sum_norm_family_convolution_le
    S H outer chainAF (Z ^ r) Z houter hchain
  let outerChain : ι × (ℕ × List (Fin t)) → ArithmeticFunction ℂ := fun ic =>
    outer ic.1 * chainAF ic.2
  have hOuterChainE := sum_norm_family_convolution_le
    (S.product H) E outerChain eAF ((Z ^ r) * Z) Z
    (fun m => by simpa [outerChain] using hOuterChain m) he
  let outerChainE : (ι × (ℕ × List (Fin t))) × ℕ → ArithmeticFunction ℂ := fun ice =>
    outerChain ice.1 * eAF ice.2
  have hAll := sum_norm_family_convolution_le
    ((S.product H).product E) K outerChainE kAF (((Z ^ r) * Z) * Z) Z
    (fun m => by simpa [outerChainE] using hOuterChainE m) hk n
  simpa [H, E, K, Z, chainAF, eAF, kAF, outerChain, outerChainE,
    pow_succ, Nat.add_assoc] using hAll

/-- Complete signed pair-box family has the sharp `ζ⁵` envelope. -/
theorem sum_norm_mtSignedPairBoxFamily_le_zeta_pow_five
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (data : MTFiniteIterationSourceData t)
    (hblock : ∀ i, data.block i = mtHarmanSourceBlock endpoint P i)
    (maxDepth : ℕ) (j : Fin (t + 1)) {δ : ℝ} (hδ : 0 < δ)
    (z D eMax kMax n : ℕ) :
    ∑ idx ∈ ((((mtHarmanActiveGoodPairCells (t := t) endpoint E).product
        (mtAllActiveBlockChains data maxDepth j)).product
        (Finset.range (eMax + 1))).product (Finset.range (kMax + 1))),
      ‖mtSignedBlockChainAdicBoxAF
        (mtHarmanPairCellCoefficient
          (data.block idx.1.1.1.1) (data.block idx.1.1.1.2))
        data.block idx.1.1.2.2 z D δ idx.1.2 idx.2 n‖ ≤
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 5) n : ℕ) : ℝ) := by
  have houter : ∀ m,
      ∑ cell ∈ mtHarmanActiveGoodPairCells (t := t) endpoint E,
        ‖mtCoefficientAF
          (mtHarmanPairCellCoefficient (data.block cell.1) (data.block cell.2)) m‖ ≤
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 2) m : ℕ) : ℝ) := by
    intro m
    simpa only [hblock] using
      sum_norm_mtHarmanPairCellFamilyCoefficientAF_le_zeta_sq hmono P E m
  simpa [mtSignedBlockChainAdicBoxAF, mtBlockChainAdicBoxAF] using
    sum_norm_outer_active_adic_boxFamily_le_zeta_pow
      (mtHarmanActiveGoodPairCells (t := t) endpoint E)
      (fun cell => mtCoefficientAF
        (mtHarmanPairCellCoefficient (data.block cell.1) (data.block cell.2)))
      data maxDepth j hδ z D eMax kMax 2 houter n

/-- Complete signed triple-box family has the sharp `ζ⁶` envelope. -/
theorem sum_norm_mtSignedTripleBoxFamily_le_zeta_pow_six
    {t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (data : MTFiniteIterationSourceData t)
    (hblock : ∀ i, data.block i = mtHarmanSourceBlock endpoint P i)
    (maxDepth : ℕ) (j : Fin (t + 1)) {δ : ℝ} (hδ : 0 < δ)
    (z D eMax kMax n : ℕ) :
    ∑ idx ∈ ((((mtHarmanActiveGoodTripleCells (t := t) endpoint E).product
        (mtAllActiveBlockChains data maxDepth j)).product
        (Finset.range (eMax + 1))).product (Finset.range (kMax + 1))),
      ‖mtSignedBlockChainAdicBoxAF
        (mtHarmanTripleCellCoefficient
          (data.block idx.1.1.1.1.1) (data.block idx.1.1.1.1.2)
          (data.block idx.1.1.1.2))
        data.block idx.1.1.2.2 z D δ idx.1.2 idx.2 n‖ ≤
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 6) n : ℕ) : ℝ) := by
  have houter : ∀ m,
      ∑ cell ∈ mtHarmanActiveGoodTripleCells (t := t) endpoint E,
        ‖mtCoefficientAF (mtHarmanTripleCellCoefficient
          (data.block cell.1.1) (data.block cell.1.2) (data.block cell.2)) m‖ ≤
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 3) m : ℕ) : ℝ) := by
    intro m
    simpa only [hblock] using
      sum_norm_mtHarmanTripleCellFamilyCoefficientAF_le_zeta_cube hmono P E m
  simpa [mtSignedBlockChainAdicBoxAF, mtBlockChainAdicBoxAF] using
    sum_norm_outer_active_adic_boxFamily_le_zeta_pow
      (mtHarmanActiveGoodTripleCells (t := t) endpoint E)
      (fun cell => mtCoefficientAF (mtHarmanTripleCellCoefficient
        (data.block cell.1.1) (data.block cell.1.2) (data.block cell.2)))
      data maxDepth j hδ z D eMax kMax 3 houter n

/-- Literal pair cells and recursive chains may use independent geometric schedules. -/
theorem sum_norm_mtSignedSeparatedPairBoxFamily_le_zeta_pow_five
    {u t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (data : MTFiniteIterationSourceData t)
    (maxDepth : ℕ) (j : Fin (t + 1)) {δ : ℝ} (hδ : 0 < δ)
    (z D eMax kMax n : ℕ) :
    ∑ idx ∈ ((((mtHarmanActiveGoodPairCells (t := u) endpoint E).product
        (mtAllActiveBlockChains data maxDepth j)).product
        (Finset.range (eMax + 1))).product (Finset.range (kMax + 1))),
      ‖mtSignedBlockChainAdicBoxAF
        (mtHarmanPairCellCoefficient
          (mtHarmanSourceBlock endpoint P idx.1.1.1.1)
          (mtHarmanSourceBlock endpoint P idx.1.1.1.2))
        data.block idx.1.1.2.2 z D δ idx.1.2 idx.2 n‖ ≤
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 5) n : ℕ) : ℝ) := by
  have houter : ∀ m,
      ∑ cell ∈ mtHarmanActiveGoodPairCells (t := u) endpoint E,
        ‖mtCoefficientAF (mtHarmanPairCellCoefficient
          (mtHarmanSourceBlock endpoint P cell.1)
          (mtHarmanSourceBlock endpoint P cell.2)) m‖ ≤
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 2) m : ℕ) : ℝ) :=
    sum_norm_mtHarmanPairCellFamilyCoefficientAF_le_zeta_sq hmono P E
  simpa [mtSignedBlockChainAdicBoxAF, mtBlockChainAdicBoxAF] using
    sum_norm_outer_active_adic_boxFamily_le_zeta_pow
      (mtHarmanActiveGoodPairCells (t := u) endpoint E)
      (fun cell => mtCoefficientAF (mtHarmanPairCellCoefficient
        (mtHarmanSourceBlock endpoint P cell.1)
        (mtHarmanSourceBlock endpoint P cell.2)))
      data maxDepth j hδ z D eMax kMax 2 houter n

/-- Literal triple cells and recursive chains may use independent geometric schedules. -/
theorem sum_norm_mtSignedSeparatedTripleBoxFamily_le_zeta_pow_six
    {u t : ℕ} {endpoint : ℕ → ℕ} (hmono : Monotone endpoint)
    (P : Finset ℕ) (E : ℝ) (data : MTFiniteIterationSourceData t)
    (maxDepth : ℕ) (j : Fin (t + 1)) {δ : ℝ} (hδ : 0 < δ)
    (z D eMax kMax n : ℕ) :
    ∑ idx ∈ ((((mtHarmanActiveGoodTripleCells (t := u) endpoint E).product
        (mtAllActiveBlockChains data maxDepth j)).product
        (Finset.range (eMax + 1))).product (Finset.range (kMax + 1))),
      ‖mtSignedBlockChainAdicBoxAF
        (mtHarmanTripleCellCoefficient
          (mtHarmanSourceBlock endpoint P idx.1.1.1.1.1)
          (mtHarmanSourceBlock endpoint P idx.1.1.1.1.2)
          (mtHarmanSourceBlock endpoint P idx.1.1.1.2))
        data.block idx.1.1.2.2 z D δ idx.1.2 idx.2 n‖ ≤
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 6) n : ℕ) : ℝ) := by
  have houter : ∀ m,
      ∑ cell ∈ mtHarmanActiveGoodTripleCells (t := u) endpoint E,
        ‖mtCoefficientAF (mtHarmanTripleCellCoefficient
          (mtHarmanSourceBlock endpoint P cell.1.1)
          (mtHarmanSourceBlock endpoint P cell.1.2)
          (mtHarmanSourceBlock endpoint P cell.2)) m‖ ≤
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 3) m : ℕ) : ℝ) :=
    sum_norm_mtHarmanTripleCellFamilyCoefficientAF_le_zeta_cube hmono P E
  simpa [mtSignedBlockChainAdicBoxAF, mtBlockChainAdicBoxAF] using
    sum_norm_outer_active_adic_boxFamily_le_zeta_pow
      (mtHarmanActiveGoodTripleCells (t := u) endpoint E)
      (fun cell => mtCoefficientAF (mtHarmanTripleCellCoefficient
        (mtHarmanSourceBlock endpoint P cell.1.1)
        (mtHarmanSourceBlock endpoint P cell.1.2)
        (mtHarmanSourceBlock endpoint P cell.2)))
      data maxDepth j hδ z D eMax kMax 3 houter n

end

end RHTower.Sieve

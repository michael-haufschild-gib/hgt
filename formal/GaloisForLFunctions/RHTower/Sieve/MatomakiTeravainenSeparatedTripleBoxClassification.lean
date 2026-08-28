import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenSeparatedPairBoxClassification
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTripleBoxClassification
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIICardinality

/-!
# Triple-box classification for independent Harman and Buchstab schedules

Literal outer triple cells remain on the aligned `[z,D)` schedule while recursive block chains
remain on the rooted `[z₀,z)` schedule.  Exact Type-I/II and Type-II factorizations preserve this
separation.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

def mtSeparatedTripleTypeI_II_M1 {u : ℕ}
    (endpoint : ℕ → ℕ) (delta : ℝ) (i2 i3 : Fin u) (eIndex : ℕ) : ℝ :=
  (mtAdjacentBlockLowerScale endpoint i2.1 *
      mtAdjacentBlockLowerScale endpoint i3.1) * mtUpperAdicScale delta eIndex

def mtSeparatedTripleTypeI_II_M2 {u t : ℕ}
    (endpoint : ℕ → ℕ) (delta : ℝ) (recStart : ℕ)
    (i1 : Fin u) (chain : List (Fin t)) : ℝ :=
  mtAdjacentBlockLowerScale endpoint i1.1 *
    ∏ j ∈ chain.toFinset, mtGeometricLevel delta recStart j.1

theorem mtSeparatedTripleTypeI_II_M1_pos
    {u : ℕ} {endpoint : ℕ → ℕ} {delta : ℝ}
    (hendpoint : ∀ i, 2 ≤ endpoint i) (hdelta : 0 < delta)
    (i2 i3 : Fin u) (eIndex : ℕ) :
    0 < mtSeparatedTripleTypeI_II_M1 endpoint delta i2 i3 eIndex := by
  unfold mtSeparatedTripleTypeI_II_M1
  have hL2 : 0 < mtAdjacentBlockLowerScale endpoint i2.1 := by
    unfold mtAdjacentBlockLowerScale
    exact_mod_cast (by have := hendpoint i2.1; omega : 0 < endpoint i2.1 - 1)
  have hL3 : 0 < mtAdjacentBlockLowerScale endpoint i3.1 := by
    unfold mtAdjacentBlockLowerScale
    exact_mod_cast (by have := hendpoint i3.1; omega : 0 < endpoint i3.1 - 1)
  exact mul_pos (mul_pos hL2 hL3) (mtUpperAdicScale_pos hdelta eIndex)

theorem mtSeparatedTripleTypeI_II_M2_pos
    {u t : ℕ} {endpoint : ℕ → ℕ} {delta : ℝ}
    (hendpoint : ∀ i, 2 ≤ endpoint i) (hdelta : 0 < delta)
    (recStart : ℕ) (i1 : Fin u) (chain : List (Fin t)) :
    0 < mtSeparatedTripleTypeI_II_M2 endpoint delta recStart i1 chain := by
  unfold mtSeparatedTripleTypeI_II_M2
  have hL1 : 0 < mtAdjacentBlockLowerScale endpoint i1.1 := by
    unfold mtAdjacentBlockLowerScale
    exact_mod_cast (by have := hendpoint i1.1; omega : 0 < endpoint i1.1 - 1)
  exact mul_pos hL1
    (Finset.prod_pos fun j _ => mtGeometricLevel_pos hdelta recStart j.1)

/-- Signed first Type-I/II factor: outer `(q₂,q₃)` pair and the adic `e` block. -/
def mtSeparatedTripleTypeI_II_FirstAF {u t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (data : MTFiniteIterationSourceData t)
    (i2 i3 : Fin u) (chainLength : ℕ)
    (z0 D : ℕ) (delta : ℝ) (eIndex : ℕ) : ArithmeticFunction ℂ :=
  ((-1 : ℂ) ^ chainLength) •
    mtBlockChainLongAF
      (mtHarmanPairCellCoefficient
        (mtHarmanSourceBlock endpoint P i2)
        (mtHarmanSourceBlock endpoint P i3))
      data.block [] z0 D delta eIndex

theorem mtSeparatedTripleTypeI_II_FirstAF_scaleSupported
    {u : ℕ} {endpoint : ℕ → ℕ} {delta : ℝ}
    (hendpoint : ∀ i, 2 ≤ endpoint i)
    (hband : ∀ i, mtAdjacentBlockUpperScale endpoint i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpoint i)
    (P : Finset ℕ) (z0 D recStart : ℕ) {recRoot : ℝ}
    (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D recStart delta recRoot hdelta hz0 hroot).block)
    (i2 i3 : Fin u) (chainLength eIndex : ℕ)
    (hdilation : (1 + delta) ^ 3 ≤ 2) :
    MTRealScaleSupported
      (mtSeparatedTripleTypeI_II_FirstAF endpoint P data i2 i3 chainLength
        z0 D delta eIndex)
      (mtSeparatedTripleTypeI_II_M1 endpoint delta i2 i3 eIndex)
      (2 * mtSeparatedTripleTypeI_II_M1 endpoint delta i2 i3 eIndex) := by
  have hunsigned : MTRealScaleSupported
      (mtBlockChainLongAF
        (mtHarmanPairCellCoefficient
          (mtHarmanSourceBlock endpoint P i2)
          (mtHarmanSourceBlock endpoint P i3))
        data.block [] z0 D delta eIndex)
      (mtSeparatedPairBoxLongScale
        (t := mtMinimalGeometricDepth delta recStart recRoot hdelta)
        endpoint delta recStart i2 i3 [] eIndex)
      (2 * mtSeparatedPairBoxLongScale
        (t := mtMinimalGeometricDepth delta recStart recRoot hdelta)
        endpoint delta recStart i2 i3 [] eIndex) := by
    intro n hn
    exact (mtSeparatedPairLongAF_scaleSupported_dyadic
      hendpoint hband P z0 D recStart hdelta hz0 hroot data hblocks
      i2 i3 (chain := []) (by simp) eIndex (by simpa using hdilation)) hn
  intro n hn
  have hs := (MTRealScaleSupported.smul hunsigned ((-1 : ℂ) ^ chainLength)) hn
  simpa [mtSeparatedTripleTypeI_II_FirstAF,
    mtSeparatedTripleTypeI_II_M1, mtSeparatedPairBoxLongScale] using hs

theorem mtSeparatedTripleTypeI_II_FirstAF_polynomialDivisorBounded
    {u t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (data : MTFiniteIterationSourceData t) (i2 i3 : Fin u)
    (chainLength : ℕ) (z0 D : ℕ) (delta : ℝ) (eIndex : ℕ) :
    MTPolynomialDivisorBounded (fun n =>
      mtSeparatedTripleTypeI_II_FirstAF endpoint P data i2 i3 chainLength
        z0 D delta eIndex n) := by
  exact MTPolynomialDivisorBounded.arithmeticFunction_smul
    (mtSeparatedPairLongAF_polynomialDivisorBounded
      endpoint P data i2 i3 (chain := []) (by simp) z0 D delta eIndex)
    ((-1 : ℂ) ^ chainLength)

/-- Second Type-I/II factor: outer `q₁` block and every recursive block. -/
def mtSeparatedTripleTypeI_II_SecondAF {u t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (data : MTFiniteIterationSourceData t)
    (i1 : Fin u) (chain : List (Fin t)) : ArithmeticFunction ℂ :=
  mtBlockChainCoefficientAF
    (fun n => if n ∈ mtHarmanSourceBlock endpoint P i1 then (1 : ℂ) else 0)
    data.block chain

theorem mtSeparatedTripleTypeI_II_SecondAF_scaleSupported
    {u : ℕ} {endpoint : ℕ → ℕ} {delta : ℝ}
    (hendpoint : ∀ i, 2 ≤ endpoint i)
    (hband : ∀ i, mtAdjacentBlockUpperScale endpoint i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpoint i)
    (P : Finset ℕ) (z0 D recStart : ℕ) {recRoot : ℝ}
    (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D recStart delta recRoot hdelta hz0 hroot).block)
    (i1 : Fin u)
    {chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta))}
    (hchain : chain.Nodup)
    (hdilation : (1 + delta) ^ (chain.length + 1) ≤ 2) :
    MTRealScaleSupported
      (mtSeparatedTripleTypeI_II_SecondAF endpoint P data i1 chain)
      (mtSeparatedTripleTypeI_II_M2 endpoint delta recStart i1 chain)
      (2 * mtSeparatedTripleTypeI_II_M2 endpoint delta recStart i1 chain) := by
  let Q : Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta) → ℝ :=
    fun i => mtGeometricLevel delta recStart i.1
  let L := mtAdjacentBlockLowerScale endpoint i1.1
  let M := mtSeparatedTripleTypeI_II_M2 endpoint delta recStart i1 chain
  have hfirst : MTRealScaleSupported
      (mtCoefficientAF
        (fun n => if n ∈ mtHarmanSourceBlock endpoint P i1 then (1 : ℂ) else 0))
      L (L * (1 + delta)) := by
    rw [mtCoefficientAF_primeBlockIndicator_eq]
    intro n hn
    have hs := mtHarmanSourceBlock_scaleSupported
      (fun i => (hendpoint i).trans' one_le_two) P i1 hn
    exact ⟨hs.1, hs.2.1, hs.2.2.trans (by
      simpa [L, mul_comm] using hband i1.1)⟩
  have hrecBlock : ∀ i,
      MTRealScaleSupported (mtPrimeBlockAF (data.block i))
        (Q i) (Q i * (1 + delta)) := by
    intro i
    rw [hblocks]
    exact mtMinimalGeometricBlock_scaleSupported
      z0 D recStart hdelta hz0 hroot i
  have hraw : MTRealScaleSupported
      (mtSeparatedTripleTypeI_II_SecondAF endpoint P data i1 chain)
      (L * ∏ j ∈ chain.toFinset, Q j)
      ((L * (1 + delta)) *
        ∏ j ∈ chain.toFinset, (Q j * (1 + delta))) := by
    exact mtBlockChainCoefficientAF_scaleSupported hfirst hrecBlock
      (fun i => (mtGeometricLevel_pos hdelta recStart i.1).le)
      (Nat.cast_nonneg _) hchain
  have hnormalized : MTRealScaleSupported
      (mtSeparatedTripleTypeI_II_SecondAF endpoint P data i1 chain)
      M ((1 + delta) ^ (chain.length + 1) * M) := by
    intro n hn
    have hs := hraw hn
    refine ⟨hs.1, by simpa [M, mtSeparatedTripleTypeI_II_M2, L, Q] using hs.2.1, ?_⟩
    have hprod : (∏ j ∈ chain.toFinset, (Q j * (1 + delta))) =
        (1 + delta) ^ chain.length * ∏ j ∈ chain.toFinset, Q j :=
      prod_mul_constant_chain_toFinset Q (1 + delta) hchain
    calc
      (n : ℝ) ≤ (L * (1 + delta)) *
          ∏ j ∈ chain.toFinset, (Q j * (1 + delta)) := hs.2.2
      _ = (1 + delta) ^ (chain.length + 1) * M := by
        rw [hprod, pow_succ]
        dsimp [M, mtSeparatedTripleTypeI_II_M2, L, Q]
        ring
  apply MTRealScaleSupported.dyadic_of_dilation hnormalized
  · exact (mtSeparatedTripleTypeI_II_M2_pos
      hendpoint hdelta recStart i1 chain).le
  · exact hdilation

theorem mtSeparatedTripleTypeI_II_SecondAF_polynomialDivisorBounded
    {u t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (data : MTFiniteIterationSourceData t) (i1 : Fin u)
    {chain : List (Fin t)} (hchain : chain.Nodup) :
    MTPolynomialDivisorBounded (fun n =>
      mtSeparatedTripleTypeI_II_SecondAF endpoint P data i1 chain n) := by
  have hindicator : MTPolynomialDivisorBounded
      (fun n => if n ∈ mtHarmanSourceBlock endpoint P i1 then (1 : ℂ) else 0) := by
    refine ⟨1, by norm_num, 0, ?_⟩
    intro n hn
    by_cases hmem : n ∈ mtHarmanSourceBlock endpoint P i1 <;> simp [hmem]
  exact mtBlockChainCoefficientAF_polynomialDivisorBounded hindicator hchain

/-- Exact algebraic Type-I/II factorization for one separated triple box. -/
theorem mtSignedSeparatedTripleBox_eq_typeI_II_factors
    {u t : ℕ} (endpoint : ℕ → ℕ) (hendpoint : ∀ i, 2 ≤ endpoint i)
    (P : Finset ℕ) (data : MTFiniteIterationSourceData t)
    (i1 i2 i3 : Fin u) (chain : List (Fin t))
    (z0 D : ℕ) (delta : ℝ) (eIndex kIndex : ℕ) :
    mtSignedBlockChainAdicBoxAF
        (mtHarmanTripleCellCoefficient
          (mtHarmanSourceBlock endpoint P i1)
          (mtHarmanSourceBlock endpoint P i2)
          (mtHarmanSourceBlock endpoint P i3))
        data.block chain z0 D delta eIndex kIndex =
      (mtSeparatedTripleTypeI_II_FirstAF endpoint P data i2 i3 chain.length
          z0 D delta eIndex *
        mtSeparatedTripleTypeI_II_SecondAF endpoint P data i1 chain) *
        mtUpperAdicOneAF delta kIndex := by
  have hpos2 : ∀ q ∈ mtHarmanSourceBlock endpoint P i2, 0 < q := by
    intro q hq
    exact ((mem_mtAdjacentPrimeBlock_scale_iff
      (fun i => (hendpoint i).trans' one_le_two) i2 q).mp
        (Finset.mem_inter.mp hq).1).1.pos
  have hpos3 : ∀ q ∈ mtHarmanSourceBlock endpoint P i3, 0 < q := by
    intro q hq
    exact ((mem_mtAdjacentPrimeBlock_scale_iff
      (fun i => (hendpoint i).trans' one_le_two) i3 q).mp
        (Finset.mem_inter.mp hq).1).1.pos
  simp only [mtSignedBlockChainAdicBoxAF, mtBlockChainAdicBoxAF,
    mtSeparatedTripleTypeI_II_FirstAF, mtSeparatedTripleTypeI_II_SecondAF,
    mtBlockChainLongAF, mtBlockChainCoefficientAF, List.toFinset_nil,
    mtPrimeBlockFamilyAF, Finset.prod_empty, mul_one]
  rw [mtCoefficientAF_tripleCell_eq_pairCell_mul_primeBlock
    (mtHarmanSourceBlock endpoint P i1)
    (mtHarmanSourceBlock endpoint P i2)
    (mtHarmanSourceBlock endpoint P i3) hpos2 hpos3]
  rw [mtCoefficientAF_primeBlockIndicator_eq, smul_mul_assoc, smul_mul_assoc]
  apply congrArg (fun H : ArithmeticFunction ℂ => ((-1 : ℂ) ^ chain.length) • H)
  ac_rfl

def mtSeparatedTripleTypeIIM2 {u t : ℕ}
    (endpoint : ℕ → ℕ) (delta : ℝ) (recStart : ℕ)
    (i1 i2 i3 : Fin u) (chain : List (Fin t)) (I : Finset (Fin t))
    (eIndex kIndex : ℕ) : ℝ :=
  mtSeparatedTripleBoxProductScale endpoint delta recStart i1 i2 i3
    (mtBlockChainRemainder chain I) eIndex kIndex

def mtSeparatedTripleTypeIIBetaAF {u t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (data : MTFiniteIterationSourceData t)
    (i1 i2 i3 : Fin u) (chain : List (Fin t)) (I : Finset (Fin t))
    (z0 D : ℕ) (delta : ℝ) (eIndex kIndex : ℕ) : ArithmeticFunction ℂ :=
  ((-1 : ℂ) ^ chain.length) •
    (mtBlockChainLongAF
      (mtHarmanTripleCellCoefficient
        (mtHarmanSourceBlock endpoint P i1)
        (mtHarmanSourceBlock endpoint P i2)
        (mtHarmanSourceBlock endpoint P i3))
      data.block (mtBlockChainRemainder chain I) z0 D delta eIndex *
      mtUpperAdicOneAF delta kIndex)

theorem mtSeparatedTripleTypeIIM2_pos
    {u t : ℕ} {endpoint : ℕ → ℕ} {delta : ℝ}
    (hendpoint : ∀ i, 2 ≤ endpoint i) (hdelta : 0 < delta)
    (recStart : ℕ) (i1 i2 i3 : Fin u) (chain : List (Fin t))
    (I : Finset (Fin t)) (eIndex kIndex : ℕ) :
    0 < mtSeparatedTripleTypeIIM2 endpoint delta recStart
      i1 i2 i3 chain I eIndex kIndex := by
  unfold mtSeparatedTripleTypeIIM2 mtSeparatedTripleBoxProductScale
  have hL1 : 0 < mtAdjacentBlockLowerScale endpoint i1.1 := by
    unfold mtAdjacentBlockLowerScale
    exact_mod_cast (by have := hendpoint i1.1; omega : 0 < endpoint i1.1 - 1)
  have hL2 : 0 < mtAdjacentBlockLowerScale endpoint i2.1 := by
    unfold mtAdjacentBlockLowerScale
    exact_mod_cast (by have := hendpoint i2.1; omega : 0 < endpoint i2.1 - 1)
  have hL3 : 0 < mtAdjacentBlockLowerScale endpoint i3.1 := by
    unfold mtAdjacentBlockLowerScale
    exact_mod_cast (by have := hendpoint i3.1; omega : 0 < endpoint i3.1 - 1)
  exact mul_pos
    (mul_pos
      (mul_pos
        (mul_pos (mul_pos hL1 hL2) hL3)
        (Finset.prod_pos fun j _ => mtGeometricLevel_pos hdelta recStart j.1))
      (mtUpperAdicScale_pos hdelta eIndex))
    (mtUpperAdicScale_pos hdelta kIndex)

theorem mtSeparatedTripleTypeIIBetaAF_scaleSupported
    {u : ℕ} {endpoint : ℕ → ℕ} {delta : ℝ}
    (hendpoint : ∀ i, 2 ≤ endpoint i)
    (hband : ∀ i, mtAdjacentBlockUpperScale endpoint i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpoint i)
    (P : Finset ℕ) (z0 D recStart : ℕ) {recRoot : ℝ}
    (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D recStart delta recRoot hdelta hz0 hroot).block)
    (i1 i2 i3 : Fin u)
    {chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta))}
    (hchain : chain.Nodup)
    (I : Finset (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta)))
    (eIndex kIndex : ℕ)
    (hdilation : (1 + delta) ^ ((mtBlockChainRemainder chain I).length + 5) ≤ 2) :
    MTRealScaleSupported
      (mtSeparatedTripleTypeIIBetaAF endpoint P data i1 i2 i3 chain I
        z0 D delta eIndex kIndex)
      (mtSeparatedTripleTypeIIM2 endpoint delta recStart
        i1 i2 i3 chain I eIndex kIndex)
      (2 * mtSeparatedTripleTypeIIM2 endpoint delta recStart
        i1 i2 i3 chain I eIndex kIndex) := by
  let remainder := mtBlockChainRemainder chain I
  let U := mtBlockChainAdicBoxAF
    (mtHarmanTripleCellCoefficient
      (mtHarmanSourceBlock endpoint P i1)
      (mtHarmanSourceBlock endpoint P i2)
      (mtHarmanSourceBlock endpoint P i3))
    data.block remainder z0 D delta eIndex kIndex
  have hsigned : MTRealScaleSupported
      (mtSignedBlockChainAdicBoxAF
        (mtHarmanTripleCellCoefficient
          (mtHarmanSourceBlock endpoint P i1)
          (mtHarmanSourceBlock endpoint P i2)
          (mtHarmanSourceBlock endpoint P i3))
        data.block remainder z0 D delta eIndex kIndex)
      (mtSeparatedTripleTypeIIM2 endpoint delta recStart
        i1 i2 i3 chain I eIndex kIndex)
      (2 * mtSeparatedTripleTypeIIM2 endpoint delta recStart
        i1 i2 i3 chain I eIndex kIndex) := by
    intro n hn
    have hs := (mtSignedSeparatedTripleBox_scaleSupported_commonProductCollar
      (eta := 1) hendpoint hband P z0 D recStart hdelta hz0 hroot data hblocks
      i1 i2 i3 (mtBlockChainRemainder_nodup hchain I)
      remainder.length eIndex kIndex (le_refl _) (by
        convert hdilation using 1
        norm_num [remainder])) hn
    norm_num at hs
    simpa [mtSeparatedTripleTypeIIM2, remainder] using hs
  have hunsigned : MTRealScaleSupported U
      (mtSeparatedTripleTypeIIM2 endpoint delta recStart
        i1 i2 i3 chain I eIndex kIndex)
      (2 * mtSeparatedTripleTypeIIM2 endpoint delta recStart
        i1 i2 i3 chain I eIndex kIndex) := by
    intro n hn
    apply hsigned
    change (((-1 : ℂ) ^ remainder.length) • U) n ≠ 0
    change ((-1 : ℂ) ^ remainder.length * U n) ≠ 0
    exact mul_ne_zero (by simp) hn
  intro n hn
  apply (MTRealScaleSupported.smul hunsigned ((-1 : ℂ) ^ chain.length))
  simpa only [mtSeparatedTripleTypeIIBetaAF, U, mtBlockChainAdicBoxAF,
    mtBlockChainLongAF, mtBlockChainCoefficientAF, remainder] using hn

theorem mtSeparatedTripleTypeIIBetaAF_polynomialDivisorBounded
    {u t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (data : MTFiniteIterationSourceData t) (i1 i2 i3 : Fin u)
    {chain : List (Fin t)} (hchain : chain.Nodup) (I : Finset (Fin t))
    (z0 D : ℕ) (delta : ℝ) (eIndex kIndex : ℕ) :
    MTPolynomialDivisorBounded (fun n =>
      mtSeparatedTripleTypeIIBetaAF endpoint P data i1 i2 i3 chain I
        z0 D delta eIndex kIndex n) := by
  have hone : MTPolynomialDivisorBounded (fun _ : ℕ => (1 : ℂ)) := by
    refine ⟨1, by norm_num, 0, ?_⟩
    intro n hn
    simp
  have hlong : MTPolynomialDivisorBounded (fun n =>
      mtBlockChainLongAF
        (mtHarmanTripleCellCoefficient
          (mtHarmanSourceBlock endpoint P i1)
          (mtHarmanSourceBlock endpoint P i2)
          (mtHarmanSourceBlock endpoint P i3))
        data.block (mtBlockChainRemainder chain I) z0 D delta eIndex n) :=
    mtBlockChainLongAF_polynomialDivisorBounded
      (mtHarmanTripleCellCoefficient_polynomialDivisorBounded
        (mtHarmanSourceBlock endpoint P i1)
        (mtHarmanSourceBlock endpoint P i2)
        (mtHarmanSourceBlock endpoint P i3))
      (mtBlockChainRemainder_nodup hchain I) z0 D delta eIndex
  have hk : MTPolynomialDivisorBounded (fun n => mtUpperAdicOneAF delta kIndex n) :=
    mtRealIntervalAF_polynomialDivisorBounded hone _ _
  exact MTPolynomialDivisorBounded.arithmeticFunction_smul
    (MTPolynomialDivisorBounded.arithmeticFunction_mul hlong hk)
    ((-1 : ℂ) ^ chain.length)

/-- Selected recursive blocks factor literally from an independent-schedule signed triple box. -/
theorem mtSignedSeparatedTripleBox_eq_selected_mul_typeIIBeta
    {u t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (data : MTFiniteIterationSourceData t) (i1 i2 i3 : Fin u)
    (chain : List (Fin t)) (I : Finset (Fin t)) (hI : I ⊆ chain.toFinset)
    (z0 D : ℕ) (delta : ℝ) (eIndex kIndex : ℕ) :
    mtSignedBlockChainAdicBoxAF
        (mtHarmanTripleCellCoefficient
          (mtHarmanSourceBlock endpoint P i1)
          (mtHarmanSourceBlock endpoint P i2)
          (mtHarmanSourceBlock endpoint P i3))
        data.block chain z0 D delta eIndex kIndex =
      mtPrimeBlockFamilyAF data.block I *
        mtSeparatedTripleTypeIIBetaAF endpoint P data i1 i2 i3 chain I
          z0 D delta eIndex kIndex := by
  rw [mtSignedBlockChainAdicBoxAF, mtBlockChainAdicBoxAF,
    mtSeparatedTripleTypeIIBetaAF, mtBlockChainLongAF,
    mtBlockChainCoefficientAF, mtPrimeBlockFamilyAF_split data.block hI,
    mtBlockChainRemainder_toFinset]
  rw [mul_smul_comm]
  congr 1
  ring

/-- Every admissible independent-schedule triple box is exactly Type I/II or Type II. -/
theorem mtSeparatedTripleBox_isProposition22Piece
    {u : ℕ} {endpoint : ℕ → ℕ} {delta : ℝ}
    (hendpoint : ∀ i, 2 ≤ endpoint i)
    (hband : ∀ i, mtAdjacentBlockUpperScale endpoint i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpoint i)
    (P : Finset ℕ) {X Y z0Real epsilon : ℝ}
    (z0 D recStart : ℕ) {recRoot : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D recStart delta recRoot hdelta hz0 hroot).block)
    (i1 i2 i3 : Fin u)
    (chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta)))
    (hchain : chain.Nodup) (eIndex kIndex : ℕ)
    (hX : 1 < X) (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ 2 / 11)
    (hrecRoot : recRoot = X ^ (2 / 11 : ℝ))
    (hrootOne : 1 ≤ mtGeometricLevel delta recStart 0)
    (hE : mtUpperAdicScale delta eIndex ≤ X ^ (epsilon / 4))
    (hQ1 : mtAdjacentBlockLowerScale endpoint i1.1 ≤
      X ^ (1 / 4 - 2 * epsilon))
    (hQ3Q2 : mtAdjacentBlockLowerScale endpoint i3.1 ≤
      mtAdjacentBlockLowerScale endpoint i2.1)
    (hgeometry : mtAdjacentBlockLowerScale endpoint i1.1 *
        mtAdjacentBlockLowerScale endpoint i2.1 ^ 4 ≤ X ^ (1 - 2 * epsilon))
    (hz0RealPos : 0 < z0Real)
    (hz0RealLevel : z0Real ≤ mtGeometricLevel delta recStart 0)
    (hchainBound : 1 < z0Real ∨ chain.toFinset.card ≤
      Nat.floor (Real.log recRoot / Real.log z0Real))
    (hdilation : ∀ R : ℕ, R ≤ chain.length + 5 → (1 + delta) ^ R ≤ 2)
    (hproduct : Y / 2 <
        mtSeparatedTripleBoxProductScale endpoint delta recStart
          i1 i2 i3 chain eIndex kIndex ∧
      mtSeparatedTripleBoxProductScale endpoint delta recStart
          i1 i2 i3 chain eIndex kIndex ≤ 4 * Y) :
    MTProposition22Piece X Y z0Real recRoot delta epsilon
      (mtSignedBlockChainAdicBoxAF
        (mtHarmanTripleCellCoefficient
          (mtHarmanSourceBlock endpoint P i1)
          (mtHarmanSourceBlock endpoint P i2)
          (mtHarmanSourceBlock endpoint P i3))
        data.block chain z0 D delta eIndex kIndex) := by
  let Q : Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta) → ℝ :=
    fun i => mtGeometricLevel delta recStart i.1
  have hQone : ∀ i ∈ chain.toFinset, 1 ≤ Q i := by
    intro i hi
    exact hrootOne.trans (mtMinimalGeometricSchedule_scale_mem hdelta recStart i).1
  have hQcap : ∀ i ∈ chain.toFinset, Q i ≤ X ^ (2 / 11 : ℝ) := by
    intro i hi
    rw [← hrecRoot]
    exact (mtMinimalGeometricSchedule_scale_mem hdelta recStart i).2.le
  rcases matomakiTeravainen_tripleTerm_typeI_II_or_typeII_finite
      (Q := Q) (S := chain.toFinset) hX hepsilon0 hepsilon
      (mtUpperAdicScale_pos hdelta eIndex).le
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      hE hQ1 hQ3Q2 hgeometry hQone hQcap with htypeI_II | htypeII
  · let M1 := mtSeparatedTripleTypeI_II_M1 endpoint delta i2 i3 eIndex
    let M2 := mtSeparatedTripleTypeI_II_M2 endpoint delta recStart i1 chain
    let M3 := mtUpperAdicScale delta kIndex
    let F := mtSeparatedTripleTypeI_II_FirstAF endpoint P data i2 i3
      chain.length z0 D delta eIndex
    let G := mtSeparatedTripleTypeI_II_SecondAF endpoint P data i1 chain
    have hsquare : M1 ^ 2 * M2 ≤ X ^ (1 - epsilon) := by
      calc
        M1 ^ 2 * M2 =
            (mtUpperAdicScale delta eIndex *
              mtAdjacentBlockLowerScale endpoint i2.1 *
              mtAdjacentBlockLowerScale endpoint i3.1) ^ 2 *
            (mtAdjacentBlockLowerScale endpoint i1.1 *
              ∏ i ∈ chain.toFinset, Q i) := by
          dsimp [M1, M2, mtSeparatedTripleTypeI_II_M1,
            mtSeparatedTripleTypeI_II_M2, Q]
          ring
        _ ≤ X ^ (1 - epsilon) := htypeI_II.1
    have hM2le : M2 ≤ X ^ (1 / 4 - epsilon) := by
      simpa [M2, mtSeparatedTripleTypeI_II_M2,
        mtAdjacentBlockLowerScale, Q] using htypeI_II.2
    have hproductEq : M1 * M2 * M3 =
        mtSeparatedTripleBoxProductScale endpoint delta recStart
          i1 i2 i3 chain eIndex kIndex := by
      dsimp [M1, M2, M3, mtSeparatedTripleTypeI_II_M1,
        mtSeparatedTripleTypeI_II_M2, mtSeparatedTripleBoxProductScale]
      ring
    have hproductI_II : Y / 2 < M1 * M2 * M3 ∧ M1 * M2 * M3 ≤ 4 * Y := by
      rw [hproductEq]
      exact hproduct
    have hFsupport : MTRealScaleSupported F M1 (2 * M1) := by
      exact mtSeparatedTripleTypeI_II_FirstAF_scaleSupported
        hendpoint hband P z0 D recStart hdelta hz0 hroot data hblocks
        i2 i3 chain.length eIndex (hdilation _ (by omega))
    have hGsupport : MTRealScaleSupported G M2 (2 * M2) := by
      exact mtSeparatedTripleTypeI_II_SecondAF_scaleSupported
        hendpoint hband P z0 D recStart hdelta hz0 hroot data hblocks
        i1 hchain (hdilation _ (by omega))
    have hFbounded : MTPolynomialDivisorBounded (fun n => F n) := by
      exact mtSeparatedTripleTypeI_II_FirstAF_polynomialDivisorBounded
        endpoint P data i2 i3 chain.length z0 D delta eIndex
    have hGbounded : MTPolynomialDivisorBounded (fun n => G n) := by
      exact mtSeparatedTripleTypeI_II_SecondAF_polynomialDivisorBounded
        endpoint P data i1 hchain
    let pieceData := mtTypeI_II_PieceDataOfSupported (delta := delta) F G
      (mtSeparatedTripleTypeI_II_M1_pos hendpoint hdelta i2 i3 eIndex)
      (mtSeparatedTripleTypeI_II_M2_pos hendpoint hdelta recStart i1 chain)
      (mtUpperAdicScale_pos hdelta kIndex)
      hFsupport hGsupport hFbounded hGbounded hsquare hM2le hproductI_II
    have hpiece : pieceData.pieceAF =
        mtSignedBlockChainAdicBoxAF
          (mtHarmanTripleCellCoefficient
            (mtHarmanSourceBlock endpoint P i1)
            (mtHarmanSourceBlock endpoint P i2)
            (mtHarmanSourceBlock endpoint P i3))
          data.block chain z0 D delta eIndex kIndex := by
      dsimp only [pieceData]
      rw [mtTypeI_II_PieceDataOfSupported_pieceAF_eq]
      exact (mtSignedSeparatedTripleBox_eq_typeI_II_factors
        endpoint hendpoint P data i1 i2 i3 chain z0 D delta eIndex kIndex).symm
    rw [← hpiece]
    exact MTProposition22Piece.typeI_II pieceData
  · obtain ⟨I, hIS, hI, hIlower, hIupper⟩ := htypeII
    have hR : I.card ≤ Nat.floor (Real.log recRoot / Real.log z0Real) := by
      rcases hchainBound with hz0RealOne | hchainCard
      · apply card_le_floor_log_div_log_of_one_lt_of_prod_le I Q hz0RealOne
        · intro i hi
          exact hz0RealLevel.trans
            (mtMinimalGeometricSchedule_scale_mem hdelta recStart i).1
        · simpa [hrecRoot] using hIupper
      · exact (Finset.card_le_card hIS).trans hchainCard
    have hIMem : X ^ (epsilon / 2) ≤ ∏ i ∈ I, Q i ∧
        (∏ i ∈ I, Q i) ≤ recRoot :=
      ⟨hIlower, by simpa [hrecRoot] using hIupper⟩
    let M2 := mtSeparatedTripleTypeIIM2 endpoint delta recStart
      i1 i2 i3 chain I eIndex kIndex
    let betaAF := mtSeparatedTripleTypeIIBetaAF endpoint P data i1 i2 i3 chain I
      z0 D delta eIndex kIndex
    have hproductEq :
        (∏ i ∈ I, Q i) * M2 =
          mtSeparatedTripleBoxProductScale endpoint delta recStart
            i1 i2 i3 chain eIndex kIndex := by
      have hsplit := prod_selected_mul_blockChainRemainder Q chain hIS
      dsimp [M2, mtSeparatedTripleTypeIIM2, mtSeparatedTripleBoxProductScale,
        Q] at hsplit ⊢
      rw [← hsplit]
      ring
    have hproductII : Y / 2 < (∏ i ∈ I, Q i) * M2 ∧
        (∏ i ∈ I, Q i) * M2 ≤ 4 * Y := by
      rw [hproductEq]
      exact hproduct
    have hbetaSupport : MTRealScaleSupported betaAF M2 (2 * M2) := by
      exact mtSeparatedTripleTypeIIBetaAF_scaleSupported
        hendpoint hband P z0 D recStart hdelta hz0 hroot data hblocks
        i1 i2 i3 hchain I eIndex kIndex (hdilation _ (by
          have hlen := mtBlockChainRemainder_length_le chain I
          omega))
    have hbetaBounded : MTPolynomialDivisorBounded (fun n => betaAF n) := by
      exact mtSeparatedTripleTypeIIBetaAF_polynomialDivisorBounded
        endpoint P data i1 i2 i3 hchain I z0 D delta eIndex kIndex
    let pieceData := mtMinimalGeometricTypeIIData
      z0 D recStart hdelta hz0 hroot I hI hz0RealPos hz0RealLevel hR
      (fun n => betaAF n)
      (mtSeparatedTripleTypeIIM2_pos hendpoint hdelta
        recStart i1 i2 i3 chain I eIndex kIndex)
      hbetaBounded hIMem hproductII
    have hpiece : pieceData.pieceAF =
        mtSignedBlockChainAdicBoxAF
          (mtHarmanTripleCellCoefficient
            (mtHarmanSourceBlock endpoint P i1)
            (mtHarmanSourceBlock endpoint P i2)
            (mtHarmanSourceBlock endpoint P i3))
          data.block chain z0 D delta eIndex kIndex := by
      calc
        pieceData.pieceAF =
            mtPrimeBlockFamilyAF
                (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
                  z0 D recStart delta recRoot hdelta hz0 hroot).block I *
              mtRealIntervalAF (fun n => betaAF n) M2 (2 * M2) := by
          exact mtMinimalGeometricTypeIIData_pieceAF_eq
            z0 D recStart hdelta hz0 hroot I hI hz0RealPos hz0RealLevel hR
            (fun n => betaAF n)
            (mtSeparatedTripleTypeIIM2_pos hendpoint hdelta
              recStart i1 i2 i3 chain I eIndex kIndex)
            hbetaBounded hIMem hproductII
        _ = mtPrimeBlockFamilyAF data.block I * betaAF := by
          rw [← hblocks, mtRealIntervalAF_coe_eq_of_scaleSupported hbetaSupport]
        _ = mtSignedBlockChainAdicBoxAF
              (mtHarmanTripleCellCoefficient
                (mtHarmanSourceBlock endpoint P i1)
                (mtHarmanSourceBlock endpoint P i2)
                (mtHarmanSourceBlock endpoint P i3))
              data.block chain z0 D delta eIndex kIndex :=
          (mtSignedSeparatedTripleBox_eq_selected_mul_typeIIBeta
            endpoint P data i1 i2 i3 chain I hIS z0 D delta eIndex kIndex).symm
    rw [← hpiece]
    exact MTProposition22Piece.typeII pieceData

end

end RHTower.Sieve

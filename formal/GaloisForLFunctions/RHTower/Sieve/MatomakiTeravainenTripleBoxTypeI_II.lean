import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPairBoxTypeII
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTripleCellFactorization

/-!
# Exact Type-I/II presentation of a triple box

The first factor contains the second and third Harman primes together with the truncated-Moebius
block.  The second factor contains the first Harman prime and every recursive block.  The terminal
cofactor is the narrow third factor.  All identities are literal Dirichlet-convolution identities.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- A finite-set indicator extended by `mtCoefficientAF` is the prime-block arithmetic function. -/
theorem mtCoefficientAF_primeBlockIndicator_eq (S : Finset ℕ) :
    mtCoefficientAF (fun n => if n ∈ S then (1 : ℂ) else 0) = mtPrimeBlockAF S := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [mtCoefficientAF, mtPrimeBlockAF]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    rw [mtCoefficientAF_apply_of_pos _ hnPos, mtPrimeBlockAF_apply_of_pos S hnPos]

/-- Base scale of the first Type-I/II factor in one triple box. -/
def mtMinimalGeometricTripleBoxTypeI_II_M1
    {t : ℕ} (delta : ℝ) (start : ℕ) (i2 i3 : Fin t) (eIndex : ℕ) : ℝ :=
  (mtGeometricLevel delta start i2.1 * mtGeometricLevel delta start i3.1) *
    mtUpperAdicScale delta eIndex

theorem mtMinimalGeometricTripleBoxTypeI_II_M1_pos
    {t : ℕ} {delta : ℝ} (hdelta : 0 < delta) (start : ℕ)
    (i2 i3 : Fin t) (eIndex : ℕ) :
    0 < mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex := by
  exact mul_pos
    (mul_pos (mtGeometricLevel_pos hdelta start i2.1)
      (mtGeometricLevel_pos hdelta start i3.1))
    (mtUpperAdicScale_pos hdelta eIndex)

/-- Base scale of the second Type-I/II factor in one triple box. -/
def mtMinimalGeometricTripleBoxTypeI_II_M2
    {t : ℕ} (delta : ℝ) (start : ℕ) (i1 : Fin t) (chain : List (Fin t)) : ℝ :=
  mtGeometricLevel delta start i1.1 *
    ∏ j ∈ chain.toFinset, mtGeometricLevel delta start j.1

theorem mtMinimalGeometricTripleBoxTypeI_II_M2_pos
    {t : ℕ} {delta : ℝ} (hdelta : 0 < delta) (start : ℕ)
    (i1 : Fin t) (chain : List (Fin t)) :
    0 < mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain := by
  exact mul_pos (mtGeometricLevel_pos hdelta start i1.1)
    (Finset.prod_pos fun j hj => mtGeometricLevel_pos hdelta start j.1)

/-- Signed first factor: pair cell for `(q₂,q₃)` convolved with the adic `e` block. -/
def mtMinimalGeometricTripleTypeI_II_FirstAF
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i2 i3 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chainLength eIndex : ℕ) : ArithmeticFunction ℂ :=
  ((-1 : ℂ) ^ chainLength) •
    mtBlockChainLongAF
      (mtHarmanPairCellCoefficient
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i2)
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i3))
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block [] z0 D delta eIndex

theorem mtMinimalGeometricTripleTypeI_II_FirstAF_scaleSupported
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i2 i3 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chainLength eIndex : ℕ) (hdilation : (1 + delta) ^ 3 ≤ 2) :
    MTRealScaleSupported
      (mtMinimalGeometricTripleTypeI_II_FirstAF
        z0 D start hdelta hz0 hroot i2 i3 chainLength eIndex)
      (mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex)
      (2 * mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex) := by
  have hunsigned : MTRealScaleSupported
      (mtBlockChainLongAF
        (mtHarmanPairCellCoefficient
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i2)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i3))
        (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block [] z0 D delta eIndex)
      (mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex)
      (2 * mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex) := by
    intro n hn
    have hs := (mtMinimalGeometricPairLongAF_scaleSupported_dyadic
        z0 D start hdelta hz0 hroot i2 i3 (chain := []) (by simp) eIndex
          (by simpa using hdilation)) hn
    simpa [mtMinimalGeometricTripleBoxTypeI_II_M1] using hs
  intro n hn
  exact (MTRealScaleSupported.smul hunsigned ((-1 : ℂ) ^ chainLength)) hn

theorem mtMinimalGeometricTripleTypeI_II_FirstAF_polynomialDivisorBounded
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i2 i3 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chainLength eIndex : ℕ) :
    MTPolynomialDivisorBounded (fun n =>
      mtMinimalGeometricTripleTypeI_II_FirstAF
        z0 D start hdelta hz0 hroot i2 i3 chainLength eIndex n) := by
  let source := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    z0 D start delta z hdelta hz0 hroot
  have hlong := mtBlockChainLongAF_polynomialDivisorBounded
    (block := source.block)
    (mtHarmanPairCellCoefficient_polynomialDivisorBounded
      (source.block i2) (source.block i3)) (chain := []) (by simp) z0 D delta eIndex
  exact MTPolynomialDivisorBounded.arithmeticFunction_smul hlong ((-1 : ℂ) ^ chainLength)

/-- Second factor: first Harman-prime block convolved with every recursive block. -/
def mtMinimalGeometricTripleTypeI_II_SecondAF
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta))) :
    ArithmeticFunction ℂ :=
  mtBlockChainCoefficientAF
    (fun n => if n ∈
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block i1 then (1 : ℂ) else 0)
    (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
      z0 D start delta z hdelta hz0 hroot).block chain

theorem mtMinimalGeometricTripleTypeI_II_SecondAF_scaleSupported
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    {chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta))}
    (hchain : chain.Nodup)
    (hdilation : (1 + delta) ^ (chain.length + 1) ≤ 2) :
    MTRealScaleSupported
      (mtMinimalGeometricTripleTypeI_II_SecondAF
        z0 D start hdelta hz0 hroot i1 chain)
      (mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain)
      (2 * mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain) := by
  let source := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    z0 D start delta z hdelta hz0 hroot
  let Q : Fin (mtMinimalGeometricDepth delta start z hdelta) → ℝ :=
    fun i => mtGeometricLevel delta start i.1
  let b : ℝ := 1 + delta
  have hfirst : MTRealScaleSupported
      (mtCoefficientAF (fun n => if n ∈ source.block i1 then (1 : ℂ) else 0))
      (Q i1) (Q i1 * b) := by
    rw [mtCoefficientAF_primeBlockIndicator_eq]
    exact mtMinimalGeometricBlock_scaleSupported z0 D start hdelta hz0 hroot i1
  have hraw : MTRealScaleSupported
      (mtMinimalGeometricTripleTypeI_II_SecondAF
        z0 D start hdelta hz0 hroot i1 chain)
      (Q i1 * ∏ j ∈ chain.toFinset, Q j)
      ((Q i1 * b) * ∏ j ∈ chain.toFinset, Q j * b) := by
    exact mtBlockChainCoefficientAF_scaleSupported hfirst
      (fun i => mtMinimalGeometricBlock_scaleSupported z0 D start hdelta hz0 hroot i)
      (fun i => (mtGeometricLevel_pos hdelta start i.1).le)
      (mtGeometricLevel_pos hdelta start i1.1).le hchain
  have hnormalized : MTRealScaleSupported
      (mtMinimalGeometricTripleTypeI_II_SecondAF
        z0 D start hdelta hz0 hroot i1 chain)
      (Q i1 * ∏ j ∈ chain.toFinset, Q j)
      (b ^ (chain.length + 1) * (Q i1 * ∏ j ∈ chain.toFinset, Q j)) := by
    intro n hn
    have hs := hraw hn
    refine ⟨hs.1, hs.2.1, hs.2.2.trans_eq ?_⟩
    rw [prod_mul_constant_chain_toFinset Q b hchain, pow_succ]
    ring
  apply MTRealScaleSupported.dyadic_of_dilation
    (M := mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain)
  · intro n hn
    have hs := hnormalized hn
    simpa [mtMinimalGeometricTripleBoxTypeI_II_M2] using hs
  · exact (mtMinimalGeometricTripleBoxTypeI_II_M2_pos hdelta start i1 chain).le
  · exact hdilation

theorem mtMinimalGeometricTripleTypeI_II_SecondAF_polynomialDivisorBounded
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    {chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta))}
    (hchain : chain.Nodup) :
    MTPolynomialDivisorBounded (fun n =>
      mtMinimalGeometricTripleTypeI_II_SecondAF
        z0 D start hdelta hz0 hroot i1 chain n) := by
  let source := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    z0 D start delta z hdelta hz0 hroot
  have hindicator : MTPolynomialDivisorBounded
      (fun n => if n ∈ source.block i1 then (1 : ℂ) else 0) := by
    refine ⟨1, by norm_num, 0, ?_⟩
    intro n hn
    by_cases hmem : n ∈ source.block i1 <;> simp [hmem]
  exact mtBlockChainCoefficientAF_polynomialDivisorBounded hindicator hchain

/-- Exact algebraic Type-I/II factorization of one signed triple box. -/
theorem mtSignedTripleBox_eq_typeI_II_factors
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 i3 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (eIndex kIndex : ℕ) :
    mtSignedBlockChainAdicBoxAF
        (mtHarmanTripleCellCoefficient
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i1)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i2)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i3))
        (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block chain
        z0 D delta eIndex kIndex =
      (mtMinimalGeometricTripleTypeI_II_FirstAF
          z0 D start hdelta hz0 hroot i2 i3 chain.length eIndex *
        mtMinimalGeometricTripleTypeI_II_SecondAF
          z0 D start hdelta hz0 hroot i1 chain) *
        mtUpperAdicOneAF delta kIndex := by
  let source := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    z0 D start delta z hdelta hz0 hroot
  have hpos2 : ∀ q ∈ source.block i2, 0 < q := by
    intro q hq
    exact (mem_ofMinimalGeometricSchedule_block_iff
      z0 D start hdelta hz0 hroot i2 q).mp hq |>.1.pos
  have hpos3 : ∀ q ∈ source.block i3, 0 < q := by
    intro q hq
    exact (mem_ofMinimalGeometricSchedule_block_iff
      z0 D start hdelta hz0 hroot i3 q).mp hq |>.1.pos
  simp only [mtSignedBlockChainAdicBoxAF, mtBlockChainAdicBoxAF,
    mtMinimalGeometricTripleTypeI_II_FirstAF,
    mtMinimalGeometricTripleTypeI_II_SecondAF,
    mtBlockChainLongAF, mtBlockChainCoefficientAF, List.toFinset_nil,
    mtPrimeBlockFamilyAF, Finset.prod_empty, mul_one]
  rw [mtCoefficientAF_tripleCell_eq_pairCell_mul_primeBlock
    (source.block i1) (source.block i2) (source.block i3) hpos2 hpos3]
  rw [mtCoefficientAF_primeBlockIndicator_eq, smul_mul_assoc, smul_mul_assoc]
  apply congrArg (fun H : ArithmeticFunction ℂ => ((-1 : ℂ) ^ chain.length) • H)
  ac_rfl

/-- Complete Type-I/II datum for one signed triple box. -/
def mtMinimalGeometricTripleBoxTypeI_II_Data
    {X Y epsilon : ℝ}
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 i3 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hchain : chain.Nodup) (eIndex kIndex : ℕ)
    (hfirstDilation : (1 + delta) ^ 3 ≤ 2)
    (hsecondDilation : (1 + delta) ^ (chain.length + 1) ≤ 2)
    (hsquare : mtMinimalGeometricTripleBoxTypeI_II_M1
        delta start i2 i3 eIndex ^ 2 *
      mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain ≤
        X ^ (1 - epsilon))
    (hM2le : mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain ≤
      X ^ (1 / 4 - epsilon))
    (hproduct : Y / 2 <
        mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex *
          mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain *
            mtUpperAdicScale delta kIndex ∧
      mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex *
          mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain *
            mtUpperAdicScale delta kIndex ≤ 4 * Y) :
    MTTypeI_II_PieceData X Y delta epsilon := by
  let F := mtMinimalGeometricTripleTypeI_II_FirstAF
    z0 D start hdelta hz0 hroot i2 i3 chain.length eIndex
  let G := mtMinimalGeometricTripleTypeI_II_SecondAF
    z0 D start hdelta hz0 hroot i1 chain
  exact mtTypeI_II_PieceDataOfSupported F G
    (mtMinimalGeometricTripleBoxTypeI_II_M1_pos hdelta start i2 i3 eIndex)
    (mtMinimalGeometricTripleBoxTypeI_II_M2_pos hdelta start i1 chain)
    (mtUpperAdicScale_pos hdelta kIndex)
    (by
      intro n hn
      exact (mtMinimalGeometricTripleTypeI_II_FirstAF_scaleSupported
        z0 D start hdelta hz0 hroot i2 i3 chain.length eIndex hfirstDilation) hn)
    (by
      intro n hn
      exact (mtMinimalGeometricTripleTypeI_II_SecondAF_scaleSupported
        z0 D start hdelta hz0 hroot i1 hchain hsecondDilation) hn)
    (mtMinimalGeometricTripleTypeI_II_FirstAF_polynomialDivisorBounded
      z0 D start hdelta hz0 hroot i2 i3 chain.length eIndex)
    (mtMinimalGeometricTripleTypeI_II_SecondAF_polynomialDivisorBounded
      z0 D start hdelta hz0 hroot i1 hchain)
    hsquare hM2le hproduct

/-- Constructed Type-I/II piece is exactly the original signed triple box. -/
theorem mtMinimalGeometricTripleBoxTypeI_II_Data_pieceAF_eq
    {X Y epsilon : ℝ}
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 i3 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hchain : chain.Nodup) (eIndex kIndex : ℕ)
    (hfirstDilation : (1 + delta) ^ 3 ≤ 2)
    (hsecondDilation : (1 + delta) ^ (chain.length + 1) ≤ 2)
    (hsquare : mtMinimalGeometricTripleBoxTypeI_II_M1
        delta start i2 i3 eIndex ^ 2 *
      mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain ≤
        X ^ (1 - epsilon))
    (hM2le : mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain ≤
      X ^ (1 / 4 - epsilon))
    (hproduct : Y / 2 <
        mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex *
          mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain *
            mtUpperAdicScale delta kIndex ∧
      mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex *
          mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain *
            mtUpperAdicScale delta kIndex ≤ 4 * Y) :
    (mtMinimalGeometricTripleBoxTypeI_II_Data z0 D start hdelta hz0 hroot
      i1 i2 i3 chain hchain eIndex kIndex hfirstDilation hsecondDilation
      hsquare hM2le hproduct).pieceAF =
      mtSignedBlockChainAdicBoxAF
        (mtHarmanTripleCellCoefficient
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i1)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i2)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i3))
        (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block chain
        z0 D delta eIndex kIndex := by
  let F := mtMinimalGeometricTripleTypeI_II_FirstAF
    z0 D start hdelta hz0 hroot i2 i3 chain.length eIndex
  let G := mtMinimalGeometricTripleTypeI_II_SecondAF
    z0 D start hdelta hz0 hroot i1 chain
  have hFsupport : MTRealScaleSupported F
      (mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex)
      (2 * mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex) := by
    intro n hn
    exact (mtMinimalGeometricTripleTypeI_II_FirstAF_scaleSupported
      z0 D start hdelta hz0 hroot i2 i3 chain.length eIndex hfirstDilation) hn
  have hGsupport : MTRealScaleSupported G
      (mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain)
      (2 * mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain) := by
    intro n hn
    exact (mtMinimalGeometricTripleTypeI_II_SecondAF_scaleSupported
      z0 D start hdelta hz0 hroot i1 hchain hsecondDilation) hn
  rw [mtMinimalGeometricTripleBoxTypeI_II_Data]
  change (mtRealIntervalAF (fun n => F n)
      (mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex)
      (2 * mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex) *
    mtRealIntervalAF (fun n => G n)
      (mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain)
      (2 * mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain)) *
    mtRealIntervalAF (fun _ => 1)
      (mtUpperAdicScale delta kIndex)
      ((1 + delta) * mtUpperAdicScale delta kIndex) = _
  rw [mtRealIntervalAF_coe_eq_of_scaleSupported hFsupport,
    mtRealIntervalAF_coe_eq_of_scaleSupported hGsupport]
  change (F * G) * mtUpperAdicOneAF delta kIndex = _
  exact (mtSignedTripleBox_eq_typeI_II_factors
    z0 D start hdelta hz0 hroot i1 i2 i3 chain eIndex kIndex).symm

end

end RHTower.Sieve

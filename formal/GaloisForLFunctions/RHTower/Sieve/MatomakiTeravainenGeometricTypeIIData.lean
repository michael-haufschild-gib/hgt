import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenSelectedPrimeProduct

/-!
# Exact Type-II data from a minimal geometric block selection

A nonempty selected subset of the minimal geometric schedule supplies every structural field in
Proposition 2.2(iii): literal block intervals, equation-(2.11) coefficient, range for the selected
product, and exact natural index count.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- The interval restriction in a complete Type-II datum does not change its prime coefficient. -/
theorem MTTypeIIPieceData.primeIntervalAF_eq_coefficientAF
    {X Y z0 z delta epsilon : ℝ}
    (data : MTTypeIIPieceData X Y z0 z delta epsilon) :
    mtRealIntervalAF (mtTypeIIPrimeCoefficient data.indices data.block)
        data.M₁ ((1 + delta) ^ data.indices.card * data.M₁) =
      mtCoefficientAF (mtTypeIIPrimeCoefficient data.indices data.block) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [mtRealIntervalAF, mtCoefficientAF]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    rw [mtRealIntervalAF_apply_of_pos _ _ _ hnPos,
      mtCoefficientAF_apply_of_pos _ hnPos]
    by_cases hcoeff : mtTypeIIPrimeCoefficient data.indices data.block n = 0
    · simp [hcoeff]
    · have hsupport := data.primeCoefficient_support hcoeff
      simp [hsupport]

/-- Exact Type-II datum attached to one selected subset of a minimal geometric schedule. -/
def mtMinimalGeometricTypeIIData
    {X Y z0 z delta epsilon M2 : ℝ}
    (z0Nat D start : ℕ) (hdelta : 0 < delta)
    (hz0Nat : (z0Nat : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (S : Finset (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hS : S.Nonempty)
    (hz0pos : 0 < z0)
    (hz0level : z0 ≤ mtGeometricLevel delta start 0)
    (hR : S.card ≤ Nat.floor (Real.log z / Real.log z0))
    (beta : ℕ → ℂ) (hM2 : 0 < M2)
    (hbeta : MTPolynomialDivisorBounded beta)
    (hM1 : X ^ (epsilon / 2) ≤
        ∏ i ∈ S, mtGeometricLevel delta start i.1 ∧
      (∏ i ∈ S, mtGeometricLevel delta start i.1) ≤ z)
    (hproduct : Y / 2 <
        (∏ i ∈ S, mtGeometricLevel delta start i.1) * M2 ∧
      (∏ i ∈ S, mtGeometricLevel delta start i.1) * M2 ≤ 4 * Y) :
    MTTypeIIPieceData X Y z0 z delta epsilon := by
  let source := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    z0Nat D start delta z hdelta hz0Nat hroot
  let Qfin : Fin (mtMinimalGeometricDepth delta start z hdelta) → ℝ :=
    fun i => mtGeometricLevel delta start i.1
  let blockNat : ℕ → Finset ℕ :=
    mtFinBlockToNat (mtEnumeratedBlock source.block S)
  let Qnat : ℕ → ℝ := mtEnumeratedScaleToNat Qfin S
  refine
    { indices := Finset.range S.card
      R_pos := by simpa using hS.card_pos
      R_le := by simpa using hR
      Q := Qnat
      block := blockNat
      M₁ := ∏ i ∈ S, mtGeometricLevel delta start i.1
      M₂ := M2
      β := beta
      z₀_pos := hz0pos
      δ_nonneg := hdelta.le
      Q_mem := ?_
      block_eq := ?_
      M₁_eq := ?_
      M₁_mem := hM1
      M₂_pos := hM2
      β_divisorBounded := hbeta
      product_mem := hproduct }
  · intro i hi
    have hiLt : i < S.card := Finset.mem_range.mp hi
    let k : Fin S.card := ⟨i, hiLt⟩
    have hscale := mtMinimalGeometricSchedule_scale_mem hdelta start
      (mtFinsetEnumeration S k)
    have hQi : Qnat i = mtGeometricLevel delta start (mtFinsetEnumeration S k).1 := by
      simp [Qnat, Qfin, mtEnumeratedScaleToNat, mtEnumeratedScale,
        mtFinsetEnumeration, hiLt, k]
    rw [hQi]
    constructor
    · exact hz0level.trans hscale.1
    · exact hscale.2
  · intro i hi q
    have hiLt : i < S.card := Finset.mem_range.mp hi
    let k : Fin S.card := ⟨i, hiLt⟩
    have hblock := mem_ofMinimalGeometricSchedule_block_iff
      z0Nat D start hdelta hz0Nat hroot (mtFinsetEnumeration S k) q
    simpa [source, blockNat, Qnat, Qfin, mtEnumeratedBlock,
      mtEnumeratedScale, mtFinBlockToNat, mtEnumeratedScaleToNat, hiLt, k,
      and_assoc] using hblock
  · rw [prod_rangeSubtype_mtEnumeratedScaleToNat Qfin S]

/-- The selected datum's first factor is exactly the selected source block convolution. -/
theorem mtMinimalGeometricTypeIIData_pieceAF_eq
    {X Y z0 z delta epsilon M2 : ℝ}
    (z0Nat D start : ℕ) (hdelta : 0 < delta)
    (hz0Nat : (z0Nat : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (S : Finset (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hS : S.Nonempty)
    (hz0pos : 0 < z0)
    (hz0level : z0 ≤ mtGeometricLevel delta start 0)
    (hR : S.card ≤ Nat.floor (Real.log z / Real.log z0))
    (beta : ℕ → ℂ) (hM2 : 0 < M2)
    (hbeta : MTPolynomialDivisorBounded beta)
    (hM1 : X ^ (epsilon / 2) ≤
        ∏ i ∈ S, mtGeometricLevel delta start i.1 ∧
      (∏ i ∈ S, mtGeometricLevel delta start i.1) ≤ z)
    (hproduct : Y / 2 <
        (∏ i ∈ S, mtGeometricLevel delta start i.1) * M2 ∧
      (∏ i ∈ S, mtGeometricLevel delta start i.1) * M2 ≤ 4 * Y) :
    (mtMinimalGeometricTypeIIData z0Nat D start hdelta hz0Nat hroot S hS
      hz0pos hz0level hR beta hM2 hbeta hM1 hproduct).pieceAF =
      mtPrimeBlockFamilyAF
          (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0Nat D start delta z hdelta hz0Nat hroot).block S *
        mtRealIntervalAF beta M2 (2 * M2) := by
  let data := mtMinimalGeometricTypeIIData z0Nat D start hdelta hz0Nat hroot S hS
    hz0pos hz0level hR beta hM2 hbeta hM1 hproduct
  rw [MTTypeIIPieceData.pieceAF, mtTypeIIPieceAF,
    data.primeIntervalAF_eq_coefficientAF]
  change mtCoefficientAF
      (mtTypeIIPrimeCoefficient (Finset.range S.card)
        (mtFinBlockToNat (mtEnumeratedBlock
          (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0Nat D start delta z hdelta hz0Nat hroot).block S))) *
      mtRealIntervalAF beta M2 (2 * M2) = _
  rw [← mtPrimeBlockFamilyAF_eq_enumeratedTypeIIPrimeCoefficientAF]
  intro i hi m hm
  exact (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    z0Nat D start delta z hdelta hz0Nat hroot).block_prime i m hm |>.pos

end

end RHTower.Sieve

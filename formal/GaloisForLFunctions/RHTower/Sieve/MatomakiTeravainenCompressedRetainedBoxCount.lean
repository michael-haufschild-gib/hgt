import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenCompressedRetainedBoxFamily
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMainLayerPaperCount

/-!
# Count of the compressed retained-box family

The recursive schedule stops at the literal real root, so its formal length is logarithmic in the
same fixed-base adic grid.  Combined with active outer cells and both upper-closed adic factors,
this gives the finite Cartesian count used by Proposition 2.2.
-/

namespace RHTower.Sieve

open Finset Filter

noncomputable section

/-- The tagged union of active chains costs at most the sum of its depth fibres. -/
theorem card_mtAllActiveBlockChains_le_sum {t : ℕ}
    (data : MTFiniteIterationSourceData t) (maxDepth : ℕ) (j : Fin (t + 1)) :
    (mtAllActiveBlockChains data maxDepth j).card ≤
      ∑ depth ∈ Finset.range (maxDepth + 1),
        (mtActiveBlockChains data.block depth j).card := by
  unfold mtAllActiveBlockChains
  calc
    _ ≤ ∑ depth ∈ Finset.range (maxDepth + 1),
        ((mtActiveBlockChains data.block depth j).image
          fun chain => (depth, chain)).card := Finset.card_biUnion_le
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro depth hdepth
      exact Finset.card_image_le

/-- Minimal exact geometric depth fits below one full fixed-base adic grid. -/
theorem mtMinimalGeometricDepth_le_adicIndex_add_one
    {delta recRoot X : ℝ} (hdelta : 0 < delta) (start : ℕ)
    (hX : 1 ≤ X) (hrootX : recRoot ≤ X) :
    mtMinimalGeometricDepth delta start recRoot hdelta ≤
      adicIndex delta 1 X + 1 := by
  have hadic := adicIndex_block hdelta (by norm_num : (0 : ℝ) < 1) hX
  have hpow : (1 + delta) ^ (adicIndex delta 1 X + 1) ≤
      mtGeometricLevel delta start (adicIndex delta 1 X + 1) := by
    rw [mtGeometricLevel]
    exact pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + delta) (by omega)
  have hpow' : 1 * (1 + delta) ^ (adicIndex delta 1 X + 1) ≤
      mtGeometricLevel delta start (adicIndex delta 1 X + 1) := by
    simpa using hpow
  have hlevel : recRoot ≤
      mtGeometricLevel delta start (adicIndex delta 1 X + 1) :=
    hrootX.trans (hadic.2.le.trans hpow')
  unfold mtMinimalGeometricDepth
  exact Nat.find_min' _ hlevel

/-- An arbitrary finite iteration schedule has at most its formal length many active blocks. -/
theorem card_mtActiveBlockIndices_le_length {t : ℕ} (block : Fin t → Finset ℕ) :
    (mtActiveBlockIndices block).card ≤ t := by
  calc
    (mtActiveBlockIndices block).card ≤ (Finset.univ : Finset (Fin t)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = t := by simp

/-- The upper-closed minimal-power index is at most the usual lower-closed adic index plus one. -/
theorem mtUpperAdicIndex_le_adicIndex_add_one
    {delta : ℝ} (hdelta : 0 < delta) {m : ℕ} (hm : 1 ≤ m) :
    mtUpperAdicIndex delta m ≤ adicIndex delta 1 (m : ℝ) + 1 := by
  by_cases hzero : mtUpperAdicIndex delta m = 0
  · omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hzero
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  have hlower := (mtUpperAdicIndex_block hdelta hmpos).1
  rw [hk] at hlower
  have hlower' : (1 + delta) ^ k < (m : ℝ) := by
    simpa [mtUpperAdicScale] using hlower
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hadic := (adicIndex_block hdelta (by norm_num : (0 : ℝ) < 1) hmReal).2
  rw [hk]
  by_contra hnot
  have hindex : adicIndex delta 1 (m : ℝ) + 1 ≤ k := by omega
  have hpow : (1 + delta) ^ (adicIndex delta 1 (m : ℝ) + 1) ≤
      (1 + delta) ^ k :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + delta) hindex
  linarith

/-- A point strictly below the `K`th adic power has adic index strictly below `K`. -/
theorem adicIndex_lt_of_lt_one_add_pow
    {delta q : ℝ} (hdelta : 0 < delta) (hq : 1 ≤ q) {K : ℕ}
    (hqK : q < (1 + delta) ^ K) :
    adicIndex delta 1 q < K := by
  have hlower := (adicIndex_block hdelta (by norm_num : (0 : ℝ) < 1) hq).1
  by_contra hnot
  have hK : K ≤ adicIndex delta 1 q := by omega
  have hpow : (1 + delta) ^ K ≤ (1 + delta) ^ adicIndex delta 1 q :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + delta) hK
  linarith

/-- Every upper-closed grid through `2X` costs at most three copies of the adic grid through `X`. -/
theorem mtUpperAdicIndex_add_one_le_three_mul_adicIndex_add_one
    {delta X : ℝ} (hdelta : 0 < delta) (hX : 2 ≤ X)
    {m : ℕ} (hm : 1 ≤ m) (hmX : (m : ℝ) ≤ 2 * X) :
    mtUpperAdicIndex delta m + 1 ≤ 3 * (adicIndex delta 1 X + 1) := by
  have hXOne : 1 ≤ X := by linarith
  have hadicX := (adicIndex_block hdelta (by norm_num : (0 : ℝ) < 1) hXOne).2
  let a := adicIndex delta 1 X
  have hbasePos : 0 < (1 + delta) ^ (a + 1) := by positivity
  have hsq : X ^ (2 : ℕ) < ((1 + delta) ^ (a + 1)) ^ (2 : ℕ) := by
    dsimp [a] at hbasePos ⊢
    nlinarith [sq_nonneg (X - (1 + delta) ^ (adicIndex delta 1 X + 1))]
  have hpow : ((1 + delta) ^ (a + 1)) ^ (2 : ℕ) =
      (1 + delta) ^ (2 * (a + 1)) := by
    rw [← pow_mul]
    congr 1
    omega
  have hmPow : (m : ℝ) < ((1 + delta) ^ (a + 1)) ^ (2 : ℕ) := by
    have htwoX : 2 * X ≤ X ^ (2 : ℕ) := by nlinarith [sq_nonneg (X - 2)]
    exact (hmX.trans htwoX).trans_lt hsq
  have hmOne : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hadicM : adicIndex delta 1 (m : ℝ) < 2 * (a + 1) := by
    apply adicIndex_lt_of_lt_one_add_pow hdelta hmOne
    rw [← hpow]
    exact hmPow
  have hupper := mtUpperAdicIndex_le_adicIndex_add_one hdelta hm
  dsimp [a] at hadicM ⊢
  omega

/-- One extra grid slot still fits the eighth-square block envelope. -/
theorem eventually_cast_adicIndex_paperWidth_one_add_two_le_exp_eighth_sq
    (A : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ((adicIndex (mtPaperWidth A X) 1 X + 2 : ℕ) : ℝ) ≤
        Real.exp ((Real.log (Real.log X)) ^ (2 : ℕ) / 8) := by
  have hlarge := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
    (8 * (((10 * A + 2 : ℕ) : ℝ)) + 3)
  filter_upwards [
    eventually_cast_adicIndex_paperWidth_one_add_one_le_three_mul_log_pow A,
    hlarge, Filter.eventually_ge_atTop (Real.exp 1)] with X hgrid hll hX
  change 8 * (((10 * A + 2 : ℕ) : ℝ)) + 3 ≤ Real.log (Real.log X) at hll
  let u := Real.log (Real.log X)
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hlogOne : (1 : ℝ) ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hlogPos : 0 < Real.log X := zero_lt_one.trans_le hlogOne
  have hlogEq : Real.log X = Real.exp u := by
    dsimp [u]
    exact (Real.exp_log hlogPos).symm
  have hlogFour : (4 : ℝ) ≤ Real.log X := by
    rw [hlogEq]
    calc
      (4 : ℝ) ≤ u + 1 := by dsimp [u] at hll ⊢; linarith
      _ ≤ Real.exp u := Real.add_one_le_exp u
  have hexponent : (((10 * A + 2 : ℕ) : ℝ)) * u ≤ u ^ (2 : ℕ) / 8 := by
    have huLower : 8 * (((10 * A + 2 : ℕ) : ℝ)) ≤ u := by
      dsimp [u] at hll ⊢
      linarith
    have := mul_le_mul_of_nonneg_right huLower hu
    nlinarith
  have hpowOne : (1 : ℝ) ≤ (Real.log X) ^ (10 * A + 1) :=
    one_le_pow₀ hlogOne
  calc
    ((adicIndex (mtPaperWidth A X) 1 X + 2 : ℕ) : ℝ) =
        ((adicIndex (mtPaperWidth A X) 1 X + 1 : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    _ ≤ 3 * (Real.log X) ^ (10 * A + 1) + 1 := by gcongr
    _ ≤ 4 * (Real.log X) ^ (10 * A + 1) := by nlinarith
    _ ≤ (Real.log X) ^ (10 * A + 2) := by
      calc
        4 * (Real.log X) ^ (10 * A + 1) ≤
            Real.log X * (Real.log X) ^ (10 * A + 1) :=
          mul_le_mul_of_nonneg_right hlogFour
            (pow_nonneg hlogPos.le (10 * A + 1))
        _ = (Real.log X) ^ (10 * A + 2) := by
          rw [pow_succ]
          ring
    _ = Real.exp ((((10 * A + 2 : ℕ) : ℝ)) * u) := by
      rw [hlogEq, Real.exp_nat_mul]
    _ ≤ Real.exp (u ^ (2 : ℕ) / 8) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp ((Real.log (Real.log X)) ^ (2 : ℕ) / 8) := rfl

/-- Minimal-root recursive chains use only half the proposition's fifth-power exponent. -/
theorem eventually_sum_card_mtActiveBlockChains_minimalGeometric_le_exp_half_fifth
    (A : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ (start : ℕ) (recRoot : ℝ)
        (hdelta : 0 < mtPaperWidth A X),
      1 ≤ X → recRoot ≤ X →
      ∀ (data : MTFiniteIterationSourceData
          (mtMinimalGeometricDepth (mtPaperWidth A X) start recRoot hdelta))
        (maxDepth : ℕ)
        (j : Fin (mtMinimalGeometricDepth
          (mtPaperWidth A X) start recRoot hdelta + 1)),
      (maxDepth : ℝ) ≤ 2 * (Real.log (Real.log X)) ^ (3 : ℕ) →
      ((∑ depth ∈ Finset.range (maxDepth + 1),
          (mtActiveBlockChains data.block depth j).card : ℕ) : ℝ) ≤
        Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ) / 2) := by
  have hll := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 3
  filter_upwards [
    eventually_cast_adicIndex_paperWidth_one_add_two_le_exp_eighth_sq A,
    hll] with X hgrid hllX
  intro start recRoot hdelta hX hrootX data maxDepth j hdepth
  apply cast_sum_card_mtActiveBlockChains_le_exp_half_fifth_of_bounds
    data.block j hllX hdepth
  have hactiveNat : (mtActiveBlockIndices data.block).card + 1 ≤
      adicIndex (mtPaperWidth A X) 1 X + 2 := by
    calc
      (mtActiveBlockIndices data.block).card + 1 ≤
          mtMinimalGeometricDepth (mtPaperWidth A X) start recRoot hdelta + 1 := by
        exact Nat.add_le_add_right (card_mtActiveBlockIndices_le_length data.block) 1
      _ ≤ adicIndex (mtPaperWidth A X) 1 X + 2 := by
        have := mtMinimalGeometricDepth_le_adicIndex_add_one hdelta start hX hrootX
        omega
  exact (by exact_mod_cast hactiveNat :
      (((mtActiveBlockIndices data.block).card + 1 : ℕ) : ℝ) ≤
        ((adicIndex (mtPaperWidth A X) 1 X + 2 : ℕ) : ℝ)).trans hgrid

/-- Exact finite family count reduced to outer active blocks, recursive chains, and two adic grids. -/
theorem card_mtHarmanCompressedRetainedBoxIndexSet_le_activeGrids
    {outerQ outerD recDepth : ℕ} (outerActive : Finset (Fin outerQ))
    (endpointQ endpointD : ℕ → ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData recDepth) (maxDepth : ℕ)
    (j : Fin (recDepth + 1)) (delta : ℝ) (N recStart : ℕ) (Y : ℝ) :
    (mtHarmanCompressedRetainedBoxIndexSet (outerD := outerD)
      outerActive endpointQ endpointD E
      data maxDepth j delta N recStart Y).card ≤
      (1 + outerActive.card +
          (mtActiveBlockIndices
            (mtAdjacentPrimeBlock (t := outerD) endpointD)).card ^ (2 : ℕ) +
          (mtActiveBlockIndices
            (mtAdjacentPrimeBlock (t := outerD) endpointD)).card ^ (3 : ℕ)) *
        (∑ depth ∈ Finset.range (maxDepth + 1),
          (mtActiveBlockChains data.block depth j).card) *
        (mtUpperAdicIndex delta data.D + 1) *
        (mtUpperAdicIndex delta N + 1) := by
  calc
    _ ≤ (1 + outerActive.card +
          (mtHarmanActiveGoodPairCells (t := outerD) endpointD E).card +
          (mtHarmanActiveGoodTripleCells (t := outerD) endpointD E).card) *
        (mtAllActiveBlockChains data maxDepth j).card *
        (mtUpperAdicIndex delta data.D + 1) *
        (mtUpperAdicIndex delta N + 1) :=
      card_mtHarmanCompressedRetainedBoxIndexSet_le outerActive endpointQ endpointD E
        data maxDepth j delta N recStart Y
    _ ≤ _ := by
      gcongr
      · exact card_mtHarmanActiveGoodPairCells_le endpointD E
      · exact card_mtHarmanActiveGoodTripleCells_le endpointD E
      · exact card_mtAllActiveBlockChains_le_sum data maxDepth j

/-- Literal compressed retained family satisfies Proposition 2.2's stated exponential budget. -/
theorem eventually_card_mtHarmanCompressedRetainedBoxIndexSet_le_exp_log_log_fifth
    (A : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ (Qouter Douter : ℕ),
      mtLowerCutoffNat X ≤ Qouter → (Qouter : ℝ) ≤ X →
      mtLowerCutoffNat X ≤ Douter → (Douter : ℝ) ≤ X →
      ∀ (E : ℝ) (start : ℕ) (recRoot : ℝ)
        (hdelta : 0 < mtPaperWidth A X),
      2 ≤ X → recRoot ≤ X →
      ∀ (data : MTFiniteIterationSourceData
          (mtMinimalGeometricDepth (mtPaperWidth A X) start recRoot hdelta)),
      1 ≤ data.D → (data.D : ℝ) ≤ 2 * X →
      ∀ (maxDepth : ℕ)
        (j : Fin (mtMinimalGeometricDepth
          (mtPaperWidth A X) start recRoot hdelta + 1)),
      (maxDepth : ℝ) ≤ 2 * (Real.log (Real.log X)) ^ (3 : ℕ) →
      ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ 2 * X →
      ∀ recStart : ℕ, ∀ Y : ℝ,
      (((mtHarmanCompressedRetainedBoxIndexSet
        (outerD := Douter - mtLowerCutoffNat X)
        (mtPaperAlignedActiveBlockIndices
          (Qouter - mtLowerCutoffNat X) (mtLowerCutoffNat X) Qouter
            (mtPaperWidth A X))
        (mtPaperAlignedEndpoint (mtLowerCutoffNat X) Qouter (mtPaperWidth A X))
        (mtPaperAlignedEndpoint (mtLowerCutoffNat X) Douter (mtPaperWidth A X))
        E data maxDepth j (mtPaperWidth A X) N recStart Y).card : ℕ) : ℝ) ≤
        Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ)) := by
  let K := 10 * A + 1
  filter_upwards [
    eventually_cast_card_mtPaperAlignedActiveBlockIndices_le_six_mul_log_pow A,
    eventually_sum_card_mtActiveBlockChains_minimalGeometric_le_exp_half_fifth A,
    eventually_cast_adicIndex_paperWidth_one_add_one_le_three_mul_log_pow A,
    eventually_const_mul_log_pow_le_exp_half_log_log_fifth
      (20979 : ℝ) (5 * K) (by norm_num),
    Filter.eventually_ge_atTop (Real.exp 1)]
    with X hactiveX hchainsX hgridX houterX hXexp
  intro Qouter Douter hQ hQX hD hDX E start recRoot hdelta hX hrootX
    data hdataD hdataDX maxDepth j hdepth N hN hNX recStart Y
  let endpointD :=
    mtPaperAlignedEndpoint (mtLowerCutoffNat X) Douter (mtPaperWidth A X)
  let activeQ := mtPaperAlignedActiveBlockIndices
    (Qouter - mtLowerCutoffNat X) (mtLowerCutoffNat X) Qouter (mtPaperWidth A X)
  let activeD := mtActiveBlockIndices
    (mtAdjacentPrimeBlock (t := Douter - mtLowerCutoffNat X) endpointD)
  let chains := ∑ depth ∈ Finset.range (maxDepth + 1),
    (mtActiveBlockChains data.block depth j).card
  let L := (Real.log X) ^ K
  have hlogOne : (1 : ℝ) ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hXexp
    simpa only [Real.log_exp] using hmono
  have hLOne : (1 : ℝ) ≤ L := by
    exact one_le_pow₀ hlogOne
  have hactiveQ : (activeQ.card : ℝ) ≤ 6 * L := by
    dsimp [activeQ, L, K]
    exact hactiveX Qouter hQ hQX
  have hactiveD : (activeD.card : ℝ) ≤ 6 * L := by
    dsimp [activeD, endpointD, L, K]
    rw [mtActiveBlockIndices_paperAligned]
    exact hactiveX Douter hD hDX
  have hchains : (chains : ℝ) ≤
      Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ) / 2) := by
    dsimp [chains]
    exact hchainsX start recRoot hdelta (by linarith) hrootX
      data maxDepth j hdepth
  have hupperD : ((mtUpperAdicIndex (mtPaperWidth A X) data.D + 1 : ℕ) : ℝ) ≤
      9 * L := by
    have hnat := mtUpperAdicIndex_add_one_le_three_mul_adicIndex_add_one
      hdelta hX hdataD hdataDX
    have hcast : ((mtUpperAdicIndex (mtPaperWidth A X) data.D + 1 : ℕ) : ℝ) ≤
        3 * ((adicIndex (mtPaperWidth A X) 1 X + 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    calc
      _ ≤ 3 * ((adicIndex (mtPaperWidth A X) 1 X + 1 : ℕ) : ℝ) := hcast
      _ ≤ 3 * (3 * (Real.log X) ^ (10 * A + 1)) := by gcongr
      _ = 9 * L := by simp [L, K]; ring
  have hupperN : ((mtUpperAdicIndex (mtPaperWidth A X) N + 1 : ℕ) : ℝ) ≤
      9 * L := by
    have hnat := mtUpperAdicIndex_add_one_le_three_mul_adicIndex_add_one
      hdelta hX hN hNX
    have hcast : ((mtUpperAdicIndex (mtPaperWidth A X) N + 1 : ℕ) : ℝ) ≤
        3 * ((adicIndex (mtPaperWidth A X) 1 X + 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    calc
      _ ≤ 3 * ((adicIndex (mtPaperWidth A X) 1 X + 1 : ℕ) : ℝ) := hcast
      _ ≤ 3 * (3 * (Real.log X) ^ (10 * A + 1)) := by gcongr
      _ = 9 * L := by simp [L, K]; ring
  have hactiveD2 : (activeD.card : ℝ) ^ (2 : ℕ) ≤ (6 * L) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hactiveD 2
  have hactiveD3 : (activeD.card : ℝ) ^ (3 : ℕ) ≤ (6 * L) ^ (3 : ℕ) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hactiveD 3
  have hLleCube : L ≤ L ^ (3 : ℕ) := by
    simpa using pow_le_pow_right₀ hLOne (by omega : 1 ≤ 3)
  have hLSqleCube : L ^ (2 : ℕ) ≤ L ^ (3 : ℕ) :=
    pow_le_pow_right₀ hLOne (by omega : 2 ≤ 3)
  have hOneLeCube : (1 : ℝ) ≤ L ^ (3 : ℕ) := one_le_pow₀ hLOne
  have houterCells :
      (((1 + activeQ.card + activeD.card ^ (2 : ℕ) + activeD.card ^ (3 : ℕ) : ℕ) : ℕ) : ℝ) ≤
        259 * L ^ (3 : ℕ) := by
    push_cast
    calc
      1 + (activeQ.card : ℝ) + (activeD.card : ℝ) ^ (2 : ℕ) +
          (activeD.card : ℝ) ^ (3 : ℕ) ≤
          1 + 6 * L + (6 * L) ^ (2 : ℕ) + (6 * L) ^ (3 : ℕ) := by gcongr
      _ ≤ 259 * L ^ (3 : ℕ) := by
        nlinarith [hLleCube, hLSqleCube, hOneLeCube]
  have houter :
      (((1 + activeQ.card + activeD.card ^ (2 : ℕ) + activeD.card ^ (3 : ℕ) : ℕ) : ℕ) : ℝ) *
          ((mtUpperAdicIndex (mtPaperWidth A X) data.D + 1 : ℕ) : ℝ) *
          ((mtUpperAdicIndex (mtPaperWidth A X) N + 1 : ℕ) : ℝ) ≤
        Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ) / 2) := by
    calc
      _ ≤ (259 * L ^ (3 : ℕ)) * (9 * L) * (9 * L) := by gcongr
      _ = 20979 * (Real.log X) ^ (5 * K) := by
        have hpow5 : (Real.log X) ^ (5 * K) = L ^ (5 : ℕ) := by
          dsimp [L]
          rw [Nat.mul_comm 5 K, pow_mul]
        rw [hpow5]
        ring
      _ ≤ Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ) / 2) := houterX
  have hcountNat := card_mtHarmanCompressedRetainedBoxIndexSet_le_activeGrids
    (outerD := Douter - mtLowerCutoffNat X) activeQ
    (mtPaperAlignedEndpoint (mtLowerCutoffNat X) Qouter (mtPaperWidth A X))
    endpointD E data maxDepth j (mtPaperWidth A X) N recStart Y
  have hcount :
      (((mtHarmanCompressedRetainedBoxIndexSet
        (outerD := Douter - mtLowerCutoffNat X) activeQ
        (mtPaperAlignedEndpoint (mtLowerCutoffNat X) Qouter (mtPaperWidth A X))
        endpointD E data maxDepth j (mtPaperWidth A X) N recStart Y).card : ℕ) : ℝ) ≤
      (((1 + activeQ.card + activeD.card ^ (2 : ℕ) + activeD.card ^ (3 : ℕ) : ℕ) : ℕ) : ℝ) *
        (chains : ℝ) *
        ((mtUpperAdicIndex (mtPaperWidth A X) data.D + 1 : ℕ) : ℝ) *
        ((mtUpperAdicIndex (mtPaperWidth A X) N + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcountNat
  calc
    _ ≤ (((1 + activeQ.card + activeD.card ^ (2 : ℕ) + activeD.card ^ (3 : ℕ) : ℕ) : ℕ) : ℝ) *
        (chains : ℝ) *
        ((mtUpperAdicIndex (mtPaperWidth A X) data.D + 1 : ℕ) : ℝ) *
        ((mtUpperAdicIndex (mtPaperWidth A X) N + 1 : ℕ) : ℝ) := hcount
    _ = ((((1 + activeQ.card + activeD.card ^ (2 : ℕ) + activeD.card ^ (3 : ℕ) : ℕ) : ℕ) : ℝ) *
          ((mtUpperAdicIndex (mtPaperWidth A X) data.D + 1 : ℕ) : ℝ) *
          ((mtUpperAdicIndex (mtPaperWidth A X) N + 1 : ℕ) : ℝ)) *
        (chains : ℝ) := by ring
    _ ≤ Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ) / 2) *
        Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ) / 2) :=
      mul_le_mul houter hchains (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

end

end RHTower.Sieve

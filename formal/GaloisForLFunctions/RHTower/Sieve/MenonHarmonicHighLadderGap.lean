import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicLadderError
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# High-ladder endpoint-gap counting

The crude global ladder estimate pays one rounding unit for every prime.  Above a cutoff `U` with
`U² > B₀`, every cofactor is smaller than every prime.  Swapping the order of summation then shows
that, for each fixed cofactor `m`, gap primes lie in only two thin endpoint intervals, around
`A₀ / m` and `B₀ / m`.  This module formalizes that exact reindexing and its harmonic cardinality
bound.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Ladder indices from step `J` through step `L - 1`. -/
def ladderIndexIco (P : Finset ℕ) (Q eta : ℝ) (J L : ℕ) :
    Finset ((_ : ℕ) × ℕ) :=
  (Finset.Ico J L).sigma (fun j => geomBlock P Q (1 + eta) j)

/-- Flattened high-ladder gap pairs `((step, prime), cofactor)`. -/
def ladderGapPairsIco (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta : ℝ) (J L : ℕ) :
    Finset ((_ : ((_ : ℕ) × ℕ)) × ℕ) :=
  (ladderIndexIco P Q eta J L).sigma (ladderGapSetAt A₀ B₀ Q eta)

/-- The two endpoint windows which can contain a gap prime for fixed cofactor `m`. -/
def ladderEndpointPrimeWindow (A₀ B₀ m : ℕ) (eta : ℝ) : Finset ℕ :=
  Finset.Icc
      ⌊(A₀ : ℝ) / ((m : ℝ) * (1 + eta))⌋₊
      ⌈(A₀ : ℝ) / (m : ℝ)⌉₊ ∪
    Finset.Icc
      ⌊(B₀ : ℝ) / (m : ℝ)⌋₊
      ⌈(B₀ : ℝ) * (1 + eta) / (m : ℝ)⌉₊

private theorem card_floor_ceil_Icc_le {u v : ℝ} (hv : 0 ≤ v) (huv : u ≤ v) :
    ((Finset.Icc ⌊u⌋₊ ⌈v⌉₊).card : ℝ) ≤ v - u + 3 := by
  have hfloor : u - 1 ≤ (⌊u⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one u
    linarith
  have hceil : (⌈v⌉₊ : ℝ) ≤ v + 1 := (Nat.ceil_lt_add_one hv).le
  have h := card_Icc_cast_le hfloor hceil (by linarith)
  convert h using 1 <;> ring

/-- Each fixed cofactor sees only the two relative-`eta` endpoint windows. -/
theorem card_ladderEndpointPrimeWindow_le
    (A₀ B₀ m : ℕ) {eta : ℝ} (heta : 0 ≤ eta) (hm : 0 < m) :
    ((ladderEndpointPrimeWindow A₀ B₀ m eta).card : ℝ) ≤
      ((A₀ : ℝ) + (B₀ : ℝ)) * eta / (m : ℝ) + 6 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hr : (0 : ℝ) < 1 + eta := by linarith
  have hA0 : (0 : ℝ) ≤ (A₀ : ℝ) := Nat.cast_nonneg A₀
  have hB0 : (0 : ℝ) ≤ (B₀ : ℝ) := Nat.cast_nonneg B₀
  have hlowMono : (A₀ : ℝ) / ((m : ℝ) * (1 + eta)) ≤
      (A₀ : ℝ) / (m : ℝ) := by
    exact div_le_div_of_nonneg_left hA0 hmR
      (by nlinarith [mul_nonneg hmR.le heta])
  have hhighMono : (B₀ : ℝ) / (m : ℝ) ≤
      (B₀ : ℝ) * (1 + eta) / (m : ℝ) := by
    exact div_le_div_of_nonneg_right
      (by nlinarith [mul_nonneg hB0 heta]) hmR.le
  have hlow := card_floor_ceil_Icc_le
    (div_nonneg hA0 hmR.le) hlowMono
  have hhigh := card_floor_ceil_Icc_le
    (div_nonneg (mul_nonneg hB0 hr.le) hmR.le) hhighMono
  have hunion := Finset.card_union_le
    (Finset.Icc ⌊(A₀ : ℝ) / ((m : ℝ) * (1 + eta))⌋₊
      ⌈(A₀ : ℝ) / (m : ℝ)⌉₊)
    (Finset.Icc ⌊(B₀ : ℝ) / (m : ℝ)⌋₊
      ⌈(B₀ : ℝ) * (1 + eta) / (m : ℝ)⌉₊)
  have hlowWidth : (A₀ : ℝ) / (m : ℝ) -
      (A₀ : ℝ) / ((m : ℝ) * (1 + eta)) ≤
      (A₀ : ℝ) * eta / (m : ℝ) := by
    field_simp
    nlinarith [mul_nonneg hA0 heta]
  have hhighWidth : (B₀ : ℝ) * (1 + eta) / (m : ℝ) -
      (B₀ : ℝ) / (m : ℝ) = (B₀ : ℝ) * eta / (m : ℝ) := by ring
  rw [ladderEndpointPrimeWindow]
  have hunionR : ((Finset.Icc
        ⌊(A₀ : ℝ) / ((m : ℝ) * (1 + eta))⌋₊
        ⌈(A₀ : ℝ) / (m : ℝ)⌉₊ ∪
      Finset.Icc
        ⌊(B₀ : ℝ) / (m : ℝ)⌋₊
        ⌈(B₀ : ℝ) * (1 + eta) / (m : ℝ)⌉₊).card : ℝ) ≤
      ((Finset.Icc
        ⌊(A₀ : ℝ) / ((m : ℝ) * (1 + eta))⌋₊
        ⌈(A₀ : ℝ) / (m : ℝ)⌉₊).card : ℝ) +
      ((Finset.Icc
        ⌊(B₀ : ℝ) / (m : ℝ)⌋₊
        ⌈(B₀ : ℝ) * (1 + eta) / (m : ℝ)⌉₊).card : ℝ) := by
    exact_mod_cast hunion
  calc
    _ ≤ ((Finset.Icc
          ⌊(A₀ : ℝ) / ((m : ℝ) * (1 + eta))⌋₊
          ⌈(A₀ : ℝ) / (m : ℝ)⌉₊).card : ℝ) +
        ((Finset.Icc
          ⌊(B₀ : ℝ) / (m : ℝ)⌋₊
          ⌈(B₀ : ℝ) * (1 + eta) / (m : ℝ)⌉₊).card : ℝ) := hunionR
    _ ≤ ((A₀ : ℝ) / (m : ℝ) -
          (A₀ : ℝ) / ((m : ℝ) * (1 + eta)) + 3) +
        ((B₀ : ℝ) * (1 + eta) / (m : ℝ) -
          (B₀ : ℝ) / (m : ℝ) + 3) := add_le_add hlow hhigh
    _ ≤ ((A₀ : ℝ) + (B₀ : ℝ)) * eta / (m : ℝ) + 6 := by
      rw [hhighWidth]
      have hsplit : ((A₀ : ℝ) + (B₀ : ℝ)) * eta / (m : ℝ) =
          (A₀ : ℝ) * eta / (m : ℝ) + (B₀ : ℝ) * eta / (m : ℝ) := by ring
      rw [hsplit]
      linarith

/-- Above a quadratic cutoff, every gap pair maps into the fixed-cofactor endpoint windows. -/
theorem ladderGapPairsIco_mapsTo_endpointWindows
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta U : ℝ} {J L : ℕ}
    (hA : 0 < A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hPprime : ∀ p ∈ P, p.Prime)
    (hJU : U ≤ Q * (1 + eta) ^ J) (hU : 0 < U)
    (hU2 : (B₀ : ℝ) < U ^ (2 : ℕ)) :
    ∀ z : ((_ : ((_ : ℕ) × ℕ)) × ℕ),
      z ∈ ladderGapPairsIco P A₀ B₀ Q eta J L →
      z.2 ∈ Finset.Icc 1 ⌊(B₀ : ℝ) / U⌋₊ ∧
        z.1.2 ∈ ladderEndpointPrimeWindow A₀ B₀ z.2 eta := by
  classical
  intro z hz
  rw [ladderGapPairsIco, Finset.mem_sigma] at hz
  obtain ⟨hx, hm⟩ := hz
  rw [ladderIndexIco, Finset.mem_sigma] at hx
  obtain ⟨hj, hpBlock⟩ := hx
  rw [Finset.mem_Ico] at hj
  let Qj : ℝ := Q * (1 + eta) ^ z.1.1
  have hrOne : (1 : ℝ) ≤ 1 + eta := by linarith
  have hrPos : (0 : ℝ) < 1 + eta := lt_of_lt_of_le zero_lt_one hrOne
  have hQj0 : 0 < Qj := by dsimp [Qj]; positivity
  have hQJle : Q * (1 + eta) ^ J ≤ Qj := by
    dsimp [Qj]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hrOne hj.1) hQ.le
  have hUQj : U ≤ Qj := hJU.trans hQJle
  have hpRange := Finset.mem_filter.1 (show z.1.2 ∈
      geomBlock P Q (1 + eta) z.1.1 from hpBlock)
  have hpP := hpRange.1
  have hpPrime := hPprime z.1.2 hpP
  have hpLo : Qj < (z.1.2 : ℝ) := by simpa [Qj] using hpRange.2.1
  have hpHi : (z.1.2 : ℝ) ≤ Qj * (1 + eta) := by
    have := hpRange.2.2
    rwa [pow_succ, show Q * ((1 + eta) ^ z.1.1 * (1 + eta)) =
      Qj * (1 + eta) by simp [Qj, mul_assoc]] at this
  have hmCommonMem := (Finset.mem_sdiff.1 hm).1
  have hmPos : 0 < z.2 := ladderGapSetAt_pos hA hQ heta z.1.1 hmCommonMem
  have hmCommon := hmCommonMem
  rw [geomCofactorBlockAt, Finset.mem_Icc] at hmCommon
  have hmR : (0 : ℝ) < (z.2 : ℝ) := by exact_mod_cast hmPos
  have hmHi : (z.2 : ℝ) ≤ (B₀ : ℝ) / Qj := by
    have hfloor := Nat.floor_le (by positivity : (0 : ℝ) ≤ (B₀ : ℝ) / Qj)
    have hcast : (z.2 : ℝ) ≤
        (⌊(B₀ : ℝ) / (Q * (1 + eta) ^ z.1.1)⌋₊ : ℝ) := by
      exact_mod_cast hmCommon.2
    simpa [Qj] using hcast.trans hfloor
  have hmU : (z.2 : ℝ) ≤ (B₀ : ℝ) / U := by
    exact le_trans hmHi (div_le_div_of_nonneg_left (Nat.cast_nonneg B₀) hU hUQj)
  have hmBound : z.2 ∈ Finset.Icc 1 ⌊(B₀ : ℝ) / U⌋₊ := by
    rw [Finset.mem_Icc]
    exact ⟨hmPos, Nat.le_floor hmU⟩
  have hmLtP : z.2 < z.1.2 := by
    have hBU : (B₀ : ℝ) / U < U := (div_lt_iff₀ hU).2 (by simpa [pow_two] using hU2)
    have : (z.2 : ℝ) < (z.1.2 : ℝ) := lt_of_le_of_lt hmU (hBU.trans_le hUQj) |>.trans hpLo
    exact_mod_cast this
  have hnotDvd : ¬ z.1.2 ∣ z.2 := by
    intro hdvd
    exact Nat.not_lt_of_ge (Nat.le_of_dvd hmPos hdvd) hmLtP
  have hnotRamare : z.2 ∉ ramareCofactorSet (Finset.Icc A₀ B₀) z.1.2 := by
    intro hramare
    exact (Finset.mem_sdiff.1 hm).2 (Finset.mem_filter.2 ⟨hramare, hnotDvd⟩)
  have hnotProduct : z.1.2 * z.2 ∉ Finset.Icc A₀ B₀ := by
    exact fun hprod => hnotRamare ((mem_ramareCofactorSet_iff hpPrime.pos).2 hprod)
  have houtside : z.1.2 * z.2 < A₀ ∨ B₀ < z.1.2 * z.2 := by
    rw [Finset.mem_Icc] at hnotProduct
    omega
  have hmLo : (A₀ : ℝ) / (Qj * (1 + eta)) ≤ (z.2 : ℝ) := by
    exact Nat.ceil_le.1 (by simpa [Qj] using hmCommon.1)
  refine ⟨hmBound, ?_⟩
  rw [ladderEndpointPrimeWindow, Finset.mem_union]
  rcases houtside with hlow | hhigh
  · apply Or.inl
    rw [Finset.mem_Icc]
    have hAprod : (A₀ : ℝ) ≤ (z.2 : ℝ) * (Qj * (1 + eta)) := by
      rwa [div_le_iff₀ (by positivity)] at hmLo
    have hlower : (A₀ : ℝ) / ((z.2 : ℝ) * (1 + eta)) < (z.1.2 : ℝ) := by
      rw [div_lt_iff₀ (mul_pos hmR hrPos)]
      calc
        (A₀ : ℝ) ≤ (z.2 : ℝ) * (Qj * (1 + eta)) := hAprod
        _ = Qj * ((z.2 : ℝ) * (1 + eta)) := by ring
        _ < (z.1.2 : ℝ) * ((z.2 : ℝ) * (1 + eta)) :=
          mul_lt_mul_of_pos_right hpLo (mul_pos hmR hrPos)
    have hupper : (z.1.2 : ℝ) < (A₀ : ℝ) / (z.2 : ℝ) := by
      rw [lt_div_iff₀ hmR]
      exact_mod_cast hlow
    constructor
    · exact_mod_cast (Nat.floor_le (by positivity :
        (0 : ℝ) ≤ (A₀ : ℝ) / ((z.2 : ℝ) * (1 + eta)))).trans hlower.le
    · exact_mod_cast hupper.le.trans (Nat.le_ceil _)
  · apply Or.inr
    rw [Finset.mem_Icc]
    have hlower : (B₀ : ℝ) / (z.2 : ℝ) < (z.1.2 : ℝ) := by
      rw [div_lt_iff₀ hmR]
      exact_mod_cast hhigh
    have hQjm : Qj * (z.2 : ℝ) ≤ (B₀ : ℝ) := by
      have hmQj : (z.2 : ℝ) * Qj ≤ (B₀ : ℝ) := (le_div_iff₀ hQj0).mp hmHi
      simpa [mul_comm] using hmQj
    have hupper : (z.1.2 : ℝ) ≤ (B₀ : ℝ) * (1 + eta) / (z.2 : ℝ) := by
      rw [le_div_iff₀ hmR]
      nlinarith [mul_le_mul_of_nonneg_right hpHi hmR.le]
    constructor
    · exact_mod_cast (Nat.floor_le (by positivity :
        (0 : ℝ) ≤ (B₀ : ℝ) / (z.2 : ℝ))).trans hlower.le
    · exact_mod_cast hupper.trans (Nat.le_ceil _)

/-- The cofactor/prime projection is injective on flattened ladder gap pairs. -/
theorem ladderGapPairsIco_swap_injective
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta : ℝ} {J L : ℕ}
    (hQ : 0 < Q) (heta : 0 ≤ eta) :
    Set.InjOn (fun z : ((_ : ((_ : ℕ) × ℕ)) × ℕ) =>
      (⟨z.2, z.1.2⟩ : ((_ : ℕ) × ℕ)))
      (ladderGapPairsIco P A₀ B₀ Q eta J L : Set _) := by
  classical
  intro x hx y hy heq
  change x ∈ ladderGapPairsIco P A₀ B₀ Q eta J L at hx
  change y ∈ ladderGapPairsIco P A₀ B₀ Q eta J L at hy
  rw [ladderGapPairsIco, Finset.mem_sigma] at hx hy
  rw [ladderIndexIco, Finset.mem_sigma] at hx hy
  have hm : x.2 = y.2 := congrArg Sigma.fst heq
  have hp : x.1.2 = y.1.2 := by
    cases x with
    | mk xpair xm =>
      cases y with
      | mk ypair ym =>
        simp only at heq ⊢
        exact congrArg Sigma.snd heq
  have hxj := hx.1.1
  have hyj := hy.1.1
  rw [Finset.mem_Ico] at hxj hyj
  have hj : x.1.1 = y.1.1 := by
    by_contra hne
    have hdisj := geomBlock_pairwiseDisjoint P hQ
      (by linarith : (1 : ℝ) ≤ 1 + eta) L
      (by simpa using hxj.2) (by simpa using hyj.2) hne
    exact (Finset.disjoint_left.1 hdisj) hx.1.2 (hp ▸ hy.1.2)
  exact Sigma.ext (Sigma.ext hj (heq_of_eq hp)) (heq_of_eq hm)

set_option maxHeartbeats 100000 in
/-- Above a quadratic cutoff, the physical product is injective on flattened high-ladder gap
pairs.  Unique factorization first recovers cofactor and prime; disjoint ladder blocks then recover
the step. -/
theorem ladderGapPairsIco_product_injective
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta U : ℝ} {J L : ℕ}
    (hA : 0 < A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hPprime : ∀ p ∈ P, p.Prime)
    (hJU : U ≤ Q * (1 + eta) ^ J) (hU : 0 < U)
    (hU2 : (B₀ : ℝ) < U ^ (2 : ℕ)) :
    Set.InjOn (fun z : ((_ : ((_ : ℕ) × ℕ)) × ℕ) => z.1.2 * z.2)
      (ladderGapPairsIco P A₀ B₀ Q eta J L : Set _) := by
  classical
  have hrOne : (1 : ℝ) ≤ 1 + eta := by linarith
  have hprimeLower : ∀ z ∈ ladderGapPairsIco P A₀ B₀ Q eta J L,
      U < (z.1.2 : ℝ) := by
    intro z hz
    rw [ladderGapPairsIco, Finset.mem_sigma, ladderIndexIco, Finset.mem_sigma] at hz
    have hj := hz.1.1
    rw [Finset.mem_Ico] at hj
    have hQJle : Q * (1 + eta) ^ J ≤ Q * (1 + eta) ^ z.1.1 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hrOne hj.1) hQ.le
    have hpLo : Q * (1 + eta) ^ z.1.1 < (z.1.2 : ℝ) := by
      exact (Finset.mem_filter.1 hz.1.2).2.1
    exact lt_of_le_of_lt (hJU.trans hQJle) hpLo
  have hprime : ∀ z ∈ ladderGapPairsIco P A₀ B₀ Q eta J L, z.1.2.Prime := by
    intro z hz
    rw [ladderGapPairsIco, Finset.mem_sigma, ladderIndexIco, Finset.mem_sigma] at hz
    exact hPprime z.1.2 (geomBlock_subset P Q (1 + eta) z.1.1 hz.1.2)
  have hcofactor : ∀ z ∈ ladderGapPairsIco P A₀ B₀ Q eta J L,
      0 < z.2 ∧ (z.2 : ℝ) ≤ (B₀ : ℝ) / U := by
    intro z hz
    have hmap := ladderGapPairsIco_mapsTo_endpointWindows
      hA hQ heta hPprime hJU hU hU2 z hz
    have hmRange := Finset.mem_Icc.1 hmap.1
    refine ⟨hmRange.1, ?_⟩
    have hfloor := Nat.floor_le (div_nonneg (Nat.cast_nonneg B₀) hU.le)
    exact (Nat.cast_le.2 hmRange.2).trans hfloor
  have hBU : (B₀ : ℝ) / U < U :=
    (div_lt_iff₀ hU).2 (by simpa [pow_two] using hU2)
  intro x hx y hy hprod
  have hxC := hcofactor x hx
  have hyC := hcofactor y hy
  have hxy : x.2 < y.1.2 := by
    exact Nat.cast_lt.1 (lt_of_le_of_lt hxC.2 (hBU.trans (hprimeLower y hy)))
  have hyx : y.2 < x.1.2 := by
    exact Nat.cast_lt.1 (lt_of_le_of_lt hyC.2 (hBU.trans (hprimeLower x hx)))
  have hdecode := RHTower.largePrimeMarker_product_injective
    (hprime x hx) (hprime y hy) hyC.1 hyx hxy (by simpa [mul_comm] using hprod)
  apply ladderGapPairsIco_swap_injective hQ heta hx hy
  exact Sigma.ext hdecode.1 (heq_of_eq hdecode.2)

/-- High-ladder gap pairs are bounded after swapping to cofactor-first endpoint windows. -/
theorem card_ladderGapPairsIco_le_endpointWindows
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta U : ℝ} {J L : ℕ}
    (hA : 0 < A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hPprime : ∀ p ∈ P, p.Prime)
    (hJU : U ≤ Q * (1 + eta) ^ J) (hU : 0 < U)
    (hU2 : (B₀ : ℝ) < U ^ (2 : ℕ)) :
    ((ladderGapPairsIco P A₀ B₀ Q eta J L).card : ℝ) ≤
      ∑ m ∈ Finset.Icc 1 ⌊(B₀ : ℝ) / U⌋₊,
        (((A₀ : ℝ) + (B₀ : ℝ)) * eta / (m : ℝ) + 6) := by
  classical
  let T : Finset ((_ : ℕ) × ℕ) :=
    (Finset.Icc 1 ⌊(B₀ : ℝ) / U⌋₊).sigma
      (fun m => ladderEndpointPrimeWindow A₀ B₀ m eta)
  have hmaps : ∀ z ∈ ladderGapPairsIco P A₀ B₀ Q eta J L,
      (⟨z.2, z.1.2⟩ : ((_ : ℕ) × ℕ)) ∈ T := by
    intro z hz
    dsimp only [T]
    rw [Finset.mem_sigma]
    exact ladderGapPairsIco_mapsTo_endpointWindows hA hQ heta hPprime hJU hU hU2 z hz
  have hinj := ladderGapPairsIco_swap_injective (P := P) (A₀ := A₀) (B₀ := B₀)
    (J := J) (L := L) hQ heta
  have hcard := Finset.card_le_card_of_injOn
    (fun z : ((_ : ((_ : ℕ) × ℕ)) × ℕ) =>
      (⟨z.2, z.1.2⟩ : ((_ : ℕ) × ℕ))) hmaps hinj
  have hcardR : ((ladderGapPairsIco P A₀ B₀ Q eta J L).card : ℝ) ≤
      (T.card : ℝ) := by exact_mod_cast hcard
  dsimp only [T] at hcardR
  rw [Finset.card_sigma, Nat.cast_sum] at hcardR
  refine hcardR.trans ?_
  exact Finset.sum_le_sum fun m hm => card_ladderEndpointPrimeWindow_le
    A₀ B₀ m heta (Finset.mem_Icc.1 hm).1

/-- Closed harmonic form of the high-ladder gap-pair bound. -/
theorem card_ladderGapPairsIco_le_harmonic
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta U : ℝ} {J L : ℕ}
    (hA : 0 < A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hPprime : ∀ p ∈ P, p.Prime)
    (hJU : U ≤ Q * (1 + eta) ^ J) (hU : 0 < U)
    (hU2 : (B₀ : ℝ) < U ^ (2 : ℕ)) :
    ((ladderGapPairsIco P A₀ B₀ Q eta J L).card : ℝ) ≤
      ((A₀ : ℝ) + (B₀ : ℝ)) * eta *
          (1 + Real.log ⌊(B₀ : ℝ) / U⌋₊) +
        6 * (⌊(B₀ : ℝ) / U⌋₊ : ℝ) := by
  have hbase := card_ladderGapPairsIco_le_endpointWindows
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (U := U)
    (J := J) (L := L) hA hQ heta hPprime hJU hU hU2
  refine hbase.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hfactor : ∑ m ∈ Finset.Icc 1 ⌊(B₀ : ℝ) / U⌋₊,
      ((A₀ : ℝ) + (B₀ : ℝ)) * eta / (m : ℝ) =
      ((A₀ : ℝ) + (B₀ : ℝ)) * eta *
        ∑ m ∈ Finset.Icc 1 ⌊(B₀ : ℝ) / U⌋₊, 1 / (m : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => by ring
  rw [hfactor]
  have hsum := sum_Icc_one_div_le_one_add_log ⌊(B₀ : ℝ) / U⌋₊
  have hcoef : 0 ≤ ((A₀ : ℝ) + (B₀ : ℝ)) * eta := by positivity
  have hcard : ((Finset.Icc 1 ⌊(B₀ : ℝ) / U⌋₊).card : ℝ) =
      (⌊(B₀ : ℝ) / U⌋₊ : ℝ) := by
    simp [Nat.card_Icc]
  rw [hcard]
  convert add_le_add_right (mul_le_mul_of_nonneg_left hsum hcoef)
    (6 * (⌊(B₀ : ℝ) / U⌋₊ : ℝ)) using 1 <;> ring

end

end RHTower.Sieve

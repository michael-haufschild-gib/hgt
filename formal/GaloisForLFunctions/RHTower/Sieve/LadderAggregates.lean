import GaloisForLFunctions.RHTower.Sieve.BlockMassCompare
import GaloisForLFunctions.RHTower.Sieve.LadderStepMajorant
import GaloisForLFunctions.RHTower.Sieve.LadderGroupBudget
import GaloisForLFunctions.RHTower.Sieve.RamareBlockSplit

/-!
# The three aggregates of a geometric ladder

`Sieve/LadderGroupBudget` reduces both ladder groups to `S`, `Bmax` and `PP`.  Here those three are
computed for the corpus's own blocks:

* `S` — the counting sum against the cofactor lengths is the harmonic mass of the range, because a
  block's primes all exceed its base by at most the factor `1 + η`;
* `Bmax` — a block holds the primes of an interval of relative width `η` about its base;
* `PP` — the blocks partition the designated primes.

The cofactor cardinality obeys `#C_j ≤ ⌊M/R_j⌋ + 1` because the block is an `Icc` ending there.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The cofactor block is no larger than its right endpoint plus one. -/
theorem card_geomCofactorBlock_le (M : ℕ) (Q η : ℝ) (j : ℕ) :
    ((geomCofactorBlock M Q η j).card : ℝ)
      ≤ ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) + 1 := by
  rw [geomCofactorBlock, Nat.card_Icc]
  have hle : ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ + 1 - ⌈((1 : ℕ) : ℝ) / ((Q * (1 + η) ^ j) * (1 + η))⌉₊
      ≤ ⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ + 1 := Nat.sub_le _ _
  have := (Nat.cast_le (α := ℝ)).2 hle
  push_cast at this ⊢
  linarith

/-- **The aggregate `S`.**  The counting sum against the cofactor lengths is the harmonic mass. -/
theorem sum_card_geomBlock_mul_floor_le {P : Finset ℕ} (M : ℕ) {Q η : ℝ} (hQ : 0 < Q)
    (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L) :
    (∑ j ∈ Finset.range L,
        ((geomBlock P Q (1 + η) j).card : ℝ) * ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
      ≤ (1 + η) * (M : ℝ) * ∑ p ∈ P, 1 / (p : ℝ) := by
  refine le_trans (Finset.sum_le_sum fun j _ => ?_)
    (sum_card_geomBlock_div_le (P := P) hQ hη hL hP (B := (M : ℝ)) (Nat.cast_nonneg M))
  have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  have hfloor : ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) ≤ (M : ℝ) / (Q * (1 + η) ^ j) :=
    Nat.floor_le (by positivity)
  exact mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg _)

/-- **The aggregate `Bmax`.**  Every block of the ladder is bounded by the top of the range. -/
theorem card_geomBlock_le_top (P : Finset ℕ) {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) {L j : ℕ}
    (hj : j ∈ Finset.range L) :
    ((geomBlock P Q (1 + η) j).card : ℝ) ≤ Q * (1 + η) ^ L * η + 1 := by
  refine le_trans (card_geomBlock_le P hQ hη j) ?_
  have hjL : j ≤ L := le_of_lt (Finset.mem_range.1 hj)
  have hmono : (1 + η) ^ j ≤ (1 + η) ^ L := pow_le_pow_right₀ (by linarith) hjL
  have hQ0 : (0 : ℝ) ≤ Q := hQ.le
  have hQη : (0 : ℝ) ≤ Q * η := mul_nonneg hQ0 hη
  nlinarith [mul_le_mul_of_nonneg_left hmono hQη]

/-- **The aggregate `PP`.**  The blocks partition the designated primes. -/
theorem sum_card_geomBlock_le_card {P : Finset ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) {L : ℕ}
    (hL : 1 ≤ L) (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L) :
    (∑ j ∈ Finset.range L, ((geomBlock P Q (1 + η) j).card : ℝ)) ≤ (P.card : ℝ) :=
  le_of_eq (sum_card_geomBlock_eq hQ hη hL hP)

/-- The harmonic mass of the designated range. -/
def rangeHarmonic (P : Finset ℕ) : ℝ := ∑ p ∈ P, 1 / (p : ℝ)

/-- **The small half's ladder group at a relative threshold.**  Everything is now expressed in the
harmonic mass of the range, the top of the range, and the number of designated primes. -/
theorem smallLadderGroup_le {P : Finset ℕ} (M : ℕ) {R η W θ : ℝ} (hR : 0 < R) (hη : 0 ≤ η)
    (hW : 0 ≤ W) {L : ℕ} (hL : 1 ≤ L)
    (hP : ∀ p ∈ P, R < (p : ℝ) ∧ (p : ℝ) ≤ R * (1 + η) ^ L) :
    2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        (θ * ((geomBlock P R (1 + η) j).card : ℝ)) ^ (2 : ℕ)
          * ((5 * Real.pi / 2 * W
                + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
              * ((geomCofactorBlock M R η j).card : ℝ))
      ≤ 5 * Real.pi * (L : ℝ) * θ ^ (2 : ℕ) * W
            * ((R * (1 + η) ^ L * η + 1) * ((1 + η) * (M : ℝ) * rangeHarmonic P)
              + (R * (1 + η) ^ L * η + 1) * (P.card : ℝ))
        + 5 * Real.exp 1 * (L : ℝ) * θ ^ (2 : ℕ)
            * (((1 + η) * (M : ℝ) * rangeHarmonic P) ^ (2 : ℕ)
              + (R * (1 + η) ^ L * η + 1) * ((1 + η) * (M : ℝ) * rangeHarmonic P)) := by
  have hBmax0 : (0 : ℝ) ≤ R * (1 + η) ^ L * η + 1 := by positivity
  have hS0 : (0 : ℝ) ≤ (1 + η) * (M : ℝ) * rangeHarmonic P := by
    have hH : (0 : ℝ) ≤ rangeHarmonic P :=
      Finset.sum_nonneg fun p _ => by positivity
    have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
    rw [rangeHarmonic] at hH ⊢
    positivity
  refine ladderGroup_mvt_le
    (B := fun j => ((geomBlock P R (1 + η) j).card : ℝ))
    (Cc := fun j => ((geomCofactorBlock M R η j).card : ℝ))
    (Nn := fun j => ((⌊(M : ℝ) / (R * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
    hW hBmax0 (fun j => Nat.cast_nonneg _) (fun j => Nat.cast_nonneg _)
    (fun j => Nat.cast_nonneg _)
    (fun j _ => card_geomCofactorBlock_le M R η j)
    (fun j hj => card_geomBlock_le_top P hR hη hj)
    ?_ hS0 ?_
  · rw [rangeHarmonic]
    exact sum_card_geomBlock_mul_floor_le M hR hη hL hP
  · exact sum_card_geomBlock_le_card hR hη hL hP

end

end RHTower.Sieve

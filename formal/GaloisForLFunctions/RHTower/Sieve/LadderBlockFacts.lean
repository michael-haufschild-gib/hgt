import GaloisForLFunctions.RHTower.Sieve.SpectralParameters

/-!
# Elementary facts about the ladder's block endpoints

The master budget theorem asks for uniform bounds on the ladder's block endpoints and on the lengths
of its cofactor blocks.  All of them follow from the two facts that the ladder starts at `Q` and does
not overshoot the window length.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

theorem ladderBlockTop_le {Q η hR : ℝ} (hQ0 : 0 < Q) (hη : 0 ≤ η) {L j : ℕ} (hj : j + 1 ≤ L)
    (hle : Q * (1 + η) ^ L ≤ hR) : Q * (1 + η) ^ (j + 1) ≤ hR := by
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr1 hj) hQ0.le
  linarith

theorem ladderBlockTop_ge {Q η : ℝ} (hQ0 : 0 < Q) (hη : 0 ≤ η) (j : ℕ) :
    Q ≤ Q * (1 + η) ^ (j + 1) := by
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hpow : (1 : ℝ) ≤ (1 + η) ^ (j + 1) := one_le_pow₀ hr1
  nlinarith [hpow, hQ0]

/-- The block endpoint, rounded, is at least the bottom of the designated range. -/
theorem le_max_ladderBlock {z₀ : ℕ} {Q η : ℝ} (hQ : Q = (z₀ : ℝ)) (hη : 0 ≤ η) (hz₀ : 1 ≤ z₀)
    (j : ℕ) : Q ≤ max ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1 := by
  have hQ0 : (0 : ℝ) < Q := by
    rw [hQ]
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hz₀
  have hfl : z₀ ≤ ⌊Q * (1 + η) ^ (j + 1)⌋₊ := by
    refine Nat.le_floor ?_
    rw [← hQ]
    exact ladderBlockTop_ge hQ0 hη j
  have hc : ((z₀ : ℕ) : ℝ) ≤ ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfl
  have : Q ≤ ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) :=
    calc Q = ((z₀ : ℕ) : ℝ) := hQ
      _ ≤ ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) := hc
  exact le_trans this (le_max_left _ _)

/-- The block endpoint, rounded, is at most the window length. -/
theorem max_ladderBlock_le {Q η hR : ℝ} (hQ0 : 0 < Q) (hη : 0 ≤ η) {L j : ℕ} (hj : j + 1 ≤ L)
    (hle : Q * (1 + η) ^ L ≤ hR) (hR1 : 1 ≤ hR) :
    max ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1 ≤ hR := by
  refine max_le ?_ hR1
  refine le_trans (Nat.floor_le (by positivity)) ?_
  exact ladderBlockTop_le hQ0 hη hj hle

/-- The cofactor blocks are at least as long as the Gallagher cut. -/
theorem le_floor_cofactor {B₀ : ℕ} {Q η hR G : ℝ} (hQ0 : 0 < Q) (hη : 0 ≤ η) {L j : ℕ}
    (hj : j < L) (hle : Q * (1 + η) ^ L ≤ hR) (hG : G = (B₀ : ℝ) / hR) :
    ((⌊G⌋₊ : ℕ) : ℝ) ≤ ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) := by
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  have hjle : Q * (1 + η) ^ j ≤ hR := by
    have := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr1 (le_of_lt hj)) hQ0.le
    linarith
  have hdiv : G ≤ (B₀ : ℝ) / (Q * (1 + η) ^ j) := by
    rw [hG]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hbase hjle
  exact_mod_cast Nat.floor_le_floor hdiv

end

end RHTower.Sieve

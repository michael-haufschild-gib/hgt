import GaloisForLFunctions.RHTower.Sieve.LadderSumBounds
import GaloisForLFunctions.RHTower.Sieve.LadderStepMajorant

/-!
# The ladder's affine slope and constant, bounded explicitly

Substituting the three ladder sums into the affine majorant leaves an expression in the parameters
alone.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The defect's shape factor, bounded. -/
theorem ladderDefectSum_le {B₀ : ℕ} {Q η hR : ℝ} (hQ1 : 1 < Q) (hη : 0 < η) (hη1 : η ≤ 1)
    {L : ℕ} (hle : Q * (1 + η) ^ L ≤ hR) :
    ladderDefectSum L B₀ Q η
      ≤ (Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log Q)
        * ((L : ℝ) * ((1 + (B₀ : ℝ)) * η ^ (2 : ℕ) + 5) + 5 * hR
          + (η * (B₀ : ℝ) + (1 + (B₀ : ℝ)) * η) * (2 / (Q * η))
          + (B₀ : ℝ) * (2 / (Q ^ (2 : ℕ) * η))) := by
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ1
  have hlogQ : (0 : ℝ) < Real.log Q := Real.log_pos hQ1
  have hlog : (0 : ℝ) ≤ Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos ⌊(B₀ : ℝ) * (1 + η)⌋₊ with h0 | hpos
    · rw [h0]; simp
    · exact Real.log_nonneg (by exact_mod_cast hpos)
  rw [ladderDefectSum]
  exact mul_le_mul_of_nonneg_left (ladderDefect_inner_le hQ0 hη hη1 hle)
    (div_nonneg hlog hlogQ.le)

/-- The slope of the ladder's affine majorant, bounded. -/
theorem ladderAffineSlope_le {B₀ : ℕ} {Q η hR ρ : ℝ} (hQ1 : 1 < Q) (hη : 0 < η) (hη1 : η ≤ 1)
    {L : ℕ} (hle : Q * (1 + η) ^ L ≤ hR) :
    ladderAffineSlope L B₀ Q η ρ
      ≤ 4 * (5 * Real.pi / 2) * ρ ^ (2 : ℕ)
          * (2 * ((L : ℝ) * Real.sqrt ((B₀ : ℝ) * hR)) ^ (2 : ℕ) + 2 * (hR / η) ^ (2 : ℕ))
        + 2 * (5 * Real.pi / 2)
          * ((Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log Q)
            * ((L : ℝ) * ((1 + (B₀ : ℝ)) * η ^ (2 : ℕ) + 5) + 5 * hR
              + (η * (B₀ : ℝ) + (1 + (B₀ : ℝ)) * η) * (2 / (Q * η))
              + (B₀ : ℝ) * (2 / (Q ^ (2 : ℕ) * η)))) := by
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ1
  have hS1 := sum_S1_le (B₀ := B₀) hQ0 hη hle
  have hS10 : (0 : ℝ) ≤ ∑ j ∈ Finset.range L,
      (Q * (1 + η) ^ j) * Real.sqrt ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1) := by
    refine Finset.sum_nonneg fun j _ => ?_
    have : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    positivity
  have hsq : (∑ j ∈ Finset.range L,
        (Q * (1 + η) ^ j) * Real.sqrt ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)) ^ (2 : ℕ)
      ≤ 2 * ((L : ℝ) * Real.sqrt ((B₀ : ℝ) * hR)) ^ (2 : ℕ) + 2 * (hR / η) ^ (2 : ℕ) := by
    nlinarith [hS1, hS10, sq_nonneg ((L : ℝ) * Real.sqrt ((B₀ : ℝ) * hR) - hR / η)]
  have hdef := ladderDefectSum_le (B₀ := B₀) hQ1 hη hη1 hle
  rw [ladderAffineSlope]
  have h1 : 4 * (5 * Real.pi / 2) * ρ ^ (2 : ℕ)
        * (∑ j ∈ Finset.range L,
            (Q * (1 + η) ^ j) * Real.sqrt ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)) ^ (2 : ℕ)
      ≤ 4 * (5 * Real.pi / 2) * ρ ^ (2 : ℕ)
        * (2 * ((L : ℝ) * Real.sqrt ((B₀ : ℝ) * hR)) ^ (2 : ℕ) + 2 * (hR / η) ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have h2 : 2 * (5 * Real.pi / 2) * ladderDefectSum L B₀ Q η
      ≤ 2 * (5 * Real.pi / 2)
        * ((Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log Q)
          * ((L : ℝ) * ((1 + (B₀ : ℝ)) * η ^ (2 : ℕ) + 5) + 5 * hR
            + (η * (B₀ : ℝ) + (1 + (B₀ : ℝ)) * η) * (2 / (Q * η))
            + (B₀ : ℝ) * (2 / (Q ^ (2 : ℕ) * η)))) :=
    mul_le_mul_of_nonneg_left hdef (by positivity)
  linarith

/-- The constant of the ladder's affine majorant, bounded. -/
theorem ladderAffineConst_le {z₀ z B₀ : ℕ} {Q η hR ρ s w₀ : ℝ} (hQ1 : 1 < Q) (hη : 0 < η)
    (hη1 : η ≤ 1) {L : ℕ} (hle : Q * (1 + η) ^ L ≤ hR) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (hP : ∀ p ∈ primesRange z₀ z, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L) :
    ladderAffineConst z₀ z L B₀ Q η ρ s w₀
      ≤ 4 * (5 * Real.exp 1 / 2) * ρ ^ (2 : ℕ)
          * (2 * ((L : ℝ) * (B₀ : ℝ)) ^ (2 : ℕ) + 2 * (hR / η) ^ (2 : ℕ))
        + 2 * ((Real.sqrt (2 * w₀) + 1)
            * (s * ((1 + η) * (B₀ : ℝ) * (∑ p ∈ primesRange z₀ z, 1 / (p : ℝ)))
              + ((primesRange z₀ z).card : ℝ)
              + s * (∑ j ∈ Finset.range L, (B₀ : ℝ) / (Q * (1 + η) ^ j)) + (L : ℝ))) ^ (2 : ℕ)
        + 2 * (5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
          * ((Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log Q)
            * ((L : ℝ) * ((1 + (B₀ : ℝ)) * η ^ (2 : ℕ) + 5) + 5 * hR
              + (η * (B₀ : ℝ) + (1 + (B₀ : ℝ)) * η) * (2 / (Q * η))
              + (B₀ : ℝ) * (2 / (Q ^ (2 : ℕ) * η)))) := by
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ1
  have hS2 := sum_S2_le (B₀ := B₀) hQ0 hη hle
  have hS20 : (0 : ℝ) ≤ ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
      * Real.sqrt (((B₀ : ℝ) / (Q * (1 + η) ^ j)) * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)) := by
    refine Finset.sum_nonneg fun j _ => ?_
    have : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    positivity
  have hsq : (∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
        * Real.sqrt (((B₀ : ℝ) / (Q * (1 + η) ^ j)) * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))) ^ (2 : ℕ)
      ≤ 2 * ((L : ℝ) * (B₀ : ℝ)) ^ (2 : ℕ) + 2 * (hR / η) ^ (2 : ℕ) := by
    nlinarith [hS2, hS20, sq_nonneg ((L : ℝ) * (B₀ : ℝ) - hR / η)]
  have hdisc := sum_discMajorant_le (P := primesRange z₀ z) hQ0 hη.le hL hP (B₀ := B₀)
    (s := s) (w₀ := w₀) hs
  have hdisc0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range L,
      discMajorant (primesRange z₀ z) B₀ Q η s w₀ j :=
    Finset.sum_nonneg fun j _ => (discMajorant_pos hQ0 hη.le hs j).le
  have hdiscsq : (∑ j ∈ Finset.range L, discMajorant (primesRange z₀ z) B₀ Q η s w₀ j) ^ (2 : ℕ)
      ≤ ((Real.sqrt (2 * w₀) + 1)
          * (s * ((1 + η) * (B₀ : ℝ) * (∑ p ∈ primesRange z₀ z, 1 / (p : ℝ)))
            + ((primesRange z₀ z).card : ℝ)
            + s * (∑ j ∈ Finset.range L, (B₀ : ℝ) / (Q * (1 + η) ^ j)) + (L : ℝ))) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hdisc0 hdisc 2
  have hdef := ladderDefectSum_le (B₀ := B₀) hQ1 hη hη1 hle
  rw [ladderAffineConst]
  have h1 : 4 * (5 * Real.exp 1 / 2) * ρ ^ (2 : ℕ)
        * (∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
            * Real.sqrt (((B₀ : ℝ) / (Q * (1 + η) ^ j))
              * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))) ^ (2 : ℕ)
      ≤ 4 * (5 * Real.exp 1 / 2) * ρ ^ (2 : ℕ)
        * (2 * ((L : ℝ) * (B₀ : ℝ)) ^ (2 : ℕ) + 2 * (hR / η) ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have h3 : 2 * (5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
        * ladderDefectSum L B₀ Q η
      ≤ 2 * (5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
        * ((Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log Q)
          * ((L : ℝ) * ((1 + (B₀ : ℝ)) * η ^ (2 : ℕ) + 5) + 5 * hR
            + (η * (B₀ : ℝ) + (1 + (B₀ : ℝ)) * η) * (2 / (Q * η))
            + (B₀ : ℝ) * (2 / (Q ^ (2 : ℕ) * η)))) :=
    mul_le_mul_of_nonneg_left hdef (by positivity)
  linarith [h1, h3, hdiscsq]

end

end RHTower.Sieve

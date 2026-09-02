import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionElementary
import GaloisForLFunctions.RHTower.Sieve.KloostermanSourceResidueMultiplicity

/-!
# Literal-interval global Kloosterman collision envelope

The elementary global collision estimate is specialized to the paper's exact source interval
`Finset.Icc 1 N`.  Existing residue-fibre multiplicity is first exposed without its common
positive modulus factor, then inserted independently into both source legs.  No injectivity,
support, modulus-size, or spectral premise is introduced.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Exact raw residue-energy specialization for the literal positive source interval. -/
theorem sum_normSq_kloostermanSourceResidue_Icc_le_interval
    (q N : ℕ) (b : ℕ → ℂ) :
    (∑ z : ZMod (q + 1),
      Complex.normSq (kloostermanSourceResidue (q + 1) (Finset.Icc 1 N) b z)) ≤
      (kloostermanIntervalResidueMultiplicity q N : ℝ) *
        ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n) := by
  have h := kloostermanSourceResidueEnergy_Icc_le_intervalBudget q N b
  unfold kloostermanSourceResidueEnergy kloostermanIntervalSourceEnergyBudget at h
  have hq : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
  nlinarith

/-- Literal-source interval form of the unconditional elementary global collision envelope. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_Icc_le_elementary
    (Q : Finset ℕ) (w : ℕ → ℂ) (N : ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w (Finset.Icc 1 N) b ≤
      ((Q.card * (Q.card - 1) : ℕ) : ℝ) *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          Complex.normSq (w q) * Complex.normSq (w r) *
            (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
              ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
                ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) *
              ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
                ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n))) := by
  calc
    kloostermanGlobalFrequencyCollisionEnergy Q w (Finset.Icc 1 N) b ≤
      ((Q.card * (Q.card - 1) : ℕ) : ℝ) *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          Complex.normSq (w q) * Complex.normSq (w r) *
            (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
              (∑ z : ZMod (q + 1),
                Complex.normSq
                  (kloostermanSourceResidue (q + 1) (Finset.Icc 1 N) b z)) *
              ∑ z : ZMod (r + 1),
                Complex.normSq
                  (kloostermanSourceResidue (r + 1) (Finset.Icc 1 N) b z)) :=
      kloostermanGlobalFrequencyCollisionEnergy_le_elementary
        Q w (Finset.Icc 1 N) b
    _ ≤ ((Q.card * (Q.card - 1) : ℕ) : ℝ) *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          Complex.normSq (w q) * Complex.normSq (w r) *
            (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
              ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
                ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) *
              ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
                ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n))) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro q hq
        apply Finset.sum_le_sum
        intro r hr
        have hqEnergy := sum_normSq_kloostermanSourceResidue_Icc_le_interval q N b
        have hrEnergy := sum_normSq_kloostermanSourceResidue_Icc_le_interval r N b
        have hproduct :
            (∑ z : ZMod (q + 1),
                Complex.normSq
                  (kloostermanSourceResidue (q + 1) (Finset.Icc 1 N) b z)) *
              (∑ z : ZMod (r + 1),
                Complex.normSq
                  (kloostermanSourceResidue (r + 1) (Finset.Icc 1 N) b z)) ≤
            ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
                ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) *
              ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
                ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) :=
          mul_le_mul hqEnergy hrEnergy
            (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _)
              (Finset.sum_nonneg fun n hn => Complex.normSq_nonneg _))
        calc
          Complex.normSq (w q) * Complex.normSq (w r) *
              (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
                (∑ z : ZMod (q + 1),
                  Complex.normSq
                    (kloostermanSourceResidue (q + 1) (Finset.Icc 1 N) b z)) *
                ∑ z : ZMod (r + 1),
                  Complex.normSq
                    (kloostermanSourceResidue (r + 1) (Finset.Icc 1 N) b z)) =
            (Complex.normSq (w q) * Complex.normSq (w r) *
              (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ))) *
                ((∑ z : ZMod (q + 1),
                    Complex.normSq
                      (kloostermanSourceResidue (q + 1) (Finset.Icc 1 N) b z)) *
                  ∑ z : ZMod (r + 1),
                    Complex.normSq
                      (kloostermanSourceResidue (r + 1) (Finset.Icc 1 N) b z)) := by ring
          _ ≤ (Complex.normSq (w q) * Complex.normSq (w r) *
              (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ))) *
                (((kloostermanIntervalResidueMultiplicity q N : ℝ) *
                    ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) *
                  ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
                    ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n))) :=
            mul_le_mul_of_nonneg_left hproduct
              (mul_nonneg
                (mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
                (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)))
          _ = Complex.normSq (w q) * Complex.normSq (w r) *
              (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
                ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
                  ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n)) *
                ((kloostermanIntervalResidueMultiplicity r N : ℝ) *
                  ∑ n ∈ Finset.Icc 1 N, Complex.normSq (b n))) := by ring
      · positivity

end

end RHTower.Sieve

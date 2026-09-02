import GaloisForLFunctions.RHTower.Sieve.KloostermanIntegerKernelGram

/-!
# Cross-modulus Kloosterman correlations

Expanding the signed-kernel Gram entry produces a double modulus sum of incomplete Kloosterman
correlations over the output support.  This file records that identity and separates equal from
distinct moduli exactly.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Incomplete correlation of two complete Kloosterman sums with possibly distinct moduli. -/
def kloostermanCrossModulusCorrelation
    (A : Finset ℕ) (q r : ℕ) (n k : ℤ) : ℂ :=
  ∑ m ∈ A,
    star (kloostermanSum (q + 1) (Int.cast m) (Int.cast n)) *
      kloostermanSum (r + 1) (Int.cast m) (Int.cast k)

/-- Cross-modulus correlation has the expected Hermitian symmetry. -/
theorem star_kloostermanCrossModulusCorrelation
    (A : Finset ℕ) (q r : ℕ) (n k : ℤ) :
    star (kloostermanCrossModulusCorrelation A q r n k) =
      kloostermanCrossModulusCorrelation A r q k n := by
  unfold kloostermanCrossModulusCorrelation
  change (starRingEnd ℂ) (∑ m ∈ A,
    star (kloostermanSum (q + 1) (Int.cast m) (Int.cast n)) *
      kloostermanSum (r + 1) (Int.cast m) (Int.cast k)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [map_mul]
  simp
  ring

/-- Every signed-kernel Gram entry is a weighted double sum of cross-modulus correlations. -/
theorem kloostermanIntegerKernelGram_eq_crossModulusCorrelation
    (Q : Finset ℕ) (w : ℕ → ℂ) (A : Finset ℕ) (n k : ℕ) :
    kloostermanIntegerKernelGram Q w A n k =
      ∑ q ∈ Q, ∑ r ∈ Q, star (w q) * w r *
        kloostermanCrossModulusCorrelation A q r (n : ℤ) (k : ℤ) := by
  unfold kloostermanIntegerKernelGram
  have hstar (m : ℕ) :
      star (kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)) =
        ∑ q ∈ Q, (starRingEnd ℂ) (w q) *
          (starRingEnd ℂ) (kloostermanSum (q + 1)
            (Int.cast m) (Int.cast n)) := by
    unfold kloostermanIntegerModulusKernel
    change (starRingEnd ℂ)
      (∑ q ∈ Q, w q * kloostermanSum (q + 1) (Int.cast m) (Int.cast n)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro q _hq
    rw [map_mul]
  simp_rw [hstar]
  unfold kloostermanIntegerModulusKernel kloostermanCrossModulusCorrelation
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _hr
  apply Finset.sum_congr rfl
  intro m _hm
  change (starRingEnd ℂ) (w q) *
      (starRingEnd ℂ) (kloostermanSum (q + 1) (Int.cast m) (Int.cast n)) *
        (w r * kloostermanSum (r + 1) (Int.cast m) (Int.cast k)) =
    (starRingEnd ℂ) (w q) * w r *
      ((starRingEnd ℂ) (kloostermanSum (q + 1) (Int.cast m) (Int.cast n)) *
        kloostermanSum (r + 1) (Int.cast m) (Int.cast k))
  ring

/-- Equal-modulus part of a signed-kernel Gram entry. -/
def kloostermanSameModulusGram
    (Q : Finset ℕ) (w : ℕ → ℂ) (A : Finset ℕ) (n k : ℕ) : ℂ :=
  ∑ q ∈ Q, star (w q) *
    (w q * kloostermanCrossModulusCorrelation A q q (n : ℤ) (k : ℤ))

/-- Distinct-modulus part, with the equal modulus literally erased. -/
def kloostermanDistinctModulusGram
    (Q : Finset ℕ) (w : ℕ → ℂ) (A : Finset ℕ) (n k : ℕ) : ℂ :=
  ∑ q ∈ Q, star (w q) *
    ∑ r ∈ Q.erase q, w r *
      kloostermanCrossModulusCorrelation A q r (n : ℤ) (k : ℤ)

/-- Exact equal/distinct-modulus split of the Gram entry. -/
theorem kloostermanIntegerKernelGram_eq_same_add_distinctModulus
    (Q : Finset ℕ) (w : ℕ → ℂ) (A : Finset ℕ) (n k : ℕ) :
    kloostermanIntegerKernelGram Q w A n k =
      kloostermanSameModulusGram Q w A n k +
        kloostermanDistinctModulusGram Q w A n k := by
  rw [kloostermanIntegerKernelGram_eq_crossModulusCorrelation]
  unfold kloostermanSameModulusGram kloostermanDistinctModulusGram
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_add]
  rw [show (∑ r ∈ Q, star (w q) * w r *
      kloostermanCrossModulusCorrelation A q r (n : ℤ) (k : ℤ)) =
      star (w q) * ∑ r ∈ Q, w r *
        kloostermanCrossModulusCorrelation A q r (n : ℤ) (k : ℤ) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    ring]
  apply congrArg (star (w q) * ·)
  exact (Finset.add_sum_erase Q
    (fun r => w r * kloostermanCrossModulusCorrelation A q r (n : ℤ) (k : ℤ)) hq).symm

end

end RHTower.Sieve

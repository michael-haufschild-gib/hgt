import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittFrobeniusRingEndomorphism
import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittFrobeniusCalkinEnergyBridge

/-!
# Coherent cross-pair Frobenius compensator

This module constructs a genuinely label-nonlocal source relation before
Hermitian norm and first-ghost scalarization. Each ordered prime seam is split
into two antisymmetric linear legs whose product is the physical
reciprocal-prime atom. Both total ordered-edge legs vanish by reversal.

Polarizing every left edge against every right edge therefore gives an
all-cross source with zero Frobenius first ghost. Its diagonal is exactly the
physical Big-Witt/Calkin source, while its off-diagonal complement has the
opposite coefficient. Thus the off-diagonal cross-pair compensator cancels
the full physical energy exactly, without RH or a submass premise.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

variable {A : Type*} [CommRing A]

/-- A finite complete ordered-edge sum of an antisymmetric coefficient
vanishes over an additively torsion-free ring. -/
theorem deningerBigWitt_doubleSum_antisymm_zero [IsAddTorsionFree A]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ι → A)
    (h : ∀ p q, f q p = -f p q) :
    ∑ p ∈ s, ∑ q ∈ s, f p q = 0 := by
  let S := ∑ p ∈ s, ∑ q ∈ s, f p q
  have hswap : S = ∑ p ∈ s, ∑ q ∈ s, f q p := by
    dsimp only [S]
    rw [Finset.sum_comm]
  have hneg : (∑ p ∈ s, ∑ q ∈ s, f q p) = -S := by
    calc
      (∑ p ∈ s, ∑ q ∈ s, f q p) =
          ∑ p ∈ s, ∑ q ∈ s, -f p q := by
            apply Finset.sum_congr rfl
            intro p hp
            apply Finset.sum_congr rfl
            intro q hq
            exact h p q
      _ = -S := by simp [S]
  have hself : S = -S := hswap.trans hneg
  have hadd : S + S = 0 := eq_neg_iff_add_eq_zero.mp hself
  change S = 0
  apply (nsmul_right_injective (M := A) (by decide : (2 : ℕ) ≠ 0))
  simpa [two_mul] using hadd

/-- Reciprocal-product-weighted oriented left seam leg. -/
def deningerBigWittCrossPairLeftLeg (a : Nat.Primes → ℂ) (p q : Nat.Primes) : ℂ :=
  (((1 / (p : ℝ)) * (1 / (q : ℝ)) : ℝ) : ℂ) * (a p - a q)

/-- Conjugate oriented right seam leg. -/
def deningerBigWittCrossPairRightLeg (a : Nat.Primes → ℂ) (p q : Nat.Primes) : ℂ :=
  (starRingEnd ℂ) (a p - a q)

theorem deningerBigWittCrossPairLeftLeg_reverse
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    deningerBigWittCrossPairLeftLeg a q p = -deningerBigWittCrossPairLeftLeg a p q := by
  simp only [deningerBigWittCrossPairLeftLeg]
  push_cast
  ring

theorem deningerBigWittCrossPairRightLeg_reverse
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    deningerBigWittCrossPairRightLeg a q p = -deningerBigWittCrossPairRightLeg a p q := by
  simp [deningerBigWittCrossPairRightLeg]

theorem deningerBigWittCrossPairLeftLeg_total_zero
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    ∑ p ∈ s, ∑ q ∈ s, deningerBigWittCrossPairLeftLeg a p q = 0 :=
  deningerBigWitt_doubleSum_antisymm_zero s (deningerBigWittCrossPairLeftLeg a)
    (deningerBigWittCrossPairLeftLeg_reverse a)

theorem deningerBigWittCrossPairRightLeg_total_zero
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    ∑ p ∈ s, ∑ q ∈ s, deningerBigWittCrossPairRightLeg a p q = 0 :=
  deningerBigWitt_doubleSum_antisymm_zero s (deningerBigWittCrossPairRightLeg a)
    (deningerBigWittCrossPairRightLeg_reverse a)

/-- Universal bilinear second ghost of the Teichmüller cross-effect. -/
theorem deningerBigWittTeichmullerCrossEffect_ghost_two (x y : A) :
    deningerBigWittGhostComponent 2 (by norm_num)
        (deningerBigWittTeichmullerCrossEffect x y) = -2 * x * y := by
  simp [deningerBigWittTeichmullerCrossEffect,
    deningerBigWittGhostComponent_teichmuller]
  ring

/-- Complete nonlocal polarization of every oriented left seam against every
oriented right seam. -/
def deningerBigWittCrossPairAllSource
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    DeningerBigWittRing ℂ :=
  ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, ∑ t ∈ s,
    deningerBigWittTeichmullerCrossEffect
      (deningerBigWittCrossPairLeftLeg a p q) (deningerBigWittCrossPairRightLeg a r t)

/-- Diagonal part of complete cross-pair polarization. Its physical ghost is
the original reciprocal-prime seam energy. -/
def deningerBigWittCrossPairDiagonalSource
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    DeningerBigWittRing ℂ :=
  ∑ p ∈ s, ∑ q ∈ s,
    deningerBigWittTeichmullerCrossEffect
      (deningerBigWittCrossPairLeftLeg a p q) (deningerBigWittCrossPairRightLeg a p q)

/-- Off-diagonal source complement, defined before Frobenius or scalar
readout. -/
def deningerBigWittCrossPairOffDiagonalCompensator
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    DeningerBigWittRing ℂ :=
  deningerBigWittCrossPairAllSource a s - deningerBigWittCrossPairDiagonalSource a s

/-- Coherent left- and right-leg cancellation annihilates the complete
all-cross second ghost. -/
theorem deningerBigWittCrossPairAllSource_ghost_two
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 2 (by norm_num)
        (deningerBigWittCrossPairAllSource a s) = 0 := by
  rw [deningerBigWittCrossPairAllSource]
  simp only [map_sum, deningerBigWittTeichmullerCrossEffect_ghost_two]
  let L := ∑ p ∈ s, ∑ q ∈ s, deningerBigWittCrossPairLeftLeg a p q
  let R := ∑ r ∈ s, ∑ t ∈ s, deningerBigWittCrossPairRightLeg a r t
  have hfactor :
      (∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, ∑ t ∈ s,
        -2 * deningerBigWittCrossPairLeftLeg a p q * deningerBigWittCrossPairRightLeg a r t) =
      -2 * L * R := by
    have hinner : ∀ p ∈ s, ∀ q ∈ s,
        (∑ r ∈ s, ∑ t ∈ s,
          -2 * deningerBigWittCrossPairLeftLeg a p q * deningerBigWittCrossPairRightLeg a r t) =
        -2 * deningerBigWittCrossPairLeftLeg a p q * R := by
      intro p hp q hq
      dsimp only [R]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
    calc
      (∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, ∑ t ∈ s,
          -2 * deningerBigWittCrossPairLeftLeg a p q * deningerBigWittCrossPairRightLeg a r t) =
          ∑ p ∈ s, ∑ q ∈ s,
            -2 * deningerBigWittCrossPairLeftLeg a p q * R := by
              apply Finset.sum_congr rfl
              intro p hp
              apply Finset.sum_congr rfl
              intro q hq
              exact hinner p hp q hq
      _ = -2 * L * R := by
          dsimp only [L]
          rw [show -2 * (∑ p ∈ s, ∑ q ∈ s, deningerBigWittCrossPairLeftLeg a p q) * R =
              (∑ p ∈ s, ∑ q ∈ s, deningerBigWittCrossPairLeftLeg a p q) * (-2 * R) by ring]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro q hq
          ring
  have hL : L = 0 := deningerBigWittCrossPairLeftLeg_total_zero a s
  have hR : R = 0 := deningerBigWittCrossPairRightLeg_total_zero a s
  rw [hfactor, hL, hR]
  ring

/-- Product of the two oriented legs is exactly one physical
reciprocal-prime Dirichlet atom. -/
theorem deningerBigWittCrossPairLeg_product_eq_physical
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    deningerBigWittCrossPairLeftLeg a p q * deningerBigWittCrossPairRightLeg a p q =
      ((deningerBigWittPrimePairExtendedPhysicalAtom p q *
        ‖a p - a q‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [deningerBigWittCrossPairLeftLeg, deningerBigWittCrossPairRightLeg,
    deningerBigWittPrimePairExtendedPhysicalAtom_eq,
    ← Complex.normSq_eq_norm_sq]
  push_cast
  rw [← Complex.mul_conj]
  ring

theorem deningerBigWittCrossPairDiagonalSource_ghost_two
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 2 (by norm_num)
        (deningerBigWittCrossPairDiagonalSource a s) =
      ((-2 * deningerBigWittPrimeSeamSourceEnergy a s : ℝ) : ℂ) := by
  rw [deningerBigWittCrossPairDiagonalSource]
  simp only [map_sum, deningerBigWittTeichmullerCrossEffect_ghost_two]
  rw [deningerBigWittPrimeSeamSourceEnergy]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [show -2 * deningerBigWittCrossPairLeftLeg a p q * deningerBigWittCrossPairRightLeg a p q =
      -2 * (deningerBigWittCrossPairLeftLeg a p q * deningerBigWittCrossPairRightLeg a p q) by ring,
    deningerBigWittCrossPairLeg_product_eq_physical]
  push_cast
  ring

/-- Off-diagonal cross-pair source carries exactly the opposite of the
diagonal physical coefficient. -/
theorem deningerBigWittCrossPairOffDiagonalCompensator_ghost_two
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 2 (by norm_num)
        (deningerBigWittCrossPairOffDiagonalCompensator a s) =
      ((2 * deningerBigWittPrimeSeamSourceEnergy a s : ℝ) : ℂ) := by
  rw [deningerBigWittCrossPairOffDiagonalCompensator, map_sub,
    deningerBigWittCrossPairAllSource_ghost_two,
    deningerBigWittCrossPairDiagonalSource_ghost_two]
  push_cast
  ring

/-- Complete coherent cross-pair source lands in the first-ghost kernel after
canonical Frobenius transgression. -/
theorem deningerBigWittFrobeniusTwo_crossPairAll_ghost_one
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittFrobeniusTwoRingHom
          (deningerBigWittCrossPairAllSource a s)) = 0 := by
  rw [deningerBigWittFrobeniusTwoRingHom_ghost]
  norm_num
  exact deningerBigWittCrossPairAllSource_ghost_two a s

theorem deningerBigWittFrobeniusTwo_crossPairDiagonal_ghost_one
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittFrobeniusTwoRingHom
          (deningerBigWittCrossPairDiagonalSource a s)) =
      ((-2 * deningerBigWittPrimeSeamSourceEnergy a s : ℝ) : ℂ) := by
  rw [deningerBigWittFrobeniusTwoRingHom_ghost]
  norm_num
  simpa using deningerBigWittCrossPairDiagonalSource_ghost_two a s

theorem deningerBigWittFrobeniusTwo_crossPairOffDiagonalCompensator_ghost_one
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittFrobeniusTwoRingHom
          (deningerBigWittCrossPairOffDiagonalCompensator a s)) =
      ((2 * deningerBigWittPrimeSeamSourceEnergy a s : ℝ) : ℂ) := by
  rw [deningerBigWittFrobeniusTwoRingHom_ghost]
  norm_num
  simpa using deningerBigWittCrossPairOffDiagonalCompensator_ghost_two a s

/-- Exact source-level Frobenius decomposition into physical diagonal and
off-diagonal compensator. -/
theorem deningerBigWittFrobeniusTwo_crossPair_source_decomposition
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittFrobeniusTwoRingHom (deningerBigWittCrossPairDiagonalSource a s) +
        deningerBigWittFrobeniusTwoRingHom
          (deningerBigWittCrossPairOffDiagonalCompensator a s) =
      deningerBigWittFrobeniusTwoRingHom (deningerBigWittCrossPairAllSource a s) := by
  rw [← map_add]
  congr 1
  simp [deningerBigWittCrossPairOffDiagonalCompensator]

/-- Diagonal refactorization is coefficient-faithful to the original
polarized prime-seam aggregate. -/
theorem deningerBigWittFrobeniusTwo_crossPairDiagonal_ghost_one_eq_original
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittFrobeniusTwoRingHom
          (deningerBigWittCrossPairDiagonalSource a s)) =
      deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittFrobeniusTwo
          (deningerBigWittPolarizedPrimeSeamAggregateSource a s)) := by
  rw [deningerBigWittFrobeniusTwo_crossPairDiagonal_ghost_one,
    deningerBigWittFrobeniusTwo_polarizedAggregate_ghost_one]

/-- Exact nonlocal cancellation of physical diagonal by its off-diagonal
cross-pair compensator. -/
theorem deningerBigWittFrobeniusTwo_crossPair_cancellation_ghost_one
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittFrobeniusTwoRingHom
          (deningerBigWittCrossPairDiagonalSource a s)) +
      deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittFrobeniusTwoRingHom
          (deningerBigWittCrossPairOffDiagonalCompensator a s)) = 0 := by
  rw [deningerBigWittFrobeniusTwoRingHom_ghost,
    deningerBigWittFrobeniusTwoRingHom_ghost]
  norm_num
  rw [deningerBigWittCrossPairDiagonalSource_ghost_two,
    deningerBigWittCrossPairOffDiagonalCompensator_ghost_two]
  push_cast
  ring

end

end RHTower

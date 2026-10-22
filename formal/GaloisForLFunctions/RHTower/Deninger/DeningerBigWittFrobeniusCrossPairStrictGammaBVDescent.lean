import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittFrobeniusCrossPairCoherentCompensator
import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittFrobeniusStrictGreenBoundaryDescent

/-!
# Strict coherent cross-pair descent through Gamma/co-Poisson and BV Green transport

The coherent Big-Witt compensator has four ordered-prime labels `(p,q,r,t)`.
This module transports each such coefficient to the genuine left-edge
Calderón--Witt Gamma witness and to a literal ordinary-integer Hochschild
Green chain. The incidence coordinate and BV ground readout agree termwise.

More strongly, for every fixed left edge `(p,q)`, the complete right-edge
fiber vanishes before any global scalar sum. Its diagonal term is exactly the
physical prime-seam source, so the off-diagonal fiber is its exact negative in
both carriers. The actual Gamma boundary and co-Poisson evaluations preserve
that sign. Consequently the existing BV ground readout cannot make the
off-diagonal compensator invisible unless the physical coefficient already
vanishes. This isolates the still-missing singular one-leg trace comparison;
no RH, zero-location, positivity, or spectral-synthesis premise is used.
-/

open Complex
open scoped BigOperators TensorProduct
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section


def deningerBigWittCrossPairFrobeniusCoefficient
    (a : Nat.Primes → ℂ) (p q r t : Nat.Primes) : ℂ :=
  deningerBigWittGhostComponent 1 Nat.zero_lt_one
    (deningerBigWittFrobeniusTwoRingHom
      (deningerBigWittTeichmullerCrossEffect
        (deningerBigWittCrossPairLeftLeg a p q)
        (deningerBigWittCrossPairRightLeg a r t)))

theorem deningerBigWittCrossPairFrobeniusCoefficient_eq
    (a : Nat.Primes → ℂ) (p q r t : Nat.Primes) :
    deningerBigWittCrossPairFrobeniusCoefficient a p q r t =
      -2 * deningerBigWittCrossPairLeftLeg a p q *
        deningerBigWittCrossPairRightLeg a r t := by
  rw [deningerBigWittCrossPairFrobeniusCoefficient, deningerBigWittFrobeniusTwoRingHom_ghost]
  norm_num
  rw [deningerBigWittTeichmullerCrossEffect_ghost_two (A := ℂ)]
  ring

def deningerBigWittCrossPairFrobeniusFiberCoefficient
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes) : ℂ :=
  ∑ r ∈ s, ∑ t ∈ s, deningerBigWittCrossPairFrobeniusCoefficient a p q r t

theorem deningerBigWittCrossPairFrobeniusFiberCoefficient_zero
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes) :
    deningerBigWittCrossPairFrobeniusFiberCoefficient a s p q = 0 := by
  rw [deningerBigWittCrossPairFrobeniusFiberCoefficient]
  simp only [deningerBigWittCrossPairFrobeniusCoefficient_eq]
  let R := ∑ r ∈ s, ∑ t ∈ s, deningerBigWittCrossPairRightLeg a r t
  have hfactor :
      (∑ r ∈ s, ∑ t ∈ s,
        -2 * deningerBigWittCrossPairLeftLeg a p q *
          deningerBigWittCrossPairRightLeg a r t) =
        (-2 * deningerBigWittCrossPairLeftLeg a p q) * R := by
    dsimp only [R]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
  have hR : R = 0 := deningerBigWittCrossPairRightLeg_total_zero a s
  rw [hfactor, hR]
  ring

theorem deningerBigWittCrossPairFrobeniusCoefficient_diagonal
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    deningerBigWittCrossPairFrobeniusCoefficient a p q p q =
      deningerBigWittFrobeniusPrimeSeamPairCoefficient a p q := by
  rw [deningerBigWittCrossPairFrobeniusCoefficient_eq,
    show -2 * deningerBigWittCrossPairLeftLeg a p q *
        deningerBigWittCrossPairRightLeg a p q =
      -2 * (deningerBigWittCrossPairLeftLeg a p q *
        deningerBigWittCrossPairRightLeg a p q) by ring,
    deningerBigWittCrossPairLeg_product_eq_physical,
    deningerBigWittFrobeniusPrimeSeamPairCoefficient_eq]
  push_cast
  ring

def deningerBigWittCrossPairFrobeniusIncidenceSource
    (a : Nat.Primes → ℂ) {p q : Nat.Primes} (hpq : p ≠ q)
    (r t : Nat.Primes) : deningerCalderonWittGlobalMilnorIncidence :=
  deningerBigWittCrossPairFrobeniusCoefficient a p q r t •
    deningerCalderonWittCrossPrimeGammaWitness hpq

def deningerBigWittCrossPairFrobeniusAllFiberIncidenceSource
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    {p q : Nat.Primes} (hpq : p ≠ q) :
    deningerCalderonWittGlobalMilnorIncidence :=
  ∑ r ∈ s, ∑ t ∈ s, deningerBigWittCrossPairFrobeniusIncidenceSource a hpq r t

def deningerBigWittCrossPairFrobeniusDiagonalIncidenceSource
    (a : Nat.Primes → ℂ) {p q : Nat.Primes} (hpq : p ≠ q) :
    deningerCalderonWittGlobalMilnorIncidence :=
  deningerBigWittCrossPairFrobeniusIncidenceSource a hpq p q

def deningerBigWittCrossPairFrobeniusOffDiagonalCoefficient
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes) : ℂ :=
  deningerBigWittCrossPairFrobeniusFiberCoefficient a s p q - deningerBigWittCrossPairFrobeniusCoefficient a p q p q

theorem deningerBigWittCrossPairFrobeniusOffDiagonalCoefficient_eq_neg_physical
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes) :
    deningerBigWittCrossPairFrobeniusOffDiagonalCoefficient a s p q =
      -deningerBigWittFrobeniusPrimeSeamPairCoefficient a p q := by
  rw [deningerBigWittCrossPairFrobeniusOffDiagonalCoefficient, deningerBigWittCrossPairFrobeniusFiberCoefficient_zero,
    deningerBigWittCrossPairFrobeniusCoefficient_diagonal, zero_sub]

def deningerBigWittCrossPairFrobeniusOffDiagonalIncidenceSource
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    {p q : Nat.Primes} (hpq : p ≠ q) :
    deningerCalderonWittGlobalMilnorIncidence :=
  deningerBigWittCrossPairFrobeniusOffDiagonalCoefficient a s p q •
    deningerCalderonWittCrossPrimeGammaWitness hpq

theorem deningerBigWittCrossPairFrobeniusAllFiberIncidenceSource_zero
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    {p q : Nat.Primes} (hpq : p ≠ q) :
    deningerBigWittCrossPairFrobeniusAllFiberIncidenceSource a s hpq = 0 := by
  rw [deningerBigWittCrossPairFrobeniusAllFiberIncidenceSource]
  simp_rw [deningerBigWittCrossPairFrobeniusIncidenceSource]
  calc
    (∑ r ∈ s, ∑ t ∈ s,
        deningerBigWittCrossPairFrobeniusCoefficient a p q r t •
          deningerCalderonWittCrossPrimeGammaWitness hpq) =
        deningerBigWittCrossPairFrobeniusFiberCoefficient a s p q •
          deningerCalderonWittCrossPrimeGammaWitness hpq := by
      rw [deningerBigWittCrossPairFrobeniusFiberCoefficient]
      symm
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_smul]
    _ = 0 := by rw [deningerBigWittCrossPairFrobeniusFiberCoefficient_zero]; simp

theorem deningerBigWittCrossPairFrobeniusDiagonalIncidenceSource_eq_physical
    (a : Nat.Primes → ℂ) {p q : Nat.Primes} (hpq : p ≠ q) :
    deningerBigWittCrossPairFrobeniusDiagonalIncidenceSource a hpq =
      deningerBigWittFrobeniusPrimeSeamPairIncidenceSource a hpq := by
  rw [deningerBigWittCrossPairFrobeniusDiagonalIncidenceSource, deningerBigWittCrossPairFrobeniusIncidenceSource,
    deningerBigWittCrossPairFrobeniusCoefficient_diagonal]
  rfl

theorem deningerBigWittCrossPairFrobeniusOffDiagonalIncidenceSource_eq_neg_physical
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    {p q : Nat.Primes} (hpq : p ≠ q) :
    deningerBigWittCrossPairFrobeniusOffDiagonalIncidenceSource a s hpq =
      -deningerBigWittFrobeniusPrimeSeamPairIncidenceSource a hpq := by
  rw [deningerBigWittCrossPairFrobeniusOffDiagonalIncidenceSource,
    deningerBigWittCrossPairFrobeniusOffDiagonalCoefficient_eq_neg_physical,
    deningerBigWittFrobeniusPrimeSeamPairIncidenceSource]
  exact neg_smul (R := ℂ)
    (M := deningerCalderonWittGlobalMilnorIncidence)
    (deningerBigWittFrobeniusPrimeSeamPairCoefficient a p q)
    (deningerCalderonWittCrossPrimeGammaWitness hpq)

theorem deningerBigWittCrossPairFrobeniusIncidenceSource_coordinate
    (a : Nat.Primes → ℂ) {p q : Nat.Primes} (hpq : p ≠ q)
    (r t : Nat.Primes) :
    deningerCalderonWittCrossPrimePacketCoordinate ⟨(p, q), hpq⟩
        (deningerBigWittCrossPairFrobeniusIncidenceSource a hpq r t) =
      deningerBigWittCrossPairFrobeniusCoefficient a p q r t := by
  rw [deningerBigWittCrossPairFrobeniusIncidenceSource, map_smul]
  change deningerBigWittCrossPairFrobeniusCoefficient a p q r t *
      deningerCalderonWittCrossPrimePacketCoordinate ⟨(p, q), hpq⟩
        (deningerCalderonWittCrossPrimeGammaWitness hpq) = _
  unfold deningerCalderonWittCrossPrimePacketCoordinate
  rw [deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate_witness]
  ring

theorem deningerBigWittCrossPairFrobeniusIncidenceSource_boundaryDefect
    (a : Nat.Primes → ℂ) {p q : Nat.Primes} (hpq : p ≠ q)
    (r t : Nat.Primes) (alpha : ℝ) (e f : ℕ) :
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect alpha
        (deningerBigWittCrossPairFrobeniusIncidenceSource a hpq r t) p q e f =
      deningerBigWittCrossPairFrobeniusCoefficient a p q r t *
        (xiGammaEulerPrimitiveReflectionOddExterior
          alpha (p, e) (q, f) : ℂ) := by
  rw [deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_eq]
  simp only [deningerBigWittCrossPairFrobeniusIncidenceSource, map_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [deningerCalderonWittGammaReflectionOddScalarTransport_crossPrimeWitness]

theorem deningerBigWittCrossPairFrobeniusIncidenceSource_coPoisson
    (a : Nat.Primes → ℂ) {p q : Nat.Primes} (hpq : p ≠ q)
    (r t : Nat.Primes) (alpha : ℝ) (e f : ℕ) :
    (deningerCalderonWittGammaBoundaryVectorOrientation q
        (deningerCalderonWittGammaPolarizedVectorTransport alpha
          (deningerBigWittCrossPairFrobeniusIncidenceSource a hpq r t) p q e f)).1
        (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)) =
      deningerBigWittCrossPairFrobeniusCoefficient a p q r t *
        xiGammaEulerPrimitiveGammaCoPoissonModularExterior
          alpha (p, e) (q, f) := by
  rw [deningerCalderonWittGammaBoundaryVectorOrientation_transport_fst_eval]
  simp only [deningerBigWittCrossPairFrobeniusIncidenceSource, map_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [deningerCalderonWittGammaModularScalarTransport_crossPrimeWitness,
    xiGammaEulerPrimitiveGammaCoPoissonModularExterior_eq]

def deningerBigWittCrossPairFrobeniusBVWeight
    (a : Nat.Primes → ℂ) (p q r t : Nat.Primes) : ℂ :=
  -2 * (a p - a q) * deningerBigWittCrossPairRightLeg a r t

def deningerBigWittCrossPairFrobeniusBVGreenChain
    (a : Nat.Primes → ℂ) (p q r t : Nat.Primes) :
    DeningerOrdinaryIntegerEnd ⊗[ℂ] DeningerOrdinaryIntegerEnd :=
  deningerBigWittCrossPairFrobeniusBVWeight a p q r t •
    (deningerOrdinaryIntegerWoldBackward
        (deningerBigWittPrimePairOrdinaryDegree p q) ⊗ₜ[ℂ]
      (deningerOrdinaryIntegerReciprocalGreen *
        deningerOrdinaryIntegerWoldShift
          (deningerBigWittPrimePairOrdinaryDegree p q)))

theorem deningerBigWittCrossPairFrobeniusBVGreenChain_boundary
    (a : Nat.Primes → ℂ) (p q r t : Nat.Primes) :
    hochschildBoundaryOne (deningerBigWittCrossPairFrobeniusBVGreenChain a p q r t) =
      deningerBigWittCrossPairFrobeniusBVWeight a p q r t •
        deningerOrdinaryIntegerBVGreenStokesBoundary
          (deningerBigWittPrimePairOrdinaryDegree p q) := by
  rw [deningerBigWittCrossPairFrobeniusBVGreenChain, map_smul]
  congr 1

theorem deningerBigWittCrossPairFrobeniusBVGreenChain_groundReadout
    (a : Nat.Primes → ℂ) (p q r t : Nat.Primes) :
    deningerOrdinaryIntegerDiagonalCoefficient 1
        (hochschildBoundaryOne (deningerBigWittCrossPairFrobeniusBVGreenChain a p q r t)) =
      deningerBigWittCrossPairFrobeniusCoefficient a p q r t := by
  rw [deningerBigWittCrossPairFrobeniusBVGreenChain_boundary, map_smul,
    deningerBigWittPrimePair_bvGreen_groundCoefficient,
    deningerBigWittCrossPairFrobeniusCoefficient_eq]
  rw [deningerBigWittCrossPairFrobeniusBVWeight, deningerBigWittCrossPairLeftLeg,
    deningerBigWittPrimePairExtendedPhysicalAtom_eq]
  push_cast
  ring

theorem deningerBigWittCrossPairFrobeniusStrictDescent
    (a : Nat.Primes → ℂ) {p q : Nat.Primes} (hpq : p ≠ q)
    (r t : Nat.Primes) :
    deningerCalderonWittCrossPrimePacketCoordinate ⟨(p, q), hpq⟩
        (deningerBigWittCrossPairFrobeniusIncidenceSource a hpq r t) =
      deningerOrdinaryIntegerDiagonalCoefficient 1
        (hochschildBoundaryOne (deningerBigWittCrossPairFrobeniusBVGreenChain a p q r t)) := by
  rw [deningerBigWittCrossPairFrobeniusIncidenceSource_coordinate,
    deningerBigWittCrossPairFrobeniusBVGreenChain_groundReadout]

theorem deningerBigWittCrossPairFrobeniusBVWeight_diagonal
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    deningerBigWittCrossPairFrobeniusBVWeight a p q p q =
      deningerBigWittFrobeniusPrimeSeamPairBVWeight a p q := by
  rw [deningerBigWittCrossPairFrobeniusBVWeight, deningerBigWittCrossPairRightLeg,
    deningerBigWittFrobeniusPrimeSeamPairBVWeight,
    ← Complex.normSq_eq_norm_sq]
  push_cast
  rw [← Complex.mul_conj]
  ring

def deningerBigWittCrossPairFrobeniusFiberBVWeight
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes) : ℂ :=
  ∑ r ∈ s, ∑ t ∈ s, deningerBigWittCrossPairFrobeniusBVWeight a p q r t

theorem deningerBigWittCrossPairFrobeniusFiberBVWeight_zero
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes) :
    deningerBigWittCrossPairFrobeniusFiberBVWeight a s p q = 0 := by
  rw [deningerBigWittCrossPairFrobeniusFiberBVWeight]
  simp only [deningerBigWittCrossPairFrobeniusBVWeight]
  let R := ∑ r ∈ s, ∑ t ∈ s, deningerBigWittCrossPairRightLeg a r t
  have hfactor :
      (∑ r ∈ s, ∑ t ∈ s,
        -2 * (a p - a q) * deningerBigWittCrossPairRightLeg a r t) =
        (-2 * (a p - a q)) * R := by
    dsimp only [R]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
  have hR : R = 0 := deningerBigWittCrossPairRightLeg_total_zero a s
  rw [hfactor, hR]
  ring

def deningerBigWittCrossPairFrobeniusAllFiberBVGreenChain
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes) :
    DeningerOrdinaryIntegerEnd ⊗[ℂ] DeningerOrdinaryIntegerEnd :=
  ∑ r ∈ s, ∑ t ∈ s, deningerBigWittCrossPairFrobeniusBVGreenChain a p q r t

theorem deningerBigWittCrossPairFrobeniusAllFiberBVGreenChain_zero
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes) :
    deningerBigWittCrossPairFrobeniusAllFiberBVGreenChain a s p q = 0 := by
  rw [deningerBigWittCrossPairFrobeniusAllFiberBVGreenChain]
  simp_rw [deningerBigWittCrossPairFrobeniusBVGreenChain]
  let B :=
    deningerOrdinaryIntegerWoldBackward
        (deningerBigWittPrimePairOrdinaryDegree p q) ⊗ₜ[ℂ]
      (deningerOrdinaryIntegerReciprocalGreen *
        deningerOrdinaryIntegerWoldShift
          (deningerBigWittPrimePairOrdinaryDegree p q))
  calc
    (∑ r ∈ s, ∑ t ∈ s, deningerBigWittCrossPairFrobeniusBVWeight a p q r t • B) =
        deningerBigWittCrossPairFrobeniusFiberBVWeight a s p q • B := by
      rw [deningerBigWittCrossPairFrobeniusFiberBVWeight]
      symm
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_smul]
    _ = 0 := by rw [deningerBigWittCrossPairFrobeniusFiberBVWeight_zero]; simp

def deningerBigWittCrossPairFrobeniusOffDiagonalBVWeight
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes) : ℂ :=
  deningerBigWittCrossPairFrobeniusFiberBVWeight a s p q - deningerBigWittCrossPairFrobeniusBVWeight a p q p q

theorem deningerBigWittCrossPairFrobeniusOffDiagonalBVWeight_eq_neg_physical
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes) :
    deningerBigWittCrossPairFrobeniusOffDiagonalBVWeight a s p q =
      -deningerBigWittFrobeniusPrimeSeamPairBVWeight a p q := by
  rw [deningerBigWittCrossPairFrobeniusOffDiagonalBVWeight, deningerBigWittCrossPairFrobeniusFiberBVWeight_zero,
    deningerBigWittCrossPairFrobeniusBVWeight_diagonal, zero_sub]

def deningerBigWittCrossPairFrobeniusOffDiagonalBVGreenChain
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes) :
    DeningerOrdinaryIntegerEnd ⊗[ℂ] DeningerOrdinaryIntegerEnd :=
  deningerBigWittCrossPairFrobeniusOffDiagonalBVWeight a s p q •
    (deningerOrdinaryIntegerWoldBackward
        (deningerBigWittPrimePairOrdinaryDegree p q) ⊗ₜ[ℂ]
      (deningerOrdinaryIntegerReciprocalGreen *
        deningerOrdinaryIntegerWoldShift
          (deningerBigWittPrimePairOrdinaryDegree p q)))

theorem deningerBigWittCrossPairFrobeniusOffDiagonalBVGreenChain_eq_neg_physical
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes) :
    deningerBigWittCrossPairFrobeniusOffDiagonalBVGreenChain a s p q =
      -deningerBigWittFrobeniusPrimeSeamPairBVGreenChain a p q := by
  rw [deningerBigWittCrossPairFrobeniusOffDiagonalBVGreenChain,
    deningerBigWittCrossPairFrobeniusOffDiagonalBVWeight_eq_neg_physical,
    deningerBigWittFrobeniusPrimeSeamPairBVGreenChain]
  exact neg_smul (R := ℂ)
    (M := DeningerOrdinaryIntegerEnd ⊗[ℂ] DeningerOrdinaryIntegerEnd)
    (deningerBigWittFrobeniusPrimeSeamPairBVWeight a p q)
    (deningerOrdinaryIntegerWoldBackward
        (deningerBigWittPrimePairOrdinaryDegree p q) ⊗ₜ[ℂ]
      (deningerOrdinaryIntegerReciprocalGreen *
        deningerOrdinaryIntegerWoldShift
          (deningerBigWittPrimePairOrdinaryDegree p q)))

theorem deningerBigWittCrossPairFrobeniusOffDiagonalBVGreenChain_groundReadout
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes) :
    deningerOrdinaryIntegerDiagonalCoefficient 1
        (hochschildBoundaryOne (deningerBigWittCrossPairFrobeniusOffDiagonalBVGreenChain a s p q)) =
      -deningerBigWittFrobeniusPrimeSeamPairCoefficient a p q := by
  rw [deningerBigWittCrossPairFrobeniusOffDiagonalBVGreenChain_eq_neg_physical, map_neg, map_neg,
    deningerBigWittFrobeniusPrimeSeamPairBVGreenChain_groundReadout]

theorem deningerBigWittCrossPairFrobeniusOffDiagonalIncidenceSource_boundaryDefect
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    {p q : Nat.Primes} (hpq : p ≠ q) (alpha : ℝ) (e f : ℕ) :
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect alpha
        (deningerBigWittCrossPairFrobeniusOffDiagonalIncidenceSource a s hpq) p q e f =
      -(deningerBigWittFrobeniusPrimeSeamPairCoefficient a p q *
        (xiGammaEulerPrimitiveReflectionOddExterior
          alpha (p, e) (q, f) : ℂ)) := by
  rw [deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_eq]
  simp only [deningerBigWittCrossPairFrobeniusOffDiagonalIncidenceSource, map_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [deningerCalderonWittGammaReflectionOddScalarTransport_crossPrimeWitness,
    deningerBigWittCrossPairFrobeniusOffDiagonalCoefficient_eq_neg_physical]
  ring

theorem deningerBigWittCrossPairFrobeniusOffDiagonalIncidenceSource_coPoisson
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    {p q : Nat.Primes} (hpq : p ≠ q) (alpha : ℝ) (e f : ℕ) :
    (deningerCalderonWittGammaBoundaryVectorOrientation q
        (deningerCalderonWittGammaPolarizedVectorTransport alpha
          (deningerBigWittCrossPairFrobeniusOffDiagonalIncidenceSource a s hpq) p q e f)).1
        (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)) =
      -(deningerBigWittFrobeniusPrimeSeamPairCoefficient a p q *
        xiGammaEulerPrimitiveGammaCoPoissonModularExterior
          alpha (p, e) (q, f)) := by
  rw [deningerCalderonWittGammaBoundaryVectorOrientation_transport_fst_eval]
  simp only [deningerBigWittCrossPairFrobeniusOffDiagonalIncidenceSource, map_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [deningerCalderonWittGammaModularScalarTransport_crossPrimeWitness,
    xiGammaEulerPrimitiveGammaCoPoissonModularExterior_eq,
    deningerBigWittCrossPairFrobeniusOffDiagonalCoefficient_eq_neg_physical]
  ring

theorem deningerBigWittCrossPairFrobeniusOffDiagonalStrictDescent
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    {p q : Nat.Primes} (hpq : p ≠ q) :
    deningerCalderonWittCrossPrimePacketCoordinate ⟨(p, q), hpq⟩
        (deningerBigWittCrossPairFrobeniusOffDiagonalIncidenceSource a s hpq) =
      deningerOrdinaryIntegerDiagonalCoefficient 1
        (hochschildBoundaryOne
          (deningerBigWittCrossPairFrobeniusOffDiagonalBVGreenChain a s p q)) := by
  rw [deningerBigWittCrossPairFrobeniusOffDiagonalIncidenceSource, map_smul]
  change deningerBigWittCrossPairFrobeniusOffDiagonalCoefficient a s p q *
      deningerCalderonWittCrossPrimePacketCoordinate ⟨(p, q), hpq⟩
        (deningerCalderonWittCrossPrimeGammaWitness hpq) = _
  unfold deningerCalderonWittCrossPrimePacketCoordinate
  rw [deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate_witness,
    mul_one, deningerBigWittCrossPairFrobeniusOffDiagonalCoefficient_eq_neg_physical,
    deningerBigWittCrossPairFrobeniusOffDiagonalBVGreenChain_groundReadout]

theorem deningerBigWittCrossPairFrobenius_groundReadout_invisibility_iff_physical_zero
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes) :
    deningerOrdinaryIntegerDiagonalCoefficient 1
          (hochschildBoundaryOne (deningerBigWittCrossPairFrobeniusOffDiagonalBVGreenChain a s p q)) = 0 ↔
      deningerBigWittFrobeniusPrimeSeamPairCoefficient a p q = 0 := by
  rw [deningerBigWittCrossPairFrobeniusOffDiagonalBVGreenChain_groundReadout, neg_eq_zero]

end

end RHTower


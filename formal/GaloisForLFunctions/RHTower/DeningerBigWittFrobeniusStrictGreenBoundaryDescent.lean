import GaloisForLFunctions.RHTower.DeningerBigWittFrobeniusPrimeSeamTransgression
import GaloisForLFunctions.RHTower.DeningerCalderonWittGammaCoPoissonHodgeBoundaryComparison
import GaloisForLFunctions.RHTower.RouteRDegreeSixBVGreenNeutralFinitePart

/-!
# Strict Big-Witt source descent to Green--Stokes boundaries

This module constructs one finite polarized prime-seam source in two genuine
chain-level realizations. Its ordered coefficients are recovered exactly by
the actual Calderón--Witt incidence coordinates and transported by the actual
Gamma/co-Poisson Hodge boundary. Independently, the same coefficients are the
ground-state readout of literal ordinary-integer Hochschild boundaries. The
finite aggregate identity is proved before scalarization, so no cancellation,
ghost injectivity, torsion-freeness, or RH-equivalent premise is imported.
-/

open Complex
open scoped BigOperators TensorProduct
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Positive ordinary-integer degree attached to an ordered prime pair. -/
def deningerBigWittPrimePairOrdinaryDegree (p q : Nat.Primes) : PNat :=
  ⟨(p : ℕ) * (q : ℕ), Nat.mul_pos p.prop.pos q.prop.pos⟩

@[simp] theorem deningerBigWittPrimePairOrdinaryDegree_coe
    (p q : Nat.Primes) :
    (deningerBigWittPrimePairOrdinaryDegree p q : ℕ) =
      (p : ℕ) * (q : ℕ) := rfl

/-- First ghost of the Frobenius-transgressed polarized pair source. -/
def deningerBigWittFrobeniusPrimeSeamPairCoefficient
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) : ℂ :=
  deningerBigWittGhostComponent 1 Nat.zero_lt_one
    (deningerBigWittFrobeniusTwo
      (deningerBigWittPolarizedPrimeSeamPairSource a p q))

theorem deningerBigWittFrobeniusPrimeSeamPairCoefficient_eq
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    deningerBigWittFrobeniusPrimeSeamPairCoefficient a p q =
      ((-2 * deningerBigWittPrimePairExtendedPhysicalAtom p q *
        ‖a p - a q‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [deningerBigWittFrobeniusPrimeSeamPairCoefficient,
    deningerBigWittFrobeniusTwo_ghost_one,
    deningerBigWittPolarizedPrimeSeamPairSource_ghost_two]

/-- Ordered Calderón--Witt incidence source carrying the transgressed
physical pair coefficient before any scalar aggregate. -/
def deningerBigWittFrobeniusPrimeSeamPairIncidenceSource
    (a : Nat.Primes → ℂ) {p q : Nat.Primes} (hpq : p ≠ q) :
    deningerCalderonWittGlobalMilnorIncidence :=
  deningerBigWittFrobeniusPrimeSeamPairCoefficient a p q •
    deningerCalderonWittCrossPrimeGammaWitness hpq

/-- Actual Gamma/co-Poisson Hodge-boundary defect reads the new source
coefficient without alteration and multiplies it by its genuine modular
exterior. -/
theorem deningerBigWittFrobeniusPrimeSeamPairIncidence_boundaryDefect
    (a : Nat.Primes → ℂ) {p q : Nat.Primes} (hpq : p ≠ q)
    (alpha : ℝ) (e f : ℕ) :
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect alpha
        (deningerBigWittFrobeniusPrimeSeamPairIncidenceSource a hpq)
        p q e f =
      deningerBigWittFrobeniusPrimeSeamPairCoefficient a p q *
        (xiGammaEulerPrimitiveReflectionOddExterior
          alpha (p, e) (q, f) : ℂ) := by
  rw [deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_eq]
  simp only [deningerBigWittFrobeniusPrimeSeamPairIncidenceSource,
    map_smul, Pi.smul_apply, smul_eq_mul]
  rw [deningerCalderonWittGammaReflectionOddScalarTransport_crossPrimeWitness]

/-- The same source coefficient is preserved by the actual oriented
Gamma/co-Poisson moving-boundary head evaluation. -/
theorem deningerBigWittFrobeniusPrimeSeamPairIncidence_coPoisson
    (a : Nat.Primes → ℂ) {p q : Nat.Primes} (hpq : p ≠ q)
    (alpha : ℝ) (e f : ℕ) :
    (deningerCalderonWittGammaBoundaryVectorOrientation q
        (deningerCalderonWittGammaPolarizedVectorTransport alpha
          (deningerBigWittFrobeniusPrimeSeamPairIncidenceSource a hpq)
          p q e f)).1
        (xiGammaEulerPrimitivePolarizedPairAction (p, e) (q, f)) =
      deningerBigWittFrobeniusPrimeSeamPairCoefficient a p q *
        xiGammaEulerPrimitiveGammaCoPoissonModularExterior
          alpha (p, e) (q, f) := by
  rw [deningerCalderonWittGammaBoundaryVectorOrientation_transport_fst_eval]
  simp only [deningerBigWittFrobeniusPrimeSeamPairIncidenceSource,
    map_smul, Pi.smul_apply, smul_eq_mul]
  rw [deningerCalderonWittGammaModularScalarTransport_crossPrimeWitness,
    xiGammaEulerPrimitiveGammaCoPoissonModularExterior_eq]

/-- Finite ordered incidence source. Diagonal pairs contribute zero and are
omitted because the Calderón--Witt packet remembers only cross-prime labels. -/
def deningerBigWittFrobeniusPrimeSeamFiniteIncidenceSource
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerCalderonWittGlobalMilnorIncidence :=
  ∑ p ∈ s, ∑ q ∈ s,
    if hpq : p ≠ q then
      deningerBigWittFrobeniusPrimeSeamPairIncidenceSource a hpq
    else 0

private theorem deningerBigWittFrobeniusPrimeSeamPairIncidenceSource_coordinate
    (a : Nat.Primes → ℂ) (i : DeningerCalderonWittCrossPrimePacketIndex)
    (p q : Nat.Primes) :
    deningerCalderonWittCrossPrimePacketCoordinate i
        (if hpq : p ≠ q then
          deningerBigWittFrobeniusPrimeSeamPairIncidenceSource a hpq
        else 0) =
      if i.1.1 = p ∧ i.1.2 = q then
        deningerBigWittFrobeniusPrimeSeamPairCoefficient a p q
      else 0 := by
  classical
  by_cases hpq : p ≠ q
  · rw [dif_pos hpq]
    simp only [deningerBigWittFrobeniusPrimeSeamPairIncidenceSource,
      map_smul, smul_eq_mul]
    unfold deningerCalderonWittCrossPrimePacketCoordinate
    by_cases hp : i.1.1 = p
    · by_cases hq : i.1.2 = q
      · rw [if_pos ⟨hp, hq⟩]
        subst p
        subst q
        rw [deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate_witness,
          mul_one]
      · rw [if_neg (fun h => hq h.2)]
        rw [deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate_witness_of_ne,
          mul_zero]
        exact fun hpair => hq (Prod.mk.inj hpair).2
    · rw [if_neg (fun h => hp h.1)]
      rw [deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate_witness_of_ne,
        mul_zero]
      exact fun hpair => hp (Prod.mk.inj hpair).1
  · rw [dif_neg hpq, map_zero]
    rw [if_neg]
    rintro ⟨hp, hq⟩
    apply i.2
    calc
      i.1.1 = p := hp
      _ = q := not_ne_iff.mp hpq
      _ = i.1.2 := hq.symm

/-- Every ordered packet coordinate of the finite incidence source is the
corresponding Frobenius-transgressed physical pair coefficient. -/
theorem deningerBigWittFrobeniusPrimeSeamFiniteIncidenceSource_coordinate
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerCalderonWittCrossPrimePacketCoordinate i
        (deningerBigWittFrobeniusPrimeSeamFiniteIncidenceSource a s) =
      if i.1.1 ∈ s ∧ i.1.2 ∈ s then
        deningerBigWittFrobeniusPrimeSeamPairCoefficient a i.1.1 i.1.2
      else 0 := by
  classical
  simp only [deningerBigWittFrobeniusPrimeSeamFiniteIncidenceSource,
    map_sum]
  simp_rw [deningerBigWittFrobeniusPrimeSeamPairIncidenceSource_coordinate]
  by_cases hi1 : i.1.1 ∈ s
  · by_cases hi2 : i.1.2 ∈ s
    · rw [if_pos ⟨hi1, hi2⟩]
      rw [Finset.sum_eq_single i.1.1]
      · rw [Finset.sum_eq_single i.1.2]
        · simp
        · intro q hqs hq
          rw [if_neg]
          exact fun h => hq h.2.symm
        · exact fun h => (h hi2).elim
      · intro p hps hp
        apply Finset.sum_eq_zero
        intro q hqs
        rw [if_neg]
        exact fun h => hp h.1.symm
      · exact fun h => (h hi1).elim
    · rw [if_neg (fun h => hi2 h.2)]
      apply Finset.sum_eq_zero
      intro p hps
      apply Finset.sum_eq_zero
      intro q hqs
      rw [if_neg]
      intro h
      apply hi2
      rw [h.2]
      exact hqs
  · rw [if_neg (fun h => hi1 h.1)]
    apply Finset.sum_eq_zero
    intro p hps
    apply Finset.sum_eq_zero
    intro q hqs
    rw [if_neg]
    intro h
    apply hi1
    rw [h.1]
    exact hps

/-- Source polarization weight before the ordinary-integer boundary inserts
its reciprocal degree. -/
def deningerBigWittFrobeniusPrimeSeamPairBVWeight
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) : ℂ :=
  ((-2 * ‖a p - a q‖ ^ (2 : ℕ) : ℝ) : ℂ)

/-- Ordinary-integer degree-`pq` Hochschild chain whose boundary vacuum
coefficient is the transgressed physical pair coefficient. -/
def deningerBigWittFrobeniusPrimeSeamPairBVGreenChain
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    DeningerOrdinaryIntegerEnd ⊗[ℂ] DeningerOrdinaryIntegerEnd :=
  deningerBigWittFrobeniusPrimeSeamPairBVWeight a p q •
    (deningerOrdinaryIntegerWoldBackward
        (deningerBigWittPrimePairOrdinaryDegree p q) ⊗ₜ[ℂ]
      (deningerOrdinaryIntegerReciprocalGreen *
        deningerOrdinaryIntegerWoldShift
          (deningerBigWittPrimePairOrdinaryDegree p q)))

theorem deningerBigWittPrimePairOrdinaryDegree_not_dvd_one
    (p q : Nat.Primes) :
    ¬ (p : PNat) * (q : PNat) ∣ (1 : PNat) := by
  rintro ⟨k, hk⟩
  have hkNat : (1 : ℕ) =
      ((p : ℕ) * (q : ℕ)) * (k : ℕ) :=
    congrArg (fun x : PNat => (x : ℕ)) hk
  have hp := p.prop.two_le
  have hq := q.prop.two_le
  have hkpos : 0 < (k : ℕ) := k.prop
  have hkge : 1 ≤ (k : ℕ) := hkpos
  have hprod : 4 ≤ (p : ℕ) * (q : ℕ) * (k : ℕ) := by
    calc
      4 = 2 * 2 * 1 := by norm_num
      _ ≤ (p : ℕ) * (q : ℕ) * (k : ℕ) :=
        Nat.mul_le_mul (Nat.mul_le_mul hp hq) hkge
  omega

/-- Vacuum coefficient of the literal degree-`pq` BV--Green boundary is
exactly the canonical reciprocal-prime Big-Witt atom. -/
theorem deningerBigWittPrimePair_bvGreen_groundCoefficient
    (p q : Nat.Primes) :
    deningerOrdinaryIntegerDiagonalCoefficient 1
        (deningerOrdinaryIntegerBVGreenStokesBoundary
          (deningerBigWittPrimePairOrdinaryDegree p q)) =
      (deningerBigWittPrimePairExtendedPhysicalAtom p q : ℂ) := by
  rw [deningerOrdinaryIntegerBVGreenDiagonalCoefficient_eq_operator]
  simp only [deningerOrdinaryIntegerBVGreenDiagonalCoefficient,
    deningerBigWittPrimePairOrdinaryDegree_coe]
  split_ifs with hdiv
  · have hle : (p : ℕ) * (q : ℕ) ≤ 1 :=
      Nat.le_of_dvd Nat.one_pos hdiv
    have hp := p.prop.two_le
    have hq := q.prop.two_le
    have hprod : 4 ≤ (p : ℕ) * (q : ℕ) := by
      calc
        4 = 2 * 2 := by norm_num
        _ ≤ (p : ℕ) * (q : ℕ) := Nat.mul_le_mul hp hq
    omega
  rw [deningerBigWittPrimePairExtendedPhysicalAtom_eq]
  push_cast
  ring

/-- Hochschild boundary of the pair chain is the actual ordinary-integer
BV--Green commutator with the same source coefficient. -/
theorem deningerBigWittFrobeniusPrimeSeamPairBVGreenChain_boundary
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    hochschildBoundaryOne
        (deningerBigWittFrobeniusPrimeSeamPairBVGreenChain a p q) =
      deningerBigWittFrobeniusPrimeSeamPairBVWeight a p q •
        deningerOrdinaryIntegerBVGreenStokesBoundary
          (deningerBigWittPrimePairOrdinaryDegree p q) := by
  rw [deningerBigWittFrobeniusPrimeSeamPairBVGreenChain, map_smul]
  congr 1

/-- The ground-state readout of the actual Hochschild boundary is exactly
the Frobenius-transgressed first ghost. -/
theorem deningerBigWittFrobeniusPrimeSeamPairBVGreenChain_groundReadout
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    deningerOrdinaryIntegerDiagonalCoefficient 1
        (hochschildBoundaryOne
          (deningerBigWittFrobeniusPrimeSeamPairBVGreenChain a p q)) =
      deningerBigWittFrobeniusPrimeSeamPairCoefficient a p q := by
  rw [deningerBigWittFrobeniusPrimeSeamPairBVGreenChain_boundary,
    map_smul, deningerBigWittPrimePair_bvGreen_groundCoefficient]
  rw [deningerBigWittFrobeniusPrimeSeamPairBVWeight,
    deningerBigWittFrobeniusPrimeSeamPairCoefficient_eq]
  push_cast
  ring

/-- Finite ordinary-integer Hochschild chain carrying all ordered prime-pair
source coefficients before the vacuum readout. -/
def deningerBigWittFrobeniusPrimeSeamFiniteBVGreenChain
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    DeningerOrdinaryIntegerEnd ⊗[ℂ] DeningerOrdinaryIntegerEnd :=
  ∑ p ∈ s, ∑ q ∈ s,
    deningerBigWittFrobeniusPrimeSeamPairBVGreenChain a p q

/-- Vacuum readout of the finite Hochschild boundary is exactly the first
ghost of the Frobenius-transgressed polarized Big-Witt aggregate. -/
theorem deningerBigWittFrobeniusPrimeSeamFiniteBVGreenChain_groundReadout
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerOrdinaryIntegerDiagonalCoefficient 1
        (hochschildBoundaryOne
          (deningerBigWittFrobeniusPrimeSeamFiniteBVGreenChain a s)) =
      deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittFrobeniusTwo
          (deningerBigWittPolarizedPrimeSeamAggregateSource a s)) := by
  rw [deningerBigWittFrobeniusTwo_polarizedAggregate_ghost_one]
  simp only [deningerBigWittFrobeniusPrimeSeamFiniteBVGreenChain,
    map_sum]
  simp_rw [deningerBigWittFrobeniusPrimeSeamPairBVGreenChain_groundReadout,
    deningerBigWittFrobeniusPrimeSeamPairCoefficient_eq]
  rw [deningerBigWittPrimeSeamSourceEnergy, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring

end

end RHTower

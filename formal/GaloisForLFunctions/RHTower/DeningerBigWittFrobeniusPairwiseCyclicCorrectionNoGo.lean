import GaloisForLFunctions.RHTower.DeningerBigWittFrobeniusStrictGreenBoundaryDescent

/-!
# Pairwise cyclic correction no-go for Frobenius-transgressed seam source

At degree `pq`, normalization on reciprocal Green density and cyclic
annihilation uniquely determine a reader in the minimal span of the ground
and degree-`pq` diagonal evaluations. The correction from this canonical
cyclic reader to the fixed physical ground reader is exactly the full
Frobenius-transgressed pair coefficient. Consequently, finite and cofinal
pairwise correction retains the entire physical residue. Any successful
Route-L Stokes descent must therefore couple distinct prime pairs through a
singular nonlocal completion; independent degreewise cyclic repairs cannot
produce submass.
-/

open Complex Filter Topology
open scoped BigOperators TensorProduct
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Two-coordinate reader at ground state and physical ordinary degree `pq`. -/
def deningerBigWittPrimePairDiagonalReader
    (p q : Nat.Primes) (alpha beta : ℂ) :
    DeningerOrdinaryIntegerEnd →ₗ[ℂ] ℂ :=
  alpha • deningerOrdinaryIntegerDiagonalCoefficient 1 +
    beta • deningerOrdinaryIntegerDiagonalCoefficient
      (deningerBigWittPrimePairOrdinaryDegree p q)

/-- Degree-`pq` diagonal of literal BV--Green boundary. -/
theorem deningerBigWittPrimePair_bvGreen_degreeCoefficient
    (p q : Nat.Primes) :
    deningerOrdinaryIntegerDiagonalCoefficient
        (deningerBigWittPrimePairOrdinaryDegree p q)
        (deningerOrdinaryIntegerBVGreenStokesBoundary
          (deningerBigWittPrimePairOrdinaryDegree p q)) =
      ((((p : ℕ) * (q : ℕ) : ℕ) : ℂ))⁻¹ ^ 2 -
        ((((p : ℕ) * (q : ℕ) : ℕ) : ℂ))⁻¹ := by
  rw [deningerOrdinaryIntegerBVGreenDiagonalCoefficient_eq_operator]
  simp only [deningerOrdinaryIntegerBVGreenDiagonalCoefficient,
    deningerBigWittPrimePairOrdinaryDegree_coe]
  rw [if_pos (dvd_refl ((p : ℕ) * (q : ℕ)))]
  push_cast
  ring

/-- Evaluation on reciprocal Green density. -/
theorem deningerBigWittPrimePairDiagonalReader_reciprocalGreen
    (p q : Nat.Primes) (alpha beta : ℂ) :
    deningerBigWittPrimePairDiagonalReader p q alpha beta
        deningerOrdinaryIntegerReciprocalGreen =
      alpha + beta * ((((p : ℕ) * (q : ℕ) : ℕ) : ℂ))⁻¹ := by
  rw [deningerBigWittPrimePairDiagonalReader,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    deningerOrdinaryIntegerDiagonalCoefficient_reciprocalGreen,
    deningerOrdinaryIntegerDiagonalCoefficient_reciprocalGreen]
  simp only [deningerBigWittPrimePairOrdinaryDegree_coe]
  norm_num

/-- Evaluation on literal degree-`pq` BV--Green boundary. -/
theorem deningerBigWittPrimePairDiagonalReader_boundary
    (p q : Nat.Primes) (alpha beta : ℂ) :
    deningerBigWittPrimePairDiagonalReader p q alpha beta
        (deningerOrdinaryIntegerBVGreenStokesBoundary
          (deningerBigWittPrimePairOrdinaryDegree p q)) =
      alpha * ((((p : ℕ) * (q : ℕ) : ℕ) : ℂ))⁻¹ +
        beta *
          (((((p : ℕ) * (q : ℕ) : ℕ) : ℂ))⁻¹ ^ 2 -
            ((((p : ℕ) * (q : ℕ) : ℕ) : ℂ))⁻¹) := by
  rw [deningerBigWittPrimePairDiagonalReader,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    deningerBigWittPrimePair_bvGreen_groundCoefficient,
    deningerBigWittPrimePair_bvGreen_degreeCoefficient,
    deningerBigWittPrimePairExtendedPhysicalAtom_eq]
  push_cast
  ring

/-- Canonical degree-adapted cyclic reader. -/
def deningerBigWittPrimePairCanonicalCyclicReader
    (p q : Nat.Primes) : DeningerOrdinaryIntegerEnd →ₗ[ℂ] ℂ :=
  deningerBigWittPrimePairDiagonalReader p q
    (1 - ((((p : ℕ) * (q : ℕ) : ℕ) : ℂ))⁻¹) 1

theorem deningerBigWittPrimePairCanonicalCyclicReader_reciprocalGreen
    (p q : Nat.Primes) :
    deningerBigWittPrimePairCanonicalCyclicReader p q
        deningerOrdinaryIntegerReciprocalGreen = 1 := by
  rw [deningerBigWittPrimePairCanonicalCyclicReader,
    deningerBigWittPrimePairDiagonalReader_reciprocalGreen]
  ring

theorem deningerBigWittPrimePairCanonicalCyclicReader_boundary
    (p q : Nat.Primes) :
    deningerBigWittPrimePairCanonicalCyclicReader p q
        (deningerOrdinaryIntegerBVGreenStokesBoundary
          (deningerBigWittPrimePairOrdinaryDegree p q)) = 0 := by
  rw [deningerBigWittPrimePairCanonicalCyclicReader,
    deningerBigWittPrimePairDiagonalReader_boundary]
  ring

/-- Normalization and cyclic annihilation uniquely force canonical reader
inside minimal span of ground and degree-`pq` diagonals. -/
theorem deningerBigWittPrimePairDiagonalReader_normalized_cyclic_iff
    (p q : Nat.Primes) (alpha beta : ℂ) :
    (deningerBigWittPrimePairDiagonalReader p q alpha beta
          deningerOrdinaryIntegerReciprocalGreen = 1 ∧
      deningerBigWittPrimePairDiagonalReader p q alpha beta
          (deningerOrdinaryIntegerBVGreenStokesBoundary
            (deningerBigWittPrimePairOrdinaryDegree p q)) = 0) ↔
      alpha = 1 - ((((p : ℕ) * (q : ℕ) : ℕ) : ℂ))⁻¹ ∧ beta = 1 := by
  rw [deningerBigWittPrimePairDiagonalReader_reciprocalGreen,
    deningerBigWittPrimePairDiagonalReader_boundary]
  let n : ℂ := (((p : ℕ) * (q : ℕ) : ℕ) : ℂ)
  have hnNat : (p : ℕ) * (q : ℕ) ≠ 0 :=
    Nat.mul_ne_zero p.prop.ne_zero q.prop.ne_zero
  have hn : n ≠ 0 := by
    dsimp only [n]
    exact_mod_cast hnNat
  constructor
  · rintro ⟨hnorm, hcyclic⟩
    have hnorm' := hnorm
    have hcyclic' := hcyclic
    change alpha + beta * n⁻¹ = 1 at hnorm'
    change alpha * n⁻¹ + beta * (n⁻¹ ^ 2 - n⁻¹) = 0 at hcyclic'
    field_simp [hn] at hnorm' hcyclic'
    have hbetaMul : beta * n = n := by
      linear_combination hnorm' - hcyclic'
    have hbeta : beta = 1 := by
      calc
        beta = beta * n / n := by field_simp [hn]
        _ = n / n := by rw [hbetaMul]
        _ = 1 := div_self hn
    refine ⟨?_, hbeta⟩
    subst beta
    change alpha = 1 - n⁻¹
    field_simp [hn]
    linear_combination hnorm'
  · rintro ⟨rfl, rfl⟩
    constructor <;> ring

/-- Fixed physical ground readout differs from unique canonical cyclic reader
by exactly the Frobenius-transgressed pair coefficient. -/
theorem deningerBigWittFrobeniusPrimeSeamPair_cyclicCorrection
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    deningerOrdinaryIntegerDiagonalCoefficient 1
          (hochschildBoundaryOne
            (deningerBigWittFrobeniusPrimeSeamPairBVGreenChain a p q)) -
        deningerBigWittPrimePairCanonicalCyclicReader p q
          (hochschildBoundaryOne
            (deningerBigWittFrobeniusPrimeSeamPairBVGreenChain a p q)) =
      deningerBigWittFrobeniusPrimeSeamPairCoefficient a p q := by
  rw [deningerBigWittFrobeniusPrimeSeamPairBVGreenChain_groundReadout]
  rw [deningerBigWittFrobeniusPrimeSeamPairBVGreenChain_boundary,
    map_smul,
    deningerBigWittPrimePairCanonicalCyclicReader_boundary]
  simp

/-- Sum of all canonical pairwise cyclic corrections. -/
def deningerBigWittFrobeniusPrimeSeamFiniteCyclicCorrection
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) : ℂ :=
  ∑ p ∈ s, ∑ q ∈ s,
    (deningerOrdinaryIntegerDiagonalCoefficient 1
          (hochschildBoundaryOne
            (deningerBigWittFrobeniusPrimeSeamPairBVGreenChain a p q)) -
      deningerBigWittPrimePairCanonicalCyclicReader p q
        (hochschildBoundaryOne
          (deningerBigWittFrobeniusPrimeSeamPairBVGreenChain a p q)))

/-- Pairwise canonical cyclic correction retains whole physical first ghost;
it creates no cofinal saving. -/
theorem deningerBigWittFrobeniusPrimeSeamFiniteCyclicCorrection_eq
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittFrobeniusPrimeSeamFiniteCyclicCorrection a s =
      deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittFrobeniusTwo
          (deningerBigWittPolarizedPrimeSeamAggregateSource a s)) := by
  rw [deningerBigWittFrobeniusPrimeSeamFiniteCyclicCorrection]
  simp_rw [deningerBigWittFrobeniusPrimeSeamPair_cyclicCorrection]
  rw [deningerBigWittFrobeniusTwo_polarizedAggregate_ghost_one]
  rw [deningerBigWittPrimeSeamSourceEnergy, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [deningerBigWittFrobeniusPrimeSeamPairCoefficient_eq]
  push_cast
  ring

/-- On every strip fibre, normalized pairwise cyclic correction has same
off-line residue as physical first ghost. -/
theorem tendsto_deningerBigWittFrobeniusPrimeSeamFiniteCyclicCorrection_div_mass
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Tendsto
      (fun s : Finset Nat.Primes =>
        Complex.re
            (deningerBigWittFrobeniusPrimeSeamFiniteCyclicCorrection
              (fun p : Nat.Primes =>
                orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s) /
          primeReciprocalMass s)
      atTop
      (nhds (-4 * orbitwisePrimeSeamWeightedNormSq rho)) := by
  simpa only [deningerBigWittFrobeniusPrimeSeamFiniteCyclicCorrection_eq]
    using
      tendsto_deningerBigWittFrobeniusTwo_polarizedAggregate_ghost_one_div_mass
        hstrip

end


end RHTower

import GaloisForLFunctions.RHTower.XiPrimeSeamPairEnergy
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSquareIndexPolarization

/-!
# Weighted-variance factorization of the Xi prime-seam pair energy

The reciprocal-prime pair energy is not intrinsically a two-particle arithmetic object.  This
module reuses the finite weighted bilinear variance identity proved for the theta-tail square-index
polarization to split it into a one-particle weighted norm and one rank-one mean direction.

For a finite prime set `s`, reciprocal mass `M_s`, weighted square norm `S_s`, and weighted mean
`A_s`, the exact identity is

`E_s(a) = 2 M_s S_s - 2 ‖A_s‖²`.

This is a source-side simplification, not an operator upper bound.  In particular, it does not
assert the missing uniform Calkin estimate for the actual two-particle Sonin sections.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Reciprocal-prime mass of a finite prime set. -/
def primeReciprocalMass (s : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ s, 1 / (p : ℝ)

/-- Reciprocal-prime weighted square norm of a finite prime-indexed packet. -/
def primePairWeightedNormSq (a : Nat.Primes → ℂ)
    (s : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ s, (1 / (p : ℝ)) * ‖a p‖ ^ (2 : ℕ)

/-- Reciprocal-prime weighted, unnormalized mean of a finite prime-indexed packet. -/
def primePairWeightedMean (a : Nat.Primes → ℂ)
    (s : Finset Nat.Primes) : ℂ :=
  ∑ p ∈ s, ((1 / (p : ℝ) : ℝ) : ℂ) * a p

/-- **Prime-pair variance identity.**  The ordered reciprocal-prime pair energy is exactly twice
the reciprocal mass times the one-particle weighted square norm, minus the rank-one mean energy. -/
theorem primePairDifferenceEnergy_eq_weightedVariance
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    primePairDifferenceEnergy a s =
      2 * primeReciprocalMass s * primePairWeightedNormSq a s -
        2 * ‖primePairWeightedMean a s‖ ^ (2 : ℕ) := by
  let w : Nat.Primes → ℝ := fun p => 1 / (p : ℝ)
  have hre0 := two_mul_weightedBilinear_eq_rankOne_add_pairwiseDispersion
    s w (fun p => (a p).re) (fun p => (a p).re)
  have him0 := two_mul_weightedBilinear_eq_rankOne_add_pairwiseDispersion
    s w (fun p => (a p).im) (fun p => (a p).im)
  have hre :
      2 * (∑ p ∈ s, w p) * (∑ p ∈ s, w p * (a p).re ^ (2 : ℕ)) =
        2 * (∑ p ∈ s, w p * (a p).re) ^ (2 : ℕ) +
          ∑ p ∈ s, ∑ q ∈ s,
            w p * w q * ((a p).re - (a q).re) ^ (2 : ℕ) := by
    simpa only [pow_two, mul_assoc] using hre0
  have him :
      2 * (∑ p ∈ s, w p) * (∑ p ∈ s, w p * (a p).im ^ (2 : ℕ)) =
        2 * (∑ p ∈ s, w p * (a p).im) ^ (2 : ℕ) +
          ∑ p ∈ s, ∑ q ∈ s,
            w p * w q * ((a p).im - (a q).im) ^ (2 : ℕ) := by
    simpa only [pow_two, mul_assoc] using him0
  have henergy : primePairDifferenceEnergy a s =
      ∑ p ∈ s, ∑ q ∈ s,
        w p * w q * ((a p - a q).re ^ (2 : ℕ) + (a p - a q).im ^ (2 : ℕ)) := by
    unfold primePairDifferenceEnergy primePairDifferenceRow
    apply Finset.sum_congr rfl
    intro p hp
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [w]
    ring
  rw [henergy]
  have hpair :
      (∑ p ∈ s, ∑ q ∈ s,
        w p * w q * ((a p - a q).re ^ (2 : ℕ) + (a p - a q).im ^ (2 : ℕ))) =
      (∑ p ∈ s, ∑ q ∈ s,
        w p * w q * ((a p).re - (a q).re) ^ (2 : ℕ)) +
      (∑ p ∈ s, ∑ q ∈ s,
        w p * w q * ((a p).im - (a q).im) ^ (2 : ℕ)) := by
    simp only [Complex.sub_re, Complex.sub_im]
    simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hpair]
  rw [show (∑ p ∈ s, ∑ q ∈ s,
      w p * w q * ((a p).re - (a q).re) ^ (2 : ℕ)) =
      2 * (∑ p ∈ s, w p) * (∑ p ∈ s, w p * (a p).re ^ (2 : ℕ)) -
        2 * (∑ p ∈ s, w p * (a p).re) ^ (2 : ℕ) by
    linarith [hre]]
  rw [show (∑ p ∈ s, ∑ q ∈ s,
      w p * w q * ((a p).im - (a q).im) ^ (2 : ℕ)) =
      2 * (∑ p ∈ s, w p) * (∑ p ∈ s, w p * (a p).im ^ (2 : ℕ)) -
        2 * (∑ p ∈ s, w p * (a p).im) ^ (2 : ℕ) by
    linarith [him]]
  have hmeanRe : (primePairWeightedMean a s).re =
      ∑ p ∈ s, w p * (a p).re := by
    simp [primePairWeightedMean, w]
  have hmeanIm : (primePairWeightedMean a s).im =
      ∑ p ∈ s, w p * (a p).im := by
    simp [primePairWeightedMean, w]
  rw [Complex.sq_norm, Complex.normSq_apply, hmeanRe, hmeanIm]
  dsimp [primeReciprocalMass, primePairWeightedNormSq, w]
  simp_rw [Complex.sq_norm, Complex.normSq_apply, mul_add, Finset.sum_add_distrib]
  ring_nf

/-- The rank-one weighted mean never exceeds the mass times the weighted square norm.  Here this
finite Cauchy--Schwarz inequality is an immediate positive consequence of pair-energy
nonnegativity and the exact variance identity. -/
theorem primePairWeightedMean_norm_sq_le
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    ‖primePairWeightedMean a s‖ ^ (2 : ℕ) ≤
      primeReciprocalMass s * primePairWeightedNormSq a s := by
  have h := primePairDifferenceEnergy_nonneg a s
  rw [primePairDifferenceEnergy_eq_weightedVariance] at h
  nlinarith

/-! ## Plucker-plane form of the pair obstruction -/

/-- The weighted Gram determinant of the constant prime section and a prime-indexed packet.
This is the squared Plucker area of their span. -/
def primePairPluckerGramDet (a : Nat.Primes → ℂ)
    (s : Finset Nat.Primes) : ℝ :=
  primeReciprocalMass s * primePairWeightedNormSq a s -
    ‖primePairWeightedMean a s‖ ^ (2 : ℕ)

/-- **Prime-pair Plucker identity.**  The reciprocal-prime pair energy is twice the weighted
Gram determinant of the constant section and the packet `a`.  Thus the two-particle obstruction
is exactly a rank-two area, rather than a sum of unrelated scalar defects. -/
theorem primePairDifferenceEnergy_eq_two_mul_pluckerGramDet
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    primePairDifferenceEnergy a s = 2 * primePairPluckerGramDet a s := by
  rw [primePairDifferenceEnergy_eq_weightedVariance]
  simp only [primePairPluckerGramDet]
  ring

/-- The weighted Plucker Gram determinant is nonnegative. -/
theorem primePairPluckerGramDet_nonneg
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    0 ≤ primePairPluckerGramDet a s := by
  have h := primePairDifferenceEnergy_nonneg a s
  rw [primePairDifferenceEnergy_eq_two_mul_pluckerGramDet] at h
  nlinarith

/-- The canonical Xi seam pair obstruction is exactly twice its finite weighted Plucker area. -/
theorem orbitwisePrimeSeamPairEnergy_eq_two_mul_pluckerGramDet
    (rho : ℂ) (s : Finset Nat.Primes) :
    primePairDifferenceEnergy
        (fun p : Nat.Primes => orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s =
      2 * primePairPluckerGramDet
        (fun p : Nat.Primes => orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s :=
  primePairDifferenceEnergy_eq_two_mul_pluckerGramDet _ _

/-- The canonical FE--Schwarz seam pair energy has the same exact one-particle variance
factorization on every finite prime set. -/
theorem orbitwisePrimeSeamPairEnergy_eq_weightedVariance
    (rho : ℂ) (s : Finset Nat.Primes) :
    primePairDifferenceEnergy
        (fun p : Nat.Primes => orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s =
      2 * primeReciprocalMass s *
          primePairWeightedNormSq
            (fun p : Nat.Primes => orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s -
        2 * ‖primePairWeightedMean
          (fun p : Nat.Primes => orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s‖ ^ (2 : ℕ) :=
  primePairDifferenceEnergy_eq_weightedVariance _ _

end

end RHTower

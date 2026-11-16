import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittGhost

/-!
# Balanced involutions and even ghost degrees

Pairing positive and negative eigenlines changes the two Euler factors
`(1-aTᵐ)(1+aTᵐ)` into `1-a²T²ᵐ`. Thus a balanced involution has logarithmic
trace supported on even multiples of the degree. This realizes the
signed Euler-product mechanism of Zehavi, Proposition 4.16,
arXiv:2611.18218, directly in the corpus's integral Witt ghost map.
-/

namespace GaloisForLFunctions.EisensteinDegeneration

open PowerSeries _root_.RHTower

variable {A : Type*} [CommRing A]

/-- Pairing opposite eigenvalues doubles the Euler degree and squares the eigenvalue. -/
theorem oppositeEulerFactors (a : A) (m : ℕ) :
    deningerBigWittFactor a m * deningerBigWittFactor (-a) m =
      deningerBigWittFactor (a ^ 2) (2 * m) := by
  simp only [deningerBigWittFactor, map_neg, map_pow, pow_mul]
  ring

/-- Equal multiplicities of opposite eigenvalues give one Euler factor in doubled degree. -/
theorem balancedEulerFactors (a : A) (m g : ℕ) :
    deningerBigWittFactor a m ^ g * deningerBigWittFactor (-a) m ^ g =
      deningerBigWittFactor (a ^ 2) (2 * m) ^ g := by
  rw [← mul_pow, oppositeEulerFactors]

/-- The exact ghost coefficient for a balanced pair, with arbitrary multiplicity. -/
theorem balancedEulerGhost_coefficient (a : A) (m g n : ℕ) :
    coeff (n + 1) (deningerBigWittLogGhost
      (deningerBigWittFactor a (m + 1) ^ g * deningerBigWittFactor (-a) (m + 1) ^ g)
      (by simp [deningerBigWittFactor_constantCoeff])) =
        g • (if 2 * (m + 1) ∣ n + 1 then
          ((2 * (m + 1) : ℕ) : A) * (a ^ 2) ^ ((n + 1) / (2 * (m + 1))) else 0) := by
  have he := deningerBigWittLogGhost_congr
    (by simp [deningerBigWittFactor_constantCoeff])
    (by simp [deningerBigWittFactor_constantCoeff, show 2 * (m + 1) ≠ 0 by omega])
    (balancedEulerFactors a (m + 1) g)
  rw [he, deningerBigWittLogGhost_pow _
    (deningerBigWittFactor_constantCoeff _ _ (by omega)), map_nsmul,
    deningerBigWittLogGhost_factor_coeff _ (by omega) (Nat.succ_pos n)]

/-- In degree one, the logarithmic trace of a balanced involution is `2g` in even degrees. -/
theorem balancedInvolutionGhost_coefficient (g n : ℕ) :
    coeff (n + 1) (deningerBigWittLogGhost
      (deningerBigWittFactor (1 : ℤ) 1 ^ g * deningerBigWittFactor (-1 : ℤ) 1 ^ g)
      (by simp [deningerBigWittFactor_constantCoeff])) =
        if 2 ∣ n + 1 then 2 * (g : ℤ) else 0 := by
  rw [balancedEulerGhost_coefficient (1 : ℤ) 0 g n]
  split_ifs <;> simp [mul_comm]

/-- The corresponding inverse Euler product has coefficient one in even degrees and zero in odd degrees. -/
theorem balancedInvolutionHilbert_coefficient (n : ℕ) :
    coeff n (invOfUnit
      (deningerBigWittFactor (1 : ℤ) 1 * deningerBigWittFactor (-1 : ℤ) 1) 1) =
        if 2 ∣ n then 1 else 0 := by
  rw [oppositeEulerFactors, deningerBigWittInvFactor_eq_geom _ (by omega),
    deningerBigWittGeom_coeff]
  simp

end GaloisForLFunctions.EisensteinDegeneration

#print axioms GaloisForLFunctions.EisensteinDegeneration.balancedEulerGhost_coefficient
#print axioms GaloisForLFunctions.EisensteinDegeneration.balancedInvolutionGhost_coefficient
#print axioms GaloisForLFunctions.EisensteinDegeneration.balancedInvolutionHilbert_coefficient

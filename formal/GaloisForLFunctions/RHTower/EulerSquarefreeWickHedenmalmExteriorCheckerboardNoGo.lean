import GaloisForLFunctions.RHTower.EulerSquarefreeWickQuadraticCharacterBridge
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCoefficientFaithfulExteriorSourceContour

/-!
# EWQ checkerboard blindness of the coefficient-faithful Hedenmalm exterior packet

The four primes `13, 5, 7, 11` realize the four unit classes modulo `12`.  Their literal EWQ
quadratic interaction signs are `+1, -1, -1, +1`.  On the other hand, the prime-normalized
coefficient-faithful Hedenmalm exterior contour has the same positive divisor-packet limit at
every prime.  Consequently the EWQ checkerboard combination converges to zero identically.

Thus applying the anchored EWQ marginal quotient after the normalized exterior construction
erases the desired off-line exterior quantum together with the marginals.  Any surviving fusion
must couple the residue interaction before prime normalization, or retain a prime-dependent
source scale in the limit.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

def ewqHedenmalmExteriorPrimeThirteen : Nat.Primes := ⟨13, by norm_num⟩
def ewqHedenmalmExteriorPrimeFive : Nat.Primes := ⟨5, by norm_num⟩
def ewqHedenmalmExteriorPrimeSeven : Nat.Primes := ⟨7, by norm_num⟩
def ewqHedenmalmExteriorPrimeEleven : Nat.Primes := ⟨11, by norm_num⟩

private theorem quadraticResidueProductPrimeCoefficient_of_mod_twelve
    (p : Nat.Primes) (hp : IsUnit (((p : Nat.Primes).1 : ℕ) : ZMod 12)) :
    quadraticResidueProductPrimeCoefficient p =
      quadraticCharacterTwelve ((p.1 : ℕ) : ZMod 12) := by
  exact quadraticResidueProductPrimeCoefficient_eq_quadraticCharacterTwelve_of_isUnit p hp

theorem quadraticResidueProductPrimeCoefficient_ewqHedenmalm_thirteen :
    quadraticResidueProductPrimeCoefficient ewqHedenmalmExteriorPrimeThirteen = 1 := by
  have hp : IsUnit
      (((ewqHedenmalmExteriorPrimeThirteen : Nat.Primes).1 : ℕ) : ZMod 12) := by
    rw [ZMod.isUnit_iff_coprime]
    norm_num [ewqHedenmalmExteriorPrimeThirteen]
  rw [quadraticResidueProductPrimeCoefficient_of_mod_twelve
    ewqHedenmalmExteriorPrimeThirteen hp]
  change quadraticCharacterTwelve (13 : ZMod 12) = 1
  rw [show (13 : ZMod 12) = 1 by decide, map_one]

theorem quadraticResidueProductPrimeCoefficient_ewqHedenmalm_five :
    quadraticResidueProductPrimeCoefficient ewqHedenmalmExteriorPrimeFive = -1 := by
  have hp : IsUnit
      (((ewqHedenmalmExteriorPrimeFive : Nat.Primes).1 : ℕ) : ZMod 12) := by
    rw [ZMod.isUnit_iff_coprime]
    norm_num [ewqHedenmalmExteriorPrimeFive]
  rw [quadraticResidueProductPrimeCoefficient_of_mod_twelve
    ewqHedenmalmExteriorPrimeFive hp]
  change quadraticCharacterTwelve (5 : ZMod 12) = -1
  rw [quadraticCharacterTwelve, _root_.RHTower.crtProductCharacter_apply]
  rw [show ZMod.chineseRemainder (by norm_num : Nat.Coprime 3 4) (5 : ZMod 12) =
      (((5 : ℤ) : ZMod 3), ((5 : ℤ) : ZMod 4)) by
    exact map_intCast _ 5]
  have hthree : quadraticCharacterThree (-1 : ZMod 3) = -1 := by
    simpa [quadraticCharacterThreeUnit] using quadraticCharacterThreeUnit_neg_one
  change quadraticCharacterThree (5 : ZMod 3) *
      _root_.RHTower.quadraticCharacterFour (5 : ZMod 4) = -1
  rw [show (5 : ZMod 3) = -1 by decide,
    show (5 : ZMod 4) = 1 by decide, hthree]
  simp

theorem quadraticResidueProductPrimeCoefficient_ewqHedenmalm_seven :
    quadraticResidueProductPrimeCoefficient ewqHedenmalmExteriorPrimeSeven = -1 := by
  have hp : IsUnit
      (((ewqHedenmalmExteriorPrimeSeven : Nat.Primes).1 : ℕ) : ZMod 12) := by
    rw [ZMod.isUnit_iff_coprime]
    norm_num [ewqHedenmalmExteriorPrimeSeven]
  rw [quadraticResidueProductPrimeCoefficient_of_mod_twelve
    ewqHedenmalmExteriorPrimeSeven hp]
  change quadraticCharacterTwelve (7 : ZMod 12) = -1
  rw [quadraticCharacterTwelve, _root_.RHTower.crtProductCharacter_apply]
  rw [show ZMod.chineseRemainder (by norm_num : Nat.Coprime 3 4) (7 : ZMod 12) =
      (((7 : ℤ) : ZMod 3), ((7 : ℤ) : ZMod 4)) by
    exact map_intCast _ 7]
  have hfour : _root_.RHTower.quadraticCharacterFour (-1 : ZMod 4) = -1 := by
    simpa [quadraticCharacterFourUnit] using quadraticCharacterFourUnit_neg_one
  change quadraticCharacterThree (7 : ZMod 3) *
      _root_.RHTower.quadraticCharacterFour (7 : ZMod 4) = -1
  rw [show (7 : ZMod 3) = 1 by decide,
    show (7 : ZMod 4) = -1 by decide, hfour]
  simp

theorem quadraticResidueProductPrimeCoefficient_ewqHedenmalm_eleven :
    quadraticResidueProductPrimeCoefficient ewqHedenmalmExteriorPrimeEleven = 1 := by
  have hp : IsUnit
      (((ewqHedenmalmExteriorPrimeEleven : Nat.Primes).1 : ℕ) : ZMod 12) := by
    rw [ZMod.isUnit_iff_coprime]
    norm_num [ewqHedenmalmExteriorPrimeEleven]
  rw [quadraticResidueProductPrimeCoefficient_of_mod_twelve
    ewqHedenmalmExteriorPrimeEleven hp]
  change quadraticCharacterTwelve (11 : ZMod 12) = 1
  rw [quadraticCharacterTwelve, _root_.RHTower.crtProductCharacter_apply]
  rw [show ZMod.chineseRemainder (by norm_num : Nat.Coprime 3 4) (11 : ZMod 12) =
      (((11 : ℤ) : ZMod 3), ((11 : ℤ) : ZMod 4)) by
    exact map_intCast _ 11]
  have hthree : quadraticCharacterThree (-1 : ZMod 3) = -1 := by
    simpa [quadraticCharacterThreeUnit] using quadraticCharacterThreeUnit_neg_one
  have hfour : _root_.RHTower.quadraticCharacterFour (-1 : ZMod 4) = -1 := by
    simpa [quadraticCharacterFourUnit] using quadraticCharacterFourUnit_neg_one
  change quadraticCharacterThree (11 : ZMod 3) *
      _root_.RHTower.quadraticCharacterFour (11 : ZMod 4) = 1
  rw [show (11 : ZMod 3) = -1 by decide,
    show (11 : ZMod 4) = -1 by decide, hthree, hfour]
  norm_num

/-- EWQ checkerboard applied across the four mod-`12` prime cells to the normalized,
coefficient-faithful Hedenmalm exterior contour. -/
def ewqHedenmalmExteriorCheckerboardCesaro
    (z₁ z₂ : ℂ) (t : ℝ) (N : ℕ) : ℂ :=
  _root_.RHTower.xiPrimeWardExteriorCoefficientFaithfulSourceCesaro
      ewqHedenmalmExteriorPrimeThirteen z₁ z₂ t N -
    _root_.RHTower.xiPrimeWardExteriorCoefficientFaithfulSourceCesaro
      ewqHedenmalmExteriorPrimeFive z₁ z₂ t N -
    _root_.RHTower.xiPrimeWardExteriorCoefficientFaithfulSourceCesaro
      ewqHedenmalmExteriorPrimeSeven z₁ z₂ t N +
    _root_.RHTower.xiPrimeWardExteriorCoefficientFaithfulSourceCesaro
      ewqHedenmalmExteriorPrimeEleven z₁ z₂ t N

/-- **Prime-normalized exterior blindness.**  The literal EWQ checkerboard cancels the complete
coefficient-faithful Hedenmalm exterior limit for every admissible reflected rectangle. -/
theorem tendsto_ewqHedenmalmExteriorCheckerboardCesaro_zero
    {z₁ z₂ : ℂ}
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ Set.uIcc z₁.re z₂.re,
      _root_.RHTower.XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ Set.uIcc z₁.re z₂.re,
      _root_.RHTower.XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ Set.uIcc z₁.im z₂.im,
      _root_.RHTower.XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ Set.uIcc z₁.im z₂.im,
      _root_.RHTower.XiExplicitAdmissible ((z₁.re : ℂ) + y * I))
    (hclosed : ∀ rho ∈ _root_.RHTower.xiDivisorSupportClosedRectangle z₁ z₂,
      _root_.RHTower.xiZeroLineConjEquiv rho ∈
        _root_.RHTower.xiDivisorSupportClosedRectangle z₁ z₂)
    (t : ℝ) :
    Tendsto (ewqHedenmalmExteriorCheckerboardCesaro z₁ z₂ t)
      atTop (nhds 0) := by
  have h13 :=
    _root_.RHTower.tendsto_xiPrimeWardExteriorCoefficientFaithfulSourceCesaro
      ewqHedenmalmExteriorPrimeThirteen hre him hbot htop hright hleft hclosed t
  have h5 :=
    _root_.RHTower.tendsto_xiPrimeWardExteriorCoefficientFaithfulSourceCesaro
      ewqHedenmalmExteriorPrimeFive hre him hbot htop hright hleft hclosed t
  have h7 :=
    _root_.RHTower.tendsto_xiPrimeWardExteriorCoefficientFaithfulSourceCesaro
      ewqHedenmalmExteriorPrimeSeven hre him hbot htop hright hleft hclosed t
  have h11 :=
    _root_.RHTower.tendsto_xiPrimeWardExteriorCoefficientFaithfulSourceCesaro
      ewqHedenmalmExteriorPrimeEleven hre him hbot htop hright hleft hclosed t
  have hlim := ((h13.sub h5).sub h7).add h11
  convert hlim using 1
  · rfl
  · apply congrArg nhds
    push_cast
    ring

end

end GaloisForLFunctions.RHTower

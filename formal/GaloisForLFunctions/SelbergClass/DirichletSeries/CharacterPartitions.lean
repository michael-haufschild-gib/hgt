import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeRestriction
import GaloisForLFunctions.RHTower.SiegelProductCoefficients

/-!
# Prime separation for Dirichlet twists and Siegel products

Prime restriction commutes with character twisting and separates the coefficients of a
Dirichlet L-function, a zeta-times-character product, and the four-factor Siegel product.
No reality or quadraticity assumption on the characters is needed for these identities.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction RHTower

variable {N M : ℕ}

/-- A character twist may be applied before or after deleting prime factors. -/
theorem primeRestrict_charTwist (S : Set ℕ) (χ : DirichletCharacter ℂ N)
    (f : ArithmeticFunction ℂ) :
    primeRestrict S (charTwist χ f) = charTwist χ (primeRestrict S f) := by
  classical
  ext n
  by_cases h : (↑n.primeFactors : Set ℕ) ⊆ S <;>
    simp [primeRestrict_apply, charTwist, pmul_apply, h]

/-- The Dirichlet coefficients of every character split over any prime partition. -/
theorem character_prime_partition (S : Set ℕ) (χ : DirichletCharacter ℂ N) :
    primeRestrict S (toArithmeticFunction (χ ·)) *
      primeRestrict Sᶜ (toArithmeticFunction (χ ·)) = toArithmeticFunction (χ ·) :=
  primeRestrict_mul_compl S _ χ.isMultiplicative_toArithmeticFunction

/-- The divisor sum of a character splits over the same partition. -/
theorem zetaMul_prime_partition (S : Set ℕ) (χ : DirichletCharacter ℂ N) :
    primeRestrict S χ.zetaMul * primeRestrict Sᶜ χ.zetaMul = χ.zetaMul :=
  primeRestrict_mul_compl S _ χ.isMultiplicative_zetaMul

/-- The four-factor Siegel coefficient stream separates without a sign assumption. -/
theorem siegelCoeff_prime_partition (S : Set ℕ)
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    primeRestrict S (siegelCoeff χ ψ) * primeRestrict Sᶜ (siegelCoeff χ ψ) =
      siegelCoeff χ ψ :=
  primeRestrict_mul_compl S _ (isMultiplicative_siegelCoeff χ ψ)

/-- The twisted convolution presentation remains valid inside every supported algebra. -/
theorem restricted_siegelCoeff (S : Set ℕ)
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    primeRestrict S (siegelCoeff χ ψ) =
      primeRestrict S χ.zetaMul * charTwist ψ (primeRestrict S χ.zetaMul) := by
  rw [siegelCoeff, primeRestrict_mul, primeRestrict_charTwist]

end GaloisForLFunctions.SelbergClass.DirichletSeries

#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.character_prime_partition
#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.zetaMul_prime_partition
#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.siegelCoeff_prime_partition
#print axioms GaloisForLFunctions.SelbergClass.DirichletSeries.restricted_siegelCoeff

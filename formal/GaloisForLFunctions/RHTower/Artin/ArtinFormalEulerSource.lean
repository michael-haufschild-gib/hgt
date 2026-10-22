import GaloisForLFunctions.RHTower.Artin.ArtinNumberFieldLocalEulerFactor
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Coefficientwise Artin Euler sources

This module turns the choice-free finite-place Artin polynomials into an actual formal Dirichlet
series.  It is deliberately coefficientwise: `ArithmeticFunction.eulerProduct` proves eventual
stabilization of each coefficient, not analytic convergence of an Euler product in a complex
half-plane.
-/

open scoped BigOperators NumberField
open IsDedekindDomain

noncomputable section

universe u

namespace GaloisForLFunctions

variable {K L G V : Type u}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The choice-free finite-place Artin local polynomial has constant coefficient one. -/
theorem numberFieldFinitePlaceLocalEulerPolynomial_eval_zero
    (v : HeightOneSpectrum (𝓞 K)) (ρ : Representation ℂ G V) :
    (numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ).eval 0 = 1 := by
  let p : MaximalSpectrum (𝓞 K) :=
    { asIdeal := v.asIdeal, isMaximal := v.isMaximal }
  let Q := chosenMaximalPrimeAbove (A := 𝓞 K) (B := 𝓞 L) p
  letI : Q.IsMaximal :=
    chosenMaximalPrimeAbove_isMaximal (A := 𝓞 K) (B := 𝓞 L) p
  letI : Q.IsPrime := (inferInstance : Q.IsMaximal).isPrime
  letI : Finite ((𝓞 L) ⧸ Q) := inferInstance
  change (frobeniusInertiaEulerPolynomial (R := 𝓞 K) Q ρ).eval 0 = 1
  exact frobeniusInertiaEulerPolynomial_eval_zero _ _

/-- The reciprocal local Artin factor as an actual complex power series. -/
noncomputable def artinLocalEulerPowerSeries
    (v : HeightOneSpectrum (𝓞 K)) (ρ : Representation ℂ G V) : PowerSeries ℂ :=
  PowerSeries.invOfUnit
    (numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ) 1

/-- Each reciprocal local Artin power series has constant coefficient one. -/
theorem artinLocalEulerPowerSeries_constantCoeff
    (v : HeightOneSpectrum (𝓞 K)) (ρ : Representation ℂ G V) :
    (artinLocalEulerPowerSeries (K := K) (L := L) v ρ).constantCoeff = 1 := by
  simp [artinLocalEulerPowerSeries]

/-- The reciprocal local power series is a genuine inverse of the finite-place polynomial. -/
theorem numberFieldFinitePlaceLocalEulerPolynomial_mul_artinLocalEulerPowerSeries
    (v : HeightOneSpectrum (𝓞 K)) (ρ : Representation ℂ G V) :
    (numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ : PowerSeries ℂ) *
        artinLocalEulerPowerSeries (K := K) (L := L) v ρ = 1 := by
  apply PowerSeries.mul_invOfUnit
  rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero]
  exact numberFieldFinitePlaceLocalEulerPolynomial_eval_zero (K := K) (L := L) v ρ

/-- The formal local Artin Euler factor, supported on powers of the finite-prime norm. -/
noncomputable def artinLocalEulerArithmeticFactor
    (v : HeightOneSpectrum (𝓞 K)) (ρ : Representation ℂ G V) : ArithmeticFunction ℂ :=
  ArithmeticFunction.ofPowerSeries v.asIdeal.absNorm
    (artinLocalEulerPowerSeries (K := K) (L := L) v ρ)

/-- The coefficientwise Artin Euler source over finite primes of the base number field. -/
noncomputable def artinFormalEulerSource
    (ρ : Representation ℂ G V) : ArithmeticFunction ℂ :=
  ArithmeticFunction.eulerProduct
    (fun v : HeightOneSpectrum (𝓞 K) =>
      artinLocalEulerArithmeticFactor (K := K) (L := L) v ρ)

/-- Every coefficient of the formal Artin Euler source eventually equals its finite Euler-product
coefficient.  This is coefficientwise stabilization, not analytic Euler-product convergence. -/
theorem artinFormalEulerSource_coefficient_eventually_eq
    (ρ : Representation ℂ G V) (n : ℕ) :
    ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 K)) in Filter.atTop,
      (∏ v ∈ S, artinLocalEulerArithmeticFactor (K := K) (L := L) v ρ) n =
        artinFormalEulerSource (K := K) (L := L) ρ n := by
  simpa [artinLocalEulerArithmeticFactor, artinFormalEulerSource] using
    (ArithmeticFunction.tendsTo_eulerProduct_ofPowerSeries
      (q := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal.absNorm)
      (f := fun v => artinLocalEulerPowerSeries (K := K) (L := L) v ρ)
      (fun v => by simp [artinLocalEulerPowerSeries]) n)

end GaloisForLFunctions

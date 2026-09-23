import GaloisForLFunctions.RHTower.ThetaPrimeCubeRadialMomentLaw
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberCrossedTranslation

/-!
# Prime-cube crossed-phase radial factorization

Arithmetic reflection removes the odd phase from both crossed finite-translation channels.  Their
product-fibre averages therefore have one common radial cosine factor, while the two external phase
factors retain opposite orientation.  At a prime cube the common factor has the exact two-radius
moment law.
-/

open Complex Real Finset Polynomial

namespace RHTower

noncomputable section

/-- Common finite radial factor of a reflected theta product fibre. -/
def thetaProductFiberFiniteRadialPolynomial (k d : ℕ) : Polynomial ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    finiteCosinePolynomial d (thetaFactorPairLogDisplacement q)

/-- Reflection factorizes the positive-negative crossed packet through the common radial factor. -/
theorem sum_finitePositiveNegativeCrossedTranslationPacket_factorPairs
    (k d : ℕ) (a : ℝ) :
    (∑ q ∈ thetaPositiveFactorPairs k,
      finitePositiveNegativeCrossedTranslationPacket d
        (thetaFactorPairLogDisplacement q) a) =
      thetaProductFiberFiniteRadialPolynomial k d *
        finiteNegativePhasePolynomial d a := by
  unfold finitePositiveNegativeCrossedTranslationPacket
    finitePositivePhasePolynomial thetaProductFiberFiniteRadialPolynomial
  have hs := sum_finiteSinePolynomial_thetaFactorPairLogDisplacement k d
  calc
    (∑ q ∈ thetaPositiveFactorPairs k,
        (finiteCosinePolynomial d (thetaFactorPairLogDisplacement q) +
          Polynomial.C Complex.I *
            finiteSinePolynomial d (thetaFactorPairLogDisplacement q)) *
          finiteNegativePhasePolynomial d a) =
        (∑ q ∈ thetaPositiveFactorPairs k,
          (finiteCosinePolynomial d (thetaFactorPairLogDisplacement q) +
            Polynomial.C Complex.I *
              finiteSinePolynomial d (thetaFactorPairLogDisplacement q))) *
            finiteNegativePhasePolynomial d a := by
              rw [Finset.sum_mul]
    _ = ((∑ q ∈ thetaPositiveFactorPairs k,
          finiteCosinePolynomial d (thetaFactorPairLogDisplacement q)) +
          Polynomial.C Complex.I *
            (∑ q ∈ thetaPositiveFactorPairs k,
              finiteSinePolynomial d (thetaFactorPairLogDisplacement q))) *
            finiteNegativePhasePolynomial d a := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∑ q ∈ thetaPositiveFactorPairs k,
          finiteCosinePolynomial d (thetaFactorPairLogDisplacement q)) *
            finiteNegativePhasePolynomial d a := by
              rw [hs, mul_zero, add_zero]

/-- Reflection factorizes the reverse crossed packet through the same radial factor. -/
theorem sum_finiteNegativePositiveCrossedTranslationPacket_factorPairs
    (k d : ℕ) (a : ℝ) :
    (∑ q ∈ thetaPositiveFactorPairs k,
      finiteNegativePositiveCrossedTranslationPacket d
        (thetaFactorPairLogDisplacement q) a) =
      thetaProductFiberFiniteRadialPolynomial k d *
        finitePositivePhasePolynomial d a := by
  unfold finiteNegativePositiveCrossedTranslationPacket
    finiteNegativePhasePolynomial thetaProductFiberFiniteRadialPolynomial
  have hs := sum_finiteSinePolynomial_thetaFactorPairLogDisplacement k d
  calc
    (∑ q ∈ thetaPositiveFactorPairs k,
        (finiteCosinePolynomial d (thetaFactorPairLogDisplacement q) -
          Polynomial.C Complex.I *
            finiteSinePolynomial d (thetaFactorPairLogDisplacement q)) *
          finitePositivePhasePolynomial d a) =
        (∑ q ∈ thetaPositiveFactorPairs k,
          (finiteCosinePolynomial d (thetaFactorPairLogDisplacement q) -
            Polynomial.C Complex.I *
              finiteSinePolynomial d (thetaFactorPairLogDisplacement q))) *
            finitePositivePhasePolynomial d a := by
              rw [Finset.sum_mul]
    _ = ((∑ q ∈ thetaPositiveFactorPairs k,
          finiteCosinePolynomial d (thetaFactorPairLogDisplacement q)) -
          Polynomial.C Complex.I *
            (∑ q ∈ thetaPositiveFactorPairs k,
              finiteSinePolynomial d (thetaFactorPairLogDisplacement q))) *
            finitePositivePhasePolynomial d a := by
              rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (∑ q ∈ thetaPositiveFactorPairs k,
          finiteCosinePolynomial d (thetaFactorPairLogDisplacement q)) *
            finitePositivePhasePolynomial d a := by
              rw [hs, mul_zero, sub_zero]

/-- The common radial factor at a prime cube has exactly the outer/inner two-radius coefficient
formula. -/
theorem thetaProductFiberFiniteRadialPolynomial_primeCube_coeff_two_mul
    {p : ℕ} (hp : p.Prime) (d l : ℕ) :
    (thetaProductFiberFiniteRadialPolynomial (p ^ (3 : ℕ)) d).coeff (2 * l) =
      if l ≤ d then
        ((-1 : ℂ) ^ l *
          (2 * (3 * Real.log p / 2) ^ (2 * l) +
            2 * (Real.log p / 2) ^ (2 * l) : ℝ)) /
          (2 * l).factorial
      else 0 := by
  exact coeff_sum_finiteCosinePolynomial_primeCube_two_mul hp d l

/-- The two crossed channels over a prime cube are a rank-one phase pair over a common explicit
two-radius radial polynomial. -/
structure ThetaPrimeCubeCrossedPhaseRadialFactorizationUniversalCertificate
    (p d : ℕ) (a : ℝ) : Prop where
  positiveNegativeFactorization :
    (∑ q ∈ thetaPositiveFactorPairs (p ^ (3 : ℕ)),
      finitePositiveNegativeCrossedTranslationPacket d
        (thetaFactorPairLogDisplacement q) a) =
      thetaProductFiberFiniteRadialPolynomial (p ^ (3 : ℕ)) d *
        finiteNegativePhasePolynomial d a
  negativePositiveFactorization :
    (∑ q ∈ thetaPositiveFactorPairs (p ^ (3 : ℕ)),
      finiteNegativePositiveCrossedTranslationPacket d
        (thetaFactorPairLogDisplacement q) a) =
      thetaProductFiberFiniteRadialPolynomial (p ^ (3 : ℕ)) d *
        finitePositivePhasePolynomial d a
  radialEvenCoefficient :
    ∀ l : ℕ,
      (thetaProductFiberFiniteRadialPolynomial (p ^ (3 : ℕ)) d).coeff (2 * l) =
        if l ≤ d then
          ((-1 : ℂ) ^ l *
            (2 * (3 * Real.log p / 2) ^ (2 * l) +
              2 * (Real.log p / 2) ^ (2 * l) : ℝ)) /
            (2 * l).factorial
        else 0

/-- **Prime-cube crossed-phase radial-factorization law.**  At every prime cube and finite cutoff,
both crossed phase channels share one reflected radial factor.  The only channel distinction is the
external positive/negative phase, while every even coefficient of the common factor is the exact
sum of its outer and inner prime-cube radii. -/
theorem thetaPrimeCube_crossedPhaseRadialFactorizationUniversalCertificate
    {p : ℕ} (hp : p.Prime) (d : ℕ) (a : ℝ) :
    ThetaPrimeCubeCrossedPhaseRadialFactorizationUniversalCertificate p d a := by
  exact {
    positiveNegativeFactorization :=
      sum_finitePositiveNegativeCrossedTranslationPacket_factorPairs (p ^ (3 : ℕ)) d a
    negativePositiveFactorization :=
      sum_finiteNegativePositiveCrossedTranslationPacket_factorPairs (p ^ (3 : ℕ)) d a
    radialEvenCoefficient := fun l =>
      thetaProductFiberFiniteRadialPolynomial_primeCube_coeff_two_mul hp d l }

end

end RHTower

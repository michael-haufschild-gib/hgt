import GaloisForLFunctions.ArithmeticPositiveDuality.TheUnitMassBoundaryOfPositiveAnnihilators

/-!
# Arbitrary multiplicity near unit annihilator mass

Integrating `(1 + X^K)^r` for odd `K` gives a positive polynomial whose
normalized translate has a zero of order `r+1` at minus one. As `K` grows,
its nonconstant mass tends to one. Substitution of `2^(β-s)` preserves the
zero order and gives literal positive one-prime Dirichlet polynomials.
-/

noncomputable section
set_option autoImplicit false

open Complex Finset Filter Topology
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

/-- The positive coefficients of the primitive of `(1 + X^(2n+1))^r`. -/
def multiplicityPrimitiveCoefficient (r n j : ℕ) : ℝ≥0 :=
  (r.choose j : ℝ≥0) / ((1 + j * (2 * n + 1) : ℕ) : ℝ≥0)

/-- The normalization that places a zero at minus one. -/
def multiplicityPrimitiveNormalizer (r n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1), (-1 : ℝ) ^ j *
    ((multiplicityPrimitiveCoefficient r n j : ℝ≥0) : ℝ)

/-- The unnormalized nonconstant mass at one. -/
def multiplicityPrimitiveMass (r n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1), ((multiplicityPrimitiveCoefficient r n j : ℝ≥0) : ℝ)

/-- A positive Dirichlet polynomial built from an odd-power primitive. -/
def arbitraryMultiplicityAnnihilator (β : ℝ) (r n : ℕ) : MvPolynomial (Fin 2) ℝ≥0 :=
  1 + MvPolynomial.C ((NNReal.ofReal (multiplicityPrimitiveNormalizer r n))⁻¹) *
    ∑ j ∈ Finset.range (r + 1), MvPolynomial.C (multiplicityPrimitiveCoefficient r n j) *
      scaledTwoMonomial β ^ (1 + j * (2 * n + 1))

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

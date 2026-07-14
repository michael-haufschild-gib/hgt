import GaloisForLFunctions.HTGeometry.PrimeDirichletTailPattern

/-!
# Projective prime tails and the two Euler lifting modes

A signed prime-Dirichlet tail identifies an orientation with its global complement.  Euler local
factors do not forget this sign: equal signs give the same local factor, while opposite signs give
the cyclotomic norm `1 - X^2`.  This file proves that these two local alternatives recover exactly
the two branches of the projective tail classification.

The result is source-free and finite-support algebra.  Analytically, evaluation at `X = p^(-s)`
turns the second mode into the Euler norm identity

`Z_epsilon(s) * Z_{-epsilon}(s) = zeta(2s)`.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open scoped BigOperators

noncomputable section

/-- The generic signed Euler polynomial at one prime coordinate. -/
def primeEulerOrientationPolynomial (b : Bool) : Polynomial ℂ :=
  1 - Polynomial.C (primeDirichletSign b) * Polynomial.X

/-- A one-prime Euler polynomial remembers the Boolean orientation exactly. -/
theorem primeEulerOrientationPolynomial_eq_iff (b c : Bool) :
    primeEulerOrientationPolynomial b = primeEulerOrientationPolynomial c ↔ b = c := by
  constructor
  · intro h
    cases b <;> cases c
    · rfl
    · have hc := congrArg (fun P : Polynomial ℂ => P.coeff 1) h
      norm_num [primeEulerOrientationPolynomial, primeDirichletSign, Polynomial.coeff_one] at hc
    · have hc := congrArg (fun P : Polynomial ℂ => P.coeff 1) h
      norm_num [primeEulerOrientationPolynomial, primeDirichletSign, Polynomial.coeff_one] at hc
    · rfl
  · exact fun h => congrArg primeEulerOrientationPolynomial h

/-- Two one-prime Euler polynomials have cyclotomic norm `1 - X^2` exactly when their signs are
opposite. -/
theorem primeEulerOrientationPolynomial_mul_eq_norm_iff (b c : Bool) :
    primeEulerOrientationPolynomial b * primeEulerOrientationPolynomial c =
        1 - Polynomial.X ^ 2 ↔
      b ≠ c := by
  constructor
  · intro h hbc
    subst c
    cases b
    · have he := congrArg (Polynomial.eval (-1 : ℂ)) h
      norm_num [primeEulerOrientationPolynomial, primeDirichletSign] at he
    · have he := congrArg (Polynomial.eval (1 : ℂ)) h
      norm_num [primeEulerOrientationPolynomial, primeDirichletSign] at he
  · intro h
    cases b <;> cases c <;>
      simp_all [primeEulerOrientationPolynomial, primeDirichletSign] <;> ring

/-- Same-sheet Euler gauge equivalence: the local Euler polynomials differ at only finitely many
coordinates. -/
def PrimeEulerTailGaugeEquivalent {P : Type*} (ε δ : P → Bool) : Prop :=
  {p | primeEulerOrientationPolynomial (ε p) ≠
    primeEulerOrientationPolynomial (δ p)}.Finite

/-- Opposite-sheet Euler norm complementarity: the local product fails to be `1 - X^2` at only
finitely many coordinates. -/
def PrimeEulerTailNormComplementary {P : Type*} (ε δ : P → Bool) : Prop :=
  {p | primeEulerOrientationPolynomial (ε p) * primeEulerOrientationPolynomial (δ p) ≠
    (1 - Polynomial.X ^ 2 : Polynomial ℂ)}.Finite

/-- Same-sheet Euler gauge equivalence is exactly eventual equality of orientations. -/
theorem primeEulerTailGaugeEquivalent_iff_eventuallyEqual
    {P : Type*} (ε δ : P → Bool) :
    PrimeEulerTailGaugeEquivalent ε δ ↔ PrimeOrientationsEventuallyEqual ε δ := by
  have hset :
      {p | primeEulerOrientationPolynomial (ε p) ≠ primeEulerOrientationPolynomial (δ p)} =
        {p | ε p ≠ δ p} := by
    ext p
    simp only [Set.mem_setOf_eq, ne_eq, primeEulerOrientationPolynomial_eq_iff]
  simp only [PrimeEulerTailGaugeEquivalent, PrimeOrientationsEventuallyEqual, hset]

/-- Opposite-sheet Euler norm complementarity is exactly eventual opposition of orientations. -/
theorem primeEulerTailNormComplementary_iff_eventuallyOpposite
    {P : Type*} (ε δ : P → Bool) :
    PrimeEulerTailNormComplementary ε δ ↔ PrimeOrientationsEventuallyOpposite ε δ := by
  have hset :
      {p | primeEulerOrientationPolynomial (ε p) * primeEulerOrientationPolynomial (δ p) ≠
          (1 - Polynomial.X ^ 2 : Polynomial ℂ)} =
        {p | ε p = δ p} := by
    ext p
    simp only [Set.mem_setOf_eq, ne_eq,
      primeEulerOrientationPolynomial_mul_eq_norm_iff, not_not]
  simp only [PrimeEulerTailNormComplementary, PrimeOrientationsEventuallyOpposite, hset]

/-- **Two-mode Euler lifting law.**  Projective dependence of signed prime tails is equivalent to
exactly the union of the same-sheet finite-gauge mode and the opposite-sheet cyclotomic-norm mode.
Thus the global sign forgotten by the projective tail field is recovered by the nonlinear Euler
lift as a two-sheeted alternative. -/
theorem primeOrientationTailPairDependent_iff_eulerModes
    {P : Type*} (ε δ : P → Bool) :
    PrimeOrientationTailPairDependent ε δ ↔
      PrimeEulerTailGaugeEquivalent ε δ ∨ PrimeEulerTailNormComplementary ε δ := by
  rw [primeOrientationTailPairDependent_iff,
    primeEulerTailGaugeEquivalent_iff_eventuallyEqual,
    primeEulerTailNormComplementary_iff_eventuallyOpposite]

/-- The exact finite Euler norm.  The right side is independent of the orientation. -/
theorem primeEulerOrientationFiniteNorm
    {P : Type*} (S : Finset P) (ε : P → Bool) (x : P → ℂ) :
    (∏ p ∈ S, (1 - primeDirichletSign (ε p) * x p)) *
        (∏ p ∈ S, (1 - primeDirichletSign (!(ε p)) * x p)) =
      ∏ p ∈ S, (1 - (x p) ^ 2) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  cases ε p <;> simp [primeDirichletSign] <;> ring

end

end GaloisForLFunctions.RHTower

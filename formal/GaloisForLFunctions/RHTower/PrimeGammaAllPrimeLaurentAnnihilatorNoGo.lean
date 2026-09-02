import GaloisForLFunctions.RHTower.PrimeGammaCofinalBocksteinDeterminantTransgression
import GaloisForLFunctions.HTGeometry.GammaPoleScaleDerivativeLaurentFreeness

/-!
# All-prime Laurent non-erasure of the physical Gamma determinant transgression

At unit clock, the forward physical prime--Gamma rotation determinant is `-p`; the reflected
determinant is its inverse.  Thus every fixed finite algebraic expression in the two local
orientations reduces to a Laurent polynomial in one unit.

This module proves that simultaneous evaluation of that Laurent algebra at every ordinary prime is
injective.  Hence no nonzero fixed finite algebraic local law can annihilate all physical
prime--Gamma determinant transgressions.  This closes the prime-local finite Laurent branch of the
G-CE source-annihilation search.  Any surviving non-erasing annihilator must be genuinely
cross-prime, infinite/singular, or non-algebraic before scalarization.

The result is unconditional and contains no RH premise or divisor-selected input.
-/

open Complex

namespace RHTower

noncomputable section

/-- All-prime profile of the forward physical rotation determinant at unit clock. -/
def primeGammaUnitForwardDeterminantProfile (p : Nat.Primes) : ℂ :=
  (primeGammaPhysicalRotationDeterminant 1 p : ℝ)

@[simp]
theorem primeGammaUnitForwardDeterminantProfile_eq (p : Nat.Primes) :
    primeGammaUnitForwardDeterminantProfile p = -((p : ℕ) : ℂ) := by
  simp [primeGammaUnitForwardDeterminantProfile,
    primeGammaPhysicalRotationDeterminant]

theorem primeGammaUnitForwardDeterminantProfile_ne_zero (p : Nat.Primes) :
    primeGammaUnitForwardDeterminantProfile p ≠ 0 := by
  rw [primeGammaUnitForwardDeterminantProfile_eq]
  exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr p.2.ne_zero)

/-- The reflected physical determinant is exactly the inverse Laurent orientation. -/
theorem primeGammaUnitReflectedDeterminant_eq_inv_forward (p : Nat.Primes) :
    ((primeGammaPhysicalRotationDeterminant (-1) p : ℝ) : ℂ) =
      (primeGammaUnitForwardDeterminantProfile p)⁻¹ := by
  rw [primeGammaPhysicalRotationDeterminant, Real.rpow_neg_one,
    primeGammaUnitForwardDeterminantProfile_eq]
  push_cast
  rw [inv_neg]

/-- Distinct ordinary primes give distinct unit-clock determinant values. -/
theorem primeGammaUnitForwardDeterminantProfile_injective :
    Function.Injective primeGammaUnitForwardDeterminantProfile := by
  intro p q h
  apply Subtype.ext
  rw [primeGammaUnitForwardDeterminantProfile_eq,
    primeGammaUnitForwardDeterminantProfile_eq] at h
  have h' : (((p : ℕ) : ℂ)) = (((q : ℕ) : ℂ)) := by
    simpa using neg_injective h
  exact_mod_cast h'

/-- The all-prime determinant profile as a unit of the pointwise function ring. -/
def primeGammaUnitForwardDeterminantProfileUnit :
    (Nat.Primes → ℂ)ˣ where
  val := primeGammaUnitForwardDeterminantProfile
  inv := fun p => (primeGammaUnitForwardDeterminantProfile p)⁻¹
  val_inv := by
    funext p
    exact mul_inv_cancel₀ (primeGammaUnitForwardDeterminantProfile_ne_zero p)
  inv_val := by
    funext p
    exact inv_mul_cancel₀ (primeGammaUnitForwardDeterminantProfile_ne_zero p)

/-- Simultaneous polynomial evaluation on every unit-clock prime--Gamma determinant. -/
def primeGammaUnitDeterminantPolynomialEval :
    Polynomial ℂ →+* (Nat.Primes → ℂ) :=
  Polynomial.eval₂RingHom (algebraMap ℂ (Nat.Primes → ℂ))
    primeGammaUnitForwardDeterminantProfileUnit

@[simp]
theorem primeGammaUnitDeterminantPolynomialEval_apply
    (P : Polynomial ℂ) (p : Nat.Primes) :
    primeGammaUnitDeterminantPolynomialEval P p =
      P.eval (primeGammaUnitForwardDeterminantProfile p) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [map_add, Pi.add_apply, Polynomial.eval_add, hP, hQ]
  | monomial n a =>
      simp [primeGammaUnitDeterminantPolynomialEval,
        primeGammaUnitForwardDeterminantProfileUnit]

/-- A polynomial is determined by its values on the infinite physical prime--Gamma profile. -/
theorem primeGammaUnitDeterminantPolynomialEval_injective :
    Function.Injective primeGammaUnitDeterminantPolynomialEval := by
  intro P Q hPQ
  apply sub_eq_zero.mp
  let R := P - Q
  apply Polynomial.eq_zero_of_infinite_isRoot R
  letI : Infinite Nat.Primes := Nat.infinite_setOf_prime.to_subtype
  have hRange :
      (Set.range primeGammaUnitForwardDeterminantProfile).Infinite :=
    Set.infinite_range_of_injective
      primeGammaUnitForwardDeterminantProfile_injective
  apply hRange.mono
  intro z hz
  rcases hz with ⟨p, rfl⟩
  change R.IsRoot (primeGammaUnitForwardDeterminantProfile p)
  rw [Polynomial.IsRoot.def]
  have hp := congrFun hPQ p
  rw [primeGammaUnitDeterminantPolynomialEval_apply,
    primeGammaUnitDeterminantPolynomialEval_apply] at hp
  simpa [R, Polynomial.eval_sub] using sub_eq_zero.mpr hp

/-- Simultaneous Laurent evaluation of both physical determinant orientations at every prime. -/
def primeGammaUnitDeterminantLaurentEval :
    LaurentPolynomial ℂ →+* (Nat.Primes → ℂ) :=
  LaurentPolynomial.eval₂ (algebraMap ℂ (Nat.Primes → ℂ))
    primeGammaUnitForwardDeterminantProfileUnit

/-- **All-prime Laurent faithfulness.**  No nonzero Laurent symbol vanishes on every physical
unit-clock prime--Gamma determinant. -/
theorem primeGammaUnitDeterminantLaurentEval_injective :
    Function.Injective primeGammaUnitDeterminantLaurentEval := by
  exact GaloisForLFunctions.laurentPolynomial_eval₂_injective_of_polynomial_eval₂_injective
    (algebraMap ℂ (Nat.Primes → ℂ))
    primeGammaUnitForwardDeterminantProfileUnit
    primeGammaUnitDeterminantPolynomialEval_injective

/-- Exact zero classification for a finite Laurent law on all physical local determinants. -/
theorem primeGammaUnitDeterminantLaurentEval_eq_zero_iff
    (F : LaurentPolynomial ℂ) :
    (∀ p : Nat.Primes, primeGammaUnitDeterminantLaurentEval F p = 0) ↔
      F = 0 := by
  constructor
  · intro hzero
    apply primeGammaUnitDeterminantLaurentEval_injective
    funext p
    simpa using hzero p
  · rintro rfl
    simp

/-- Proposed non-erasing prime-local finite Laurent annihilator for the G-CE source. -/
def GCEPrimeLocalFiniteLaurentAnnihilatorExists : Prop :=
  ∃ F : LaurentPolynomial ℂ, F ≠ 0 ∧
    ∀ p : Nat.Primes, primeGammaUnitDeterminantLaurentEval F p = 0

/-- **G-CE route-class kill.**  No nonzero finite Laurent law in the forward/reflected local
physical determinants can supply the missing all-prime source annihilation. -/
theorem not_GCEPrimeLocalFiniteLaurentAnnihilatorExists :
    ¬ GCEPrimeLocalFiniteLaurentAnnihilatorExists := by
  rintro ⟨F, hF, hzero⟩
  exact hF ((primeGammaUnitDeterminantLaurentEval_eq_zero_iff F).mp hzero)

end

end RHTower

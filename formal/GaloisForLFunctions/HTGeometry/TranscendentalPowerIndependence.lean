import Mathlib

/-!
# Rational independence from a single transcendental

The powers of a transcendental element are linearly independent over the base field
(`Transcendental.linearIndependent_pow`): a vanishing finite rational combination of powers
is the evaluation of a polynomial that annihilates the element, so the polynomial — and hence
every coefficient — is zero.  Restricting to any injective index selection, an arbitrary
finite family of distinct powers `τ^{ν v}` is rationally independent
(`transcendental_pow_comp_linearIndependent`).

This is the realization device for constraint-dimension bounds: a family of translation data
whose only requirement is global rational independence can always be produced from one
transcendental number, adding a single independent coordinate `τ^{ν v}` to each vector.
-/

open Polynomial

namespace GaloisForLFunctions

/-- Evaluating the polynomial with coefficient list `l` at `x` is the linear combination of
the powers of `x` with those coefficients. -/
theorem aeval_ofFinsupp_eq_linearCombination {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (x : A) (l : ℕ →₀ R) :
    (aeval x) (⟨AddMonoidAlgebra.ofCoeff l⟩ : R[X]) =
      Finsupp.linearCombination R (fun n : ℕ => x ^ n) l := by
  rw [Finsupp.linearCombination_apply, aeval_def, eval₂_eq_sum, Polynomial.sum]
  simp only [Polynomial.coeff_ofFinsupp, Polynomial.support]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def]

/-- **Powers of a transcendental are linearly independent.**  If `x` is transcendental over
`R`, the family `n ↦ xⁿ` is `R`-linearly independent. -/
theorem Transcendental.linearIndependent_pow {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x : A} (hx : Transcendental R x) :
    LinearIndependent R (fun n : ℕ => x ^ n) := by
  rw [linearIndependent_iff]
  intro l hl
  have hp : (aeval x) (⟨AddMonoidAlgebra.ofCoeff l⟩ : R[X]) = 0 := by
    rw [aeval_ofFinsupp_eq_linearCombination]; exact hl
  have hz : (⟨AddMonoidAlgebra.ofCoeff l⟩ : R[X]) = 0 :=
    (transcendental_iff.mp hx) _ hp
  apply Finsupp.ext
  intro n
  have := congrArg (Polynomial.coeff · n) hz
  simpa [Polynomial.coeff_ofFinsupp] using this

/-- **Distinct powers of a transcendental are rationally independent.**  For an injective
index map `ν`, the family `v ↦ τ^{ν v}` is linearly independent over `R`.  This is the
one-coordinate realization of an arbitrary rationally-independent translation family. -/
theorem transcendental_pow_comp_linearIndependent {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {ι : Type*} {τ : A} (hτ : Transcendental R τ) {ν : ι → ℕ}
    (hν : Function.Injective ν) :
    LinearIndependent R (fun v : ι => τ ^ ν v) :=
  ((Transcendental.linearIndependent_pow hτ).comp ν hν)

end GaloisForLFunctions

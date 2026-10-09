import GaloisForLFunctions.HTGeometry.PaperPrimePolynomialClocks
import GaloisForLFunctions.HTGeometry.PaperLNDLinearAction

/-!
# Genuine additive prime-coordinate actions on convolution polynomials

The source exponential integrates each terminating prime clock. The chosen
prime variable moves by the additive parameter, other prime variables remain
fixed, and joint invariants are exactly scalars.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate CoactionLND

noncomputable section

attribute [local instance 2000] Algebra.toModule
attribute [local instance 2100] Semiring.toModule

local instance (S : Finset Nat.Primes) : CharZero (paperPrimePolynomialAlgebra S) :=
  charZero_of_injective_algebraMap (algebraMap ℂ (paperPrimePolynomialAlgebra S)).injective

/-- The source exponential action of a literal native prime clock. -/
def paperPrimePolynomialAction (S : Finset Nat.Primes) (p : S) :
    PolynomialAdditiveAction ℂ (paperPrimePolynomialAlgebra S) :=
  exponentialAction (k := ℂ) (A := paperPrimePolynomialAlgebra S) (paperPrimePolynomialClock S p)
    (paperPrimePolynomialClock_locallyNilpotent S p)

@[simp] theorem paperPrimePolynomialAction_derivation (S : Finset Nat.Primes) (p : S) :
    (paperPrimePolynomialAction S p).derivation = paperPrimePolynomialClock S p :=
  exponentialAction_derivation _ _

/-- Every prime variable has its exact affine polynomial orbit. -/
theorem paperPrimePolynomialAction_generator (S : Finset Nat.Primes) (p q : S) :
    (paperPrimePolynomialAction S p).toAlgHom (paperPrimePolynomialGenerator S q) =
      Polynomial.C (paperPrimePolynomialGenerator S q) +
        Polynomial.C (if q = p then 1 else 0) * Polynomial.X := by
  classical
  have htwo : paperPrimePolynomialClock S p
      (paperPrimePolynomialClock S p (paperPrimePolynomialGenerator S q)) = 0 := by
    rw [paperPrimePolynomialClock_generator]
    split_ifs <;> simp
  rw [paperPrimePolynomialAction, paperLND_exponential_linear_on _ _ _ htwo,
    paperPrimePolynomialClock_generator]

/-- Scalar specialization translates the selected prime coordinate and fixes the others. -/
theorem paperPrimePolynomialAction_specialize_generator
    (S : Finset Nat.Primes) (p q : S) (t : ℂ) :
    (paperPrimePolynomialAction S p).specialize t (paperPrimePolynomialGenerator S q) =
      paperPrimePolynomialGenerator S q +
        if q = p then algebraMap ℂ (paperPrimePolynomialAlgebra S) t else 0 := by
  classical
  rw [PolynomialAdditiveAction.specialize_apply, paperPrimePolynomialAction_generator]
  split_ifs <;> simp

/-- The coordinate action is nontrivial on the actual convolution subalgebra. -/
theorem paperPrimePolynomialAction_moves_generator (S : Finset Nat.Primes) (p : S) :
    (paperPrimePolynomialAction S p).toAlgHom (paperPrimePolynomialGenerator S p) ≠
      Polynomial.C (paperPrimePolynomialGenerator S p) := by
  intro h
  have he := congrArg (fun P => Polynomial.coeff P 1) h
  simp [paperPrimePolynomialAction_generator] at he

/-- Polynomial invariants of a prime action are exactly native prime-clock constants. -/
theorem paperPrimePolynomialAction_fixed_iff (S : Finset Nat.Primes) (p : S)
    (f : paperPrimePolynomialAlgebra S) :
    (paperPrimePolynomialAction S p).toAlgHom f = Polynomial.C f ↔
      paperPrimePolynomialClock S p f = 0 := by
  rw [PolynomialAdditiveAction.invariant_iff_derivation_eq_zero,
    paperPrimePolynomialAction_derivation]

/-- All prime actions together fix exactly the scalar convolution constants. -/
theorem paperPrimePolynomialAction_common_invariants (S : Finset Nat.Primes)
    (f : paperPrimePolynomialAlgebra S) :
    (∀ p : S, (paperPrimePolynomialAction S p).toAlgHom f = Polynomial.C f) ↔
      ∃ c : ℂ, f = algebraMap ℂ (paperPrimePolynomialAlgebra S) c := by
  simp only [paperPrimePolynomialAction_fixed_iff]
  exact paperPrimePolynomialClock_common_kernel S f

/-- The complete polynomial actions agree under enlargement, not only their first derivatives. -/
theorem paperPrimePolynomialAction_inclusion {S T : Finset Nat.Primes} (h : S ⊆ T)
    (p : S) (f : paperPrimePolynomialAlgebra S) :
    Polynomial.map (Subalgebra.inclusion (paperPrimePolynomialAlgebra_mono h)).toRingHom
        ((paperPrimePolynomialAction S p).toAlgHom f) =
      (paperPrimePolynomialAction T ⟨p.1, h p.2⟩).toAlgHom
        (Subalgebra.inclusion (paperPrimePolynomialAlgebra_mono h) f) := by
  simp only [paperPrimePolynomialAction, exponentialAction_toAlgHom]
  apply Polynomial.ext
  intro m
  rw [Polynomial.coeff_map, LNDExponential.coeff_exponential,
    LNDExponential.coeff_exponential, paperPrimePolynomialClock_iterate_inclusion]
  exact (Subalgebra.inclusion (paperPrimePolynomialAlgebra_mono h)).toLinearMap.map_smul
    ((m.factorial : ℂ)⁻¹) ((paperPrimePolynomialClock S p)^[m] f)

end

end GaloisForLFunctions.HTGeometry

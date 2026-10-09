import GaloisForLFunctions.HTGeometry.PaperTerminatingCore
import GaloisForLFunctions.HTGeometry.PaperPrimePolynomialExtensionBoundary

/-!
# Global formal flows on the Dirichlet-convolution algebra

The full arithmetic-function algebra has no nonzero locally nilpotent
derivations. Nevertheless each of its derivations has a faithful formal
flow. Native prime flows extend all finite-prime polynomial translations;
their polynomial-valued locus is a proper, canonically constructed algebra.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

/-- On the full arithmetic algebra, an everywhere-polynomial formal flow is exactly trivial. -/
theorem paperArithmeticFormal_all_polynomial_iff
    (D : Derivation ℂ (ArithmeticFunction ℂ) (ArithmeticFunction ℂ)) :
    (∀ f, ∃ P : Polynomial (ArithmeticFunction ℂ),
      paperFormalExponential D f = (P : PowerSeries (ArithmeticFunction ℂ))) ↔ D = 0 := by
  rw [paperFormalExponential_all_polynomial_iff, paperArithmeticFunction_LND_iff_eq_zero]

/-- The maximal terminating algebra fills the ambient algebra exactly for the zero clock. -/
theorem paperArithmeticTerminatingCore_eq_top_iff
    (D : Derivation ℂ (ArithmeticFunction ℂ) (ArithmeticFunction ℂ)) :
    paperTerminatingCore D = ⊤ ↔ D = 0 := by
  rw [paperTerminatingCore_eq_top_iff, paperArithmeticFunction_LND_iff_eq_zero]

/-- A global formal prime translation, on every arithmetic function. -/
def paperArithmeticPrimeFormalFlow (q : Nat.Primes) :
    ArithmeticFunction ℂ →ₐ[ℂ] PowerSeries (ArithmeticFunction ℂ) :=
  paperFormalExponential (primeArithmeticDerivation (q : ℕ) q.property)

/-- Each individual prime coordinate undergoes the expected exact translation. -/
theorem paperArithmeticPrimeFormalFlow_coordinate (p q : Nat.Primes) :
    paperArithmeticPrimeFormalFlow p (paperPrimeCoordinate q) =
      PowerSeries.C (paperPrimeCoordinate q) +
        PowerSeries.C (if p = q then 1 else 0) * PowerSeries.X := by
  classical
  let D := primeArithmeticDerivation (p : ℕ) p.property
  have hfirst : D (paperPrimeCoordinate q) = if p = q then 1 else 0 := by
    simp only [D, primeArithmeticDerivation_apply, paperPrimeCoordinate_primeDeriv]
  have htwo : D (D (paperPrimeCoordinate q)) = 0 := by
    rw [hfirst]
    split_ifs <;> simp
  change paperFormalExponential D (paperPrimeCoordinate q) = _
  rw [paperFormalExponential_linear_on D _ htwo, hfirst]

/-- Global formal prime motion is nontrivial despite the absence of global polynomial actions. -/
theorem paperArithmeticPrimeFormalFlow_moves_coordinate (q : Nat.Primes) :
    paperArithmeticPrimeFormalFlow q (paperPrimeCoordinate q) ≠
      PowerSeries.C (paperPrimeCoordinate q) := by
  intro h
  have he := congrArg (PowerSeries.coeff 1) h
  simp [paperArithmeticPrimeFormalFlow, primeArithmeticDerivation_apply,
    paperPrimeCoordinate_primeDeriv] at he

/-- The existing finite-prime actions are literal restrictions of the global formal flow. -/
theorem paperArithmeticPrimeFormalFlow_chart (S : Finset Nat.Primes) (p : S)
    (f : paperPrimePolynomialAlgebra S) :
    paperArithmeticPrimeFormalFlow p.val (f : ArithmeticFunction ℂ) =
      PowerSeries.map (paperPrimePolynomialAlgebra S).val.toRingHom
        ((paperPrimePolynomialAction S p).toAlgHom f :
          PowerSeries (paperPrimePolynomialAlgebra S)) := by
  have he := paperFormalExponential_naturality (paperPrimePolynomialClock S p)
    (primeArithmeticDerivation (p.val : ℕ) p.val.property)
    (paperPrimePolynomialAlgebra S).val
    (fun a => (paperPrimePolynomialClock_coe S p a).symm) f
  rw [paperFormalExponential_eq_additiveAction (paperPrimePolynomialClock S p)
    (paperPrimePolynomialClock_locallyNilpotent S p) f] at he
  exact he

/-- Every finite-prime chart lies in each of its active prime's maximal terminating cores. -/
theorem paperPrimePolynomialAlgebra_le_terminatingCore (S : Finset Nat.Primes) (p : S) :
    paperPrimePolynomialAlgebra S ≤
      paperTerminatingCore (primeArithmeticDerivation (p.val : ℕ) p.val.property) := by
  have h := paperTerminatingCore_maximal
    (primeArithmeticDerivation (p.val : ℕ) p.val.property) (paperPrimePolynomialAlgebra S)
    (paperPrimePolynomialClock S p) (paperPrimePolynomialClock_locallyNilpotent S p)
    (fun a => (paperPrimePolynomialClock_coe S p a).symm)
  exact h

/-- Some inputs necessarily have genuinely infinite prime-flow series. -/
theorem paperArithmeticPrimeFormalFlow_exists_nonpolynomial (q : Nat.Primes) :
    ∃ f : ArithmeticFunction ℂ, ∀ P : Polynomial (ArithmeticFunction ℂ),
      paperArithmeticPrimeFormalFlow q f ≠ (P : PowerSeries (ArithmeticFunction ℂ)) := by
  classical
  have h : ¬ ∀ f : ArithmeticFunction ℂ, ∃ P : Polynomial (ArithmeticFunction ℂ),
      paperArithmeticPrimeFormalFlow q f = (P : PowerSeries (ArithmeticFunction ℂ)) := by
    intro h
    exact paperNativePrimeDerivation_not_locallyNilpotent q
      ((paperFormalExponential_all_polynomial_iff _).mp h)
  push Not at h
  exact h

/-- The native prime's maximal terminating algebra remains strictly smaller than the full ring. -/
theorem paperArithmeticPrimeTerminatingCore_ne_top (q : Nat.Primes) :
    paperTerminatingCore (primeArithmeticDerivation (q : ℕ) q.property) ≠ ⊤ := by
  rw [ne_eq, paperTerminatingCore_eq_top_iff]
  exact paperNativePrimeDerivation_not_locallyNilpotent q

/-- The native rotated logarithmic clock also integrates globally as a formal flow. -/
def paperArithmeticLogFormalFlow :
    ArithmeticFunction ℂ →ₐ[ℂ] PowerSeries (ArithmeticFunction ℂ) :=
  paperFormalExponential rotatedLogArithmeticDerivationComplex

/-- Each Dirichlet coefficient carries its exact divided logarithmic-frequency powers. -/
theorem paperArithmeticLogFormalFlow_coeff (f : ArithmeticFunction ℂ) (n m : ℕ) :
    PowerSeries.coeff m (paperArithmeticLogFormalFlow f) n =
      ((m.factorial : ℂ)⁻¹) * (Complex.I * (Real.log n : ℂ)) ^ m * f n := by
  simp only [paperArithmeticLogFormalFlow, paperFormalExponential_coeff,
    ArithmeticFunction.smul_map, paperArithmeticLog_iterate_apply, smul_eq_mul]
  rw [mul_assoc]

/-- Only scalar convolution constants have polynomial logarithmic-flow orbits. -/
theorem paperArithmeticLogFormalFlow_polynomial_iff (f : ArithmeticFunction ℂ) :
    (∃ P : Polynomial (ArithmeticFunction ℂ),
      paperArithmeticLogFormalFlow f = (P : PowerSeries (ArithmeticFunction ℂ))) ↔
      f = f 1 • (1 : ArithmeticFunction ℂ) := by
  rw [paperArithmeticLogFormalFlow, paperFormalExponential_polynomial_iff,
    paperArithmeticLog_terminates_iff]

/-- For this diagonal clock, a polynomial orbit is already a fixed orbit. -/
theorem paperArithmeticLogFormalFlow_polynomial_iff_fixed (f : ArithmeticFunction ℂ) :
    (∃ P : Polynomial (ArithmeticFunction ℂ),
      paperArithmeticLogFormalFlow f = (P : PowerSeries (ArithmeticFunction ℂ))) ↔
      paperArithmeticLogFormalFlow f = PowerSeries.C f := by
  rw [paperArithmeticLogFormalFlow_polynomial_iff, paperArithmeticLogFormalFlow,
    paperFormalExponential_fixed_iff, paperArithmeticLog_kernel_iff]

end

end GaloisForLFunctions.HTGeometry

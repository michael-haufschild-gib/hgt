import GaloisForLFunctions.HTGeometry.PrimeValueJacobianCriterion
import GaloisForLFunctions.HTGeometry.PrimeValueJacobianCoefficientField
import GaloisForLFunctions.HTGeometry.HelsonPhaseAnalyticJets

/-!
# The shifted derivative rectangle of a Helson zeta function is algebraically independent

The prime-value criterion needs nothing but the values at the primes, so it applies to the
Dirichlet series of a completely multiplicative function — which is supported on all integers — as
readily as to a prime-supported carrier.  For a unimodular phase the prime values of the shifted
derivative rectangle are exactly the shift–jet palette of the phase, whose tail rank is full.

This is Pong's conclusion for `Z_chi` itself: for one source and any finite palette of shifts with
distinct real parts, the shifted derivatives of the Helson zeta function are algebraically
independent.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial ArithmeticFunction Finset

noncomputable section

/-- The shifted rotated jet of an arbitrary arithmetic function: the coefficient stream of
`(d/ds)^k Z(s + a)` in the rotated normalization. -/
def arithmeticShiftedRotatedJet (f : ArithmeticFunction ℂ) (a : ℂ) (k : ℕ) :
    ArithmeticFunction ℂ where
  toFun n := cpowWeight a n * (Complex.I * (Real.log n : ℂ)) ^ k * f n
  map_zero' := by simp

@[simp] theorem arithmeticShiftedRotatedJet_apply (f : ArithmeticFunction ℂ) (a : ℂ) (k n : ℕ) :
    arithmeticShiftedRotatedJet f a k n
      = cpowWeight a n * (Complex.I * (Real.log n : ℂ)) ^ k * f n := rfl

/-- At a prime the jet is the corresponding entry of the shift–jet palette. -/
theorem arithmeticShiftedRotatedJet_apply_prime (f : ArithmeticFunction ℂ) (a : ℂ) (k : ℕ)
    (p : Nat.Primes) :
    arithmeticShiftedRotatedJet f a k (p : ℕ)
      = f (p : ℕ) * primeShiftFactor a p * rotatedPrimeLogClock p ^ k := by
  rw [arithmeticShiftedRotatedJet_apply,
    show cpowWeight a (p : ℕ) = primeShiftFactor a p from cpowWeight_prime_eq_primeShiftFactor a p]
  simp only [rotatedPrimeLogClock, primeLogClock]
  ring

/-- **The shifted derivative rectangle of a Dirichlet series with nowhere-vanishing prime
coefficients is algebraically independent.**  No hypothesis on the coefficients away from the
primes: the criterion sees only the prime values. -/
theorem algebraicIndependent_arithmeticShiftedRotatedJets {A : Type*} [Fintype A] [DecidableEq A]
    (f : ArithmeticFunction ℂ) (hf : ∀ p : Nat.Primes, f (p : ℕ) ≠ 0)
    (alpha : A → ℂ) (hdistinct : Function.Injective fun a => (alpha a).re) (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun ak : A × Fin (m + 1) => arithmeticShiftedRotatedJet f (alpha ak.1) ak.2) := by
  classical
  refine algebraicIndependent_of_primeValueIndependent _ ?_
  refine primeValueIndependent_of_tailIndependent _ ?_
  have htail := phasePrimeShiftedRotatedJet_tailIndependent
    (fun p : Nat.Primes => f (p : ℕ)) hf alpha hdistinct m
  convert htail using 1
  funext ak p
  exact arithmeticShiftedRotatedJet_apply_prime f (alpha ak.1) ak.2 p

/-- **Pong's conclusion for a Helson zeta function.**  For a completely multiplicative unimodular
phase the coefficient stream is nowhere vanishing at the primes, so every finite rectangle of
shifted derivatives is algebraically independent. -/
theorem algebraicIndependent_helsonZetaShiftedJets {A : Type*} [Fintype A] [DecidableEq A]
    (f : ArithmeticFunction ℂ) (hf : ∀ p : Nat.Primes, ‖f (p : ℕ)‖ = 1)
    (alpha : A → ℂ) (hdistinct : Function.Injective fun a => (alpha a).re) (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun ak : A × Fin (m + 1) => arithmeticShiftedRotatedJet f (alpha ak.1) ak.2) := by
  refine algebraicIndependent_arithmeticShiftedRotatedJets f (fun p => ?_) alpha hdistinct m
  intro h0
  have := hf p
  rw [h0, norm_zero] at this
  exact zero_ne_one this

/-- **Pong's conclusion for a Helson zeta function over `E_fin`.** -/
theorem algebraicIndependent_helsonZetaShiftedJets_over_finitePrimeCoefficientField
    {A : Type*} [Fintype A] [DecidableEq A]
    (f : ArithmeticFunction ℂ) (hf : ∀ p : Nat.Primes, ‖f (p : ℕ)‖ = 1)
    (alpha : A → ℂ) (hdistinct : Function.Injective fun a => (alpha a).re) (m : ℕ) :
    AlgebraicIndependent finitePrimeCoefficientField
      (fun ak : A × Fin (m + 1) =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticShiftedRotatedJet f (alpha ak.1) ak.2)) := by
  classical
  have hf0 : ∀ p : Nat.Primes, f (p : ℕ) ≠ 0 := by
    intro p h0
    have := hf p
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  refine algebraicIndependent_over_finitePrimeCoefficientField_of_tailIndependent _ ?_
  have htail := phasePrimeShiftedRotatedJet_tailIndependent
    (fun p : Nat.Primes => f (p : ℕ)) hf0 alpha hdistinct m
  convert htail using 1
  funext ak p
  exact arithmeticShiftedRotatedJet_apply_prime f (alpha ak.1) ak.2 p

/-- **Pong's conclusion for a Helson zeta function over the card's `E_fin(s)`.** -/
theorem algebraicIndependent_helsonZetaShiftedJets_over_finitePrimeRationalCoefficientField
    {A : Type*} [Fintype A] [DecidableEq A]
    (f : ArithmeticFunction ℂ) (hf : ∀ p : Nat.Primes, ‖f (p : ℕ)‖ = 1)
    (alpha : A → ℂ) (hdistinct : Function.Injective fun a => (alpha a).re) (m : ℕ) :
    AlgebraicIndependent finitePrimeRationalCoefficientField
      (fun ak : A × Fin (m + 1) =>
        algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
          (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (arithmeticShiftedRotatedJet f (alpha ak.1) ak.2))) :=
  algebraicIndependent_constants_over_finitePrimeRationalCoefficientField _
    (algebraicIndependent_helsonZetaShiftedJets_over_finitePrimeCoefficientField
      f hf alpha hdistinct m)

/-! ### The analytic form -/

/-- A coefficientwise bounded stream sits in the translation-stable finite-abscissa algebra. -/
def boundedFiniteAbscissa (f : ArithmeticFunction ℂ) (hf : ∀ n : ℕ, ‖f n‖ ≤ 1) :
    finiteAbscissaArithmeticSubalgebra := by
  refine ⟨f, 1, ?_⟩
  intro y hy
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => hf n) ?_
  simpa using hy

/-- The shifted rotated jet of a bounded stream, inside the finite-abscissa algebra. -/
def boundedShiftedRotatedJet (f : ArithmeticFunction ℂ) (hf : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (a : ℂ) (k : ℕ) : finiteAbscissaArithmeticSubalgebra :=
  finiteAbscissaDirichletShift a
    ((finiteAbscissaRotatedDeriv^[k]) (boundedFiniteAbscissa f hf))

theorem boundedShiftedRotatedJet_coe (f : ArithmeticFunction ℂ) (hf : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (a : ℂ) (k : ℕ) :
    (boundedShiftedRotatedJet f hf a k).1 = arithmeticShiftedRotatedJet f a k := by
  ext n
  rw [boundedShiftedRotatedJet, finiteAbscissaDirichletShift_apply,
    finiteAbscissaRotatedDeriv_iterate_apply, arithmeticShiftedRotatedJet_apply]
  show cpowWeight a n * ((Complex.I * (Real.log n : ℂ)) ^ k * f n) = _
  ring

/-- **The analytic form of Pong's conclusion for a Helson zeta function.**  The shifted derivative
rectangle is algebraically independent as a family of actual analytic upper-end germs. -/
theorem algebraicIndependent_helsonZetaShiftedUpperEndGerms
    {A : Type*} [Fintype A] [DecidableEq A]
    (f : ArithmeticFunction ℂ) (hf : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (hfp : ∀ p : Nat.Primes, f (p : ℕ) ≠ 0)
    (alpha : A → ℂ) (hdistinct : Function.Injective fun a => (alpha a).re) (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun ak : A × Fin (m + 1) =>
        finiteAbscissaLSeriesToUpperEndGerm (boundedShiftedRotatedJet f hf (alpha ak.1) ak.2)) := by
  classical
  have hraw := algebraicIndependent_arithmeticShiftedRotatedJets f hfp alpha hdistinct m
  let incl : finiteAbscissaArithmeticSubalgebra →ₐ[ℂ] ArithmeticFunction ℂ :=
    finiteAbscissaArithmeticSubalgebra.val
  have hincl : Function.Injective incl := fun x y hxy => Subtype.ext hxy
  have hsub : AlgebraicIndependent ℂ
      (fun ak : A × Fin (m + 1) => boundedShiftedRotatedJet f hf (alpha ak.1) ak.2) := by
    apply (AlgHom.algebraicIndependent_iff incl hincl).mp
    convert hraw using 1
    funext ak
    exact boundedShiftedRotatedJet_coe f hf (alpha ak.1) ak.2
  exact hsub.map' finiteAbscissaLSeriesToUpperEndGerm_injective

end

end GaloisForLFunctions.HTGeometry

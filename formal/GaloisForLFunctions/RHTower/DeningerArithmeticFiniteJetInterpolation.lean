import GaloisForLFunctions.RHTower.DeningerArithmeticContinuousJets
import GaloisForLFunctions.RHTower.FiniteHermiteCRT

/-!
# Finite jet interpolation in Deninger arithmetic cohomology

Polynomial Hermite CRT realizes every finite packet of local polynomial residue classes.  Since
polynomials are compact-open entire sources, this gives the finite-stage surjectivity required by
the global Xi-divisor jet map.

This theorem is unconditional but deliberately finite.  Passing to the full divisor requires a
normally convergent interpolation construction (or Cartan theorem B); that separate infinite
theorem is not hidden here.
-/

open Complex Function Polynomial

namespace RHTower

noncomputable section

/-- A complex polynomial as an element of the compact-open entire source. -/
def deningerCompactOpenPolynomial (P : Polynomial ℂ) :
    DeningerCompactOpenEntire :=
  ⟨⟨fun z => P.eval z, Polynomial.continuous P⟩,
    Polynomial.differentiable P⟩

@[simp]
theorem deningerCompactOpenPolynomial_apply
    (P : Polynomial ℂ) (z : ℂ) :
    deningerCompactOpenPolynomial P z = P.eval z :=
  rfl

/-- Analytic iterated derivatives of polynomial evaluation equal formal iterated derivatives. -/
theorem iteratedDeriv_deningerPolynomial_eval
    (P : Polynomial ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w => P.eval w) z =
      (Polynomial.derivative^[n] P).eval z := by
  induction n generalizing P with
  | zero =>
      simp
  | succ n ih =>
      rw [iteratedDeriv_succ']
      have hderiv :
          deriv (fun w => P.eval w) =
            fun w => (Polynomial.derivative P).eval w := by
        funext w
        exact Polynomial.deriv P
      rw [hderiv, ih, Function.iterate_succ_apply']
      rw [← Function.iterate_succ_apply]
      rw [Function.iterate_succ_apply']

/-- The compact-open jet of a polynomial source is its formal polynomial jet. -/
theorem deningerCompactOpenJet_polynomial
    (P : Polynomial ℂ) (n : ℕ) (z : ℂ) :
    deningerCompactOpenJet z n (deningerCompactOpenPolynomial P) =
      (Polynomial.derivative^[n] P).eval z := by
  rw [deningerCompactOpenJet_apply]
  exact iteratedDeriv_deningerPolynomial_eval P n z

/--
Finite-stage compact-open Hermite interpolation: one polynomial entire source realizes arbitrary
local polynomial residue classes at finitely many distinct points.
-/
theorem exists_deningerCompactOpenPolynomial_finiteJets
    {ι : Type*} [Finite ι]
    (w : ι → ℂ) (hw : Function.Injective w)
    (m : ι → ℕ) (target : ι → Polynomial ℂ) :
    ∃ F : DeningerCompactOpenEntire, ∀ i n, n < m i →
      deningerCompactOpenJet (w i) n F =
        (Polynomial.derivative^[n] (target i)).eval (w i) := by
  obtain ⟨B, hB⟩ :=
    exists_polynomial_iterateDerivative_eval_eq w hw m target
  refine ⟨deningerCompactOpenPolynomial B, ?_⟩
  intro i n hn
  rw [deningerCompactOpenJet_polynomial]
  exact hB i n hn

/--
Xi-specific finite-stage interpolation.  Every finite packet of local polynomial classes on the
actual Xi divisor has a compact-open entire representative.
-/
theorem exists_deningerCompactOpenPolynomial_finiteXiJets
    (S : Finset XiDivisorSupport)
    (target : ↥S → Polynomial ℂ) :
    ∃ F : DeningerCompactOpenEntire,
      ∀ rho : ↥S, ∀ n, n < xiSupportMultiplicity rho.1 →
        deningerCompactOpenJet
            (xiSpectralPointSupport rho.1) n F =
          (Polynomial.derivative^[n] (target rho)).eval
            (xiSpectralPointSupport rho.1) := by
  refine exists_deningerCompactOpenPolynomial_finiteJets
    (fun rho : ↥S => xiSpectralPointSupport rho.1) ?_
    (fun rho : ↥S => xiSupportMultiplicity rho.1)
    target
  intro rho tau h
  apply Subtype.ext
  exact xiSpectralPointSupport_injective h

end

end RHTower

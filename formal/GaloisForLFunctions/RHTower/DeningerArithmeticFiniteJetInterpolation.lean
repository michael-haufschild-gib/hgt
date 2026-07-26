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

/-- Centered Taylor polynomial realizing one arbitrary finite derivative packet. -/
def deningerLocalJetPolynomial
    (w : ℂ) {m : ℕ} (jet : Fin m → ℂ) :
    Polynomial ℂ :=
  ∑ k : Fin m,
    Polynomial.C (jet k / (k.val.factorial : ℂ)) *
      (Polynomial.X - Polynomial.C w) ^ k.val

/-- The centered local polynomial has exactly the prescribed derivative jets. -/
theorem deningerLocalJetPolynomial_iterateDerivative_eval
    (w : ℂ) {m : ℕ} (jet : Fin m → ℂ)
    {n : ℕ} (hn : n < m) :
    (Polynomial.derivative^[n]
      (deningerLocalJetPolynomial w jet)).eval w =
        jet ⟨n, hn⟩ := by
  rw [deningerLocalJetPolynomial,
    Polynomial.iterate_derivative_sum,
    Polynomial.eval_finsetSum,
    Fintype.sum_eq_single (⟨n, hn⟩ : Fin m)]
  · rw [Polynomial.iterate_derivative_C_mul,
      Polynomial.iterate_derivative_X_sub_pow_self,
      Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_natCast]
    have hfac : (n.factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr n.factorial_ne_zero
    exact div_mul_cancel₀ _ hfac
  · intro k hkn
    rw [Polynomial.iterate_derivative_C_mul,
      Polynomial.iterate_derivative_X_sub_pow,
      Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_smul, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self]
    by_cases hlt : k.val < n
    · simp [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
    · have hne : k.val ≠ n := by
        intro h
        apply hkn
        exact Fin.ext h
      have hgt : n < k.val := lt_of_le_of_ne
        (Nat.le_of_not_gt hlt) (Ne.symm hne)
      simp [Nat.sub_ne_zero_of_lt hgt]

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

/--
Scalar form of Xi finite interpolation: every arbitrary finite packet of multiplicity-bounded
complex jet values is realized by one compact-open polynomial source.
-/
theorem exists_deningerCompactOpenPolynomial_finiteXiScalarJets
    (S : Finset XiDivisorSupport)
    (target :
      (rho : ↥S) → DeningerArithmeticJetIndex rho.1 → ℂ) :
    ∃ F : DeningerCompactOpenEntire,
      ∀ rho : ↥S, ∀ k : DeningerArithmeticJetIndex rho.1,
        deningerCompactOpenJet
            (xiSpectralPointSupport rho.1) k F =
          target rho k := by
  let localTarget : ↥S → Polynomial ℂ := fun rho =>
    deningerLocalJetPolynomial
      (xiSpectralPointSupport rho.1) (target rho)
  obtain ⟨F, hF⟩ :=
    exists_deningerCompactOpenPolynomial_finiteXiJets
      S localTarget
  refine ⟨F, ?_⟩
  intro rho k
  rw [hF rho k k.isLt]
  exact deningerLocalJetPolynomial_iterateDerivative_eval
    (xiSpectralPointSupport rho.1) (target rho) k.isLt

end

end RHTower

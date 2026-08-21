import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveEulerCorrection
import GaloisForLFunctions.RHTower.ChenGuptaLiAnalyticAnchor

/-!
# Primitive conductor finite Euler factor

This file promotes the finite coefficientwise Möbius correction for an
imprimitive Dirichlet character to an identity of Dirichlet `L`-series in the
certified absolute-convergence half-plane.

The result is deliberately restricted to `Re(s) > 1`. Extending it by
analytic continuation and proving that the finite factor does not add zeros
in a zero-density region are separate closed tasks.
-/

open Complex LSeries DirichletCharacter

noncomputable section

namespace RHTower

/-- The finite primitive Euler correction has a summable `L`-series at every
complex point because its support is contained in the finite divisor set of
the original modulus. -/
theorem lseriesSummable_cglPrimitiveEulerCorrection
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : ℂ) :
    LSeriesSummable (cglPrimitiveEulerCorrection n χ) s := by
  unfold LSeriesSummable
  apply summable_of_hasFiniteSupport
  rw [Function.HasFiniteSupport]
  apply Set.Finite.subset (Finset.finite_toSet (n + 1).divisors)
  intro d hd
  simp only [Function.mem_support] at hd
  by_contra hmem
  have hnot : d ∉ (n + 1).divisors := by
    intro hdmem
    exact hmem hdmem
  rw [LSeries.term] at hd
  by_cases hd0 : d = 0
  · simp [hd0] at hd
  · simp [hd0, cglPrimitiveEulerCorrection, hnot] at hd

/-- The primitive conductor `L`-function attached to a certified nonprincipal
input character. Positivity of the canonical conductor supplies the required
nonzero-modulus instance internally. -/
noncomputable def cglPrimitiveLFunction
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : ℂ) : ℂ := by
  letI : NeZero (cglPrimitiveCharacterReduction n χ).conductor :=
    ⟨Nat.ne_of_gt (cglPrimitiveCharacterReduction n χ).conductor_pos⟩
  exact DirichletCharacter.LFunction (cglPrimitiveCharacterReduction n χ).primitiveCharacter s

/-- In the certified absolute-convergence half-plane, the original character
`L`-function is the product of its finite primitive correction and canonical
primitive conductor `L`-function. -/
theorem cglPrimitiveEulerCorrection_lseries_mul_primitiveLFunction_eq_input
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : CGLAbsoluteConvergencePoint) :
    LSeries (cglPrimitiveEulerCorrection n χ) s.1 *
      cglPrimitiveLFunction n χ s.1 =
      DirichletCharacter.LFunction χ.1 s.1 := by
  unfold cglPrimitiveLFunction
  letI : NeZero (cglPrimitiveCharacterReduction n χ).conductor :=
    ⟨Nat.ne_of_gt (cglPrimitiveCharacterReduction n χ).conductor_pos⟩
  calc
    LSeries (cglPrimitiveEulerCorrection n χ) s.1 *
        DirichletCharacter.LFunction (cglPrimitiveCharacterReduction n χ).primitiveCharacter s.1 =
        LSeries (cglPrimitiveEulerCorrection n χ) s.1 *
          LSeries (fun k => (cglPrimitiveCharacterReduction n χ).primitiveCharacter k) s.1 := by
      rw [DirichletCharacter.LFunction_eq_LSeries _ s.2]
    _ = LSeries (LSeries.convolution (cglPrimitiveEulerCorrection n χ)
        (fun k => (cglPrimitiveCharacterReduction n χ).primitiveCharacter k)) s.1 := by
      exact (LSeries_convolution'
        (lseriesSummable_cglPrimitiveEulerCorrection n χ s.1)
        (DirichletCharacter.LSeriesSummable_of_one_lt_re
          (cglPrimitiveCharacterReduction n χ).primitiveCharacter s.2)).symm
    _ = LSeries (fun k => χ.1 k) s.1 := by
      congr 1
      funext k
      exact cglPrimitiveEulerCorrection_convolution_eq_input n χ k
    _ = DirichletCharacter.LFunction χ.1 s.1 := by
      rw [DirichletCharacter.LFunction_eq_LSeries _ s.2]

end RHTower

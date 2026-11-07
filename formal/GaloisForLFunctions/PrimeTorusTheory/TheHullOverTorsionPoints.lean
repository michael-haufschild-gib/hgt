import GaloisForLFunctions.PrimeTorusTheory.TheHullOverTheTorus
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The hull over torsion points

Being a torsion point of the torus decides nothing about the hull. The Liouville point `λ(p) = −1` has order two, and its fibre `ζ(2s)/ζ(s)` extends to `Re s > ½` if and only if RH holds (`riemannHypothesis_iff_liouvilleFibre_extends`). A Dirichlet character is also a torsion point, and its fibre is entire and zero-free on `Re s ≥ 1`, with no hypothesis (`fibre_extends_of_character`).

So the hull over torsion points is governed by arithmetic, not by the order. A character has an additive structure: it is periodic on the integers. This is what the Liouville point lacks. The zeros carried by a character fibre on `Re s > ½` are those of `L(s, χ)`: that the fibre extends is known, and where its zeros lie is the generalized Riemann hypothesis.
-/

namespace GaloisForLFunctions.PrimeTorusTheory

/-- **Characters.** The fibre over a nontrivial Dirichlet character extends to an entire function, zero-free on `Re s ≥ 1`. -/
theorem fibre_extends_of_character {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ s : ℂ, 1 < s.re → F s = LSeries (fun n => χ n) s) ∧
      ∀ s : ℂ, 1 ≤ s.re → F s ≠ 0 :=
  ⟨DirichletCharacter.LFunction χ, DirichletCharacter.differentiable_LFunction hχ,
    fun _ hs => DirichletCharacter.LFunction_eq_LSeries χ hs,
    fun _ hs => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs⟩

end GaloisForLFunctions.PrimeTorusTheory

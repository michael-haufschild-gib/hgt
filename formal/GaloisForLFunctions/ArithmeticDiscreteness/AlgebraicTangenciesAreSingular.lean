import Mathlib
import GaloisForLFunctions.«arithmetic-positivity-theory».BakerPrimeLogTranscendenceAndCollarSpectrumDisjointness

/-!
# Algebraic tangencies are singular

A finite-prime carrier `D(s) = G(p₁^{−s}, …, p_d^{−s})` has derivative
`D'(s) = −Σ_i log p_i · x_i ∂_i G(x)` at `x = (p_i^{−s})`, so a tangency of its Bohr lift at a point
`x` is a zero of the **tangency form** `Σ_i log p_i · x_i ∂_i G(x)` (`tangencyForm`). If `G` has
algebraic coefficients and `x` has algebraic coordinates — every torsion point, and every point
`u_i p_i^{−σ}` with `σ ∈ ℚ` and roots of unity `u_i` — the numbers `x_i ∂_i G(x)` are algebraic,
and Baker's theorem (`ArithmeticPositivityTheory.primeLog_linearForm_transcendental`) makes the form
transcendental unless all of them vanish.

* **Algebraic tangencies are singular** (`algebraic_tangency_is_singular`,
  `pderiv_eval_eq_zero_of_algebraic_tangency`). At an algebraic point with nonzero coordinates, a
  tangency of an algebraic carrier is a singular point of `G`: every `∂_i G(x)` vanishes.

So near-coincidences of algebraic carriers that come from algebraic points (e.g. the Euler product
at `(1, …, 1)`, the cusp carrier at `(1, 1)`) come from singularities of `G`; a smooth tangency at a
torsion point needs transcendental coefficients (`logTrinomial_collision_or_close_pair`).
-/

open MvPolynomial

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- The field of algebraic numbers in `ℂ`. -/
abbrev Qbar : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

theorem isAlgebraic_coe_qbar (a : Qbar) : IsAlgebraic ℚ (a : ℂ) := mem_algebraicClosure_iff.mp a.2

/-- The tangency form `Σ_i log p_i · x_i ∂_i G(x)` of an algebraic carrier at an algebraic point. -/
def tangencyForm {d : ℕ} (p : Fin d → ℕ) (G : MvPolynomial (Fin d) Qbar) (x : Fin d → Qbar) : ℂ :=
  ∑ i, ((x i * eval x (pderiv i G) : Qbar) : ℂ) * ((Real.log (p i) : ℝ) : ℂ)

/-- **Algebraic tangencies are singular.** If the tangency form of an algebraic carrier vanishes at an
algebraic point, every term `x_i ∂_i G(x)` vanishes. -/
theorem algebraic_tangency_is_singular {d : ℕ} (p : Fin d → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) (G : MvPolynomial (Fin d) Qbar) (x : Fin d → Qbar)
    (htan : tangencyForm p G x = 0) : ∀ i, x i * eval x (pderiv i G) = 0 := by
  by_contra h
  push Not at h
  obtain ⟨i, hi⟩ := h
  have htr := ArithmeticPositivityTheory.primeLog_linearForm_transcendental p hp hprime
    (fun i => ((x i * eval x (pderiv i G) : Qbar) : ℂ)) (fun i => isAlgebraic_coe_qbar _)
    ⟨i, fun h0 => hi (by exact_mod_cast h0)⟩
  unfold tangencyForm at htan
  rw [htan] at htr
  exact htr isAlgebraic_zero

/-- At an algebraic point with nonzero coordinates, a tangency of an algebraic carrier is a singular
point of `G`. -/
theorem pderiv_eval_eq_zero_of_algebraic_tangency {d : ℕ} (p : Fin d → ℕ)
    (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime) (G : MvPolynomial (Fin d) Qbar)
    (x : Fin d → Qbar) (hx : ∀ i, x i ≠ 0) (htan : tangencyForm p G x = 0) :
    ∀ i, eval x (pderiv i G) = 0 := fun i =>
  (mul_eq_zero.mp (algebraic_tangency_is_singular p hp hprime G x htan i)).resolve_left (hx i)

end GaloisForLFunctions.ArithmeticDiscreteness

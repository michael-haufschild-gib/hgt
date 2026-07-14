import Mathlib

/-!
# Iterated derivatives of a rational function share a power denominator

For polynomials `A, B` with `B ≠ 0` at `z`, the `k`-th derivative of the rational function
`r = A/B` is, off the zeros of `B`, a rational function with denominator `B^{k+1}`:
`r⁽ᵏ⁾(z) = Cₖ(z) / B(z)^{k+1}` for an explicit polynomial `Cₖ` (`C₀ = A`,
`Cₖ₊₁ = Cₖ'·B − (k+1)·Cₖ·B'`, the quotient-rule recursion).

This is the denominator-clearing input for the neutral/nonzero-charge hypertranscendence direction of the
signed-archimedean orbit-charge law: the digamma carrier's rational part
`∑_j m_j ∑_{i<n_j} 1/(w+i)` and all its jets have a common polynomial denominator, so a hypothetical
algebraic differential relation for the carrier can be denominator-cleared into a polynomial-coefficient
jet relation for the pure digamma carrier `ψ(w)` and killed by the off-pole digamma Hölder theorem.
-/

open Polynomial

namespace GaloisForLFunctions

/-- **Rational iterated-derivative denominator.**  For polynomials `A, B`, the `k`-th derivative of
`A/B` equals `Cₖ/B^{k+1}` off the zeros of `B`, with `Cₖ` polynomial (`C₀ = A`,
`Cₖ₊₁ = Cₖ'·B − (k+1)·Cₖ·B'`). -/
theorem exists_poly_iteratedDeriv_ratEval (A B : Polynomial ℂ) (k : ℕ) :
    ∃ C : Polynomial ℂ, ∀ z : ℂ, B.eval z ≠ 0 →
      iteratedDeriv k (fun w => A.eval w / B.eval w) z = C.eval z / B.eval z ^ (k + 1) := by
  induction k with
  | zero =>
    refine ⟨A, fun z _ => ?_⟩
    rw [iteratedDeriv_zero, pow_one]
  | succ k ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C.derivative * B - Polynomial.C ((k : ℂ) + 1) * C * B.derivative, fun z hz => ?_⟩
    have hcont : Continuous (fun w : ℂ => B.eval w) := Polynomial.continuous B
    have hopen : IsOpen {w : ℂ | B.eval w ≠ 0} := hcont.isOpen_preimage {x : ℂ | x ≠ 0} isOpen_ne
    have hmem : {w : ℂ | B.eval w ≠ 0} ∈ nhds z := hopen.mem_nhds hz
    have hEq : iteratedDeriv k (fun w => A.eval w / B.eval w)
        =ᶠ[nhds z] fun w => C.eval w / B.eval w ^ (k + 1) :=
      Filter.eventuallyEq_of_mem hmem (fun w hw => hC w hw)
    have hdiv := (C.hasDerivAt z).div ((B.hasDerivAt z).pow (k + 1)) (pow_ne_zero (k + 1) hz)
    rw [iteratedDeriv_succ, hEq.deriv_eq,
      show (fun w : ℂ => C.eval w / B.eval w ^ (k + 1))
        = (fun x : ℂ => C.eval x) / (fun x : ℂ => B.eval x) ^ (k + 1) from rfl,
      hdiv.deriv]
    simp only [Pi.pow_apply, Nat.add_sub_cancel, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C]
    have hBk : B.eval z ^ (k + 1) ≠ 0 := pow_ne_zero _ hz
    push_cast
    field_simp
    ring
end GaloisForLFunctions

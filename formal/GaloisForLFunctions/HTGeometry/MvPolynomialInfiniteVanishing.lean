import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Vanishing on a power of an infinite set

A polynomial in finitely many variables which vanishes at every tuple drawn from one infinite set of
scalars is the zero polynomial.  This is the multivariate form of "a polynomial with infinitely many
roots is zero", and it is what turns countably many scalar identities -- one per choice of
frequencies -- into an identity of polynomials.

The proof peels off one variable at a time: for a fixed tail the remaining one-variable polynomial
has infinitely many roots, so every coefficient vanishes on the smaller power.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **A polynomial vanishing on a power of an infinite set is zero.** -/
theorem mvPolynomial_eq_zero_of_eval_eq_zero_on_infinite_pow {S : Set ℂ} (hS : S.Infinite) :
    ∀ (m : ℕ) (p : MvPolynomial (Fin m) ℂ),
      (∀ x : Fin m → ℂ, (∀ j, x j ∈ S) → MvPolynomial.eval x p = 0) → p = 0 := by
  intro m
  induction m with
  | zero =>
      intro p h
      obtain ⟨x₀, hx₀⟩ := hS.nonempty
      have hval : MvPolynomial.eval (fun _ : Fin 0 => x₀) p = 0 :=
        h (fun _ => x₀) fun j => j.elim0
      refine MvPolynomial.funext fun x => ?_
      rw [Subsingleton.elim x (fun _ : Fin 0 => x₀), hval, map_zero]
  | succ m ih =>
      intro p h
      set q : Polynomial (MvPolynomial (Fin m) ℂ) := MvPolynomial.finSuccEquiv ℂ m p with hq
      have hcoeff : ∀ k : ℕ, q.coeff k = 0 := by
        intro k
        refine ih (q.coeff k) fun y hy => ?_
        have hroots : S ⊆ {x : ℂ | (Polynomial.map (MvPolynomial.eval y) q).IsRoot x} := by
          intro x₀ hx₀
          show Polynomial.eval x₀ (Polynomial.map (MvPolynomial.eval y) q) = 0
          rw [hq, ← MvPolynomial.eval_eq_eval_mv_eval' y x₀ p]
          refine h (Fin.cons x₀ y) fun j => ?_
          refine Fin.cases ?_ ?_ j
          · rw [Fin.cons_zero]
            exact hx₀
          · intro i
            rw [Fin.cons_succ]
            exact hy i
        have hpoly : Polynomial.map (MvPolynomial.eval y) q = 0 :=
          Polynomial.eq_zero_of_infinite_isRoot _ (hS.mono hroots)
        have hck := congrArg (fun r : Polynomial ℂ => r.coeff k) hpoly
        simpa [Polynomial.coeff_map] using hck
      have hq0 : q = 0 := Polynomial.ext fun k => by simpa using hcoeff k
      have hpq : p = (MvPolynomial.finSuccEquiv ℂ m).symm q := by
        rw [hq]
        exact ((MvPolynomial.finSuccEquiv ℂ m).symm_apply_apply p).symm
      rw [hpq, hq0, map_zero]

end

end GaloisForLFunctions.HTGeometry

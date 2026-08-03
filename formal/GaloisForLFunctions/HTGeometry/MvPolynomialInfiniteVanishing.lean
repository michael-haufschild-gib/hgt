import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import GaloisForLFunctions.HTGeometry.ExpandedMatrixDistinctNodes

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

/-- The product of the differences of distinct variables. -/
def vandermondeProduct (m : ℕ) : MvPolynomial (Fin m) ℂ :=
  ∏ q ∈ Finset.univ.offDiag, (MvPolynomial.X q.1 - MvPolynomial.X q.2)

theorem vandermondeProduct_ne_zero (m : ℕ) : vandermondeProduct m ≠ 0 := by
  classical
  refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
  exact X_sub_X_ne_zero (by simpa using (Finset.mem_offDiag.1 hq).2.2)

theorem eval_vandermondeProduct_eq_zero_of_not_injective {m : ℕ} {x : Fin m → ℂ}
    (hx : ¬ Function.Injective x) : MvPolynomial.eval x (vandermondeProduct m) = 0 := by
  classical
  rw [Function.Injective] at hx
  push Not at hx
  obtain ⟨l, l', hval, hne⟩ := hx
  rw [vandermondeProduct, map_prod]
  refine Finset.prod_eq_zero (i := (l, l')) ?_ ?_
  · exact Finset.mem_offDiag.2 ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩
  · simp only [map_sub, MvPolynomial.eval_X]
    rw [hval, sub_self]

/-- **A polynomial vanishing at every tuple of distinct values from an infinite set is zero.** -/
theorem mvPolynomial_eq_zero_of_eval_eq_zero_on_infinite_pow_injective {S : Set ℂ}
    (hS : S.Infinite) {m : ℕ} (p : MvPolynomial (Fin m) ℂ)
    (h : ∀ x : Fin m → ℂ, (∀ j, x j ∈ S) → Function.Injective x →
      MvPolynomial.eval x p = 0) : p = 0 := by
  classical
  have hmul : p * vandermondeProduct m = 0 := by
    refine mvPolynomial_eq_zero_of_eval_eq_zero_on_infinite_pow hS m _ fun x hx => ?_
    rw [map_mul]
    by_cases hinj : Function.Injective x
    · rw [h x hx hinj, zero_mul]
    · rw [eval_vandermondeProduct_eq_zero_of_not_injective hinj, mul_zero]
  rcases mul_eq_zero.mp hmul with hp | hv
  · exact hp
  · exact absurd hv (vandermondeProduct_ne_zero m)

end

end GaloisForLFunctions.HTGeometry

import Mathlib

/-!
# Jets of a function pulled back along `z ↦ z^q`

Composing with the `q`-th power map replaces the derivation `d/dw` by `q z^{q-1} d/dz`, so every
iterated derivative of `w ↦ f(w)` pulled back to `z ↦ f(z^q)` is a *polynomial-coefficient* triangular
combination of the pulled-back jets of `f`:

`(f(·^q))^{(k)}(z) = ∑_{j ≤ k} p_{k,j}(z) · f^{(j)}(z^q)`,

with `p_{0,0} = 1`, `p_{k+1,0} = p_{k,0}'` and `p_{k+1,j+1} = p_{k,j+1}' + q X^{q-1} · p_{k,j}`.

The transition matrix is lower triangular with diagonal `p_{k,k} = (q X^{q-1})^k`, hence invertible at
every `z ≠ 0` once `q ≥ 1`.  That invertibility is what makes the substitution on jet variables
injective, and is the algebraic engine behind the descent of differential algebraicity along
`z ↦ z^q`.
-/

namespace HTGeometry

open Polynomial

/-- Chain-rule coefficients for the substitution `z ↦ z^q`: the polynomial `p_{k,j}` occurring in
`(f(·^q))^{(k)}(z) = ∑_{j ≤ k} p_{k,j}(z) · f^{(j)}(z^q)`. -/
noncomputable def powChainCoeff (q : ℕ) : ℕ → ℕ → Polynomial ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, 0 => (powChainCoeff q k 0).derivative
  | k + 1, j + 1 =>
      (powChainCoeff q k (j + 1)).derivative
        + (Polynomial.C (q : ℂ) * Polynomial.X ^ (q - 1)) * powChainCoeff q k j

@[simp] theorem powChainCoeff_zero_zero (q : ℕ) : powChainCoeff q 0 0 = 1 := rfl

@[simp] theorem powChainCoeff_zero_succ (q j : ℕ) : powChainCoeff q 0 (j + 1) = 0 := rfl

theorem powChainCoeff_succ_zero (q k : ℕ) :
    powChainCoeff q (k + 1) 0 = (powChainCoeff q k 0).derivative := rfl

theorem powChainCoeff_succ_succ (q k j : ℕ) :
    powChainCoeff q (k + 1) (j + 1) =
      (powChainCoeff q k (j + 1)).derivative
        + (Polynomial.C (q : ℂ) * Polynomial.X ^ (q - 1)) * powChainCoeff q k j := rfl

/-- The transition matrix is lower triangular: no jet above the current order occurs. -/
theorem powChainCoeff_eq_zero_of_lt (q : ℕ) {k j : ℕ} (h : k < j) : powChainCoeff q k j = 0 := by
  induction k generalizing j with
  | zero =>
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp
  | succ k ih =>
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [powChainCoeff_succ_succ, ih (by omega), ih (by omega)]
    simp

/-- The diagonal of the transition matrix is `(q X^{q-1})^k`. -/
theorem powChainCoeff_self (q k : ℕ) :
    powChainCoeff q k k = (Polynomial.C (q : ℂ) * Polynomial.X ^ (q - 1)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [powChainCoeff_succ_succ, powChainCoeff_eq_zero_of_lt q (Nat.lt_succ_self k), ih]
    simp [pow_succ, mul_comm]

/-- **Chain rule for the `q`-th power substitution.**  For a function all of whose iterated
derivatives are differentiable, the jets of the pullback `z ↦ f(z^q)` are the triangular
polynomial-coefficient combination of the pulled-back jets of `f`. -/
theorem iteratedDeriv_comp_pow {f : ℂ → ℂ}
    (hf : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m f)) (q k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun w => f (w ^ q)) z
      = ∑ j ∈ Finset.range (k + 1), (powChainCoeff q k j).eval z * iteratedDeriv j f (z ^ q) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    have hstep : ∀ x : ℂ,
        iteratedDeriv k (fun w => f (w ^ q)) x
          = ∑ j ∈ Finset.range (k + 1),
              (powChainCoeff q k j).eval x * iteratedDeriv j f (x ^ q) := fun x => ih x
    have hjet : ∀ (j : ℕ) (x : ℂ),
        HasDerivAt (fun y : ℂ => iteratedDeriv j f (y ^ q))
          ((q : ℂ) * x ^ (q - 1) * iteratedDeriv (j + 1) f (x ^ q)) x := by
      intro j x
      have houter : HasDerivAt (iteratedDeriv j f)
          (iteratedDeriv (j + 1) f (x ^ q)) (x ^ q) := by
        have := (hf j (x ^ q)).hasDerivAt
        rwa [← iteratedDeriv_succ] at this
      have hinner : HasDerivAt (fun y : ℂ => y ^ q) ((q : ℂ) * x ^ (q - 1)) x :=
        hasDerivAt_pow q x
      have hcomp := houter.comp x hinner
      have hval : (q : ℂ) * x ^ (q - 1) * iteratedDeriv (j + 1) f (x ^ q)
          = iteratedDeriv (j + 1) f (x ^ q) * ((q : ℂ) * x ^ (q - 1)) := by ring
      rw [hval]
      exact hcomp
    have hsum : HasDerivAt
        (fun x : ℂ => ∑ j ∈ Finset.range (k + 1),
          (powChainCoeff q k j).eval x * iteratedDeriv j f (x ^ q))
        (∑ j ∈ Finset.range (k + 1),
          ((powChainCoeff q k j).derivative.eval z * iteratedDeriv j f (z ^ q)
            + (powChainCoeff q k j).eval z *
                ((q : ℂ) * z ^ (q - 1) * iteratedDeriv (j + 1) f (z ^ q)))) z :=
      HasDerivAt.fun_sum fun j _ => ((powChainCoeff q k j).hasDerivAt z).mul (hjet j z)
    have hderiv : iteratedDeriv (k + 1) (fun w => f (w ^ q)) z
        = ∑ j ∈ Finset.range (k + 1),
            ((powChainCoeff q k j).derivative.eval z * iteratedDeriv j f (z ^ q)
              + (powChainCoeff q k j).eval z *
                  ((q : ℂ) * z ^ (q - 1) * iteratedDeriv (j + 1) f (z ^ q))) := by
      rw [iteratedDeriv_succ, funext hstep]
      exact hsum.deriv
    have hA : ∑ j ∈ Finset.range (k + 1),
          (powChainCoeff q k j).derivative.eval z * iteratedDeriv j f (z ^ q)
        = (∑ i ∈ Finset.range (k + 1),
              (powChainCoeff q k (i + 1)).derivative.eval z * iteratedDeriv (i + 1) f (z ^ q))
            + (powChainCoeff q k 0).derivative.eval z * iteratedDeriv 0 f (z ^ q) := by
      have hshift := Finset.sum_range_succ'
        (fun j => (powChainCoeff q k j).derivative.eval z * iteratedDeriv j f (z ^ q)) (k + 1)
      have hdrop : ∑ j ∈ Finset.range (k + 1 + 1),
            (powChainCoeff q k j).derivative.eval z * iteratedDeriv j f (z ^ q)
          = ∑ j ∈ Finset.range (k + 1),
            (powChainCoeff q k j).derivative.eval z * iteratedDeriv j f (z ^ q) := by
        rw [Finset.sum_range_succ, powChainCoeff_eq_zero_of_lt q (Nat.lt_succ_self k)]
        simp
      rw [← hdrop, hshift]
    have hT : ∑ j ∈ Finset.range (k + 1 + 1),
          (powChainCoeff q (k + 1) j).eval z * iteratedDeriv j f (z ^ q)
        = (∑ i ∈ Finset.range (k + 1),
              (powChainCoeff q (k + 1) (i + 1)).eval z * iteratedDeriv (i + 1) f (z ^ q))
            + (powChainCoeff q (k + 1) 0).eval z * iteratedDeriv 0 f (z ^ q) :=
      Finset.sum_range_succ'
        (fun j => (powChainCoeff q (k + 1) j).eval z * iteratedDeriv j f (z ^ q)) (k + 1)
    have hR : ∑ i ∈ Finset.range (k + 1),
          (powChainCoeff q (k + 1) (i + 1)).eval z * iteratedDeriv (i + 1) f (z ^ q)
        = (∑ i ∈ Finset.range (k + 1),
              (powChainCoeff q k (i + 1)).derivative.eval z * iteratedDeriv (i + 1) f (z ^ q))
            + ∑ i ∈ Finset.range (k + 1),
                (powChainCoeff q k i).eval z *
                  ((q : ℂ) * z ^ (q - 1) * iteratedDeriv (i + 1) f (z ^ q)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [powChainCoeff_succ_succ]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      ring
    rw [hderiv, Finset.sum_add_distrib, hA, hT, hR, powChainCoeff_succ_zero]
    ring

end HTGeometry

import Mathlib

/-!
# The Euler operator is diagonal on Taylor coefficients

The directional derivation of the periodic pencil acts on a carrier `Ψ(exp (L z))` through the
Euler operator `Θ Ψ (u) = u · Ψ'(u)` on the inner variable, up to the constant `L w`.  On Taylor
coefficients `Θ` is diagonal: it multiplies the coefficient of `uᵐ` by `m`.  In terms of iterated
derivatives at the origin,

```text
(Θ Ψ)⁽ᵐ⁾(0) = m · Ψ⁽ᵐ⁾(0),      (Θ^r Ψ)⁽ᵐ⁾(0) = m^r · Ψ⁽ᵐ⁾(0).
```

The proof is the Leibniz identity `(u·g)⁽ⁿ⁺¹⁾ = u·g⁽ⁿ⁺¹⁾ + (n+1)·g⁽ⁿ⁾`, evaluated at the origin.

* `eulerOp` — the operator;
* `iteratedDeriv_eulerOp_zero`, `iteratedDeriv_eulerOp_iterate_zero` — the diagonal action.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Smoothness bookkeeping -/

theorem contDiff_iteratedDeriv {f : ℂ → ℂ} (h : ContDiff ℂ (⊤ : ℕ∞) f) (n : ℕ) :
    ContDiff ℂ (⊤ : ℕ∞) (iteratedDeriv n f) := by
  induction n with
  | zero => simpa [iteratedDeriv_zero] using h
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv'

theorem differentiable_iteratedDeriv_eulerOperatorDiagonal {f : ℂ → ℂ} (h : ContDiff ℂ (⊤ : ℕ∞) f) (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n f) :=
  (contDiff_iteratedDeriv h n).differentiable (by simp)

/-! ### The Leibniz identity for multiplication by the coordinate -/

/-- `(u·g)⁽ⁿ⁺¹⁾ = u·g⁽ⁿ⁺¹⁾ + (n+1)·g⁽ⁿ⁾`. -/
private theorem iteratedDeriv_id_mul {g : ℂ → ℂ} (hg : ContDiff ℂ (⊤ : ℕ∞) g) (n : ℕ) :
    iteratedDeriv (n + 1) (fun u => u * g u)
      = fun u => u * iteratedDeriv (n + 1) g u + ((n : ℂ) + 1) * iteratedDeriv n g u := by
  induction n with
  | zero =>
    funext u
    have hgd : Differentiable ℂ g := hg.differentiable (by simp)
    have hprod : HasDerivAt (fun y : ℂ => y * g y) (1 * g u + u * deriv g u) u :=
      (hasDerivAt_id u).mul (hgd u).hasDerivAt
    rw [iteratedDeriv_one, iteratedDeriv_one, iteratedDeriv_zero, hprod.deriv]
    push_cast
    ring
  | succ n ih =>
    funext u
    have hd1 : Differentiable ℂ (iteratedDeriv (n + 1) g) := differentiable_iteratedDeriv_eulerOperatorDiagonal hg _
    have hd0 : Differentiable ℂ (iteratedDeriv n g) := differentiable_iteratedDeriv_eulerOperatorDiagonal hg _
    have hA : HasDerivAt (fun y : ℂ => y * iteratedDeriv (n + 1) g y)
        (1 * iteratedDeriv (n + 1) g u + u * iteratedDeriv (n + 1 + 1) g u) u := by
      have hstep := (hasDerivAt_id u).mul (hd1 u).hasDerivAt
      rwa [← iteratedDeriv_succ] at hstep
    have hB : HasDerivAt (fun y : ℂ => ((n : ℂ) + 1) * iteratedDeriv n g y)
        (((n : ℂ) + 1) * iteratedDeriv (n + 1) g u) u := by
      have hstep := ((hd0 u).hasDerivAt).const_mul ((n : ℂ) + 1)
      rwa [← iteratedDeriv_succ] at hstep
    have hAB : HasDerivAt (fun y : ℂ => y * iteratedDeriv (n + 1) g y
          + ((n : ℂ) + 1) * iteratedDeriv n g y)
        ((1 * iteratedDeriv (n + 1) g u + u * iteratedDeriv (n + 1 + 1) g u)
          + ((n : ℂ) + 1) * iteratedDeriv (n + 1) g u) u := hA.add hB
    rw [iteratedDeriv_succ, ih, hAB.deriv]
    push_cast
    ring

/-! ### The Euler operator -/

/-- The Euler operator `Ψ ↦ (u ↦ u · Ψ'(u))`. -/
def eulerOp (Ψ : ℂ → ℂ) : ℂ → ℂ := fun u => u * deriv Ψ u

theorem contDiff_eulerOp {Ψ : ℂ → ℂ} (h : ContDiff ℂ (⊤ : ℕ∞) Ψ) :
    ContDiff ℂ (⊤ : ℕ∞) (eulerOp Ψ) :=
  contDiff_id.mul h.deriv'

/-- **The Euler operator is diagonal at the origin.** -/
theorem iteratedDeriv_eulerOp_zero {Ψ : ℂ → ℂ} (h : ContDiff ℂ (⊤ : ℕ∞) Ψ) (m : ℕ) :
    iteratedDeriv m (eulerOp Ψ) 0 = (m : ℂ) * iteratedDeriv m Ψ 0 := by
  cases m with
  | zero =>
    rw [iteratedDeriv_zero]
    show (0 : ℂ) * deriv Ψ 0 = _
    simp
  | succ n =>
    have hfun : eulerOp Ψ = fun u => u * deriv Ψ u := rfl
    rw [hfun, iteratedDeriv_id_mul h.deriv' n]
    show (0 : ℂ) * iteratedDeriv (n + 1) (deriv Ψ) 0
      + ((n : ℂ) + 1) * iteratedDeriv n (deriv Ψ) 0 = _
    rw [zero_mul, zero_add, ← iteratedDeriv_succ']
    push_cast
    ring

/-- **Iterating the Euler operator multiplies the `m`-th coefficient by `m^r`.** -/
theorem iteratedDeriv_eulerOp_iterate_zero {Ψ : ℂ → ℂ} (h : ContDiff ℂ (⊤ : ℕ∞) Ψ) (r m : ℕ) :
    iteratedDeriv m (eulerOp^[r] Ψ) 0 = (m : ℂ) ^ r * iteratedDeriv m Ψ 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hiter : ContDiff ℂ (⊤ : ℕ∞) (eulerOp^[r] Ψ) := by
      clear ih
      induction r with
      | zero => simpa using h
      | succ r ihr =>
        rw [Function.iterate_succ_apply']
        exact contDiff_eulerOp ihr
    rw [Function.iterate_succ_apply', iteratedDeriv_eulerOp_zero hiter, ih]
    ring

end

end GaloisForLFunctions.HTGeometry

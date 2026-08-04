import GaloisForLFunctions.HTGeometry.PoincareRecession

/-!
# Sharpness: transcendence cannot be dropped

A cascade of polynomials is a polynomial, and a polynomial satisfies an algebraic differential
equation of order zero.  So a length-`n` cascade of polynomial constituents has order `0`, not `n`,
however long the cascade is.

The unit-cost law therefore genuinely needs the constituents to be transcendental; no weakening to
"nonlinear" or "nonconstant" is possible.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- Evaluating a one-variable polynomial pushed into the first slot. -/
theorem eval_eval₂_X_zero (p : Polynomial ℂ) (z w : ℂ) :
    MvPolynomial.eval ![z, w] (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) p)
      = p.eval z := by
  induction p using Polynomial.induction_on' with
  | add q r ihq ihr =>
      rw [Polynomial.eval₂_add, map_add, ihq, ihr, Polynomial.eval_add]
  | monomial k c =>
      rw [Polynomial.eval₂_monomial, map_mul, map_pow, MvPolynomial.eval_C,
        MvPolynomial.eval_X, Polynomial.eval_monomial]
      rfl

/-- **A polynomial satisfies an order-zero equation.** -/
theorem differentiallyAlgebraicOfOrder_zero_of_polynomial {g : ℂ → ℂ} (p : Polynomial ℂ)
    (hg : ∀ z : ℂ, g z = p.eval z) : DifferentiallyAlgebraicOfOrder g 0 := by
  classical
  set P : MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.X 1 - Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) p with hP
  have heval : ∀ z w : ℂ, MvPolynomial.eval ![z, w] P = w - p.eval z := by
    intro z w
    rw [hP, map_sub, MvPolynomial.eval_X, eval_eval₂_X_zero]
    rfl
  refine ⟨P, ?_, ?_⟩
  · intro hzero
    have h0 := heval 0 0
    have h1 := heval 0 1
    rw [hzero] at h0 h1
    simp only [map_zero] at h0 h1
    have hone : (1 : ℂ) = 0 := by
      have hc : (0 : ℂ) - p.eval 0 = 0 := h0.symm
      have hd : (1 : ℂ) - p.eval 0 = 0 := h1.symm
      linear_combination hd - hc
    exact one_ne_zero hone
  · intro z
    have hvec : (Fin.cons z fun j : Fin 1 => iteratedDeriv (j : ℕ) g z) = ![z, g z] := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp
      · rw [Fin.cons_succ]
        fin_cases i
        simp [iteratedDeriv_zero]
    rw [hvec, heval z (g z), hg z, sub_self]

/-- A cascade of polynomials is a polynomial. -/
theorem exists_polynomial_entireCascade {f : ℕ → ℂ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : ∀ k : ℕ, ∀ z : ℂ, f k z = (p k).eval z) (n : ℕ) :
    ∃ q : Polynomial ℂ, ∀ z : ℂ, entireCascade f n z = q.eval z := by
  induction n with
  | zero =>
      refine ⟨Polynomial.X, fun z => ?_⟩
      rw [Polynomial.eval_X]
      rfl
  | succ n ih =>
      obtain ⟨q, hq⟩ := ih
      refine ⟨(p n).comp q, fun z => ?_⟩
      rw [Polynomial.eval_comp, ← hq z]
      show f n (entireCascade f n z) = (p n).eval (entireCascade f n z)
      exact hp n _

/-- **A polynomial cascade has order zero, at every length.** -/
theorem differentiallyAlgebraicOfOrder_zero_entireCascade_of_polynomial {f : ℕ → ℂ → ℂ}
    {p : ℕ → Polynomial ℂ} (hp : ∀ k : ℕ, ∀ z : ℂ, f k z = (p k).eval z) (n : ℕ) :
    DifferentiallyAlgebraicOfOrder (entireCascade f n) 0 := by
  obtain ⟨q, hq⟩ := exists_polynomial_entireCascade hp n
  exact differentiallyAlgebraicOfOrder_zero_of_polynomial q hq

/-- **The unit-cost law fails for polynomial constituents.**  So transcendence of the constituents
cannot be weakened. -/
theorem not_exactDifferentialOrder_entireCascade_of_polynomial {f : ℕ → ℂ → ℂ}
    {p : ℕ → Polynomial ℂ} (hp : ∀ k : ℕ, ∀ z : ℂ, f k z = (p k).eval z) {n : ℕ} (hn : 1 ≤ n) :
    ¬ ExactDifferentialOrder (entireCascade f n) n := by
  intro h
  exact h.2 0 hn (differentiallyAlgebraicOfOrder_zero_entireCascade_of_polynomial hp n)

/-! ## The order-zero class, characterized -/

/-- **An entire function is algebraic over the coordinate exactly when it is a polynomial.** -/
theorem differentiallyAlgebraicOfOrder_zero_iff_polynomial {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) :
    DifferentiallyAlgebraicOfOrder g 0 ↔ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z := by
  constructor
  · intro h
    by_contra hnp
    exact not_differentiallyAlgebraicOfOrder_zero_of_transcendental hg hnp h
  · rintro ⟨p, hp⟩
    exact differentiallyAlgebraicOfOrder_zero_of_polynomial p hp

/-- **Exact order zero is exactly the polynomial class.** -/
theorem exactDifferentialOrder_zero_iff_polynomial {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    ExactDifferentialOrder g 0 ↔ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z := by
  constructor
  · intro h
    exact (differentiallyAlgebraicOfOrder_zero_iff_polynomial hg).mp h.1
  · intro h
    exact ⟨(differentiallyAlgebraicOfOrder_zero_iff_polynomial hg).mpr h,
      fun m hm => absurd hm (Nat.not_lt_zero m)⟩

/-! ## The charge count

The card's quantization formula: the order is the number of nonzero Wiman charges, not their sizes.
Once every constituent contributes a nonzero charge the count is the length of the cascade. -/

/-- The number of nonzero charges among the first `n`. -/
theorem chargeCount_eq {n : ℕ} {ω : ℕ → ℝ} (hω : ∀ k, k < n → ω k ≠ 0) :
    (∑ k ∈ Finset.range n, if ω k ≠ 0 then (1 : ℕ) else 0) = n := by
  classical
  rw [Finset.sum_congr rfl (fun k hk => if_pos (hω k (Finset.mem_range.mp hk)))]
  simp

/-- **The order is the charge count.**  Every constituent with a nonzero charge costs exactly one
differential order, whatever the size of the charge. -/
theorem exactDifferentialOrder_eq_chargeCount {f : ℕ → ℂ → ℂ} {n : ℕ} {ω : ℕ → ℝ}
    (hω : ∀ k, k < n → ω k ≠ 0)
    (h : ExactDifferentialOrder (entireCascade f n) n) :
    ExactDifferentialOrder (entireCascade f n)
      (∑ k ∈ Finset.range n, if ω k ≠ 0 then (1 : ℕ) else 0) := by
  rwa [chargeCount_eq hω]

end GaloisForLFunctions.HTGeometry

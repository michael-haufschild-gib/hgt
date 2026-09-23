import GaloisForLFunctions.HTGeometry.SecondKindMomentPolynomials

/-!
# The second kind is the moment functional of a divided difference

For each `z` the divided difference `x ↦ (Qₙ(x) − Qₙ(z))/(x − z)` is a polynomial, and applying the
moment functional in `x` returns `s₀·Rₙ(z)`.

Both sides obey the same three-term recurrence: splitting
`(z − aₙ)Q_{n+1}(z) − (x − aₙ)Q_{n+1}(x) = (z − aₙ)(Q_{n+1}(z) − Q_{n+1}(x)) + Q_{n+1}(x)(z − x)`
contributes the extra term `L(Q_{n+1})`, which vanishes because `Q_{n+1}` is orthogonal to the
constants.  The initial data agree, so the two sequences coincide.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The divided difference of a first-kind polynomial, as a polynomial in the running variable. -/
noncomputable def firstKindDividedDiff (s : ℕ → ℝ) (n : ℕ) (z : ℝ) : Polynomial ℝ :=
  (monicOrtho s n - C ((monicOrtho s n).eval z)) /ₘ (X - C z)

/-- The defining identity: multiplying back by `X − z` returns the difference. -/
theorem mul_firstKindDividedDiff (s : ℕ → ℝ) (n : ℕ) (z : ℝ) :
    (X - C z) * firstKindDividedDiff s n z
      = monicOrtho s n - C ((monicOrtho s n).eval z) := by
  have hmonic : (X - C z).Monic := monic_X_sub_C z
  have hmod : (monicOrtho s n - C ((monicOrtho s n).eval z)) %ₘ (X - C z) = 0 := by
    rw [Polynomial.modByMonic_X_sub_C_eq_C_eval]
    simp
  have hadd := Polynomial.modByMonic_add_div
    (monicOrtho s n - C ((monicOrtho s n).eval z)) (X - C z)
  rw [hmod, zero_add] at hadd
  exact hadd

@[simp] theorem firstKindDividedDiff_zero (s : ℕ → ℝ) (z : ℝ) :
    firstKindDividedDiff s 0 z = 0 := by
  have hmul := mul_firstKindDividedDiff s 0 z
  rw [monicOrtho_zero] at hmul
  simp only [Polynomial.eval_one, map_one, sub_self] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left (X_sub_C_ne_zero z)

/-- The recurrence for the divided differences, with the extra constant term. -/
theorem firstKindDividedDiff_succ_succ (h : PositiveMomentForm s) (n : ℕ) (z : ℝ) :
    firstKindDividedDiff s (n + 2) z
      = (C z - C (recurDiag s n)) * firstKindDividedDiff s (n + 1) z
        - C (recurOff s n) * firstKindDividedDiff s n z
        + monicOrtho s (n + 1) := by
  have hmonic : (X - C z).Monic := monic_X_sub_C z
  refine mul_left_cancel₀ (X_sub_C_ne_zero z) ?_
  rw [mul_firstKindDividedDiff]
  have h1 := mul_firstKindDividedDiff s (n + 1) z
  have h2 := mul_firstKindDividedDiff s n z
  have hrec := monicOrtho_succ_succ h n
  have hrecz : (monicOrtho s (n + 2)).eval z
      = (z - recurDiag s n) * (monicOrtho s (n + 1)).eval z
        - recurOff s n * (monicOrtho s n).eval z := monicOrtho_succ_succ_eval h n z
  rw [hrecz, hrec]
  push_cast [Polynomial.C_sub, Polynomial.C_mul]
  linear_combination (C (recurDiag s n) - C z) * h1 + C (recurOff s n) * h2


@[simp] theorem firstKindDividedDiff_one (s : ℕ → ℝ) (z : ℝ) :
    firstKindDividedDiff s 1 z = 1 := by
  have hmul := mul_firstKindDividedDiff s 1 z
  have hQ1 : monicOrtho s 1 - C ((monicOrtho s 1).eval z) = X - C z := by
    rw [monicOrtho_eq s 1]
    simp only [Fin.sum_univ_one, Fin.val_zero, monicOrtho_zero, pow_one,
      Polynomial.smul_eq_C_mul, mul_one, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.C_sub]
    ring
  rw [hQ1] at hmul
  have hcancel : (X - C z) * firstKindDividedDiff s 1 z = (X - C z) * 1 := by
    rw [hmul, mul_one]
  exact mul_left_cancel₀ (X_sub_C_ne_zero z) hcancel

/-- **The second kind is the moment functional of the divided difference.**  Both sides satisfy the
same three-term recurrence with the same initial data; the extra term in the recurrence is
`L(Q_{n+1})`, which vanishes by orthogonality to the constants. -/
theorem momentFunctional_firstKindDividedDiff (h : PositiveMomentForm s) (n : ℕ) (z : ℝ) :
    momentFunctional s (firstKindDividedDiff s n z) = s 0 * (secondKind s n).eval z := by
  have hstep : ∀ m : ℕ,
      momentFunctional s (firstKindDividedDiff s m z) = s 0 * (secondKind s m).eval z ∧
      momentFunctional s (firstKindDividedDiff s (m + 1) z)
        = s 0 * (secondKind s (m + 1)).eval z := by
    intro m
    induction m with
    | zero =>
        constructor
        · simp
        · rw [firstKindDividedDiff_one]
          have h1 : (1 : Polynomial ℝ) = Polynomial.X ^ (0 : ℕ) := by simp
          rw [h1, momentFunctional_X_pow]
          simp
    | succ m ih =>
        refine ⟨ih.2, ?_⟩
        have hzero : momentFunctional s (monicOrtho s (m + 1)) = 0 := by
          have hdeg : (1 : Polynomial ℝ).degree < ((1 : ℕ) : WithBot ℕ) := by
            rw [Polynomial.degree_one]
            exact_mod_cast Nat.zero_lt_one
          have := monicOrtho_inner_eq_zero_of_degree_lt h (m + 1) 1 (by omega) 1 hdeg
          rwa [momentInner_def, mul_one] at this
        have hML : ∀ p : Polynomial ℝ, momentFunctional s p = momentInner s p 1 := fun p => by
          rw [momentInner_def, mul_one]
        have hCmul : ∀ (c : ℝ) (p : Polynomial ℝ),
            momentFunctional s (C c * p) = c * momentFunctional s p := by
          intro c p
          rw [hML, hML, ← Polynomial.smul_eq_C_mul, momentInner_smul_left]
        have hAdd : ∀ p q : Polynomial ℝ,
            momentFunctional s (p + q) = momentFunctional s p + momentFunctional s q := by
          intro p q
          rw [hML, hML, hML, momentInner_add_left]
        have hSub : ∀ p q : Polynomial ℝ,
            momentFunctional s (p - q) = momentFunctional s p - momentFunctional s q := by
          intro p q
          rw [hML, hML, hML, momentInner_sub_left]
        rw [firstKindDividedDiff_succ_succ h m z, ← Polynomial.C_sub, hAdd, hSub, hCmul, hCmul,
          hzero, ih.1, ih.2, secondKind_succ_succ_eval s m z]
        ring
  exact (hstep n).1

end HTGeometry

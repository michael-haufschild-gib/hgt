import GaloisForLFunctions.HTGeometry.PolynomialVariableShift
import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicInvariance

/-!
# Adding a constant preserves hypertranscendence

Adding a constant to a function changes its value and none of its derivatives.  So a differential
polynomial annihilating the shifted function becomes one annihilating the original after shifting
the value variable, and that shift is an algebra automorphism.

This is the invariance the regularized Herglotz transform needs: it differs from the plain Cauchy
transform by a constant, so the two have the same hypertranscendence status.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Adding a constant does not change any derivative. -/
theorem deriv_add_const_fun (f : ℂ → ℂ) (c : ℂ) :
    deriv (fun w => f w + c) = deriv f := by
  funext z
  exact deriv_add_const c

/-- Adding a constant does not change any iterated derivative of positive order. -/
theorem iteratedDeriv_add_const_succ (f : ℂ → ℂ) (c : ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv (n + 1) (fun w => f w + c) z = iteratedDeriv (n + 1) f z := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ', deriv_add_const_fun]

/-- **Adding a constant preserves differential algebraicity.** -/
theorem differentiallyAlgebraic_add_const {f : ℂ → ℂ} (c : ℂ)
    (h : DifferentiallyAlgebraic fun w => f w + c) : DifferentiallyAlgebraic f := by
  classical
  obtain ⟨n, P, hP, hzero⟩ := h
  refine ⟨n, shiftSubst 1 c P, shiftSubst_ne_zero 1 c hP, ?_⟩
  intro z
  rw [eval_shiftSubst]
  have hupd : Function.update
      (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) :
        Fin (n + 2) → ℂ) 1
      ((Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) :
        Fin (n + 2) → ℂ) 1 + c)
      = Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (fun w => f w + c) z) := by
    funext i
    by_cases hi1 : i = 1
    · subst hi1
      simp [Function.update_self, iteratedDeriv_zero]
    · rw [Function.update_of_ne hi1]
      rcases Fin.eq_zero_or_eq_succ i with hi | ⟨i', hi⟩
      · subst hi
        simp
      · subst hi
        have hi'0 : i' ≠ 0 := fun h => hi1 (by subst h; rfl)
        obtain ⟨k, hk⟩ := Fin.eq_succ_of_ne_zero hi'0
        subst hk
        simp only [Fin.cons_succ, Fin.val_succ]
        exact (iteratedDeriv_add_const_succ f c _ z).symm
  rw [hupd]
  exact hzero z

/-- **Adding a constant preserves differential algebraicity, both ways.** -/
theorem differentiallyAlgebraic_add_const_iff {f : ℂ → ℂ} (c : ℂ) :
    DifferentiallyAlgebraic (fun w => f w + c) ↔ DifferentiallyAlgebraic f := by
  constructor
  · exact differentiallyAlgebraic_add_const c
  · intro h
    refine differentiallyAlgebraic_add_const (f := fun w => f w + c) (-c) ?_
    simpa using h

/-- **Adding a constant preserves hypertranscendence.**  The invariance the regularized Herglotz
transform needs: it differs from the plain Cauchy transform by a constant. -/
theorem hypertranscendental_add_const_iff {f : ℂ → ℂ} (c : ℂ) :
    Hypertranscendental (fun w => f w + c) ↔ Hypertranscendental f :=
  not_congr (differentiallyAlgebraic_add_const_iff c)

end

end GaloisForLFunctions.HTGeometry

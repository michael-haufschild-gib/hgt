import Mathlib

/-!
# Smoothness from a complete derivative chain

A family `f m` whose `m`-th member differentiates everywhere to `f (m + 1)` is automatically smooth
at every level, and its iterated derivatives are the shifted members of the chain.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_nat_of_hasDerivAt_chain {f : ℕ → ℝ → F}
    (hf : ∀ m x, HasDerivAt (f m) (f (m + 1) x) x) :
    ∀ n m : ℕ, ContDiff ℝ n (f m) := by
  intro n
  induction n with
  | zero =>
      intro m
      exact contDiff_zero.mpr
        (continuous_iff_continuousAt.mpr fun x ↦ (hf m x).continuousAt)
  | succ n ih =>
      intro m
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) =
          (n : WithTop ℕ∞) + 1 := by push_cast; ring
      rw [hcast, contDiff_succ_iff_deriv]
      refine ⟨fun x ↦ (hf m x).differentiableAt, ?_, ?_⟩
      · intro h
        exact absurd h (by simp)
      · have hderiv : deriv (f m) = f (m + 1) :=
          funext fun x ↦ (hf m x).deriv
        rw [hderiv]
        exact ih (m + 1)

theorem contDiff_top_of_hasDerivAt_chain {f : ℕ → ℝ → F}
    (hf : ∀ m x, HasDerivAt (f m) (f (m + 1) x) x) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (f m) := by
  rw [contDiff_infty]
  exact fun n ↦ contDiff_nat_of_hasDerivAt_chain hf n m

theorem iteratedDeriv_eq_of_hasDerivAt_chain {f : ℕ → ℝ → F}
    (hf : ∀ m x, HasDerivAt (f m) (f (m + 1) x) x) (m n : ℕ) :
    iteratedDeriv n (f m) = f (m + n) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, Nat.add_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      simpa only [Nat.add_assoc] using (hf (m + n) x).deriv

end GaloisForLFunctions.HTGeometry

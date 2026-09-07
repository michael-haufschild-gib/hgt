import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Iteration of a two-index derivative recurrence through integration -/

open MeasureTheory
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Repeated increment of the first derivative index minus the second. -/
def alternatingPairJet : ℕ → (ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ
  | 0, F, m, n => F m n
  | k+1, F, m, n => alternatingPairJet k F (m+1) n - alternatingPairJet k F m (n+1)

/-- The derivative recurrence propagates to every finite iterated jet. -/
theorem hasDerivAt_alternatingPairJet
    (F : ℕ → ℕ → ℝ → ℝ)
    (hF : ∀ m n t, HasDerivAt (F m n) (F (m+1) n t-F m (n+1) t) t)
    (k m n : ℕ) (t : ℝ) :
    HasDerivAt (fun t => alternatingPairJet k (fun m n => F m n t) m n)
      (alternatingPairJet (k+1) (fun m n => F m n t) m n) t := by
  induction k generalizing m n with
  | zero => exact hF m n t
  | succ k ih => exact (ih (m+1) n).sub (ih m (n+1))

/-- The recurrence is the literal iterated derivative, with no smoothness premise left implicit. -/
theorem iteratedDeriv_eq_alternatingPairJet
    (F : ℕ → ℕ → ℝ → ℝ)
    (hF : ∀ m n t, HasDerivAt (F m n) (F (m+1) n t-F m (n+1) t) t)
    (k m n : ℕ) :
    iteratedDeriv k (F m n) = fun t => alternatingPairJet k (fun m n => F m n t) m n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hasDerivAt_alternatingPairJet F hF k m n t).deriv

/-- Integrability propagates through every finite recurrence step. -/
theorem integrable_alternatingPairJet
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℕ → ℕ → α → ℝ) (hF : ∀ m n, Integrable (F m n) μ)
    (k m n : ℕ) : Integrable (fun r => alternatingPairJet k (fun m n => F m n r) m n) μ := by
  induction k generalizing m n with
  | zero => exact hF m n
  | succ k ih => exact (ih (m+1) n).sub (ih m (n+1))

/-- Integration commutes with the full finite derivative recurrence. -/
theorem integral_alternatingPairJet
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℕ → ℕ → α → ℝ) (hF : ∀ m n, Integrable (F m n) μ)
    (k m n : ℕ) :
    (∫ r, alternatingPairJet k (fun m n => F m n r) m n ∂μ) =
      alternatingPairJet k (fun m n => ∫ r, F m n r ∂μ) m n := by
  induction k generalizing m n with
  | zero => rfl
  | succ k ih =>
    simp only [alternatingPairJet]
    rw [integral_sub (integrable_alternatingPairJet F hF k (m+1) n)
      (integrable_alternatingPairJet F hF k m (n+1)), ih, ih]

end
end GaloisForLFunctions.HTGeometry

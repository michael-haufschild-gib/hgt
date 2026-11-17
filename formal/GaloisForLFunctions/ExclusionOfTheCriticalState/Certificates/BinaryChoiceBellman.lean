import GaloisForLFunctions.ExclusionOfTheCriticalState.Certificates.FiniteDecisionBellman
import Mathlib.Data.Fin.Basic

/-!
# Exact Bellman optimization over binary configurations

A complete binary decision tree enumerates every configuration once.
Its Bellman value is the attained minimum of an arbitrary payoff on the
Boolean cube. The residual certificate therefore certifies a global
discrete optimum, and exactly `n + 1` sweeps forget all initial values.
-/

namespace GaloisForLFunctions.ExclusionOfTheCriticalState.DecisionBellman
noncomputable section
variable {α : Type*}

/-- Enumerate binary coordinates, retaining the specified terminal labels. -/
def choices : (n : ℕ) → ((Fin n → Bool) → α) → Tree α
  | 0, f => .leaf (f Fin.elim0)
  | n + 1, f => .branch 0 (choices n (fun σ => f (Fin.cases false σ)))
      0 (choices n (fun σ => f (Fin.cases true σ)))

theorem depth_choices (n : ℕ) (f : (Fin n → Bool) → α) : depth (choices n f) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [choices, depth, ih, max_self]

private theorem fin_cases_reconstruct {n : ℕ} (σ : Fin (n + 1) → Bool) :
    Fin.cases (σ 0) (fun i => σ i.succ) = σ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Literal route outcomes are exactly the values on the whole Boolean cube. -/
theorem outcomes_choices (g : α → ℝ) (n : ℕ) (f : (Fin n → Bool) → α) :
    outcomes g (choices n f) = Set.range (fun σ => g (f σ)) := by
  induction n with
  | zero =>
    ext q
    constructor
    · intro h
      exact ⟨Fin.elim0, h.symm⟩
    · rintro ⟨σ, rfl⟩
      have he : σ = Fin.elim0 := by funext i; exact Fin.elim0 i
      rw [he]
      rfl
  | succ n ih =>
    simp only [choices, outcomes, ih]
    ext q
    constructor
    · rintro (⟨v, ⟨σ, rfl⟩, rfl⟩ | ⟨v, ⟨σ, rfl⟩, rfl⟩)
      · exact ⟨Fin.cases false σ, (zero_add _).symm⟩
      · exact ⟨Fin.cases true σ, (zero_add _).symm⟩
    · rintro ⟨σ, rfl⟩
      have he := fin_cases_reconstruct σ
      cases h : σ 0
      · apply Or.inl
        refine ⟨g (f (Fin.cases false (fun i => σ i.succ))),
          ⟨fun i => σ i.succ, rfl⟩, ?_⟩
        rw [← h, he]
        exact zero_add _
      · apply Or.inr
        refine ⟨g (f (Fin.cases true (fun i => σ i.succ))),
          ⟨fun i => σ i.succ, rfl⟩, ?_⟩
        rw [← h, he]
        exact zero_add _

/-- The global minimum is attained, with no sign or convexity condition on the payoff. -/
theorem choices_value_isLeast (n : ℕ) (g : (Fin n → Bool) → ℝ) :
    IsLeast (Set.range g) (value g (choices n id)) := by
  simpa only [outcomes_choices, id_eq] using value_isLeast g (choices n id)

/-- Every candidate admits a computable residual interval for the true discrete optimum. -/
theorem choices_optimality_certificate (n : ℕ) (g : (Fin n → Bool) → ℝ)
    (W : Tree (Fin n → Bool) → ℝ) :
    ∃ σ : Fin n → Bool,
      (∀ τ, g σ ≤ g τ) ∧
      |W (choices n id) - g σ| ≤ certificate g W (choices n id) := by
  obtain ⟨σ, hσ⟩ := (choices_value_isLeast n g).1
  refine ⟨σ, ?_, ?_⟩
  · intro τ
    rw [hσ]
    exact (choices_value_isLeast n g).2 ⟨τ, rfl⟩
  · rw [hσ]
    exact abs_error_le_certificate g W _

/-- Full sweeps terminate after the coordinate depth plus the terminal reset. -/
theorem choices_iterate_exact (n : ℕ) (g : (Fin n → Bool) → ℝ)
    (W : Tree (Fin n → Bool) → ℝ) :
    (step g)^[n + 1] W (choices n id) = value g (choices n id) := by
  simpa only [depth_choices] using iterate_exact g W (choices n id)

/-- Strict negativity somewhere on the cube is equivalent to a strict residual certificate. -/
theorem choices_negative_certificate_iff (n : ℕ) (g : (Fin n → Bool) → ℝ) :
    (∃ W : Tree (Fin n → Bool) → ℝ,
      W (choices n id) + certificate g W (choices n id) < 0) ↔
      ∃ σ, g σ < 0 := by
  rw [negative_certificate_iff, outcomes_choices]
  constructor
  · rintro ⟨q, ⟨σ, rfl⟩, h⟩
    exact ⟨σ, h⟩
  · rintro ⟨σ, h⟩
    exact ⟨g σ, ⟨σ, rfl⟩, h⟩

#print axioms choices_value_isLeast
#print axioms choices_optimality_certificate
#print axioms choices_iterate_exact
#print axioms choices_negative_certificate_iff
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.DecisionBellman

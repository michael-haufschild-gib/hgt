import GaloisForLFunctions.HTGeometry.PartialCompletionAdmissionSeparationLaw

/-!
# Reflection-stable partial completions exist

Both reflection interfaces of a partial completion are realized by the identity reflection: it
preserves the admission domain and leaves every admitted observation where it is.  Stability is
also closed under composition, so the reflections a completion admits form a monoid rather than an
isolated example.
-/

namespace GaloisForLFunctions.HTGeometry

namespace PartialCompletion

variable {X Q : Type*} (P : PartialCompletion X Q)

/-- The identity reflection is stable. -/
theorem reflectionStable_id : P.ReflectionStable (id : X → X) := fun _ hx => hx

/-- Stable reflections compose. -/
theorem reflectionStable_comp {σ τ : X → X} (hσ : P.ReflectionStable σ)
    (hτ : P.ReflectionStable τ) : P.ReflectionStable (σ ∘ τ) :=
  fun x hx => hσ (τ x) (hτ x hx)

/-- **Every admitted observation is invariant under the identity reflection.** -/
theorem reflectionInvariantOnStable_id :
    P.ReflectionInvariantOnStable (id : X → X) (P.reflectionStable_id) := by
  intro x hx
  rfl

end PartialCompletion

end GaloisForLFunctions.HTGeometry

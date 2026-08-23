import GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemoryWitnesses

/-!
# Function transcendence carries no value information

Transcendence of a function over the rational function field `ℂ(z)` says nothing about the
arithmetic nature of any of its specialized values: a single witness — a function transcendental
over `ℂ(z)` taking a rational value at a point — defeats the implication.
-/

namespace RHTower

/-- A function transcendental over `ℂ(z)` may still take a rational value. -/
theorem exists_transcendental_with_rational_value :
    ∃ f : ℂ → ℂ, ¬ GaloisForLFunctions.HTGeometry.AlgebraicOn f (Set.univ : Set ℂ)
      ∧ ∃ z : ℂ, ∃ q : ℚ, f z = (q : ℂ) := by
  refine ⟨GaloisForLFunctions.HTGeometry.expSq,
    GaloisForLFunctions.HTGeometry.not_algebraicOn_expSq, 0, 1, ?_⟩
  rw [GaloisForLFunctions.HTGeometry.expSq]
  norm_num

/-- **Theorem B.**  Function-transcendence over `ℂ(z)` carries no information about the arithmetic
nature of a specialized value: transcendence of a function over the rational function field never
implies irrationality of its values. -/
theorem functionTranscendence_not_imply_valueIrrationality :
    ¬ ∀ f : ℂ → ℂ, ¬ GaloisForLFunctions.HTGeometry.AlgebraicOn f (Set.univ : Set ℂ) →
      ∀ z : ℂ, ¬ ∃ q : ℚ, f z = (q : ℂ) := by
  intro hcon
  obtain ⟨f, hf, z, q, hq⟩ := exists_transcendental_with_rational_value
  exact hcon f hf z ⟨q, hq⟩

end RHTower

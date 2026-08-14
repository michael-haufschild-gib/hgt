import GaloisForLFunctions.HTGeometry.BoundedPerturbedFriedrichsOperator

open Module Topology
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- A representation identity tested only on a dense form core extends to every form vector,
and therefore identifies an unbounded core operator with a restriction of the Friedrichs
realization. -/
theorem boundedPerturbedFriedrichsOperator_extends_of_formCore
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H))
    (T : H →ₗ.[ℂ] H) (coreLift : T.domain →ₗ[ℂ] V)
    (hsection : ∀ x : T.domain, J (coreLift x) = (x : H))
    (hcoreDense : DenseRange coreLift)
    (hformCore : ∀ x y : T.domain,
      inner ℂ (coreLift x) (coreLift y) +
          inner ℂ (B (x : H)) (y : H) =
        inner ℂ (T x) (y : H)) :
    T ≤ boundedPerturbedFriedrichsOperator J B hB := by
  apply boundedPerturbedFriedrichsOperator_extends_core
    J B hB hJinj hDense T coreLift hsection
  intro x v
  let P : V → Prop := fun w =>
    inner ℂ (coreLift x) w + inner ℂ (B (x : H)) (J w) =
      inner ℂ (T x) (J w)
  apply DenseRange.induction_on (p := P) hcoreDense v
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro y
    change inner ℂ (coreLift x) (coreLift y) +
        inner ℂ (B (x : H)) (J (coreLift y)) =
      inner ℂ (T x) (J (coreLift y))
    rw [hsection]
    exact hformCore x y

end

end GaloisForLFunctions.HTGeometry

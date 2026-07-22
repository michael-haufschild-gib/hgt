import GaloisForLFunctions.HTGeometry.HorizonContactSharpCrossing
import GaloisForLFunctions.HTGeometry.CommutativeRepresentationHorizon

/-!
# Sharp crossing-cone commutativity phase law

The crossing cone is the first nonlinear complete dependence horizon.  Its free-word realization
uses exactly one commutator channel, the full exterior rank available in two law directions.
Nevertheless no root in any autonomous commutative linear representation has this horizon,
regardless of hidden-state dimension, cyclicity, or faithfulness.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {K : Type u} {A : Type v} {M : Type w}
  [Field K] [CharZero K]
  [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module K M]

/-- **Sharp crossing-cone commutativity phase law.**  The crossing cone is attained by a
free-word observable at exact commutator rank one, but is excluded from every autonomous
one-root commutative linear representation. -/
theorem crossingCone_sharpFree_arbitraryCommutativeRepresentation_impossible
    (rho : A →ₐ[K] Module.End K M) (m : M) (L : (Fin 2 → K) →ₗ[K] A) :
    (∃ a : CommonDegreeEquationIndex (Fin 2) (fun _ : Fin 1 ↦ 2) →
        ProjectiveWordState (Fin 2) → K,
      linearDerivationDependenceHorizon (projectiveCompleteLawMap a 3)
          (projectiveCompleteRoot (K := K) (ι := Fin 2)
            (η := CommonDegreeEquationIndex (Fin 2) (fun _ : Fin 1 ↦ 2))) =
        crossingCone K ∧
      Module.finrank K
          (derivationCommutatorMap (projectiveCompleteLawMap a 3)).range = 1) ∧
      {c : Fin 2 → K |
        ¬ AlgebraicIndependent K (commutativeRepresentationJet rho m L c)} ≠
        crossingCone K := by
  obtain ⟨a, ha, hrank⟩ := exists_crossingCone_horizon_sharp_commutator_rank (K := K)
  refine ⟨⟨a, ha, ?_⟩, ?_⟩
  · simpa [horizonCommutatorIndex_crossingCone (K := K)] using hrank
  · rw [commutativeRepresentation_dependenceHorizon_eq_submodule rho m L]
    exact crossingCone_not_submodule (commutativeRepresentationHorizon rho m L)

end

end GaloisForLFunctions.HTGeometry

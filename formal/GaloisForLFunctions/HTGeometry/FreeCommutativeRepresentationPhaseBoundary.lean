import GaloisForLFunctions.HTGeometry.CommutativeRepresentationHorizon
import GaloisForLFunctions.HTGeometry.FreeCommutingHorizonPhaseBoundary

/-!
# The free/autonomous-commutative phase boundary

The cyclic commuting no-go theorem is not evaded by placing the observable root inside a larger,
noncyclic hidden state space.  Every one-root autonomous representation of a commutative
principal-symbol algebra reduces intrinsically to the quotient by that root's annihilator, so its
complete dependence horizon remains linear.

Combining this reduction with free-word projective universality gives the representation-level
phase theorem: every finite homogeneous nonlinear projective cone is the exact complete horizon of
one free noncommuting differential observable, but it is impossible for one root in every
autonomous commutative linear representation, without any finiteness or faithfulness assumption.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

universe u v w x

variable {K : Type u} {ι η : Type v} {A : Type w} {M : Type x}
  [Field K] [Fintype ι] [Fintype η]
  [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module K M]

/-- **General free/commutative-representation phase boundary.**  A nonlinear finite homogeneous
projective cone is freely realizable as an exact one-observable complete horizon, but cannot be
the horizon of the same one-root observable problem in any autonomous commutative linear
representation, even on an arbitrary hidden state space. -/
theorem nonlinearProjectiveHorizon_free_realizable_commutativeRepresentation_impossible
    (P : η → MvPolynomial ι K) (d : η → ℕ)
    (hP : ∀ j, (P j).IsHomogeneous (d j))
    (hNonlinear : ∀ H : Submodule K (ι → K),
      (H : Set (ι → K)) ≠ finiteLawZeroCone P)
    (ρ : A →ₐ[K] Module.End K M) (m : M) (L : (ι → K) →ₗ[K] A) :
    (∃ a : CommonDegreeEquationIndex ι d → ProjectiveWordState ι → K,
      ∀ (c : ι → K), (∃ i, c i ≠ 0) →
        ((¬ AlgebraicIndependent K
            (fun r : ℕ ↦ directionalJet
              (projectiveCompleteDerivation a ((∑ j, d j) + 1)) c r
              (projectiveCompleteRoot
                (K := K) (ι := ι) (η := CommonDegreeEquationIndex ι d)))) ↔
          c ∈ finiteLawZeroCone P)) ∧
      {c : ι → K |
        ¬ AlgebraicIndependent K (commutativeRepresentationJet ρ m L c)} ≠
        finiteLawZeroCone P := by
  obtain ⟨hfree, _⟩ :=
    nonlinearProjectiveHorizon_free_realizable_cyclicCommuting_impossible
      P d hP hNonlinear
  refine ⟨hfree, ?_⟩
  rw [commutativeRepresentation_dependenceHorizon_eq_submodule ρ m L]
  exact hNonlinear (commutativeRepresentationHorizon ρ m L)

end


end GaloisForLFunctions.HTGeometry

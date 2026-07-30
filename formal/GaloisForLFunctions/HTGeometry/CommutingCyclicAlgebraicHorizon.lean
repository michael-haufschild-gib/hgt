import GaloisForLFunctions.HTGeometry.AlgebraicDirectionHorizon
import GaloisForLFunctions.HTGeometry.CommutingCyclicDifferentialObservable

/-!
# Unconditional cyclic commuting horizon linearity

This file removes the homogeneity assumption from the complete differential-horizon classification.
For an arbitrary ideal `I` in the commutative law algebra, the class of the directional law form in
`K[X_i] / I` is either algebraic or transcendental over `K`.  Algebraicity is equivalent to linear
dependence of its complete power orbit and hence to algebraic dependence of the actual iterated
directional jet of the root observable in the symmetric differential domain.

The algebraic elements of a commutative algebra form a `K`-subalgebra.  Their inverse image under
the linear law-form map is therefore a vector subspace.  Thus every complete dependence horizon in
the cyclic commuting construction is linear for every annihilator ideal, including nonhomogeneous
and nonreduced ideals.

This yields an unconditional free/commuting phase separation: the nonlinear crossing horizon is an
exact complete-jet horizon in the free noncommuting word field, but cannot occur in any cyclic
commuting model of this form.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v

variable {K : Type u} {ι : Type v} [Field K] [Fintype ι]

/-- The directional law form followed by the quotient map into the cyclic law algebra. -/
def quotientLawLinearForm (I : Ideal (MvPolynomial ι K)) :
    (ι → K) →ₗ[K] (MvPolynomial ι K ⧸ I) :=
  (Ideal.Quotient.mkₐ K I).toLinearMap.comp lawLinearForm

/-- Directions whose law class is algebraic over the base field.  This is a submodule without any
homogeneity assumption on the annihilator ideal. -/
def commutingCyclicAlgebraicHorizon
    (I : Ideal (MvPolynomial ι K)) : Submodule K (ι → K) :=
  algebraicDirectionHorizon (quotientLawLinearForm I)

/-- A direction lies on the unconditional cyclic horizon exactly when its quotient law element is
algebraic over the base field. -/
theorem mem_commutingCyclicAlgebraicHorizon_iff
    (I : Ideal (MvPolynomial ι K)) (c : ι → K) :
    c ∈ commutingCyclicAlgebraicHorizon I ↔
      IsAlgebraic K (Ideal.Quotient.mk I (lawLinearForm c)) := by
  rw [commutingCyclicAlgebraicHorizon,
    mem_algebraicDirectionHorizon_iff]
  simp [quotientLawLinearForm, Ideal.Quotient.mkₐ_eq_mk]

/-- The canonical cyclic observable jet is algebraically independent exactly when the quotient law
element is transcendental.  No grading or homogeneity is used. -/
theorem commutingCyclicObservableJet_algebraicIndependent_iff_transcendental
    (I : Ideal (MvPolynomial ι K)) (c : ι → K) :
    AlgebraicIndependent K (commutingCyclicObservableJet I c) ↔
      Transcendental K (Ideal.Quotient.mk I (lawLinearForm c)) := by
  simpa [commutingCyclicObservableJet, cyclicSymmetricObservableJet,
    cyclicPowerState] using!
      symmetricPowerObservable_algebraicIndependent_iff_transcendental
        (K := K) (A := MvPolynomial ι K ⧸ I)
        (Ideal.Quotient.mk I (lawLinearForm c))

/-- **Unconditional complete cyclic differential classification.**  The actual iterated jet of the
single root observable is algebraically dependent exactly on the algebraic-direction submodule. -/
theorem not_algebraicIndependent_cyclicDirectionalJet_iff_algebraicHorizon
    (I : Ideal (MvPolynomial ι K)) (c : ι → K) :
    (¬ AlgebraicIndependent K (cyclicDirectionalJet I c)) ↔
      c ∈ commutingCyclicAlgebraicHorizon I := by
  have hjet : cyclicDirectionalJet I c = commutingCyclicObservableJet I c :=
    funext (cyclicDirectionalJet_eq_observableJet I c)
  rw [hjet, commutingCyclicObservableJet_algebraicIndependent_iff_transcendental]
  simpa [Transcendental] using
    (mem_commutingCyclicAlgebraicHorizon_iff I c).symm

/-- The full differential-dependence horizon is exactly the carrier of a vector subspace for every
annihilator ideal. -/
theorem cyclicDifferentialDependenceHorizon_eq_algebraicSubspace
    (I : Ideal (MvPolynomial ι K)) :
    {c : ι → K | ¬ AlgebraicIndependent K (cyclicDirectionalJet I c)} =
      (commutingCyclicAlgebraicHorizon I : Set (ι → K)) := by
  ext c
  exact not_algebraicIndependent_cyclicDirectionalJet_iff_algebraicHorizon I c

/-- In the homogeneous case, the unconditional algebraic horizon reduces to the radical
nilpotence horizon proved previously. -/
theorem commutingCyclicAlgebraicHorizon_eq_nilpotenceHorizon
    (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K)) :
    commutingCyclicAlgebraicHorizon I = commutingCyclicNilpotenceHorizon I := by
  ext c
  rw [← not_algebraicIndependent_cyclicDirectionalJet_iff_algebraicHorizon I c,
    not_algebraicIndependent_cyclicDirectionalJet_iff I hI c]

/-- The nonlinear crossing cone cannot be the complete differential-dependence horizon of any
cyclic commuting model, with no homogeneity assumption. -/
theorem crossingCone_not_cyclicAlgebraicDifferentialHorizon
    (I : Ideal (MvPolynomial (Fin 2) K)) :
    {c : Fin 2 → K | ¬ AlgebraicIndependent K (cyclicDirectionalJet I c)} ≠
      crossingCone K := by
  rw [cyclicDifferentialDependenceHorizon_eq_algebraicSubspace I]
  exact crossingCone_not_submodule (commutingCyclicAlgebraicHorizon I)

/-- **Unconditional free/commuting phase boundary.**  One free noncommuting observable realizes the
nonlinear crossing as its exact complete horizon, while no cyclic commuting annihilator model can
have that horizon. -/
theorem crossingHorizon_free_realizable_cyclicAlgebraic_impossible :
    ( ∃ a : CommonDegreeEquationIndex (Fin 2) (fun _ : Fin 1 ↦ 2) →
        ProjectiveWordState (Fin 2) → K,
      ∀ (c : Fin 2 → K), (∃ i, c i ≠ 0) →
        ((¬ AlgebraicIndependent K
            (fun r : ℕ ↦ directionalJet
              (projectiveCompleteDerivation a 3) c r
              (projectiveCompleteRoot
                (K := K) (ι := Fin 2)
                (η := CommonDegreeEquationIndex (Fin 2) (fun _ : Fin 1 ↦ 2))))) ↔
          c ∈ crossingCone K)) ∧
      (∀ I : Ideal (MvPolynomial (Fin 2) K),
        {c : Fin 2 → K |
          ¬ AlgebraicIndependent K (cyclicDirectionalJet I c)} ≠ crossingCone K) := by
  exact ⟨exists_completeJet_crossingHorizon,
    crossingCone_not_cyclicAlgebraicDifferentialHorizon⟩

end

end GaloisForLFunctions.HTGeometry

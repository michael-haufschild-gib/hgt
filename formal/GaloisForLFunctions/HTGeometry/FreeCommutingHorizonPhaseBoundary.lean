import GaloisForLFunctions.HTGeometry.CommutingCyclicAlgebraicHorizon

/-!
# The free/commuting hypertranscendence phase boundary

Every finite homogeneous zero locus is the exact complete directional dependence horizon of one
observable in the free noncommuting word field.  In contrast, every complete horizon of the actual
cyclic commuting differential observable is a vector subspace, for every annihilator ideal.

This file combines those classification theorems at their natural level of generality.  Whenever
the affine zero cone of a finite homogeneous family is not a vector subspace, that cone is freely
realizable and cyclic-commutatively impossible.  The result applies at once to reducible unions,
singular nonlinear cones, and arbitrary nonlinear projective zero loci.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

universe u v

variable {K : Type u} {ι η : Type v} [Field K] [Fintype ι] [Fintype η]

/-- The affine cone cut out by a finite family of law polynomials. -/
def finiteLawZeroCone (P : η → MvPolynomial ι K) : Set (ι → K) :=
  {c | ∀ j, MvPolynomial.eval c (P j) = 0}

/-- **General free/commuting phase boundary.**  If a finite homogeneous zero cone is not the
carrier of any vector subspace, then it is an exact complete horizon in the free noncommuting
model and cannot be the complete horizon of any cyclic commuting annihilator model. -/
theorem nonlinearProjectiveHorizon_free_realizable_cyclicCommuting_impossible
    (P : η → MvPolynomial ι K) (d : η → ℕ)
    (hP : ∀ j, (P j).IsHomogeneous (d j))
    (hNonlinear : ∀ H : Submodule K (ι → K),
      (H : Set (ι → K)) ≠ finiteLawZeroCone P) :
    (∃ a : CommonDegreeEquationIndex ι d → ProjectiveWordState ι → K,
      ∀ (c : ι → K), (∃ i, c i ≠ 0) →
        ((¬ AlgebraicIndependent K
            (fun r : ℕ ↦ directionalJet
              (projectiveCompleteDerivation a ((∑ j, d j) + 1)) c r
              (projectiveCompleteRoot
                (K := K) (ι := ι) (η := CommonDegreeEquationIndex ι d)))) ↔
          c ∈ finiteLawZeroCone P)) ∧
      (∀ I : Ideal (MvPolynomial ι K),
        {c : ι → K | ¬ AlgebraicIndependent K (cyclicDirectionalJet I c)} ≠
          finiteLawZeroCone P) := by
  obtain ⟨a, ha⟩ :=
    exists_completeJet_horizon_eq_finiteHomogeneousZeroLocus P d hP
  refine ⟨⟨a, ?_⟩, ?_⟩
  · intro c hc
    simpa [finiteLawZeroCone] using ha c hc
  · intro I hEq
    apply hNonlinear (commutingCyclicAlgebraicHorizon I)
    calc
      ((commutingCyclicAlgebraicHorizon I : Submodule K (ι → K)) :
          Set (ι → K)) =
          {c : ι → K |
            ¬ AlgebraicIndependent K (cyclicDirectionalJet I c)} :=
        (cyclicDifferentialDependenceHorizon_eq_algebraicSubspace I).symm
      _ = finiteLawZeroCone P := hEq

end

end GaloisForLFunctions.HTGeometry

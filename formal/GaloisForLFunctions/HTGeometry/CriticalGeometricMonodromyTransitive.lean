import GaloisForLFunctions.HTGeometry.CriticalGeometricMonodromy
import Mathlib.FieldTheory.Normal.Basic

/-!
# Transitivity of the actual critical geometric monodromy

The normal-closure Galois group acts transitively on the observation-field embeddings of the
actual critical source field.  The proof uses a primitive element for the finite separable source
extension and normality of the actual normal closure; no abstract cover or transitivity premise is
introduced.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

/-- Any two actual geometric sheets differ by an automorphism of the actual normal closure. -/
theorem criticalNormalClosureAction_transitive
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (f g : criticalGeometricSheet K m n) :
    ∃ σ : criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
        criticalNormalClosure K m n,
      criticalNormalClosureAction K m n σ f = g := by
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  letI : Algebra.IsSeparable (criticalObservationField K m n)
      (criticalSourceField K m n) := inferInstance
  letI : IsScalarTower (criticalObservationField K m n)
      (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n) :=
    AlgebraicClosure.instIsScalarTower (criticalSourceField K m n)
  letI : Algebra.IsAlgebraic (criticalObservationField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    Algebra.IsAlgebraic.trans (criticalObservationField K m n)
      (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n)
  letI : Normal (criticalObservationField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    { splits' _ := IsAlgClosed.splits _ }
  letI : Normal (criticalObservationField K m n)
      (criticalNormalClosure K m n) :=
    normalClosure.normal (criticalObservationField K m n)
      (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n)
  let pb := Field.powerBasisOfFiniteOfSeparable
    (criticalObservationField K m n) (criticalSourceField K m n)
  have hmin : minpoly (criticalObservationField K m n) (g pb.gen) =
      minpoly (criticalObservationField K m n) (f pb.gen) := by
    rw [minpoly.algHom_eq g g.injective, minpoly.algHom_eq f f.injective]
  have horbit : g pb.gen ∈ MulAction.orbit
      (criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
        criticalNormalClosure K m n) (f pb.gen) :=
    (Normal.minpoly_eq_iff_mem_orbit (criticalNormalClosure K m n)).mp hmin
  rw [MulAction.mem_orbit_iff] at horbit
  obtain ⟨σ, hσ⟩ := horbit
  refine ⟨σ, ?_⟩
  apply pb.algHom_ext
  exact hσ

/-- The actual geometric monodromy subgroup acts transitively on the actual geometric sheets. -/
theorem criticalGeometricMonodromy_isPretransitive
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    MulAction.IsPretransitive (criticalGeometricMonodromy K m n)
      (criticalGeometricSheet K m n) := by
  rw [MulAction.isPretransitive_iff]
  intro f g
  obtain ⟨σ, hσ⟩ := criticalNormalClosureAction_transitive K hm hn f g
  refine ⟨⟨criticalNormalClosureAction K m n σ, ⟨σ, rfl⟩⟩, ?_⟩
  exact hσ

end

end GaloisForLFunctions.HTGeometry

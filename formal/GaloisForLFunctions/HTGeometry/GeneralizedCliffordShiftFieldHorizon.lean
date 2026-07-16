import GaloisForLFunctions.HTGeometry.GeneralizedCliffordShiftHorizon
import GaloisForLFunctions.HTGeometry.FractionRingDerivation

/-!
# Differential-field realization of generalized Clifford horizons

The shift-suspended Clifford principal symbol first acts by derivations on a symmetric observable
domain.  This file extends those derivations by the quotient rule to its fraction field.  The
canonical embedding preserves algebraic independence, so the exact scalar horizon survives in an
actual differential field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {K : Type u} {M : Type v}
  [Field K] [AddCommGroup M] [Module K M]

/-- The rational observable field of the suspended internal state space. -/
abbrev GeneralizedCliffordShiftField (K : Type u) (M : Type v)
    [Field K] [AddCommGroup M] [Module K M] :=
  FractionRing (SymmetricAlgebra K (ℕ → M))

/-- The canonical embedding of polynomial observables into the rational observable field. -/
def generalizedCliffordShiftFieldEmbedding :
    SymmetricAlgebra K (ℕ → M) →ₐ[K] GeneralizedCliffordShiftField K M :=
  IsScalarTower.toAlgHom K (SymmetricAlgebra K (ℕ → M))
    (GeneralizedCliffordShiftField K M)

theorem generalizedCliffordShiftFieldEmbedding_injective :
    Function.Injective
      (generalizedCliffordShiftFieldEmbedding (K := K) (M := M)) :=
  IsFractionRing.injective (SymmetricAlgebra K (ℕ → M))
    (GeneralizedCliffordShiftField K M)

@[simp]
theorem generalizedCliffordShiftFieldEmbedding_apply
    (x : SymmetricAlgebra K (ℕ → M)) :
    generalizedCliffordShiftFieldEmbedding (K := K) (M := M) x =
      algebraMap (SymmetricAlgebra K (ℕ → M))
        (GeneralizedCliffordShiftField K M) x := rfl

/-- The observable derivation, with values embedded in the rational field. -/
def generalizedCliffordShiftSourceDerivation (A : Module.End K M) :
    Derivation K (SymmetricAlgebra K (ℕ → M))
      (GeneralizedCliffordShiftField K M) :=
  (Algebra.linearMap (SymmetricAlgebra K (ℕ → M))
      (GeneralizedCliffordShiftField K M)).compDer
    (generalizedCliffordShiftDerivation A)

/-- The quotient-rule extension to the full rational observable field. -/
def generalizedCliffordShiftFieldDerivation (A : Module.End K M) :
    Derivation K (GeneralizedCliffordShiftField K M)
      (GeneralizedCliffordShiftField K M) :=
  fractionRingDerivation (generalizedCliffordShiftSourceDerivation A)

/-- The field derivation agrees with the suspended action on embedded polynomial observables. -/
theorem generalizedCliffordShiftFieldDerivation_embedding
    (A : Module.End K M) (x : SymmetricAlgebra K (ℕ → M)) :
    generalizedCliffordShiftFieldDerivation A
        (generalizedCliffordShiftFieldEmbedding (K := K) (M := M) x) =
      generalizedCliffordShiftFieldEmbedding (K := K) (M := M)
        (generalizedCliffordShiftDerivation A x) := by
  rw [generalizedCliffordShiftFieldDerivation,
    generalizedCliffordShiftFieldEmbedding_apply,
    fractionRingDerivation_algebraMap]
  rfl

/-- The grade-zero root observable in the rational field. -/
def generalizedCliffordShiftFieldRoot (m : M) :
    GeneralizedCliffordShiftField K M :=
  generalizedCliffordShiftFieldEmbedding (K := K) (M := M)
    (SymmetricAlgebra.ι K (ℕ → M) (periodicLevel 0 m))

/-- The complete ordinary differential jet of the rational root observable. -/
def generalizedCliffordShiftFieldJet
    (A : Module.End K M) (m : M) (n : ℕ) :
    GeneralizedCliffordShiftField K M :=
  ((generalizedCliffordShiftFieldDerivation A :
      GeneralizedCliffordShiftField K M → GeneralizedCliffordShiftField K M)^[n])
    (generalizedCliffordShiftFieldRoot m)

/-- Every rational-field jet is the embedded linear observable of the suspended state orbit. -/
theorem generalizedCliffordShiftFieldJet_eq_embeddedObservableOrbit
    (A : Module.End K M) (m : M) :
    ∀ n : ℕ,
      generalizedCliffordShiftFieldJet A m n =
        generalizedCliffordShiftFieldEmbedding (K := K) (M := M)
          (SymmetricAlgebra.ι K (ℕ → M)
            (((generalizedCliffordShiftOperator A : (ℕ → M) → (ℕ → M))^[n])
              (periodicLevel 0 m))) := by
  intro n
  induction n with
  | zero => simp [generalizedCliffordShiftFieldJet,
      generalizedCliffordShiftFieldRoot]
  | succ n ih =>
      rw [generalizedCliffordShiftFieldJet, Function.iterate_succ_apply',
        ← generalizedCliffordShiftFieldJet, ih,
        generalizedCliffordShiftFieldDerivation_embedding,
        generalizedCliffordShiftDerivation,
        symmetricAlgebraDerivation_ι,
        Function.iterate_succ_apply']

/-- **Differential-field Clifford horizon theorem.**  In the rational observable field, the
complete root jet is algebraically independent exactly off the scalar generalized-Clifford
horizon. -/
theorem generalizedCliffordShiftFieldJet_algebraicIndependent_iff
    (A : Module.End K M) (d : ℕ) (F : K) (m : M)
    (hd : d ≠ 0) (hpower : A ^ d = F • LinearMap.id) (hm : m ≠ 0) :
    AlgebraicIndependent K (generalizedCliffordShiftFieldJet A m) ↔ F ≠ 0 := by
  constructor
  · intro hAI hF
    apply hAI.ne_zero d
    rw [generalizedCliffordShiftFieldJet_eq_embeddedObservableOrbit,
      generalizedCliffordShiftOperator_orbit_eq_zero A d F m hpower hF]
    simp
  · intro hF
    have hstate := generalizedCliffordShiftOperator_orbit_linearIndependent
      A d F m hd hpower hF hm
    have hsym : AlgebraicIndependent K (fun n : ℕ ↦
        SymmetricAlgebra.ι K (ℕ → M)
          (((generalizedCliffordShiftOperator A : (ℕ → M) → (ℕ → M))^[n])
            (periodicLevel 0 m))) :=
      symmetricAlgebra_ι_algebraicIndependent_of_linearIndependent _ hstate
    have hemb := hsym.map'
      (generalizedCliffordShiftFieldEmbedding_injective (K := K) (M := M))
    have hfamily : generalizedCliffordShiftFieldJet A m =
        generalizedCliffordShiftFieldEmbedding (K := K) (M := M) ∘
          (fun n : ℕ ↦ SymmetricAlgebra.ι K (ℕ → M)
            (((generalizedCliffordShiftOperator A : (ℕ → M) → (ℕ → M))^[n])
              (periodicLevel 0 m))) := by
      funext n
      exact generalizedCliffordShiftFieldJet_eq_embeddedObservableOrbit A m n
    rw [hfamily]
    exact hemb

variable {V : Type w} [AddCommGroup V] [Module K V]

/-- Every pointwise Roby power pencil has exact scalar zero-locus dependence horizon in one
explicit rational differential field. -/
theorem generalizedCliffordShiftField_dependenceHorizon_eq_zeroLocus
    (symbol : V →ₗ[K] Module.End K M) (F : V → K)
    (d : ℕ) (hd : d ≠ 0) (m : M) (hm : m ≠ 0)
    (hpower : ∀ c : V, (symbol c) ^ d = F c • LinearMap.id) :
    {c : V | ¬ AlgebraicIndependent K
      (generalizedCliffordShiftFieldJet (symbol c) m)} =
      {c : V | F c = 0} := by
  ext c
  change (¬ AlgebraicIndependent K
    (generalizedCliffordShiftFieldJet (symbol c) m)) ↔ F c = 0
  rw [generalizedCliffordShiftFieldJet_algebraicIndependent_iff
    (symbol c) d (F c) m hd (hpower c) hm]
  exact not_ne_iff

end

end GaloisForLFunctions.HTGeometry

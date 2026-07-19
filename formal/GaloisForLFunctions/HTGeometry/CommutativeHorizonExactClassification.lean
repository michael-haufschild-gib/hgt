import GaloisForLFunctions.HTGeometry.CommutativeRepresentationHorizon
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Exact classification of autonomous commutative horizons

The general representation theorem proves that every autonomous one-root commutative linear
horizon is a vector subspace.  This leaf proves the converse: every vector subspace is realized by
the regular representation of the symmetric algebra on the quotient law space.  Hence the
possible complete dependence horizons in the autonomous commutative phase are exactly all vector
subspaces.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The commutative law algebra realizing a prescribed linear horizon. -/
abbrev SubspaceCommutativeLawAlgebra
    (H : Submodule K V) :=
  SymmetricAlgebra K (V ⧸ H)

/-- Send a law direction to its degree-one class modulo the prescribed horizon. -/
def subspaceCommutativeLawMap
    (H : Submodule K V) :
    V →ₗ[K] SubspaceCommutativeLawAlgebra H :=
  (SymmetricAlgebra.ι K (V ⧸ H)).comp H.mkQ

/-- The regular representation of the law algebra used by the linear-horizon realization. -/
def subspaceCommutativeRegularRepresentation
    (H : Submodule K V) :
    SubspaceCommutativeLawAlgebra H →ₐ[K]
      Module.End K (SubspaceCommutativeLawAlgebra H) :=
  Algebra.lsmul K K (SubspaceCommutativeLawAlgebra H)

/-- **Exact classification of the commutative phase.**  Every vector subspace of any law space
is the complete dependence horizon of an explicit autonomous one-root commutative linear
representation.  Together with `commutativeRepresentation_dependenceHorizon_eq_submodule`, this
classifies the possible horizons in that phase exactly. -/
theorem subspaceCommutative_dependenceHorizon_eq
    (H : Submodule K V) :
    {v : V |
        ¬ AlgebraicIndependent K
          (commutativeRepresentationJet
            (subspaceCommutativeRegularRepresentation H)
            (1 : SubspaceCommutativeLawAlgebra H)
            (subspaceCommutativeLawMap H) v)} =
      (H : Set V) := by
  ext v
  have hstate : ∀ n : ℕ,
      (((subspaceCommutativeRegularRepresentation H
          (subspaceCommutativeLawMap H v)) ^ n)
          (1 : SubspaceCommutativeLawAlgebra H)) =
        (subspaceCommutativeLawMap H v) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, ih]
        simp [subspaceCommutativeRegularRepresentation, Algebra.lsmul_coe, pow_succ']
  have hjet :
      commutativeRepresentationJet
          (subspaceCommutativeRegularRepresentation H)
          (1 : SubspaceCommutativeLawAlgebra H)
          (subspaceCommutativeLawMap H) v =
        fun n : ℕ => SymmetricAlgebra.ι K (SubspaceCommutativeLawAlgebra H)
          ((subspaceCommutativeLawMap H v) ^ n) := by
    funext n
    rw [commutativeRepresentationJet_eq_powerObservable]
    rw [hstate n]
  rw [Set.mem_setOf_eq, hjet,
    symmetricPowerObservable_algebraicIndependent_iff_transcendental]
  constructor
  · intro hnot
    by_contra hv
    have hq : H.mkQ v ≠ 0 := fun hq0 =>
      hv ((Submodule.Quotient.mk_eq_zero H).mp hq0)
    have hlinear : LinearIndependent K (fun _ : Unit ↦ H.mkQ v) :=
      (linearIndependent_unique_iff).2 hq
    have hindependent : AlgebraicIndependent K
        (fun _ : Unit ↦ SymmetricAlgebra.ι K (V ⧸ H) (H.mkQ v)) :=
      (symmetricAlgebra_ι_algebraicIndependent_iff_linearIndependent _).2 hlinear
    apply hnot
    simpa [subspaceCommutativeLawMap] using hindependent.transcendental ()
  · intro hv
    have hq : H.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero H).mpr hv
    simpa [subspaceCommutativeLawMap, hq, Transcendental] using
      (isAlgebraic_zero : IsAlgebraic K (0 : SubspaceCommutativeLawAlgebra H))

end

end GaloisForLFunctions.HTGeometry

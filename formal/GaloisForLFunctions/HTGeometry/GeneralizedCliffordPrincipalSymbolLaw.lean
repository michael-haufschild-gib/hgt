import GaloisForLFunctions.HTGeometry.GeneralizedCliffordShiftFieldHorizon
import GaloisForLFunctions.HTGeometry.SymmetricAlgebraDerivationLinear
import GaloisForLFunctions.HTGeometry.HorizonCommutatorGeometry

/-!
# The generalized Clifford principal-symbol law

A linear pencil of internal Roby symbols gives a genuine linear law space of derivations on the
rational shift-observable field.  Its complete differential-dependence horizon is exactly the
scalar zero locus.  Consequently, any projective chord escaping that zero locus forces a nonzero
Lie commutator of the endpoint laws.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {K : Type u} {M : Type v} {V : Type w}
  [Field K] [CharZero K]
  [AddCommGroup M] [Module K M]
  [AddCommGroup V] [Module K V]

/-- Shift suspension depends linearly on the internal principal symbol. -/
def generalizedCliffordShiftOperatorLinearMap :
    Module.End K M →ₗ[K] Module.End K (ℕ → M) where
  toFun := generalizedCliffordShiftOperator
  map_add' A B := by
    ext f n
    cases n <;>
      simp [generalizedCliffordShiftOperator, periodicUnilateralShift,
        periodicPointwiseEnd]
  map_smul' c A := by
    ext f n
    cases n <;>
      simp [generalizedCliffordShiftOperator, periodicUnilateralShift,
        periodicPointwiseEnd]

omit [CharZero K] in
theorem generalizedCliffordShiftDerivation_add (A B : Module.End K M) :
    generalizedCliffordShiftDerivation (A + B) =
      generalizedCliffordShiftDerivation A + generalizedCliffordShiftDerivation B := by
  simp only [generalizedCliffordShiftDerivation]
  rw [show generalizedCliffordShiftOperator (A + B) =
      generalizedCliffordShiftOperator A + generalizedCliffordShiftOperator B by
    exact (generalizedCliffordShiftOperatorLinearMap (K := K) (M := M)).map_add A B]
  exact symmetricAlgebraDerivation_add _ _

omit [CharZero K] in
theorem generalizedCliffordShiftDerivation_smul (c : K) (A : Module.End K M) :
    generalizedCliffordShiftDerivation (c • A) =
      c • generalizedCliffordShiftDerivation A := by
  simp only [generalizedCliffordShiftDerivation]
  rw [show generalizedCliffordShiftOperator (c • A) =
      c • generalizedCliffordShiftOperator A by
    exact (generalizedCliffordShiftOperatorLinearMap (K := K) (M := M)).map_smul c A]
  exact symmetricAlgebraDerivation_smul _ _

omit [CharZero K] in
theorem generalizedCliffordShiftFieldDerivation_add (A B : Module.End K M) :
    generalizedCliffordShiftFieldDerivation (A + B) =
      generalizedCliffordShiftFieldDerivation A +
        generalizedCliffordShiftFieldDerivation B := by
  apply fractionRing_derivation_ext
    (A := SymmetricAlgebra K (ℕ → M))
  intro x
  change generalizedCliffordShiftFieldDerivation (A + B)
      (generalizedCliffordShiftFieldEmbedding (K := K) (M := M) x) =
    generalizedCliffordShiftFieldDerivation A
        (generalizedCliffordShiftFieldEmbedding (K := K) (M := M) x) +
      generalizedCliffordShiftFieldDerivation B
        (generalizedCliffordShiftFieldEmbedding (K := K) (M := M) x)
  rw [generalizedCliffordShiftFieldDerivation_embedding,
    generalizedCliffordShiftFieldDerivation_embedding,
    generalizedCliffordShiftFieldDerivation_embedding,
    generalizedCliffordShiftDerivation_add]
  simp

omit [CharZero K] in
theorem generalizedCliffordShiftFieldDerivation_smul
    (c : K) (A : Module.End K M) :
    generalizedCliffordShiftFieldDerivation (c • A) =
      c • generalizedCliffordShiftFieldDerivation A := by
  apply fractionRing_derivation_ext
    (A := SymmetricAlgebra K (ℕ → M))
  intro x
  change generalizedCliffordShiftFieldDerivation (c • A)
      (generalizedCliffordShiftFieldEmbedding (K := K) (M := M) x) =
    c • generalizedCliffordShiftFieldDerivation A
      (generalizedCliffordShiftFieldEmbedding (K := K) (M := M) x)
  rw [generalizedCliffordShiftFieldDerivation_embedding,
    generalizedCliffordShiftFieldDerivation_embedding,
    generalizedCliffordShiftDerivation_smul]
  simp

/-- The rational-field derivation depends linearly on the internal Clifford symbol. -/
def generalizedCliffordShiftFieldDerivationLinearMap :
    Module.End K M →ₗ[K]
      Derivation K (GeneralizedCliffordShiftField K M)
        (GeneralizedCliffordShiftField K M) where
  toFun := generalizedCliffordShiftFieldDerivation
  map_add' := generalizedCliffordShiftFieldDerivation_add
  map_smul' := generalizedCliffordShiftFieldDerivation_smul

/-- The linear differential-field law induced by a linear pencil of generalized Clifford
symbols. -/
def generalizedCliffordShiftFieldDerivationLaw
    (symbol : V →ₗ[K] Module.End K M) :
    V →ₗ[K] Derivation K (GeneralizedCliffordShiftField K M)
      (GeneralizedCliffordShiftField K M) :=
  (generalizedCliffordShiftFieldDerivationLinearMap (K := K) (M := M)).comp symbol

omit [CharZero K] in
@[simp]
theorem generalizedCliffordShiftFieldDerivationLaw_apply
    (symbol : V →ₗ[K] Module.End K M) (c : V) :
    generalizedCliffordShiftFieldDerivationLaw symbol c =
      generalizedCliffordShiftFieldDerivation (symbol c) := rfl

omit [CharZero K] in
/-- The abstract linear-law jet agrees with the explicit rational Clifford-shift jet. -/
theorem generalizedCliffordField_linearDerivationLawJet_eq
    (symbol : V →ₗ[K] Module.End K M) (m : M) (c : V) (n : ℕ) :
    linearDerivationLawJet (generalizedCliffordShiftFieldDerivationLaw symbol)
        (generalizedCliffordShiftFieldRoot m) c n =
      generalizedCliffordShiftFieldJet (symbol c) m n := by
  rfl

omit [CharZero K] in
/-- **Generalized Clifford principal-symbol theorem.**  The actual dependence horizon of the
linear differential-field law is exactly the zero locus of the scalar form in its Roby power
relation. -/
theorem generalizedCliffordField_linearDependenceHorizon_eq_zeroLocus
    (symbol : V →ₗ[K] Module.End K M) (F : V → K)
    (d : ℕ) (hd : d ≠ 0) (m : M) (hm : m ≠ 0)
    (hpower : ∀ c : V, (symbol c) ^ d = F c • LinearMap.id) :
    linearDerivationDependenceHorizon
        (generalizedCliffordShiftFieldDerivationLaw symbol)
        (generalizedCliffordShiftFieldRoot m) =
      {c : V | F c = 0} := by
  ext c
  change (¬ AlgebraicIndependent K
    (linearDerivationLawJet (generalizedCliffordShiftFieldDerivationLaw symbol)
      (generalizedCliffordShiftFieldRoot m) c)) ↔ F c = 0
  rw [show linearDerivationLawJet
      (generalizedCliffordShiftFieldDerivationLaw symbol)
      (generalizedCliffordShiftFieldRoot m) c =
        generalizedCliffordShiftFieldJet (symbol c) m by
    funext n
    exact generalizedCliffordField_linearDerivationLawJet_eq symbol m c n]
  rw [generalizedCliffordShiftFieldJet_algebraicIndependent_iff
    (symbol c) d (F c) m hd (hpower c) hm]
  exact not_ne_iff

/-- An escaping chord of the scalar hypersurface is an unconditional noncommutativity witness for
the corresponding generalized Clifford laws on the rational observable field. -/
theorem generalizedCliffordField_escapingChord_forces_noncommute
    (symbol : V →ₗ[K] Module.End K M) (F : V → K)
    (d : ℕ) (hd : d ≠ 0) (m : M) (hm : m ≠ 0)
    (hpower : ∀ c : V, (symbol c) ^ d = F c • LinearMap.id)
    {v w : V} (hv : F v = 0) (hw : F w = 0)
    {a b : K} (hescape : F (a • v + b • w) ≠ 0) :
    ¬ Function.Commute
      (generalizedCliffordShiftFieldDerivationLaw symbol v)
      (generalizedCliffordShiftFieldDerivationLaw symbol w) := by
  apply hypertranscendental_chord_forces_noncommute
    (generalizedCliffordShiftFieldDerivationLaw symbol)
    (generalizedCliffordShiftFieldRoot m) (v := v) (w := w) (a := a) (b := b)
  · rw [generalizedCliffordField_linearDependenceHorizon_eq_zeroLocus
      symbol F d hd m hm hpower]
    exact hv
  · rw [generalizedCliffordField_linearDependenceHorizon_eq_zeroLocus
      symbol F d hd m hm hpower]
    exact hw
  · have hjet : linearDerivationLawJet
        (generalizedCliffordShiftFieldDerivationLaw symbol)
        (generalizedCliffordShiftFieldRoot m) (a • v + b • w) =
      generalizedCliffordShiftFieldJet (symbol (a • v + b • w)) m := by
      funext n
      exact generalizedCliffordField_linearDerivationLawJet_eq
        symbol m (a • v + b • w) n
    rw [hjet]
    exact (generalizedCliffordShiftFieldJet_algebraicIndependent_iff
      (symbol (a • v + b • w)) d (F (a • v + b • w)) m hd
      (hpower (a • v + b • w)) hm).2 hescape

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.HTGeometry.GeneralizedCliffordPrincipalSymbolLaw
import GaloisForLFunctions.HTGeometry.HolographicCommutatorRank

/-!
# Faithfulness of the generalized Clifford principal symbol

The shift suspension does more than preserve the scalar dependence horizon.  Its Lie bracket has
an exact principal-symbol factorization: the commutator of two one-step laws is the two-step shift
of the commutator of their internal symbols.  Passing first to the symmetric observable algebra
and then to its rational function field loses no information, because both lifts are faithful.

Consequently the complete exterior commutator kernel of the differential-field law is exactly the
kernel of the internal endomorphism-valued commutator symbol.  The scalar hypersurface and the
noncommutative symbol kernel are therefore independent pieces of horizon data.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

universe u v w

variable {K : Type u} {M : Type v} {V : Type w}
  [Field K] [CharZero K]
  [AddCommGroup M] [Module K M]
  [AddCommGroup V] [Module K V]

/-- The degree-one embedding into a symmetric algebra is faithful over a field. -/
theorem symmetricAlgebra_ι_injective :
    Function.Injective (SymmetricAlgebra.ι K M) := by
  intro x y hxy
  apply sub_eq_zero.mp
  by_contra hne
  have hli : LinearIndependent K (fun _ : Unit ↦ x - y) :=
    (linearIndependent_unique_iff).2 hne
  have hAI := symmetricAlgebra_ι_algebraicIndependent_of_linearIndependent
    (fun _ : Unit ↦ x - y) hli
  apply hAI.ne_zero Unit.unit
  simpa only [map_sub, hxy, sub_self]

/-- The symmetric-observable lift preserves Lie brackets exactly. -/
theorem symmetricAlgebraDerivation_commutator
    (T U : Module.End K M) :
    ⁅symmetricAlgebraDerivation T, symmetricAlgebraDerivation U⁆ =
      symmetricAlgebraDerivation ⁅T, U⁆ := by
  ext x
  apply (symmetricPolynomialEquiv (K := K) (M := M)).injective
  simp only [Derivation.commutator_apply, symmetricAlgebraDerivation_equiv_apply,
    map_sub]
  let b := symmetricChosenBasis (K := K) (M := M)
  let e := symmetricPolynomialEquiv (K := K) (M := M)
  let DT := symmetricPolynomialDerivation T
  let DU := symmetricPolynomialDerivation U
  let DC := symmetricPolynomialDerivation ⁅T, U⁆
  have hpoly : ⁅DT, DU⁆ = DC := by
    apply MvPolynomial.derivation_ext
    intro j
    rw [Derivation.commutator_apply]
    have hDU : DU (MvPolynomial.X j) =
        e (SymmetricAlgebra.ι K M (U (b j))) := by
      simp [DU, e, b, symmetricPolynomialDerivation,
        symmetricPolynomialEquiv, symmetricChosenBasis]
    have hDT : DT (MvPolynomial.X j) =
        e (SymmetricAlgebra.ι K M (T (b j))) := by
      simp [DT, e, b, symmetricPolynomialDerivation,
        symmetricPolynomialEquiv, symmetricChosenBasis]
    rw [hDU, hDT]
    rw [symmetricPolynomialDerivation_on_ι,
      symmetricPolynomialDerivation_on_ι]
    simp [DC, symmetricPolynomialDerivation, e, b,
      LieRing.of_associative_ring_bracket, Module.End.mul_apply]
  exact DFunLike.congr_fun hpoly (e x)

/-- Lift an arbitrary graded state action to the rational observable field. -/
def generalizedCliffordObservableFieldDerivation
    (T : Module.End K (ℕ → M)) :
    Derivation K (GeneralizedCliffordShiftField K M)
      (GeneralizedCliffordShiftField K M) :=
  fractionRingDerivation
    ((Algebra.linearMap (SymmetricAlgebra K (ℕ → M))
      (GeneralizedCliffordShiftField K M)).compDer
        (symmetricAlgebraDerivation T))

/-- The arbitrary state-action lift agrees with its action on polynomial observables. -/
theorem generalizedCliffordObservableFieldDerivation_embedding
    (T : Module.End K (ℕ → M)) (x : SymmetricAlgebra K (ℕ → M)) :
    generalizedCliffordObservableFieldDerivation T
        (generalizedCliffordShiftFieldEmbedding (K := K) (M := M) x) =
      generalizedCliffordShiftFieldEmbedding (K := K) (M := M)
        (symmetricAlgebraDerivation T x) := by
  rw [generalizedCliffordObservableFieldDerivation,
    generalizedCliffordShiftFieldEmbedding_apply,
    fractionRingDerivation_algebraMap]
  rfl

/-- The existing one-step Clifford law is the arbitrary observable lift of its state action. -/
theorem generalizedCliffordShiftFieldDerivation_eq_observableLift
    (A : Module.End K M) :
    generalizedCliffordShiftFieldDerivation A =
      generalizedCliffordObservableFieldDerivation
        (generalizedCliffordShiftOperator A) := rfl

theorem generalizedCliffordObservableFieldDerivation_add
    (T U : Module.End K (ℕ → M)) :
    generalizedCliffordObservableFieldDerivation (T + U) =
      generalizedCliffordObservableFieldDerivation T +
        generalizedCliffordObservableFieldDerivation U := by
  apply fractionRing_derivation_ext
    (A := SymmetricAlgebra K (ℕ → M))
  intro x
  change generalizedCliffordObservableFieldDerivation (T + U)
      (generalizedCliffordShiftFieldEmbedding (K := K) (M := M) x) =
    generalizedCliffordObservableFieldDerivation T
        (generalizedCliffordShiftFieldEmbedding (K := K) (M := M) x) +
      generalizedCliffordObservableFieldDerivation U
        (generalizedCliffordShiftFieldEmbedding (K := K) (M := M) x)
  rw [generalizedCliffordObservableFieldDerivation_embedding,
    generalizedCliffordObservableFieldDerivation_embedding,
    generalizedCliffordObservableFieldDerivation_embedding,
    symmetricAlgebraDerivation_add, Derivation.add_apply, map_add]

theorem generalizedCliffordObservableFieldDerivation_smul
    (c : K) (T : Module.End K (ℕ → M)) :
    generalizedCliffordObservableFieldDerivation (c • T) =
      c • generalizedCliffordObservableFieldDerivation T := by
  apply fractionRing_derivation_ext
    (A := SymmetricAlgebra K (ℕ → M))
  intro x
  change generalizedCliffordObservableFieldDerivation (c • T)
      (generalizedCliffordShiftFieldEmbedding (K := K) (M := M) x) =
    c • generalizedCliffordObservableFieldDerivation T
      (generalizedCliffordShiftFieldEmbedding (K := K) (M := M) x)
  rw [generalizedCliffordObservableFieldDerivation_embedding,
    generalizedCliffordObservableFieldDerivation_embedding,
    symmetricAlgebraDerivation_smul, Derivation.smul_apply, map_smul]

/-- Arbitrary linear state actions lift linearly to the rational observable field. -/
def generalizedCliffordObservableFieldDerivationLinearMap :
    Module.End K (ℕ → M) →ₗ[K]
      Derivation K (GeneralizedCliffordShiftField K M)
        (GeneralizedCliffordShiftField K M) where
  toFun := generalizedCliffordObservableFieldDerivation
  map_add' := generalizedCliffordObservableFieldDerivation_add
  map_smul' := generalizedCliffordObservableFieldDerivation_smul

@[simp]
theorem generalizedCliffordObservableFieldDerivation_zero :
    generalizedCliffordObservableFieldDerivation
        (0 : Module.End K (ℕ → M)) = 0 := by
  exact (generalizedCliffordObservableFieldDerivationLinearMap
    (K := K) (M := M)).map_zero

/-- The rational observable lift preserves Lie brackets. -/
theorem generalizedCliffordObservableFieldDerivation_commutator
    (T U : Module.End K (ℕ → M)) :
    ⁅generalizedCliffordObservableFieldDerivation T,
        generalizedCliffordObservableFieldDerivation U⁆ =
      generalizedCliffordObservableFieldDerivation ⁅T, U⁆ := by
  apply fractionRing_derivation_ext
    (A := SymmetricAlgebra K (ℕ → M))
  intro x
  change ⁅generalizedCliffordObservableFieldDerivation T,
      generalizedCliffordObservableFieldDerivation U⁆
        (generalizedCliffordShiftFieldEmbedding (K := K) (M := M) x) =
    generalizedCliffordObservableFieldDerivation ⁅T, U⁆
      (generalizedCliffordShiftFieldEmbedding (K := K) (M := M) x)
  rw [Derivation.commutator_apply,
    generalizedCliffordObservableFieldDerivation_embedding,
    generalizedCliffordObservableFieldDerivation_embedding,
    generalizedCliffordObservableFieldDerivation_embedding,
    generalizedCliffordObservableFieldDerivation_embedding,
    generalizedCliffordObservableFieldDerivation_embedding]
  have hstate := DFunLike.congr_fun
    (symmetricAlgebraDerivation_commutator T U) x
  simpa only [Derivation.commutator_apply, map_sub] using
    congrArg (generalizedCliffordShiftFieldEmbedding (K := K) (M := M)) hstate

/-- The rational observable lift is a Lie homomorphism. -/
def generalizedCliffordObservableFieldLieHom :
    Module.End K (ℕ → M) →ₗ⁅K⁆
      Derivation K (GeneralizedCliffordShiftField K M)
        (GeneralizedCliffordShiftField K M) where
  toFun := generalizedCliffordObservableFieldDerivation
  map_add' := generalizedCliffordObservableFieldDerivation_add
  map_smul' := generalizedCliffordObservableFieldDerivation_smul
  map_lie' := fun T U =>
    (generalizedCliffordObservableFieldDerivation_commutator T U).symm

/-- No state-action information is lost by passage to the rational observable field. -/
theorem generalizedCliffordObservableFieldLieHom_injective :
    Function.Injective
      (generalizedCliffordObservableFieldLieHom (K := K) (M := M)) := by
  intro T U hTU
  change generalizedCliffordObservableFieldDerivation T =
    generalizedCliffordObservableFieldDerivation U at hTU
  apply LinearMap.ext
  intro f
  apply sub_eq_zero.mp
  have hfield : generalizedCliffordObservableFieldDerivation T
      (generalizedCliffordShiftFieldEmbedding (K := K) (M := M)
        (SymmetricAlgebra.ι K (ℕ → M) f)) =
    generalizedCliffordObservableFieldDerivation U
      (generalizedCliffordShiftFieldEmbedding (K := K) (M := M)
        (SymmetricAlgebra.ι K (ℕ → M) f)) :=
    DFunLike.congr_fun hTU _
  rw [generalizedCliffordObservableFieldDerivation_embedding,
    generalizedCliffordObservableFieldDerivation_embedding,
    symmetricAlgebraDerivation_ι, symmetricAlgebraDerivation_ι] at hfield
  have hiota : SymmetricAlgebra.ι K (ℕ → M) (T f) =
      SymmetricAlgebra.ι K (ℕ → M) (U f) :=
    generalizedCliffordShiftFieldEmbedding_injective hfield
  exact sub_eq_zero.mpr (symmetricAlgebra_ι_injective hiota)

/-- The alternating internal commutator of an endomorphism-valued symbol pencil. -/
def endomorphismCommutatorAlternatingMap
    (symbol : V →ₗ[K] Module.End K M) :
    V [⋀^Fin 2]→ₗ[K] Module.End K M where
  toFun f := ⁅symbol (f 0), symbol (f 1)⁆
  map_update_add' f i x y := by
    fin_cases i <;> simp
  map_update_smul' f i c x := by
    fin_cases i <;> simp
  map_eq_zero_of_eq' f i j hij hne := by
    fin_cases i <;> fin_cases j <;> simp_all

/-- The internal commutator principal symbol on the second exterior law space. -/
def endomorphismCommutatorMap
    (symbol : V →ₗ[K] Module.End K M) :
    (⋀[K]^2 V) →ₗ[K] Module.End K M :=
  exteriorPower.alternatingMapLinearEquiv
    (endomorphismCommutatorAlternatingMap symbol)

@[simp]
theorem endomorphismCommutatorMap_wedge
    (symbol : V →ₗ[K] Module.End K M) (v w : V) :
    endomorphismCommutatorMap symbol (exteriorPower.ιMulti K 2 ![v, w]) =
      ⁅symbol v, symbol w⁆ := by
  simp [endomorphismCommutatorMap, endomorphismCommutatorAlternatingMap]

/-- Apply one internal operator after two unilateral grade shifts. -/
def generalizedCliffordDoubleShiftOperator (C : Module.End K M) :
    Module.End K (ℕ → M) :=
  periodicUnilateralShift.comp (generalizedCliffordShiftOperator C)

/-- The commutator of one-step suspensions is exactly the double shift of the internal
commutator. -/
theorem generalizedCliffordShiftOperator_commutator
    (A B : Module.End K M) :
    ⁅generalizedCliffordShiftOperator A,
        generalizedCliffordShiftOperator B⁆ =
      generalizedCliffordDoubleShiftOperator ⁅A, B⁆ := by
  apply LinearMap.ext
  intro f
  funext n
  cases n with
  | zero =>
      simp [LieRing.of_associative_ring_bracket,
        generalizedCliffordShiftOperator, generalizedCliffordDoubleShiftOperator,
        periodicUnilateralShift, periodicPointwiseEnd, Module.End.mul_apply]
  | succ n =>
      cases n with
      | zero =>
          simp [LieRing.of_associative_ring_bracket,
            generalizedCliffordShiftOperator, generalizedCliffordDoubleShiftOperator,
            periodicUnilateralShift, periodicPointwiseEnd, Module.End.mul_apply]
      | succ n =>
          simp [LieRing.of_associative_ring_bracket,
            generalizedCliffordShiftOperator, generalizedCliffordDoubleShiftOperator,
            periodicUnilateralShift, periodicPointwiseEnd, Module.End.mul_apply]

/-- Double shift depends linearly on its internal principal symbol. -/
def generalizedCliffordDoubleShiftOperatorLinearMap :
    Module.End K M →ₗ[K] Module.End K (ℕ → M) where
  toFun := generalizedCliffordDoubleShiftOperator
  map_add' A B := by
    apply LinearMap.ext
    intro f
    funext n
    cases n with
    | zero =>
        simp [generalizedCliffordDoubleShiftOperator,
          generalizedCliffordShiftOperator, periodicUnilateralShift,
          periodicPointwiseEnd]
    | succ n =>
        cases n <;> simp [generalizedCliffordDoubleShiftOperator,
          generalizedCliffordShiftOperator, periodicUnilateralShift,
          periodicPointwiseEnd]
  map_smul' c A := by
    apply LinearMap.ext
    intro f
    funext n
    cases n with
    | zero =>
        simp [generalizedCliffordDoubleShiftOperator,
          generalizedCliffordShiftOperator, periodicUnilateralShift,
          periodicPointwiseEnd]
    | succ n =>
        cases n <;> simp [generalizedCliffordDoubleShiftOperator,
          generalizedCliffordShiftOperator, periodicUnilateralShift,
          periodicPointwiseEnd]

@[simp]
theorem generalizedCliffordDoubleShiftOperator_zero :
    generalizedCliffordDoubleShiftOperator (0 : Module.End K M) = 0 := by
  exact (generalizedCliffordDoubleShiftOperatorLinearMap
    (K := K) (M := M)).map_zero

/-- Two unilateral shifts do not erase any internal endomorphism. -/
theorem generalizedCliffordDoubleShiftOperatorLinearMap_injective :
    Function.Injective
      (generalizedCliffordDoubleShiftOperatorLinearMap (K := K) (M := M)) := by
  intro A B hAB
  apply LinearMap.ext
  intro m
  have hlevel := LinearMap.congr_fun hAB (periodicLevel 0 m)
  have hcoord := congrFun hlevel 2
  simpa [generalizedCliffordDoubleShiftOperator,
    generalizedCliffordShiftOperator, periodicUnilateralShift,
    periodicPointwiseEnd, periodicLevel] using hcoord

/-- **General principal-symbol factorization.**  The exterior commutator law on the rational
observable field factors exactly through the internal endomorphism commutator, followed by a
faithful double shift and a faithful observable-field lift. -/
theorem generalizedCliffordField_derivationCommutatorMap_factorization
    (symbol : V →ₗ[K] Module.End K M) :
    derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw symbol) =
      (generalizedCliffordObservableFieldDerivationLinearMap (K := K) (M := M)).comp
        ((generalizedCliffordDoubleShiftOperatorLinearMap (K := K) (M := M)).comp
          (endomorphismCommutatorMap symbol)) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro f
  have hf : f = ![f 0, f 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hf]
  rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply]
  rw [derivationCommutatorMap_wedge,
    LinearMap.comp_apply, LinearMap.comp_apply,
    endomorphismCommutatorMap_wedge,
    generalizedCliffordShiftFieldDerivationLaw_apply,
    generalizedCliffordShiftFieldDerivationLaw_apply,
    generalizedCliffordShiftFieldDerivation_eq_observableLift,
    generalizedCliffordShiftFieldDerivation_eq_observableLift,
    generalizedCliffordObservableFieldDerivation_commutator,
    generalizedCliffordShiftOperator_commutator]
  rfl

/-- **General principal-symbol kernel theorem.**  Shift suspension and passage to the rational
observable field preserve the entire exterior commutator kernel exactly. -/
theorem generalizedCliffordField_derivationCommutatorMap_ker_eq
    (symbol : V →ₗ[K] Module.End K M) :
    (derivationCommutatorMap
      (generalizedCliffordShiftFieldDerivationLaw symbol)).ker =
        (endomorphismCommutatorMap symbol).ker := by
  ext z
  simp only [LinearMap.mem_ker]
  rw [generalizedCliffordField_derivationCommutatorMap_factorization,
    LinearMap.comp_apply, LinearMap.comp_apply]
  constructor
  · intro h
    have hshift : generalizedCliffordDoubleShiftOperatorLinearMap
        (endomorphismCommutatorMap symbol z) = 0 := by
      apply generalizedCliffordObservableFieldLieHom_injective
      simpa [generalizedCliffordObservableFieldLieHom,
        generalizedCliffordObservableFieldDerivationLinearMap] using h
    apply generalizedCliffordDoubleShiftOperatorLinearMap_injective
    simpa using hshift
  · intro h
    rw [h]
    simp

/-- The differential-field law has maximal exterior commutator rank exactly when its internal
principal-symbol representation does. -/
theorem generalizedCliffordField_derivationCommutatorMap_injective_iff
    (symbol : V →ₗ[K] Module.End K M) :
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw symbol)) ↔
      Function.Injective (endomorphismCommutatorMap symbol) := by
  rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot,
    generalizedCliffordField_derivationCommutatorMap_ker_eq]

/-- Pairwise commutativity is reflected, not only preserved, by the generalized-Clifford field
construction. -/
theorem generalizedCliffordShiftFieldDerivation_commute_iff
    (A B : Module.End K M) :
    Function.Commute
        (generalizedCliffordShiftFieldDerivation A)
        (generalizedCliffordShiftFieldDerivation B) ↔
      Function.Commute A B := by
  rw [derivation_commute_iff_commutator_eq_zero]
  constructor
  · intro h
    have hlift : generalizedCliffordObservableFieldDerivation
        (generalizedCliffordDoubleShiftOperator ⁅A, B⁆) = 0 := by
      simpa [generalizedCliffordShiftFieldDerivation_eq_observableLift,
        generalizedCliffordObservableFieldDerivation_commutator,
        generalizedCliffordShiftOperator_commutator] using h
    have hshift : generalizedCliffordDoubleShiftOperator ⁅A, B⁆ = 0 := by
      apply generalizedCliffordObservableFieldLieHom_injective
      simpa [generalizedCliffordObservableFieldLieHom,
        generalizedCliffordObservableFieldDerivationLinearMap] using hlift
    have hcomm : ⁅A, B⁆ = 0 := by
      apply generalizedCliffordDoubleShiftOperatorLinearMap_injective
      simpa [generalizedCliffordDoubleShiftOperatorLinearMap] using hshift
    intro m
    have hm := LinearMap.congr_fun hcomm m
    exact sub_eq_zero.mp (by
      simpa [LieRing.of_associative_ring_bracket, Module.End.mul_apply] using hm)
  · intro h
    have hcomm : ⁅A, B⁆ = 0 := by
      ext m
      simpa [LieRing.of_associative_ring_bracket, Module.End.mul_apply]
        using sub_eq_zero.mpr (h m)
    rw [generalizedCliffordShiftFieldDerivation_eq_observableLift,
      generalizedCliffordShiftFieldDerivation_eq_observableLift,
      generalizedCliffordObservableFieldDerivation_commutator,
      generalizedCliffordShiftOperator_commutator, hcomm]
    rfl

end

end GaloisForLFunctions.HTGeometry

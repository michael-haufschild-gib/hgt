import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticGlobalField
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticInfinityResidue
import GaloisForLFunctions.HTGeometry.DiscreteValuedCompletion
import GaloisForLFunctions.HTGeometry.DedekindResidueFieldAtPlace
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Local fields and full adeles of the finite-field elliptic curve

The completions are taken at the actual height-one primes of the affine integral
closure and at the proved degree-one infinity valuation. Their compact integer
rings give locally compact finite and full adele rings.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

open IsDedekindDomain HTGeometry HTGeometry.DiscreteValuedCompletion
open scoped WithZero WithZeroMulInt

noncomputable section

/-- The completion at the unique omitted infinity place. -/
abbrev InfinityCompletion := infinityValuation.Completion

instance infinityValuation_integer_residueFinite :
    Finite (IsLocalRing.ResidueField infinityValuation.integer) :=
  (inferInstance : Finite InfinityResidueField)

instance finiteValuation_integer_residueFinite (v : FinitePlace) :
    Finite (IsLocalRing.ResidueField (v.valuation K).integer) :=
  finite_residueField_valuationSubring K v

instance infinityCompletion_localField : IsNonarchimedeanLocalField InfinityCompletion :=
  valuationCompletionLocalField infinityValuation

/-- The completed infinity residue field is still the original constant field. -/
def infinityCompletionResidueEquiv :
    IsLocalRing.ResidueField (Valued.v : Valuation InfinityCompletion ℤᵐ⁰).integer ≃+*
      Constants :=
  (valuationCompletionResidueEquiv infinityValuation).symm.trans infinityResidueEquiv.symm

theorem infinityCompletionResidue_card :
    Nat.card (IsLocalRing.ResidueField
      (Valued.v : Valuation InfinityCompletion ℤᵐ⁰).integer) = 3 := by
  rw [Nat.card_congr infinityCompletionResidueEquiv.toEquiv]
  simpa only [Nat.card_eq_fintype_card] using ZMod.card 3

instance finiteCompletion_locallyCompact (v : FinitePlace) :
    LocallyCompactSpace (v.adicCompletion K) :=
  (HeightOneSpectrum.adicCompletion.uniformEquiv K v).toHomeomorph.isOpenEmbedding.locallyCompactSpace

instance finiteCompletion_valuativeRel (v : FinitePlace) :
    ValuativeRel (v.adicCompletion K) :=
  .ofValuation (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

instance finiteCompletion_valuationCompatible (v : FinitePlace) :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).Compatible := .ofValuation _

instance finiteCompletion_localField (v : FinitePlace) :
    IsNonarchimedeanLocalField (v.adicCompletion K) :=
  ABHN.isNonarchimedeanLocalField_of_valued_of_locallyCompact (v.adicCompletion K) ℤᵐ⁰

/-- The adic-completion wrapper preserves its integer ring. -/
def finiteCompletionIntegerEquiv (v : FinitePlace) :
    v.adicCompletionIntegers K ≃+*
      (Valued.v : Valuation (v.valuation K).Completion ℤᵐ⁰).integer where
  toFun x := ⟨x.1.toCompletion, x.2⟩
  invFun x := ⟨HeightOneSpectrum.adicCompletion.ofCompletion x.1, x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def finiteCompletionIntegerHomeomorph (v : FinitePlace) :
    v.adicCompletionIntegers K ≃ₜ
      (Valued.v : Valuation (v.valuation K).Completion ℤᵐ⁰).integer where
  toEquiv := (finiteCompletionIntegerEquiv v).toEquiv
  continuous_toFun :=
    ((HeightOneSpectrum.adicCompletion.continuous_toCompletion K v).comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v).comp
      continuous_subtype_val).subtype_mk _

instance finiteCompletionInteger_compact (v : FinitePlace) :
    CompactSpace (v.adicCompletionIntegers K) :=
  Homeomorph.compactSpace (finiteCompletionIntegerHomeomorph v).symm

/-- Completion preserves the actual prime residue ring, not only its cardinality. -/
def finiteCompletionResidueEquiv (v : FinitePlace) :
    IsLocalRing.ResidueField (v.adicCompletionIntegers K) ≃+*
      (RingOfIntegers ⧸ v.asIdeal) :=
  (IsLocalRing.ResidueField.mapEquiv (finiteCompletionIntegerEquiv v)).trans
    ((valuationCompletionResidueEquiv (v.valuation K)).symm.trans
      (residueFieldAtPlaceEquiv K v))

instance finiteCompletionInteger_open :
    Fact (∀ v : FinitePlace, IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
  ⟨fun _ => Valued.isOpen_valuationSubring _⟩

instance finiteAdeles_locallyCompact : LocallyCompactSpace FiniteAdeles := by
  unfold FiniteAdeles IsDedekindDomain.FiniteAdeleRing
  exact RestrictedProduct.locallyCompactSpace_of_addGroup
    (fun v : FinitePlace => v.adicCompletion K)
    (Filter.Eventually.of_forall fun v =>
      isCompact_iff_compactSpace.mpr
        (inferInstance : CompactSpace (v.adicCompletionIntegers K)))

/-- The full adele ring, including the actual infinity completion. -/
abbrev Adeles := FiniteAdeles × InfinityCompletion

instance adeles_locallyCompact : LocallyCompactSpace Adeles := inferInstance

/-- The field embedding at infinity is the dense completion map. -/
def infinityEmbedding : K →+* InfinityCompletion :=
  UniformSpace.Completion.coeRingHom.comp (WithVal.equiv infinityValuation).symm.toRingHom

@[simp] lemma infinityEmbedding_valuation (a : K) :
    Valued.v (infinityEmbedding a) = infinityValuation a := by
  exact Valued.valuedCompletion_apply (WithVal.toVal infinityValuation a)

/-- The diagonal map into all actual completions. -/
def adeleEmbedding : K →+* Adeles := finiteAdeleEmbedding.prod infinityEmbedding

theorem adeleEmbedding_injective : Function.Injective adeleEmbedding :=
  adeleEmbedding.injective

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase


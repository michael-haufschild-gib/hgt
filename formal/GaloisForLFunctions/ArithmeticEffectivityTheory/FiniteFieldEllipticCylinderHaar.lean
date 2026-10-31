import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticFiniteCylinders
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticGapTopology
import GaloisForLFunctions.HTGeometry.DiscreteValuationHaar
import GaloisForLFunctions.HTGeometry.CompactAbelianHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Exact local products for actual elliptic adelic Haar

On each open finite-place cylinder, coordinate assembly pulls ambient Haar
back to normalized local Haar times the compact integral-tail probability.
Both measures are additive Haar and give the full integral box mass one.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open MeasureTheory MeasureTheory.Measure Set
open HTGeometry.DiscreteValuationHaar
open scoped WithZero WithZeroMulInt ENNReal NNReal
noncomputable section

private theorem topological_measurable_add {A : Type*} [AddGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] :
    MeasurableAdd A := ContinuousAdd.measurableAdd

private theorem product_measurable_add {A B : Type*} [Add A] [Add B]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableAdd A] [MeasurableAdd B] :
    MeasurableAdd (A × B) where
  measurable_const_add c := (measurable_fst.const_add c.1).prodMk
    (measurable_snd.const_add c.2)
  measurable_add_const c := (measurable_fst.add_const c.1).prodMk
    (measurable_snd.add_const c.2)

local instance (v : FinitePlace) : MeasurableSpace (v.adicCompletion K) := borel _
local instance (v : FinitePlace) : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
local instance (v : FinitePlace) : CompactSpace (Integer (v.adicCompletion K)) :=
  finiteCompletionInteger_compact v
local instance (v : FinitePlace) : SecondCountableTopology (v.adicCompletionIntegers K) :=
  (Valued.isOpen_valuationSubring (v.adicCompletion K)).isOpenEmbedding_subtypeVal.isEmbedding.secondCountableTopology
local instance (v : FinitePlace) :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsNontrivial := inferInstance
local instance (v : FinitePlace) : IsTopologicalAddGroup (v.adicCompletionIntegers K) :=
  Topology.IsInducing.subtypeVal.topologicalAddGroup
    (v.adicCompletionIntegers K).subtype.toAddMonoidHom
local instance (S : Finset FinitePlace) :
    IsTopologicalAddGroup ((v : {v : FinitePlace // v ∉ S}) → v.1.adicCompletionIntegers K) :=
  Pi.topologicalAddGroup
private abbrev actualFieldTopAdd (v : FinitePlace) : IsTopologicalAddGroup (v.adicCompletion K) := by
  letI : IsTopologicalRing (v.adicCompletion K) := Valued.instIsTopologicalRing
  exact IsTopologicalRing.to_topologicalAddGroup
private abbrev actualIntegerAddGroup (v : FinitePlace) : AddCommGroup (v.adicCompletionIntegers K) :=
  inferInstance
private abbrev actualIntegerAdd (v : FinitePlace) : Add (v.adicCompletionIntegers K) :=
  inferInstance
attribute [local instance] actualFieldTopAdd actualIntegerAddGroup actualIntegerAdd

local instance (v : FinitePlace) : SigmaCompactSpace (v.adicCompletion K) := by
  letI := finiteCompletion_secondCountable v
  letI := finiteCompletion_locallyCompact v
  exact sigmaCompactSpace_of_locallyCompact_secondCountable
local instance (v : FinitePlace) : (normalizedHaar (v.adicCompletion K)).IsAddHaarMeasure :=
  normalizedHaar_isAddHaar (v.adicCompletion K)
local instance (v : FinitePlace) : SigmaFinite (normalizedHaar (v.adicCompletion K)) := inferInstance
local instance (S : Finset FinitePlace) : IsTopologicalAddGroup (FiniteCylinderFields S) := by
  letI (v : S) : IsTopologicalAddGroup (v.1.adicCompletion K) := actualFieldTopAdd v.1
  exact Pi.topologicalAddGroup
local instance (v : FinitePlace) : MeasurableAdd (v.adicCompletionIntegers K) :=
  topological_measurable_add
local instance (S : Finset FinitePlace) : MeasurableAdd (FiniteCylinderFields S) := by
  letI (v : S) : MeasurableAdd (v.1.adicCompletion K) := ContinuousAdd.measurableAdd
  exact Pi.measurableAdd
local instance (S : Finset FinitePlace) : MeasurableAdd (FiniteCylinderTail S) := by
  letI (v : {v : FinitePlace // v ∉ S}) : Add (v.1.adicCompletionIntegers K) :=
    actualIntegerAdd v.1
  letI (v : {v : FinitePlace // v ∉ S}) : MeasurableAdd (v.1.adicCompletionIntegers K) :=
    inferInstance
  exact Pi.measurableAdd
local instance : MeasurableSpace InfinityCompletion := borel _
local instance : BorelSpace InfinityCompletion := ⟨rfl⟩
local instance : MeasurableAdd InfinityCompletion := ContinuousAdd.measurableAdd
local instance : MeasurableAdd Adeles := ContinuousAdd.measurableAdd

abbrev EllipticCylinderCoordinates (S : Finset FinitePlace) :=
  (FiniteCylinderFields S × FiniteCylinderTail S) × InfinityCompletion

local instance (S : Finset FinitePlace) :
    MeasurableAdd (FiniteCylinderFields S × FiniteCylinderTail S) := product_measurable_add
local instance (S : Finset FinitePlace) : MeasurableAdd (EllipticCylinderCoordinates S) :=
  product_measurable_add

/-- Assemble the finite cylinder and the unrestricted infinity completion. -/
def ellipticCylinderAssembly (S : Finset FinitePlace) : EllipticCylinderCoordinates S →+ Adeles where
  toFun x := ((finiteCylinderAssembly S x.1 : FiniteAdeles), x.2)
  map_zero' := Prod.ext (congrArg (Subtype.val : finiteAdeleCylinder S → FiniteAdeles)
    ((finiteCylinderAssembly S).map_zero)) rfl
  map_add' x y := Prod.ext (congrArg (Subtype.val : finiteAdeleCylinder S → FiniteAdeles)
    ((finiteCylinderAssembly S).map_add x.1 y.1)) rfl

/-- The actual coordinate assembly embeds onto an open adelic subgroup. -/
theorem ellipticCylinderAssembly_isOpenEmbedding (S : Finset FinitePlace) :
    Topology.IsOpenEmbedding (ellipticCylinderAssembly S) := by
  have hf : Topology.IsOpenEmbedding (fun x : FiniteCylinderFields S × FiniteCylinderTail S =>
      (finiteCylinderAssembly S x : FiniteAdeles)) :=
    (finiteAdeleCylinder_isOpen S).isOpenEmbedding_subtypeVal.comp
      (finiteAdeleCylinderHomeomorph S).isOpenEmbedding
  exact hf.prodMap (Homeomorph.refl InfinityCompletion).isOpenEmbedding

/-- The common compact normalization box in cylinder coordinates. -/
def ellipticCylinderIntegralBox (S : Finset FinitePlace) : Set (EllipticCylinderCoordinates S) :=
  ((Set.univ.pi fun v : S => (v.1.adicCompletionIntegers K : Set (v.1.adicCompletion K))) ×ˢ
    Set.univ) ×ˢ ((Valued.v : Valuation InfinityCompletion ℤᵐ⁰).integer : Set InfinityCompletion)

/-- Local Haar factors and the probability of the compact integral tail. -/
def ellipticCylinderProductHaar (S : Finset FinitePlace) : Measure (EllipticCylinderCoordinates S) :=
  ((Measure.pi fun v : S => normalizedHaar (v.1.adicCompletion K)).prod
    (CompactAbelian.haarProb (FiniteCylinderTail S))).prod (normalizedHaar InfinityCompletion)

private instance cylinderFieldsHaar_isAddHaar (S : Finset FinitePlace) :
    (Measure.pi fun v : S => normalizedHaar (v.1.adicCompletion K)).IsAddHaarMeasure := by
  letI (v : S) : (normalizedHaar (v.1.adicCompletion K)).IsAddHaarMeasure :=
    normalizedHaar_isAddHaar (v.1.adicCompletion K)
  letI (v : S) : SecondCountableTopology (v.1.adicCompletion K) :=
    finiteCompletion_secondCountable v.1
  letI (v : S) : LocallyCompactSpace (v.1.adicCompletion K) :=
    finiteCompletion_locallyCompact v.1
  letI (v : S) : SigmaCompactSpace (v.1.adicCompletion K) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  letI (v : S) : SigmaFinite (normalizedHaar (v.1.adicCompletion K)) := inferInstance
  exact Measure.pi.isAddHaarMeasure _

instance ellipticCylinderProductHaar_isAddHaar (S : Finset FinitePlace) :
    (ellipticCylinderProductHaar S).IsAddHaarMeasure := by
  letI (v : {v : FinitePlace // v ∉ S}) : AddCommGroup (v.1.adicCompletionIntegers K) :=
    actualIntegerAddGroup v.1
  letI (v : {v : FinitePlace // v ∉ S}) : Add (v.1.adicCompletionIntegers K) :=
    actualIntegerAdd v.1
  letI (v : S) : SigmaFinite (normalizedHaar (v.1.adicCompletion K)) := inferInstance
  letI : ((Measure.pi fun v : S => normalizedHaar (v.1.adicCompletion K)).prod
      (CompactAbelian.haarProb (FiniteCylinderTail S))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  exact Measure.prod.instIsAddHaarMeasure _ _

/-- Pullback of the actual ambient Haar measure along open cylinder assembly. -/
def ellipticCylinderAmbientHaar (S : Finset FinitePlace) : Measure (EllipticCylinderCoordinates S) :=
  adeleHaar.comap (ellipticCylinderAssembly S)

instance ellipticCylinderAmbientHaar_isAddHaar (S : Finset FinitePlace) :
    (ellipticCylinderAmbientHaar S).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.comap (mH := inferInstance) adeleHaar
    (ellipticCylinderAssembly_isOpenEmbedding S)

private theorem assembly_preimage_integral (S : Finset FinitePlace) :
    ellipticCylinderAssembly S ⁻¹' integralAdeles = ellipticCylinderIntegralBox S := by
  classical
  ext x
  change ((∀ v : FinitePlace, (finiteCylinderAssembly S x.1 : FiniteAdeles) v ∈
      v.adicCompletionIntegers K) ∧ Valued.v x.2 ≤ 1) ↔
    ((∀ v : S, v ∈ Set.univ → x.1.1 v ∈ v.1.adicCompletionIntegers K) ∧
      x.1.2 ∈ Set.univ) ∧ Valued.v x.2 ≤ 1
  constructor
  · rintro ⟨hf, hi⟩
    refine ⟨⟨fun v _ => ?_, Set.mem_univ _⟩, hi⟩
    simpa only [finiteCylinderAssembly_apply_mem] using hf v.1
  · rintro ⟨⟨hf, _⟩, hi⟩
    refine ⟨fun v => ?_, hi⟩
    by_cases hv : v ∈ S
    · have he := finiteCylinderAssembly_apply_mem S x.1 ⟨v, hv⟩
      rw [he]
      exact hf ⟨v, hv⟩ (Set.mem_univ _)
    · have he := finiteCylinderAssembly_apply_notMem S x.1 ⟨v, hv⟩
      rw [he]
      exact (x.1.2 ⟨v, hv⟩).property

private theorem assembly_image_integralBox (S : Finset FinitePlace) :
    ellipticCylinderAssembly S '' ellipticCylinderIntegralBox S = integralAdeles := by
  rw [← assembly_preimage_integral]
  apply Set.image_preimage_eq_of_subset
  intro a ha
  let b : finiteAdeleCylinder S := ⟨a.1, fun v _ => ha.1 v⟩
  refine ⟨((finiteAdeleCylinderEquiv S).symm b, a.2), ?_⟩
  apply Prod.ext
  · exact congrArg (Subtype.val : finiteAdeleCylinder S → FiniteAdeles)
      ((finiteAdeleCylinderEquiv S).apply_symm_apply b)
  · rfl

/-- The product measure gives the full integral box mass one. -/
theorem ellipticCylinderProductHaar_integralBox (S : Finset FinitePlace) :
    ellipticCylinderProductHaar S (ellipticCylinderIntegralBox S) = 1 := by
  classical
  letI (v : S) : SigmaFinite (normalizedHaar (v.1.adicCompletion K)) := inferInstance
  have hf (v : S) : normalizedHaar (v.1.adicCompletion K)
      (v.1.adicCompletionIntegers K : Set (v.1.adicCompletion K)) = 1 :=
    normalizedHaar_integer (v.1.adicCompletion K)
  rw [ellipticCylinderProductHaar, ellipticCylinderIntegralBox,
    Measure.prod_prod, Measure.prod_prod, Measure.pi_pi]
  simp only [hf, normalizedHaar_integer, measure_univ, Finset.prod_const_one, mul_one]

/-- Pullback of ambient normalized Haar has the same normalization. -/
theorem ellipticCylinderAmbientHaar_integralBox (S : Finset FinitePlace) :
    ellipticCylinderAmbientHaar S (ellipticCylinderIntegralBox S) = 1 := by
  rw [ellipticCylinderAmbientHaar,
    (ellipticCylinderAssembly_isOpenEmbedding S).measurableEmbedding.comap_apply,
    assembly_image_integralBox, adeleHaar_integralAdeles]

private theorem haar_eq_of_normalized_set {G : Type*}
    [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ ν : Measure G) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (s : Set G) (hμ : μ s = 1) (hν : ν s = 1) : μ = ν := by
  have h := Measure.isAddLeftInvariant_eq_smul μ ν
  have hc : ((Measure.addHaarScalarFactor μ ν : ℝ≥0) : ℝ≥0∞) = 1 := by
    have he := congrArg (fun ρ : Measure G => ρ s) h
    rw [hμ, Measure.smul_apply, hν] at he
    simpa only [ENNReal.smul_def, smul_eq_mul, mul_one] using he.symm
  have hc' : Measure.addHaarScalarFactor μ ν = 1 := ENNReal.coe_eq_one.mp hc
  rwa [hc', one_smul] at h

/-- Actual adelic Haar is exactly the normalized local product in each finite cylinder. -/
theorem ellipticCylinderAmbientHaar_eq_product (S : Finset FinitePlace) :
    ellipticCylinderAmbientHaar S = ellipticCylinderProductHaar S :=
  haar_eq_of_normalized_set _ _ (ellipticCylinderIntegralBox S)
    (ellipticCylinderAmbientHaar_integralBox S) (ellipticCylinderProductHaar_integralBox S)

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticCylinderAssembly_isOpenEmbedding
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticCylinderAmbientHaar_eq_product

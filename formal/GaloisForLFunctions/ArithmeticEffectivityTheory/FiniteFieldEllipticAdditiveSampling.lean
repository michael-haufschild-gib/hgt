import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticFiniteCylinders
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticGapTopology
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticAdditivePeriodization
open MeasureTheory Set


/-!
# Second countability and additive sampling of the actual elliptic adeles

Countably many open finite cylinders give second countability. Scalar
periodization identifies domain Haar probability times function-field
counting measure with ambient adelic Haar under addition.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
noncomputable section

local instance topologyIntegerSecondCountable (v : FinitePlace) :
    SecondCountableTopology (v.adicCompletionIntegers K) :=
  (Valued.isOpen_valuationSubring (v.adicCompletion K)).isOpenEmbedding_subtypeVal.isEmbedding.secondCountableTopology

/-- Countably many open local-field cylinders cover the finite adeles. -/
instance ellipticFiniteAdeles_secondCountable : SecondCountableTopology FiniteAdeles := by
  letI (S : Finset FinitePlace) : SecondCountableTopology (finiteAdeleCylinder S) := by
    letI (v : S) : SecondCountableTopology (v.1.adicCompletion K) := finiteCompletion_secondCountable v.1
    letI (v : {v : FinitePlace // v ∉ S}) :
        SecondCountableTopology (v.1.adicCompletionIntegers K) := topologyIntegerSecondCountable v.1
    exact (finiteAdeleCylinderHomeomorph S).symm.isEmbedding.secondCountableTopology
  apply TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun S : Finset FinitePlace => (finiteAdeleCylinder S : Set FiniteAdeles))
    finiteAdeleCylinder_isOpen
  ext a
  simp only [mem_iUnion, mem_univ, iff_true]
  exact exists_mem_finiteAdeleCylinder a

/-- The actual full adele ring is second countable. -/
instance ellipticAdeles_secondCountable : SecondCountableTopology Adeles := by
  letI : SecondCountableTopology FiniteAdeles := ellipticFiniteAdeles_secondCountable
  infer_instance

/-- Addition on the actual adeles is jointly Borel measurable. -/
instance ellipticAdeles_measurableAdd₂ : MeasurableAdd₂ Adeles := ⟨continuous_add.measurable⟩

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase


namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open MeasureTheory
open scoped ENNReal
noncomputable section

local instance scalarSamplerFieldMeasurable : MeasurableSpace K := ⊤
local instance scalarSamplerFieldSingleton : MeasurableSingletonClass K := ⟨fun _ => trivial⟩

/-- A compact-domain point and a rational translation give an actual adele. -/
def ellipticAdditiveSampler (p : ellipticAdditiveDomain × K) : Adeles :=
  adeleEmbedding p.2 + (p.1 : Adeles)

/-- Sampling uses domain Haar probability and counting measure on the actual function field. -/
def ellipticAdditiveSamplerMeasure : Measure (ellipticAdditiveDomain × K) :=
  ellipticDomainHaar.prod Measure.count

private theorem measurable_ellipticAdditiveSampler : Measurable ellipticAdditiveSampler := by
  apply measurable_from_prod_countable_left
  intro z
  exact (continuous_const.add continuous_subtype_val).measurable

/-- Scalar periodization is an exact measure-preserving sampling of ambient adelic Haar. -/
theorem ellipticAdditiveSampler_measurePreserving :
    MeasurePreserving ellipticAdditiveSampler ellipticAdditiveSamplerMeasure adeleHaar := by
  refine ⟨measurable_ellipticAdditiveSampler, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_ellipticAdditiveSampler]
  unfold ellipticAdditiveSamplerMeasure
  rw [lintegral_prod (fun p => f (ellipticAdditiveSampler p))
    (hf.comp measurable_ellipticAdditiveSampler).aemeasurable]
  simp only [ellipticAdditiveSampler, lintegral_count]
  exact (lintegral_adeleHaar_periodization f hf).symm

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticFiniteAdeles_secondCountable

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticAdeles_measurableAdd₂

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticAdditiveSampler_measurePreserving

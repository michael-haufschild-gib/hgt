import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticLocalFields
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Data.Finsupp.Encodable

/-!
# Normalized Haar measure on the actual elliptic adeles

The product of all local integer rings is compact and open. Denominator clearing
covers finite adeles by countably many compact dilates, giving sigma-compactness.
Adding the infinity completion gives the full locally compact additive group and
its Haar measure normalized to assign mass one to the integral product.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

open IsDedekindDomain MeasureTheory
open scoped WithZero WithZeroMulInt

noncomputable section

instance constantsPolynomial_countable : Countable (Polynomial Constants) :=
  (AddMonoidAlgebra.coeffEquiv.injective.comp
    (Polynomial.toFinsuppIso Constants).injective).countable

instance coordinateRing_countable : Countable CoordinateRing :=
  (WeierstrassCurve.Affine.CoordinateRing.basis curve.toAffine).repr.injective.countable

instance functionField_countable : Countable K := by
  have hs : Function.Surjective (fun p : CoordinateRing × CoordinateRing =>
      algebraMap CoordinateRing K p.1 / algebraMap CoordinateRing K p.2) := by
    intro z
    obtain ⟨a, b, _, h⟩ := IsFractionRing.div_surjective CoordinateRing z
    exact ⟨(a, b), h⟩
  exact hs.countable

instance ringOfIntegers_countable : Countable RingOfIntegers :=
  (IsFractionRing.injective RingOfIntegers K).countable

instance finiteCompletion_t2 (v : FinitePlace) : T2Space (v.adicCompletion K) :=
  (HeightOneSpectrum.adicCompletion.uniformEquiv K v).toHomeomorph.isEmbedding.t2Space

instance finiteAdeles_t2 : T2Space FiniteAdeles := by
  unfold FiniteAdeles IsDedekindDomain.FiniteAdeleRing
  exact @RestrictedProduct.instT2Space
    FinitePlace (fun v => v.adicCompletion K)
    (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    Filter.cofinite (fun _ => inferInstance) (fun v => finiteCompletion_t2 v)

/-- The compact open product of all finite-place integer rings. -/
def integralFiniteAdeles : Set FiniteAdeles :=
  {a | ∀ v : FinitePlace, a v ∈ v.adicCompletionIntegers K}

theorem integralFiniteAdeles_isOpen : IsOpen integralFiniteAdeles :=
  RestrictedProduct.isOpen_forall_mem
    (R := fun v : FinitePlace => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (fun _ => Valued.isOpen_valuationSubring _)

theorem integralFiniteAdeles_isCompact : IsCompact integralFiniteAdeles := by
  letI : CompactSpace ((v : FinitePlace) → v.adicCompletionIntegers K) := Pi.compactSpace
  rw [show integralFiniteAdeles = Set.range
      (RestrictedProduct.structureMap
        (fun v : FinitePlace => v.adicCompletion K)
        (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
        Filter.cofinite) by
    ext a
    rw [integralFiniteAdeles, RestrictedProduct.range_structureMap]
    rfl]
  exact isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : FinitePlace => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (fun _ => Valued.isOpen_valuationSubring _)).continuous

theorem zero_mem_integralFiniteAdeles : (0 : FiniteAdeles) ∈ integralFiniteAdeles :=
  fun _ => zero_mem _

/-- One actual affine integer clears all finite-place denominators of an adele. -/
theorem finiteAdele_exists_integral_denominator (a : FiniteAdeles) :
    ∃ d : RingOfIntegers, d ≠ 0 ∧
      ∀ v : FinitePlace, a v * algebraMap RingOfIntegers (v.adicCompletion K) d ∈
        v.adicCompletionIntegers K := by
  classical
  choose b hb hab using fun v : FinitePlace =>
    HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers
      (K := K) v (a v)
  have hbad : {v : FinitePlace | a v ∉ v.adicCompletionIntegers K}.Finite := by
    rw [← Filter.eventually_cofinite]
    exact a.2
  let S := hbad.toFinset
  let d : RingOfIntegers := ∏ v ∈ S, b v
  refine ⟨d, Finset.prod_ne_zero_iff.mpr (fun v _ => nonZeroDivisors.ne_zero (hb v)), ?_⟩
  intro v
  by_cases hv : v ∈ S
  · have hd : d = b v * ∏ w ∈ S.erase v, b w := by
      exact (Finset.mul_prod_erase S b hv).symm
    rw [hd, map_mul, ← mul_assoc]
    exact mul_mem (hab v) (HeightOneSpectrum.coe_mem_adicCompletionIntegers v _)
  · have hav : a v ∈ v.adicCompletionIntegers K := by
      by_contra hn
      exact hv (by simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hn)
    exact mul_mem hav (HeightOneSpectrum.coe_mem_adicCompletionIntegers v d)

def finiteAdeleDenominatorCompact (d : RingOfIntegers) : Set FiniteAdeles :=
  (fun z => z * finiteAdeleEmbedding ((algebraMap RingOfIntegers K d)⁻¹)) '' integralFiniteAdeles

theorem finiteAdeleDenominatorCompact_isCompact (d : RingOfIntegers) :
    IsCompact (finiteAdeleDenominatorCompact d) :=
  integralFiniteAdeles_isCompact.image (continuous_id.mul continuous_const)

theorem finiteAdele_mem_denominatorCompact (a : FiniteAdeles) :
    ∃ d : RingOfIntegers, a ∈ finiteAdeleDenominatorCompact d := by
  obtain ⟨d, hd, had⟩ := finiteAdele_exists_integral_denominator a
  refine ⟨d, a * finiteAdeleEmbedding (algebraMap RingOfIntegers K d), had, ?_⟩
  change (a * finiteAdeleEmbedding (algebraMap RingOfIntegers K d)) *
    finiteAdeleEmbedding ((algebraMap RingOfIntegers K d)⁻¹) = a
  rw [mul_assoc, ← map_mul, mul_inv_cancel₀]
  · rw [map_one, mul_one]
  · exact (IsFractionRing.injective RingOfIntegers K).ne hd

instance finiteAdeles_sigmaCompact : SigmaCompactSpace FiniteAdeles := by
  apply SigmaCompactSpace.of_countable
    (Set.range finiteAdeleDenominatorCompact) (Set.countable_range _)
  · rintro _ ⟨d, rfl⟩
    exact finiteAdeleDenominatorCompact_isCompact d
  · apply Set.eq_univ_of_forall
    intro a
    obtain ⟨d, hd⟩ := finiteAdele_mem_denominatorCompact a
    exact Set.mem_sUnion_of_mem hd ⟨d, rfl⟩

instance infinityCompletion_sigmaCompact : SigmaCompactSpace InfinityCompletion := by
  letI : NormedField InfinityCompletion :=
    HTGeometry.DiscreteValuedCompletion.completedNormedField (WithVal infinityValuation)
  letI : ProperSpace InfinityCompletion :=
    HTGeometry.DiscreteValuedCompletion.completedProperSpace (WithVal infinityValuation)
  letI : SecondCountableTopology InfinityCompletion := secondCountable_of_proper
  infer_instance

instance adeles_sigmaCompact : SigmaCompactSpace Adeles := inferInstance
instance adeles_t2 : T2Space Adeles := inferInstance
instance adeles_measurableSpace : MeasurableSpace Adeles := borel _
instance adeles_borelSpace : BorelSpace Adeles := ⟨rfl⟩

/-- All local integer rings, including the genuine degree-one infinity place. -/
def integralAdeles : Set Adeles :=
  integralFiniteAdeles ×ˢ ((Valued.v : Valuation InfinityCompletion ℤᵐ⁰).integer : Set InfinityCompletion)

theorem integralAdeles_isOpen : IsOpen integralAdeles :=
  integralFiniteAdeles_isOpen.prod (Valued.isOpen_valuationSubring InfinityCompletion)

theorem integralAdeles_isCompact : IsCompact integralAdeles :=
  integralFiniteAdeles_isCompact.prod (isCompact_iff_compactSpace.mpr
    (HTGeometry.DiscreteValuedCompletion.completedIntegerCompact (WithVal infinityValuation)))

def integralAdelesPositiveCompacts : TopologicalSpace.PositiveCompacts Adeles where
  carrier := integralAdeles
  isCompact' := integralAdeles_isCompact
  interior_nonempty' := by
    rw [integralAdeles_isOpen.interior_eq]
    exact ⟨0, zero_mem_integralFiniteAdeles, zero_mem _⟩

/-- The actual additive Haar measure, normalized by volume one for the full integral product. -/
def adeleHaar : Measure Adeles := Measure.addHaarMeasure integralAdelesPositiveCompacts

instance adeleHaar_isAddHaar : adeleHaar.IsAddHaarMeasure := by
  unfold adeleHaar
  infer_instance

instance adeleHaar_sigmaFinite : SigmaFinite adeleHaar := inferInstance

@[simp] theorem adeleHaar_integralAdeles : adeleHaar integralAdeles = 1 :=
  Measure.addHaarMeasure_self

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase


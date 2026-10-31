import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticUnipotentQuotient
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticUnipotentProbability

/-!
# Invariant probability on the rational coefficient quotient

The product-domain probability descends through the canonical quotient
homeomorphism. The normalized domain action agrees with actual left
multiplication on every rational coset, so its invariant law is an
invariant probability on the quotient itself.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open HTGeometry.LoopEisenstein MeasureTheory
noncomputable section

instance : MeasurableSpace UnipotentCoefficientQuotient := borel _
instance : BorelSpace UnipotentCoefficientQuotient := ⟨rfl⟩

theorem continuous_domainToUnipotentCoefficientQuotient :
    Continuous domainToUnipotentCoefficientQuotient :=
  unipotentCoefficientQuotientHomeomorph.symm.continuous

/-- Actual quotient left multiplication, expressed through canonical domain coordinates. -/
def unipotentCoefficientQuotientLeft (g : UniformUnipotentModel)
    (q : UnipotentCoefficientQuotient) : UnipotentCoefficientQuotient :=
  domainToUnipotentCoefficientQuotient (adeleUnipotentDomainAction g.1
    (unipotentCoefficientQuotientNormalization q))

theorem continuous_unipotentCoefficientQuotientLeft (g : UniformUnipotentModel) :
    Continuous (unipotentCoefficientQuotientLeft g) :=
  continuous_domainToUnipotentCoefficientQuotient.comp
    ((continuous_adeleUnipotentDomainAction g.1).comp
      unipotentCoefficientQuotientHomeomorph.continuous)

private theorem domainAction_to_quotient (g : UniformUnipotentModel)
    (d : ℕ → ellipticAdditiveDomain) :
    domainToUnipotentCoefficientQuotient (adeleUnipotentDomainAction g.1 d) =
      ((g * domainToUniformUnipotent d : UniformUnipotentModel) : UnipotentCoefficientQuotient) := by
  have he : uniformUnipotentNormalization (g * domainToUniformUnipotent d) =
      adeleUnipotentDomainAction g.1 d := by
    change adeleUnipotentNormalization (unipotentCoefficientStreamEquiv Adeles
      (g.1 * (unipotentCoefficientStreamEquiv Adeles).symm (fun n => (d n : Adeles)))) =
        adeleUnipotentNormalization (unipotentStreamProduct
          (unipotentCoefficientStreamEquiv Adeles g.1, fun n => (d n : Adeles)))
    unfold unipotentStreamProduct
    rw [Equiv.symm_apply_apply]
  calc
    domainToUnipotentCoefficientQuotient (adeleUnipotentDomainAction g.1 d) =
        domainToUnipotentCoefficientQuotient
          (uniformUnipotentNormalization (g * domainToUniformUnipotent d)) :=
      congrArg domainToUnipotentCoefficientQuotient he.symm
    _ = _ := unipotentCoefficientQuotientEquiv.symm_apply_apply
      ((g * domainToUniformUnipotent d : UniformUnipotentModel) : UnipotentCoefficientQuotient)

private theorem quotient_left_mul_congr {G : Type*} [Group G] (H : Subgroup G)
    (g a b : G) (h : (a : G ⧸ H) = (b : G ⧸ H)) :
    ((g * a : G) : G ⧸ H) = ((g * b : G) : G ⧸ H) := by
  apply QuotientGroup.eq.mpr
  have he : (g * a)⁻¹ * (g * b) = a⁻¹ * b := by group
  rw [he]
  exact QuotientGroup.eq.mp h

/-- The coordinate-defined action is exactly left multiplication on every actual rational coset. -/
theorem unipotentCoefficientQuotientLeft_mk (g h : UniformUnipotentModel) :
    unipotentCoefficientQuotientLeft g (h : UnipotentCoefficientQuotient) =
      ((g * h : UniformUnipotentModel) : UnipotentCoefficientQuotient) := by
  let d := unipotentCoefficientQuotientNormalization (h : UnipotentCoefficientQuotient)
  calc
    unipotentCoefficientQuotientLeft g (h : UnipotentCoefficientQuotient) =
        ((g * domainToUniformUnipotent d : UniformUnipotentModel) : UnipotentCoefficientQuotient) :=
      domainAction_to_quotient g d
    _ = _ := quotient_left_mul_congr uniformRationalUnipotentRange g
      (domainToUniformUnipotent d) h
      (unipotentCoefficientQuotientEquiv.symm_apply_apply (h : UnipotentCoefficientQuotient))

private theorem quotientLeft_domain (g : UniformUnipotentModel) :
    unipotentCoefficientQuotientLeft g ∘ domainToUnipotentCoefficientQuotient =
      domainToUnipotentCoefficientQuotient ∘ adeleUnipotentDomainAction g.1 := by
  funext d
  change unipotentCoefficientQuotientEquiv.symm
    (adeleUnipotentDomainAction g.1
      (unipotentCoefficientQuotientEquiv (unipotentCoefficientQuotientEquiv.symm d))) =
        unipotentCoefficientQuotientEquiv.symm (adeleUnipotentDomainAction g.1 d)
  rw [Equiv.apply_symm_apply]

/-- The canonical probability on the rational coefficient quotient. -/
def unipotentCoefficientQuotientProbability : Measure UnipotentCoefficientQuotient :=
  Measure.map domainToUnipotentCoefficientQuotient adeleUnipotentDomainProbability

instance unipotentCoefficientQuotientProbability_isProbability :
    IsProbabilityMeasure unipotentCoefficientQuotientProbability := by
  constructor
  change (Measure.map domainToUnipotentCoefficientQuotient adeleUnipotentDomainProbability) Set.univ = 1
  rw [Measure.map_apply continuous_domainToUnipotentCoefficientQuotient.measurable
    MeasurableSet.univ, Set.preimage_univ]
  exact measure_univ

/-- Actual left multiplication preserves the probability on the rational quotient. -/
theorem measurePreserving_unipotentCoefficientQuotientLeft (g : UniformUnipotentModel) :
    MeasurePreserving (unipotentCoefficientQuotientLeft g)
      unipotentCoefficientQuotientProbability unipotentCoefficientQuotientProbability := by
  refine ⟨(continuous_unipotentCoefficientQuotientLeft g).measurable, ?_⟩
  change Measure.map (unipotentCoefficientQuotientLeft g)
    (Measure.map domainToUnipotentCoefficientQuotient adeleUnipotentDomainProbability) =
      Measure.map domainToUnipotentCoefficientQuotient adeleUnipotentDomainProbability
  rw [Measure.map_map (continuous_unipotentCoefficientQuotientLeft g).measurable
    continuous_domainToUnipotentCoefficientQuotient.measurable, quotientLeft_domain,
    ← Measure.map_map continuous_domainToUnipotentCoefficientQuotient.measurable
      (continuous_adeleUnipotentDomainAction g.1).measurable,
    (measurePreserving_adeleUnipotentDomainAction g.1).map_eq]

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.unipotentCoefficientQuotientLeft_mk
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.unipotentCoefficientQuotientProbability_isProbability
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.measurePreserving_unipotentCoefficientQuotientLeft

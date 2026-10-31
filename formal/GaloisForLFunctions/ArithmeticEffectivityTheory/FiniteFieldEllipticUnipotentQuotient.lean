import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticUnipotentIntegrality
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticUnipotentNormalization
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The normalized coefficient quotient of elliptic unipotents

The uniform matrix group is given its explicit free-coefficient topology.
Canonical normalization and decoding induce inverse continuous maps
between its right rational quotient and the countable product of actual
additive fundamental domains.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open HTGeometry.LoopEisenstein Filter
noncomputable section

/-- The uniform matrix carrier with the free-coefficient topology specified below. -/
def UniformUnipotentModel := uniformlyIntegralUnipotent

instance : Group UniformUnipotentModel := inferInstanceAs (Group uniformlyIntegralUnipotent)

def uniformUnipotentStream (g : UniformUnipotentModel) : ℕ → Adeles :=
  unipotentCoefficientStreamEquiv Adeles g.1

instance : TopologicalSpace UniformUnipotentModel :=
  TopologicalSpace.induced uniformUnipotentStream inferInstance

theorem continuous_uniformUnipotentStream : Continuous uniformUnipotentStream :=
  continuous_induced_dom

/-- Diagonal rational matrices in the uniform coefficient model. -/
def uniformRationalUnipotentEmbedding : uniformlyIntegralRationalUnipotent →* UniformUnipotentModel where
  toFun r := ⟨unipotentCoefficientMap adeleEmbedding r, r.property⟩
  map_one' := Subtype.ext (unipotentCoefficientMap adeleEmbedding).map_one
  map_mul' r s := Subtype.ext ((unipotentCoefficientMap adeleEmbedding).map_mul r.1 s.1)

def uniformRationalUnipotentRange : Subgroup UniformUnipotentModel :=
  uniformRationalUnipotentEmbedding.range

/-- Right cosets by the actual uniformly integral rational coefficient subgroup. -/
abbrev UnipotentCoefficientQuotient := UniformUnipotentModel ⧸ uniformRationalUnipotentRange

def uniformUnipotentNormalization (g : UniformUnipotentModel) : ℕ → ellipticAdditiveDomain :=
  adeleUnipotentNormalization (uniformUnipotentStream g)

theorem continuous_uniformUnipotentNormalization : Continuous uniformUnipotentNormalization :=
  continuous_adeleUnipotentNormalization.comp continuous_uniformUnipotentStream

/-- Decode an arbitrary domain stream inside the uniform coefficient group. -/
def domainToUniformUnipotent (d : ℕ → ellipticAdditiveDomain) : UniformUnipotentModel :=
  ⟨(unipotentCoefficientStreamEquiv Adeles).symm (fun n => (d n : Adeles)), by
    apply (mem_uniformlyIntegralUnipotent _).mpr
    apply Eventually.of_forall
    intro v n
    rw [Equiv.apply_symm_apply]
    exact (d n).property.1 v⟩

theorem uniformUnipotentStream_domain (d : ℕ → ellipticAdditiveDomain) :
    uniformUnipotentStream (domainToUniformUnipotent d) = fun n => (d n : Adeles) :=
  (unipotentCoefficientStreamEquiv Adeles).apply_symm_apply _

theorem continuous_domainToUniformUnipotent : Continuous domainToUniformUnipotent := by
  apply continuous_induced_rng.mpr
  have he : uniformUnipotentStream ∘ domainToUniformUnipotent =
      (fun d : ℕ → ellipticAdditiveDomain => fun n => (d n : Adeles)) := by
    funext d
    exact uniformUnipotentStream_domain d
  rw [he]
  exact continuous_pi fun n => continuous_subtype_val.comp (continuous_apply n)

theorem uniformUnipotentNormalization_domain (d : ℕ → ellipticAdditiveDomain) :
    uniformUnipotentNormalization (domainToUniformUnipotent d) = d := by
  change adeleUnipotentNormalization (uniformUnipotentStream (domainToUniformUnipotent d)) = d
  rw [uniformUnipotentStream_domain]
  exact adeleUnipotentNormalization_domain d

theorem uniformUnipotentNormalization_mul_rational (g : UniformUnipotentModel)
    (r : uniformlyIntegralRationalUnipotent) :
    uniformUnipotentNormalization (g * uniformRationalUnipotentEmbedding r) =
      uniformUnipotentNormalization g := by
  funext n
  apply Subtype.ext
  change (adeleUnipotentNormalization (unipotentCoefficientStreamEquiv Adeles
    (g.1 * unipotentCoefficientMap adeleEmbedding r)) n : Adeles) =
      (adeleUnipotentNormalization (unipotentCoefficientStreamEquiv Adeles g.1) n : Adeles)
  rw [adeleUnipotentNormalization_stream, adeleUnipotentNormalization_stream,
    adeleUnipotentReduced_mul_rational]

private theorem normalization_coset (a b : UniformUnipotentModel)
    (hab : a⁻¹ * b ∈ uniformRationalUnipotentRange) :
    uniformUnipotentNormalization a = uniformUnipotentNormalization b := by
  obtain ⟨r, hr⟩ := hab
  have hb : a * uniformRationalUnipotentEmbedding r = b := by
    rw [hr]
    exact mul_inv_cancel_left a b
  rw [← hb, uniformUnipotentNormalization_mul_rational]

/-- Continuous canonical representatives on right rational cosets. -/
def unipotentCoefficientQuotientNormalization :
    UnipotentCoefficientQuotient → (ℕ → ellipticAdditiveDomain) :=
  Quotient.lift uniformUnipotentNormalization
    (fun a b h => normalization_coset a b (QuotientGroup.leftRel_apply.mp h))

def domainToUnipotentCoefficientQuotient (d : ℕ → ellipticAdditiveDomain) :
    UnipotentCoefficientQuotient := (domainToUniformUnipotent d : UnipotentCoefficientQuotient)

/-- Decoding the normalized domain stream recovers the canonical reduced matrix. -/
theorem domainToUniformUnipotent_normalization (g : UniformUnipotentModel) :
    (domainToUniformUnipotent (uniformUnipotentNormalization g)).1 = adeleUnipotentReduced g.1 := by
  apply (unipotentCoefficientStreamEquiv Adeles).injective
  funext n
  have hd := congrFun (uniformUnipotentStream_domain (uniformUnipotentNormalization g)) n
  exact hd.trans (adeleUnipotentNormalization_stream g.1 n)

private theorem quotient_normalization_inverse (q : UnipotentCoefficientQuotient) :
    domainToUnipotentCoefficientQuotient (unipotentCoefficientQuotientNormalization q) = q := by
  induction q using Quotient.inductionOn with
  | h g =>
    change (domainToUniformUnipotent (uniformUnipotentNormalization g) :
      UnipotentCoefficientQuotient) = (g : UnipotentCoefficientQuotient)
    symm
    apply QuotientGroup.eq.mpr
    let r : uniformlyIntegralRationalUnipotent :=
      ⟨adeleUnipotentRationalCorrection g.1, adeleUnipotentRationalCorrection_uniform g.1 g.property⟩
    have he : g * uniformRationalUnipotentEmbedding r =
        domainToUniformUnipotent (uniformUnipotentNormalization g) := by
      apply Subtype.ext
      exact (domainToUniformUnipotent_normalization g).symm
    refine ⟨r, ?_⟩
    rw [← he]
    exact (inv_mul_cancel_left g (uniformRationalUnipotentEmbedding r)).symm

/-- The rational coefficient quotient has one and only one domain stream per coset. -/
def unipotentCoefficientQuotientEquiv :
    UnipotentCoefficientQuotient ≃ (ℕ → ellipticAdditiveDomain) where
  toFun := unipotentCoefficientQuotientNormalization
  invFun := domainToUnipotentCoefficientQuotient
  left_inv := quotient_normalization_inverse
  right_inv := uniformUnipotentNormalization_domain

/-- The quotient topology is exactly the product topology of the actual domain coordinates. -/
def unipotentCoefficientQuotientHomeomorph :
    UnipotentCoefficientQuotient ≃ₜ (ℕ → ellipticAdditiveDomain) where
  toEquiv := unipotentCoefficientQuotientEquiv
  continuous_toFun := continuous_uniformUnipotentNormalization.quotient_lift _
  continuous_invFun := (continuous_quotient_mk'
    (s := QuotientGroup.leftRel uniformRationalUnipotentRange)).comp continuous_domainToUniformUnipotent

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.unipotentCoefficientQuotientEquiv
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.unipotentCoefficientQuotientHomeomorph

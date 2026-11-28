import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FinitePlaceOfAbsoluteValuation
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilGroupAtFinitePlace
import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerFactorOfAnInducedRepresentation

/-! A finite decomposition automorphism is the restriction of a Weil
element. Lift its residue action by a power of Frobenius and the
remaining inertia action by absolute inertia. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField GaloisForLFunctions
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped Pointwise

namespace GlobalTheory.Reciprocity

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] [IsGalois K L] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)

def finiteWeilRestriction :
    Weil h →* MulAction.stabilizer Gal(L/K) (finitePlaceAtAbsoluteValuation (L := L) A h).asIdeal :=
  ((AlgEquiv.restrictNormalHom L).comp (Weil h).subtype).codRestrict _
    fun σ => restrictNormalHom_mem_stabilizer_of_mem_Dec A h (Weil_le_Dec h σ.2)

theorem finiteWeilRestriction_surjective : Function.Surjective (finiteWeilRestriction (L := L) h) := by
  let w := finitePlaceAtAbsoluteValuation (L := L) A h
  letI := w.isMaximal
  letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := L) A h
  letI : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  let r := (AlgEquiv.restrictNormalHom L).comp (Weil h).subtype
  let φ := frob h
  have hφ : IsArithFrobAt (𝓞 K) (r φ) w.asIdeal := restrictNormalHom_isArithFrobAt A h (isFrob_frob (h := h))
  intro x
  obtain ⟨n, τ, hτ, hx⟩ := (mem_stabilizer_iff_exists_pow_mul w.asIdeal hφ x.val).mp x.2
  obtain ⟨σ, hσ⟩ := exists_Ine_restrictNormalHom_eq A h τ hτ
  refine ⟨φ ^ n * ineIncl h σ, Subtype.ext ?_⟩
  change r (φ ^ n * ineIncl h σ) = x.val
  have hσ' : r (ineIncl h σ) = τ := hσ
  rw [map_mul, map_pow, hσ', ← hx]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteWeilRestriction_surjective

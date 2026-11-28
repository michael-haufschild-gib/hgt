import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionNormReduction
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ArtinResidueDegree
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.GaloisValuations.Global

/-! The completion of a decomposition automorphism preserves integral
elements. An arithmetic Frobenius induces the residue-cardinality power. -/

noncomputable section

open NumberField IsDedekindDomain GaloisForLFunctions WindowedLandauTheory.ConjugateSelfDual
open scoped Pointwise GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

local notation "D" => MulAction.stabilizer Gal(L/K) w.asIdeal

def decompositionOnCompletedIntegersEquiv (σ : D) :
    CompletedIntegers w ≃+* CompletedIntegers w where
  toFun := decompositionOnCompletedIntegers v w σ
  invFun := decompositionOnCompletedIntegers v w σ⁻¹
  left_inv x := by
    apply Subtype.ext
    change (decompositionMulEquiv v w σ⁻¹) ((decompositionMulEquiv v w σ) x.val) = x.val
    rw [map_inv]
    exact (decompositionMulEquiv v w σ).symm_apply_apply _
  right_inv x := by
    apply Subtype.ext
    change (decompositionMulEquiv v w σ) ((decompositionMulEquiv v w σ⁻¹) x.val) = x.val
    rw [map_inv]
    exact (decompositionMulEquiv v w σ).apply_symm_apply _
  map_add' := map_add (decompositionOnCompletedIntegers v w σ)
  map_mul' := map_mul (decompositionOnCompletedIntegers v w σ)

theorem completionReduction_decomposition_frobenius (σ : D)
    (hσ : IsArithFrobAt (𝓞 K) σ.val w.asIdeal) (x : CompletedIntegers w) :
    completionReduction w (decompositionOnCompletedIntegersEquiv v w σ x) =
      completionReduction w x ^ normV v := by
  change completionReduction w (decompositionOnCompletedIntegers v w σ x) = _
  rw [completionReduction_decomposition]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (completionReduction w x)
  rw [← ha, Ideal.Quotient.stabilizerHom_apply, ← map_pow]
  apply Ideal.Quotient.eq.mpr
  have h := hσ a
  rwa [← Ideal.over_def w.asIdeal v.asIdeal] at h

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.completionReduction_decomposition_frobenius

import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionReduction
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionNormValuation
import Mathlib.FieldTheory.Finite.GaloisField

/-! At an unramified prime, reduction commutes with the local norm. -/

noncomputable section

open NumberField IsDedekindDomain
open scoped GlobalTheory.Reciprocity.AdicLiesOver Pointwise

namespace GlobalTheory.Reciprocity

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

private def completedIntegerAlgebraMap : CompletedIntegers v →+* CompletedIntegers w :=
  ((AdicLiesOver.completionMap v w).comp (CompletedIntegers v).subtype).codRestrict _
    (fun x => by
      change Valued.v (AdicLiesOver.completionMap v w x.val) ≤ 1
      rw [AdicLiesOver.valued_completionMap]
      exact pow_le_one' x.2 _)

private theorem completedIntegerAlgebraMap_toCompletedIntegers (r : 𝓞 K) :
    completedIntegerAlgebraMap v w (toCompletedIntegers v r) =
      toCompletedIntegers w (algebraMap (𝓞 K) (𝓞 L) r) := by
  apply Subtype.ext
  exact algebraMap_completion_algebraMap_int v w r

private theorem completionReduction_algebraMap (x : CompletedIntegers v) :
    completionReduction w (completedIntegerAlgebraMap v w x) =
      algebraMap (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w.asIdeal) (completionReduction v x) := by
  obtain ⟨r, hr⟩ := exists_int_valued_sub_lt_one v x.val x.2
  have hm : completionReduction w (completedIntegerAlgebraMap v w x) =
      completionReduction w (completedIntegerAlgebraMap v w (toCompletedIntegers v r)) := by
    apply (completionReduction_eq_iff w _ _).mpr
    change Valued.v (AdicLiesOver.completionMap v w x.val -
      AdicLiesOver.completionMap v w (algebraMap (𝓞 K) (v.adicCompletion K) r)) < 1
    rw [← map_sub, AdicLiesOver.valued_completionMap]
    exact pow_lt_one' hr (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
      w.asIdeal v.ne_bot)
  rw [hm, completedIntegerAlgebraMap_toCompletedIntegers, completionReduction_toCompletedIntegers,
    (completionReduction_eq_iff v x (toCompletedIntegers v r)).mpr hr,
    completionReduction_toCompletedIntegers, Ideal.Quotient.algebraMap_mk_of_liesOver]

variable [IsGalois K L]

local notation "D" => MulAction.stabilizer Gal(L/K) w.asIdeal

/-- The local field norm restricts to a monoid homomorphism on integral elements. -/
def completedIntegerNorm : CompletedIntegers w →* CompletedIntegers v :=
  (Algebra.norm (v.adicCompletion K)).comp (CompletedIntegers w).subtype.toMonoidHom
    |>.codRestrict _ (fun x => by
      change Valued.v (Algebra.norm (v.adicCompletion K) x.val) ≤ 1
      rw [valued_finiteCompletion_norm v w]
      exact pow_le_one' x.2 _)

/-- The decomposition action restricts to the integral elements of the completion. -/
def decompositionOnCompletedIntegers (σ : D) : CompletedIntegers w →+* CompletedIntegers w :=
  ((decompositionMulEquiv v w σ).toRingHom.comp (CompletedIntegers w).subtype).codRestrict _
    (fun x => by
      change Valued.v (decompositionMulEquiv v w σ x.val) ≤ 1
      rw [valued_decompositionMulEquiv]
      exact x.2)

private theorem decompositionOnCompletedIntegers_toCompletedIntegers (σ : D) (r : 𝓞 L) :
    decompositionOnCompletedIntegers v w σ (toCompletedIntegers w r) =
      toCompletedIntegers w (σ • r) := by
  apply Subtype.ext
  change decompositionMulEquiv v w σ (algebraMap (𝓞 L) (w.adicCompletion L) r) =
    algebraMap (𝓞 L) (w.adicCompletion L) (σ • r)
  rw [IsScalarTower.algebraMap_apply (𝓞 L) L (w.adicCompletion L),
    IsScalarTower.algebraMap_apply (𝓞 L) L (w.adicCompletion L), decompositionMulEquiv_algebraMap]
  rfl

theorem completionReduction_decomposition (σ : D) (x : CompletedIntegers w) :
    completionReduction w (decompositionOnCompletedIntegers v w σ x) =
      Ideal.Quotient.stabilizerHom w.asIdeal v.asIdeal Gal(L/K) σ (completionReduction w x) := by
  obtain ⟨r, hr⟩ := exists_int_valued_sub_lt_one w x.val x.2
  have h : completionReduction w (decompositionOnCompletedIntegers v w σ x) =
      completionReduction w (decompositionOnCompletedIntegers v w σ (toCompletedIntegers w r)) := by
    apply (completionReduction_eq_iff w _ _).mpr
    change Valued.v (decompositionMulEquiv v w σ x.val -
      decompositionMulEquiv v w σ (algebraMap (𝓞 L) (w.adicCompletion L) r)) < 1
    rwa [← map_sub, valued_decompositionMulEquiv]
  rw [h, decompositionOnCompletedIntegers_toCompletedIntegers, completionReduction_toCompletedIntegers,
    (completionReduction_eq_iff w x (toCompletedIntegers w r)).mpr hr,
    completionReduction_toCompletedIntegers, Ideal.Quotient.stabilizerHom_apply]

private theorem completedIntegerNorm_prod_decomposition (x : CompletedIntegers w) :
    completedIntegerAlgebraMap v w (completedIntegerNorm v w x) =
      ∏ σ : D, decompositionOnCompletedIntegers v w σ x := by
  apply Subtype.ext
  change algebraMap (v.adicCompletion K) (w.adicCompletion L)
      (Algebra.norm (v.adicCompletion K) x.val) = (CompletedIntegers w).subtype
        (∏ σ : D, decompositionOnCompletedIntegers v w σ x)
  rw [Algebra.norm_eq_prod_automorphisms, map_prod]
  exact Fintype.prod_equiv (decompositionMulEquiv v w).symm.toEquiv _ _ (fun σ => by
    change σ x.val = decompositionMulEquiv v w ((decompositionMulEquiv v w).symm σ) x.val
    rw [MulEquiv.apply_symm_apply])

private theorem quotientStabilizerHom_bijective (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Function.Bijective (Ideal.Quotient.stabilizerHom w.asIdeal v.asIdeal Gal(L/K)) := by
  letI := v.isMaximal
  letI := w.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  letI := Ideal.Quotient.field w.asIdeal
  letI : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  have hs := Ideal.Quotient.stabilizerHom_surjective Gal(L/K) v.asIdeal w.asIdeal
  apply hs.bijective_of_nat_card_le
  rw [card_decompositionGroup v w, he, one_mul, IsGalois.card_aut_eq_finrank,
    Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal]

/-- Modulo an unramified prime, the norm of an integer becomes the residue field norm. -/
theorem completionReduction_norm_of_unramified (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    (x : CompletedIntegers w) :
    completionReduction v (completedIntegerNorm v w x) =
      Algebra.norm (𝓞 K ⧸ v.asIdeal) (completionReduction w x) := by
  letI := v.isMaximal
  letI := w.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  letI := Ideal.Quotient.field w.asIdeal
  letI : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  apply (algebraMap (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w.asIdeal)).injective
  rw [← completionReduction_algebraMap v w, completedIntegerNorm_prod_decomposition,
    map_prod, Algebra.norm_eq_prod_automorphisms]
  exact Fintype.prod_bijective _ (quotientStabilizerHom_bijective v w he) _ _
    (fun σ => completionReduction_decomposition v w σ x)

end GlobalTheory.Reciprocity

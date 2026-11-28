import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicProductNorm

/-! The idelic norm of an idele supported at a finite place is the
corresponding local norm supported at the place below it. -/

noncomputable section

open NumberField IsDedekindDomain
open scoped GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

theorem ideleNorm_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (w : finitePlacesAbove L v)
    (x : (w.val.adicCompletion L)ˣ) :
    ideleNorm (K := K) (finiteEmbedding w.val x) =
      finiteEmbedding v (Units.map (Algebra.norm (v.adicCompletion K)) x) := by
  classical
  apply ext_of_localUnits
  · intro u
    rw [finiteProj_ideleNorm]
    change (∏ p : finitePlacesAbove L u, Units.map (Algebra.norm (u.adicCompletion K))
      (finiteProj p.val (finiteEmbedding w.val x))) = _
    by_cases hu : u = v
    · subst u
      rw [Fintype.prod_eq_single w]
      · rw [finiteProj_finiteEmbedding, finiteProj_finiteEmbedding]
      · intro p hp
        rw [finiteProj_finiteEmbedding_of_ne (fun h => hp (Subtype.ext h)), map_one]
    · rw [finiteProj_finiteEmbedding_of_ne hu]
      apply Finset.prod_eq_one
      intro p _
      have hp : p.val ≠ w.val := by
        intro hp
        have h₁ := (finitePlace_under_eq_iff p.val u).mpr inferInstance
        have h₂ := (finitePlace_under_eq_iff w.val v).mpr inferInstance
        exact hu (h₁.symm.trans ((congrArg (HeightOneSpectrum.under (𝓞 K)) hp).trans h₂))
      rw [finiteProj_finiteEmbedding_of_ne hp, map_one]
  · intro u
    rw [infiniteProj_ideleNorm, infiniteProj_finiteEmbedding]
    have h : (fun p : infinitePlacesAbove L u => infiniteProj p.val (finiteEmbedding w.val x)) = 1 := by
      funext p
      exact infiniteProj_finiteEmbedding L p.val w.val x
    rw [h, map_one]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.ideleNorm_finiteEmbedding

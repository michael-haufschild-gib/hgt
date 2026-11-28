import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionBaseChange

/-! Maps of finite completions compose along towers of places. -/

noncomputable section

open NumberField IsDedekindDomain
open scoped GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable {K M L : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L]
  [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
  (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 M)) (w : HeightOneSpectrum (𝓞 L))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal] [w.asIdeal.LiesOver v.asIdeal]

theorem finiteCompletionMap_tower (x : v.adicCompletion K) :
    AdicLiesOver.completionMap v w x =
      AdicLiesOver.completionMap u w (AdicLiesOver.completionMap v u x) := by
  let f := AdicLiesOver.completionMap v w
  let g := (AdicLiesOver.completionMap u w).comp (AdicLiesOver.completionMap v u)
  have hf : Continuous f := AdicLiesOver.continuous_completionMap v w
  have hg : Continuous g := (AdicLiesOver.continuous_completionMap u w).comp
    (AdicLiesOver.continuous_completionMap v u)
  have h := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) (K := K) v).equalizer hf hg
    (funext fun a => by
      change AdicLiesOver.completionMap v w (algebraMap K (v.adicCompletion K) a) =
        AdicLiesOver.completionMap u w
          (AdicLiesOver.completionMap v u (algebraMap K (v.adicCompletion K) a))
      rw [AdicLiesOver.completionMap_algebraMap v w, AdicLiesOver.completionMap_algebraMap v u,
        AdicLiesOver.completionMap_algebraMap u w, IsScalarTower.algebraMap_apply K M L])
  exact congrFun h x

theorem finiteCompletion_isScalarTower :
    IsScalarTower (v.adicCompletion K) (u.adicCompletion M) (w.adicCompletion L) :=
  .of_algebraMap_eq (finiteCompletionMap_tower v u w)

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteCompletion_isScalarTower

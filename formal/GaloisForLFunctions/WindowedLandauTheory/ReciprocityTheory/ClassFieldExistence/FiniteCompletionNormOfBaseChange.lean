import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionTensorEquivalence
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.AlgebraNormOfProducts

/-! The global field norm becomes the product of local norms after
embedding into a finite completion. -/

noncomputable section

open NumberField IsDedekindDomain
open scoped GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem algebraMap_norm_eq_prod_finiteCompletion_norms (v : HeightOneSpectrum (𝓞 K)) (x : L) :
    algebraMap K (v.adicCompletion K) (Algebra.norm K x) =
      ∏ w : finitePlacesAbove L v,
        Algebra.norm (v.adicCompletion K) (algebraMap L (w.val.adicCompletion L) x) := by
  rw [← algebraNorm_one_tmul, ← Algebra.norm_eq_of_algEquiv (finiteCompletionTensorEquiv L v),
    finiteCompletionTensorEquiv_one_tmul, algebraNorm_pi]
  rfl

end GlobalTheory.Reciprocity

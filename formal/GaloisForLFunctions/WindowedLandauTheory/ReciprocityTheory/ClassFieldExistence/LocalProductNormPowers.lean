import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicProductNorm

/-! Applying the norm to a scalar in every component gives the power
by the global degree, using the sum of the local degrees. -/

noncomputable section

open NumberField IsDedekindDomain WithZero
open scoped GlobalTheory.Reciprocity.AdicLiesOver NumberField.LiesOver

namespace GlobalTheory.Reciprocity

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem finiteLocalNorm_of_scalar (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    finiteLocalNorm L v (fun w =>
      Units.map (algebraMap (v.adicCompletion K) (w.val.adicCompletion L)).toMonoidHom x) =
      x ^ Module.finrank K L := by
  apply Units.ext
  rw [coe_finiteLocalNorm, Units.val_pow_eq_pow_val, ← sum_finiteCompletion_finrank L v,
    ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun w _ => Algebra.norm_algebraMap (x : v.adicCompletion K)

theorem infiniteLocalNorm_of_scalar (v : InfinitePlace K) (x : v.Completionˣ) :
    infiniteLocalNorm L v (fun w =>
      Units.map (algebraMap v.Completion w.val.Completion).toMonoidHom x) =
      x ^ Module.finrank K L := by
  apply Units.ext
  rw [coe_infiniteLocalNorm, Units.val_pow_eq_pow_val, ← sum_infiniteCompletion_finrank L v,
    ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun w _ => Algebra.norm_algebraMap (x : v.Completion)

theorem completedScalar_mem_unitsLevel_zero (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (x : (v.adicCompletion K)ˣ) (hx : x ∈ unitsLevel v 0) :
    Units.map (algebraMap (v.adicCompletion K) (w.adicCompletion L)).toMonoidHom x ∈ unitsLevel w 0 := by
  have he : Valued.v (AdicLiesOver.completionMap v w x.val) = 1 := by
    rw [AdicLiesOver.valued_completionMap, (mem_unitsLevel.mp hx).1, one_pow]
  refine mem_unitsLevel.mpr ⟨he, ?_⟩
  change Valued.v (AdicLiesOver.completionMap v w x.val - 1) ≤ exp (-(0 : ℤ))
  simpa only [neg_zero, exp_zero] using Valuation.map_sub_le (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰)
    he.le (show Valued.v (1 : w.adicCompletion L) ≤ 1 by simp)

open Classical in
theorem finiteLocalNorm_mulSingle (v : HeightOneSpectrum (𝓞 K))
    (w : finitePlacesAbove L v) (x : (w.val.adicCompletion L)ˣ) :
    finiteLocalNorm L v (Pi.mulSingle w x) = Units.map (Algebra.norm (v.adicCompletion K)) x := by
  apply Units.ext
  rw [coe_finiteLocalNorm, Fintype.prod_eq_single w]
  · rw [Pi.mulSingle_eq_same, Units.coe_map]
  · intro w' hw
    rw [Pi.mulSingle_eq_of_ne hw, Units.val_one, map_one]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteLocalNorm_of_scalar
#print axioms GlobalTheory.Reciprocity.infiniteLocalNorm_of_scalar

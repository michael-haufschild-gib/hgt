import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.RamificationInertia.Valuation

/-! An extension of number fields induces a map of completions at
two places related by lying over. Its valuation raises to the
ramification index. -/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero

namespace GlobalTheory.Reciprocity.AdicLiesOver

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The map of completions induced by the number-field embedding. -/
def completionMap : v.adicCompletion K →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
        (uniformContinuous_algebraMap_liesOver K L v w).continuous).comp
      (adicCompletion.equiv K v).toRingHom)

theorem continuous_completionMap : Continuous (completionMap v w) :=
  (adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v)

theorem completionMap_algebraMap (x : K) :
    completionMap v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  apply adicCompletion.ext
  change UniformSpace.Completion.mapRingHom _
    (uniformContinuous_algebraMap_liesOver K L v w).continuous
    ((algebraMap K (WithVal (v.valuation K)) x : WithVal (v.valuation K)) :
      UniformSpace.Completion (WithVal (v.valuation K))) = _
  rw [UniformSpace.Completion.mapRingHom_coe]
  rfl

scoped instance : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (completionMap v w).toAlgebra

scoped instance : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun x => ((completionMap_algebraMap v w x).trans
    (IsScalarTower.algebraMap_apply K L (w.adicCompletion L) x).symm).symm

scoped instance : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) :=
  continuousSMul_of_algebraMap _ _ (continuous_completionMap v w)

theorem valued_completionMap (x : v.adicCompletion K) :
    Valued.v (completionMap v w x) = Valued.v x ^ v.asIdeal.ramificationIdx' w.asIdeal := by
  have he : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot
  rcases eq_or_ne x 0 with rfl | hx
  · simp [he]
  have hx' : Valued.v x ≠ 0 := by simpa using hx
  have hy : Valued.v (completionMap v w x) ≠ 0 := by simpa using hx
  have h1 := Valued.locally_const hx'
  have h2 := (continuous_completionMap v w).continuousAt.preimage_mem_nhds (Valued.locally_const hy)
  obtain ⟨k, hk1, hk2⟩ := (denseRange_algebraMap (R := 𝓞 K) (K := K) v).mem_nhds
    (Filter.inter_mem h1 h2)
  simp only [Set.mem_preimage] at hk1 hk2
  rw [← hk1, ← hk2, completionMap_algebraMap]
  erw [valuedAdicCompletion_eq_valuation' w, valuedAdicCompletion_eq_valuation' v]
  exact (valuation_liesOver L v w k).symm

theorem mapsTo_completionIntegers :
    Set.MapsTo (completionMap v w) (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  intro x hx
  rw [SetLike.mem_coe, mem_adicCompletionIntegers] at hx ⊢
  rw [valued_completionMap]
  exact pow_le_one' hx _

end GlobalTheory.Reciprocity.AdicLiesOver

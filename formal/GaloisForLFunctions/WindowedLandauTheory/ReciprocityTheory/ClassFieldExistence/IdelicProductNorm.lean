import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionNormOfBaseChange
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionNormValuation
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.InfiniteCompletionNormOfBaseChange
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FinitePlaceFibres
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdelesFromLocalUnits
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.LocalUnitFiltration

/-! The idelic norm is the product of the local norms above each place.
A product of integral finite units has integral norm. -/

noncomputable section

open NumberField IsDedekindDomain Filter WithZero
open scoped GlobalTheory.Reciprocity.AdicLiesOver NumberField.LiesOver

namespace GlobalTheory.Reciprocity

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]

/-- The product of the finite local norms above a base place. -/
def finiteLocalNorm (v : HeightOneSpectrum (𝓞 K)) :
    ((w : finitePlacesAbove L v) → (w.val.adicCompletion L)ˣ) →* (v.adicCompletion K)ˣ where
  toFun x := ∏ w, Units.map (Algebra.norm (v.adicCompletion K)) (x w)
  map_one' := by simp
  map_mul' x y := by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]

@[simp] theorem coe_finiteLocalNorm (v : HeightOneSpectrum (𝓞 K))
    (x : ∀ w : finitePlacesAbove L v, (w.val.adicCompletion L)ˣ) :
    (finiteLocalNorm L v x : v.adicCompletion K) =
      ∏ w : finitePlacesAbove L v, Algebra.norm (v.adicCompletion K) (x w : w.val.adicCompletion L) := by
  simp [finiteLocalNorm, Units.coe_prod]

/-- The product of the infinite local norms above a base place. -/
def infiniteLocalNorm (v : InfinitePlace K) :
    ((w : infinitePlacesAbove L v) → w.val.Completionˣ) →* v.Completionˣ where
  toFun x := ∏ w, Units.map (Algebra.norm v.Completion) (x w)
  map_one' := by simp
  map_mul' x y := by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]

@[simp] theorem coe_infiniteLocalNorm (v : InfinitePlace K)
    (x : ∀ w : infinitePlacesAbove L v, w.val.Completionˣ) :
    (infiniteLocalNorm L v x : v.Completion) =
      ∏ w : infinitePlacesAbove L v, Algebra.norm v.Completion (x w : w.val.Completion) := by
  simp [infiniteLocalNorm, Units.coe_prod]

variable {L} [IsGalois K L]

theorem finiteLocalNorm_mem_integralUnits (v : HeightOneSpectrum (𝓞 K))
    (x : ∀ w : finitePlacesAbove L v, (w.val.adicCompletion L)ˣ)
    (hx : ∀ w, x w ∈ (Submonoid.ofClass (w.val.adicCompletionIntegers L)).units) :
    finiteLocalNorm L v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  rw [← unitsLevel_zero, mem_unitsLevel]
  have h : Valued.v (finiteLocalNorm L v x : v.adicCompletion K) = 1 := by
    rw [coe_finiteLocalNorm, map_prod]
    apply Finset.prod_eq_one
    intro w _
    have hw := hx w
    rw [← unitsLevel_zero, mem_unitsLevel] at hw
    rw [valued_finiteCompletion_norm v w.val, hw.1, one_pow]
  exact ⟨h, by simpa only [Nat.cast_zero, neg_zero, exp_zero] using
    Valuation.map_sub_le _ h.le (show Valued.v (1 : v.adicCompletion K) ≤ 1 by simp)⟩

open IdeleGroup

/-- The norm of an idele, with each coordinate given by the product over its fibre. -/
def ideleNorm : IdeleGroup L →* IdeleGroup K where
  toFun y := ofLocalUnits
    ⟨fun v => finiteLocalNorm L v (fun w => finiteProj w.val y),
      (eventually_forall_finitePlacesAbove (K := K) (eventually_finiteProj_integralUnits y)).mono
        (fun v hv => finiteLocalNorm_mem_integralUnits v _ hv)⟩
    (fun v => infiniteLocalNorm L v (fun w => infiniteProj w.val y))
  map_one' := by
    apply ext_of_localUnits <;> intro v
    · rw [finiteProj_ofLocalUnits]
      change finiteLocalNorm L v (fun w => finiteProj w.val (1 : IdeleGroup L)) = _
      simp only [map_one, ← Pi.one_def]
    · rw [infiniteProj_ofLocalUnits]
      simp only [map_one, ← Pi.one_def]
  map_mul' x y := by
    apply ext_of_localUnits <;> intro v
    · simp only [finiteProj_ofLocalUnits, map_mul]
      exact map_mul (finiteLocalNorm L v)
        (fun w : finitePlacesAbove L v => finiteProj w.val x)
        (fun w : finitePlacesAbove L v => finiteProj w.val y)
    · simp only [infiniteProj_ofLocalUnits, map_mul]
      exact map_mul (infiniteLocalNorm L v)
        (fun w : infinitePlacesAbove L v => infiniteProj w.val x)
        (fun w : infinitePlacesAbove L v => infiniteProj w.val y)

@[simp] theorem finiteProj_ideleNorm (y : IdeleGroup L) (v : HeightOneSpectrum (𝓞 K)) :
    finiteProj v (ideleNorm y) = finiteLocalNorm L v (fun w => finiteProj w.val y) :=
  finiteProj_ofLocalUnits _ _ _

@[simp] theorem infiniteProj_ideleNorm (y : IdeleGroup L) (v : InfinitePlace K) :
    infiniteProj v (ideleNorm y) = infiniteLocalNorm L v (fun w => infiniteProj w.val y) :=
  infiniteProj_ofLocalUnits _ _ _

theorem ideleNorm_diagonal (y : Lˣ) :
    ideleNorm (K := K) (diagonal L y) = diagonal K (Units.map (Algebra.norm K) y) := by
  apply ext_of_localUnits
  · intro v
    apply Units.ext
    rw [finiteProj_ideleNorm, coe_finiteLocalNorm, coe_finiteProj_diagonal, Units.coe_map]
    change _ = algebraMap K (v.adicCompletion K) (Algebra.norm K (y : L))
    rw [algebraMap_norm_eq_prod_finiteCompletion_norms]
    exact Finset.prod_congr rfl fun w _ => rfl
  · intro v
    apply Units.ext
    rw [infiniteProj_ideleNorm, coe_infiniteLocalNorm]
    change _ = algebraMap K v.Completion (Algebra.norm K (y : L))
    rw [algebraMap_norm_eq_prod_infiniteCompletion_norms]
    exact Finset.prod_congr rfl fun w _ => rfl

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.ideleNorm_diagonal

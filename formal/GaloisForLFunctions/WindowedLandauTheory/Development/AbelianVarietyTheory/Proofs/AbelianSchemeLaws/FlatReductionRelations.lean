import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic.Abel

/-! A relation in a flat quotient module lifts to a tensor relation upstairs. -/

open LinearMap TensorProduct
open scoped Pointwise

namespace GlobalTheory.FiniteFibreFlat

variable {A C M M' F : Type*} [CommRing A] [CommRing C] [Algebra A C]
  [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] [Module C M']
  [IsScalarTower A C M'] [AddCommGroup F] [Module A F]

/-- If the reduction of `M` modulo `I` is flat, lift a tensor relation into the
submodule of vectors whose coefficients map into `I`. -/
theorem mem_range_lTensor_comap_of_flat_reduction {I : Ideal A}
    (hC : Function.Surjective (algebraMap A C)) (hI : RingHom.ker (algebraMap A C) = I)
    [Module.Flat C M'] (q : M →ₗ[A] M') (hq : Function.Surjective q)
    (hker : ker q = I • (⊤ : Submodule A M)) (f : F →ₗ[A] A) (x : M ⊗[A] F)
    (hx : TensorProduct.rid A M (f.lTensor M x) ∈ I • (⊤ : Submodule A M)) :
    x ∈ range ((Submodule.comap f I).subtype.lTensor M) := by
  obtain ⟨k, m, v, rfl⟩ := TensorProduct.exists_sum_tmul_eq x
  rw [← hker, mem_ker] at hx
  have hz : ∑ i, algebraMap A C (f (v i)) • q (m i) = 0 := by
    simpa [map_sum] using hx
  obtain ⟨l, c, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hz
  choose a ha using fun i j => hC (c i j)
  choose z hz using fun j => hq (y j)
  have hd (i : Fin k) : m i - ∑ j, a i j • z j ∈ I • (⊤ : Submodule A M) := by
    rw [← hker, mem_ker, map_sub, show q (m i) = _ from hy i, map_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hz, ← ha, algebraMap_smul]
  have hsum : ∑ i, m i ⊗ₜ[A] v i = ∑ i, (m i - ∑ j, a i j • z j) ⊗ₜ[A] v i +
      ∑ j, z j ⊗ₜ[A] (∑ i, a i j • v i) := by
    simp only [sub_tmul, sum_tmul, tmul_sum, smul_tmul, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun j i => z j ⊗ₜ[A] (a i j • v i))]
    abel
  rw [hsum]
  refine add_mem (Submodule.sum_mem _ fun i _ => ?_) (Submodule.sum_mem _ fun j _ => ?_)
  · refine Submodule.smul_induction_on (p := fun d => d ⊗ₜ[A] v i ∈
      range ((Submodule.comap f I).subtype.lTensor M)) (hd i) ?_ ?_
    · intro r hr n _
      refine ⟨n ⊗ₜ ⟨r • v i, ?_⟩, ?_⟩
      · simpa using I.mul_mem_right _ hr
      · simp [smul_tmul]
    · intro x y hx hy
      rw [add_tmul]
      exact add_mem hx hy
  · refine ⟨z j ⊗ₜ ⟨∑ i, a i j • v i, ?_⟩, by simp⟩
    rw [Submodule.mem_comap, ← hI]
    change algebraMap A C _ = 0
    rw [← hc j]
    simp [map_sum, ha, mul_comm]

end GlobalTheory.FiniteFibreFlat

import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.AlgebraNormOfProducts
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.MultiplicativeWeakApproximation
import Mathlib.NumberTheory.NumberField.Completion.Ramification

/-! Scalar extension at an infinite place decomposes into the completions
above it, so the field norm becomes the product of their norms. -/

noncomputable section

open NumberField IsDedekindDomain TensorProduct
open scoped TensorProduct NumberField.LiesOver

namespace GlobalTheory.Reciprocity

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (L) (v : InfinitePlace K)

/-- The finite set of infinite places of L over v. -/
def infinitePlacesAbove : Finset (InfinitePlace L) := by
  classical
  exact (v.placesOver L).toFinset

omit [NumberField K] in
theorem mem_infinitePlacesAbove (w : InfinitePlace L) :
    w ∈ infinitePlacesAbove L v ↔ w.1.LiesOver v.1 := by
  classical
  change w ∈ (v.placesOver L).toFinset ↔ w.1.LiesOver v.1
  exact Set.mem_toFinset

instance (w : infinitePlacesAbove L v) : w.val.1.LiesOver v.1 :=
  (mem_infinitePlacesAbove L v w.val).mp w.2

instance (w : infinitePlacesAbove L v) : FiniteDimensional v.Completion w.val.Completion := by
  apply Module.finite_of_finrank_pos
  by_cases h : w.val.IsUnramified K
  · rw [InfinitePlace.Completion.finrank_eq_one_of_isUnramified v h]
    exact Nat.one_pos
  · rw [InfinitePlace.Completion.finrank_eq_two_of_isRamified v
      (InfinitePlace.isRamified_iff.mpr (InfinitePlace.not_isUnramified_iff.mp h))]
    exact Nat.two_pos

local instance (w : InfinitePlace L) : IsScalarTower K L w.Completion :=
  .of_algebraMap_eq fun _ => rfl

/-- The product of the completions above an infinite place. -/
abbrev InfiniteCompletionsAbove : Type _ :=
  (w : infinitePlacesAbove L v) → w.val.Completion

private def infiniteCompletionTensorMap :
    v.Completion ⊗[K] L →ₐ[v.Completion] InfiniteCompletionsAbove L v :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom K L _)
    (fun _ _ => Commute.all _ _)

private theorem infiniteCompletionTensorMap_one_tmul (x : L) :
    infiniteCompletionTensorMap L v (1 ⊗ₜ x) =
      algebraMap L (InfiniteCompletionsAbove L v) x := by
  simp [infiniteCompletionTensorMap]

private theorem infiniteCompletionTensorMap_surjective :
    Function.Surjective (infiniteCompletionTensorMap L v) := by
  letI : NontriviallyNormedField v.Completion :=
    { non_trivial := by
        refine ⟨2, ?_⟩
        have he := (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
          (map_zero _) (2 : v.Completion)
        rw [← he, map_ofNat]
        norm_num }
  let f := (infiniteCompletionTensorMap L v).toLinearMap
  have hc : IsClosed (f.range : Set (InfiniteCompletionsAbove L v)) :=
    f.range.closed_of_finiteDimensional
  have hd : DenseRange (algebraMap L (InfiniteCompletionsAbove L v)) :=
    Prod.snd_surjective.denseRange.comp
      (denseRange_algebraMap_prod_pi (K := L) (∅ : Finset (HeightOneSpectrum (𝓞 L)))
        (infinitePlacesAbove L v)) continuous_snd
  have hf : Dense (f.range : Set (InfiniteCompletionsAbove L v)) := by
    refine hd.mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, infiniteCompletionTensorMap_one_tmul L v x⟩
  exact Set.range_eq_univ.mp (hc.closure_eq.symm.trans hf.closure_eq)

theorem sum_infiniteCompletion_finrank :
    ∑ w : infinitePlacesAbove L v, Module.finrank v.Completion w.val.Completion =
      Module.finrank K L := by
  classical
  rw [← InfinitePlace.sum_inertiaDeg_eq_finrank K L v]
  change _ = ∑ w ∈ infinitePlacesAbove L v, v.inertiaDeg w
  rw [← Finset.sum_attach (s := infinitePlacesAbove L v)]
  exact Finset.sum_congr rfl fun w _ => (InfinitePlace.inertiaDeg_eq_finrank v w.val).symm

private def infiniteCompletionTensorEquiv :
    v.Completion ⊗[K] L ≃ₐ[v.Completion] InfiniteCompletionsAbove L v :=
  AlgEquiv.ofBijective (infiniteCompletionTensorMap L v) ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (infiniteCompletionTensorMap L v).toLinearMap)
      (by rw [Module.finrank_baseChange, Module.finrank_pi_fintype, sum_infiniteCompletion_finrank])).mpr
      (infiniteCompletionTensorMap_surjective L v),
    infiniteCompletionTensorMap_surjective L v⟩

theorem algebraMap_norm_eq_prod_infiniteCompletion_norms (x : L) :
    algebraMap K v.Completion (Algebra.norm K x) =
      ∏ w : infinitePlacesAbove L v, Algebra.norm v.Completion (algebraMap L w.val.Completion x) := by
  rw [← algebraNorm_one_tmul, ← Algebra.norm_eq_of_algEquiv (infiniteCompletionTensorEquiv L v)]
  change Algebra.norm v.Completion (infiniteCompletionTensorMap L v (1 ⊗ₜ x)) = _
  rw [infiniteCompletionTensorMap_one_tmul, algebraNorm_pi]
  rfl

end GlobalTheory.Reciprocity

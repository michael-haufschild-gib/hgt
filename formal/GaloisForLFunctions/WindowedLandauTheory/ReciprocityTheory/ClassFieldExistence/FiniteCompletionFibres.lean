import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionBaseChange
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.MultiplicativeWeakApproximation
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! The diagonal field is dense in the product of the completions
above a finite prime. Scalar extension maps onto that product. -/

noncomputable section

open NumberField IsDedekindDomain TensorProduct Module
open scoped TensorProduct GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (L) (v : HeightOneSpectrum (𝓞 K))

/-- The finite set of places of L over v. -/
def finitePlacesAbove : Finset (HeightOneSpectrum (𝓞 L)) := by
  letI := v.isMaximal
  exact ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).preimage
    (f := fun w : HeightOneSpectrum (𝓞 L) => w.asIdeal)
    (fun a _ b _ h => HeightOneSpectrum.ext h)).toFinset

theorem mem_finitePlacesAbove (w : HeightOneSpectrum (𝓞 L)) :
    w ∈ finitePlacesAbove L v ↔ w.asIdeal.LiesOver v.asIdeal := by
  rw [finitePlacesAbove, Set.Finite.mem_toFinset]
  exact ⟨fun h => h.2, fun h => ⟨w.isPrime, h⟩⟩

instance (w : finitePlacesAbove L v) : w.val.asIdeal.LiesOver v.asIdeal :=
  (mem_finitePlacesAbove L v w.val).mp w.2

/-- The product of the completions at the places over v. -/
abbrev FiniteCompletionsAbove : Type _ :=
  (w : finitePlacesAbove L v) → w.val.adicCompletion L

/-- The scalar extension map to the product of completions. -/
def finiteCompletionTensorMap :
    v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K] FiniteCompletionsAbove L v :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom K L _)
    (fun _ _ => Commute.all _ _)

@[simp]
theorem finiteCompletionTensorMap_tmul (a : v.adicCompletion K) (x : L) :
    finiteCompletionTensorMap L v (a ⊗ₜ x) =
      algebraMap (v.adicCompletion K) (FiniteCompletionsAbove L v) a *
        algebraMap L (FiniteCompletionsAbove L v) x := by
  simp [finiteCompletionTensorMap]

theorem denseRange_algebraMap_finiteCompletionsAbove :
    DenseRange (algebraMap L (FiniteCompletionsAbove L v)) := by
  have h := denseRange_algebraMap_prod_pi (K := L) (finitePlacesAbove L v)
    (∅ : Finset (InfinitePlace L))
  exact Prod.fst_surjective.denseRange.comp h continuous_fst

open scoped Valued in
theorem finiteCompletionTensorMap_surjective : Function.Surjective (finiteCompletionTensorMap L v) := by
  let f := finiteCompletionTensorMap L v
  have hclosed : IsClosed (LinearMap.range f.toLinearMap : Set (FiniteCompletionsAbove L v)) :=
    Submodule.closed_of_finiteDimensional _
  have hdense : Dense (Set.range f) := by
    refine (denseRange_algebraMap_finiteCompletionsAbove L v).mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp [f]⟩
  have hclosed' : IsClosed (Set.range f) := by
    change IsClosed (Set.range f.toLinearMap)
    rwa [← LinearMap.coe_range]
  exact Set.range_eq_univ.mp (hclosed'.closure_eq.symm.trans hdense.closure_eq)

end GlobalTheory.Reciprocity

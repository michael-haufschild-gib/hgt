import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionFibres
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionDegreeLowerBound
import Mathlib.RingTheory.RamificationInertia.Basic

/-! The degree formula identifies scalar extension at a finite place
with the product of the completions above it. -/

noncomputable section

open NumberField IsDedekindDomain TensorProduct Module
open scoped TensorProduct GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (L) (v : HeightOneSpectrum (𝓞 K))

private def finitePlacesAboveEquivPrimesOver : (finitePlacesAbove L v : Type _) ≃ v.asIdeal.primesOver (𝓞 L) where
  toFun w := ⟨w.val.asIdeal, w.val.isPrime, inferInstance⟩
  invFun q := by
    letI : q.val.LiesOver v.asIdeal := q.2.2
    let w : HeightOneSpectrum (𝓞 L) :=
      ⟨q.val, q.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.val⟩
    exact ⟨w, (mem_finitePlacesAbove L v w).mpr inferInstance⟩
  left_inv w := Subtype.ext (HeightOneSpectrum.ext rfl)
  right_inv q := Subtype.ext rfl

private theorem sum_finite_ramification_mul_inertia :
    ∑ w : finitePlacesAbove L v, w.val.asIdeal.ramificationIdx (𝓞 K) *
      w.val.asIdeal.inertiaDeg (𝓞 K) = Module.finrank K L := by
  letI := v.isMaximal
  letI : Fintype (v.asIdeal.primesOver (𝓞 L)) :=
    (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).fintype
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 K) K (𝓞 L) L,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 L)]
  exact Fintype.sum_equiv (finitePlacesAboveEquivPrimesOver L v) _ _ (fun _ => rfl)

/-- The local degrees over one finite place sum to the global degree. -/
theorem sum_finiteCompletion_finrank :
    ∑ w : finitePlacesAbove L v, Module.finrank (v.adicCompletion K) (w.val.adicCompletion L) =
      Module.finrank K L := by
  refine le_antisymm ?_ ?_
  · rw [← Module.finrank_pi_fintype]
    calc _ ≤ Module.finrank (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) :=
          LinearMap.finrank_le_finrank_of_surjective
            (f := (finiteCompletionTensorMap L v).toLinearMap) (finiteCompletionTensorMap_surjective L v)
      _ = Module.finrank K L := Module.finrank_baseChange
  · rw [← sum_finite_ramification_mul_inertia L v]
    exact Finset.sum_le_sum fun w _ => ramificationIdx_mul_inertiaDeg_le_finrank v w.val

theorem finiteCompletion_finrank_eq_ramification_mul_inertia (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  have h := (Finset.sum_eq_sum_iff_of_le
    (fun (q : finitePlacesAbove L v) _ => ramificationIdx_mul_inertiaDeg_le_finrank v q.val)).1
    (by rw [sum_finite_ramification_mul_inertia, sum_finiteCompletion_finrank])
  exact (h ⟨w, (mem_finitePlacesAbove L v w).mpr inferInstance⟩ (Finset.mem_univ _)).symm

/-- Scalar extension agrees with the product of completions at every finite place. -/
def finiteCompletionTensorEquiv :
    v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K] FiniteCompletionsAbove L v :=
  AlgEquiv.ofBijective (finiteCompletionTensorMap L v) ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (finiteCompletionTensorMap L v).toLinearMap)
      (by rw [Module.finrank_baseChange, Module.finrank_pi_fintype, sum_finiteCompletion_finrank])).mpr
      (finiteCompletionTensorMap_surjective L v),
    finiteCompletionTensorMap_surjective L v⟩

@[simp]
theorem finiteCompletionTensorEquiv_one_tmul (x : L) :
    finiteCompletionTensorEquiv L v (1 ⊗ₜ x) =
      algebraMap L (FiniteCompletionsAbove L v) x := by
  change finiteCompletionTensorMap L v (1 ⊗ₜ x) = _
  rw [finiteCompletionTensorMap_tmul, map_one, one_mul]

end GlobalTheory.Reciprocity

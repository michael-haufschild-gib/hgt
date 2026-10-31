import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteColumns
import GaloisForLFunctions.HTGeometry.ExponentialKernelAlternatingInertia

/-!
# Finite-rank perturbations preserve finite negative index

Evaluation bounds every sampled Gram rank by the full column-space dimension. Intersecting a
negative subspace with the correction's kernel then bounds the index after subtraction.
-/

open Module Matrix
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz
variable {G : Type*} [Group G]

/-- Sampling a finite column space cannot increase its dimension. -/
theorem rank_gram_le_finrank_columnSpan (k : G → ℂ)
    [Module.Finite ℂ (kernelColumnSpan k)] {ι : Type*} [Fintype ι] (x : ι → G) :
    (gram k x).rank ≤ finrank ℂ (kernelColumnSpan k) := by
  let F := (LinearMap.funLeft ℂ ℂ x).domRestrict (kernelColumnSpan k)
  rw [Matrix.rank_eq_finrank_span_cols]
  apply (Submodule.finrank_mono (t := LinearMap.range F) ?_).trans
    (LinearMap.finrank_range_le F)
  apply Submodule.span_le.mpr
  rintro y ⟨i, rfl⟩
  exact ⟨⟨kernelColumn k (x i), Submodule.subset_span ⟨x i, rfl⟩⟩, rfl⟩

/-- Subtracting a finite-rank kernel changes the negative index by at most its rank. -/
theorem negIndex_sub_le_add_finrank (k q : G → ℂ)
    [Module.Finite ℂ (kernelColumnSpan q)] :
    negIndex (fun g => k g - q g) ≤ negIndex k + finrank ℂ (kernelColumnSpan q) := by
  apply negIndex_le_iff.mpr
  intro n x
  have h := hermNegIndex_le_add_rank (gram (fun g => k g - q g) x) (gram q x)
  have he : gram (fun g => k g - q g) x + gram q x = gram k x := by
    ext i j
    exact sub_add_cancel _ _
  rw [he] at h
  have hr := rank_gram_le_finrank_columnSpan q x
  calc
    (hermNegIndex (gram (fun g => k g - q g) x) : ℕ∞) ≤
        (hermNegIndex (gram k x) : ℕ∞) + (gram q x).rank := by exact_mod_cast h
    _ ≤ negIndex k + finrank ℂ (kernelColumnSpan q) :=
      add_le_add (hermNegIndex_gram_le_negIndex k x) (Nat.cast_le.mpr hr)

#print axioms rank_gram_le_finrank_columnSpan
#print axioms negIndex_sub_le_add_finrank
end GaloisForLFunctions.HeckeKreinToeplitz

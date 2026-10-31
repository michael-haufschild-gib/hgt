import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteRankPerturbations

/-!
# Stability of finite negative index under finite-rank changes

The rank perturbation inequality in both directions shows that a finite-column-rank
change preserves finiteness of negative index.
-/

open Module Matrix
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz
variable {G : Type*} [Group G]

/-- The reverse rank perturbation bound uses the negative of the correction matrix. -/
theorem negIndex_le_sub_add_finrank (k q : G → ℂ)
    [Module.Finite ℂ (kernelColumnSpan q)] :
    negIndex k ≤ negIndex (fun g => k g - q g) + finrank ℂ (kernelColumnSpan q) := by
  apply negIndex_le_iff.mpr
  intro n x
  have h := hermNegIndex_le_add_rank (gram k x) (-(gram q x))
  have he : gram k x + -(gram q x) = gram (fun g => k g - q g) x := by
    ext i j
    exact (sub_eq_add_neg _ _).symm
  rw [he] at h
  have hrneg : (-(gram q x)).rank ≤ (gram q x).rank := by
    rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
    apply Submodule.finrank_mono
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hr := hrneg.trans (rank_gram_le_finrank_columnSpan q x)
  calc
    (hermNegIndex (gram k x) : ℕ∞) ≤
        (hermNegIndex (gram (fun g => k g - q g) x) : ℕ∞) + (-(gram q x)).rank := by
      exact_mod_cast h
    _ ≤ negIndex (fun g => k g - q g) + finrank ℂ (kernelColumnSpan q) :=
      add_le_add (hermNegIndex_gram_le_negIndex _ x) (Nat.cast_le.mpr hr)

/-- A finite-rank change preserves finiteness of negative index. -/
theorem negIndex_sub_lt_top_iff (k q : G → ℂ)
    [Module.Finite ℂ (kernelColumnSpan q)] :
    negIndex (fun g => k g - q g) < ⊤ ↔ negIndex k < ⊤ := by
  constructor
  · intro h
    exact lt_of_le_of_lt (negIndex_le_sub_add_finrank k q)
      (by simpa only [ENat.add_lt_top, ENat.coe_lt_top, and_true] using h)
  · intro h
    exact lt_of_le_of_lt (negIndex_sub_le_add_finrank k q)
      (by simpa only [ENat.add_lt_top, ENat.coe_lt_top, and_true] using h)

#print axioms negIndex_le_sub_add_finrank
#print axioms negIndex_sub_lt_top_iff
end GaloisForLFunctions.HeckeKreinToeplitz

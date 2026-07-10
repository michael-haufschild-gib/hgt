import GaloisForLFunctions.RHTower.BakerProof.CoefficientField

/-!
# Normalizing a reduced Baker relation at one coefficient

Dividing by any nonzero pivot coefficient expresses its prime logarithm as an algebraic linear
combination of the remaining logarithms.  The normalized coefficients live in the canonical
coefficient number field, which is the form needed by the auxiliary-function matrix.
-/

open scoped Classical

namespace GaloisForLFunctions.RHTower.BakerProof

/-- The coefficient at `i`, normalized by the nonzero coefficient at `pivot`, inside the canonical
coefficient field. -/
noncomputable def Relation.normalizedCoeff (R : Relation) (pivot i : Fin R.n) :
    R.CoefficientField := R.coeffLift i / R.coeffLift pivot

@[simp] theorem Relation.coeffEmbedding_normalizedCoeff (R : Relation) (pivot i : Fin R.n) :
    R.coeffEmbedding (R.normalizedCoeff pivot i) = R.coeff i / R.coeff pivot := by
  simp [Relation.normalizedCoeff]

/-- Solving the vanishing relation for any chosen prime logarithm.  This is the algebraic
normalization used to expand derivatives of the Baker auxiliary exponential polynomial in the
remaining logarithms. -/
theorem Relation.pivot_log_eq (R : Relation) (pivot : Fin R.n) :
    ((Real.log (R.p pivot) : ℝ) : ℂ) =
      -∑ i ∈ Finset.univ.erase pivot,
        R.coeffEmbedding (R.normalizedCoeff pivot i) * ((Real.log (R.p i) : ℝ) : ℂ) := by
  let L : Fin R.n → ℂ := fun i => ((Real.log (R.p i) : ℝ) : ℂ)
  let S : ℂ := ∑ i ∈ Finset.univ.erase pivot, R.coeff i * L i
  have hdecomp : S + R.coeff pivot * L pivot = 0 := by
    rw [show S = ∑ i ∈ Finset.univ.erase pivot, R.coeff i * L i by rfl]
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ pivot)]
    exact R.vanishes
  have hpivot : R.coeff pivot ≠ 0 := R.coeff_ne_zero pivot
  have hpivotTerm : R.coeff pivot * L pivot = -S :=
    eq_neg_of_add_eq_zero_right hdecomp
  calc
    L pivot = (R.coeff pivot)⁻¹ * (R.coeff pivot * L pivot) := by
      field_simp
    _ = (R.coeff pivot)⁻¹ * (-S) := by rw [hpivotTerm]
    _ = -∑ i ∈ Finset.univ.erase pivot, (R.coeff i / R.coeff pivot) * L i := by
      simp only [S, Finset.mul_sum, mul_neg, neg_inj]
      apply Finset.sum_congr rfl
      intro i hi
      field_simp
    _ = -∑ i ∈ Finset.univ.erase pivot,
        R.coeffEmbedding (R.normalizedCoeff pivot i) * L i := by simp

end GaloisForLFunctions.RHTower.BakerProof

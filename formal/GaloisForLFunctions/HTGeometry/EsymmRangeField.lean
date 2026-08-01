import GaloisForLFunctions.HTGeometry.SymmetricCoefficientFractionModel

/-!
# The coefficient field is exactly the image of the model

Every polynomial in the elementary symmetric functions lies in the field they generate, and every
element of the fraction field is a quotient of two polynomials, so the image of the model is
contained in that field.  With the reverse inclusion already available, the two agree.

Hence the coefficient field of the generic polynomial is isomorphic to a rational function field in
which the top elementary symmetric function is a variable.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K] {d : ℕ}

theorem esymmEmbedding_mem_esymmField (p : MvPolynomial (Fin d) K) :
    esymmEmbedding K d p ∈ esymmField K d := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [esymmEmbedding, MvPolynomial.aeval_C]
      exact (esymmField K d).algebraMap_mem a
  | add q r hq hr =>
      rw [map_add]
      exact add_mem hq hr
  | mul_X q i hq =>
      rw [map_mul]
      refine mul_mem hq ?_
      rw [esymmEmbedding, MvPolynomial.aeval_X]
      exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩

/-- **The image of the model is contained in the coefficient field.** -/
theorem esymmRangeField_le_esymmField : esymmRangeField K d ≤ esymmField K d := by
  rintro _ ⟨u, rfl⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin d) K) u
  rw [map_div₀, esymmFracEmbedding_algebraMap, esymmFracEmbedding_algebraMap]
  exact div_mem (esymmEmbedding_mem_esymmField a) (esymmEmbedding_mem_esymmField b)

/-- **The coefficient field is exactly the image of the model.** -/
theorem esymmRangeField_eq_esymmField : esymmRangeField K d = esymmField K d :=
  le_antisymm esymmRangeField_le_esymmField esymmField_le_esymmRangeField

end GaloisForLFunctions.HTGeometry

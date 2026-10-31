import GaloisForLFunctions.HTGeometry.LoopEisenstein.IntegralLoopBorelIntersection

/-!
# Integral words representing every affine Weyl element

Two constant simple matrices have entries in `{0,1,-1}`. Their images are
integral for every coefficient valuation. The product of the affine word
and inverse finite word projects to one monomial translation, so its
integer powers represent all translation cells without an integrality assumption.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
open scoped WithZero WithZeroMulInt
noncomputable section
variable (F : Type*) [Field F]

private theorem constant_weyl_projection :
    constantLaurentSL2Map F (sl2WeylLower 1) = sl2WeylLower 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [constantLaurentSL2Map_apply,sl2WeylLower]

private theorem swapped_negative_weyl :
    sl2Swap F (sl2WeylLower (-1)) = sl2WeylLower 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2Swap,sl2WeylLower]

private theorem affine_weyl_projection :
    affineConstantSL2Map F (sl2WeylLower 1) = sl2WeylLower (laurentXUnit F) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [affineConstantSL2Map_zero_zero,affineConstantSL2Map_zero_one,
      affineConstantSL2Map_one_zero,affineConstantSL2Map_one_one,sl2WeylLower]

namespace LoopSL2

/-- A finite simple Weyl word integral at every coefficient valuation. -/
def integralFiniteWeylWord : LoopSL2 F := finiteSL2Embedding F (sl2WeylLower 1)

/-- An affine simple Weyl word with projection `W(X)`. -/
def integralAffineWeylWord : LoopSL2 F := affineSimpleSL2Embedding F (sl2WeylLower (-1))

/-- An integral word projecting to the unit monomial translation. -/
def integralTranslationWord : LoopSL2 F :=
  integralAffineWeylWord F * (integralFiniteWeylWord F)⁻¹

/-- Actual integral words for both dihedral families. -/
def integralWeylWord : AffineA1.Weyl → LoopSL2 F
  | .r m => integralTranslationWord F ^ (show ℤ from m)
  | .sr m => integralFiniteWeylWord F * integralTranslationWord F ^ (show ℤ from m)

private theorem projection_integralTranslationWord :
    projection F (integralTranslationWord F) = sl2Diagonal ((laurentXUnit F)⁻¹) := by
  rw [integralTranslationWord,map_mul,map_inv,integralAffineWeylWord,
    integralFiniteWeylWord,projection_affineSimpleSL2Embedding,
    projection_finiteSL2Embedding,swapped_negative_weyl,affine_weyl_projection,
    constant_weyl_projection,sl2WeylLower_inv]
  simpa only [mul_one] using sl2WeylLower_relative (laurentXUnit F) 1

/-- The integral words have exactly the previously defined affine Weyl matrices. -/
theorem projection_integralWeylWord (w : AffineA1.Weyl) :
    projection F (integralWeylWord F w) = affineWeylMatrix F w := by
  have ht (m : ℤ) : projection F (integralTranslationWord F ^ m) =
      sl2Diagonal (laurentXUnit F ^ (-m)) := by
    rw [map_zpow,projection_integralTranslationWord]
    have h := map_zpow (sl2DiagonalHom (LaurentSeries F)) (laurentXUnit F)⁻¹ m
    change sl2Diagonal (((laurentXUnit F)⁻¹)^m) = sl2Diagonal ((laurentXUnit F)⁻¹) ^ m at h
    rw [inv_zpow,←zpow_neg] at h
    exact h.symm
  cases w with
  | r m => exact ht (show ℤ from m)
  | sr m =>
    rw [integralWeylWord,map_mul,ht,integralFiniteWeylWord,
      projection_finiteSL2Embedding,constant_weyl_projection]
    change sl2WeylLower 1 * sl2Diagonal (laurentXUnit F ^ (-(show ℤ from m))) = _
    rw [sl2WeylLower_mul_diagonal,one_mul]
    rfl

variable {F} (v : Valuation F ℤᵐ⁰)

private theorem weyl_one_integral : sl2WeylLower (1 : Fˣ) ∈ valuationIntegralSL2 v := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [sl2WeylLower,Valuation.map_neg]

private theorem weyl_negative_one_integral : sl2WeylLower (-1 : Fˣ) ∈ valuationIntegralSL2 v := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [sl2WeylLower,Valuation.map_neg]

private theorem integralFiniteWeylWord_mem : integralFiniteWeylWord F ∈ integralSimpleLoop v :=
  Subgroup.mem_sup_left ⟨sl2WeylLower 1,weyl_one_integral v,rfl⟩

private theorem integralAffineWeylWord_mem : integralAffineWeylWord F ∈ integralSimpleLoop v :=
  Subgroup.mem_sup_right ⟨sl2WeylLower (-1),weyl_negative_one_integral v,rfl⟩

/-- Every affine Weyl cell has an actual representative integral for every coefficient valuation. -/
theorem integralWeylWord_mem_integralLoop (w : AffineA1.Weyl) :
    integralWeylWord F w ∈ integralLoop v := by
  have ht : integralTranslationWord F ∈ integralSimpleLoop v :=
    (integralSimpleLoop v).mul_mem (integralAffineWeylWord_mem v)
      ((integralSimpleLoop v).inv_mem (integralFiniteWeylWord_mem v))
  apply integralSimpleLoop_le_integralLoop v
  cases w with
  | r m => exact (integralSimpleLoop v).zpow_mem ht (show ℤ from m)
  | sr m =>
    exact (integralSimpleLoop v).mul_mem (integralFiniteWeylWord_mem v)
      ((integralSimpleLoop v).zpow_mem ht (show ℤ from m))

end LoopSL2
end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.projection_integralWeylWord

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.integralWeylWord_mem_integralLoop

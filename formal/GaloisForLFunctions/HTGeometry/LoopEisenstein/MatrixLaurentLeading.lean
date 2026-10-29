import GaloisForLFunctions.HTGeometry.HahnLeadingCoefficient
import GaloisForLFunctions.HTGeometry.LoopEisenstein.ConstantSL2Embedding
import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentIwahoriCriteria

/-!
# Laurent boundary coefficients of rank-two matrices

Entrywise lower degree bounds multiply, and their boundary matrices multiply
with them. The affine simple embedding has a single possible entry in degree
minus one. A nonzero negative boundary excludes the integral Iwahori.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

/-- Entrywise lower bound with its boundary coefficient matrix. -/
def MatrixHasLeadAt (M : Matrix (Fin 2) (Fin 2) (LaurentSeries F))
    (d : ℤ) (A : Matrix (Fin 2) (Fin 2) F) : Prop :=
  ∀ i j, HasLeadAt (M i j) d (A i j)

theorem MatrixHasLeadAt.mul {M N : Matrix (Fin 2) (Fin 2) (LaurentSeries F)}
    {d e : ℤ} {A B : Matrix (Fin 2) (Fin 2) F}
    (hM : MatrixHasLeadAt F M d A) (hN : MatrixHasLeadAt F N e B) :
    MatrixHasLeadAt F (M * N) (d + e) (A * B) := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hM i 0).mul (hN 0 j)).add ((hM i 1).mul (hN 1 j))

theorem hasLeadAt_laurent_single (d : ℤ) (a : F) :
    HasLeadAt (HahnSeries.single d a) d a := by
  constructor
  · intro k hk
    rw [HahnSeries.coeff_single, if_neg (ne_of_lt hk)]
  · rw [HahnSeries.coeff_single, if_pos rfl]

theorem hasLeadAt_laurent_constant (a : F) :
    HasLeadAt (laurentConstantRingHom F a) 0 a := by
  change HasLeadAt (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C a)) 0 a
  rw [HahnSeries.ofPowerSeries_C]
  exact hasLeadAt_laurent_single F 0 a

theorem constantLaurentSL2Map_hasLeadAt (g : SL2 F) :
    MatrixHasLeadAt F (constantLaurentSL2Map F g) 0 g := by
  intro i j
  exact hasLeadAt_laurent_constant F (g i j)

theorem affineUpperParameter_eq_single (a : F) :
    affineUpperParameter F a = HahnSeries.single (-1 : ℤ) a := by
  have hx : (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) =
      HahnSeries.single (-1 : ℤ) (1 : F) := by
    rw [Units.val_inv_eq_inv_val, coe_laurentXUnit]
    rw [← zpow_neg_one, ← RatFunc.single_zpow]
  change (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) *
    HahnSeries.ofPowerSeries ℤ F (PowerSeries.C a) = _
  rw [hx, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply,
    HahnSeries.single_mul_single, add_zero, one_mul]

theorem affineLowerParameter_eq_single (a : F) :
    affineLowerParameter F a = HahnSeries.single (1 : ℤ) a := by
  change (laurentXUnit F : LaurentSeries F) *
    HahnSeries.ofPowerSeries ℤ F (PowerSeries.C a) = _
  rw [coe_laurentXUnit, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply,
    HahnSeries.single_mul_single, add_zero, one_mul]

/-- The only possible coefficient of degree minus one in an affine simple matrix. -/
theorem affineConstantSL2Map_hasLeadAt (g : SL2 F) :
    MatrixHasLeadAt F (affineConstantSL2Map F g) (-1) !![0, g 0 1; 0, 0] := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact (hasLeadAt_laurent_constant F (g 0 0)).mono (by omega)
  · change HasLeadAt (affineUpperParameter F (g 0 1)) (-1) (g 0 1)
    rw [affineUpperParameter_eq_single]
    exact hasLeadAt_laurent_single F _ _
  · change HasLeadAt (affineConstantSL2Map F g 1 0) (-1) 0
    rw [affineConstantSL2Map_one_zero]
    change HasLeadAt (affineLowerParameter F (g 1 0)) (-1) 0
    rw [affineLowerParameter_eq_single]
    exact (hasLeadAt_laurent_single F 1 (g 1 0)).mono (by omega)
  · exact (hasLeadAt_laurent_constant F (g 1 1)).mono (by omega)

/-- A nonzero coefficient matrix in negative degree excludes the integral Iwahori. -/
theorem not_mem_laurentIwahori_of_negative_lead {g : SL2 (LaurentSeries F)}
    {d : ℤ} {A : Matrix (Fin 2) (Fin 2) F} (h : MatrixHasLeadAt F g d A)
    (hd : d < 0) (hA : A ≠ 0) : g ∉ laurentIwahori F := by
  rintro ⟨p, _, hp⟩
  apply hA
  ext i j
  have hc := (h i j).2
  rw [← hp, powerSeriesSL2Map_apply, PowerSeries.coeff_coe, if_pos hd] at hc
  exact hc.symm

/-- Invertible constant factors cannot annihilate a nonzero boundary matrix. -/
theorem sl2_mul_matrix_ne_zero (g : SL2 F) {A : Matrix (Fin 2) (Fin 2) F}
    (hA : A ≠ 0) : (g : Matrix (Fin 2) (Fin 2) F) * A ≠ 0 := by
  intro hz
  have hi : ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) *
      (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  apply hA
  calc
    A = (((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * g) * A := by rw [hi, one_mul]
    _ = 0 := by rw [mul_assoc, hz, mul_zero]

/-- A boundary matrix supported in its top row. -/
def topRowMatrix (a b : F) : Matrix (Fin 2) (Fin 2) F := !![a, b; 0, 0]

theorem topRowMatrix_ne_zero {a b : F} (h : a ≠ 0 ∨ b ≠ 0) :
    topRowMatrix F a b ≠ 0 := by
  intro hz
  rcases h with ha | hb
  · exact ha (congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hz)
  · exact hb (congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hz)

theorem topRowMatrix_zero_mul (b : F) (C : Matrix (Fin 2) (Fin 2) F) :
    topRowMatrix F 0 b * C = topRowMatrix F (b * C 1 0) (b * C 1 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [topRowMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Each internal finite factor contributes its nonzero lower-left entry. -/
theorem topRowMatrix_zero_mul_topRow (b u v : F) (C : Matrix (Fin 2) (Fin 2) F) :
    topRowMatrix F 0 b * C * topRowMatrix F u v =
      topRowMatrix F (b * C 1 0 * u) (b * C 1 0 * v) := by
  rw [topRowMatrix_zero_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [topRowMatrix, Matrix.mul_apply, Fin.sum_univ_two]

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein

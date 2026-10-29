import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentIwahoriCriteria
import GaloisForLFunctions.HTGeometry.LoopEisenstein.MatrixValuationContent

/-!
# Valuation invariants of the two-step Iwahori lattice chain

Both the standard lattice and the lattice with second coordinate divisible
by `X` are preserved by the Iwahori. Their matrix valuation contents give
three invariants of the actual double cosets.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

/-- Change from the standard lattice to the adjacent lattice in the Iwahori flag. -/
def latticeStep : Matrix (Fin 2) (Fin 2) (LaurentSeries F) :=
  !![1, 0; 0, (laurentXUnit F : LaurentSeries F)]

/-- The inverse lattice-change matrix, over the Laurent field. -/
def latticeStepInv : Matrix (Fin 2) (Fin 2) (LaurentSeries F) :=
  !![1, 0; 0, ((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ)]

@[simp] theorem latticeStepInv_mul_step : latticeStepInv F * latticeStep F = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [latticeStep, latticeStepInv, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem latticeStep_mul_inv : latticeStep F * latticeStepInv F = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [latticeStep, latticeStepInv, Matrix.mul_apply, Fin.sum_univ_two]

/-- Express an endomorphism in the adjacent lattice basis. -/
def latticeConjugate (M : Matrix (Fin 2) (Fin 2) (LaurentSeries F)) :=
  latticeStepInv F * M * latticeStep F

/-- Express the output lattice in the adjacent basis and retain the standard input basis. -/
def latticeRows (M : Matrix (Fin 2) (Fin 2) (LaurentSeries F)) := latticeStepInv F * M

theorem latticeConjugate_mul (M N : Matrix (Fin 2) (Fin 2) (LaurentSeries F)) :
    latticeConjugate F (M * N) = latticeConjugate F M * latticeConjugate F N := by
  symm
  change (latticeStepInv F * M * latticeStep F) * (latticeStepInv F * N * latticeStep F) = _
  calc
    _ = latticeStepInv F * M * (latticeStep F * latticeStepInv F) * N * latticeStep F := by
      simp only [mul_assoc]
    _ = latticeConjugate F (M * N) := by
      rw [latticeStep_mul_inv, mul_one]
      simp only [latticeConjugate, mul_assoc]

@[simp] theorem latticeConjugate_one : latticeConjugate F 1 = 1 := by
  rw [latticeConjugate, mul_one, latticeStepInv_mul_step]

theorem latticeRows_mul_left (A M : Matrix (Fin 2) (Fin 2) (LaurentSeries F)) :
    latticeRows F (A * M) = latticeConjugate F A * latticeRows F M := by
  symm
  change (latticeStepInv F * A * latticeStep F) * (latticeStepInv F * M) = _
  calc
    _ = latticeStepInv F * A * (latticeStep F * latticeStepInv F) * M := by
      simp only [mul_assoc]
    _ = latticeRows F (A * M) := by
      rw [latticeStep_mul_inv, mul_one]
      simp only [latticeRows, mul_assoc]

theorem latticeRows_mul_right (M A : Matrix (Fin 2) (Fin 2) (LaurentSeries F)) :
    latticeRows F (M * A) = latticeRows F M * A := (mul_assoc _ _ _).symm

theorem latticeConjugate_entries (M : Matrix (Fin 2) (Fin 2) (LaurentSeries F)) :
    latticeConjugate F M =
      !![M 0 0, (laurentXUnit F : LaurentSeries F) * M 0 1;
        (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) * M 1 0, M 1 1] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [latticeConjugate, latticeStep, latticeStepInv, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc]

theorem latticeRows_entries (M : Matrix (Fin 2) (Fin 2) (LaurentSeries F)) :
    latticeRows F M =
      !![M 0 0, M 0 1;
        (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) * M 1 0,
        (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) * M 1 1] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [latticeRows, latticeStepInv, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem laurentIwahori_content_le_one {g : SL2 (LaurentSeries F)} (hg : g ∈ laurentIwahori F) :
    matrixValuationContent (laurentValuation F) g ≤ 1 :=
  (matrixValuationContent_le_iff _ _ _).2 ((mem_laurentIwahori F g).1 hg).1

/-- The Iwahori preserves the adjacent lattice as well as the standard one. -/
theorem laurentIwahori_conjugate_content_le_one {g : SL2 (LaurentSeries F)}
    (hg : g ∈ laurentIwahori F) :
    matrixValuationContent (laurentValuation F) (latticeConjugate F g) ≤ 1 := by
  obtain ⟨p, hp, rfl⟩ := hg
  have hc := (mem_iwahoriMatrices F p).1 hp
  obtain ⟨s, hs⟩ := PowerSeries.X_dvd_iff.2 hc
  have hupper : (laurentXUnit F : LaurentSeries F) * (p 0 1 : LaurentSeries F) =
      ((PowerSeries.X * p 0 1 : PowerSeries F) : LaurentSeries F) := by
    rw [PowerSeries.coe_mul, PowerSeries.coe_X]
    rfl
  have hlower : (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) *
      (p 1 0 : LaurentSeries F) = (s : LaurentSeries F) := by
    rw [hs, PowerSeries.coe_mul, PowerSeries.coe_X]
    change (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) *
      ((laurentXUnit F : LaurentSeries F) * (s : LaurentSeries F)) = (s : LaurentSeries F)
    rw [← mul_assoc]
    simp
  apply (matrixValuationContent_le_iff _ _ _).2
  intro i j
  rw [latticeConjugate_entries]
  fin_cases i <;> fin_cases j
  · exact valuation_powerSeries_le_one F (p 0 0)
  · change laurentValuation F ((laurentXUnit F : LaurentSeries F) * (p 0 1 : LaurentSeries F)) ≤ 1
    rw [hupper]
    exact valuation_powerSeries_le_one F _
  · change laurentValuation F
      ((((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) * (p 1 0 : LaurentSeries F)) ≤ 1
    rw [hlower]
    exact valuation_powerSeries_le_one F s
  · exact valuation_powerSeries_le_one F (p 1 1)

private theorem coe_inv_mul (g : SL2 (LaurentSeries F)) :
    ((g⁻¹ : SL2 (LaurentSeries F)) : Matrix (Fin 2) (Fin 2) (LaurentSeries F)) * g = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
  rfl

private theorem coe_mul_inv (g : SL2 (LaurentSeries F)) :
    (g : Matrix (Fin 2) (Fin 2) (LaurentSeries F)) * (g⁻¹ : SL2 (LaurentSeries F)) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
  rfl

theorem iwahori_content_left {i : SL2 (LaurentSeries F)} (hi : i ∈ laurentIwahori F)
    (M : Matrix (Fin 2) (Fin 2) (LaurentSeries F)) :
    matrixValuationContent (laurentValuation F) ((i : Matrix _ _ _) * M) =
      matrixValuationContent (laurentValuation F) M :=
  matrixValuationContent_mul_left_eq _ i i⁻¹ M
    (laurentIwahori_content_le_one F hi)
    (laurentIwahori_content_le_one F ((laurentIwahori F).inv_mem hi)) (coe_inv_mul F i)

theorem iwahori_content_right {i : SL2 (LaurentSeries F)} (hi : i ∈ laurentIwahori F)
    (M : Matrix (Fin 2) (Fin 2) (LaurentSeries F)) :
    matrixValuationContent (laurentValuation F) (M * (i : Matrix _ _ _)) =
      matrixValuationContent (laurentValuation F) M :=
  matrixValuationContent_mul_right_eq _ M i i⁻¹
    (laurentIwahori_content_le_one F hi)
    (laurentIwahori_content_le_one F ((laurentIwahori F).inv_mem hi)) (coe_mul_inv F i)

theorem iwahori_conjugate_content_left {i : SL2 (LaurentSeries F)} (hi : i ∈ laurentIwahori F)
    (M : Matrix (Fin 2) (Fin 2) (LaurentSeries F)) :
    matrixValuationContent (laurentValuation F) (latticeConjugate F i * M) =
      matrixValuationContent (laurentValuation F) M := by
  apply matrixValuationContent_mul_left_eq _ _ (latticeConjugate F (i⁻¹ : SL2 (LaurentSeries F)))
  · exact laurentIwahori_conjugate_content_le_one F hi
  · exact laurentIwahori_conjugate_content_le_one F ((laurentIwahori F).inv_mem hi)
  · rw [← latticeConjugate_mul, coe_inv_mul, latticeConjugate_one]

theorem iwahori_conjugate_content_right {i : SL2 (LaurentSeries F)} (hi : i ∈ laurentIwahori F)
    (M : Matrix (Fin 2) (Fin 2) (LaurentSeries F)) :
    matrixValuationContent (laurentValuation F) (M * latticeConjugate F i) =
      matrixValuationContent (laurentValuation F) M := by
  apply matrixValuationContent_mul_right_eq _ _ _ (latticeConjugate F (i⁻¹ : SL2 (LaurentSeries F)))
  · exact laurentIwahori_conjugate_content_le_one F hi
  · exact laurentIwahori_conjugate_content_le_one F ((laurentIwahori F).inv_mem hi)
  · rw [← latticeConjugate_mul, coe_mul_inv, latticeConjugate_one]

/-- Three contents record the relative position of the two lattices in the Iwahori chain. -/
def iwahoriLatticeProfile (g : SL2 (LaurentSeries F)) :
    WithZero (Multiplicative ℤ) × WithZero (Multiplicative ℤ) × WithZero (Multiplicative ℤ) :=
  (matrixValuationContent (laurentValuation F) g,
    matrixValuationContent (laurentValuation F) (latticeRows F g),
    matrixValuationContent (laurentValuation F) (latticeConjugate F g))

theorem iwahoriLatticeProfile_left_mul {i : SL2 (LaurentSeries F)}
    (hi : i ∈ laurentIwahori F) (g : SL2 (LaurentSeries F)) :
    iwahoriLatticeProfile F (i * g) = iwahoriLatticeProfile F g := by
  apply Prod.ext
  · exact iwahori_content_left F hi g
  · apply Prod.ext
    · change matrixValuationContent (laurentValuation F) (latticeRows F
        ((i * g : SL2 (LaurentSeries F)) : Matrix _ _ _)) = _
      rw [Matrix.SpecialLinearGroup.coe_mul, latticeRows_mul_left]
      exact iwahori_conjugate_content_left F hi _
    · change matrixValuationContent (laurentValuation F) (latticeConjugate F
        ((i * g : SL2 (LaurentSeries F)) : Matrix _ _ _)) = _
      rw [Matrix.SpecialLinearGroup.coe_mul, latticeConjugate_mul]
      exact iwahori_conjugate_content_left F hi _

theorem iwahoriLatticeProfile_right_mul {i : SL2 (LaurentSeries F)}
    (hi : i ∈ laurentIwahori F) (g : SL2 (LaurentSeries F)) :
    iwahoriLatticeProfile F (g * i) = iwahoriLatticeProfile F g := by
  apply Prod.ext
  · exact iwahori_content_right F hi g
  · apply Prod.ext
    · change matrixValuationContent (laurentValuation F) (latticeRows F
        ((g * i : SL2 (LaurentSeries F)) : Matrix _ _ _)) = _
      rw [Matrix.SpecialLinearGroup.coe_mul, latticeRows_mul_right]
      exact iwahori_content_right F hi _
    · change matrixValuationContent (laurentValuation F) (latticeConjugate F
        ((g * i : SL2 (LaurentSeries F)) : Matrix _ _ _)) = _
      rw [Matrix.SpecialLinearGroup.coe_mul, latticeConjugate_mul]
      exact iwahori_conjugate_content_right F hi _

/-- Both Iwahori factors preserve all three lattice-chain contents. -/
theorem iwahoriLatticeProfile_factors {l r : SL2 (LaurentSeries F)}
    (hl : l ∈ laurentIwahori F) (hr : r ∈ laurentIwahori F) (g : SL2 (LaurentSeries F)) :
    iwahoriLatticeProfile F (l * g * r) = iwahoriLatticeProfile F g := by
  rw [iwahoriLatticeProfile_right_mul F hr, iwahoriLatticeProfile_left_mul F hl]

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein

import GaloisForLFunctions.HTGeometry.LoopEisenstein.PositiveIwahori

/-!
# Unique Gauss coordinates on the positive Iwahori

An Iwahori matrix has a power-series unit in its upper-left corner. Its lower,
diagonal, and upper Gauss factors are therefore uniquely defined. The lower
parameter has zero constant coefficient; the unipotent radical is exactly the
locus where the diagonal unit has constant coefficient one.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

/-- The diagonal power-series torus. -/
def powerSeriesDiagonal (a : (PowerSeries F)ˣ) : PowerSeriesSL2 F :=
  ⟨!![(a : PowerSeries F), 0; 0, ((a⁻¹ : (PowerSeries F)ˣ) : PowerSeries F)], by
    simp [Matrix.det_fin_two]⟩

/-- The power-series unit group embeds multiplicatively as the diagonal torus. -/
def powerSeriesDiagonalHom : (PowerSeries F)ˣ →* PowerSeriesSL2 F where
  toFun := powerSeriesDiagonal F
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [powerSeriesDiagonal]
  map_mul' a b := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [powerSeriesDiagonal, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- Multiply the lower, diagonal, and upper Gauss factors. -/
def gaussMatrix (l : PowerSeries F) (a : (PowerSeries F)ˣ) (u : PowerSeries F) :
    PowerSeriesSL2 F :=
  FiniteRingSl2.lower l * powerSeriesDiagonal F a * FiniteRingSl2.upper u

theorem gaussMatrix_entries (l : PowerSeries F) (a : (PowerSeries F)ˣ) (u : PowerSeries F) :
    (gaussMatrix F l a u : Matrix (Fin 2) (Fin 2) (PowerSeries F)) =
      !![(a : PowerSeries F), (a : PowerSeries F) * u;
        l * (a : PowerSeries F), l * (a : PowerSeries F) * u + ((a⁻¹ : (PowerSeries F)ˣ) : PowerSeries F)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gaussMatrix, powerSeriesDiagonal, FiniteRingSl2.lower, FiniteRingSl2.upper,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem gaussMatrix_zero_zero (l : PowerSeries F) (a : (PowerSeries F)ˣ) (u : PowerSeries F) :
    gaussMatrix F l a u 0 0 = (a : PowerSeries F) := by rw [gaussMatrix_entries]; rfl

@[simp] theorem gaussMatrix_zero_one (l : PowerSeries F) (a : (PowerSeries F)ˣ) (u : PowerSeries F) :
    gaussMatrix F l a u 0 1 = (a : PowerSeries F) * u := by rw [gaussMatrix_entries]; rfl

@[simp] theorem gaussMatrix_one_zero (l : PowerSeries F) (a : (PowerSeries F)ˣ) (u : PowerSeries F) :
    gaussMatrix F l a u 1 0 = l * (a : PowerSeries F) := by rw [gaussMatrix_entries]; rfl

@[simp] theorem gaussMatrix_one_one (l : PowerSeries F) (a : (PowerSeries F)ˣ) (u : PowerSeries F) :
    gaussMatrix F l a u 1 1 = l * (a : PowerSeries F) * u + ((a⁻¹ : (PowerSeries F)ˣ) : PowerSeries F) := by
  rw [gaussMatrix_entries]
  rfl

/-- A unit upper-left entry determines the Gauss factorization over the power-series ring. -/
theorem gaussMatrix_factorization (g : PowerSeriesSL2 F) (a : (PowerSeries F)ˣ)
    (ha : (a : PowerSeries F) = g 0 0) :
    gaussMatrix F (g 1 0 * ((a⁻¹ : (PowerSeries F)ˣ) : PowerSeries F)) a
      (((a⁻¹ : (PowerSeries F)ˣ) : PowerSeries F) * g 0 1) = g := by
  have hu : (a : PowerSeries F) * ((a⁻¹ : (PowerSeries F)ˣ) : PowerSeries F) = 1 := by simp
  have hc : (g 1 0 * ((a⁻¹ : (PowerSeries F)ˣ) : PowerSeries F)) * (a : PowerSeries F) = g 1 0 := by
    simp [mul_assoc]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · rw [gaussMatrix_zero_zero]
    exact ha
  · rw [gaussMatrix_zero_one, ← mul_assoc, hu, one_mul]
  · rw [gaussMatrix_one_zero, hc]
  · rw [gaussMatrix_one_one, hc]
    -- The determinant equation determines the remaining lower-right entry.
    have hd := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two, ← ha] at hd
    linear_combination -((a⁻¹ : (PowerSeries F)ˣ) : PowerSeries F) * hd + g 1 1 * hu

/-- Equality of Gauss matrices determines all three parameters. -/
theorem gaussMatrix_parameters {l l' u u' : PowerSeries F} {a a' : (PowerSeries F)ˣ}
    (h : gaussMatrix F l a u = gaussMatrix F l' a' u') :
    l = l' ∧ a = a' ∧ u = u' := by
  have haa := congrArg (fun g : PowerSeriesSL2 F => g 0 0) h
  rw [gaussMatrix_zero_zero, gaussMatrix_zero_zero] at haa
  have ha : a = a' := Units.ext haa
  subst a'
  have hl := congrArg (fun g : PowerSeriesSL2 F => g 1 0) h
  have hu := congrArg (fun g : PowerSeriesSL2 F => g 0 1) h
  rw [gaussMatrix_one_zero, gaussMatrix_one_zero] at hl
  rw [gaussMatrix_zero_one, gaussMatrix_zero_one] at hu
  refine ⟨?_, rfl, ?_⟩
  · have hli := congrArg (fun p : PowerSeries F => p * ((a⁻¹ : (PowerSeries F)ˣ) : PowerSeries F)) hl
    simpa [mul_assoc] using hli
  · have hui := congrArg (fun p : PowerSeries F => ((a⁻¹ : (PowerSeries F)ˣ) : PowerSeries F) * p) hu
    simpa [← mul_assoc] using hui

theorem iwahori_upper_left_constant_ne_zero (g : iwahoriMatrices F) :
    PowerSeries.constantCoeff ((g : PowerSeriesSL2 F) 0 0) ≠ 0 := by
  have hc := (mem_iwahoriMatrices F g).1 g.property
  have hd := Matrix.SpecialLinearGroup.det_coe (powerSeriesReduction F g)
  rw [Matrix.det_fin_two] at hd
  simp only [powerSeriesReduction_apply, hc, mul_zero, sub_zero] at hd
  intro ha
  rw [ha, zero_mul] at hd
  exact zero_ne_one hd

/-- The unrestricted Gauss coordinates of a positive Iwahori matrix. -/
@[ext] structure IwahoriCoordinates where
  lower : PowerSeries F
  lower_constant : PowerSeries.constantCoeff lower = 0
  diagonal : (PowerSeries F)ˣ
  upper : PowerSeries F

/-- The matrix represented by admissible Gauss coordinates. -/
def IwahoriCoordinates.toMatrix (p : IwahoriCoordinates F) : iwahoriMatrices F :=
  ⟨gaussMatrix F p.lower p.diagonal p.upper, by
    rw [mem_iwahoriMatrices, gaussMatrix_one_zero, map_mul, p.lower_constant, zero_mul]⟩

/-- Recover the three Gauss parameters from an Iwahori matrix. -/
def iwahoriCoordinates (g : iwahoriMatrices F) : IwahoriCoordinates F where
  lower := (g : PowerSeriesSL2 F) 1 0 *
    (((powerSeriesUnitOfConstant F ((g : PowerSeriesSL2 F) 0 0)
      (iwahori_upper_left_constant_ne_zero F g))⁻¹ : (PowerSeries F)ˣ) : PowerSeries F)
  lower_constant := by
    rw [map_mul, (mem_iwahoriMatrices F g).1 g.property, zero_mul]
  diagonal := powerSeriesUnitOfConstant F ((g : PowerSeriesSL2 F) 0 0)
    (iwahori_upper_left_constant_ne_zero F g)
  upper := (((powerSeriesUnitOfConstant F ((g : PowerSeriesSL2 F) 0 0)
      (iwahori_upper_left_constant_ne_zero F g))⁻¹ : (PowerSeries F)ˣ) : PowerSeries F) *
    (g : PowerSeriesSL2 F) 0 1

theorem iwahoriCoordinates_toMatrix (g : iwahoriMatrices F) :
    (iwahoriCoordinates F g).toMatrix F = g := by
  apply Subtype.ext
  exact gaussMatrix_factorization F g _ (coe_powerSeriesUnitOfConstant F _ _)

theorem IwahoriCoordinates.toMatrix_injective :
    Function.Injective (IwahoriCoordinates.toMatrix F) := by
  intro p q h
  have hpq := gaussMatrix_parameters F (congrArg Subtype.val h)
  exact IwahoriCoordinates.ext hpq.1 hpq.2.1 hpq.2.2

/-- Unique Gauss coordinates on the full positive Iwahori, with no truncation. -/
def iwahoriGaussEquiv : IwahoriCoordinates F ≃ iwahoriMatrices F where
  toFun := IwahoriCoordinates.toMatrix F
  invFun := iwahoriCoordinates F
  left_inv p := IwahoriCoordinates.toMatrix_injective F (iwahoriCoordinates_toMatrix F (p.toMatrix F))
  right_inv := iwahoriCoordinates_toMatrix F

/-- The unipotent locus is precisely the principal diagonal-unit locus. -/
theorem IwahoriCoordinates.unipotent_iff (p : IwahoriCoordinates F) :
    (p.toMatrix F : PowerSeriesSL2 F) ∈ positiveUnipotentMatrices F ↔
      powerSeriesResidueUnit F p.diagonal = 1 := by
  rw [mem_positiveUnipotentMatrices]
  change PowerSeries.constantCoeff (gaussMatrix F p.lower p.diagonal p.upper 0 0) = 1 ∧
      PowerSeries.constantCoeff (gaussMatrix F p.lower p.diagonal p.upper 1 0) = 0 ∧
      PowerSeries.constantCoeff (gaussMatrix F p.lower p.diagonal p.upper 1 1) = 1 ↔ _
  rw [gaussMatrix_zero_zero, gaussMatrix_one_zero, gaussMatrix_one_one]
  constructor
  · intro h
    apply Units.ext
    exact h.1
  · intro h
    have ha : PowerSeries.constantCoeff (p.diagonal : PowerSeries F) = 1 :=
      congrArg (fun a : Fˣ => (a : F)) h
    have hi : PowerSeries.constantCoeff ((p.diagonal⁻¹ : (PowerSeries F)ˣ) : PowerSeries F) = 1 := by
      change (powerSeriesResidueUnit F (p.diagonal⁻¹) : F) = 1
      rw [map_inv, h, inv_one]
      rfl
    simp only [map_add, map_mul, p.lower_constant, zero_mul, zero_add, ha, hi, and_self]

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein

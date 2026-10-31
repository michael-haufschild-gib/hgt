import GaloisForLFunctions.HTGeometry.FiniteRingSl2
import GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2DiagonalRescaling

/-!
# Unit diagonal rescaling over a commutative ring

General-linear diagonal conjugation acts on determinant-one matrices
without a field hypothesis. This ring form applies in particular to
coefficient-integral power series and commutes with their embeddings.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Rescale the two off-diagonal entries inversely by a ring unit. -/
def ringSL2Rescale (u : Rˣ) :
    Matrix.SpecialLinearGroup (Fin 2) R →* Matrix.SpecialLinearGroup (Fin 2) R where
  toFun g := ⟨!![g 0 0, (u : R) * g 0 1; ((u⁻¹ : Rˣ) : R) * g 1 0, g 1 1], by
    rw [Matrix.det_fin_two]
    change g 0 0 * g 1 1 - ((u : R) * g 0 1) * (((u⁻¹ : Rˣ) : R) * g 1 0) = 1
    have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := by simp
    calc
      _ = g 0 0 * g 1 1 - ((u : R) * ((u⁻¹ : Rˣ) : R)) * (g 0 1 * g 1 0) := by ring
      _ = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by rw [hu, one_mul]
      _ = 1 := by simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe g⟩
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j
    · change g 0 0 * h 0 0 + g 0 1 * h 1 0 =
        g 0 0 * h 0 0 + ((u : R) * g 0 1) * (((u⁻¹ : Rˣ) : R) * h 1 0)
      have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := by simp
      calc
        _ = g 0 0 * h 0 0 + ((u : R) * ((u⁻¹ : Rˣ) : R)) * (g 0 1 * h 1 0) := by
          rw [hu, one_mul]
        _ = _ := by ring
    · change (u : R) * (g 0 0 * h 0 1 + g 0 1 * h 1 1) =
        g 0 0 * ((u : R) * h 0 1) + ((u : R) * g 0 1) * h 1 1
      ring
    · change ((u⁻¹ : Rˣ) : R) * (g 1 0 * h 0 0 + g 1 1 * h 1 0) =
        (((u⁻¹ : Rˣ) : R) * g 1 0) * h 0 0 + g 1 1 * (((u⁻¹ : Rˣ) : R) * h 1 0)
      ring
    · change g 1 0 * h 0 1 + g 1 1 * h 1 1 =
        (((u⁻¹ : Rˣ) : R) * g 1 0) * ((u : R) * h 0 1) + g 1 1 * h 1 1
      have hu : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := by simp
      calc
        _ = (((u⁻¹ : Rˣ) : R) * (u : R)) * (g 1 0 * h 0 1) + g 1 1 * h 1 1 := by
          rw [hu, one_mul]
        _ = _ := by ring

@[simp] theorem coe_ringSL2Rescale (u : Rˣ) (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    (ringSL2Rescale u g : Matrix (Fin 2) (Fin 2) R) =
      !![g 0 0, (u : R) * g 0 1; ((u⁻¹ : Rˣ) : R) * g 1 0, g 1 1] := rfl

/-- The inverse scalar gives the inverse matrix rescaling. -/
theorem ringSL2Rescale_inverse (u : Rˣ) (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    ringSL2Rescale u⁻¹ (ringSL2Rescale u g) = g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_ringSL2Rescale, ← mul_assoc]

/-- Unit diagonal rescaling is natural under every coefficient-ring homomorphism. -/
theorem ringSL2Rescale_map (f : R →+* S) (u : Rˣ)
    (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    Matrix.SpecialLinearGroup.map f (ringSL2Rescale u g) =
      ringSL2Rescale (Units.map f.toMonoidHom u) (Matrix.SpecialLinearGroup.map f g) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_ringSL2Rescale, map_mul]

@[simp] theorem ringSL2Rescale_upper (u : Rˣ) (s : R) :
    ringSL2Rescale u (FiniteRingSl2.upper s) = FiniteRingSl2.upper ((u : R) * s) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_ringSL2Rescale, FiniteRingSl2.upper]

@[simp] theorem ringSL2Rescale_lower (u : Rˣ) (s : R) :
    ringSL2Rescale u (FiniteRingSl2.lower s) = FiniteRingSl2.lower (((u⁻¹ : Rˣ) : R) * s) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_ringSL2Rescale, FiniteRingSl2.lower]

/-- Over a field this is the existing Laurent-matrix rescaling. -/
theorem ringSL2Rescale_eq {F : Type*} [Field F] (u : Fˣ) (g : SL2 F) :
    ringSL2Rescale u g = sl2Rescale u g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rfl

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.ringSL2Rescale
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.ringSL2Rescale_map

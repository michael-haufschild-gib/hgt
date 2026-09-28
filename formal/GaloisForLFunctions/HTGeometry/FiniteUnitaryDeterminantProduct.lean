import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitarySimplyConnected

/-!
# Global determinant coordinates on finite unitary groups

Choosing one coordinate gives a homeomorphism `U(ι) ≃ₜ SU(ι) × Circle`.
The inverse multiplies a special-unitary matrix by the diagonal determinant
section. This is a topological product decomposition; normalization need
not preserve matrix multiplication.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Recover a unitary matrix from its determinant-normalized component. -/
theorem specialUnitaryNormalize_mul_circleSection (i0 : ι)
    (U : Matrix.unitaryGroup ι ℂ) :
    specialUnitaryToUnitary (specialUnitaryNormalize i0 U) *
      finiteUnitaryCircleSection i0 (finiteUnitaryDeterminant ι U) = U := by
  change (U * (finiteUnitaryCircleSection i0 (finiteUnitaryDeterminant ι U))⁻¹) *
    finiteUnitaryCircleSection i0 (finiteUnitaryDeterminant ι U) = U
  simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- Determinant normalization removes the entire diagonal circle section. -/
theorem specialUnitaryNormalize_circleSection (i0 : ι) (z : Circle) :
    specialUnitaryNormalize i0 (finiteUnitaryCircleSection i0 z) = 1 := by
  have hdet : finiteUnitaryDeterminant ι (finiteUnitaryCircleSection i0 z) = z :=
    DFunLike.congr_fun (finiteUnitaryDeterminant_comp_section i0) z
  have h := specialUnitaryNormalize_mul_circleSection i0 (finiteUnitaryCircleSection i0 z)
  rw [hdet] at h
  have hu : specialUnitaryToUnitary
      (specialUnitaryNormalize i0 (finiteUnitaryCircleSection i0 z)) = 1 :=
    mul_right_cancel (h.trans (one_mul _).symm)
  exact Subtype.ext (congrArg (fun U : Matrix.unitaryGroup ι ℂ =>
    (U : Matrix ι ι ℂ)) hu)

/-- Global determinant coordinates split a finite unitary group as a space. -/
def finiteUnitaryDeterminantProductHomeomorph (i0 : ι) :
    Matrix.unitaryGroup ι ℂ ≃ₜ Matrix.specialUnitaryGroup ι ℂ × Circle where
  toFun U := (specialUnitaryNormalize i0 U, finiteUnitaryDeterminant ι U)
  invFun p := specialUnitaryToUnitary p.1 * finiteUnitaryCircleSection i0 p.2
  left_inv U := specialUnitaryNormalize_mul_circleSection i0 U
  right_inv p := by
    apply Prod.ext
    · change specialUnitaryNormalize i0
        (specialUnitaryToUnitary p.1 * finiteUnitaryCircleSection i0 p.2) = p.1
      rw [specialUnitaryNormalize_mul_left, specialUnitaryNormalize_circleSection, mul_one]
    · apply Subtype.ext
      change ((p.1 : Matrix ι ι ℂ) *
        (finiteUnitaryCircleSection i0 p.2 : Matrix ι ι ℂ)).det = (p.2 : ℂ)
      rw [Matrix.det_mul, (Matrix.mem_specialUnitaryGroup_iff.mp p.1.2).2, one_mul]
      exact unitaryDeterminantSection_det i0 p.2
        (Unitary.mem_iff.mp (circleUnitary p.2).2).1
  continuous_toFun := (continuous_specialUnitaryNormalize i0).prodMk
    (finiteUnitaryDeterminant ι).continuous
  continuous_invFun :=
    ((finiteSpecialUnitaryInclusionHom (ι := ι)).continuous.comp continuous_fst).mul
      ((finiteUnitaryCircleSection i0).continuous.comp continuous_snd)

/-- The second global coordinate is the actual determinant. -/
theorem finiteUnitaryDeterminantProductHomeomorph_snd (i0 : ι)
    (U : Matrix.unitaryGroup ι ℂ) :
    (finiteUnitaryDeterminantProductHomeomorph i0 U).2 = finiteUnitaryDeterminant ι U := rfl

end

end GaloisForLFunctions.HTGeometry

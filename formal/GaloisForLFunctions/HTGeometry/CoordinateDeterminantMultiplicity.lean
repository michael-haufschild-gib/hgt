import GaloisForLFunctions.RHTower.MertensClockRelativeDeterminant
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantAlgebraicMultiplicity
import GaloisForLFunctions.HTGeometry.GeneralizedEigenspaceIntertwining

/-! # Exact determinant multiplicities on the original Hilbert space -/

noncomputable section
open HilbertSchmidt ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [DecidableEq ι]

omit [CompleteSpace H] [DecidableEq ι] in
theorem maxGenEigenspace_coordOp_map (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (μ : ℂ) :
    Submodule.map b.repr.toLinearEquiv.toLinearMap
        (Module.End.maxGenEigenspace (T : H →ₗ[ℂ] H) μ) =
      Module.End.maxGenEigenspace (coordOp b T).toLinearMap μ := by
  apply map_maxGenEigenspace_eq_of_intertwining
    (T : H →ₗ[ℂ] H) (coordOp b T).toLinearMap b.repr.toLinearEquiv.toLinearMap
    b.repr.injective
  · intro x
    simp [coordOp_apply]
  · intro v _
    exact ⟨b.repr.symm v, by simp⟩

omit [CompleteSpace H] [DecidableEq ι] in
theorem finrank_maxGenEigenspace_coordOp (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (μ : ℂ) :
    Module.finrank ℂ (Module.End.maxGenEigenspace (T : H →ₗ[ℂ] H) μ) =
      Module.finrank ℂ (Module.End.maxGenEigenspace (coordOp b T).toLinearMap μ) := by
  rw [← maxGenEigenspace_coordOp_map b T μ]
  exact (Submodule.equivMapOfInjective b.repr.toLinearEquiv.toLinearMap b.repr.injective
    (Module.End.maxGenEigenspace (T : H →ₗ[ℂ] H) μ)).finrank_eq

omit [CompleteSpace H] [DecidableEq ι] in
theorem finiteDimensional_maxGenEigenspace_of_coordOp (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (μ : ℂ)
    [FiniteDimensional ℂ (Module.End.maxGenEigenspace (coordOp b T).toLinearMap μ)] :
    FiniteDimensional ℂ (Module.End.maxGenEigenspace (T : H →ₗ[ℂ] H) μ) := by
  letI : FiniteDimensional ℂ (Submodule.map b.repr.toLinearEquiv.toLinearMap
      (Module.End.maxGenEigenspace (T : H →ₗ[ℂ] H) μ)) := by
    rw [maxGenEigenspace_coordOp_map b T μ]
    infer_instance
  let e := Submodule.equivMapOfInjective b.repr.toLinearEquiv.toLinearMap b.repr.injective
    (Module.End.maxGenEigenspace (T : H →ₗ[ℂ] H) μ)
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

/-- Coordinate transport identifies the actual generalized eigenspace, including
its finite-dimensionality, not just the scalar determinant's zero order. -/
theorem analyticOrderAt_coordMatrix_eq_finrank_and_finite
    (b : HilbertBasis ι ℂ H)
    {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) {z : ℂ}
    (hz : entireDet2 (coordMatrix b T) z = 0) :
    (analyticOrderAt (entireDet2 (coordMatrix b T)) z =
      (Module.finrank ℂ (Module.End.maxGenEigenspace (T : H →ₗ[ℂ] H) z⁻¹) : ℕ∞)) ∧
    FiniteDimensional ℂ (Module.End.maxGenEigenspace (T : H →ₗ[ℂ] H) z⁻¹) := by
  have hM := isHS_coordMatrix b hT
  have hz0 : z ≠ 0 := by
    intro he
    subst z
    have hone := (isRegularizedDet_entireDet2 hM).eq_one_at_zero
    rw [hz] at hone
    exact zero_ne_one hone
  obtain ⟨w, hw0, hw⟩ := exists_eigenvector_of_entireDet2_eq_zero hM hz0 hz
  have hp := analyticOrderAt_entireDet2_eq_finrank_maxGenEigenspace_and_finite_of_eigenvector
    hM hz0 hw0 hw
  have hC : toOperator hM = coordOp b T :=
    toOperator_matrixOf (isHilbertSchmidt_coordOp b hT)
  rw [hC] at hp
  constructor
  · rw [finrank_maxGenEigenspace_coordOp b T z⁻¹]
    exact hp.1
  · letI := hp.2
    exact finiteDimensional_maxGenEigenspace_of_coordOp b T z⁻¹

end GaloisForLFunctions.HTGeometry

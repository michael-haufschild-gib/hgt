import GaloisForLFunctions.RHTower.HedenmalmThetaCompactDivisorEigenmode
import GaloisForLFunctions.RHTower.HedenmalmThetaEntireDeterminant
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantAlgebraicMultiplicity

/-!
# Correctly signed entire determinant and algebraic multiplicity of the theta source inverse

The legacy `thetaEntireDet2` is `det₂(I - zB)`.  The source card asks for `det₂(I + zB)`, hence
the kernel entering `entireDet2` is `-thetaKernelMatrix`.
-/

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HilbertSchmidt MeasureTheory

/-- **The entire Hilbert--Carleman determinant `det₂(I + zB)` of the source inverse.** -/
noncomputable def thetaSourceEntireDet2 : ℂ → ℂ := entireDet2 (-thetaKernelMatrix)

theorem isHS_neg_thetaKernelMatrix : IsHS (-thetaKernelMatrix) :=
  isHS_neg isHS_thetaKernelMatrix

theorem differentiable_thetaSourceEntireDet2 : Differentiable ℂ thetaSourceEntireDet2 :=
  differentiable_entireDet2 isHS_neg_thetaKernelMatrix

theorem thetaSourceEntireDet2_zero : thetaSourceEntireDet2 0 = 1 :=
  (isRegularizedDet_entireDet2 isHS_neg_thetaKernelMatrix).eq_one_at_zero

theorem toOperator_neg_thetaKernelMatrix :
    toOperator isHS_neg_thetaKernelMatrix = -thetaKernelMatrixOperator := by
  simpa only [toOperator_thetaKernelMatrix] using toOperator_neg isHS_thetaKernelMatrix

theorem thetaKernelOperator_eq_thetaCompactSourceInverse :
    thetaKernelOperator = thetaCompactSourceInverse := rfl

/-- The theta coordinate equivalence intertwines `-B` with the represented negated kernel. -/
theorem thetaCoord_intertwines_neg_sourceInverse (f : Lp ℂ 2 unitIntervalMeasure) :
    thetaCoord ((-thetaKernelOperator) f) =
      toOperator isHS_neg_thetaKernelMatrix (thetaCoord f) := by
  rw [toOperator_neg_thetaKernelMatrix]
  simp [thetaKernelMatrixOperator]

/-- **`det₂(I + zB)` vanishes exactly at the source-inverse divisor eigenmodes.** -/
theorem thetaSourceEntireDet2_eq_zero_iff_exists_eigenvector {z : ℂ} (hz : z ≠ 0) :
    thetaSourceEntireDet2 z = 0 ↔
      ∃ f : Lp ℂ 2 unitIntervalMeasure,
        f ≠ 0 ∧ thetaKernelOperator f = (-z⁻¹) • f := by
  rw [thetaSourceEntireDet2,
    entireDet2_eq_zero_iff_exists_eigenvector isHS_neg_thetaKernelMatrix hz]
  constructor
  · rintro ⟨w, hw0, hw⟩
    let f : Lp ℂ 2 unitIntervalMeasure := thetaCoord.symm w
    refine ⟨f, ?_, ?_⟩
    · intro hf
      apply hw0
      simpa [f] using congrArg thetaCoord hf
    · apply thetaCoord.injective
      have hinter := thetaCoord_intertwines_neg_sourceInverse f
      have hw' : toOperator isHS_neg_thetaKernelMatrix (thetaCoord f) = z⁻¹ • thetaCoord f := by
        simpa [f] using hw
      rw [← hinter] at hw'
      have hneg : thetaCoord (thetaKernelOperator f) = (-z⁻¹) • thetaCoord f := by
        have := congrArg Neg.neg hw'
        simpa using this
      simpa [map_smul] using hneg
  · rintro ⟨f, hf0, hf⟩
    refine ⟨thetaCoord f, ?_, ?_⟩
    · intro hzero
      apply hf0
      apply thetaCoord.injective
      simpa using hzero
    rw [← thetaCoord_intertwines_neg_sourceInverse]
    have := congrArg (fun x : Lp ℂ 2 unitIntervalMeasure => -x) hf
    simpa [map_smul] using congrArg thetaCoord this

/-- Coordinate transport preserves every generalized root-space dimension. -/
theorem finrank_maxGenEigenspace_neg_thetaKernelMatrix_eq_sourceInverse (z : ℂ) :
    Module.finrank ℂ (Module.End.maxGenEigenspace
      (toOperator isHS_neg_thetaKernelMatrix :
        lp (fun _ : thetaIndex => ℂ) 2 →ₗ[ℂ] lp (fun _ : thetaIndex => ℂ) 2) z⁻¹) =
    Module.finrank ℂ (Module.End.maxGenEigenspace
      (thetaKernelOperator :
        Lp ℂ 2 unitIntervalMeasure →ₗ[ℂ] Lp ℂ 2 unitIntervalMeasure) (-z⁻¹)) := by
  let L : Lp ℂ 2 unitIntervalMeasure →ₗ[ℂ] lp (fun _ : thetaIndex => ℂ) 2 :=
    thetaCoord.toLinearEquiv.toLinearMap
  have hinter (f : Lp ℂ 2 unitIntervalMeasure) :
      L ((-thetaKernelOperator :
        Lp ℂ 2 unitIntervalMeasure →ₗ[ℂ] Lp ℂ 2 unitIntervalMeasure) f) =
      (toOperator isHS_neg_thetaKernelMatrix :
        lp (fun _ : thetaIndex => ℂ) 2 →ₗ[ℂ] lp (fun _ : thetaIndex => ℂ) 2) (L f) := by
    exact thetaCoord_intertwines_neg_sourceInverse f
  have hrange : Module.End.maxGenEigenspace
      (toOperator isHS_neg_thetaKernelMatrix :
        lp (fun _ : thetaIndex => ℂ) 2 →ₗ[ℂ] lp (fun _ : thetaIndex => ℂ) 2) z⁻¹ ≤
      LinearMap.range L := by
    intro w hw
    exact ⟨thetaCoord.symm w, by simp [L]⟩
  have htransport := finrank_maxGenEigenspace_eq_of_intertwining
    (-thetaKernelOperator :
      Lp ℂ 2 unitIntervalMeasure →ₗ[ℂ] Lp ℂ 2 unitIntervalMeasure)
    (toOperator isHS_neg_thetaKernelMatrix :
      lp (fun _ : thetaIndex => ℂ) 2 →ₗ[ℂ] lp (fun _ : thetaIndex => ℂ) 2)
    L thetaCoord.injective hinter z⁻¹ hrange
  calc
    Module.finrank ℂ (Module.End.maxGenEigenspace
        (toOperator isHS_neg_thetaKernelMatrix :
          lp (fun _ : thetaIndex => ℂ) 2 →ₗ[ℂ] lp (fun _ : thetaIndex => ℂ) 2) z⁻¹) =
        Module.finrank ℂ (Module.End.maxGenEigenspace
          (-thetaKernelOperator :
            Lp ℂ 2 unitIntervalMeasure →ₗ[ℂ] Lp ℂ 2 unitIntervalMeasure) z⁻¹) :=
      htransport.symm
    _ = Module.finrank ℂ (Module.End.maxGenEigenspace
        (thetaKernelOperator :
          Lp ℂ 2 unitIntervalMeasure →ₗ[ℂ] Lp ℂ 2 unitIntervalMeasure) (-z⁻¹)) := by
      have hgen := maxGenEigenspace_neg_neg
        (thetaKernelOperator :
          Lp ℂ 2 unitIntervalMeasure →ₗ[ℂ] Lp ℂ 2 unitIntervalMeasure) (-z⁻¹)
      have hparam : -(-z⁻¹) = z⁻¹ := by simp
      rw [hparam] at hgen
      exact congrArg
        (fun W : Submodule ℂ (Lp ℂ 2 unitIntervalMeasure) => Module.finrank ℂ W) hgen

/-- **A determinant zero has exactly the algebraic multiplicity of `-z⁻¹` for the fixed source
inverse `B`.** -/
theorem analyticOrderAt_thetaSourceEntireDet2_eq_algebraicMultiplicity
    {z : ℂ} (hz : thetaSourceEntireDet2 z = 0) :
    analyticOrderAt thetaSourceEntireDet2 z =
      (Module.finrank ℂ (Module.End.maxGenEigenspace
        (thetaKernelOperator :
          Lp ℂ 2 unitIntervalMeasure →ₗ[ℂ] Lp ℂ 2 unitIntervalMeasure) (-z⁻¹)) : ℕ∞) := by
  rw [thetaSourceEntireDet2]
  rw [analyticOrderAt_entireDet2_eq_finrank_maxGenEigenspace
    isHS_neg_thetaKernelMatrix hz,
    finrank_maxGenEigenspace_neg_thetaKernelMatrix_eq_sourceInverse]

end RHTower.HedenmalmThetaSource

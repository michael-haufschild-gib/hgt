import GaloisForLFunctions.HTGeometry.HardyDiskModelDimension
import GaloisForLFunctions.HTGeometry.HardyMultiplierZeroModelDimension
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGeneralizedSchurInertia

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem range_hardyMul_mul_finiteBlaschke
    (B₀ B₁ : FiniteBlaschke) :
    LinearMap.range
        ((hardyMul (B₀.toMultiplier.mul B₁.toMultiplier) :
          HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk) =
      (LinearMap.range
        ((hardyMul B₁.toMultiplier : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk)).map
        ((hardyMul B₀.toMultiplier : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨hardyMul B₁.toMultiplier x, ⟨x, rfl⟩, ?_⟩
    exact hardyMul_mul B₀.toMultiplier B₁.toMultiplier x
  · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (hardyMul_mul B₀.toMultiplier B₁.toMultiplier x).symm⟩

/-- Exact model-space product identity
`K_(B₀B₁) = K_(B₀) ⊕ B₀ K_(B₁)` for finite Blaschke products. -/
theorem hardyMultiplierModelSpace_mul_finiteBlaschke_eq_sup
    (B₀ B₁ : FiniteBlaschke) :
    hardyMultiplierModelSpace (B₀.toMultiplier.mul B₁.toMultiplier) =
      finiteBlaschkeModelSpace B₀ ⊔
        (finiteBlaschkeModelSpace B₁).map
          ((hardyMul B₀.toMultiplier : HardyDisk →L[ℂ] HardyDisk) :
            HardyDisk →ₗ[ℂ] HardyDisk) := by
  let T : HardyDisk →L[ℂ] HardyDisk := hardyMul B₀.toMultiplier
  let V : Submodule ℂ HardyDisk :=
    LinearMap.range
      ((hardyMul B₁.toMultiplier : HardyDisk →L[ℂ] HardyDisk) :
        HardyDisk →ₗ[ℂ] HardyDisk)
  have hsplit := orthogonal_map_eq_sup (T := T)
    (hardyMulBlaschke_isometry B₀) V
  rw [show V.map (T : HardyDisk →ₗ[ℂ] HardyDisk) =
      LinearMap.range
        ((hardyMul (B₀.toMultiplier.mul B₁.toMultiplier) :
          HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk) by
      exact (range_hardyMul_mul_finiteBlaschke B₀ B₁).symm] at hsplit
  exact hsplit

/-- The two summands in the finite-Blaschke model-space product identity are orthogonal. -/
theorem finiteBlaschkeModelSpace_inner_transported_eq_zero
    (B₀ B₁ : FiniteBlaschke)
    (x : finiteBlaschkeModelSpace B₀)
    (y : finiteBlaschkeModelSpace B₁) :
    inner ℂ (x : HardyDisk) (hardyMul B₀.toMultiplier (y : HardyDisk)) = 0 := by
  have hyrange : hardyMul B₀.toMultiplier (y : HardyDisk) ∈
      LinearMap.range
        ((hardyMul B₀.toMultiplier : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk) :=
    ⟨(y : HardyDisk), rfl⟩
  have hreverse := x.property _ hyrange
  rw [← inner_conj_symm, hreverse, map_zero]

end

end GaloisForLFunctions.HTGeometry

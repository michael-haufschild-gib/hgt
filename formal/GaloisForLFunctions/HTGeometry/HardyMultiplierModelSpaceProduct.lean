import GaloisForLFunctions.HTGeometry.GeneralizedSchurKernelRankProfile

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem range_hardyMul_mul
    (B₀ B₁ : DiskMultiplier) :
    LinearMap.range
        ((hardyMul (B₀.mul B₁) : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk) =
      (LinearMap.range
        ((hardyMul B₁ : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk)).map
        ((hardyMul B₀ : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨hardyMul B₁ x, ⟨x, rfl⟩, ?_⟩
    exact hardyMul_mul B₀ B₁ x
  · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (hardyMul_mul B₀ B₁ x).symm⟩

/-- Product of two inner Hardy multipliers is inner. -/
theorem HardyMultiplierIsometry.mul
    {B₀ B₁ : DiskMultiplier} (hB₀ : HardyMultiplierIsometry B₀)
    (hB₁ : HardyMultiplierIsometry B₁) :
    HardyMultiplierIsometry (B₀.mul B₁) := by
  intro x
  rw [← hardyMul_mul B₀ B₁ x, hB₀, hB₁]

/-- Exact arbitrary-inner model-space product identity
`K_(B₀B₁) = K_(B₀) ⊕ B₀ K_(B₁)`. -/
theorem hardyMultiplierModelSpace_mul_eq_sup
    (B₀ B₁ : DiskMultiplier) (hB₀ : HardyMultiplierIsometry B₀) :
    hardyMultiplierModelSpace (B₀.mul B₁) =
      hardyMultiplierModelSpace B₀ ⊔
        (hardyMultiplierModelSpace B₁).map
          ((hardyMul B₀ : HardyDisk →L[ℂ] HardyDisk) :
            HardyDisk →ₗ[ℂ] HardyDisk) := by
  let T : HardyDisk →L[ℂ] HardyDisk := hardyMul B₀
  let V : Submodule ℂ HardyDisk :=
    LinearMap.range
      ((hardyMul B₁ : HardyDisk →L[ℂ] HardyDisk) :
        HardyDisk →ₗ[ℂ] HardyDisk)
  have hsplit := orthogonal_map_eq_sup (T := T) hB₀ V
  rw [show V.map (T : HardyDisk →ₗ[ℂ] HardyDisk) =
      LinearMap.range
        ((hardyMul (B₀.mul B₁) : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk) by
      exact (range_hardyMul_mul B₀ B₁).symm] at hsplit
  exact hsplit

/-- The two summands in the arbitrary-inner model-space product identity are orthogonal. -/
theorem hardyMultiplierModelSpace_inner_transported_eq_zero
    (B₀ B₁ : DiskMultiplier) (x : hardyMultiplierModelSpace B₀)
    (y : hardyMultiplierModelSpace B₁) :
    inner ℂ (x : HardyDisk) (hardyMul B₀ (y : HardyDisk)) = 0 := by
  have hyrange : hardyMul B₀ (y : HardyDisk) ∈
      LinearMap.range
        ((hardyMul B₀ : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk) :=
    ⟨(y : HardyDisk), rfl⟩
  have hreverse := x.property _ hyrange
  rw [← inner_conj_symm, hreverse, map_zero]

end

end GaloisForLFunctions.HTGeometry

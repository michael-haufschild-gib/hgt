import GaloisForLFunctions.HTGeometry.L2FrameCovariance

/-!
# Orthonormal packing limits for signed covariance bounds

Density features preserve orthonormality. Bessel's inequality therefore
controls the sum of squared signed energies of every orthonormal source
family by the single covariance norm. This detects the dimensional loss
in a Hilbert norm bound without deleting any frequency interaction.
-/

open Complex MeasureTheory
open scoped InnerProduct BoundedContinuousFunction
noncomputable section
namespace GaloisForLFunctions.HTGeometry

theorem orthonormal_l2DensityFeature {ι : Type*} {f : ι → RealLineL2}
    (hf : Orthonormal ℂ f) : Orthonormal ℂ (fun i => l2DensityFeature (f i)) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [l2DensityFeature_inner, orthonormal_iff_ite.mp hf i j]
  split_ifs <;> simp

/-- Every signed analysis value is an exact density coordinate, including its sign. -/
theorem l2DensityFeature_inner_covariance_sub (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (v : ℝ →ᵇ RealLineL2)
    (θ : ℝ) (f : RealLineL2) :
    inner ℂ (l2DensityFeature f) (l2FrameCovariance μ v - (θ : ℂ) • l2FrameCovariance ν v) =
      (((∫ x, ‖inner ℂ (v x) f‖ ^ 2 ∂μ) -
        θ * (∫ x, ‖inner ℂ (v x) f‖ ^ 2 ∂ν) : ℝ) : ℂ) := by
  rw [inner_sub_right, inner_smul_right, l2DensityFeature_inner_covariance,
    l2DensityFeature_inner_covariance, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  simp only [norm_inner_symm]

/-- The same ceiling must pay for all orthogonal source directions simultaneously. -/
theorem l2Frame_difference_sum_sq_le {ι : Type*} (s : Finset ι)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (v : ℝ →ᵇ RealLineL2) (θ : ℝ) (f : ι → RealLineL2) (hf : Orthonormal ℂ f) :
    ∑ i ∈ s, ((∫ x, ‖inner ℂ (v x) (f i)‖ ^ 2 ∂μ) -
      θ * (∫ x, ‖inner ℂ (v x) (f i)‖ ^ 2 ∂ν)) ^ 2 ≤
        ‖l2FrameCovariance μ v - (θ : ℂ) • l2FrameCovariance ν v‖ ^ 2 := by
  have h := (orthonormal_l2DensityFeature hf).sum_inner_products_le
    (s := s) (l2FrameCovariance μ v - (θ : ℂ) • l2FrameCovariance ν v)
  simpa only [l2DensityFeature_inner_covariance_sub, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] using h

end GaloisForLFunctions.HTGeometry

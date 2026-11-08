import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainTriality

/-!
# A positive majorant for the Narain partition

Poisson triality turns removal of the target-area phase into a positive
partition dominating the norm at every worldsheet point.
-/

open Complex RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- At zero angular variable every charge has positive real weight. -/
theorem narainPartition_zero_phase (ρ σ : D4BMUpperHalfPlaneCoordinate) (y : ℝ) :
    narainPartition ρ σ 0 y =
      ((y * ∑' q, narainBoltzmann ρ σ y q : ℝ) : ℂ) := by
  simp only [narainPartition, narainPartitionTerm, fourierChar, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, mul_one, Complex.ofReal_mul, Complex.ofReal_tsum]

/-- Removing the spin phase gives a positive majorant for the convergent partition. -/
theorem norm_narainPartition_le_real_sum (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖narainPartition ρ σ x y‖ ≤ y * ∑' q, narainBoltzmann ρ σ y q := by
  rw [narainPartition, norm_mul, Complex.norm_of_nonneg hy.le]
  apply mul_le_mul_of_nonneg_left _ hy.le
  simpa only [norm_narainPartitionTerm] using
    norm_tsum_le_tsum_norm (summable_norm_narainPartitionTerm ρ σ x hy)

/-- Triality makes the zero-area-phase partition positive at every worldsheet point. -/
theorem narainPartition_pureArea (ρ σ τ : D4BMUpperHalfPlaneCoordinate) :
    narainPartition ⟨0, ρ.y, ρ.y_pos⟩ σ τ.x τ.y =
      ((ρ.y * ∑' q, narainBoltzmann τ σ ρ.y q : ℝ) : ℂ) := by
  rw [narainPartition_triality, narainPartition_zero_phase]

/-- One actual positive Narain partition controls the norm on the whole worldsheet. -/
theorem norm_narainPartition_le_pureArea (ρ σ τ : D4BMUpperHalfPlaneCoordinate) :
    ‖narainPartition ρ σ τ.x τ.y‖ ≤
      (narainPartition ⟨0, ρ.y, ρ.y_pos⟩ σ τ.x τ.y).re := by
  rw [narainPartition_pureArea, Complex.ofReal_re, narainPartition_triality]
  exact norm_narainPartition_le_real_sum τ σ ρ.x ρ.y_pos

/-- The dominating partition has zero imaginary part and nonnegative real part. -/
theorem narainPartition_pureArea_nonneg (ρ σ τ : D4BMUpperHalfPlaneCoordinate) :
    0 ≤ (narainPartition ⟨0, ρ.y, ρ.y_pos⟩ σ τ.x τ.y).re ∧
      (narainPartition ⟨0, ρ.y, ρ.y_pos⟩ σ τ.x τ.y).im = 0 := by
  rw [narainPartition_pureArea, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨mul_nonneg ρ.y_pos.le (tsum_nonneg fun q => (Real.exp_pos _).le), rfl⟩

#print axioms norm_narainPartition_le_pureArea
#print axioms narainPartition_pureArea_nonneg
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

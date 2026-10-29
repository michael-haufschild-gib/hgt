import GaloisForLFunctions.HTGeometry.ParityGaussianPoisson
import GaloisForLFunctions.HTGeometry.IntrinsicLatticeTheta

/-!
# Parity Poisson summation on intrinsic dual lattices

Reindexing affine parity Poisson through actual lattice-point bijections replaces
integer coordinates by the lattice and its integer dual. The Fourier multiplier
is inverse covolume times the parity Gaussian factor. Both physical and dual
series converge absolutely, also for shifted and additively twisted kernels.
-/

noncomputable section
open MeasureTheory Module
open scoped Classical
namespace GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
variable {ι : Type*} [Fintype ι]
local notation "X" => ι → ℝ
local notation "E" => EuclideanSpace ℝ ι

/-- Absolute convergence of shifted, modulated parity kernels on an actual lattice. -/
theorem summable_norm_intrinsic_parity_affine (B : E ≃L[ℝ] E) (ε : ι → Bool)
    {t : ℝ} (ht : 0 < t) (v w : E) :
    Summable (fun x : coordinateLattice B =>
      ‖parityModulation ε t w (WithLp.toLp 2 (x : X) + v)‖) := by
  apply (latticePointEquiv B).summable_iff.mp
  exact summable_norm_parityModulation_affine B ε ht v w

/-- Parity Poisson summation over a lattice and its intrinsic integer dual. -/
theorem intrinsic_parity_poisson (B : E ≃L[ℝ] E) (ε : ι → Bool)
    {t : ℝ} (ht : 0 < t) (v w : E) :
    (∑' x : coordinateLattice B,
      parityModulation ε t w (WithLp.toLp 2 (x : X) + v)) =
    (((ZLattice.covolume (coordinateLattice B))⁻¹ : ℝ) : ℂ) *
      ((t ^ (-((finrank ℝ E : ℝ)/2)) : ℝ) : ℂ) *
      (-Complex.I/(t : ℂ)) ^ parityDegree ε *
      ∑' x : DualZLattice.dual (coordinateLattice B),
        latticePhase v (WithLp.toLp 2 (x : X)) *
          parityGaussian ε (1/t) (WithLp.toLp 2 (x : X) - w) := by
  rw [dual_coordinateLattice, ← latticeScale_eq_inv_covolume]
  have hp := (latticePointEquiv B).tsum_eq
    (fun x : coordinateLattice B => parityModulation ε t w (WithLp.toLp 2 (x : X) + v))
  have hd := (latticePointEquiv (inverseAdjointEquiv B)).tsum_eq
    (fun x : coordinateLattice (inverseAdjointEquiv B) =>
      latticePhase v (WithLp.toLp 2 (x : X)) *
        parityGaussian ε (1/t) (WithLp.toLp 2 (x : X) - w))
  rw [← hp, ← hd]
  exact parity_gaussian_theta_characteristics B ε ht v w

/-- The intrinsic parity transform on the integer span of any real basis. -/
theorem intrinsic_parity_basis_poisson (b : Basis ι ℝ X) (ε : ι → Bool)
    {t : ℝ} (ht : 0 < t) (v w : E) :
    (∑' x : Submodule.span ℤ (Set.range b),
      parityModulation ε t w (WithLp.toLp 2 (x : X) + v)) =
    (((ZLattice.covolume (Submodule.span ℤ (Set.range b)))⁻¹ : ℝ) : ℂ) *
      ((t ^ (-((finrank ℝ E : ℝ)/2)) : ℝ) : ℂ) *
      (-Complex.I/(t : ℂ)) ^ parityDegree ε *
      ∑' x : DualZLattice.dual (Submodule.span ℤ (Set.range b)),
        latticePhase v (WithLp.toLp 2 (x : X)) *
          parityGaussian ε (1/t) (WithLp.toLp 2 (x : X) - w) := by
  have h := intrinsic_parity_poisson (basisLatticeEquiv b) ε ht v w
  rw [coordinateLattice_basisLatticeEquiv] at h
  exact h

theorem summable_norm_intrinsic_parity_basis_affine (b : Basis ι ℝ X) (ε : ι → Bool)
    {t : ℝ} (ht : 0 < t) (v w : E) :
    Summable (fun x : Submodule.span ℤ (Set.range b) =>
      ‖parityModulation ε t w (WithLp.toLp 2 (x : X) + v)‖) := by
  have h := summable_norm_intrinsic_parity_affine (basisLatticeEquiv b) ε ht v w
  rw [coordinateLattice_basisLatticeEquiv] at h
  exact h

/-- Absolute convergence of the dual phase-weighted parity series. -/
theorem summable_norm_intrinsic_dual_parity (B : E ≃L[ℝ] E) (ε : ι → Bool)
    {t : ℝ} (ht : 0 < t) (v w : E) :
    Summable (fun x : DualZLattice.dual (coordinateLattice B) =>
      ‖latticePhase v (WithLp.toLp 2 (x : X)) *
        parityGaussian ε t (WithLp.toLp 2 (x : X) - w)‖) := by
  rw [dual_coordinateLattice]
  apply (latticePointEquiv (inverseAdjointEquiv B)).summable_iff.mp
  exact summable_norm_dual_parity_phase B ε ht v w

theorem summable_norm_intrinsic_dual_parity_basis (b : Basis ι ℝ X) (ε : ι → Bool)
    {t : ℝ} (ht : 0 < t) (v w : E) :
    Summable (fun x : DualZLattice.dual (Submodule.span ℤ (Set.range b)) =>
      ‖latticePhase v (WithLp.toLp 2 (x : X)) *
        parityGaussian ε t (WithLp.toLp 2 (x : X) - w)‖) := by
  have h := summable_norm_intrinsic_dual_parity (basisLatticeEquiv b) ε ht v w
  rw [coordinateLattice_basisLatticeEquiv] at h
  exact h

end GaloisForLFunctions.HTGeometry.IntegerLatticePoisson

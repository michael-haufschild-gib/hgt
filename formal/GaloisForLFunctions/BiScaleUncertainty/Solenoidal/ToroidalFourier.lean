import GaloisForLFunctions.HTGeometry.SchwartzSobolevEstimate
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Fourier invariance of toroidal Schwartz fields

A toroidal field has both zero divergence and zero radial contraction.
Fourier transform exchanges these two equations, with the factors dictated
by the `exp(-2π i ⟪x,ξ⟫)` normalization. Their common kernel is consequently
Fourier invariant. This is the mechanism in Section 4.2 of
Do–Duong–Lam–Lu–Nguyen, *Second order Heisenberg Uncertainty Principle for
solenoidal fields*, https://arxiv.org/abs/2611.00362.

The derivatives here are actual Schwartz-space directional derivatives.
-/

noncomputable section
open scoped SchwartzMap FourierTransform LineDeriv BigOperators
open LineDeriv FourierTransform

namespace GaloisForLFunctions.BiScaleUncertainty.Solenoidal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Space (ι : Type*) [Fintype ι] := EuclideanSpace ℝ ι
abbrev ScalarSchwartz (ι : Type*) [Fintype ι] := SchwartzMap (Space ι) ℂ
abbrev Field (ι : Type*) [Fintype ι] := ι → ScalarSchwartz ι

/-- Multiplication by one real coordinate, as a complex-linear operator. -/
def position (i : ι) : ScalarSchwartz ι →ₗ[ℂ] ScalarSchwartz ι where
  toFun f := SchwartzMap.smulLeftCLM ℂ (inner ℝ · (EuclideanSpace.single i 1)) f
  map_add' f g := map_add _ f g
  map_smul' c f := by
    ext x
    have hg : (inner ℝ · (EuclideanSpace.single i 1 : Space ι)).HasTemperateGrowth :=
      ((innerSL ℝ).flip (EuclideanSpace.single i 1)).hasTemperateGrowth
    simp only [RingHom.id_apply, smul_apply, SchwartzMap.smulLeftCLM_apply hg]
    change inner ℝ x (EuclideanSpace.single i 1) • (c • f x) =
      c • (inner ℝ x (EuclideanSpace.single i 1) • f x)
    exact smul_comm _ _ _

theorem position_apply (i : ι) (f : ScalarSchwartz ι) (x : Space ι) :
    position i f x = (x i : ℂ) * f x := by
  have hg : (inner ℝ · (EuclideanSpace.single i 1 : Space ι)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (EuclideanSpace.single i 1)).hasTemperateGrowth
  change (SchwartzMap.smulLeftCLM ℂ (inner ℝ · (EuclideanSpace.single i 1)) f) x = _
  rw [SchwartzMap.smulLeftCLM_apply hg]
  simp [EuclideanSpace.inner_single_right]

/-- Divergence on an actual vector-valued Schwartz field. -/
def divergence : Field ι →ₗ[ℂ] ScalarSchwartz ι :=
  ∑ i, (lineDerivOpCLM ℂ (ScalarSchwartz ι)
    (EuclideanSpace.single i 1 : Space ι)).toLinearMap.comp
    (LinearMap.proj i)

/-- Radial contraction `x · U(x)`. -/
def radialContraction : Field ι →ₗ[ℂ] ScalarSchwartz ι :=
  ∑ i, (position i).comp (LinearMap.proj i)

theorem divergence_apply (U : Field ι) :
    divergence U = ∑ i, ∂_{(EuclideanSpace.single i 1 : Space ι)} (U i) := by
  simp [divergence]

theorem radialContraction_apply (U : Field ι) :
    radialContraction U = ∑ i, position i (U i) := by
  simp [radialContraction]

theorem radialContraction_pointwise (U : Field ι) (x : Space ι) :
    radialContraction U x = ∑ i, (x i : ℂ) * U i x := by
  simp [radialContraction_apply, position_apply]

theorem divergence_pointwise (U : Field ι) (x : Space ι) :
    divergence U x = ∑ i, fderiv ℝ (U i) x (EuclideanSpace.single i 1) := by
  simp [divergence_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- Componentwise Fourier transform, with its actual inverse. -/
def fieldFourier : Field ι ≃ₗ[ℂ] Field ι where
  toFun U i := 𝓕 (U i)
  invFun U i := 𝓕⁻ (U i)
  left_inv U := by funext i; exact fourierInv_fourier_eq _
  right_inv U := by funext i; exact fourier_fourierInv_eq _
  map_add' U V := by funext i; exact fourier_add _ _
  map_smul' c U := by
    funext i
    exact fourier_smul c (U i)

/-- Fourier transform turns divergence into radial contraction. -/
theorem fourier_divergence (U : Field ι) :
    𝓕 (divergence U) = (2 * (Real.pi : ℂ) * Complex.I) •
      radialContraction (fieldFourier U) := by
  rw [divergence_apply, fourier_sum, radialContraction_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => SchwartzMap.fourier_lineDerivOp_eq _ _

/-- Radial contraction becomes divergence on the Fourier side. -/
theorem divergence_fourier (U : Field ι) :
    divergence (fieldFourier U) = -(2 * (Real.pi : ℂ) * Complex.I) •
      𝓕 (radialContraction U) := by
  rw [divergence_apply, radialContraction_apply, fourier_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (SchwartzMap.lineDerivOp_fourier_eq (U i) _).trans (fourier_smul _ _)

omit [DecidableEq ι] in
private theorem scalar_fourier_eq_zero_iff (f : ScalarSchwartz ι) : 𝓕 f = 0 ↔ f = 0 := by
  exact (fourierCLE ℂ (ScalarSchwartz ι)).map_eq_zero_iff

/-- The joint differential and radial constraint, as a complex linear subspace. -/
def toroidal : Submodule ℂ (Field ι) :=
  LinearMap.ker divergence ⊓ LinearMap.ker radialContraction

theorem mem_toroidal (U : Field ι) :
    U ∈ toroidal ↔ divergence U = 0 ∧ radialContraction U = 0 := Iff.rfl

/-- Both toroidal equations are preserved, and recovered, by Fourier transform. -/
theorem fieldFourier_mem_toroidal_iff (U : Field ι) :
    fieldFourier U ∈ toroidal ↔ U ∈ toroidal := by
  rw [mem_toroidal, mem_toroidal, divergence_fourier]
  have hc := GaloisForLFunctions.two_pi_I_ne_zero
  have hrad : radialContraction (fieldFourier U) = 0 ↔ divergence U = 0 := by
    rw [← scalar_fourier_eq_zero_iff (divergence U), fourier_divergence]
    exact (smul_eq_zero_iff_right hc).symm
  rw [smul_eq_zero_iff_right (neg_ne_zero.mpr hc), scalar_fourier_eq_zero_iff, hrad]
  exact and_comm

/-- Fourier transform is a genuine automorphism of the toroidal Schwartz space. -/
def toroidalFourier : toroidal (ι := ι) ≃ₗ[ℂ] toroidal (ι := ι) where
  toFun U := ⟨fieldFourier U.val, (fieldFourier_mem_toroidal_iff U.val).mpr U.property⟩
  invFun U := ⟨fieldFourier.symm U.val, by
    apply (fieldFourier_mem_toroidal_iff _).mp
    simpa only [LinearEquiv.apply_symm_apply] using U.property⟩
  left_inv U := by apply Subtype.ext; exact fieldFourier.symm_apply_apply U.val
  right_inv U := by apply Subtype.ext; exact fieldFourier.apply_symm_apply U.val
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul _ _ _

#print axioms fieldFourier_mem_toroidal_iff
#print axioms toroidalFourier
end GaloisForLFunctions.BiScaleUncertainty.Solenoidal

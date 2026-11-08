import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainIncompleteUnfolding

/-!
# The exact incomplete Narain overlap

Hyperbolic strip Fubini and scalar angular projection identify the
normalized incomplete Eisenstein overlap with the literal truncated
Mellin integral, including its vacuum contribution.
-/

open Complex RHTower UpperHalfPlane ModularGroup Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Angular projection identifies the unfolded seed with the literal truncated scalar Mellin integral. -/
theorem integral_narainIncompleteSeed_eq (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) (T : ℝ) :
    (∫ τ in modularStrip, narainIncompleteSeed ρ σ s T τ) =
      ∫ y in Ioc (0 : ℝ) T, (y : ℂ) ^ (s - 1) * (1 + narainScalarHeat ρ σ y) := by
  rw [setIntegral_modularStrip_eq_iterated _ (integrableOn_narainIncompleteSeed ρ σ hs T)]
  have hset : Ioi (0 : ℝ) ∩ Iic T = Ioc 0 T := by ext y; rfl
  rw [← hset, ← setIntegral_indicator measurableSet_Iic]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have he (x : ℝ) :
      narainIncompleteSeed ρ σ s T (ofComplex (⟨x, y⟩ : ℂ)) =
        if y ≤ T then (y : ℂ) ^ s * narainPartition ρ σ x y else 0 := by
    simp only [narainIncompleteSeed, narainPartitionOnUpperHalfPlane,
      ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy)]
    rfl
  simp_rw [he]
  by_cases hT : y ≤ T
  · rw [indicator_of_mem (show y ∈ Iic T from hT)]
    simp only [if_pos hT]
    rw [integral_const_mul, integral_Ico_eq_integral_Ioc,
      integral_narainPartition_eq_scalar ρ σ hy, narainScalarPartition_eq_heat ρ σ hy,
      Complex.real_smul]
    have hw : (((y ^ 2)⁻¹ : ℝ) : ℂ) * (y : ℂ) ^ s * (y : ℂ) =
        (y : ℂ) ^ (s - 1) := by
      rw [Complex.ofReal_inv, Complex.ofReal_pow,
        Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hy.ne'), Complex.cpow_one]
      field_simp [Complex.ofReal_ne_zero.mpr hy.ne']
    calc
      _ = ((((y ^ 2)⁻¹ : ℝ) : ℂ) * (y : ℂ) ^ s * (y : ℂ)) *
          (1 + narainScalarHeat ρ σ y) := by ring
      _ = _ := by rw [hw]
  · rw [indicator_of_notMem (show y ∉ Iic T from hT)]
    simp only [if_neg hT, integral_zero, smul_zero]

/-- The normalized incomplete Eisenstein overlap equals the actual scalar Mellin cutoff. -/
theorem narainPartition_incomplete_overlap (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) (T : ℝ) :
    (∫ τ in fd, ((1 / 2 : ℂ) * truncatedRowSum s T τ) *
      narainPartitionOnUpperHalfPlane ρ σ τ) =
        ∫ y in Ioc (0 : ℝ) T, (y : ℂ) ^ (s - 1) * (1 + narainScalarHeat ρ σ y) := by
  simp_rw [mul_assoc]
  rw [integral_const_mul, narainPartition_truncatedRowSum_unfold ρ σ hs T,
    integral_narainIncompleteSeed_eq ρ σ hs T]
  ring

#print axioms integral_narainIncompleteSeed_eq
#print axioms narainPartition_incomplete_overlap
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

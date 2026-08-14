import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The exponential of a complex multiple of a self-adjoint operator

For a bounded self-adjoint operator `T` on a complex Hilbert space and a complex number `w`, the
exponential `exp(w T)` splits into a self-adjoint factor and a unitary factor:

`exp(w T) = exp((Re w) T) · exp((i Im w) T)`.

The first factor is bounded by `exp(|Re w| ‖T‖)` through the functional calculus, the second is
unitary and has norm one.  Hence only the real part of `w` contributes to the growth of the
operator exponential — the estimate that keeps the Gamma strip transport bounded along every
horizontal line.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

/-- A unitary element of a `C*`-algebra has norm one. -/
theorem norm_eq_one_of_mem_unitary {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
    [NormOneClass A] [Nontrivial A] {u : A} (hu : u ∈ unitary A) : ‖u‖ = 1 := by
  have hstar : star u * u = 1 := (Unitary.mem_iff.mp hu).1
  have hsq : ‖u‖ * ‖u‖ = 1 := by
    have := CStarRing.norm_star_mul_self (x := u)
    rw [hstar, norm_one] at this
    exact this.symm
  nlinarith [norm_nonneg u, hsq]

/-- The exponential of a real multiple of a self-adjoint operator grows at most exponentially in
the norm. -/
theorem norm_exp_real_smul_le {T : X →L[ℂ] X} (hT : IsSelfAdjoint T) (r : ℝ) :
    ‖NormedSpace.exp ((r : ℝ) • T)‖ ≤ Real.exp (|r| * ‖T‖) := by
  have hsa : IsSelfAdjoint ((r : ℝ) • T) := (IsSelfAdjoint.all r).smul hT
  have hcfc : NormedSpace.exp ((r : ℝ) • T) = cfc Real.exp ((r : ℝ) • T) :=
    (CFC.real_exp_eq_normedSpace_exp hsa).symm
  rw [hcfc]
  refine norm_cfc_le (Real.exp_nonneg _) fun x hx => ?_
  have hnorm : ‖x‖ ≤ ‖(r : ℝ) • T‖ := spectrum.norm_le_norm_of_mem hx
  have hsmul : ‖(r : ℝ) • T‖ = |r| * ‖T‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have hle : x ≤ |r| * ‖T‖ := by
    have h1 : |x| ≤ |r| * ‖T‖ := by
      rwa [Real.norm_eq_abs, hsmul] at hnorm
    exact le_trans (le_abs_self x) h1
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
  exact Real.exp_le_exp.mpr hle

/-- The exponential of an imaginary multiple of a self-adjoint operator is unitary. -/
theorem norm_exp_imaginary_smul_eq_one {T : X →L[ℂ] X} (hT : IsSelfAdjoint T)
    (s : ℝ) : ‖NormedSpace.exp ((((s : ℂ) * Complex.I)) • T)‖ = 1 := by
  letI : NormedAlgebra ℚ (X →L[ℂ] X) := .restrictScalars ℚ ℂ _
  have hskew : (((s : ℂ) * Complex.I)) • T ∈ skewAdjoint (X →L[ℂ] X) := by
    rw [skewAdjoint.mem_iff, star_smul, hT.star_eq]
    have hstar : star ((s : ℂ) * Complex.I) = -((s : ℂ) * Complex.I) := by
      simp [Complex.conj_I]
    rw [hstar, neg_smul]
  have hunit := NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hskew
  exact norm_eq_one_of_mem_unitary hunit

/-- **Only the real part of the exponent contributes.**  For a self-adjoint operator the
exponential of a complex multiple is bounded by the exponential of the real part. -/
theorem norm_exp_smul_le {T : X →L[ℂ] X} (hT : IsSelfAdjoint T) (w : ℂ) :
    ‖NormedSpace.exp (w • T)‖ ≤ Real.exp (|w.re| * ‖T‖) := by
  letI : NormedAlgebra ℚ (X →L[ℂ] X) := .restrictScalars ℚ ℂ _
  have hreal : ((w.re : ℝ) : ℂ) • T = (w.re : ℝ) • T := by
    rw [← Complex.coe_algebraMap, algebraMap_smul]
  have hsplit : w • T = ((w.re : ℝ) • T) + ((((w.im : ℂ)) * Complex.I) • T) := by
    rw [← hreal, ← add_smul]
    congr 1
    exact (Complex.re_add_im w).symm
  have hcomm : Commute ((w.re : ℝ) • T) ((((w.im : ℂ)) * Complex.I) • T) := by
    rw [← hreal]
    exact ((Commute.refl T).smul_left _).smul_right _
  rw [hsplit, NormedSpace.exp_add_of_commute hcomm]
  calc ‖NormedSpace.exp ((w.re : ℝ) • T) * NormedSpace.exp ((((w.im : ℂ)) * Complex.I) • T)‖
      ≤ ‖NormedSpace.exp ((w.re : ℝ) • T)‖
        * ‖NormedSpace.exp ((((w.im : ℂ)) * Complex.I) • T)‖ := norm_mul_le _ _
    _ = ‖NormedSpace.exp ((w.re : ℝ) • T)‖ := by
        rw [norm_exp_imaginary_smul_eq_one hT w.im, mul_one]
    _ ≤ Real.exp (|w.re| * ‖T‖) := norm_exp_real_smul_le hT w.re

end

end GaloisForLFunctions.HTGeometry

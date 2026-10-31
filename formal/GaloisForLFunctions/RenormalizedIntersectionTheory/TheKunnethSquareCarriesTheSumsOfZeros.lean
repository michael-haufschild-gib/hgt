import GaloisForLFunctions.RenormalizedIntersectionTheory.TheKunnethSquareOfWeilsKernelIsRH

/-!
# The Künneth square carries the sums of zeros

The zero-side terms of Weil's kernel are absolutely summable at every scale
(`summable_norm_splineTerm`: on the strip `‖e^{t(ρ−1/2)} w_ρ‖ ≤ e^{|t|/2}‖w_ρ‖`). Hence the tensor
square of `K_ζ` is the exponential sum over pairs of zeros:

* **Künneth spectral identity** (`kunnethZeta_eq_tsum`):
  `(K_ζ ⊠ K_ζ)(u, v) = Σ_{ρ, ρ'} e^{−(ρ−1/2) log u − (ρ'−1/2) log v} w_ρ w_{ρ'}`.
* **Diagonal (Hadamard) square** (`zetaKernel_sq_eq_tsum`):
  `K_ζ(u)² = Σ_{ρ, ρ'} u^{1 − ρ − ρ'} w_ρ w_{ρ'}`: the frequencies of the diagonal are the sums
  `ρ + ρ'` of two zeros.

So the second Künneth layer of the scaling surface is the configuration of sums of zeros, the
`H¹ ⊗ H¹ ⊂ H²` of the weight route; its sign is the sign of `K_ζ`
(`riemannHypothesis_iff_negIndex_kunnethZeta_eq_zero`).
-/

open Complex
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
  GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Zeta23
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

/-- The weight `w_ρ = W_ρ(B, B)` of the cubic spline at a zero. -/
abbrev splineWeight (τ : zetaZeroConfig.carrier) : ℂ :=
  zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) τ

theorem summable_norm_splineTerm (t : ℝ) :
    Summable fun τ : zetaZeroConfig.carrier =>
      ‖cexp ((t : ℂ) * ((τ : ℂ) - 1 / 2)) * splineWeight τ‖ := by
  have hsum := summable_norm_Wsummand zetaZeroConfig SquareRootThreshold.temperedConfig_zetaZeroConfig
    (cx_contDiff contDiff_cubicSpline) (cx_hasCompactSupport hasCompactSupport_cubicSpline)
    (cx_contDiff contDiff_cubicSpline) (cx_hasCompactSupport hasCompactSupport_cubicSpline)
  refine (hsum.mul_left (Real.exp (|t| / 2))).of_nonneg_of_le (fun _ => norm_nonneg _)
    fun τ => ?_
  have hstrip := zetaZeroConfig.strip τ.1 τ.2
  rw [norm_mul, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have hre : ((t : ℂ) * ((τ : ℂ) - 1 / 2)).re = t * ((τ : ℂ).re - 1 / 2) := by simp
  rw [hre]
  have h1 : |(τ : ℂ).re - 1 / 2| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith [hstrip.1], by linarith [hstrip.2]⟩
  calc t * ((τ : ℂ).re - 1 / 2) ≤ |t * ((τ : ℂ).re - 1 / 2)| := le_abs_self _
    _ = |t| * |(τ : ℂ).re - 1 / 2| := abs_mul _ _
    _ ≤ |t| * (1 / 2) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |t| / 2 := by ring

/-- **Künneth spectral identity.** -/
theorem kunnethZeta_eq_tsum (u v : HeckeLattice) :
    kunnethZeta (u, v) = ∑' z : zetaZeroConfig.carrier × zetaZeroConfig.carrier,
      cexp (-(Real.log ((u : ℚ) : ℝ) : ℂ) * ((z.1 : ℂ) - 1 / 2) -
        (Real.log ((v : ℚ) : ℝ) : ℂ) * ((z.2 : ℂ) - 1 / 2)) * splineWeight z.1 * splineWeight z.2 := by
  rw [kunnethZeta, tensorKernel, zetaKernel_eq_splineSeries, zetaKernel_eq_splineSeries,
    splineSeries, splineSeries,
    tsum_mul_tsum_of_summable_norm (summable_norm_splineTerm _) (summable_norm_splineTerm _)]
  refine tsum_congr fun z => ?_
  rw [sub_eq_add_neg, Complex.exp_add]
  push_cast
  ring_nf

/-- **The diagonal square has the sums of zeros as frequencies.** -/
theorem zetaKernel_sq_eq_tsum (u : HeckeLattice) :
    zetaKernel u ^ 2 = ∑' z : zetaZeroConfig.carrier × zetaZeroConfig.carrier,
      cexp (-(Real.log ((u : ℚ) : ℝ) : ℂ) * ((z.1 : ℂ) + z.2 - 1)) *
        splineWeight z.1 * splineWeight z.2 := by
  have h := kunnethZeta_eq_tsum u u
  rw [kunnethZeta, tensorKernel] at h
  rw [sq, h]
  refine tsum_congr fun z => ?_
  congr 2
  ring_nf

end GaloisForLFunctions.RenormalizedIntersectionTheory

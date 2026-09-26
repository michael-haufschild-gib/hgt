import GaloisForLFunctions.HTGeometry.KernelClosedSpanInertia
import GaloisForLFunctions.RHTower.ThetaTailLaplaceTotality

/-!
# Exact finite signature of the theta tail and its double Laplace transform

Every real tail of the complete theta first-moment kernel and every positive
vertical Laplace line have the same finite negative dimensions. The statement
retains the original source, the literal double integral, and all mixed terms.
It imposes no positivity assumption and does not determine the common sign.
-/

noncomputable section
namespace RHTower.ThetaTailSignature
open DominatedL2Sections GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.KernelClosedSpanInertia
open MeasureTheory Set
open scoped InnerProductSpace

/-- Every real tail and every positive vertical Laplace line have the same
literal finite negative dimensions for the complete theta source. -/
theorem thetaTail_negative_dimensions_vertical_iff (a : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (r : ℕ) :
    HasFiniteKernelNegativeDimension
      (fun x y : Ioi a => (thetaTailFirstMomentKernel x y : ℂ)) r ↔
    HasFiniteKernelNegativeDimension
      (fun t u : ℝ => thetaBilateralLaplaceBezoutian
        ((σ:ℂ)+(t:ℂ)*Complex.I) ((σ:ℂ)+(u:ℂ)*Complex.I)) r := by
  have hs := (real_tail_closedSpan_eq a).trans (laplace_closedSpan_eq hσ).symm
  have hi := kernel_negative_iff_of_closedSpan_eq differenceForm
    (fun x : Ioi a => completeThetaSource.section (x:ℂ))
    (fun t : ℝ => laplaceSection ((σ:ℂ)+(t:ℂ)*Complex.I) (by simpa using hσ)) hs r
  simp_rw [real_section_kernel, laplace_section_kernel] at hi
  exact (kernel_negative_scale_iff _ (by norm_num : (0:ℝ)<2) r).symm.trans
    (hi.trans (kernel_negative_scale_iff _ (by norm_num : (0:ℝ)<2) r))

/-- Euler-line specialization of the exact source signature identity. -/
theorem thetaTail_negative_dimensions_eulerLine_iff (a : ℝ) {σ : ℝ}
    (hσ : 1/2 < σ) (r : ℕ) :
    HasFiniteKernelNegativeDimension
      (fun x y : Ioi a => (thetaTailFirstMomentKernel x y : ℂ)) r ↔
    HasFiniteKernelNegativeDimension
      (fun t u : ℝ => thetaBilateralLaplaceBezoutian
        ((σ:ℂ)+(t:ℂ)*Complex.I) ((σ:ℂ)+(u:ℂ)*Complex.I)) r :=
  thetaTail_negative_dimensions_vertical_iff a (by linarith) r

/-- The signature identity for the literal product-measure double Laplace integral. -/
theorem thetaTail_negative_dimensions_doubleLaplace_iff (a : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (r : ℕ) :
    HasFiniteKernelNegativeDimension
      (fun x y : Ioi a => (thetaTailFirstMomentKernel x y : ℂ)) r ↔
    HasFiniteKernelNegativeDimension
      (fun t u : ℝ => ∫ z : ℝ × ℝ,
        thetaTailDoubleLaplaceIntegrand ((σ:ℂ)+(t:ℂ)*Complex.I)
          ((σ:ℂ)+(u:ℂ)*Complex.I) z ∂(volume.prod volume)) r := by
  have he (t u : ℝ) :
      (∫ z : ℝ × ℝ, thetaTailDoubleLaplaceIntegrand ((σ:ℂ)+(t:ℂ)*Complex.I)
        ((σ:ℂ)+(u:ℂ)*Complex.I) z ∂(volume.prod volume)) =
      thetaBilateralLaplaceBezoutian ((σ:ℂ)+(t:ℂ)*Complex.I)
        ((σ:ℂ)+(u:ℂ)*Complex.I) := by
    apply integral_thetaTailDoubleLaplaceIntegrand_eq_bilateralLaplaceBezoutian
      (c := 1) (by norm_num)
    simpa using add_pos hσ hσ
  simp_rw [he]
  exact thetaTail_negative_dimensions_vertical_iff a hσ r

end RHTower.ThetaTailSignature

import GaloisForLFunctions.HTGeometry.CauchyMatrixDeterminant

/-!
# Complete neutral screening kernel and its retained Cauchy interaction

For every integer count, the level-four neutral position kernel retains all
within-charge squared distances and all opposite-charge inverse sixth powers.
The current corpus Cauchy determinant identity gives its exact decomposition
as the squared norm of the Cauchy determinant divided by the fourth power of
the product of all opposite-charge distances.

The result covers all configurations, including totalized collision values,
without an additional separation premise. It is a pointwise source identity;
no admission, regularized integral, fractional count, gauge-volume cancellation,
physical normalization or Ward vanishing is asserted. In particular the retained
pair interaction cannot be dropped when proposing a determinant continuation.
-/

open Finset Matrix
noncomputable section
namespace GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

def fzzNeutralScreeningCrossDistance {n : ℕ} (z w : Fin n → ℂ) : ℝ :=
  ∏ i, ∏ j, ‖z i-w j‖

def fzzNeutralScreeningWithinDistance {n : ℕ} (z w : Fin n → ℂ) : ℝ :=
  ∏ i, ∏ j ∈ Finset.Ioi i, ‖z i-z j‖*‖w i-w j‖

/-- Literal neutral position kernel at level four, with every pair retained. -/
def fzzNeutralCubicScreeningKernel {n : ℕ} (z w : Fin n → ℂ) : ℝ :=
  (∏ i, ∏ j ∈ Finset.Ioi i, ‖z i-z j‖^2*‖w i-w j‖^2)*
    ∏ i, ∏ j, (‖z i-w j‖^6)⁻¹

private theorem kernel_quotient {n : ℕ} (z w : Fin n → ℂ) :
    fzzNeutralCubicScreeningKernel z w =
      (fzzNeutralScreeningWithinDistance z w)^2/(fzzNeutralScreeningCrossDistance z w)^6 := by
  unfold fzzNeutralCubicScreeningKernel fzzNeutralScreeningWithinDistance
    fzzNeutralScreeningCrossDistance
  simp only [← mul_pow,Finset.prod_pow,Finset.prod_inv_distrib,div_eq_mul_inv]

private theorem cauchy_norm {n : ℕ} (z w : Fin n → ℂ)
    (h : fzzNeutralScreeningCrossDistance z w ≠ 0) :
    ‖(cauchyMatrix z (fun j => -w j)).det‖*fzzNeutralScreeningCrossDistance z w =
      fzzNeutralScreeningWithinDistance z w := by
  have hne (i j : Fin n) : z i+ -w j ≠ 0 := by
    have hi := (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)
    have hij := (Finset.prod_ne_zero_iff.mp hi) j (Finset.mem_univ j)
    exact norm_ne_zero_iff.mp hij
  have hd := congrArg (fun q : ℂ => ‖q‖) (det_cauchyMatrix z (fun j => -w j) hne)
  simp only [norm_mul,norm_prod,← sub_eq_add_neg] at hd
  have hs (i j : Fin n) : -w i - -w j = -(w i-w j) := by ring
  simpa only [hs,norm_neg,fzzNeutralScreeningCrossDistance,
    fzzNeutralScreeningWithinDistance] using hd

/-- The source is a Cauchy determinant squared with a retained interaction
between every opposite-charge pair. The equality also covers totalized collisions. -/
theorem fzzNeutralCubicScreeningKernel_eq_cauchy_interaction {n : ℕ}
    (z w : Fin n → ℂ) :
    fzzNeutralCubicScreeningKernel z w =
      ‖(cauchyMatrix z (fun j => -w j)).det‖^2/
        (fzzNeutralScreeningCrossDistance z w)^4 := by
  rw [kernel_quotient]
  by_cases h : fzzNeutralScreeningCrossDistance z w = 0
  · simp only [h,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,div_zero]
  · rw [← cauchy_norm z w h]
    field_simp

end GaloisForLFunctions.RHTower

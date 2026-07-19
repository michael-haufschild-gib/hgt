import GaloisForLFunctions.HTGeometry.GramOffDiagonalBound
import GaloisForLFunctions.HTGeometry.HalfLineSteinRobertson

/-!
# Cauchy-Schwarz for the measure pairing of two kernels

The off-diagonal entry of a Pick Gram matrix is the pairing of the Cauchy kernels at two nodes.  Its
modulus is bounded by the geometric mean of the two diagonal entries.

No integrability of the product is needed: the modulus of an integral never exceeds the integral of
the modulus, and the resulting real pairing is bounded by Cauchy-Schwarz using only square
integrability of each factor.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- **Cauchy-Schwarz for a complex measure pairing.**  The squared modulus of the pairing is bounded
by the product of the two energies. -/
theorem norm_integral_mul_conj_sq_le
    {ν : Measure ℝ} {f g : ℝ → ℂ}
    (hf : AEStronglyMeasurable (fun t => ‖f t‖) ν)
    (hg : AEStronglyMeasurable (fun t => ‖g t‖) ν)
    (hfsq : Integrable (fun t => ‖f t‖ ^ 2) ν)
    (hgsq : Integrable (fun t => ‖g t‖ ^ 2) ν) :
    ‖∫ t, f t * (starRingEnd ℂ) (g t) ∂ν‖ ^ 2 ≤
      (∫ t, ‖f t‖ ^ 2 ∂ν) * (∫ t, ‖g t‖ ^ 2 ∂ν) := by
  have hnorm : ‖∫ t, f t * (starRingEnd ℂ) (g t) ∂ν‖ ≤ ∫ t, ‖f t‖ * ‖g t‖ ∂ν := by
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    congr 1
    funext t
    rw [norm_mul, Complex.norm_conj]
  have hcs := _root_.HTGeometry.sq_integral_mul_le_integral_sq_mul_integral_sq hf hg hfsq hgsq
  calc ‖∫ t, f t * (starRingEnd ℂ) (g t) ∂ν‖ ^ 2
      ≤ (∫ t, ‖f t‖ * ‖g t‖ ∂ν) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∫ t, ‖f t‖ ^ 2 ∂ν) * (∫ t, ‖g t‖ ^ 2 ∂ν) := hcs

/-- **The scaled Gram off-diagonal is bounded by the diagonal.**  The squared modulus of the pairing
of the scaled Cauchy kernels at two nodes is at most the product of the two atom kernel integrals. -/
theorem norm_scaledPairing_sq_le_atomKernel_mul
    {ν : Measure ℝ} {a b y : ℝ}
    (hfm : AEStronglyMeasurable
      (fun t : ℝ => ‖(y : ℂ) * ((t : ℂ) - upperNode a y)⁻¹‖) ν)
    (hgm : AEStronglyMeasurable
      (fun t : ℝ => ‖(y : ℂ) * ((t : ℂ) - upperNode b y)⁻¹‖) ν)
    (hfi : Integrable (fun t : ℝ => atomKernel a y t) ν)
    (hgi : Integrable (fun t : ℝ => atomKernel b y t) ν) :
    ‖∫ t, ((y : ℂ) * ((t : ℂ) - upperNode a y)⁻¹) *
        (starRingEnd ℂ) ((y : ℂ) * ((t : ℂ) - upperNode b y)⁻¹) ∂ν‖ ^ 2 ≤
      (∫ t, atomKernel a y t ∂ν) * (∫ t, atomKernel b y t ∂ν) := by
  have hfsq : Integrable
      (fun t : ℝ => ‖(y : ℂ) * ((t : ℂ) - upperNode a y)⁻¹‖ ^ 2) ν :=
    (integrable_normSq_scaled_cauchy_iff ν a y).2 hfi
  have hgsq : Integrable
      (fun t : ℝ => ‖(y : ℂ) * ((t : ℂ) - upperNode b y)⁻¹‖ ^ 2) ν :=
    (integrable_normSq_scaled_cauchy_iff ν b y).2 hgi
  have h := norm_integral_mul_conj_sq_le hfm hgm hfsq hgsq
  rwa [integral_normSq_scaled_cauchy ν a y, integral_normSq_scaled_cauchy ν b y] at h

end

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.RHTower.FokasLenellsCutoffComplexCauchy
import GaloisForLFunctions.RHTower.FokasLenellsHardyOrientation

/-!
# Exact Hardy range and concrete invisible vectors at complex time

Entire complex evolution is invertible before Cauchy compression. Its
compressed range is always the same lower Hardy space; its kernel is the
inverse image of the upper Hardy space. Actual lower-pole rational probes
give nonzero invisible vectors at every cutoff and complex time.
-/

open MeasureTheory Complex Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem complex_inverse_apply (a : ℝ) (τ : ℂ) (u : SoninL2) :
    cutoffComplexOperator a 0 τ (cutoffComplexOperator a 0 (-τ) u) = u := by
  have h := Ring.mul_inverse_cancel (cutoffComplexOperator a 0 τ) (isUnit_cutoffComplexOperator a τ)
  rw [ringInverse_cutoffComplexOperator] at h
  exact congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T u) h

/-- Complex Cauchy compression has precisely the unchanged lower-half-plane Hardy range. -/
theorem cutoffComplexCauchyOperator_range_iff (a : ℝ) (τ : ℂ) (u : SoninL2) :
    (∃ v : SoninL2, cutoffComplexCauchyOperator a 0 τ v = u) ↔ u ∈ hardyL2ᗮ := by
  constructor
  · rintro ⟨v,rfl⟩
    exact (negativeCauchy_eq_neg_iff _).1 (negativeCauchy_square _)
  · intro hu
    refine ⟨cutoffComplexOperator a 0 (-τ) (-u),?_⟩
    change negativeCauchy (cutoffComplexOperator a 0 τ (cutoffComplexOperator a 0 (-τ) (-u))) = u
    rw [complex_inverse_apply,map_neg,(negativeCauchy_eq_neg_iff u).2 hu,neg_neg]

/-- The complete compressed kernel is the inverse evolution of the upper-half-plane Hardy space. -/
theorem cutoffComplexCauchyOperator_kernel_iff (a : ℝ) (τ : ℂ) (u : SoninL2) :
    cutoffComplexCauchyOperator a 0 τ u = 0 ↔
      ∃ v : SoninL2, v ∈ hardyL2 ∧ u = cutoffComplexOperator a 0 (-τ) v := by
  constructor
  · intro hu
    refine ⟨cutoffComplexOperator a 0 τ u,(negativeCauchy_eq_zero_iff _).1 hu,?_⟩
    have h := complex_inverse_apply a (-τ) u
    simpa only [neg_neg] using h.symm
  · rintro ⟨v,hv,rfl⟩
    change negativeCauchy (cutoffComplexOperator a 0 τ (cutoffComplexOperator a 0 (-τ) v)) = 0
    rw [complex_inverse_apply]
    exact (negativeCauchy_eq_zero_iff v).2 hv

/-- Every actual lower-pole rational probe is a nonzero vector in the original L2 carrier. -/
theorem lowerPoleProbe_ne_zero (r b : ℝ) : lowerPoleProbe r b ≠ 0 := by
  intro h0
  have hae := (memLp_cauchyKernel (w := (r:ℂ)-(Real.exp b:ℂ)*I)
    (by simpa only [Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_mul,add_zero,zero_add,zero_sub,neg_ne_zero,
      neg_lt_zero] using Real.exp_ne_zero b)).coeFn_toLp
  change (lowerPoleProbe r b : ℝ → ℂ) =ᵐ[volume]
    (fun x : ℝ => ((x:ℂ)-((r:ℂ)-(Real.exp b:ℂ)*I))⁻¹) at hae
  rw [h0] at hae
  have hz : ∀ᵐ x ∂(volume : Measure ℝ), False := by
    filter_upwards [hae,Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hzero
    have hd : (x:ℂ)-((r:ℂ)-(Real.exp b:ℂ)*I) ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      simp at hi
      exact Real.exp_ne_zero b hi
    exact (inv_ne_zero hd) (hx.symm.trans hzero)
  obtain ⟨x,hx⟩ := hz.exists
  exact hx

/-- An explicit rational Hardy vector pulled back by actual inverse complex evolution. -/
def cutoffComplexHardyKernelVector (a : ℝ) (τ : ℂ) (r b : ℝ) : SoninL2 :=
  cutoffComplexOperator a 0 (-τ) (lowerPoleProbe r b)

/-- The explicit invisible vector is nonzero at every width, time, and rational-probe location. -/
theorem cutoffComplexHardyKernelVector_ne_zero (a : ℝ) (τ : ℂ) (r b : ℝ) :
    cutoffComplexHardyKernelVector a τ r b ≠ 0 := by
  intro h0
  have h := congrArg (cutoffComplexOperator a 0 τ) h0
  change cutoffComplexOperator a 0 τ (cutoffComplexOperator a 0 (-τ) (lowerPoleProbe r b)) = _ at h
  rw [complex_inverse_apply,map_zero] at h
  exact lowerPoleProbe_ne_zero r b h

/-- Actual Cauchy compression kills this explicit nonzero inverse-evolved rational vector. -/
theorem cutoffComplexCauchyOperator_kernelVector (a : ℝ) (τ : ℂ) (r b : ℝ) :
    cutoffComplexCauchyOperator a 0 τ (cutoffComplexHardyKernelVector a τ r b) = 0 := by
  change negativeCauchy (cutoffComplexOperator a 0 τ
    (cutoffComplexOperator a 0 (-τ) (lowerPoleProbe r b))) = 0
  rw [complex_inverse_apply,negativeCauchy_lowerPoleProbe]

/-- Despite exact operator-norm preservation, every complex-time Cauchy operator is noninjective. -/
theorem cutoffComplexCauchyOperator_not_injective (a : ℝ) (τ : ℂ) :
    ¬ Function.Injective (cutoffComplexCauchyOperator a 0 τ) := by
  intro h
  apply cutoffComplexHardyKernelVector_ne_zero a τ 0 0
  apply h
  rw [cutoffComplexCauchyOperator_kernelVector,map_zero]

end
end RHTower.FokasLenells

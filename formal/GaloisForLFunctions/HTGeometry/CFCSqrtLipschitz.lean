import GaloisForLFunctions.HTGeometry.SylvesterInverseBounds
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinNormBounds

/-!
# The square root is Lipschitz on a Loewner interval

`√b (√b - √c) + (√b - √c) √c = b - c` is a Sylvester equation with positive coefficients, so the
Sylvester norm bounds give `2√α ‖√b - √c‖ ≤ ‖b - c‖` whenever `α · 1 ≤ b, c`, in the operator norm
and in the Hilbert–Schmidt norm, and the same identity shows the square root preserves the
Hilbert–Schmidt class.
-/

open scoped Ring BigOperators
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The Sylvester equation for the difference of two square roots. -/
theorem cfcSqrt_sub_sylvester' {b c : A} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    CFC.sqrt b * (CFC.sqrt b - CFC.sqrt c) + (CFC.sqrt b - CFC.sqrt c) * CFC.sqrt c = b - c := by
  have h1 : CFC.sqrt b * CFC.sqrt b = b := CFC.sqrt_mul_sqrt_self b hb
  have h2 : CFC.sqrt c * CFC.sqrt c = c := CFC.sqrt_mul_sqrt_self c hc
  have hexp : CFC.sqrt b * (CFC.sqrt b - CFC.sqrt c) + (CFC.sqrt b - CFC.sqrt c) * CFC.sqrt c
      = CFC.sqrt b * CFC.sqrt b - CFC.sqrt c * CFC.sqrt c := by noncomm_ring
  rw [hexp, h1, h2]

/-- A Loewner lower bound passes to the square root. -/
lemma smul_one_le_cfcSqrt {b : A} {α : ℝ} (hα : 0 < α) (hbα : α • (1 : A) ≤ b) :
    (Real.sqrt α) • (1 : A) ≤ CFC.sqrt b := by
  have hm := CFC.sqrt_le_sqrt _ _ hbα
  rwa [BuresWasserstein.cfcSqrt_smul hα.le (zero_le_one (α := A)), CFC.sqrt_one] at hm

/-- **The square root is Lipschitz on a Loewner interval** (operator norm). -/
theorem norm_cfcSqrt_sub_le_of_Icc {b c : A} {α : ℝ} (hα : 0 < α)
    (hbα : α • (1 : A) ≤ b) (hcα : α • (1 : A) ≤ c) :
    (2 * Real.sqrt α) * ‖CFC.sqrt b - CFC.sqrt c‖ ≤ ‖b - c‖ := by
  have hbnn : (0 : A) ≤ b := le_trans (smul_nonneg hα.le zero_le_one) hbα
  have hcnn : (0 : A) ≤ c := le_trans (smul_nonneg hα.le zero_le_one) hcα
  have hpos : (0 : ℝ) < Real.sqrt α := Real.sqrt_pos.mpr hα
  have h := norm_le_of_sylvester (CFC.sqrt_nonneg b).isSelfAdjoint
    (CFC.sqrt_nonneg c).isSelfAdjoint hpos hpos (smul_one_le_cfcSqrt hα hbα)
    (smul_one_le_cfcSqrt hα hcα) (cfcSqrt_sub_sylvester' hbnn hcnn)
  calc (2 * Real.sqrt α) * ‖CFC.sqrt b - CFC.sqrt c‖
      = (Real.sqrt α + Real.sqrt α) * ‖CFC.sqrt b - CFC.sqrt c‖ := by ring
    _ ≤ ‖b - c‖ := h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]

/-- **The square root is Lipschitz on a Loewner interval** (Hilbert–Schmidt norm). -/
theorem hsNorm_cfcSqrt_sub_le_of_Icc {b c : E →L[ℂ] E} {α : ℝ} (hα : 0 < α)
    (hbα : α • (1 : E →L[ℂ] E) ≤ b) (hcα : α • (1 : E →L[ℂ] E) ≤ c)
    (h : IsHilbertSchmidt (b - c)) :
    (2 * Real.sqrt α) * hsNorm (CFC.sqrt b - CFC.sqrt c) ≤ hsNorm (b - c) := by
  have hbnn : (0 : E →L[ℂ] E) ≤ b := le_trans (smul_nonneg hα.le zero_le_one) hbα
  have hcnn : (0 : E →L[ℂ] E) ≤ c := le_trans (smul_nonneg hα.le zero_le_one) hcα
  have hpos : (0 : ℝ) < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hzHS : IsHilbertSchmidt (CFC.sqrt b - CFC.sqrt c) :=
    isHilbertSchmidt_of_sylvester (CFC.sqrt_nonneg b).isSelfAdjoint
      (CFC.sqrt_nonneg c).isSelfAdjoint hpos hpos (smul_one_le_cfcSqrt hα hbα)
      (smul_one_le_cfcSqrt hα hcα) h (cfcSqrt_sub_sylvester' hbnn hcnn)
  have hs := hsNorm_le_of_sylvester (CFC.sqrt_nonneg b).isSelfAdjoint
    (CFC.sqrt_nonneg c).isSelfAdjoint hzHS hpos hpos (smul_one_le_cfcSqrt hα hbα)
    (smul_one_le_cfcSqrt hα hcα) (cfcSqrt_sub_sylvester' hbnn hcnn)
  calc (2 * Real.sqrt α) * hsNorm (CFC.sqrt b - CFC.sqrt c)
      = (Real.sqrt α + Real.sqrt α) * hsNorm (CFC.sqrt b - CFC.sqrt c) := by ring
    _ ≤ hsNorm (b - c) := hs

end

end GaloisForLFunctions.HTGeometry

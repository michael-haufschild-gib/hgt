import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiCriticalMarkedPolarDefectDecomposition

/-!
# Bulk orientation of the literal critical CCM--FU polar channel

The signed outgoing polar channel is not globally monotone.  This module proves its exact
bulk orientation without replacing the moving third-grade reporter by a fixed or positive
surrogate.  The factorization used below is

`H * Phi_H(h) = (h - 7) * (H - 3 - h) + (H - 21)`.

Thus every physical wall `H ≥ 21` has a complete increasing corridor `[7, H - 3]`.  The two
remaining collars retain their opposite orientation and must remain in any global producer.
-/

open Set

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

/-- On the literal physical bulk, the outgoing half-polar profile is increasing. -/
theorem ccmFUSuzukiCriticalOutgoingPolarProfile_monotoneOn_bulk
    {H : ℝ} (hH : 21 ≤ H) :
    MonotoneOn (ccmFUSuzukiCriticalOutgoingPolarProfile H) (Icc 7 (H - 3)) := by
  have hderiv : ∀ h : ℝ, h ≠ 0 →
      HasDerivAt (ccmFUSuzukiCriticalOutgoingPolarProfile H)
        (ccmFUSuzukiCriticalOutgoingPolarCellDerivative H h) h := by
    intro h hh
    unfold ccmFUSuzukiCriticalOutgoingPolarProfile
      ccmFUSuzukiCriticalOutgoingPolarCellDerivative
    have hExp : HasDerivAt (fun x : ℝ => Real.exp (x / 2))
        (Real.exp (h / 2) * (1 / 2)) h := by
      have hinner : HasDerivAt (fun x : ℝ => x / 2) (1 / 2 : ℝ) h := by
        simpa using (hasDerivAt_id h).div_const 2
      simpa using hinner.exp
    have hW : HasDerivAt (ccmGuinandWeilThirdGradeCesaroTriangularWeight H)
        (-ccmGuinandWeilThirdGradeCesaroErrorKernel H h) h :=
      hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight hh
    exact (hExp.mul hW).congr_deriv (by ring)
  apply monotoneOn_of_deriv_nonneg (convex_Icc 7 (H - 3))
  · intro h hh
    exact (hderiv h (by linarith [hh.1])).continuousAt.continuousWithinAt
  · intro h hh
    have hmem : h ∈ Icc 7 (H - 3) := interior_subset hh
    exact (hderiv h (by linarith [hmem.1])).differentiableAt.differentiableWithinAt
  · intro h hh
    have hmem : h ∈ Icc 7 (H - 3) := interior_subset hh
    rw [(hderiv h (by linarith [hmem.1])).deriv]
    have hH0 : 0 < H := by linarith
    have hh0 : 0 < h := by linarith [hmem.1]
    have hfactor : H * (h - 6) - h * (h - 4) =
        (h - 7) * (H - 3 - h) + (H - 21) := by ring
    have hbulk : 0 ≤ H * (h - 6) - h * (h - 4) := by
      rw [hfactor]
      apply add_nonneg
      · exact mul_nonneg (by linarith [hmem.1]) (by linarith [hmem.2])
      · linarith
    unfold ccmFUSuzukiCriticalOutgoingPolarCellDerivative
      ccmGuinandWeilThirdGradeCesaroTriangularWeight
      ccmGuinandWeilThirdGradeWeight
      ccmGuinandWeilThirdGradeCesaroErrorKernel
    field_simp [hH0.ne', hh0.ne']
    nlinarith [Real.exp_pos (h / 2)]

end

end GaloisForLFunctions.RHTower

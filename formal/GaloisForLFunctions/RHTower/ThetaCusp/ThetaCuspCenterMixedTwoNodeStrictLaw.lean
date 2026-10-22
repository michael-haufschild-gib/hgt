import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCenterMixedThreePoint

/-!
# Strict two-node theta-cusp center-mixed law

At positive aperture the center-mixed theta density is positive, even, and strictly smaller away
from the reflection center.  Combining this radial theorem with the unconditional two-node
positive-semidefinite Bochner wall places every nonzero displacement strictly inside the
positive-definite cone.
-/

namespace RHTower

noncomputable section

/-- **Strict two-node theta-cusp law.**  Every nonzero displacement at a positive critical
aperture gives a positive-definite center-mixed two-node Bochner matrix. -/
theorem thetaCuspCenterMixedTwoNodeMatrix_posDef
    {a t : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (ht : t ≠ 0) :
    Matrix.PosDef (thetaCuspCenterMixedTwoNodeMatrix a t) := by
  have hlt : thetaCuspCenterMixedDensity a t < thetaCuspCenterMixedDensity a 0 := by
    rcases lt_or_gt_of_ne ht with htneg | htpos
    · rw [← thetaCuspCenterMixedDensity_even a t]
      exact thetaCuspCenterMixedDensity_lt_zero ha0 ha (neg_pos.mpr htneg)
    · exact thetaCuspCenterMixedDensity_lt_zero ha0 ha htpos
  have hdet : 0 < (thetaCuspCenterMixedTwoNodeMatrix a t).det := by
    rw [Matrix.det_fin_two]
    simp [thetaCuspCenterMixedTwoNodeMatrix]
    have ht0 := thetaCuspCenterMixedDensity_nonneg (a := a) (t := t) ha0.le
    have h00 := thetaCuspCenterMixedDensity_pos ha0 ha 0
    nlinarith
  exact ((thetaCuspCenterMixedTwoNodeMatrix_posSemidef ha0.le ha t).posDef_iff_det_ne_zero).2
    hdet.ne'

/-- Equivalent ordered determinant form of strict two-node theta-cusp positivity. -/
theorem det_thetaCuspCenterMixedTwoNodeMatrix_pos
    {a t : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (ht : t ≠ 0) :
    0 < (thetaCuspCenterMixedTwoNodeMatrix a t).det :=
  (thetaCuspCenterMixedTwoNodeMatrix_posDef ha0 ha ht).det_pos

end

end RHTower

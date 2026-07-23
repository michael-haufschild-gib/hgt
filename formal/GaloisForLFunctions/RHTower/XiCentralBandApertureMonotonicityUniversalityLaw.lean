import GaloisForLFunctions.RHTower.HedenmalmCentralBandGaussianHankel
import GaloisForLFunctions.RHTower.XiNormalizedApertureRelativeKrein

/-!
# Xi central-band aperture monotonicity universality law

The normalized-aperture theory identifies the aperture derivative of the squared Xi orbit modulus
with its Krein slope.  Independently, exact off-line-quartet accretivity makes that Krein form
nonnegative on the complete central frequency band.  Therefore every central-band Xi orbit has
nondecreasing squared modulus along the entire nonnegative aperture ray.
-/

open Set

namespace RHTower

noncomputable section

/-- **Xi central-band aperture monotonicity universality law.**  Every exact off-line-quartet
accretive band is simultaneously a nonnegative-aperture monotonicity band for squared modulus of
the actual theta/Xi Hedenmalm orbit. -/
theorem xiApertureModulusSq_monotoneOn_nonnegative_of_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    {b : ℝ} (hb : |b| ≤ R) :
    MonotoneOn (fun a : ℝ => xiApertureModulusSq a b) (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · intro a _
    exact (hasDerivAt_xiApertureModulusSq a b).continuousAt.continuousWithinAt
  · intro a _
    exact (hasDerivAt_xiApertureModulusSq a b).differentiableAt.differentiableWithinAt
  · intro a ha
    rw [(hasDerivAt_xiApertureModulusSq a b).deriv]
    have haPos : 0 < a := by
      simpa only [interior_Ici, mem_Ioi] using ha
    simpa only [xiApertureKreinSlope] using
      thetaXiHankelOrbit_kreinForm_nonneg_exactOffLineQuartetBand
        R hband haPos hb

/-- Pairwise form: increasing nonnegative aperture cannot decrease central-band Xi orbit modulus
squared. -/
theorem xiApertureModulusSq_le_of_nonnegative_aperture_of_exactOffLineQuartetBand
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    {b a₁ a₂ : ℝ} (hb : |b| ≤ R) (ha₁ : 0 ≤ a₁) (ha₁₂ : a₁ ≤ a₂) :
    xiApertureModulusSq a₁ b ≤ xiApertureModulusSq a₂ b := by
  exact xiApertureModulusSq_monotoneOn_nonnegative_of_exactOffLineQuartetBand
    R hband hb ha₁ (ha₁.trans ha₁₂) ha₁₂

end

end RHTower

import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSourceProfile
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceParameters

/-! Identification of the full retained source with the endpoint Green profile. -/
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMLaplaceRadial
open D4BMModularCore D4BMHorizon
noncomputable section

/-- The original smooth-onset source's actual time integral equals the profile
used in the radial inverse, with the Xi occurrence and both angular fields fixed. -/
theorem sourceProfile_smoothCurrent (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : {r : ℝ // 1 < r}) (ang : Point) (k : Fin 2) {w : ℂ} (hw : 0 < w.re) :
    sourceProfile (physicalRate q branch) w a (fullSquareCovector q k ang)
      (fullGradientCovector q branch k ang)
      (1/(w-currentRate q branch)+onsetCorrection (currentRate q branch) w) (1-r.val⁻¹^2) =
      smoothCurrentLaplace q branch a r ang k w := by
  rw [sourceProfile_original _ _ _ _ _ _ r.property,smoothCurrentLaplace_eq q branch a r ang k hw]
  rfl

end
end RHTower.D4BMLaplaceRadial

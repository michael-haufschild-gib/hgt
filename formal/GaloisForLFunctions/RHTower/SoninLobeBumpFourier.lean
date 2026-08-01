import GaloisForLFunctions.RHTower.SoninOneSidedPacket

/-!
# The lobe profile's transform is centre free

A lobe of the annulus profile is the reference bump dilated by the half-width and translated to the
lobe's centre.  Translation contributes only a unimodular phase, so the magnitude of the lobe's
transform is the half-width times the reference magnitude at the rescaled frequency — with no
dependence on the centre at all.

This is what makes a tail estimate for the reference profile serve every annulus of the family.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- The reference profile, complexified. -/
def soninUnitBumpC : ℝ → ℂ := fun y => (soninUnitBumpData y : ℂ)

/-- The lobe profile is the reference profile dilated and translated. -/
theorem soninOneSidedBump_eq_comp (m δ : ℝ) (x : ℝ) :
    ((soninOneSidedBump m δ x : ℝ) : ℂ) = (fun y : ℝ => soninUnitBumpC (y / δ)) (x + -m) := by
  show ((soninUnitBumpData ((x - m) / δ) : ℝ) : ℂ) =
    ((soninUnitBumpData ((x + -m) / δ) : ℝ) : ℂ)
  congr 3

/-- **Transform of the lobe profile.**  A phase, the half-width, and the reference transform at the
rescaled frequency. -/
theorem fourier_soninOneSidedBump (m δ : ℝ) (hδ : 0 < δ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((soninOneSidedBump m δ x : ℝ) : ℂ)) ξ =
      Complex.exp ((↑(2 * Real.pi * -m * ξ) : ℂ) * Complex.I) •
        (δ • 𝓕 soninUnitBumpC (δ * ξ)) := by
  have hcomp : (fun x : ℝ => ((soninOneSidedBump m δ x : ℝ) : ℂ)) =
      (fun y : ℝ => soninUnitBumpC (y / δ)) ∘ fun x : ℝ => x + -m := by
    funext x
    exact soninOneSidedBump_eq_comp m δ x
  rw [hcomp]
  have htrans := GaloisForLFunctions.HTGeometry.fourierIntegral_comp_add_right
    (fun y : ℝ => soninUnitBumpC (y / δ)) (-m) ξ
  have hdil := GaloisForLFunctions.HTGeometry.fourierIntegral_comp_div soninUnitBumpC δ hδ ξ
  show 𝓕 (fun x : ℝ => (fun y : ℝ => soninUnitBumpC (y / δ)) (x + -m)) ξ =
    Complex.exp ((↑(2 * Real.pi * -m * ξ) : ℂ) * Complex.I) • (δ • 𝓕 soninUnitBumpC (δ * ξ))
  rw [htrans, hdil]

/-- **Centre freedom.**  The magnitude of the lobe profile's transform does not see the centre. -/
theorem norm_fourier_soninOneSidedBump (m δ : ℝ) (hδ : 0 < δ) (ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => ((soninOneSidedBump m δ x : ℝ) : ℂ)) ξ‖ =
      δ * ‖𝓕 soninUnitBumpC (δ * ξ)‖ := by
  rw [fourier_soninOneSidedBump m δ hδ ξ, norm_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos hδ, Complex.norm_exp]
  have harg : ((↑(2 * Real.pi * -m * ξ) : ℂ) * Complex.I).re = 0 := by
    simp
  rw [harg, Real.exp_zero, one_mul]

end RHTower

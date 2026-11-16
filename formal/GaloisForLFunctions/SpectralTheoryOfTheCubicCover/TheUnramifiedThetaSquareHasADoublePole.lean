import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTranslatedCorrelationHasADoublePole
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTranslatedDifferenceIsTheUnramifiedSquare

/-!
# The unramified theta square has a double pole

The phase selector gives `D₀ = (2/3)(D − C_U)`. The full and translated
completed series have leading coefficients `108π³r³` and `27π³r³`.
Thus the unramified contribution has leading coefficient `54π³r³`.
-/

noncomputable section
open Filter Topology

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent.CubicEisenstein

def completedUnramified (s : ℂ) : ℂ :=
  (2 / 3) * (completedThetaSq s - completedTranslated s)

theorem completedUnramified_eq (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3)
    (hi : 0 < s.im) :
    completedUnramified s = besselSqMellin s * besselDirichlet unramifiedSquareCoeff s := by
  rw [completedUnramified, completedThetaSq_eq s hs4 hs hi, completedTranslated_eq s hs4 hs hi]
  linear_combination (2 / 3 * besselSqMellin s) * thetaSqDirichlet_sub_translated s hs4

theorem completedUnramified_differentiableAt (s : ℂ) (hs1 : 1 < s.re)
    (hs : s.re < 13 / 3) (hi : 0 < s.im) : DifferentiableAt ℂ completedUnramified s :=
  ((completedThetaSq_differentiableAt s hs1 hs hi).sub
    (completedTranslated_differentiableAt s hs1 hs hi)).const_mul _

theorem completedUnramified_differentiableAt_near :
    ∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ completedUnramified s := by
  filter_upwards [completedThetaSq_differentiableAt_near,
    completedTranslated_differentiableAt_near] with s h1 h2
  exact (h1.sub h2).const_mul _

theorem completedUnramified_double_pole :
    Tendsto (fun s => (s - 4 / 3) ^ 2 * completedUnramified s) (𝓝[≠] (4 / 3 : ℂ))
      (𝓝 (6 * (Real.pi : ℂ) * thetaCoeff ^ 2 * constantArithmeticResidue)) := by
  have h := (completedThetaSq_double_pole.sub completedTranslated_double_pole).const_mul (2 / 3 : ℂ)
  have he : (2 / 3 : ℂ) *
      (12 * Real.pi * thetaCoeff ^ 2 * constantArithmeticResidue -
        3 * Real.pi * thetaCoeff ^ 2 * constantArithmeticResidue) =
      6 * Real.pi * thetaCoeff ^ 2 * constantArithmeticResidue := by ring
  rw [he] at h
  exact h.congr fun s => by dsimp only [completedUnramified]; ring

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover

import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceGaussFactors
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplacePowerJets

/-! Physical horizon dressing of actual radial fields at independent frequency. -/

open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def dress (w : ℂ) (F : ℝ → ℂ) (z : ℝ) : ℂ := power (w/2) z*F z
def dressFirst (w : ℂ) (F D : ℝ → ℂ) (z : ℝ) : ℂ :=
  powerFirst (w/2) z*F z+power (w/2) z*D z
def dressSecond (w : ℂ) (F D DD : ℝ → ℂ) (z : ℝ) : ℂ :=
  powerSecond (w/2) z*F z+2*powerFirst (w/2) z*D z+power (w/2) z*DD z

/-- Both physical dressing derivatives retain the nonconstant horizon factor. -/
theorem dress_derivatives (w : ℂ) {F D DD : ℝ → ℂ} {z : ℝ} (hz : 0 < z)
    (hF : HasDerivAt F (D z) z) (hD : HasDerivAt D (DD z) z) :
    HasDerivAt (dress w F) (dressFirst w F D z) z ∧
    HasDerivAt (dressFirst w F D) (dressSecond w F D DD z) z := by
  obtain ⟨hp,hpd⟩ := power_derivatives (w/2) hz
  constructor
  · exact hp.mul hF
  · exact ((hpd.mul hF).add (hp.mul hD)).congr_deriv (by dsimp [dressSecond]; ring)

/-- Exact physical BM operator on the dressed complete jet. -/
theorem dress_physical (w chi : ℂ) (F D DD : ℝ → ℂ) {z : ℝ} (hz : 0 < z) :
    D4BMPhysicalMaster.radialJet (Complex.I*w) chi z
      (dress w F z) (dressFirst w F D z) (dressSecond w F D DD z) =
      power (w/2) z*gaussJet w chi z (F z) (D z) (DD z) := by
  have hz0 : (z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  dsimp [D4BMPhysicalMaster.radialJet,dress,dressFirst,dressSecond,powerFirst,powerSecond,
    gaussJet,gaussA,gaussB,gaussC]
  field_simp [hz0]
  ring_nf
  simp only [Complex.I_sq]
  ring

end
end RHTower.D4BMLaplaceRadial

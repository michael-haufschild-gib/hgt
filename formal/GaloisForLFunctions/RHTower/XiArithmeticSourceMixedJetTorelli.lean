import GaloisForLFunctions.RHTower.XiArithmeticSourceMomentTorelli
import GaloisForLFunctions.RHTower.XiStratifiedFormationDaggerCoherence

open Complex Filter intervalIntegral Set
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- The mixed Real defect read directly from a centered spectral point. -/
def xiMixedJetFromSpectralPoint (w : ℂ) : ℝ :=
  -2 * (w ^ 2).im

/-- The spectral-point defect is exactly the source-marked mixed jet. -/
theorem xiMixedJetFromSpectralPoint_eq_reflectedPhaseNeutralMixedJet
    (q : XiZeroCopy) :
    xiMixedJetFromSpectralPoint (xiSpectralPoint q) =
      xiReflectedPhaseNeutralMixedJet q := by
  rw [xiMixedJetFromSpectralPoint,
    xiReflectedPhaseNeutralMixedJet_eq_neg_two_mul_squaredNode_im,
    xiSquaredNode]

/-- The mixed source jet vanishes exactly on the critical line. -/
theorem xiReflectedPhaseNeutralMixedJet_eq_zero_iff_re_eq_half
    (q : XiZeroCopy) :
    xiReflectedPhaseNeutralMixedJet q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [xiReflectedPhaseNeutralMixedJet_eq_neg_two_mul_squaredNode_im,
    xiSquaredNode_im]
  constructor
  · intro h
    have him := xiZeroCopy_fortyOne_div_two_lt_im_sq q
    have him0 : (q.1 : ℂ).im ≠ 0 := by nlinarith
    have hprod : ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im = 0 := by
      nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right him0)
  · intro h
    rw [h]
    ring

/-- Arithmetic contour moments reconstruct not only the finite Xi divisor but the complete
multiset of its signed mixed Real defects. -/
theorem xiArithmeticSourceRectangleMoment_mixedJet_torelli
    {z₁ z₂ : ℂ} (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I))
    (f : Fin (xiZeroCopyClosedRectangle z₁ z₂).card → ℂ)
    (hmom : ∀ k ≤ (xiZeroCopyClosedRectangle z₁ z₂).card,
      ∑ i, f i ^ k =
        xiArithmeticSourceRectangleMoment z₁ z₂ k) :
    (Finset.univ.val.map f).map xiMixedJetFromSpectralPoint =
      Finset.univ.val.map
        (fun i => xiReflectedPhaseNeutralMixedJet
          (xiZeroCopyClosedRectangleEnumeration z₁ z₂ i)) := by
  rw [xiArithmeticSourceRectangleMoment_torelli
    hre him hbot htop hright hleft f hmom,
    Multiset.map_map]
  congr 1
  funext i
  exact xiMixedJetFromSpectralPoint_eq_reflectedPhaseNeutralMixedJet _

end

end RHTower

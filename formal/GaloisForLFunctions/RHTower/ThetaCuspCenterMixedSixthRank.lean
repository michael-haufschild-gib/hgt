import GaloisForLFunctions.HTGeometry.SixPointSignedHankel
import GaloisForLFunctions.RHTower.ThetaCuspGlobalOddCompensation
import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedSignedJetCompleteness

/-! # The literal mixed source has a strict six-dimensional signed Hankel section -/
namespace RHTower
open GaloisForLFunctions.HTGeometry Matrix
noncomputable section
set_option maxHeartbeats 2000000

/-- Exact parity form of the actual six-dimensional signed source Hankel matrix. -/
theorem thetaCuspCenterMixedSignedHankel_six_eq (a : ℝ) :
    thetaCuspCenterMixedSignedHankel a 6 =
      sixPointSignedHankel (thetaCuspCenterMixedDensity a 0)
        (-iteratedDeriv 2 (thetaCuspCenterMixedDensity a) 0)
        (iteratedDeriv 4 (thetaCuspCenterMixedDensity a) 0)
        (-iteratedDeriv 6 (thetaCuspCenterMixedDensity a) 0)
        (iteratedDeriv 8 (thetaCuspCenterMixedDensity a) 0)
        (-iteratedDeriv 10 (thetaCuspCenterMixedDensity a) 0) := by
  have he0 := thetaCuspCenterMixedSignedJet_even a 0
  norm_num at he0
  have he1 := thetaCuspCenterMixedSignedJet_even a 1
  norm_num at he1
  have he2 := thetaCuspCenterMixedSignedJet_even a 2
  norm_num at he2
  have he3 := thetaCuspCenterMixedSignedJet_even a 3
  norm_num at he3
  have he4 := thetaCuspCenterMixedSignedJet_even a 4
  norm_num at he4
  have he5 := thetaCuspCenterMixedSignedJet_even a 5
  norm_num at he5
  have ho0 := thetaCuspCenterMixedSignedJet_odd a 0
  norm_num at ho0
  have ho1 := thetaCuspCenterMixedSignedJet_odd a 1
  norm_num at ho1
  have ho2 := thetaCuspCenterMixedSignedJet_odd a 2
  norm_num at ho2
  have ho3 := thetaCuspCenterMixedSignedJet_odd a 3
  norm_num at ho3
  have ho4 := thetaCuspCenterMixedSignedJet_odd a 4
  norm_num at ho4
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [thetaCuspCenterMixedSignedHankel, sixPointSignedHankel,
      he0, he1, he2, he3, he4, he5, ho0, ho1, ho2, ho3, ho4]

/-- Global compensation closes the full six-dimensional section at every critical aperture. -/
theorem thetaCuspCenterMixedSignedHankel_six_posDef
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (thetaCuspCenterMixedSignedHankel a 6).PosDef := by
  have h1 : 0 < -iteratedDeriv 2 (thetaCuspCenterMixedDensity a) 0 := by
    rw [iteratedDeriv_two_thetaCuspCenterMixedDensity ha0.le ha]
    exact neg_pos.mpr (thetaCuspCenterMixedDensitySecondJet_zero_neg ha0 ha)
  have h2 : 0 < thetaCuspCenterMixedDensity a 0 *
      iteratedDeriv 4 (thetaCuspCenterMixedDensity a) 0-
      (-iteratedDeriv 2 (thetaCuspCenterMixedDensity a) 0)^2 := by
    rw [iteratedDeriv_four_thetaCuspCenterMixedDensity ha0.le ha,
      iteratedDeriv_two_thetaCuspCenterMixedDensity ha0.le ha]
    simpa only [neg_sq] using thetaCuspCenterMixedDensity_fourthHankel_pos ha0 ha
  have h3 : 0 < (-iteratedDeriv 2 (thetaCuspCenterMixedDensity a) 0)*
      (-iteratedDeriv 6 (thetaCuspCenterMixedDensity a) 0)-
      (iteratedDeriv 4 (thetaCuspCenterMixedDensity a) 0)^2 := by
    simpa only [neg_mul_neg] using
      thetaCuspCenterMixedDensity_iteratedDeriv_secondSixthHankel_pos ha0 ha
  have h4 : 0 < HilbertMetric.signedEvenHankelThreeDet
      (thetaCuspCenterMixedDensity a 0)
      (-iteratedDeriv 2 (thetaCuspCenterMixedDensity a) 0)
      (iteratedDeriv 4 (thetaCuspCenterMixedDensity a) 0)
      (-iteratedDeriv 6 (thetaCuspCenterMixedDensity a) 0)
      (iteratedDeriv 8 (thetaCuspCenterMixedDensity a) 0) := by
    have h := thetaCuspCenterMixedDensity_iteratedDeriv_eighthHankel_pos ha0 ha
    unfold HilbertMetric.signedEvenHankelThreeDet at h ⊢
    nlinarith only [h]
  rw [thetaCuspCenterMixedSignedHankel_six_eq]
  exact sixPointSignedHankel_posDef (thetaCuspCenterMixedDensity_pos ha0 ha 0)
    h1 h2 h3 h4 (thetaCuspCenterMixed_oddHankelThree_pos a ha0 ha)

end
end RHTower

import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspMiddleCompensatedDeterminant
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddEnergyCompensation

/-! # Global literal-source compensation and the integrated odd rank-three determinant -/
namespace RHTower
noncomputable section

/-- Every coefficient in the proved billion-scale interval repairs the entire positive half-orbit. -/
theorem thetaCuspNativeOddCompensatedDet_pos_global {C : ℝ}
    (hC0 : 1000000000 ≤ C) (hC1 : C ≤ 3000000000) :
    ∀ x : ℝ, 0 ≤ x → 0 < thetaCuspNativeOddCompensatedDet C x := by
  intro x hx
  by_cases hsmall : x ≤ 8/95
  · exact thetaCuspNativeOddCompensatedDet_pos_on_energy_interval hC0 ⟨hx, hsmall⟩
  · have hq0 := thirtySevenTenths_le_firstAtomScale_of_energy_endpoint (le_of_not_ge hsmall)
    by_cases hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 7
    · exact thetaCuspNativeOddCompensatedDet_pos_on_middle (by linarith) hC1 hq0 hq1
    · exact thetaCuspNativeOddCompensatedDet_pos_of_seven_le (by linarith) hC1 (le_of_not_ge hq1)

/-- Closed canonical compensation positivity, including every center in the former middle gap. -/
theorem thetaCuspNativeOddCanonicalCompensatedDet_pos_global :
    ∀ x : ℝ, 0 ≤ x →
      0 < thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient x :=
  thetaCuspNativeOddCompensatedDet_pos_global
    thetaCuspNativeOddCompensationCoefficient_bounds.1.le
    thetaCuspNativeOddCompensationCoefficient_bounds.2.le

/-- The literal corrected weighted determinant is positive at every positive aperture and center. -/
theorem thetaCuspCenterCorrectedOddDet_pos_global {a C r : ℝ}
    (ha : 0 < a) (hC0 : 1000000000 ≤ C) (hC1 : C ≤ 3000000000) (hr : 0 < r) :
    0 < thetaCuspCenterCorrectedOddDet a C r := by
  have hs := thetaCuspNativeOddCompensatedDet_pos_global hC0 hC1 (r/2) (by linarith)
  have hw : 0 < r*Real.sinh (a*r) := mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha hr))
  exact (mul_pos (pow_pos hw 3) hs).trans_le
    (thetaCuspCenterCorrectedOddDet_lower ha.le (by linarith) hr.le)

/-- Unconditional strict odd rank-three determinant for the actual mixed source at every critical aperture. -/
theorem thetaCuspCenterMixed_oddHankelThree_pos :
    ∀ a : ℝ, 0 < a → a < 1/2 →
      0 < HilbertMetric.signedEvenHankelThreeDet
        (-iteratedDeriv 2 (thetaCuspCenterMixedDensity a) 0)
        (iteratedDeriv 4 (thetaCuspCenterMixedDensity a) 0)
        (-iteratedDeriv 6 (thetaCuspCenterMixedDensity a) 0)
        (iteratedDeriv 8 (thetaCuspCenterMixedDensity a) 0)
        (-iteratedDeriv 10 (thetaCuspCenterMixedDensity a) 0) := by
  intro a ha0 ha
  exact thetaCuspCenterMixed_oddHankelThree_pos_of_compensatedSource
    thetaCuspNativeOddCompensationCoefficient_pos.le
    (fun x hx => thetaCuspNativeOddCanonicalCompensatedDet_pos_global x hx.le) ha0 ha

end
end RHTower

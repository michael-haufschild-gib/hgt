import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactDeterminant
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddCompactCorrectionReserve

/-!
# Explicit compact positivity of the compensated odd determinant

The literal source has a positive correction reserve on [0, 137/2000].
Every coefficient at least one billion gives a positive corrected determinant
throughout that interval, including the canonical source-selected coefficient.
-/

open Set
namespace RHTower
noncomputable section
set_option maxHeartbeats 2000000

/-- The literal corrected determinant has a uniform arithmetic reserve on the full compact orbit. -/
theorem thetaCuspNativeOddCompensatedDet_compact_lower {C x : ℝ}
    (hC : 1000000000 ≤ C) (hx : x ∈ Icc (0 : ℝ) (137/2000)) :
    Bottcher.completedThetaProfile x^(6 : ℕ)*100000000000000 ≤
      thetaCuspNativeOddCompensatedDet C x := by
  obtain ⟨hS0, hS1, hA0, hA1, hW0, _⟩ := thetaCuspModularLyapunovState_compact_box hx
  have hu0 : 0 ≤ -(thetaCuspModularDrift x).re := by linarith
  have hu1 : -(thetaCuspModularDrift x).re ≤ 1 := by linarith
  have hp := HTGeometry.oddCompactDet_corrected_lower hu0 hu1 hA0 hA1 hW0
    (thetaCuspModularTransverseShear_le_one_on_compact hx)
  have hm := mul_le_mul_of_nonneg_left hp
    (pow_nonneg (thetaCuspCompletedThetaProfile_pos x).le 6)
  have hg := thetaCuspCenterCompensationSource_compact_lower hx
  have hdpos := thetaCuspNativeOddHeadDet_pos x
  have hcg := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ (1000000000 : ℝ)*thetaCuspNativeOddHeadDet x from by positivity)
  have hfixed : Bottcher.completedThetaProfile x^(6 : ℕ)*100000000000000 ≤
      thetaCuspNativeOddCompensatedDet 1000000000 x := by
    unfold thetaCuspNativeOddCompensatedDet
    rw [thetaCuspNativeOddHankelThreeDet_eq_compactPolynomial]
    rw [thetaCuspNativeOddHeadDet_eq_compactPolynomial] at hcg ⊢
    nlinarith only [hm, hcg]
  have hG : 0 ≤ thetaCuspCenterCompensationSource x :=
    (sq_nonneg (Bottcher.completedThetaProfile x)).trans
      (thetaCuspCenterCompensationSource_ge_mass_sq_on_compact hx)
  have hmono := mul_le_mul_of_nonneg_right hC (mul_nonneg hdpos.le hG)
  apply hfixed.trans
  unfold thetaCuspNativeOddCompensatedDet
  nlinarith only [hmono]

/-- Every coefficient at least one billion repairs every center in the explicit compact interval. -/
theorem thetaCuspNativeOddCompensatedDet_pos_on_compact {C x : ℝ}
    (hC : 1000000000 ≤ C) (hx : x ∈ Icc (0 : ℝ) (137/2000)) :
    0 < thetaCuspNativeOddCompensatedDet C x := by
  exact (mul_pos (pow_pos (thetaCuspCompletedThetaProfile_pos x) 6)
    (by norm_num : (0 : ℝ) < 100000000000000)).trans_le
      (thetaCuspNativeOddCompensatedDet_compact_lower hC hx)

/-- Unconditional explicit-interval positivity for the canonical source-selected coefficient. -/
theorem thetaCuspNativeOddCanonicalCompensatedDet_pos_on_compact :
    ∀ x : ℝ, x ∈ Icc (0 : ℝ) (137/2000) →
      0 < thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient x := by
  intro x hx
  exact thetaCuspNativeOddCompensatedDet_pos_on_compact
    thetaCuspNativeOddCompensationCoefficient_bounds.1.le hx

/-- The corrected weighted determinant is positive on the explicit center interval at every aperture. -/
theorem thetaCuspCenterCorrectedOddDet_pos_on_compact {a C r : ℝ}
    (ha : 0 < a) (hC : 1000000000 ≤ C) (hr : 0 < r) (hr1 : r ≤ 137/1000) :
    0 < thetaCuspCenterCorrectedOddDet a C r := by
  have hsource := thetaCuspNativeOddCompensatedDet_pos_on_compact hC
    (show r/2 ∈ Icc (0 : ℝ) (137/2000) from ⟨by linarith, by linarith⟩)
  have hw : 0 < r*Real.sinh (a*r) :=
    mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha hr))
  exact (mul_pos (pow_pos hw 3) hsource).trans_le
    (thetaCuspCenterCorrectedOddDet_lower ha.le (by linarith) hr.le)

end
end RHTower

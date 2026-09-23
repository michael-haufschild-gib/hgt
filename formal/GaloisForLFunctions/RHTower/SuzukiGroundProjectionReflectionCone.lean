import GaloisForLFunctions.RHTower.SuzukiGroundResiduePolarizationSelection
import GaloisForLFunctions.HTGeometry.PositiveOperatorInner

/-!
# Suzuki bottom-projection reflection cone

Let `vp` be the projection of Suzuki's positive deficiency source `exp(x)` onto a bottom
eigenspace and let `vm` be its reflected partner, the projection of `exp(-x)`.  Reflection
invariance gives equal norms.  The even and odd ground-pole residues are then the squared norms
of the even and odd parts of `(vp,vm)`.

This module identifies the exact source geometry behind the mixed-ground Xi-admission inequality.
For any equal-norm, nonzero pair, that inequality is equivalent to the sharp reflection-fidelity
cone

`kappaXi * ‖vp‖² < ⟪vm,vp⟫`.

Equivalently, the odd projected mass and the squared reflection distance obey exact bounds.
The unconditional prime--Gamma estimate `77/85 < kappaXi` then forces odd share `< 4/85` and
relative squared reflection distance `< 16/85`.  A reflection-fixed bottom source is admitted;
a reflection-antifixed bottom source is not.

The Hilbert-space identities are classical.  The content here is their exact calibration to the
Suzuki bottom-residue selector and the unconditional Xi first defect.  No Riemann-hypothesis
assumption or numerical computation occurs.
-/

namespace RHTower

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## Exact reflection-fidelity criterion -/

/-- For an equal-norm source pair, a target lies below its ground-residue angle exactly when the
reflected overlap lies in the corresponding open cone. -/
theorem target_lt_suzukiGroundProjectionAngle_iff_reflectionCone
    {target : ℝ} {vp vm : H}
    (hnorm : ‖vm‖ = ‖vp‖) (hvp : vp ≠ 0) :
    target <
        suzukiGroundResidueAngle
          (‖GaloisForLFunctions.HTGeometry.evenPart vp vm‖ ^ (2 : ℕ))
          (‖GaloisForLFunctions.HTGeometry.oddPart vp vm‖ ^ (2 : ℕ)) ↔
      target * ‖vp‖ ^ (2 : ℕ) < inner ℝ vm vp := by
  rw [suzukiGroundResidueAngle,
    GaloisForLFunctions.RHTower.suzukiDefectAngle,
    ← GaloisForLFunctions.HTGeometry.inner_div_norm_sq_eq_imbalance hnorm]
  exact lt_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hvp))

/-- Suzuki's prime--Gamma bottom-residue admission inequality is exactly the Xi-calibrated
reflection-fidelity cone. -/
theorem primeArchSuzukiGroundProjection_admitted_iff_reflectionCone
    {vp vm : H} (hnorm : ‖vm‖ = ‖vp‖) (hvp : vp ≠ 0) :
    (1 + primeArchSuzukiFirstDefectCalibration) *
          ‖GaloisForLFunctions.HTGeometry.oddPart vp vm‖ ^ (2 : ℕ) <
        (1 - primeArchSuzukiFirstDefectCalibration) *
          ‖GaloisForLFunctions.HTGeometry.evenPart vp vm‖ ^ (2 : ℕ) ↔
      primeArchSuzukiFirstDefectCalibration * ‖vp‖ ^ (2 : ℕ) <
        inner ℝ vm vp := by
  let evenMass :=
    ‖GaloisForLFunctions.HTGeometry.evenPart vp vm‖ ^ (2 : ℕ)
  let oddMass :=
    ‖GaloisForLFunctions.HTGeometry.oddPart vp vm‖ ^ (2 : ℕ)
  have hsum : 0 < evenMass + oddMass := by
    rw [← GaloisForLFunctions.HTGeometry.norm_sq_eq_evenPart_sq_add_oddPart_sq hnorm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hvp)
  rw [← target_lt_suzukiGroundResidueAngle_iff hsum]
  exact target_lt_suzukiGroundProjectionAngle_iff_reflectionCone hnorm hvp

/-! ## Exact odd-mass and metric forms -/

/-- The reflection cone is exactly the sharp odd projected-mass bound.  This version avoids
division and remains meaningful at the boundary. -/
theorem primeArchSuzukiGroundProjection_reflectionCone_iff_oddMass
    {vp vm : H} (hnorm : ‖vm‖ = ‖vp‖) :
    primeArchSuzukiFirstDefectCalibration * ‖vp‖ ^ (2 : ℕ) <
          inner ℝ vm vp ↔
      2 * ‖GaloisForLFunctions.HTGeometry.oddPart vp vm‖ ^ (2 : ℕ) <
        (1 - primeArchSuzukiFirstDefectCalibration) * ‖vp‖ ^ (2 : ℕ) := by
  rw [GaloisForLFunctions.HTGeometry.inner_eq_evenPart_sq_sub_oddPart_sq,
    GaloisForLFunctions.HTGeometry.norm_sq_eq_evenPart_sq_add_oddPart_sq hnorm]
  constructor <;> intro h
  · calc
      2 * ‖GaloisForLFunctions.HTGeometry.oddPart vp vm‖ ^ (2 : ℕ)
          < (1 - primeArchSuzukiFirstDefectCalibration) *
              ‖GaloisForLFunctions.HTGeometry.evenPart vp vm‖ ^ (2 : ℕ)
            + (1 - primeArchSuzukiFirstDefectCalibration) *
              ‖GaloisForLFunctions.HTGeometry.oddPart vp vm‖ ^ (2 : ℕ) := by
              nlinarith
      _ = (1 - primeArchSuzukiFirstDefectCalibration) *
            (‖GaloisForLFunctions.HTGeometry.evenPart vp vm‖ ^ (2 : ℕ) +
              ‖GaloisForLFunctions.HTGeometry.oddPart vp vm‖ ^ (2 : ℕ)) := by ring
  · calc
      primeArchSuzukiFirstDefectCalibration *
            (‖GaloisForLFunctions.HTGeometry.evenPart vp vm‖ ^ (2 : ℕ) +
              ‖GaloisForLFunctions.HTGeometry.oddPart vp vm‖ ^ (2 : ℕ))
          < ‖GaloisForLFunctions.HTGeometry.evenPart vp vm‖ ^ (2 : ℕ) -
              ‖GaloisForLFunctions.HTGeometry.oddPart vp vm‖ ^ (2 : ℕ) := by
              nlinarith

/-- The same cone is exactly a relative-distance ball around the reflection-fixed ray. -/
theorem primeArchSuzukiGroundProjection_reflectionCone_iff_distance
    {vp vm : H} (hnorm : ‖vm‖ = ‖vp‖) :
    primeArchSuzukiFirstDefectCalibration * ‖vp‖ ^ (2 : ℕ) <
          inner ℝ vm vp ↔
      ‖vp - vm‖ ^ (2 : ℕ) <
        2 * (1 - primeArchSuzukiFirstDefectCalibration) * ‖vp‖ ^ (2 : ℕ) := by
  rw [primeArchSuzukiGroundProjection_reflectionCone_iff_oddMass hnorm,
    GaloisForLFunctions.HTGeometry.oddPart, norm_smul]
  norm_num
  constructor <;> intro h <;> nlinarith

/-! ## Unconditional Xi aperture -/

/-- Every admitted Suzuki bottom projection has reflection correlation strictly larger than
`77/85` of its energy. -/
theorem
    primeArchSuzukiGroundProjection_reflectionCorrelation_gt_seventySeven_div_eightyFive
    {vp vm : H} (hvp : vp ≠ 0)
    (hcone :
      primeArchSuzukiFirstDefectCalibration * ‖vp‖ ^ (2 : ℕ) <
        inner ℝ vm vp) :
    ((77 : ℝ) / 85) * ‖vp‖ ^ (2 : ℕ) < inner ℝ vm vp := by
  have hk := primeArchSuzukiFirstDefectCalibration_mem_Ioo.1
  have hnormSq : 0 < ‖vp‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hvp)
  nlinarith

/-- Every admitted Suzuki bottom projection has odd source share strictly below `4/85`. -/
theorem primeArchSuzukiGroundProjection_oddShare_lt_four_div_eightyFive
    {vp vm : H} (hnorm : ‖vm‖ = ‖vp‖) (hvp : vp ≠ 0)
    (hcone :
      primeArchSuzukiFirstDefectCalibration * ‖vp‖ ^ (2 : ℕ) <
        inner ℝ vm vp) :
    ‖GaloisForLFunctions.HTGeometry.oddPart vp vm‖ ^ (2 : ℕ) / ‖vp‖ ^ (2 : ℕ) <
      (4 : ℝ) / 85 := by
  have hnormSq : 0 < ‖vp‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hvp)
  have hcorr :=
    primeArchSuzukiGroundProjection_reflectionCorrelation_gt_seventySeven_div_eightyFive
      hvp hcone
  have hdiff :=
    GaloisForLFunctions.HTGeometry.inner_eq_evenPart_sq_sub_oddPart_sq vp vm
  have hsum :=
    GaloisForLFunctions.HTGeometry.norm_sq_eq_evenPart_sq_add_oddPart_sq hnorm
  rw [div_lt_iff₀ hnormSq]
  nlinarith

/-- Every admitted Suzuki bottom projection lies in a relative squared reflection-distance ball
of radius `16/85`. -/
theorem primeArchSuzukiGroundProjection_reflectionDistance_sq_lt
    {vp vm : H} (hnorm : ‖vm‖ = ‖vp‖) (hvp : vp ≠ 0)
    (hcone :
      primeArchSuzukiFirstDefectCalibration * ‖vp‖ ^ (2 : ℕ) <
        inner ℝ vm vp) :
    ‖vp - vm‖ ^ (2 : ℕ) < ((16 : ℝ) / 85) * ‖vp‖ ^ (2 : ℕ) := by
  have hodd :=
    primeArchSuzukiGroundProjection_oddShare_lt_four_div_eightyFive
      hnorm hvp hcone
  have hnormSq : 0 < ‖vp‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hvp)
  rw [div_lt_iff₀ hnormSq] at hodd
  rw [GaloisForLFunctions.HTGeometry.oddPart, norm_smul] at hodd
  norm_num at hodd ⊢
  nlinarith

/-- Xi admission forces the projected even source mass to exceed `81/4` times the projected odd
source mass.  This is the quantitative parity amplification demanded of the restricted-Weil
bottom eigenspace. -/
theorem primeArchSuzukiGroundProjection_evenMass_gt_eightyOne_div_four_mul_oddMass
    {vp vm : H}
    (hadmitted :
      (1 + primeArchSuzukiFirstDefectCalibration) *
            ‖GaloisForLFunctions.HTGeometry.oddPart vp vm‖ ^ (2 : ℕ) <
          (1 - primeArchSuzukiFirstDefectCalibration) *
            ‖GaloisForLFunctions.HTGeometry.evenPart vp vm‖ ^ (2 : ℕ)) :
    ((81 : ℝ) / 4) *
          ‖GaloisForLFunctions.HTGeometry.oddPart vp vm‖ ^ (2 : ℕ) <
        ‖GaloisForLFunctions.HTGeometry.evenPart vp vm‖ ^ (2 : ℕ) := by
  have hk := primeArchSuzukiFirstDefectCalibration_mem_Ioo.1
  have heven :
      0 ≤ ‖GaloisForLFunctions.HTGeometry.evenPart vp vm‖ ^ (2 : ℕ) := sq_nonneg _
  have hodd :
      0 ≤ ‖GaloisForLFunctions.HTGeometry.oddPart vp vm‖ ^ (2 : ℕ) := sq_nonneg _
  nlinarith

/-! ## Pure-parity boundary classification -/

/-- A nonzero reflection-fixed bottom source, hence a pure-even bottom source, is admitted. -/
theorem primeArchSuzukiGroundProjection_admitted_of_reflection_fixed
    {vp vm : H} (hvp : vp ≠ 0) (hfixed : vm = vp) :
    (1 + primeArchSuzukiFirstDefectCalibration) *
          ‖GaloisForLFunctions.HTGeometry.oddPart vp vm‖ ^ (2 : ℕ) <
        (1 - primeArchSuzukiFirstDefectCalibration) *
          ‖GaloisForLFunctions.HTGeometry.evenPart vp vm‖ ^ (2 : ℕ) := by
  have hnorm : ‖vm‖ = ‖vp‖ := by rw [hfixed]
  rw [primeArchSuzukiGroundProjection_admitted_iff_reflectionCone hnorm hvp,
    hfixed, real_inner_self_eq_norm_sq]
  have hk := primeArchSuzukiFirstDefectCalibration_mem_Ioo.2
  have hnormSq : 0 < ‖vp‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hvp)
  nlinarith

/-- A nonzero reflection-antifixed bottom source, hence a pure-odd bottom source, is never
admitted. -/
theorem primeArchSuzukiGroundProjection_not_admitted_of_reflection_antifixed
    {vp vm : H} (hvp : vp ≠ 0) (hfixed : vm = -vp) :
    ¬ (1 + primeArchSuzukiFirstDefectCalibration) *
          ‖GaloisForLFunctions.HTGeometry.oddPart vp vm‖ ^ (2 : ℕ) <
        (1 - primeArchSuzukiFirstDefectCalibration) *
          ‖GaloisForLFunctions.HTGeometry.evenPart vp vm‖ ^ (2 : ℕ) := by
  have hnorm : ‖vm‖ = ‖vp‖ := by rw [hfixed, norm_neg]
  rw [primeArchSuzukiGroundProjection_admitted_iff_reflectionCone hnorm hvp,
    hfixed, inner_neg_left, real_inner_self_eq_norm_sq]
  have hk := primeArchSuzukiFirstDefectCalibration_mem_Ioo.1
  have hnormSq : 0 < ‖vp‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hvp)
  nlinarith

end

end RHTower

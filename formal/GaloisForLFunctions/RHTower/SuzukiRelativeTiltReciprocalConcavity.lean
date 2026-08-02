import GaloisForLFunctions.RHTower.SuzukiTwoJetShiftedHankelGate
import GaloisForLFunctions.RHTower.SquaredXiRadialJetXiSpecialization

/-!
# Suzuki relative tilt and reciprocal-Xi concavity

The source coordinate missed by the position torque is the dimensionless relative tilt gap

`g = beta / O - alpha / E`.

For positive parity energies, the complete Suzuki two-jet Schur law is exactly `g ≤ 1`, while
negative Xi curvature is exactly `g > 0`.  Thus an Xi-identifying finite-aperture source must enter
the sharp transition window `0 < g ≤ 1`.

At the prime--Gamma target this same scalar is

`(A B + B² - 2 A C) / (B (A-B))`,

where `A = Re M₀(1)`, `B = Re M₁(1)`, and `C = Re M₂(1)`.  Its upper endpoint is equivalent to
`A C - B² ≥ 0`.

The latter determinant also has an exact differential meaning.  If

`G(y) = Re M₀(y) / 2`

is the squared-Xi radial logarithmic-derivative field, then

`(G⁻¹)''(1) = 4 (B² - A C) / A³`.

Consequently Suzuki's first nonlinear admission gate is precisely local concavity, at the safe
shift, of the reciprocal radial response.  No Riemann-hypothesis assumption or numerical
computation occurs.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-! ## The source-normalized relative tilt -/

/-- Dimensionless odd-versus-even relative exponential-tilt gap. -/
def suzukiRelativeTiltGap
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ) : ℝ :=
  oddTilt / oddEnergy - evenTilt / evenEnergy

/-- The Schur numerator factors into positive parity mass times distance from the sharp relative
tilt wall `g = 1`. -/
theorem suzukiParity_twoJetSlackNumerator_eq_relativeTiltGap
    {evenEnergy oddEnergy evenTilt oddTilt : ℝ}
    (heven : evenEnergy ≠ 0) (hodd : oddEnergy ≠ 0) :
    oddEnergy * (evenEnergy + evenTilt) - evenEnergy * oddTilt =
      evenEnergy * oddEnergy *
        (1 - suzukiRelativeTiltGap
          evenEnergy oddEnergy evenTilt oddTilt) := by
  rw [suzukiRelativeTiltGap]
  field_simp [heven, hodd]
  ring

/-- The complete parity curvature is the Schwarz boundary width times the relative tilt gap. -/
theorem suzukiSecondDefectParityCurvature_eq_relativeTiltGap
    {evenEnergy oddEnergy evenTilt oddTilt : ℝ}
    (heven : evenEnergy ≠ 0) (hodd : oddEnergy ≠ 0)
    (hsum : evenEnergy + oddEnergy ≠ 0) :
    suzukiSecondDefectParityCurvature
        evenEnergy oddEnergy evenTilt oddTilt =
      -2 *
        (1 - GaloisForLFunctions.RHTower.suzukiDefectAngle
          evenEnergy oddEnergy ^ 2) *
        suzukiRelativeTiltGap
          evenEnergy oddEnergy evenTilt oddTilt := by
  rw [suzukiSecondDefectParityCurvature,
    GaloisForLFunctions.RHTower.suzukiDefectAngle,
    suzukiRelativeTiltGap]
  field_simp [heven, hodd, hsum]
  ring

/-- For positive energies, nonnegativity of Suzuki's source Schur numerator is exactly the
dimensionless bound `g ≤ 1`. -/
theorem suzukiParity_twoJetSlack_nonneg_iff_relativeTiltGap_le_one
    {evenEnergy oddEnergy evenTilt oddTilt : ℝ}
    (heven : 0 < evenEnergy) (hodd : 0 < oddEnergy) :
    0 ≤ oddEnergy * (evenEnergy + evenTilt) - evenEnergy * oddTilt ↔
      suzukiRelativeTiltGap
        evenEnergy oddEnergy evenTilt oddTilt ≤ 1 := by
  rw [suzukiParity_twoJetSlackNumerator_eq_relativeTiltGap
    heven.ne' hodd.ne']
  have hprod : 0 < evenEnergy * oddEnergy := mul_pos heven hodd
  rw [mul_nonneg_iff_of_pos_left hprod]
  constructor <;> intro h <;> linarith

/-- Strictly negative curvature is the lower endpoint `0 < g` of the transition window. -/
theorem suzukiRelativeTiltGap_pos_iff_secondDefectParityCurvature_neg
    {evenEnergy oddEnergy evenTilt oddTilt : ℝ}
    (heven : 0 < evenEnergy) (hodd : 0 < oddEnergy) :
    0 < suzukiRelativeTiltGap
        evenEnergy oddEnergy evenTilt oddTilt ↔
      suzukiSecondDefectParityCurvature
        evenEnergy oddEnergy evenTilt oddTilt < 0 := by
  rw [suzukiSecondDefectParityCurvature_neg_iff heven hodd,
    suzukiRelativeTiltGap]
  constructor <;> intro h <;> linarith

/-- **Sharp literal Suzuki transition window, upper endpoint.**  The actual all-angle
Hermite--Biehler carrier forces `g ≤ 1`; no abstract disk-map hypothesis remains. -/
theorem suzukiAllAngleCarrier_forces_relativeTiltGap_le_one
    {A E : ℂ → ℂ} {evenEnergy oddEnergy evenTilt oddTilt : ℝ}
    (hA : Differentiable ℂ A) (hE : Differentiable ℂ E)
    (hAi : A I = 0)
    (hreal : GaloisForLFunctions.RHTower.SuzukiAllAngleRealZeros A E)
    (heven : 0 < evenEnergy) (hodd : 0 < oddEnergy)
    (hfirst : deriv (fun w =>
      GaloisForLFunctions.RHTower.suzukiLivsicQuotient A E
        (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w)) 0 =
      (GaloisForLFunctions.RHTower.suzukiDefectAngle
        evenEnergy oddEnergy : ℂ))
    (hsecond : iteratedDeriv 2 (fun w =>
      GaloisForLFunctions.RHTower.suzukiLivsicQuotient A E
        (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w)) 0 =
      (suzukiSecondDefectParityCurvature
        evenEnergy oddEnergy evenTilt oddTilt : ℂ)) :
    suzukiRelativeTiltGap
        evenEnergy oddEnergy evenTilt oddTilt ≤ 1 := by
  exact
    (suzukiParity_twoJetSlack_nonneg_iff_relativeTiltGap_le_one
      heven hodd).mp
      (suzukiAllAngleCarrier_forces_parity_twoJetSlack
        hA hE hAi hreal heven hodd hfirst hsecond)

/-! ## Prime--Gamma target calibration -/

/-- Exact prime--Gamma value of Suzuki's dimensionless relative tilt gap. -/
def primeArchSuzukiRelativeTiltGapCalibration : ℝ :=
  -primeArchSuzukiSecondDefectCalibration /
    (2 * (1 - primeArchSuzukiFirstDefectCalibration ^ 2))

private theorem primeArchSuzuki_schurBoundary_pos :
    0 < 2 * (1 - primeArchSuzukiFirstDefectCalibration ^ 2) := by
  rcases primeArchSuzukiFirstDefectCalibration_mem_Ioo with ⟨hlower, hupper⟩
  have hpos : 0 < primeArchSuzukiFirstDefectCalibration := by
    linarith
  nlinarith

/-- Xi's target relative tilt lies strictly above the flat-curvature boundary. -/
theorem primeArchSuzukiRelativeTiltGapCalibration_pos :
    0 < primeArchSuzukiRelativeTiltGapCalibration := by
  rw [primeArchSuzukiRelativeTiltGapCalibration]
  exact div_pos (neg_pos.mpr primeArchSuzukiSecondDefectCalibration_neg)
    primeArchSuzuki_schurBoundary_pos

/-- Exact safe-shift moment formula for Xi's relative tilt target. -/
theorem primeArchSuzukiRelativeTiltGapCalibration_eq_moments :
    primeArchSuzukiRelativeTiltGapCalibration =
      ((primeArchShiftedReciprocalMoment 1 0).re *
            (primeArchShiftedReciprocalMoment 1 1).re +
          (primeArchShiftedReciprocalMoment 1 1).re ^ 2 -
          2 * (primeArchShiftedReciprocalMoment 1 0).re *
            (primeArchShiftedReciprocalMoment 1 2).re) /
        ((primeArchShiftedReciprocalMoment 1 1).re *
          ((primeArchShiftedReciprocalMoment 1 0).re -
            (primeArchShiftedReciprocalMoment 1 1).re)) := by
  let A := (primeArchShiftedReciprocalMoment 1 0).re
  let B := (primeArchShiftedReciprocalMoment 1 1).re
  let C := (primeArchShiftedReciprocalMoment 1 2).re
  have hA : 0 < A := re_primeArchShiftedReciprocalMoment_one_zero_pos
  have hB : 0 < B := re_primeArchShiftedReciprocalMoment_one_one_pos
  have h85 : 85 * B < 4 * A :=
    eightyFive_mul_re_primeArchShiftedReciprocalMoment_one_lt_four_mul_zero
  have hAB : 0 < A - B := by linarith
  have hidentity :
      2 * (1 - ((A - 2 * B) / A) ^ 2) =
        8 * B * (A - B) / A ^ 2 := by
    field_simp [hA.ne']
    ring
  have hboundary :
      2 * (1 - ((A - 2 * B) / A) ^ 2) ≠ 0 := by
    rw [hidentity]
    positivity
  rw [primeArchSuzukiRelativeTiltGapCalibration,
    primeArchSuzukiSecondDefectCalibration,
    primeArchSuzukiFirstDefectCalibration]
  change
    -(8 * (2 * C / A - B / A - (B / A) ^ 2)) /
        (2 * (1 - ((A - 2 * B) / A) ^ 2)) =
      (A * B + B ^ 2 - 2 * A * C) / (B * (A - B))
  rw [hidentity]
  field_simp [hA.ne', hB.ne', hAB.ne', hboundary]
  ring

/-- The target upper wall `g_Xi ≤ 1` is exactly the safe-shift first Hankel inequality. -/
theorem primeArchSuzukiRelativeTiltGapCalibration_le_one_iff_shiftedHankelMinor_nonneg :
    primeArchSuzukiRelativeTiltGapCalibration ≤ 1 ↔
      0 ≤
        (primeArchShiftedReciprocalMoment 1 0).re *
            (primeArchShiftedReciprocalMoment 1 2).re -
          (primeArchShiftedReciprocalMoment 1 1).re ^ 2 := by
  have hden := primeArchSuzuki_schurBoundary_pos
  calc
    primeArchSuzukiRelativeTiltGapCalibration ≤ 1 ↔
        0 ≤ primeArchSuzukiSecondDefectCalibration +
          2 * (1 - primeArchSuzukiFirstDefectCalibration ^ 2) := by
      rw [primeArchSuzukiRelativeTiltGapCalibration, div_le_one hden]
      constructor <;> intro h <;> linarith
    _ ↔ _ :=
      primeArchSuzuki_twoJetSlack_nonneg_iff_shiftedHankelMinor_nonneg

/-! ## Reciprocal radial-response concavity -/

/-- Reciprocal of the squared-Xi radial logarithmic-derivative field. -/
def squaredXiReciprocalRadialField (y : ℝ) : ℝ :=
  (squaredXiRadialField y)⁻¹

theorem squaredXiRadialField_pos {y : ℝ} (hy : 0 < y) :
    0 < squaredXiRadialField y := by
  simpa using
    (alternating_iteratedDeriv_squaredXiRadialField_pos
      hy (n := 0) (by norm_num))

theorem deriv_squaredXiReciprocalRadialField
    {y : ℝ} (hy : 0 < y) :
    deriv squaredXiReciprocalRadialField y =
      -iteratedDeriv 1 squaredXiRadialField y /
        squaredXiRadialField y ^ 2 := by
  have hfield :=
    hasDerivAt_iteratedDeriv_squaredXiRadialField 0 hy
  have hne : squaredXiRadialField y ≠ 0 :=
    ne_of_gt (squaredXiRadialField_pos hy)
  have hderiv :
      deriv squaredXiRadialField y =
        iteratedDeriv 1 squaredXiRadialField y := by
    simpa only [iteratedDeriv_zero, zero_add] using hfield.deriv
  change deriv (fun v : ℝ => (squaredXiRadialField v)⁻¹) y = _
  rw [show (fun v : ℝ => (squaredXiRadialField v)⁻¹) =
      (fun t : ℝ => t⁻¹) ∘ squaredXiRadialField by rfl,
    deriv_comp y (hasDerivAt_inv hne).differentiableAt hfield.differentiableAt,
    deriv_inv, hderiv]
  field_simp [hne]

/-- Exact second derivative of the reciprocal radial response at every positive shift. -/
theorem iteratedDeriv_two_squaredXiReciprocalRadialField
    {y : ℝ} (hy : 0 < y) :
    iteratedDeriv 2 squaredXiReciprocalRadialField y =
      4 *
        ((xiShiftedReciprocalMoment y 1).re ^ 2 -
          (xiShiftedReciprocalMoment y 0).re *
            (xiShiftedReciprocalMoment y 2).re) /
        (xiShiftedReciprocalMoment y 0).re ^ 3 := by
  let F := squaredXiRadialField
  have hF0 : F y ≠ 0 := ne_of_gt (squaredXiRadialField_pos hy)
  have hF :
      HasDerivAt F (iteratedDeriv 1 F y) y := by
    simpa only [F, iteratedDeriv_zero, zero_add] using
      hasDerivAt_iteratedDeriv_squaredXiRadialField 0 hy
  have hF1 :
      HasDerivAt (iteratedDeriv 1 F) (iteratedDeriv 2 F y) y := by
    simpa only [F, one_add_one_eq_two] using
      hasDerivAt_iteratedDeriv_squaredXiRadialField 1 hy
  have hEq :
      deriv squaredXiReciprocalRadialField =ᶠ[nhds y]
        fun v => -iteratedDeriv 1 F v / F v ^ 2 := by
    filter_upwards [Ioi_mem_nhds hy] with v hv
    simpa only [F] using deriv_squaredXiReciprocalRadialField hv
  have hquotRaw :=
    hF1.neg.div (hF.pow 2) (pow_ne_zero 2 hF0)
  have hquot :
      deriv (fun v => -iteratedDeriv 1 F v / F v ^ 2) y =
        ((-iteratedDeriv 2 F y) * F y ^ 2 -
            (-iteratedDeriv 1 F y) *
              (2 * F y * iteratedDeriv 1 F y)) /
          (F y ^ 2) ^ 2 := by
    rw [show (fun v => -iteratedDeriv 1 F v / F v ^ 2) =
      -iteratedDeriv 1 F / F ^ 2 by rfl]
    simpa only [Pi.neg_apply, Pi.pow_apply, Nat.cast_ofNat,
      Nat.reduceSub, pow_one] using hquotRaw.deriv
  have habstract :
      iteratedDeriv 2 squaredXiReciprocalRadialField y =
        (2 * (iteratedDeriv 1 F y) ^ 2 -
          F y * iteratedDeriv 2 F y) / F y ^ 3 := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one, hEq.deriv_eq, hquot]
    field_simp [hF0]
    ring
  rw [habstract]
  have hzero :=
    iteratedDeriv_squaredXiRadialField 0 hy
  have hone :=
    iteratedDeriv_squaredXiRadialField 1 hy
  have htwo :=
    iteratedDeriv_squaredXiRadialField 2 hy
  simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, one_mul] at hzero
  norm_num at hzero hone htwo
  dsimp only [F]
  rw [iteratedDeriv_one, hzero, hone, htwo]
  have hm0 : (xiShiftedReciprocalMoment y 0).re ≠ 0 :=
    ne_of_gt (re_xiShiftedReciprocalMoment_pos hy (n := 0) (by norm_num))
  field_simp [hm0]
  ring

/-- At the safe shift, reciprocal radial curvature is the negative normalized Hankel minor in
prime--Gamma coordinates. -/
theorem iteratedDeriv_two_squaredXiReciprocalRadialField_one_eq_primeArch :
    iteratedDeriv 2 squaredXiReciprocalRadialField 1 =
      4 *
        ((primeArchShiftedReciprocalMoment 1 1).re ^ 2 -
          (primeArchShiftedReciprocalMoment 1 0).re *
            (primeArchShiftedReciprocalMoment 1 2).re) /
        (primeArchShiftedReciprocalMoment 1 0).re ^ 3 := by
  rw [iteratedDeriv_two_squaredXiReciprocalRadialField (by norm_num)]
  rw [xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 0,
    xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 1,
    xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 2]

/-- **Reciprocal-concavity form of Suzuki's exact two-jet gate.** -/
theorem squaredXiReciprocalRadialField_concaveAt_one_iff_shiftedHankelMinor_nonneg :
    iteratedDeriv 2 squaredXiReciprocalRadialField 1 ≤ 0 ↔
      0 ≤
        (primeArchShiftedReciprocalMoment 1 0).re *
            (primeArchShiftedReciprocalMoment 1 2).re -
          (primeArchShiftedReciprocalMoment 1 1).re ^ 2 := by
  rw [iteratedDeriv_two_squaredXiReciprocalRadialField_one_eq_primeArch]
  have hA : 0 < (primeArchShiftedReciprocalMoment 1 0).re :=
    re_primeArchShiftedReciprocalMoment_one_zero_pos
  have hA3 : 0 < (primeArchShiftedReciprocalMoment 1 0).re ^ 3 := by
    positivity
  rw [div_le_iff₀ hA3]
  constructor <;> intro h <;> nlinarith

/-- The source transition upper wall, the Xi target wall, the safe-shift Hankel gate, and local
reciprocal-radial concavity are one exact condition. -/
theorem primeArchSuzuki_relativeTiltGap_le_one_iff_reciprocalRadial_concaveAt_one :
    primeArchSuzukiRelativeTiltGapCalibration ≤ 1 ↔
      iteratedDeriv 2 squaredXiReciprocalRadialField 1 ≤ 0 := by
  rw [primeArchSuzukiRelativeTiltGapCalibration_le_one_iff_shiftedHankelMinor_nonneg,
    squaredXiReciprocalRadialField_concaveAt_one_iff_shiftedHankelMinor_nonneg]

end

end RHTower

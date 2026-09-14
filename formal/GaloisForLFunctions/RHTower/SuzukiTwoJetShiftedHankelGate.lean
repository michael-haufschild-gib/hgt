import GaloisForLFunctions.RHTower.SuzukiSecondDefectCompactParitySource
import GaloisForLFunctions.RHTower.SuzukiAllAngleCarrierSchurSecondJet

/-!
# Suzuki's two-jet shifted-Hankel gate

An anchored holomorphic self-map of the disk has a nonlinear second-jet constraint

`‖f''(0)‖ ≤ 2 * (1 - ‖f'(0)‖²)`.

For Suzuki's parity coordinates this is exactly

`0 ≤ O * (E + alpha) - E * beta`.

For the normalized Xi target the same slack is exactly sixteen times the first `2 × 2`
Hankel determinant of the safe-shift reciprocal moments, divided by the square of the zeroth
moment.  Thus the finite-aperture Schur problem and the shifted Hankel problem are the same
two-jet gate, not merely analogous positivity questions.

The final decomposition records a sharp limitation of the position-torque invariant:
`alpha - beta` controls only one summand of the Schur slack.  The local tilt-asymmetry term
`alpha * (O - E)` remains independent.

No RH assumption or numerical computation occurs.
-/

open Complex Metric Set

namespace RHTower

noncomputable section

/-- Real form of the anchored Schur lower-curvature boundary. -/
theorem real_secondJet_add_schurBoundary_nonneg
    {f : ℂ → ℂ} {firstJet secondJet : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf0 : f 0 = 0)
    (hmap : MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 1))
    (hfirst : deriv f 0 = (firstJet : ℂ))
    (hsecond : iteratedDeriv 2 f 0 = (secondJet : ℂ)) :
    0 ≤ secondJet + 2 * (1 - firstJet ^ 2) := by
  have hbound := norm_iteratedDeriv_two_le_schurSlack_closed hf hf0 hmap
  rw [hfirst, hsecond] at hbound
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hbound
  have hlower := neg_le_of_abs_le hbound
  linarith

/-- The abstract disk hypotheses above are automatic for Suzuki's actual all-angle
Hermite--Biehler carrier after disk conjugation. -/
theorem suzukiAllAngleCarrier_forces_real_twoJetSlack
    {A E : ℂ → ℂ} {firstJet secondJet : ℝ}
    (hA : Differentiable ℂ A) (hE : Differentiable ℂ E)
    (hAi : A I = 0)
    (hreal : GaloisForLFunctions.RHTower.SuzukiAllAngleRealZeros A E)
    (hfirst : deriv (fun w =>
      GaloisForLFunctions.RHTower.suzukiLivsicQuotient A E
        (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w)) 0 =
      (firstJet : ℂ))
    (hsecond : iteratedDeriv 2 (fun w =>
      GaloisForLFunctions.RHTower.suzukiLivsicQuotient A E
        (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w)) 0 =
      (secondJet : ℂ)) :
    0 ≤ secondJet + 2 * (1 - firstJet ^ 2) := by
  have hbound := norm_suzukiAllAngleCarrier_secondJet_le_schurSlack
    hA hE hAi hreal
  dsimp only at hbound
  rw [hfirst, hsecond] at hbound
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hbound
  have hlower := neg_le_of_abs_le hbound
  linarith

/-- Exact parity-coordinate form of the Schur two-jet slack. -/
theorem suzukiParity_twoJetSlack_eq
    {evenEnergy oddEnergy evenTilt oddTilt : ℝ}
    (hsum : evenEnergy + oddEnergy ≠ 0) :
    suzukiSecondDefectParityCurvature
          evenEnergy oddEnergy evenTilt oddTilt +
        2 * (1 - GaloisForLFunctions.RHTower.suzukiDefectAngle
          evenEnergy oddEnergy ^ 2) =
      8 * (oddEnergy * (evenEnergy + evenTilt) -
          evenEnergy * oddTilt) /
        (evenEnergy + oddEnergy) ^ 2 := by
  rw [suzukiSecondDefectParityCurvature,
    GaloisForLFunctions.RHTower.suzukiDefectAngle]
  field_simp [hsum]
  ring

/-- **Suzuki source Schur law.**  Any finite-aperture carrier satisfying the anchored disk
self-map property forces this nonlinear inequality between parity energies and their exponential
tilts.  It is a source law, not a target-selected calibration. -/
theorem suzukiSchurCarrier_forces_parity_twoJetSlack
    {f : ℂ → ℂ} {evenEnergy oddEnergy evenTilt oddTilt : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf0 : f 0 = 0)
    (hmap : MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 1))
    (heven : 0 < evenEnergy) (hodd : 0 < oddEnergy)
    (hfirst : deriv f 0 =
      (GaloisForLFunctions.RHTower.suzukiDefectAngle
        evenEnergy oddEnergy : ℂ))
    (hsecond : iteratedDeriv 2 f 0 =
      (suzukiSecondDefectParityCurvature
        evenEnergy oddEnergy evenTilt oddTilt : ℂ)) :
    0 ≤ oddEnergy * (evenEnergy + evenTilt) -
      evenEnergy * oddTilt := by
  have hsum : 0 < evenEnergy + oddEnergy := add_pos heven hodd
  have hslack := real_secondJet_add_schurBoundary_nonneg
    hf hf0 hmap hfirst hsecond
  rw [suzukiParity_twoJetSlack_eq hsum.ne'] at hslack
  have hden : 0 < (evenEnergy + oddEnergy) ^ 2 :=
    sq_pos_of_pos hsum
  have hnum := (le_div_iff₀ hden).mp hslack
  nlinarith

/-- **Literal all-angle Suzuki source law.**  The abstract disk-map hypothesis has been eliminated:
Suzuki's all-angle real-zero theorem supplies it through finite-aperture Hermite--Biehler
separation. -/
theorem suzukiAllAngleCarrier_forces_parity_twoJetSlack
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
    0 ≤ oddEnergy * (evenEnergy + evenTilt) -
      evenEnergy * oddTilt := by
  have hsum : 0 < evenEnergy + oddEnergy := add_pos heven hodd
  have hslack := suzukiAllAngleCarrier_forces_real_twoJetSlack
    hA hE hAi hreal hfirst hsecond
  rw [suzukiParity_twoJetSlack_eq hsum.ne'] at hslack
  have hden : 0 < (evenEnergy + oddEnergy) ^ 2 :=
    sq_pos_of_pos hsum
  have hnum := (le_div_iff₀ hden).mp hslack
  nlinarith

/-- The source Schur numerator decomposes into energy, position torque, and a residual local
tilt-asymmetry term.  Therefore the commutator torque alone cannot determine its sign. -/
theorem suzukiParity_twoJetSlack_torque_decomposition
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ) :
    oddEnergy * (evenEnergy + evenTilt) - evenEnergy * oddTilt =
      evenEnergy * oddEnergy +
        evenEnergy * (evenTilt - oddTilt) +
        evenTilt * (oddEnergy - evenEnergy) := by
  ring

/-- **Torque-only fiber classification.**  Away from exact parity-energy balance, fixing the
commutator torque `evenTilt - oddTilt` leaves the Schur numerator completely unconstrained: every
real value occurs.  This is a class-complete obstruction to closing Suzuki's two-jet gate from
position torque alone. -/
theorem suzukiParity_twoJetSlack_surjective_at_fixed_torque
    {evenEnergy oddEnergy torque target : ℝ}
    (hbalance : oddEnergy ≠ evenEnergy) :
    ∃ evenTilt oddTilt : ℝ,
      evenTilt - oddTilt = torque ∧
      oddEnergy * (evenEnergy + evenTilt) -
          evenEnergy * oddTilt = target := by
  let evenTilt :=
    (target - evenEnergy * oddEnergy - evenEnergy * torque) /
      (oddEnergy - evenEnergy)
  let oddTilt := evenTilt - torque
  refine ⟨evenTilt, oddTilt, by simp only [oddTilt]; ring, ?_⟩
  dsimp only [evenTilt, oddTilt]
  field_simp [sub_ne_zero.mpr hbalance]
  ring

/-- At exact parity-energy balance the missing local tilt term vanishes, so torque becomes a
complete sign coordinate for the two-jet Schur numerator. -/
theorem suzukiParity_twoJetSlack_of_balanced_energy
    (energy evenTilt oddTilt : ℝ) :
    energy * (energy + evenTilt) - energy * oddTilt =
      energy * (energy + (evenTilt - oddTilt)) := by
  ring

/-- Sharp balanced-energy torque threshold. -/
theorem suzukiParity_twoJetSlack_balanced_nonneg_iff
    {energy torque : ℝ} (henergy : 0 < energy) :
    0 ≤ energy * (energy + torque) ↔ -energy ≤ torque := by
  constructor
  · intro h
    nlinarith
  · intro h
    exact mul_nonneg henergy.le (by linarith)

/-- Generic moment algebra behind the shifted-Hankel identification. -/
theorem moment_twoJetSlack_eq_hankelMinor
    {A B C : ℝ} (hA : A ≠ 0) :
    8 * (2 * C / A - B / A - (B / A) ^ 2) +
        2 * (1 - ((A - 2 * B) / A) ^ 2) =
      16 * (A * C - B ^ 2) / A ^ 2 := by
  field_simp [hA]
  ring

/-- **Exact safe-shift Hankel gate.**  Xi's first and second Suzuki calibrations have Schur slack
equal to the normalized first `2 × 2` Hankel minor of the safe-shift reciprocal moments. -/
theorem primeArchSuzuki_twoJetSlack_eq_shiftedHankelMinor :
    primeArchSuzukiSecondDefectCalibration +
        2 * (1 - primeArchSuzukiFirstDefectCalibration ^ 2) =
      16 *
          ((primeArchShiftedReciprocalMoment 1 0).re *
              (primeArchShiftedReciprocalMoment 1 2).re -
            (primeArchShiftedReciprocalMoment 1 1).re ^ 2) /
        (primeArchShiftedReciprocalMoment 1 0).re ^ 2 := by
  have hA : (primeArchShiftedReciprocalMoment 1 0).re ≠ 0 :=
    ne_of_gt re_primeArchShiftedReciprocalMoment_one_zero_pos
  rw [primeArchSuzukiFirstDefectCalibration,
    primeArchSuzukiSecondDefectCalibration]
  exact moment_twoJetSlack_eq_hankelMinor hA

/-- Nonnegativity of Xi's Suzuki two-jet Schur slack is equivalent, with no loss, to
nonnegativity of the safe-shift first Hankel minor. -/
theorem primeArchSuzuki_twoJetSlack_nonneg_iff_shiftedHankelMinor_nonneg :
    0 ≤ primeArchSuzukiSecondDefectCalibration +
          2 * (1 - primeArchSuzukiFirstDefectCalibration ^ 2) ↔
      0 ≤
        (primeArchShiftedReciprocalMoment 1 0).re *
            (primeArchShiftedReciprocalMoment 1 2).re -
          (primeArchShiftedReciprocalMoment 1 1).re ^ 2 := by
  rw [primeArchSuzuki_twoJetSlack_eq_shiftedHankelMinor]
  have hA : 0 < (primeArchShiftedReciprocalMoment 1 0).re :=
    re_primeArchShiftedReciprocalMoment_one_zero_pos
  have hden :
      0 < (primeArchShiftedReciprocalMoment 1 0).re ^ 2 :=
    sq_pos_of_pos hA
  constructor
  · intro h
    have hnum := (le_div_iff₀ hden).mp h
    nlinarith
  · intro h
    apply (le_div_iff₀ hden).2
    nlinarith

end

end RHTower

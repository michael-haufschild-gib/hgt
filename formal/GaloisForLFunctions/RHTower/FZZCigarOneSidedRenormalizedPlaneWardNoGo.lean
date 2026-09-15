import GaloisForLFunctions.RHTower.FZZCigarMarkedScreeningCutoff
import GaloisForLFunctions.RHTower.FZZCigarOneSidedRadialRealCompactWardNoGo

/-!
# One-sided FZZ radial / scalar renormalized-plane Ward no-go

The literal first-exponent derivative of the counterterm-preserving plane source
is real, both before independent cutoff removal and at its finite-part limit.
It cannot cancel the strictly negative imaginary orientation of the physical
one-sided radial receiver. This eliminates scalar-real renormalized-plane Ward
branches, while leaving a genuinely complex, non-scalar source law open.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- One-sided radial receiver plus the real first-exponent derivative of the
counterterm-preserving plane source at finite cutoffs. -/
def fzzOneSidedRadialRenormalizedPlaneWardDefect
    (radialCoupling radialScale momentum u v T U : ℝ) : ℂ :=
  deriv (fzzMarkedRadialReplicaResponse radialCoupling radialScale) momentum +
    ((deriv (fun a : ℝ =>
      fzzScreeningPlaneCorrectedCutoff a
        (fzzScreeningFirstContinuationPower v) T U)
      (fzzScreeningFirstContinuationPower u) : ℝ) : ℂ)

/-- The finite-cutoff scalar renormalized-plane branch never satisfies a
vanishing complex mixed Ward equation. -/
theorem fzzOneSidedRadialRenormalizedPlaneWardDefect_ne_zero
    (radialCoupling radialScale momentum u v T U : ℝ) :
    fzzOneSidedRadialRenormalizedPlaneWardDefect
      radialCoupling radialScale momentum u v T U ≠ 0 := by
  unfold fzzOneSidedRadialRenormalizedPlaneWardDefect
  exact fzzOneSidedRadialMixedResponse_add_real_ne_zero
    radialCoupling radialScale momentum _

/-- One-sided radial receiver plus the corresponding real full-plane finite-part
first-exponent derivative. -/
def fzzOneSidedRadialFinitePlaneWardDefect
    (radialCoupling radialScale momentum u v : ℝ) : ℂ :=
  deriv (fzzMarkedRadialReplicaResponse radialCoupling radialScale) momentum +
    ((deriv (fun a : ℝ => fzzScreeningPlaneFinitePart a
      (fzzScreeningFirstContinuationPower v))
      (fzzScreeningFirstContinuationPower u) : ℝ) : ℂ)

/-- The scalar real finite-part branch never satisfies a vanishing complex mixed
Ward equation. -/
theorem fzzOneSidedRadialFinitePlaneWardDefect_ne_zero
    (radialCoupling radialScale momentum u v : ℝ) :
    fzzOneSidedRadialFinitePlaneWardDefect
      radialCoupling radialScale momentum u v ≠ 0 := by
  unfold fzzOneSidedRadialFinitePlaneWardDefect
  exact fzzOneSidedRadialMixedResponse_add_real_ne_zero
    radialCoupling radialScale momentum _

/-- Closed FZZ-P branch: no scalar-real renormalized plane source, at finite
cutoff or after finite-part removal, can be the missing one-sided mixed-Ward
cancellation. -/
def FZZOneSidedRadialRealRenormalizedPlaneWardRouteKilled : Prop :=
  (∀ radialCoupling radialScale momentum u v T U : ℝ,
    fzzOneSidedRadialRenormalizedPlaneWardDefect
      radialCoupling radialScale momentum u v T U ≠ 0) ∧
  ∀ radialCoupling radialScale momentum u v : ℝ,
    fzzOneSidedRadialFinitePlaneWardDefect
      radialCoupling radialScale momentum u v ≠ 0

/-- **FZZ-P route kill.** Counterterm-preserving scalar-real plane source terms
cannot close the physical one-sided radial mixed Ward equation. -/
theorem fzzOneSidedRadialRealRenormalizedPlaneWardRouteKilled :
    FZZOneSidedRadialRealRenormalizedPlaneWardRouteKilled := by
  exact ⟨fzzOneSidedRadialRenormalizedPlaneWardDefect_ne_zero,
    fzzOneSidedRadialFinitePlaneWardDefect_ne_zero⟩

end

end GaloisForLFunctions.RHTower

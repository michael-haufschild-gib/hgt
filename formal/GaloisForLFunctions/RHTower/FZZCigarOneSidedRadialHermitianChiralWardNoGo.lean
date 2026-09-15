import GaloisForLFunctions.RHTower.FZZCigarOneSidedRadialRealCompactWardNoGo
import GaloisForLFunctions.RHTower.FZZCigarParityHermitianChiralOrientationClassification

/-!
# One-sided FZZ radial / Hermitian chiral Ward no-go

Hermitian chiral reporters contain an imaginary off-diagonal *coefficient*,
but their observable value is real. They may distinguish conjugate Krein
orientations, yet cannot cancel the strictly negative imaginary component of
the physical one-sided radial response. This kills every additive Hermitian
chiral completion of that Ward equation.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Physical one-sided radial receiver plus an arbitrary Hermitian chiral FZZ
reporter. -/
def fzzOneSidedRadialHermitianChiralWardDefect
    (radialCoupling radialScale momentum : ℝ)
    (a b c d : ℝ) (u : ℂ × ℂ) : ℂ :=
  deriv (fzzMarkedRadialReplicaResponse radialCoupling radialScale) momentum +
    RHTower.fzzCigarParityHermitianQuadraticObservable a b c d u

/-- No Hermitian chiral reporter can cancel the physical one-sided radial
response, regardless of its imaginary off-diagonal coefficient. -/
theorem fzzOneSidedRadialHermitianChiralWardDefect_ne_zero
    (radialCoupling radialScale momentum : ℝ)
    (a b c d : ℝ) (u : ℂ × ℂ) :
    fzzOneSidedRadialHermitianChiralWardDefect
      radialCoupling radialScale momentum a b c d u ≠ 0 := by
  have him := RHTower.fzzCigarParityHermitianQuadraticObservable_im_eq_zero
    a b c d u
  have hreal : RHTower.fzzCigarParityHermitianQuadraticObservable a b c d u =
      (RHTower.fzzCigarParityHermitianQuadraticObservable a b c d u).re := by
    apply Complex.ext <;> simp [him]
  unfold fzzOneSidedRadialHermitianChiralWardDefect
  rw [hreal]
  exact fzzOneSidedRadialMixedResponse_add_real_ne_zero
    radialCoupling radialScale momentum _

/-- Closed FZZ-P branch: no additive Hermitian chiral FZZ reporter supplies
the complex response needed by the physical one-sided mixed Ward equation. -/
def FZZOneSidedRadialHermitianChiralWardRouteKilled : Prop :=
  ∀ radialCoupling radialScale momentum a b c d : ℝ, ∀ u : ℂ × ℂ,
    fzzOneSidedRadialHermitianChiralWardDefect
      radialCoupling radialScale momentum a b c d u ≠ 0

/-- **FZZ-P route kill.** Hermitian chiral orientation is not a complex Ward
cancellation term. -/
theorem fzzOneSidedRadialHermitianChiralWardRouteKilled :
    FZZOneSidedRadialHermitianChiralWardRouteKilled := by
  exact fzzOneSidedRadialHermitianChiralWardDefect_ne_zero

end

end GaloisForLFunctions.RHTower

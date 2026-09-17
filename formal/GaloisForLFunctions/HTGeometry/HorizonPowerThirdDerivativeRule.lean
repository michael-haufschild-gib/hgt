import GaloisForLFunctions.HTGeometry.HorizonPowerJetAlgebra

/-! A bounded-elaboration third-derivative rule for an exponential jet. -/

namespace GaloisForLFunctions.HTGeometry

theorem third_deriv_of_quadratic_log_jet
    {P P₁ P₂ X Y Z : ℝ → ℂ} {x : ℝ}
    (hX : HasDerivAt X (Y x) x) (hY : HasDerivAt Y (Z x) x)
    (hP : HasDerivAt P (P₁ x) x)
    (hP₁ : P₁ = fun t => X t * P t)
    (hP₂ : P₂ = (Y + X ^ 2) * P) :
    HasDerivAt P₂ ((Z x + 3 * Y x * X x + X x ^ 3) * P x) x := by
  rw [hP₂]
  have hsquare := hX.pow 2
  have hsum := hY.add hsquare
  have hproduct := hsum.mul hP
  rw [hP₁] at hproduct
  apply hproduct.congr_deriv
  simpa only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, pow_one, pow_two,
    Nat.reduceSub, Nat.cast_ofNat] using
    horizonPowerThird_algebra (X x) (Y x) (Z x) (P x)

end GaloisForLFunctions.HTGeometry

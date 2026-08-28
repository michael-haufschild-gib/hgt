import GaloisForLFunctions.RHTower.ThetaTailFirstMomentDoubleLaplace

/-!
# Tilt collapse of the theta-tail Krein channels

The two Krein channels of the theta tail are one Laplace packet reweighted by the tilted
logarithmic pair of the completed source transform: with

`xiCentTiltPlus c w = deriv xiCent w + c·xiCent w`,
`xiCentTiltMinus c w = deriv xiCent w - c·xiCent w`,

the literal source integrals `thetaTailKreinPlusTransform`/`MinusTransform` factor as
`e^{-ws}` times the corresponding tilt.  The tilt pair carries the Bezoutian without division
and without any half-plane hypothesis: the bilinear difference of the two tilts is `2c` times
the Bezoutian numerator on all of `ℂ²`, and `2c(w+y)`-times the Bezoutian equals that
difference everywhere, including the antidiagonal `y = -w`, where both sides vanish by the
parity of the completed source.

On the critical boundary `Re w = 0` the two tilts are exact negated conjugates of each other,
so the two channels have identical modulus there: the boundary is lossless for every tilt
parameter.  Off-boundary modulus comparison of the tilts is the Bezoutian diagonal.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- Positive tilt of the completed-source logarithmic pair. -/
def xiCentTiltPlus (c : ℝ) (w : ℂ) : ℂ :=
  deriv xiCent w + (c : ℂ) * xiCent w

/-- Negative tilt of the completed-source logarithmic pair. -/
def xiCentTiltMinus (c : ℝ) (w : ℂ) : ℂ :=
  deriv xiCent w - (c : ℂ) * xiCent w

/-- The positive Krein channel is the Laplace exponential times the positive tilt. -/
theorem thetaTailKreinPlusTransform_eq_exp_mul_tilt (c : ℝ) (w : ℂ) (s : ℝ) :
    thetaTailKreinPlusTransform c w s =
      Complex.exp (-(w * (s : ℂ))) * xiCentTiltPlus c w := by
  rw [thetaTailKreinPlusTransform_eq, thetaBilateralLaplaceMoment_eq_deriv_xiCent,
    thetaBilateralLaplace_eq_xiCent, xiCentTiltPlus]

/-- The negative Krein channel is the Laplace exponential times the negative tilt. -/
theorem thetaTailKreinMinusTransform_eq_exp_mul_tilt (c : ℝ) (w : ℂ) (s : ℝ) :
    thetaTailKreinMinusTransform c w s =
      Complex.exp (-(w * (s : ℂ))) * xiCentTiltMinus c w := by
  rw [thetaTailKreinMinusTransform_eq, thetaBilateralLaplaceMoment_eq_deriv_xiCent,
    thetaBilateralLaplace_eq_xiCent, xiCentTiltMinus]

/-- The bilinear tilt difference is `2c` times the Bezoutian numerator, on all of `ℂ²`. -/
theorem xiCentTilt_mul_sub_eq_bezoutianNumerator (c : ℝ) (w y : ℂ) :
    xiCentTiltPlus c w * xiCentTiltPlus c y -
      xiCentTiltMinus c w * xiCentTiltMinus c y =
    2 * (c : ℂ) * xiCentBezoutianNumerator w y := by
  unfold xiCentTiltPlus xiCentTiltMinus xiCentBezoutianNumerator
  ring

/-- Tilt parity across the antidiagonal: reflecting the argument swaps the tilts and flips the
sign. -/
theorem xiCentTiltPlus_neg (c : ℝ) (w : ℂ) :
    xiCentTiltPlus c (-w) = -xiCentTiltMinus c w := by
  unfold xiCentTiltPlus xiCentTiltMinus
  rw [deriv_xiCent_neg, xiCent_even]
  ring

theorem xiCentTiltMinus_neg (c : ℝ) (w : ℂ) :
    xiCentTiltMinus c (-w) = -xiCentTiltPlus c w := by
  unfold xiCentTiltPlus xiCentTiltMinus
  rw [deriv_xiCent_neg, xiCent_even]
  ring

/-- **Division-free tilt form of the Bezoutian, on all of `ℂ²`.**  `2c(w+y)` times the entire
Bezoutian is the bilinear tilt difference; on the antidiagonal both sides vanish by parity. -/
theorem two_mul_add_mul_xiCentBezoutian_eq_tilt (c : ℝ) (w y : ℂ) :
    2 * (c : ℂ) * (w + y) * xiCentBezoutian w y =
      xiCentTiltPlus c w * xiCentTiltPlus c y -
        xiCentTiltMinus c w * xiCentTiltMinus c y := by
  by_cases hy : w + y = 0
  · have hyw : y = -w := by linear_combination hy
    rw [hy, hyw, xiCentTiltPlus_neg, xiCentTiltMinus_neg]
    ring
  · rw [xiCentBezoutian_eq_div hy, xiCentTilt_mul_sub_eq_bezoutianNumerator]
    field_simp

/-- Real tilts are conjugation-equivariant. -/
theorem xiCentTiltPlus_conj (c : ℝ) (w : ℂ) :
    xiCentTiltPlus c (conj w) = conj (xiCentTiltPlus c w) := by
  unfold xiCentTiltPlus
  rw [deriv_xiCent_conj, xiCent_conj, map_add, map_mul, Complex.conj_ofReal]

theorem xiCentTiltMinus_conj (c : ℝ) (w : ℂ) :
    xiCentTiltMinus c (conj w) = conj (xiCentTiltMinus c w) := by
  unfold xiCentTiltMinus
  rw [deriv_xiCent_conj, xiCent_conj, map_sub, map_mul, Complex.conj_ofReal]

/-- **The critical boundary is lossless.**  On `Re w = 0` the negative tilt is the negated
conjugate of the positive tilt: the two Krein channels differ there only by a phase. -/
theorem xiCentTiltMinus_I_mul_eq_neg_conj (c τ : ℝ) :
    xiCentTiltMinus c (Complex.I * τ) = -conj (xiCentTiltPlus c (Complex.I * τ)) := by
  have hneg : -(Complex.I * (τ : ℂ)) = conj (Complex.I * (τ : ℂ)) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have h := xiCentTiltMinus_neg c (Complex.I * τ)
  rw [show xiCentTiltMinus c (-(Complex.I * (τ : ℂ))) =
      -xiCentTiltPlus c (Complex.I * τ) from h ▸ rfl] at *
  calc
    xiCentTiltMinus c (Complex.I * τ) =
        -xiCentTiltPlus c (-(Complex.I * τ)) := by
      rw [xiCentTiltPlus_neg]
      ring
    _ = -xiCentTiltPlus c (conj (Complex.I * τ)) := by rw [hneg]
    _ = -conj (xiCentTiltPlus c (Complex.I * τ)) := by rw [xiCentTiltPlus_conj]

/-- Equal channel modulus on the critical boundary. -/
theorem norm_xiCentTiltMinus_I_mul (c τ : ℝ) :
    ‖xiCentTiltMinus c (Complex.I * τ)‖ = ‖xiCentTiltPlus c (Complex.I * τ)‖ := by
  rw [xiCentTiltMinus_I_mul_eq_neg_conj, norm_neg, Complex.norm_conj]

end

end RHTower

module
public import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayCoefficients
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Interior perfect-square symbol of the complete primitive theta ray

The growing completion coefficient by itself has a sign-indefinite Jacobi symbol away from the
critical boundary.  The complete five-derivative primitive-ray packet has a different, rigid
symbol.  If `a` is the interior beta exponent, `b = 1 / 2 - a`, and the radial Laplace exponent is
`lambda = 2 * a - 1 / 2`, then the packet is exactly the coefficient obtained by applying
`(d^2/dt^2 - b^2)^2` to the angular ground state `sech(t)^a`.

After the two elementary beta-shift ratios are inserted, every lower mode cancels and the
spectral multiplier is the nonnegative perfect square

```text
(s^2 + b^2)^2.
```

At `a = 1 / 2` this specializes to the fourth-order `s^4` collapse.  The result is the exact
algebraic core of an interior primitive-ray transform; this module does not assert the global
change of variables, endpoint control, a current sign, or RH.
-/

@[expose] public section
open Real

namespace RHTower

noncomputable section

/-- The radial Laplace polynomial of the complete five-derivative primitive-ray packet.  The
alternating signs are those produced by integration by parts against `exp (lambda * r)`. -/
def thetaCuspPrimitiveRayRadialLaplacePacket (u lambda : ℝ) : ℝ :=
  thetaCuspPrimitiveRayCoefficientZero u -
    lambda * thetaCuspPrimitiveRayCoefficientOne u +
    lambda ^ 2 * thetaCuspPrimitiveRayCoefficientTwo u -
    lambda ^ 3 * thetaCuspPrimitiveRayCoefficientThree u +
    lambda ^ 4 * thetaCuspPrimitiveRayCoefficientFour u

/-- The coefficient of `sech(t)^a` after applying the fourth-order shifted operator
`(d^2/dt^2 - b^2)^2`, written in the primitive angular coordinate `w = u(1-u)`. -/
def thetaCuspPrimitiveRayFourthOrderGroundCoefficient (a b u : ℝ) : ℝ :=
  (a ^ 2 - b ^ 2) ^ 2 -
    8 * a * (a + 1) * (a ^ 2 + 2 * a + 2 - b ^ 2) *
      thetaCuspPrimitiveRayMoment u +
    16 * a * (a + 1) * (a + 2) * (a + 3) *
      thetaCuspPrimitiveRayMoment u ^ 2

/-- **Complete interior packet identity.**  The source-selected radial exponent converts the
five theta derivatives into the fourth-order shifted ground-state coefficient. -/
theorem thetaCuspPrimitiveRayRadialLaplacePacket_two_mul_sub_half
    (a u : ℝ) :
    thetaCuspPrimitiveRayRadialLaplacePacket u (2 * a - 1 / 2) =
      thetaCuspPrimitiveRayFourthOrderGroundCoefficient
        a (1 / 2 - a) u := by
  unfold thetaCuspPrimitiveRayRadialLaplacePacket
    thetaCuspPrimitiveRayFourthOrderGroundCoefficient
    thetaCuspPrimitiveRayCoefficientZero
    thetaCuspPrimitiveRayCoefficientOne
    thetaCuspPrimitiveRayCoefficientTwo
    thetaCuspPrimitiveRayCoefficientThree
    thetaCuspPrimitiveRayCoefficientFour
  ring

/-- At the critical boundary the complete radial Laplace packet is twice the growing completion
coefficient, explaining why the lower modes disappear there without an interior correction. -/
theorem thetaCuspPrimitiveRayRadialLaplacePacket_half
    (u : ℝ) :
    thetaCuspPrimitiveRayRadialLaplacePacket u (1 / 2) =
      2 * thetaCuspPrimitiveRayGrowingCoefficient u := by
  unfold thetaCuspPrimitiveRayRadialLaplacePacket
    thetaCuspPrimitiveRayCoefficientZero
    thetaCuspPrimitiveRayCoefficientOne
    thetaCuspPrimitiveRayCoefficientTwo
    thetaCuspPrimitiveRayCoefficientThree
    thetaCuspPrimitiveRayCoefficientFour
    thetaCuspPrimitiveRayGrowingCoefficient
  ring

/-- Fourier ratio between the beta weights `sech(t)^(a+2)` and `sech(t)^a`. -/
def thetaCuspPrimitiveRayBetaShiftTwoRatio (a s : ℝ) : ℝ :=
  (a ^ 2 + s ^ 2) / (a * (a + 1))

/-- Fourier ratio between the beta weights `sech(t)^(a+4)` and `sech(t)^a`. -/
def thetaCuspPrimitiveRayBetaShiftFourRatio (a s : ℝ) : ℝ :=
  ((a ^ 2 + s ^ 2) * ((a + 2) ^ 2 + s ^ 2)) /
    (a * (a + 1) * (a + 2) * (a + 3))

/-- The algebraic generalized-Jacobi multiplier of the complete interior packet.  The factors
`1/4` and `1/16` come from `u(1-u) = sech(t)^2 / 4`. -/
def thetaCuspPrimitiveRayInteriorSpectralMultiplier (a s : ℝ) : ℝ :=
  let b := 1 / 2 - a
  (a ^ 2 - b ^ 2) ^ 2 -
    (8 * a * (a + 1) * (a ^ 2 + 2 * a + 2 - b ^ 2) / 4) *
      thetaCuspPrimitiveRayBetaShiftTwoRatio a s +
    (16 * a * (a + 1) * (a + 2) * (a + 3) / 16) *
      thetaCuspPrimitiveRayBetaShiftFourRatio a s

/-- **Interior perfect-square collapse.**  For every positive beta exponent, the complete
primitive-ray spectral multiplier is exactly `(s^2 + (1/2-a)^2)^2`. -/
theorem thetaCuspPrimitiveRayInteriorSpectralMultiplier_eq_square
    {a : ℝ} (ha : 0 < a) (s : ℝ) :
    thetaCuspPrimitiveRayInteriorSpectralMultiplier a s =
      (s ^ 2 + (1 / 2 - a) ^ 2) ^ 2 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ha1 : a + 1 ≠ 0 := by linarith
  have ha2 : a + 2 ≠ 0 := by linarith
  have ha3 : a + 3 ≠ 0 := by linarith
  unfold thetaCuspPrimitiveRayInteriorSpectralMultiplier
    thetaCuspPrimitiveRayBetaShiftTwoRatio
    thetaCuspPrimitiveRayBetaShiftFourRatio
  dsimp only
  field_simp [ha0, ha1, ha2, ha3]
  ring

theorem thetaCuspPrimitiveRayInteriorSpectralMultiplier_nonneg
    {a : ℝ} (ha : 0 < a) (s : ℝ) :
    0 ≤ thetaCuspPrimitiveRayInteriorSpectralMultiplier a s := by
  rw [thetaCuspPrimitiveRayInteriorSpectralMultiplier_eq_square ha]
  positivity

/-- Critical-boundary specialization of the interior square. -/
theorem thetaCuspPrimitiveRayInteriorSpectralMultiplier_half
    (s : ℝ) :
    thetaCuspPrimitiveRayInteriorSpectralMultiplier (1 / 2) s = s ^ 4 := by
  rw [thetaCuspPrimitiveRayInteriorSpectralMultiplier_eq_square (by norm_num)]
  ring

end

end RHTower

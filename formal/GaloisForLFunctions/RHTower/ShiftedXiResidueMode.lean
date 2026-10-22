import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.Suzuki.SuzukiAntiPickIdentity

/-!
# The simple-zero residue mode of the shifted-xi quotient

For a positive shift `omega` and a certified simple zero `rho` of the completed Riemann xi
function, this file identifies the corresponding pole of

`xi (1/2 - omega - i*z) / xi (1/2 + omega - i*z)`

and proves its exact residue.  Multiplication by the contour factor `i` gives
`-xi (rho - 2*omega) / xi' rho`, equation (7) of the Euler-leakage residue-mode card.
-/

namespace RHTower

open Complex Filter Set

/-- A point certified to be a simple zero of the completed Riemann xi function. -/
structure XiSimpleZero where
  point : ℂ
  xi_eq_zero : xi point = 0
  deriv_ne_zero : deriv xi point ≠ 0

/-- Strictly positive real shifts used in the shifted-xi quotient. -/
abbrev PositiveXiShift := {ω : ℝ // 0 < ω}

noncomputable def shiftedXiNumerator (ω : ℝ) (z : ℂ) : ℂ :=
  xi ((1 / 2 : ℂ) - (ω : ℂ) - Complex.I * z)

noncomputable def shiftedXiDenominator (ω : ℝ) (z : ℂ) : ℂ :=
  xi ((1 / 2 : ℂ) + (ω : ℂ) - Complex.I * z)

noncomputable def shiftedXiQuotient (ω : ℝ) (z : ℂ) : ℂ :=
  shiftedXiNumerator ω z / shiftedXiDenominator ω z

/-- Pole in the spectral `z`-plane corresponding to a xi zero `rho`. -/
noncomputable def shiftedXiPole (ω : ℝ) (ρ : ℂ) : ℂ :=
  (-ρ.im : ℂ) + Complex.I * (ρ.re - 1 / 2 - ω)

theorem shiftedXiDenominator_argument_at_pole (ω : ℝ) (ρ : ℂ) :
    (1 / 2 : ℂ) + (ω : ℂ) - Complex.I * shiftedXiPole ω ρ = ρ := by
  apply Complex.ext
  · simp [shiftedXiPole]
    ring
  · simp [shiftedXiPole]

theorem shiftedXiNumerator_argument_at_pole (ω : ℝ) (ρ : ℂ) :
    (1 / 2 : ℂ) - (ω : ℂ) - Complex.I * shiftedXiPole ω ρ = ρ - 2 * (ω : ℂ) := by
  apply Complex.ext
  · simp [shiftedXiPole]
    ring
  · simp [shiftedXiPole]

theorem shiftedXiDenominator_hasDerivAt (ω : ℝ) (ρ : ℂ) :
    HasDerivAt (shiftedXiDenominator ω) (-Complex.I * deriv xi ρ)
      (shiftedXiPole ω ρ) := by
  have hinner : HasDerivAt
      (fun z : ℂ => (1 / 2 : ℂ) + (ω : ℂ) - Complex.I * z) (-Complex.I)
      (shiftedXiPole ω ρ) := by
    exact (hasDerivAt_const_mul (x := shiftedXiPole ω ρ) Complex.I).const_sub
      ((1 / 2 : ℂ) + (ω : ℂ))
  have hxi : HasDerivAt xi
      (deriv xi ((1 / 2 : ℂ) + (ω : ℂ) - Complex.I * shiftedXiPole ω ρ))
      ((1 / 2 : ℂ) + (ω : ℂ) - Complex.I * shiftedXiPole ω ρ) :=
    xi_differentiable.differentiableAt.hasDerivAt
  have hcomp := hxi.comp (shiftedXiPole ω ρ) hinner
  rw [shiftedXiDenominator_argument_at_pole ω ρ] at hcomp
  have hcomp' : HasDerivAt
      (xi ∘ fun z : ℂ => (1 / 2 : ℂ) + (ω : ℂ) - z * Complex.I)
      (-Complex.I * deriv xi ρ) (shiftedXiPole ω ρ) := by
    simpa only [mul_neg, mul_comm] using hcomp
  refine hcomp'.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro z
  simp only [Function.comp_apply, shiftedXiDenominator]
  rw [mul_comm z Complex.I]

theorem shiftedXiDenominator_eq_zero (ω : ℝ) (Z : XiSimpleZero) :
    shiftedXiDenominator ω (shiftedXiPole ω Z.point) = 0 := by
  rw [shiftedXiDenominator, shiftedXiDenominator_argument_at_pole, Z.xi_eq_zero]

theorem shiftedXiNumerator_continuousAt (ω : ℝ) (ρ : ℂ) :
    ContinuousAt (shiftedXiNumerator ω) (shiftedXiPole ω ρ) := by
  unfold shiftedXiNumerator
  have hinner : DifferentiableAt ℂ
      (fun z : ℂ => (1 / 2 : ℂ) - (ω : ℂ) - Complex.I * z) (shiftedXiPole ω ρ) := by
    fun_prop
  exact (xi_differentiable.differentiableAt.comp (shiftedXiPole ω ρ) hinner).continuousAt

noncomputable def shiftedXiResidueCoeff (ω : ℝ) (Z : XiSimpleZero) : ℂ :=
  xi (Z.point - 2 * (ω : ℂ)) / (-Complex.I * deriv xi Z.point)

/-- The shifted-xi quotient has the residue forced by a certified simple xi zero. -/
theorem shiftedXiQuotient_residue_tendsto (ω : PositiveXiShift) (Z : XiSimpleZero) :
    Filter.Tendsto
      (fun z => (z - shiftedXiPole ω Z.point) * shiftedXiQuotient ω z)
      (nhdsWithin (shiftedXiPole ω Z.point) {shiftedXiPole ω Z.point}ᶜ)
      (nhds (shiftedXiResidueCoeff ω Z)) := by
  have hderiv := shiftedXiDenominator_hasDerivAt (ω : ℝ) Z.point
  have hderiv_ne : -Complex.I * deriv xi Z.point ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) Z.deriv_ne_zero
  have hres := tendsto_residue_of_simple_zero hderiv
    (shiftedXiDenominator_eq_zero (ω : ℝ) Z) hderiv_ne
    (shiftedXiNumerator_continuousAt (ω : ℝ) Z.point)
  simpa only [shiftedXiQuotient, shiftedXiResidueCoeff,
    shiftedXiNumerator, shiftedXiNumerator_argument_at_pole] using hres

/-- Equation (7): multiplication by the contour factor `i` gives the explicit xi coefficient. -/
theorem I_mul_shiftedXiResidueCoeff (ω : PositiveXiShift) (Z : XiSimpleZero) :
    Complex.I * shiftedXiResidueCoeff ω Z =
      -xi (Z.point - 2 * ((ω : ℝ) : ℂ)) / deriv xi Z.point := by
  rw [shiftedXiResidueCoeff]
  field_simp [Z.deriv_ne_zero, Complex.I_ne_zero]

end RHTower

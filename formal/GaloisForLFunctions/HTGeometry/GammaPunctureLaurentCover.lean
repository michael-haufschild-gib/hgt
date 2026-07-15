import GaloisForLFunctions.HTGeometry.GammaExteriorInverseBranches

/-!
# The inverse-Gamma source puncture and its Laurent cover

The common inverse-Gamma exterior has the source-defined puncture coordinate
`t = -1 / Gamma`.  On its logarithmic cover, write the exterior value as
`y(z) = -exp(-z)`.  Then `t(z) = exp(z)` and `t(z)⁻¹ = exp(-z)` are genuine opposite Laurent
coordinates.  A deck translation by `2*pi*I` fixes the exterior value, every inverse-Gamma sheet,
and both integral Laurent halves, while the fractional section `t^(-s)` acquires the exact
holonomy `exp(-2*pi*I*s)`.

This supplies a source puncture and a scalar Laurent double without choosing a divisor point.  It
does not identify these scalar modes with a projective-horizon current action or provide a
positive level for the affine residue cocycle.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exterior inverse-Gamma value lifted to the logarithmic puncture cover. -/
def gammaPunctureExteriorLift (z : ℂ) : ℂ :=
  -Complex.exp (-z)

/-- The source puncture coordinate `t = -1 / Gamma` on the logarithmic cover. -/
def gammaPunctureCoordinate (z : ℂ) : ℂ :=
  Complex.exp z

/-- The opposite scalar Laurent coordinate `t⁻¹ = -Gamma`. -/
def gammaPunctureOppositeCoordinate (z : ℂ) : ℂ :=
  Complex.exp (-z)

/-- The fractional source section `t^(-s)` on the logarithmic cover. -/
def gammaPunctureFractionalMode (s z : ℂ) : ℂ :=
  Complex.exp (-s * z)

/-- Holonomy of `t^(-s)` around the source puncture. -/
def gammaPunctureFractionalHolonomy (s : ℂ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * s))

/-- The exterior inverse-Gamma value is deck invariant. -/
theorem gammaPunctureExteriorLift_shift (z : ℂ) :
    gammaPunctureExteriorLift
        (z + 2 * (Real.pi : ℂ) * Complex.I) =
      gammaPunctureExteriorLift z := by
  rw [gammaPunctureExteriorLift, gammaPunctureExteriorLift]
  rw [show -(z + 2 * (Real.pi : ℂ) * Complex.I) =
      -z + -(2 * (Real.pi : ℂ) * Complex.I) by ring]
  have hperiod : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  rw [Complex.exp_add, hperiod, mul_one]

/-- The positive scalar Laurent coordinate is deck invariant. -/
theorem gammaPunctureCoordinate_shift (z : ℂ) :
    gammaPunctureCoordinate
        (z + 2 * (Real.pi : ℂ) * Complex.I) =
      gammaPunctureCoordinate z := by
  rw [gammaPunctureCoordinate, gammaPunctureCoordinate,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The negative scalar Laurent coordinate is deck invariant. -/
theorem gammaPunctureOppositeCoordinate_shift (z : ℂ) :
    gammaPunctureOppositeCoordinate
        (z + 2 * (Real.pi : ℂ) * Complex.I) =
      gammaPunctureOppositeCoordinate z := by
  rw [gammaPunctureOppositeCoordinate, gammaPunctureOppositeCoordinate]
  rw [show -(z + 2 * (Real.pi : ℂ) * Complex.I) =
      -z + -(2 * (Real.pi : ℂ) * Complex.I) by ring]
  have hperiod : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  rw [Complex.exp_add, hperiod, mul_one]

/-- The two source coordinates are exact multiplicative inverses. -/
theorem gammaPunctureCoordinate_mul_opposite (z : ℂ) :
    gammaPunctureCoordinate z * gammaPunctureOppositeCoordinate z = 1 := by
  rw [gammaPunctureCoordinate, gammaPunctureOppositeCoordinate, ← Complex.exp_add]
  simp

/-- The positive Laurent coordinate is literally `-1 / Gamma` on an inverse sheet. -/
theorem gammaPunctureCoordinate_eq_neg_inv_exteriorLift (z : ℂ) :
    gammaPunctureCoordinate z = -(gammaPunctureExteriorLift z)⁻¹ := by
  rw [gammaPunctureCoordinate, gammaPunctureExteriorLift, inv_neg, neg_neg,
    Complex.exp_neg, inv_inv]

/-- The opposite Laurent coordinate is literally `-Gamma` on an inverse sheet. -/
theorem gammaPunctureOppositeCoordinate_eq_neg_exteriorLift (z : ℂ) :
    gammaPunctureOppositeCoordinate z = -gammaPunctureExteriorLift z := by
  simp [gammaPunctureOppositeCoordinate, gammaPunctureExteriorLift]

/-- A fractional mode acquires its exact scalar holonomy under one deck translation. -/
theorem gammaPunctureFractionalMode_shift (s z : ℂ) :
    gammaPunctureFractionalMode s
        (z + 2 * (Real.pi : ℂ) * Complex.I) =
      gammaPunctureFractionalHolonomy s * gammaPunctureFractionalMode s z := by
  rw [gammaPunctureFractionalMode, gammaPunctureFractionalMode,
    gammaPunctureFractionalHolonomy]
  rw [show -s * (z + 2 * (Real.pi : ℂ) * Complex.I) =
      -(2 * (Real.pi : ℂ) * Complex.I * s) + -s * z by ring]
  rw [Complex.exp_add]

/-- Every actual inverse-Gamma sheet is fixed by the puncture deck translation. -/
theorem gammaExteriorInverseBranch_puncture_shift
    (n : ℕ) (z : ℂ) :
    gammaExteriorInverseBranch n
        (gammaPunctureExteriorLift
          (z + 2 * (Real.pi : ℂ) * Complex.I)) =
      gammaExteriorInverseBranch n (gammaPunctureExteriorLift z) := by
  rw [gammaPunctureExteriorLift_shift]

/-- On the exterior chamber the lifted source really is the Gamma value of the inverse sheet. -/
theorem Gamma_gammaExteriorInverseBranch_puncture
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    {z : ℂ} (hz : gammaPunctureExteriorLift z ∈ gammaExterior) :
    Complex.Gamma
        (gammaExteriorInverseBranch n (gammaPunctureExteriorLift z)) =
      gammaPunctureExteriorLift z := by
  exact Gamma_gammaExteriorInverseBranch hn hz

end

end GaloisForLFunctions.HTGeometry

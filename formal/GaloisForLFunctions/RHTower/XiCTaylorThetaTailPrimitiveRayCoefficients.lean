module
public import Mathlib.Data.Real.Basic

/-! # Scalar coefficients of the complete primitive theta ray

These are the unchanged coefficients used by the literal density-pair identity in
`XiCTaylorThetaTailPrimitiveRayPolarization`. Keeping them separate makes the
interior transform independent of the source differentiation import tree.
-/

@[expose] public section
namespace RHTower
noncomputable section

/-- The single symmetric angular coordinate carried by a primitive ray. -/
def thetaCuspPrimitiveRayMoment (u : ℝ) : ℝ :=
  u * (1 - u)

/-- Zeroth radial derivative coefficient of the primitive-ray density packet. -/
def thetaCuspPrimitiveRayCoefficientZero (u : ℝ) : ℝ :=
  -(25 / 4 : ℝ) * thetaCuspPrimitiveRayMoment u +
    (585 / 16 : ℝ) * thetaCuspPrimitiveRayMoment u ^ 2

/-- First radial derivative coefficient of the primitive-ray density packet. -/
def thetaCuspPrimitiveRayCoefficientOne (u : ℝ) : ℝ :=
  (75 / 4 : ℝ) * thetaCuspPrimitiveRayMoment u -
    (203 / 2 : ℝ) * thetaCuspPrimitiveRayMoment u ^ 2

/-- Second radial derivative coefficient of the primitive-ray density packet. -/
def thetaCuspPrimitiveRayCoefficientTwo (u : ℝ) : ℝ :=
  (1 / 4 : ℝ) - 14 * thetaCuspPrimitiveRayMoment u +
    (127 / 2 : ℝ) * thetaCuspPrimitiveRayMoment u ^ 2

/-- Third radial derivative coefficient of the primitive-ray density packet. -/
def thetaCuspPrimitiveRayCoefficientThree (u : ℝ) : ℝ :=
  3 * thetaCuspPrimitiveRayMoment u -
    14 * thetaCuspPrimitiveRayMoment u ^ 2

/-- Fourth radial derivative coefficient of the primitive-ray density packet. -/
def thetaCuspPrimitiveRayCoefficientFour (u : ℝ) : ℝ :=
  thetaCuspPrimitiveRayMoment u ^ 2

/-- Coefficient of the growing half-exponential after radial theta reflection. -/
def thetaCuspPrimitiveRayGrowingCoefficient (u : ℝ) : ℝ :=
  (1 / 32 : ℝ) - (39 / 4 : ℝ) * thetaCuspPrimitiveRayMoment u +
    (105 / 2 : ℝ) * thetaCuspPrimitiveRayMoment u ^ 2

end
end RHTower

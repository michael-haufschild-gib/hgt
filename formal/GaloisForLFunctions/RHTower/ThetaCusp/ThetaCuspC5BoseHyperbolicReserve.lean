import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFixedActionC5LikelihoodHomotopyCurvatureReduction

/-!
# Exact hyperbolic boundary of the C5 compensation reserve

This is an algebraic bridge, not a theta-source sign theorem. It retains the complete signed
three-channel compensation and identifies its scalar boundary after normalization by action
loss, velocity, and negative center transport. In the physical nondegenerate domain, write
`b = (exp q + 1)/(exp q - 1)`, `r = -dv/(v A)`, `s = H'/(B A)`, `h = H''/(B A²)`,
where `A = -dq` and `B = -H`. Then the normalized third compensation is

`(b²-1) * (12*(r-b/2)*(s-b/2)-1) + 3*h*((6+4*b)*r-2*(b²-1))`.

The first two channels have a hyperbolic sign boundary. The last channel supplies an explicit
critical-curvature reserve. Every identity below is unconditional: one extra denominator
factor makes the cleared identities valid also at degenerate real-field division by zero.
The theta-source inequality placing actual curvature above the critical reserve remains open.
No numerical experiment, finite sign census, or numerical oracle is used in these proofs.
-/

namespace RHTower
noncomputable section

/-- Scalar form of the complete affine C5 third compensation. -/
def c5AffineScalarThird (e v dv dq H H1 H2 : ℝ) : ℝ :=
  let R0 := 1 / (e - 1)
  let R1 := (-e) * dq / (e - 1)^(2 : ℕ)
  let R2 := e * (e + 1) * dq^(2 : ℕ) / (e - 1)^(3 : ℕ)
  let R3 := (-e) * (e^(2 : ℕ) + 4*e + 1) * dq^(3 : ℕ) / (e - 1)^(4 : ℕ)
  show ℝ from -(8 * (3*dv*R2 + v*R3) * H +
    3 * (8*(2*dv*R1 + v*R2)) * H1 +
    3 * (10*dv + 8*(dv*R0 + v*R1)) * H2)

/-- Exact incidence with the existing affine likelihood-homotopy compensation. -/
theorem c5AffineScalarThird_eq_compensationThree
    (d : C5LikelihoodAffineData) (l : ℝ) :
    c5AffineScalarThird (Real.exp (d.action l)) (d.t*d.jetOne l)
      (d.t*d.da) d.dq (d.velocityCenter l) (d.velocityCenterOne l) d.velocityCenterTwo =
      d.compensationThree l := by
  rfl

/-- Denominator-cleared complete reserve in exponential coordinates. -/
def c5BoseReservePolynomial (e r s h : ℝ) : ℝ :=
  4*e*(12*((e-1)*r-(e+1)/2)*((e-1)*s-(e+1)/2)-(e-1)^(2 : ℕ)) +
    3*h*(e-1)^(2 : ℕ)*(r*(10*(e-1)^(2 : ℕ)+8*(e-1))-8*e)

/-- Complete compensation has this homogeneous reserve, including every signed channel. -/
theorem c5AffineScalarThird_cleared_reserve (e v A B r s h : ℝ) :
    (e-1)^(5 : ℕ) * c5AffineScalarThird e v (-v*A*r) (-A) (-B) (B*A*s) (B*A^(2 : ℕ)*h) =
      v*B*A^(3 : ℕ)*(e-1)*c5BoseReservePolynomial e r s h := by
  by_cases hz : e-1=0
  · simp [hz]
  · unfold c5AffineScalarThird c5BoseReservePolynomial
    dsimp only
    field_simp
    ring

/-- Normalized negative first Bose derivative: `W' = -v*A*lowerSlope`. -/
def c5BoseLowerSlope (b r : ℝ) : ℝ := (6+4*b)*r-2*(b^(2 : ℕ)-1)

/-- Mixed hyperbolic budget plus the exact lower-curvature contribution. -/
def c5BoseHyperbolicBudget (b r s h : ℝ) : ℝ :=
  (b^(2 : ℕ)-1)*(12*(r-b/2)*(s-b/2)-1)+3*h*c5BoseLowerSlope b r

/-- The hyperbolic coordinates represent the same complete reserve polynomial. -/
theorem c5BoseHyperbolicBudget_cleared (e r s h : ℝ) :
    (e-1)^(5 : ℕ)*c5BoseHyperbolicBudget ((e+1)/(e-1)) r s h =
      (e-1)*c5BoseReservePolynomial e r s h := by
  by_cases hz : e-1=0
  · simp [hz]
  · unfold c5BoseHyperbolicBudget c5BoseLowerSlope c5BoseReservePolynomial
    field_simp
    ring

/-- Exact curvature threshold when the normalized negative Bose slope is positive. -/
def c5BoseCriticalCurvature (b r s : ℝ) : ℝ :=
  (b^(2 : ℕ)-1)*(1-12*(r-b/2)*(s-b/2))/(3*c5BoseLowerSlope b r)

/-- Sharp reserve identity: shifting from the critical curvature leaves only the prescribed
reserve times a square. This does not assert a sign for the actual source reserve. -/
theorem c5BoseHyperbolicBudget_shifted_reserve (b r s z : ℝ) :
    c5BoseLowerSlope b r *
      c5BoseHyperbolicBudget b r s (c5BoseCriticalCurvature b r s + z) =
      3*z*(c5BoseLowerSlope b r)^(2 : ℕ) := by
  by_cases hz : c5BoseLowerSlope b r=0
  · simp [hz]
  · unfold c5BoseHyperbolicBudget c5BoseCriticalCurvature
    field_simp
    ring

/-- Curvature coefficient after retaining the mixed source coordinate
`k = s-r+h/(2*r)`. Its sign has a square decomposition. -/
def c5BoseCurvatureCoefficient (b r : ℝ) : ℝ :=
  (6+4*b)*r^(2 : ℕ)-4*(b^(2 : ℕ)-1)*r+b*(b^(2 : ℕ)-1)

/-- Exact square decomposition of the retained-coordinate curvature coefficient. -/
theorem c5BoseCurvatureCoefficient_square_identity (b r : ℝ) :
    (6+4*b)*c5BoseCurvatureCoefficient b r =
      (c5BoseLowerSlope b r)^(2 : ℕ)+(b^(2 : ℕ)-1)*(6*b+4) := by
  unfold c5BoseCurvatureCoefficient c5BoseLowerSlope
  ring

/-- Division-free decomposition retaining the exact source-coordinate incidence residual.
Dropping that residual without proving its vanishing would change the budget. -/
theorem c5BoseHyperbolicBudget_curvature_incidence (b r s h k : ℝ) :
    r*c5BoseHyperbolicBudget b r s h =
      r*c5BoseHyperbolicBudget b r (r+k) 0 +
      6*(b^(2 : ℕ)-1)*(r-b/2)*(2*r*(s-r-k)+h) +
      3*h*c5BoseCurvatureCoefficient b r := by
  unfold c5BoseHyperbolicBudget c5BoseLowerSlope c5BoseCurvatureCoefficient
  ring

/-- Cleared fixed-coordinate curvature law, including the degenerate case `r=0`.
It gives a positive curvature coefficient for `b>1,r>0`; it does not claim the actual
theta homotopy keeps the other coordinates fixed. -/
theorem c5BoseHyperbolicBudget_curvature_cleared (b r h k : ℝ) :
    r^(2 : ℕ)*c5BoseHyperbolicBudget b r (r+k-h/(2*r)) h =
      r^(2 : ℕ)*c5BoseHyperbolicBudget b r (r+k) 0 +
      3*h*r*c5BoseCurvatureCoefficient b r := by
  by_cases hz : r=0
  · simp [hz]
  · unfold c5BoseHyperbolicBudget c5BoseLowerSlope c5BoseCurvatureCoefficient
    field_simp
    ring

/-- Unconditional nonnegative-coordinate chart for the coefficient: `b=1+x²`.
This is an algebraic sign theorem, not a sign assumption about the theta source. -/
theorem c5BoseCurvatureCoefficient_positive_chart (x r : ℝ) :
    0 ≤ c5BoseCurvatureCoefficient (1+x^(2 : ℕ)) r := by
  have hx := sq_nonneg x
  have hb : 0 ≤ (1+x^(2 : ℕ))^(2 : ℕ)-1 := by nlinarith [sq_nonneg (x^(2 : ℕ))]
  have hs := sq_nonneg (c5BoseLowerSlope (1+x^(2 : ℕ)) r)
  have hp : 0 ≤ ((1+x^(2 : ℕ))^(2 : ℕ)-1)*(6*(1+x^(2 : ℕ))+4) :=
    mul_nonneg hb (by positivity)
  have hi := c5BoseCurvatureCoefficient_square_identity (1+x^(2 : ℕ)) r
  nlinarith

end
end RHTower

import GaloisForLFunctions.HTGeometry.KerrNewmanHorizonAlgebra

/-!
# Kerr--Newman stationary-limit algebra

The numerator of the Boyer--Lindquist `g_tt` coefficient is the stationary-limit
polynomial.  Its discriminant differs from the horizon discriminant by the
nonnegative rotational term `a^2 sin^2(theta)`.  This gives an exact algebraic
comparison between the stationary-limit and horizon boundaries without dividing
at coordinate-singular points.

This does not establish the global causal theory of the ergoregion.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The denominator-free stationary-limit polynomial of the Kerr--Newman `t--t` coefficient. -/
def kerrNewmanStationaryLimitPolynomial
    (mass spin charge radius polar : ℝ) : ℝ :=
  kerrNewmanDelta mass spin charge radius - spin ^ 2 * Real.sin polar ^ 2

/-- The stationary-limit polynomial is `Sigma - 2 M r + Q^2`. -/
theorem kerrNewmanStationaryLimitPolynomial_eq_sigma
    (mass spin charge radius polar : ℝ) :
    kerrNewmanStationaryLimitPolynomial mass spin charge radius polar =
      kerrNewmanSigma spin radius polar - 2 * mass * radius + charge ^ 2 := by
  unfold kerrNewmanStationaryLimitPolynomial
  have htrig : Real.sin polar ^ 2 = 1 - Real.cos polar ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq polar]
  rw [htrig]
  simp only [kerrNewmanDelta, kerrNewmanSigma]
  ring

/-- The stationary-limit polynomial is the denominator-cleared numerator of the Kerr--Newman
`g_tt` coefficient.  Squaring `Sigma` keeps this identity valid at the totalized coordinate
singular locus. -/
theorem kerrNewmanKillingBlock_tt_cleared_stationaryLimitPolynomial
    (mass spin charge radius polar : ℝ) :
    kerrNewmanSigma spin radius polar ^ 2 *
        kerrNewmanKillingBlock mass spin charge radius polar 0 0 =
      -kerrNewmanSigma spin radius polar *
        kerrNewmanStationaryLimitPolynomial mass spin charge radius polar := by
  change kerrNewmanSigma spin radius polar ^ 2 *
      (-(kerrNewmanDelta mass spin charge radius - spin ^ 2 * Real.sin polar ^ 2) /
        kerrNewmanSigma spin radius polar) =
    -kerrNewmanSigma spin radius polar *
      (kerrNewmanDelta mass spin charge radius - spin ^ 2 * Real.sin polar ^ 2)
  by_cases hSigma : kerrNewmanSigma spin radius polar = 0
  · simp [hSigma]
  · field_simp [hSigma]

/-- Completing the square isolates the stationary-limit discriminant. -/
theorem kerrNewmanStationaryLimitPolynomial_completeSquare
    (mass spin charge radius polar : ℝ) :
    kerrNewmanStationaryLimitPolynomial mass spin charge radius polar =
      (radius - mass) ^ 2 - (mass ^ 2 - charge ^ 2 - spin ^ 2 * Real.cos polar ^ 2) := by
  rw [kerrNewmanStationaryLimitPolynomial_eq_sigma]
  simp only [kerrNewmanSigma]
  ring

/-- At the mass-centered radius, the stationary-limit polynomial vanishes exactly on its angular
discriminant boundary. -/
theorem kerrNewmanStationaryLimitPolynomial_at_mass_zero_iff
    (mass spin charge polar : ℝ) :
    kerrNewmanStationaryLimitPolynomial mass spin charge mass polar = 0 ↔
      mass ^ 2 = charge ^ 2 + spin ^ 2 * Real.cos polar ^ 2 := by
  rw [kerrNewmanStationaryLimitPolynomial_completeSquare]
  constructor <;> intro h <;> nlinarith

/-- On the rotation axis, the stationary-limit polynomial is exactly the horizon polynomial. -/
theorem kerrNewmanStationaryLimitPolynomial_axis
    (mass spin charge radius : ℝ) :
    kerrNewmanStationaryLimitPolynomial mass spin charge radius 0 =
      kerrNewmanDelta mass spin charge radius := by
  simp [kerrNewmanStationaryLimitPolynomial]

/-- Therefore the stationary-limit and horizon boundaries agree at the mass-centered axis. -/
theorem kerrNewmanStationaryLimitPolynomial_axis_at_mass_zero_iff_extremal
    (mass spin charge : ℝ) :
    kerrNewmanStationaryLimitPolynomial mass spin charge mass 0 = 0 ↔
      mass ^ 2 = spin ^ 2 + charge ^ 2 := by
  rw [kerrNewmanStationaryLimitPolynomial_axis,
    kerrNewmanDelta_at_mass_zero_iff_extremal]

/-- The stationary-limit discriminant exceeds the horizon discriminant by the rotational angular
term. -/
theorem kerrNewmanStationaryLimit_discriminant_eq_horizonDiscriminant_add
    (mass spin charge polar : ℝ) :
    mass ^ 2 - charge ^ 2 - spin ^ 2 * Real.cos polar ^ 2 =
      (mass ^ 2 - spin ^ 2 - charge ^ 2) + spin ^ 2 * Real.sin polar ^ 2 := by
  have htrig : Real.sin polar ^ 2 = 1 - Real.cos polar ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq polar]
  rw [htrig]
  ring

/-- Rotation can only enlarge the stationary-limit discriminant relative to the horizon
discriminant. -/
theorem kerrNewmanStationaryLimit_discriminant_ge_horizonDiscriminant
    (mass spin charge polar : ℝ) :
    mass ^ 2 - spin ^ 2 - charge ^ 2 ≤
      mass ^ 2 - charge ^ 2 - spin ^ 2 * Real.cos polar ^ 2 := by
  rw [kerrNewmanStationaryLimit_discriminant_eq_horizonDiscriminant_add]
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg spin) (sq_nonneg (Real.sin polar)))

end

end GaloisForLFunctions.HTGeometry

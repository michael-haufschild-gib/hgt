import GaloisForLFunctions.RHTower.PolynomialMomentFock

/-!
# Polynomial Fock radial geometry

This file records the exact radial slope, radial curvature, and planar Laplacian-density formulas
for the polynomial Fock potential `(1 + r²)^(m/2)`.  It also proves uniform two-sided comparison of
the Laplacian density with its adapted power model.  These estimates are shared input for the
doubling, kernel-localization, Carleson, and Schatten arguments.
-/

open Filter Topology Set MeasureTheory
open scoped Real

namespace RHTower

noncomputable section

/-- Algebraic radial-slope formula for the polynomial Fock potential. -/
def polynomialFockRadialSlope (m r : ℝ) : ℝ :=
  m * r * (1 + r ^ 2) ^ (m / 2 - 1)

/-- Algebraic radial-curvature formula for the polynomial Fock potential. -/
def polynomialFockRadialCurvature (m r : ℝ) : ℝ :=
  m * (1 + r ^ 2) ^ (m / 2 - 2) * (1 + (m - 1) * r ^ 2)

/-- Exact planar Laplacian-density formula for the radial polynomial Fock potential. -/
def polynomialFockLaplacianDensity (m r : ℝ) : ℝ :=
  m * (1 + r ^ 2) ^ (m / 2 - 2) * (2 + m * r ^ 2)

/-- Exact reciprocal-square-root radius attached to the polynomial Fock Laplacian density. -/
def polynomialFockAdaptedRadius (m r : ℝ) : ℝ :=
  (Real.sqrt (polynomialFockLaplacianDensity m r))⁻¹

/-- Radial curvature is strictly positive throughout the convex range `m ≥ 1`. -/
theorem polynomialFockRadialCurvature_pos
    {m r : ℝ} (hm : 1 ≤ m) :
    0 < polynomialFockRadialCurvature m r := by
  unfold polynomialFockRadialCurvature
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hlast : 0 < 1 + (m - 1) * r ^ 2 := by positivity
  positivity

/-- Away from the origin, the planar radial Laplacian is radial curvature plus slope divided by
radius. -/
theorem polynomialFockLaplacianDensity_eq
    (m r : ℝ) (hr : r ≠ 0) :
    polynomialFockRadialCurvature m r +
        polynomialFockRadialSlope m r / r =
      polynomialFockLaplacianDensity m r := by
  unfold polynomialFockRadialCurvature polynomialFockRadialSlope
    polynomialFockLaplacianDensity
  rw [show m / 2 - 1 = (m / 2 - 2) + 1 by ring, Real.rpow_add (by positivity),
    Real.rpow_one]
  field_simp [hr]
  ring

/-- The polynomial Fock Laplacian density is strictly positive for every positive degree. -/
theorem polynomialFockLaplacianDensity_pos
    {m r : ℝ} (hm : 0 < m) :
    0 < polynomialFockLaplacianDensity m r := by
  unfold polynomialFockLaplacianDensity
  positivity

/-- Lower comparison with the exact adapted density model `(1+r²)^(m/2-1)`. -/
theorem polynomialFockLaplacianDensity_lower
    {m r : ℝ} (hm : 2 ≤ m) :
    2 * m * (1 + r ^ 2) ^ (m / 2 - 1) ≤
      polynomialFockLaplacianDensity m r := by
  have hbase : 0 < 1 + r ^ 2 := by positivity
  have hfactor :
      (1 + r ^ 2) ^ (m / 2 - 1) =
        (1 + r ^ 2) ^ (m / 2 - 2) * (1 + r ^ 2) := by
    rw [show m / 2 - 1 = (m / 2 - 2) + 1 by ring,
      Real.rpow_add hbase, Real.rpow_one]
  rw [hfactor]
  unfold polynomialFockLaplacianDensity
  have hp : 0 ≤ m * (1 + r ^ 2) ^ (m / 2 - 2) := by positivity
  have hbracket : 2 * (1 + r ^ 2) ≤ 2 + m * r ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sq_nonneg r)]
  calc
    2 * m * ((1 + r ^ 2) ^ (m / 2 - 2) * (1 + r ^ 2)) =
        (m * (1 + r ^ 2) ^ (m / 2 - 2)) * (2 * (1 + r ^ 2)) := by ring
    _ ≤ (m * (1 + r ^ 2) ^ (m / 2 - 2)) * (2 + m * r ^ 2) :=
      mul_le_mul_of_nonneg_left hbracket hp

/-- Upper comparison with the exact adapted density model `(1+r²)^(m/2-1)`. -/
theorem polynomialFockLaplacianDensity_upper
    {m r : ℝ} (hm : 2 ≤ m) :
    polynomialFockLaplacianDensity m r ≤
      m ^ 2 * (1 + r ^ 2) ^ (m / 2 - 1) := by
  have hbase : 0 < 1 + r ^ 2 := by positivity
  have hfactor :
      (1 + r ^ 2) ^ (m / 2 - 1) =
        (1 + r ^ 2) ^ (m / 2 - 2) * (1 + r ^ 2) := by
    rw [show m / 2 - 1 = (m / 2 - 2) + 1 by ring,
      Real.rpow_add hbase, Real.rpow_one]
  rw [hfactor]
  unfold polynomialFockLaplacianDensity
  have hp : 0 ≤ m * (1 + r ^ 2) ^ (m / 2 - 2) := by positivity
  have hbracket : 2 + m * r ^ 2 ≤ m * (1 + r ^ 2) := by linarith
  calc
    m * (1 + r ^ 2) ^ (m / 2 - 2) * (2 + m * r ^ 2) ≤
        (m * (1 + r ^ 2) ^ (m / 2 - 2)) * (m * (1 + r ^ 2)) :=
      mul_le_mul_of_nonneg_left hbracket hp
    _ = m ^ 2 * ((1 + r ^ 2) ^ (m / 2 - 2) * (1 + r ^ 2)) := by ring

/-- The exact adapted radius is positive in every positive degree. -/
theorem polynomialFockAdaptedRadius_pos
    {m r : ℝ} (hm : 0 < m) :
    0 < polynomialFockAdaptedRadius m r := by
  unfold polynomialFockAdaptedRadius
  exact inv_pos.mpr (Real.sqrt_pos.2 (polynomialFockLaplacianDensity_pos hm))

/-- Upper reciprocal-square-root comparison for the exact adapted radius. -/
theorem polynomialFockAdaptedRadius_upper
    {m r : ℝ} (hm : 2 ≤ m) :
    polynomialFockAdaptedRadius m r ≤
      (Real.sqrt (2 * m * (1 + r ^ 2) ^ (m / 2 - 1)))⁻¹ := by
  have hm0 : 0 < m := by linarith
  have hlowerPos : 0 < 2 * m * (1 + r ^ 2) ^ (m / 2 - 1) := by positivity
  have hdensityPos := polynomialFockLaplacianDensity_pos (m := m) (r := r) hm0
  unfold polynomialFockAdaptedRadius
  rw [inv_le_inv₀ (Real.sqrt_pos.2 hdensityPos) (Real.sqrt_pos.2 hlowerPos)]
  exact Real.sqrt_le_sqrt (polynomialFockLaplacianDensity_lower hm)

/-- Lower reciprocal-square-root comparison for the exact adapted radius. -/
theorem polynomialFockAdaptedRadius_lower
    {m r : ℝ} (hm : 2 ≤ m) :
    (Real.sqrt (m ^ 2 * (1 + r ^ 2) ^ (m / 2 - 1)))⁻¹ ≤
      polynomialFockAdaptedRadius m r := by
  have hm0 : 0 < m := by linarith
  have hupperPos : 0 < m ^ 2 * (1 + r ^ 2) ^ (m / 2 - 1) := by positivity
  have hdensityPos := polynomialFockLaplacianDensity_pos (m := m) (r := r) hm0
  unfold polynomialFockAdaptedRadius
  rw [inv_le_inv₀ (Real.sqrt_pos.2 hupperPos) (Real.sqrt_pos.2 hdensityPos)]
  exact Real.sqrt_le_sqrt (polynomialFockLaplacianDensity_upper hm)

/-! ## Global tangent geometry -/

/-- Tangent-line lower bound for a real power of exponent at least one. -/
theorem rpow_tangent_lower {A B α : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hα : 1 ≤ α) :
    A ^ α + α * A ^ (α - 1) * (B - A) ≤ B ^ α := by
  have hα0 : 0 < α := zero_lt_one.trans_le hα
  let t : ℝ := B / A
  have ht : 0 ≤ t := div_nonneg hB hA.le
  have htα : 0 ≤ t ^ α := Real.rpow_nonneg ht α
  have hs0 : 0 ≤ 1 / α := by positivity
  have hs1 : 1 / α ≤ 1 := (div_le_one hα0).2 hα
  have hbern : (t ^ α) ^ (1 / α) ≤ 1 + (1 / α) * (t ^ α - 1) := by
    have h := Real.geom_mean_le_arith_mean2_weighted hs0 (by linarith : 0 ≤ 1 - 1 / α)
      htα zero_le_one (by ring)
    rw [Real.one_rpow, mul_one, mul_one] at h
    linarith
  have hroot : (t ^ α) ^ (1 / α) = t := by
    rw [← Real.rpow_mul ht]
    have : α * (1 / α) = 1 := by field_simp
    rw [this, Real.rpow_one]
  rw [hroot] at hbern
  have hinv : α * (1 / α) = 1 := by field_simp
  have hbern' : 1 + α * (t - 1) ≤ t ^ α := by
    nlinarith
  have hBA : B = A * t := by
    dsimp [t]
    field_simp
  have hsplit : A ^ α = A ^ (α - 1) * A := by
    symm
    calc
      A ^ (α - 1) * A = A ^ (α - 1) * A ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = A ^ ((α - 1) + 1) := (Real.rpow_add hA (α - 1) 1).symm
      _ = A ^ α := by ring_nf
  calc
    A ^ α + α * A ^ (α - 1) * (B - A) =
        A ^ α * (1 + α * (t - 1)) := by rw [hBA, hsplit]; ring
    _ ≤ A ^ α * t ^ α :=
      mul_le_mul_of_nonneg_left hbern' (Real.rpow_nonneg hA.le α)
    _ = (A * t) ^ α := by rw [Real.mul_rpow hA.le ht]
    _ = B ^ α := by rw [← hBA]

/-- The tangent gauge of the polynomial Fock potential leaves a globally coercive quadratic
Bregman remainder.  This is the source of the sharp adapted Gaussian scale. -/
theorem polynomialFockPotential_bregman_lower
    {m x : ℝ} (hm : 2 ≤ m) (z : ℂ) :
    polynomialFockPotential m x +
        polynomialFockRadialSlope m x * (z.re - x) +
        (m / 2) * (1 + x ^ 2) ^ (m / 2 - 1) * ‖z - (x : ℂ)‖ ^ 2 ≤
      polynomialFockPotential m ‖z‖ := by
  have hA : 0 < 1 + x ^ 2 := by positivity
  have hB : 0 ≤ 1 + ‖z‖ ^ 2 := by positivity
  have hα : 1 ≤ m / 2 := by linarith
  have ht := rpow_tangent_lower hA hB hα
  unfold polynomialFockPotential polynomialFockRadialSlope at *
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hsubnorm : ‖z - (x : ℂ)‖ ^ 2 = (z.re - x) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [hnorm] at ht
  rw [hsubnorm]
  have hid :
      (m / 2) * (1 + x ^ 2) ^ (m / 2 - 1) *
          (1 + (z.re ^ 2 + z.im ^ 2) - (1 + x ^ 2)) =
        m * x * (1 + x ^ 2) ^ (m / 2 - 1) * (z.re - x) +
          (m / 2) * (1 + x ^ 2) ^ (m / 2 - 1) *
            ((z.re - x) ^ 2 + z.im ^ 2) := by
    ring
  rw [hid] at ht
  simpa only [hnorm, add_assoc] using ht

end

end RHTower

import GaloisForLFunctions.RHTower.RoutePComplexPointedFourUnitPolarization

/-!
# Route P: full Hardy-half-plane polarization

The literal complex full-Euler column is square summable on its sharp source domain
`Re u > -1/2`, not merely on the sufficient inward chart `Re u >= 0`.  On this full domain the
projective nodes `R * a - 1/2` are admitted for every positive scale and depth.  Their finite-sigma
Euler overlaps converge, after the fixed projective scaling, to the universal Route-P Hardy
kernel.  Thus projective scale blow-up was a chart artifact rather than a source obstruction.
-/

open Complex Filter Set
open scoped BigOperators Topology ComplexOrder

namespace RHTower

noncomputable section

/-- Real exponent controlling the squared norm of a complex-damped full-Euler column. -/
def eulerPositiveComplexHardySquareExponent (sigma : ℝ) (u : ℂ) : ℝ :=
  sigma + 2 * u.re * (sigma - 1)

theorem one_lt_eulerPositiveComplexHardySquareExponent
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : -1 / 2 < u.re) :
    1 < eulerPositiveComplexHardySquareExponent sigma u := by
  unfold eulerPositiveComplexHardySquareExponent
  nlinarith [mul_pos (by nlinarith : 0 < 1 + 2 * u.re) (sub_pos.mpr hsigma)]

theorem one_lt_eulerPositiveComplexBoundaryParameter_re_of_neg_half_lt
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : -1 / 2 < u.re) :
    1 < (eulerPositiveComplexBoundaryParameter sigma u).re := by
  simp only [eulerPositiveComplexBoundaryParameter, add_re, mul_re,
    ofReal_re, ofReal_im, mul_zero, sub_zero]
  nlinarith [mul_pos (by nlinarith : 0 < 1 + u.re) (sub_pos.mpr hsigma)]

private theorem norm_sq_eulerPositiveCriticalComplexDampedStateWeight_eq_mass
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (n : ℕ+) :
    ‖eulerPositiveCriticalComplexDampedStateWeight sigma u n‖ ^ 2 =
      eulerPositiveMass (eulerPositiveComplexHardySquareExponent sigma u) n /
        eulerPositiveTotal sigma := by
  rw [norm_eulerPositiveCriticalComplexDampedStateWeight,
    eulerPositiveCriticalDampedStateWeight, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    eulerPositiveCriticalDamping,
    abs_of_pos (Real.exp_pos _), mul_pow,
    norm_eulerPositiveStateWeight_sq hsigma,
    eulerPositiveProbability,
    eulerPositiveMass, eulerPositiveMass]
  have hnpos : (0 : ℝ) < (n : ℕ) := by positivity
  have hpow :
      Real.exp (-(u.re * (sigma - 1) * Real.log (n : ℕ))) =
        ((n : ℕ) : ℝ) ^ (-(u.re * (sigma - 1))) := by
    rw [Real.rpow_def_of_pos hnpos]
    congr 1
    ring
  rw [hpow]
  rw [← Real.rpow_natCast (((n : ℕ) : ℝ) ^ (-(u.re * (sigma - 1)))) 2,
    ← Real.rpow_mul hnpos.le,
    ← Real.rpow_add hnpos]
  congr 2
  unfold eulerPositiveComplexHardySquareExponent
  ring

private theorem summable_norm_sq_eulerPositiveCriticalComplexHardyStateWeight
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : -1 / 2 < u.re) :
    Summable (fun n : ℕ+ =>
      ‖eulerPositiveCriticalComplexDampedStateWeight sigma u n‖ ^ 2) := by
  have hmass := summable_eulerPositiveMass
    (one_lt_eulerPositiveComplexHardySquareExponent hsigma hu)
  exact (hmass.div_const (eulerPositiveTotal sigma)).congr fun n =>
    (norm_sq_eulerPositiveCriticalComplexDampedStateWeight_eq_mass hsigma n).symm

/-- Actual full-Euler column on the sharp Hardy source half-plane `Re u > -1/2`. -/
def eulerPositiveCriticalComplexHardyStateLp
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : -1 / 2 < u.re) :
    EulerPositiveL2 :=
  ⟨eulerPositiveCriticalComplexDampedStateWeight sigma u,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_eulerPositiveCriticalComplexHardyStateWeight hsigma hu)⟩

end

end RHTower

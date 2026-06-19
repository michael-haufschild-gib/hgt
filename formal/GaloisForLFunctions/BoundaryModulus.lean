import GaloisForLFunctions.Core

/-!
# Boundary-radius normalization (Tier A scalar skeleton)

`dynamics-continent-lyapunov-avila-morales-ramis.md` §7 flags a formalizable floor behind the
boundary-modulus normalization: if a scalar coordinate has boundary radius `p^(-1/2)`, multiplying
by the inverse radius puts it on the unit circle.

This file proves exactly that scalar statement, and the diagonal specialization for `p^{-s}`. It
does not formalize Lyapunov exponents, Avila theory, Morales-Ramis theory, or the DMR consequences
in the draft.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The boundary radius attached to a positive real base `p`. -/
def boundaryRadius (p : ℝ) : ℝ := p ^ (-(1 / 2 : ℝ))

/-- Normalize a scalar by the inverse boundary radius. -/
def boundaryUnitNormalize (p : ℝ) (x : ℂ) : ℂ := (boundaryRadius p)⁻¹ • x

/-- The boundary radius is positive for a positive base. -/
lemma boundaryRadius_pos {p : ℝ} (hp : 0 < p) : 0 < boundaryRadius p := by
  exact Real.rpow_pos_of_pos hp _

/-- Scaling a complex scalar by the inverse of a positive radius has unit norm exactly when the
original scalar has that radius. -/
theorem norm_inv_smul_eq_one_iff {r : ℝ} (hr : 0 < r) (x : ℂ) :
    ‖(r⁻¹ : ℝ) • x‖ = 1 ↔ ‖x‖ = r := by
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  have hrne : r ≠ 0 := ne_of_gt hr
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hri]
  constructor
  · intro h
    have hm : r * (r⁻¹ * ‖x‖) = r := by
      simpa using congrArg (fun y : ℝ => r * y) h
    rw [← mul_assoc, mul_inv_cancel₀ hrne, one_mul] at hm
    exact hm
  · intro h
    rw [h, inv_mul_cancel₀ hrne]

/-- Boundary-radius normalization puts a scalar on the unit circle exactly when it lies on the
boundary circle of radius `p^(-1/2)`. -/
theorem boundaryUnitNormalize_norm_eq_one_iff {p : ℝ} (hp : 0 < p) (x : ℂ) :
    ‖boundaryUnitNormalize p x‖ = 1 ↔ ‖x‖ = boundaryRadius p := by
  exact norm_inv_smul_eq_one_iff (boundaryRadius_pos hp) x

/-- On the diagonal coordinate `p^{-s}`, boundary-radius normalization is unitary exactly on
`Re(s)=1/2`. -/
theorem diagonalBoundary_unit_norm_iff (p : ℝ) (hp : 1 < p) (s : ℂ) :
    ‖boundaryUnitNormalize p ((p : ℂ) ^ (-s))‖ = 1 ↔ s.re = 1 / 2 := by
  rw [boundaryUnitNormalize_norm_eq_one_iff (zero_lt_one.trans hp), boundaryRadius]
  exact norm_cpow_eq_critical_iff p hp s

end

end GaloisForLFunctions

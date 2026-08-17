import GaloisForLFunctions.HTGeometry.RationalAffineTransport
import GaloisForLFunctions.HTGeometry.QuadraticNoInvariantDifferential

/-!
# `z ↦ (z − 1)²` carries no rational affine connection

The map has the single critical point `1`, with critical value `0`, so the critical obstruction says
that a connection must have a pole at `1` or at `0`.

The critical value is not the critical point, so a pole there travels forward to a pole at `1`; and
`2` is a preimage of `1` which is neither periodic nor postcritical, so it carries an injective
critical-free backward orbit along which a pole at `1` produces infinitely many poles.  A nonzero
rational function has only finitely many zeros and poles, so no connection exists; and the zero
function is not one because the curvature term `2` survives.

Unlike `z ↦ z² + 1`, this map is postcritically finite — the critical orbit is the two-cycle
`1 ↦ 0 ↦ 1` — so the forward orbit of the critical value is useless here and the whole argument runs
backward.  This is the obstruction that closes the fixed branch of the orbifold-tail trichotomy at
jet order two for `z ↦ (z − 1)²`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

theorem quadTwo_natDegree_ne_zero : quadTwo.natDegree ≠ 0 := by
  rw [natDegree_quadTwo]; norm_num

/-- `z ↦ (z − 1)²` is not a constant. -/
theorem quadTwo_not_isConst :
    ¬ ∃ c : ℂ, (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo) = RatFunc.C c :=
  not_isConst_algebraMap quadTwo_natDegree_ne_zero

theorem derivative_quadTwo_eval (z : ℂ) : (derivative quadTwo).eval z = 2 * (z - 1) := by
  rw [derivative_quadTwo]
  simp

theorem quadTwo_critical : (derivative quadTwo).eval 1 = 0 := by
  rw [derivative_quadTwo_eval]; ring

theorem quadTwo_eval_one : quadTwo.eval (1 : ℂ) = 0 := by rw [quadTwo_eval]; ring

theorem quadTwo_eval_zero : quadTwo.eval (0 : ℂ) = 1 := by rw [quadTwo_eval]; ring

theorem quadTwo_eval_two : quadTwo.eval (2 : ℂ) = 1 := by rw [quadTwo_eval]; ring

/-! ## No pole at either point of the critical pair -/

/-- The critical point carries no pole: `2` is a preimage of it carrying an injective critical-free
backward orbit. -/
theorem quadTwo_affine_no_pole_at_one {a : RatFunc ℂ} (ha : a ≠ 0)
    (heq : IsAffineConnection quadTwo quadTwo_not_isConst a) : 0 ≤ ratOrder a 1 := by
  by_contra hpole
  rw [not_le] at hpole
  have htwo : (derivative quadTwo).eval 2 ≠ 0 := by
    rw [derivative_quadTwo_eval]
    norm_num
  have htwopole : ratOrder a 2 < 0 :=
    affine_pole_backward quadTwo_natDegree_ne_zero ha heq htwo (by rw [quadTwo_eval_two]; exact hpole)
  obtain ⟨b, hb0, hstep, hinj, hcrit⟩ :=
    exists_backward_orbit quadTwo_natDegree_ne_zero aperiodic_quadTwo_two postcritical_quadTwo_ne_two
  exact no_pole_of_backward_orbit quadTwo_natDegree_ne_zero ha heq hstep hcrit hinj
    (by rw [hb0]; exact htwopole)

/-- The critical value carries no pole: it is not the critical point, so a pole there travels
forward to the critical point. -/
theorem quadTwo_affine_no_pole_at_zero {a : RatFunc ℂ} (ha : a ≠ 0)
    (heq : IsAffineConnection quadTwo quadTwo_not_isConst a) : 0 ≤ ratOrder a 0 := by
  by_contra hpole
  rw [not_le] at hpole
  have hzero : (derivative quadTwo).eval 0 ≠ 0 := by
    rw [derivative_quadTwo_eval]
    norm_num
  have hone := affine_pole_forward quadTwo_natDegree_ne_zero ha heq hzero hpole
  rw [quadTwo_eval_zero] at hone
  exact absurd hone (not_lt.mpr (quadTwo_affine_no_pole_at_one ha heq))

/-- **`z ↦ (z − 1)²` carries no rational affine connection.** -/
theorem quadTwo_no_affine_connection (a : RatFunc ℂ) :
    ¬ IsAffineConnection quadTwo quadTwo_not_isConst a := by
  intro heq
  rcases eq_or_ne a 0 with rfl | ha
  · have hcurv := derivative_derivative_eq_zero_of_isAffineConnection_zero heq
    rw [derivative_quadTwo, derivative_mul, derivative_C, derivative_sub, derivative_X,
      derivative_C, sub_zero, zero_mul, mul_one, zero_add] at hcurv
    have hc := congrArg (fun p => Polynomial.coeff p 0) hcurv
    simp at hc
  · exact no_affine_connection_regular_at_critical quadTwo_natDegree_ne_zero ha heq quadTwo_critical
      (quadTwo_affine_no_pole_at_one ha heq)
      (by rw [quadTwo_eval_one]; exact quadTwo_affine_no_pole_at_zero ha heq)

end GaloisForLFunctions.HTGeometry

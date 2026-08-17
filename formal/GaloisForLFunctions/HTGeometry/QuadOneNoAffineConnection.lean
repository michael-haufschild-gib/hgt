import GaloisForLFunctions.HTGeometry.RationalAffineTransport
import GaloisForLFunctions.HTGeometry.QuadraticNoInvariantDifferential

/-!
# `z ↦ z² + 1` carries no rational affine connection

The map has the single critical point `0`, with critical value `1`, so the critical obstruction says
that a connection must have a pole at `0` or at `1`.

Both are fatal.  The critical value has the strictly increasing forward orbit `1, 2, 5, 26, …`,
which never returns to the critical point, so a pole there produces infinitely many poles.  The
imaginary unit is a preimage of the critical point which is neither periodic nor postcritical, so it
carries an injective critical-free backward orbit, and a pole at the critical point produces
infinitely many poles along it.  A nonzero rational function has only finitely many zeros and poles,
so no connection exists; and the zero function is not one because the curvature term `2` survives.

This is the obstruction that closes the fixed branch of the orbifold-tail trichotomy at jet order
two for `z ↦ z² + 1`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

theorem quadOne_natDegree_ne_zero : quadOne.natDegree ≠ 0 := by
  rw [natDegree_quadOne]; norm_num

/-- `z ↦ z² + 1` is not a constant. -/
theorem quadOne_not_isConst :
    ¬ ∃ c : ℂ, (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne) = RatFunc.C c :=
  not_isConst_algebraMap quadOne_natDegree_ne_zero

theorem derivative_quadOne_eval (z : ℂ) : (derivative quadOne).eval z = 2 * z := by
  rw [derivative_quadOne]
  simp

theorem quadOne_critical : (derivative quadOne).eval 0 = 0 := by
  rw [derivative_quadOne_eval]; ring

theorem quadOne_eval_zero : quadOne.eval (0 : ℂ) = 1 := by rw [quadOne_eval]; ring

/-! ## The forward orbit of the critical value -/

theorem quadOneOrbit_lt_succ (n : ℕ) : quadOneOrbit n < quadOneOrbit (n + 1) := by
  have h : quadOneOrbit n ≤ quadOneOrbit n ^ 2 :=
    Nat.le_self_pow (by norm_num) (quadOneOrbit n)
  rw [quadOneOrbit]
  omega

theorem strictMono_quadOneOrbit : StrictMono quadOneOrbit :=
  strictMono_nat_of_lt_succ quadOneOrbit_lt_succ

theorem quadOneOrbit_succ_ne_zero (n : ℕ) : quadOneOrbit (n + 1) ≠ 0 := by
  rw [quadOneOrbit]; omega

theorem quadOne_eval_quadOneOrbit (n : ℕ) :
    quadOne.eval ((quadOneOrbit n : ℕ) : ℂ) = ((quadOneOrbit (n + 1) : ℕ) : ℂ) := by
  rw [quadOne_eval, quadOneOrbit]
  push_cast
  ring

/-! ## No pole at either point of the critical pair -/

/-- The critical value carries no pole: its forward orbit is infinite and critical-free. -/
theorem quadOne_affine_no_pole_at_one {a : RatFunc ℂ} (ha : a ≠ 0)
    (heq : IsAffineConnection quadOne quadOne_not_isConst a) : 0 ≤ ratOrder a 1 := by
  by_contra hpole
  rw [not_le] at hpole
  refine no_pole_of_forward_orbit quadOne_natDegree_ne_zero ha heq
    (f := fun n : ℕ => ((quadOneOrbit (n + 1) : ℕ) : ℂ)) (fun n => ?_) (fun n => ?_) ?_ ?_
  · exact (quadOne_eval_quadOneOrbit (n + 1)).symm
  · rw [derivative_quadOne_eval]
    refine mul_ne_zero (by norm_num) ?_
    exact_mod_cast (Nat.cast_ne_zero (R := ℂ)).mpr (quadOneOrbit_succ_ne_zero n)
  · intro m n hmn
    simp only at hmn
    have h1 := Nat.cast_injective (R := ℂ) hmn
    have h2 := strictMono_quadOneOrbit.injective h1
    omega
  · have h1 : ((quadOneOrbit 1 : ℕ) : ℂ) = 1 := by norm_num [quadOneOrbit]
    simpa [h1] using hpole

/-- The critical point carries no pole: the imaginary unit is a preimage carrying an injective
critical-free backward orbit. -/
theorem quadOne_affine_no_pole_at_zero {a : RatFunc ℂ} (ha : a ≠ 0)
    (heq : IsAffineConnection quadOne quadOne_not_isConst a) : 0 ≤ ratOrder a 0 := by
  by_contra hpole
  rw [not_le] at hpole
  have hI : quadOne.eval Complex.I = 0 := by rw [quadOne_eval, Complex.I_sq]; ring
  have hIcrit : (derivative quadOne).eval Complex.I ≠ 0 := by
    rw [derivative_quadOne_eval]
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hIpole : ratOrder a Complex.I < 0 :=
    affine_pole_backward quadOne_natDegree_ne_zero ha heq hIcrit (by rw [hI]; exact hpole)
  obtain ⟨b, hb0, hstep, hinj, hcrit⟩ :=
    exists_backward_orbit quadOne_natDegree_ne_zero aperiodic_quadOne_I postcritical_quadOne_ne_I
  exact no_pole_of_backward_orbit quadOne_natDegree_ne_zero ha heq hstep hcrit hinj
    (by rw [hb0]; exact hIpole)

/-- **`z ↦ z² + 1` carries no rational affine connection.** -/
theorem quadOne_no_affine_connection (a : RatFunc ℂ) :
    ¬ IsAffineConnection quadOne quadOne_not_isConst a := by
  intro heq
  rcases eq_or_ne a 0 with rfl | ha
  · have hcurv := derivative_derivative_eq_zero_of_isAffineConnection_zero heq
    rw [derivative_quadOne, derivative_mul, derivative_C, derivative_X, zero_mul, mul_one,
      zero_add] at hcurv
    have hc := congrArg (fun p => Polynomial.coeff p 0) hcurv
    simp at hc
  · exact no_affine_connection_regular_at_critical quadOne_natDegree_ne_zero ha heq quadOne_critical
      (quadOne_affine_no_pole_at_zero ha heq)
      (by rw [quadOne_eval_zero]; exact quadOne_affine_no_pole_at_one ha heq)

end GaloisForLFunctions.HTGeometry

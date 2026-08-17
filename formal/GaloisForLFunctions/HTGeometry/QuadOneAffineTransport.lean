import GaloisForLFunctions.HTGeometry.RationalAffineTransport
import GaloisForLFunctions.HTGeometry.QuadOneNoAffineConnection

/-!
# Affine transport equations of `z ↦ z² + 1`

Every coefficient equation produced by the orbifold descent of `z ↦ z² + 1` has the shape

`a(z² + 1) · (2z)^k = b(z) · a(z) + c(z)`

with `b` a unit and `c` regular away from the origin — the origin being the critical point, where the
inhomogeneous term of the descent acquires its pole.

For such an equation the solution has no pole at the critical point and none at the critical value:
a pole at the critical value runs forward along `1, 2, 5, 26, …`, and a pole at the critical point
pulls back to the imaginary unit, whose chosen backward orbit is injective and avoids the origin
because it avoids the critical set.  Either way the pole set would be infinite.

If moreover `c` has a pole at the origin and `k` is nonnegative, no nonzero solution exists at all:
the substitution ramifies to order two at the critical point, so the left side has order at least
`2·ord₁(a) + k ≥ 0` there, while the right side has the order of `c`, which is negative.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **No pole at the critical pair.**  For an affine transport of `z ↦ z² + 1` whose coefficient is a
unit and whose inhomogeneous term is regular away from the origin, the solution is regular at the
critical point and at the critical value. -/
theorem quadOne_affineTransport_regular_at_critical_pair {k : ℤ} {b c a : RatFunc ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : IsAffineTransport quadOne quadOne_not_isConst k b c a)
    (hbunit : ∀ p : ℂ, p ≠ 0 → ratOrder b p = 0)
    (hcreg : ∀ p : ℂ, p ≠ 0 → 0 ≤ ratOrder c p) :
    0 ≤ ratOrder a 0 ∧ 0 ≤ ratOrder a 1 := by
  have hone : 0 ≤ ratOrder a 1 := by
    by_contra hpole
    rw [not_le] at hpole
    have hne : ∀ n : ℕ, ((quadOneOrbit (n + 1) : ℕ) : ℂ) ≠ 0 := by
      intro n
      exact_mod_cast (Nat.cast_ne_zero (R := ℂ)).mpr (quadOneOrbit_succ_ne_zero n)
    refine no_pole_of_forward_orbit_affineTransport quadOne_natDegree_ne_zero ha hb heq
      (f := fun n : ℕ => ((quadOneOrbit (n + 1) : ℕ) : ℂ)) (fun n => ?_) (fun n => ?_)
      (fun n => hbunit _ (hne n)) (fun n => hcreg _ (hne n)) ?_ ?_
    · exact (quadOne_eval_quadOneOrbit (n + 1)).symm
    · rw [derivative_quadOne_eval]
      exact mul_ne_zero (by norm_num) (hne n)
    · intro m n hmn
      simp only at hmn
      have h1 := Nat.cast_injective (R := ℂ) hmn
      have h2 := strictMono_quadOneOrbit.injective h1
      omega
    · have h1 : ((quadOneOrbit 1 : ℕ) : ℂ) = 1 := by norm_num [quadOneOrbit]
      simpa [h1] using hpole
  refine ⟨?_, hone⟩
  by_contra hpole
  rw [not_le] at hpole
  have hI : quadOne.eval Complex.I = 0 := by rw [quadOne_eval, Complex.I_sq]; ring
  have hIcrit : (derivative quadOne).eval Complex.I ≠ 0 := by
    rw [derivative_quadOne_eval]
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hIpole : ratOrder a Complex.I < 0 :=
    affineTransport_pole_backward quadOne_natDegree_ne_zero ha hb heq hIcrit
      (hbunit _ Complex.I_ne_zero) (hcreg _ Complex.I_ne_zero) (by rw [hI]; exact hpole)
  obtain ⟨q, hq0, hstep, hinj, hcrit⟩ :=
    exists_backward_orbit quadOne_natDegree_ne_zero aperiodic_quadOne_I postcritical_quadOne_ne_I
  have hqne : ∀ n : ℕ, q (n + 1) ≠ 0 := by
    intro n h
    exact hcrit n (by rw [h, derivative_quadOne_eval]; ring)
  exact no_pole_of_backward_orbit_affineTransport quadOne_natDegree_ne_zero ha hb heq hstep hcrit
    (fun n => hbunit _ (hqne n)) (fun n => hcreg _ (hqne n)) hinj (by rw [hq0]; exact hIpole)

/-- **A polar inhomogeneous term at the critical point kills the equation.**  For `z ↦ z² + 1`, an
affine transport with nonnegative exponent, unit coefficient, and inhomogeneous term regular away
from the origin but polar at it has no nonzero solution. -/
theorem quadOne_no_affineTransport_of_polar_at_critical {k : ℤ} {b c a : RatFunc ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc0 : c ≠ 0)
    (heq : IsAffineTransport quadOne quadOne_not_isConst k b c a)
    (hbunit : ∀ p : ℂ, p ≠ 0 → ratOrder b p = 0)
    (hcreg : ∀ p : ℂ, p ≠ 0 → 0 ≤ ratOrder c p)
    (hb0 : ratOrder b 0 = 0) (hcpole : ratOrder c 0 < 0) (hk : 0 ≤ k) : False := by
  obtain ⟨hzero, hone⟩ :=
    quadOne_affineTransport_regular_at_critical_pair ha hb heq hbunit hcreg
  have hkey := ratOrder_le_of_critical quadOne_natDegree_ne_zero ha hb hc0 heq
    (p := (0 : ℂ)) (by omega)
  have hval : quadOne.eval (0 : ℂ) = 1 := quadOne_eval_zero
  rw [rootMultiplicity_quadOne_crit, rootMultiplicity_derivative_quadOne, hval] at hkey
  norm_num at hkey
  omega

end GaloisForLFunctions.HTGeometry

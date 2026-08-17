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

/-- **The critical-point obstruction.**  For `z ↦ z² + 1`, an affine transport whose coefficient is a
unit away from the origin and whose inhomogeneous term is regular away from the origin has no nonzero
solution as soon as, at the origin, the order of the inhomogeneous term is below both the order of
the coefficient and the exponent.

The substitution ramifies to order two at the critical point and the derivative vanishes there to
order one, so the left side has order at least `2·ord₁(a) + k ≥ k`; the right side has the order of
the inhomogeneous term. -/
theorem quadOne_no_affineTransport_of_critical_order {k : ℤ} {b c a : RatFunc ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc0 : c ≠ 0)
    (heq : IsAffineTransport quadOne quadOne_not_isConst k b c a)
    (hbunit : ∀ p : ℂ, p ≠ 0 → ratOrder b p = 0)
    (hcreg : ∀ p : ℂ, p ≠ 0 → 0 ≤ ratOrder c p)
    (hcb : ratOrder c 0 < ratOrder b 0) (hck : ratOrder c 0 < k) : False := by
  obtain ⟨hzero, hone⟩ :=
    quadOne_affineTransport_regular_at_critical_pair ha hb heq hbunit hcreg
  have hkey := ratOrder_le_of_critical quadOne_natDegree_ne_zero ha hb hc0 heq
    (p := (0 : ℂ)) (by omega)
  have hval : quadOne.eval (0 : ℂ) = 1 := quadOne_eval_zero
  rw [rootMultiplicity_quadOne_crit, rootMultiplicity_derivative_quadOne, hval] at hkey
  norm_num at hkey
  omega

/-- **A polar inhomogeneous term at the critical point kills the equation.** -/
theorem quadOne_no_affineTransport_of_polar_at_critical {k : ℤ} {b c a : RatFunc ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc0 : c ≠ 0)
    (heq : IsAffineTransport quadOne quadOne_not_isConst k b c a)
    (hbunit : ∀ p : ℂ, p ≠ 0 → ratOrder b p = 0)
    (hcreg : ∀ p : ℂ, p ≠ 0 → 0 ≤ ratOrder c p)
    (hb0 : 0 ≤ ratOrder b 0) (hcpole : ratOrder c 0 < 0) (hk : 0 ≤ k) : False :=
  quadOne_no_affineTransport_of_critical_order ha hb hc0 heq hbunit hcreg (by omega) (by omega)


/-- **A nonzero constant inhomogeneous term, with the derivative as coefficient, kills the
equation.**  This is the shape the weight-zero descent produces at the base of the tower: the
inhomogeneous term is a nonzero constant, which neither vanishes at the critical point nor reaches
the exponent. -/
theorem quadOne_no_affineTransport_of_const {k : ℤ} {γ : ℂ} {a : RatFunc ℂ}
    (hγ : γ ≠ 0) (ha : a ≠ 0) (hk : 1 ≤ k)
    (heq : IsAffineTransport quadOne quadOne_not_isConst k
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne))
      (RatFunc.C γ) a) : False := by
  have hb : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero
      (derivative_ne_zero_of_natDegree_ne_zero quadOne_natDegree_ne_zero)
  have hc0 : (RatFunc.C γ : RatFunc ℂ) ≠ 0 := by
    intro hh
    exact hγ ((RatFunc.C_injective (K := ℂ)) (by rw [hh, map_zero]))
  have hb0 : ratOrder (algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (Polynomial.derivative quadOne)) 0 = 1 := by
    rw [ratOrder_algebraMap, rootMultiplicity_derivative_quadOne, Nat.cast_one]
  refine quadOne_no_affineTransport_of_critical_order ha hb hc0 heq (fun p hp => ?_)
    (fun p _ => ?_) ?_ ?_
  · rw [ratOrder_algebraMap, rootMultiplicity_eq_zero ?_, Nat.cast_zero]
    rw [Polynomial.IsRoot.def, derivative_quadOne_eval]
    exact mul_ne_zero (by norm_num) hp
  · rw [ratOrder_C]
  · rw [ratOrder_C, hb0]
    norm_num
  · rw [ratOrder_C]
    omega

end GaloisForLFunctions.HTGeometry

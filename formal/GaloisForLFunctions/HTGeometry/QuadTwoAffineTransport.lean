import GaloisForLFunctions.HTGeometry.RationalAffineTransport
import GaloisForLFunctions.HTGeometry.QuadTwoNoAffineConnection

/-!
# Affine transport equations of `z ↦ (z − 1)²`

The companion of `QuadOneAffineTransport` for the postcritically finite quadratic map.  Here the
critical point is `1` and the critical value `0`, and the critical orbit is the two-cycle
`1 ↦ 0 ↦ 1`, so no forward orbit is available: a pole at the critical value travels forward to the
critical point, and a pole at the critical point pulls back to `2`, whose chosen backward orbit is
injective and avoids the critical point.

If moreover the inhomogeneous term has a pole at the critical point and the exponent is nonnegative,
no nonzero solution exists.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **No pole at the critical pair.** -/
theorem quadTwo_affineTransport_regular_at_critical_pair {k : ℤ} {b c a : RatFunc ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : IsAffineTransport quadTwo quadTwo_not_isConst k b c a)
    (hbunit : ∀ p : ℂ, p ≠ 1 → ratOrder b p = 0)
    (hcreg : ∀ p : ℂ, p ≠ 1 → 0 ≤ ratOrder c p) :
    0 ≤ ratOrder a 1 ∧ 0 ≤ ratOrder a 0 := by
  have hone : 0 ≤ ratOrder a 1 := by
    by_contra hpole
    rw [not_le] at hpole
    have htwo : (derivative quadTwo).eval 2 ≠ 0 := by
      rw [derivative_quadTwo_eval]; norm_num
    have htwone : (2 : ℂ) ≠ 1 := by norm_num
    have htwopole : ratOrder a 2 < 0 :=
      affineTransport_pole_backward quadTwo_natDegree_ne_zero ha hb heq htwo
        (hbunit _ htwone) (hcreg _ htwone) (by rw [quadTwo_eval_two]; exact hpole)
    obtain ⟨q, hq0, hstep, hinj, hcrit⟩ :=
      exists_backward_orbit quadTwo_natDegree_ne_zero aperiodic_quadTwo_two
        postcritical_quadTwo_ne_two
    have hqne : ∀ n : ℕ, q (n + 1) ≠ 1 := by
      intro n h
      exact hcrit n (by rw [h, derivative_quadTwo_eval]; ring)
    exact no_pole_of_backward_orbit_affineTransport quadTwo_natDegree_ne_zero ha hb heq hstep hcrit
      (fun n => hbunit _ (hqne n)) (fun n => hcreg _ (hqne n)) hinj (by rw [hq0]; exact htwopole)
  refine ⟨hone, ?_⟩
  by_contra hpole
  rw [not_le] at hpole
  have hzero : (derivative quadTwo).eval 0 ≠ 0 := by
    rw [derivative_quadTwo_eval]; norm_num
  have hzne : (0 : ℂ) ≠ 1 := by norm_num
  have hforward := affineTransport_pole_forward quadTwo_natDegree_ne_zero ha hb heq hzero
    (hbunit _ hzne) (hcreg _ hzne) hpole
  rw [quadTwo_eval_zero] at hforward
  exact absurd hforward (not_lt.mpr hone)

/-- **A polar inhomogeneous term at the critical point kills the equation.** -/
theorem quadTwo_no_affineTransport_of_polar_at_critical {k : ℤ} {b c a : RatFunc ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc0 : c ≠ 0)
    (heq : IsAffineTransport quadTwo quadTwo_not_isConst k b c a)
    (hbunit : ∀ p : ℂ, p ≠ 1 → ratOrder b p = 0)
    (hcreg : ∀ p : ℂ, p ≠ 1 → 0 ≤ ratOrder c p)
    (hb1 : ratOrder b 1 = 0) (hcpole : ratOrder c 1 < 0) (hk : 0 ≤ k) : False := by
  obtain ⟨hone, hzero⟩ :=
    quadTwo_affineTransport_regular_at_critical_pair ha hb heq hbunit hcreg
  have hkey := ratOrder_le_of_critical quadTwo_natDegree_ne_zero ha hb hc0 heq
    (p := (1 : ℂ)) (by omega)
  rw [rootMultiplicity_quadTwo_crit, rootMultiplicity_derivative_quadTwo, quadTwo_eval_one] at hkey
  norm_num at hkey
  omega

end GaloisForLFunctions.HTGeometry

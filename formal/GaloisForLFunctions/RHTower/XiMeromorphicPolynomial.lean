import GaloisForLFunctions.HTGeometry.MeromorphicPolynomialLift
import GaloisForLFunctions.RHTower.XiPolynomialLeftFactors
import GaloisForLFunctions.RHTower.XiCubicMeromorphic

/-!
# Polynomial left factors over the global meromorphic plane

Local pole removal upgrades a field-valued polynomial lift to an entire
representative. Actual tilted Xi then forces the outer polynomial to be linear.
-/

open Complex Polynomial Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Every polynomial left factor of tilted Xi over the global meromorphic plane has degree one. -/
theorem xi_polynomial_plane_factor_natDegree_eq_one (a : ℝ) (P : Polynomial ℂ)
    (x : MeromorphicPlane)
    (hrel : Polynomial.aeval x P = xiCubicParameterElement a) : P.natDegree = 1 := by
  have hd := xiCubicParameter_differentiable a
  have hPdeg : 0 < P.natDegree := by
    by_contra hn
    have heP := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos hn)
    rw [heP, Polynomial.aeval_C, algebraMap_plane] at hrel
    have he := (ofMeromorphic_eq_iff (fun z => MeromorphicAt.const (P.coeff 0) z)
      (fun z => (hd.analyticAt z).meromorphicAt)).mp hrel
    have hc (z : ℂ) : P.coeff 0 = xiCubicParameter a z :=
      ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const
        hd.continuous.continuousAt).mp (he z)).eq_of_nhds
    apply xi_tilt_not_exp_ray_bound a 1
    refine ⟨‖P.coeff 0‖ + 1, by positivity, fun t ht => ?_⟩
    change ‖xiCubicParameter a ((1 + t : ℝ) : ℂ)‖ ≤ _
    rw [← hc]
    nlinarith [Real.add_one_le_exp ((‖P.coeff 0‖ + 1) * t), norm_nonneg (P.coeff 0)]
  obtain ⟨h, hh, _, hval⟩ := entire_polynomial_lift_of_plane hd P hPdeg x hrel
  exact xi_polynomial_left_factor_natDegree_eq_one a hh hval

end RHTower

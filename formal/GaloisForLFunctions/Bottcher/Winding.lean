/-
# Böttcher tower — the base period `∮ d log φ_c = 2πi` (total mass / cap normalization)

The logarithmic derivative `d log φ_c = φ_c'/φ_c = z⁻¹ + ∑ₖ deriv(termₖ)` is the Cauchy
transform of the equilibrium measure `μ_c` (Brolin). Its period around a large circle `C(0,R)`
is the **total mass**:

  `∮_{C(0,R)} d log φ_c = 2πi · μ_c(ℂ) = 2πi`,    i.e. `cap(K_c) = 1` and winding `= 1`.

Proof: split `d log φ_c = z⁻¹ + deriv(∑ₖ termₖ)`. The pole term integrates to `2πi`
(`integral_sub_inv_of_mem_ball`); the series part is the derivative of a single-valued analytic
function on the escape annulus, so its loop integral vanishes (FTC,
`integral_eq_zero_of_hasDerivWithinAt`). This is the `n = 0` case of the dyadic period tower:
the deeper cylinder periods `2πi/2ⁿ` (the monodromy multipliers) are the same integral around
inner loops enclosing equilibrium mass `2⁻ⁿ`, fed to `multiplier_orderOf_of_mass`.
-/
import GaloisForLFunctions.Bottcher.BottcherCoord
import Mathlib.MeasureTheory.Integral.CircleIntegral

open Complex Metric

namespace Bottcher

/-- **Base period / total mass.** The logarithmic derivative of `φ_c` integrates to `2πi`
around any escape-regime circle `C(0,R)` (`R > max 2 ‖c‖`): the winding number of `φ_c` is `1`
and the equilibrium measure has total mass `1` (`cap K_c = 1`). The `n = 0` rung of the dyadic
period tower. -/
theorem circleIntegral_dlog_bottcher {c : ℂ} {R : ℝ} (hR : max 2 ‖c‖ < R) :
    (∮ z in C(0, R), z⁻¹ + deriv (fun w => ∑' k, bottcherLogTerm c w k) z)
      = 2 * (Real.pi : ℂ) * Complex.I := by
  have hRpos : 0 < R := lt_of_le_of_lt (le_max_left _ _ |>.trans' (by norm_num)) hR
  have hR0 : 0 ≤ R := le_of_lt hRpos
  have hsub : sphere (0 : ℂ) R ⊆ escapeOpen c := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    rw [escapeOpen, Set.mem_setOf_eq, hz]; exact hR
  have hSan : AnalyticOnNhd ℂ (fun w => ∑' k, bottcherLogTerm c w k) (escapeOpen c) :=
    (differentiableOn_bottcherLogSum c).analyticOnNhd (isOpen_escapeOpen c)
  have hci1 : CircleIntegrable (fun z : ℂ => z⁻¹) 0 R := by
    apply ContinuousOn.circleIntegrable hR0
    apply continuousOn_inv₀.mono
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h; rw [h, norm_zero] at hz; linarith
  have hci2 : CircleIntegrable (deriv (fun w => ∑' k, bottcherLogTerm c w k)) 0 R :=
    ((hSan.deriv).continuousOn.mono hsub).circleIntegrable hR0
  rw [circleIntegral.integral_add hci1 hci2]
  have h1 : (∮ z in C(0, R), z⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
    have key := circleIntegral.integral_sub_inv_of_mem_ball (c := (0:ℂ)) (w := (0:ℂ)) (R := R)
      (by simp [hRpos])
    simp only [sub_zero] at key
    exact key
  have h2 : (∮ z in C(0, R), deriv (fun w => ∑' k, bottcherLogTerm c w k) z) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR0
    intro z hz
    exact (((hSan z (hsub hz)).differentiableAt).hasDerivAt).hasDerivWithinAt
  rw [h1, h2, add_zero]

end Bottcher

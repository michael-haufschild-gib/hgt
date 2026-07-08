/-
Littlewood's lemma for ξ: the weighted zero count on a disc is fixed by a log-modulus circle average.

This is the disc form of Littlewood's lemma for the completed Riemann ξ — a holography-type
constraint: the weighted interior zero count is pinned by boundary data.  Jensen's formula (mathlib
`AnalyticOnNhd.circleAverage_log_norm`) reads the weighted zero count off the boundary integral of
`log‖ξ‖`:

  circleAverage (log‖ξ‖) c R = ∑ᶠ ρ  ord_ρ(ξ) · log (R / ‖c − ρ‖)  +  log‖ξ(c)‖,

where `circleAverage g c R = (2π)⁻¹ ∫₀²π g(c + R e^{iθ}) dθ`.  Every zero in the closed ball
`B(c, R)` contributes its multiplicity weighted by `log(R/‖c−ρ‖) ≥ 0`; zeros deep inside (in
`B(c, r)`, `r < R`) each contribute at least `log(R/r)`.  Hence the number of ξ-zeros in the inner
ball is bounded by the boundary data:

  (#zeros in B(c,r)) · log(R/r) ≤ log(M / ‖ξ(c)‖),     ‖ξ‖ ≤ M on the sphere of radius R.

`xi_circleAverage_log_norm` is the identity, `xi_zeroCount_disc_le` the counting inequality
(mathlib's `sum_divisor_le` specialised to ξ), and `xi_zeroCount_disc_le_logModulus` the constraint in
strip-shaped form: the boundary log-modulus caps the interior zero count, with the radial gap
`log(R/r) > 0` in the role of `σ₀ − σ₁`.  The anchor `ξ(c) ≠ 0` is available for any `c` with
`Re c > 1` (`xi_ne_zero_of_one_lt_re`), e.g. `c = 2 + iτ`.
-/
import GaloisForLFunctions.RHTower.FarFieldAnchor
import Mathlib.Analysis.Complex.JensenFormula

open Complex Real MeasureTheory Metric

namespace RHTower

/-- ξ is analytic on every closed ball. -/
theorem xi_analyticOnNhd_ball (c : ℂ) (R : ℝ) : AnalyticOnNhd ℂ xi (closedBall c |R|) :=
  fun z _ => xi_analyticOnNhd_univ z (Set.mem_univ z)

/-- **Jensen's formula for ξ.**  The circle average of `log‖ξ‖` on `∂B(c, R)` equals the weighted
zero count in the closed ball plus the anchor value `log‖ξ(c)‖`.  This is the disc-form Littlewood
identity: `(1/2π)∫₀²π log‖ξ(c + R e^{iθ})‖ dθ = ∑_ρ ord_ρ(ξ)·log(R/‖c−ρ‖) + log‖ξ(c)‖`. -/
theorem xi_circleAverage_log_norm {c : ℂ} {R : ℝ} (hR : R ≠ 0) (hc : xi c ≠ 0) :
    circleAverage (fun x => Real.log ‖xi x‖) c R
      = ∑ᶠ u, ((MeromorphicOn.divisor xi (closedBall c |R|)) u : ℝ) * Real.log (R * ‖c - u‖⁻¹)
        + Real.log ‖xi c‖ :=
  (xi_analyticOnNhd_ball c R).circleAverage_log_norm hR hc

/-- **Littlewood's counting inequality for ξ.**  The number of ξ-zeros (with multiplicity) in the
inner ball `B(c, r)` is bounded by `log(M/‖ξ(c)‖) / log(R/r)`, where `M` bounds `‖ξ‖` on the outer
sphere of radius `R > r` and `ξ(c) ≠ 0`.  Directly Jensen's inequality (`sum_divisor_le`) for the
entire function ξ. -/
theorem xi_zeroCount_disc_le {c : ℂ} {r R M : ℝ} (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (hc : xi c ≠ 0) (hbound : ∀ z ∈ sphere c |R|, ‖xi z‖ ≤ M) :
    (↑(∑ᶠ u, (MeromorphicOn.divisor xi (closedBall c |r|)) u) : ℝ)
      ≤ Real.log (M / ‖xi c‖) / Real.log (R / r) :=
  (xi_analyticOnNhd_ball c R).sum_divisor_le hr hrR hM hc hbound

/-- The anchor is available on the right of `Re s = 1`: `ξ(2 + iτ) ≠ 0`. -/
theorem xi_anchor_two_add_I_mul (τ : ℝ) : xi (2 + I * (τ : ℂ)) ≠ 0 := by
  apply xi_ne_zero_of_one_lt_re
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]

/-- **Boundary log-modulus caps the interior zero count** (positive radii).  If the inner ball
`B(c, r)` contains at least `K` ξ-zeros (counted with multiplicity) and `‖ξ‖ ≤ M` on the outer sphere
of radius `R > r`, then `K · log(R/r) ≤ log M − log‖ξ(c)‖`: the zero count is fixed from above by the
boundary log-modulus, with the gap `log(R/r) > 0` playing the role of `σ₀ − σ₁` in the strip form.  A
holography-type constraint — the interior count cannot exceed what the boundary data allows. -/
theorem xi_zeroCount_disc_le_logModulus {c : ℂ} {r R M K : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M) (hc : xi c ≠ 0)
    (hbound : ∀ z ∈ sphere c |R|, ‖xi z‖ ≤ M)
    (hK : (K : ℝ) ≤ ↑(∑ᶠ u, (MeromorphicOn.divisor xi (closedBall c |r|)) u)) :
    K * Real.log (R / r) ≤ Real.log M - Real.log ‖xi c‖ := by
  have hra : 0 < |r| := by rwa [abs_of_pos hr]
  have hrRa : |r| < |R| := by rwa [abs_of_pos hr, abs_of_pos (hr.trans hrR)]
  have hcount := xi_zeroCount_disc_le hra hrRa hM hc hbound
  have hKle : (K : ℝ) ≤ Real.log (M / ‖xi c‖) / Real.log (R / r) := le_trans hK hcount
  have hnorm : (0 : ℝ) < ‖xi c‖ := norm_pos_iff.mpr hc
  have hlogRr : 0 < Real.log (R / r) := Real.log_pos (by rw [lt_div_iff₀ hr]; linarith)
  rw [le_div_iff₀ hlogRr] at hKle
  rwa [Real.log_div (by positivity) (ne_of_gt hnorm)] at hKle

end RHTower

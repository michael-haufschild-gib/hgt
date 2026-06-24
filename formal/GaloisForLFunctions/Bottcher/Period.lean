/-
# Böttcher tower — Tier 3a: the per-point period dichotomy

The period formula `∮_γ dlogφ_c = 2πi ∫_K Ind(γ,·) dμ_c` (which discharges the
analytic half of the `mono` input to the disconnected case) is built on the contour
integral of the Cauchy kernel `(z-ζ)⁻¹` around a circle:

  * `ζ` inside the disk   ⟹  `∮ (z-ζ)⁻¹ dz = 2πi`   (winding number 1),
  * `ζ` outside the disk  ⟹  `∮ (z-ζ)⁻¹ dz = 0`     (Cauchy's theorem).

Integrating this dichotomy against the equilibrium measure `μ_c` and summing over the
removed Cantor cylinders yields the dyadic periods `2πi/2ⁿ`. This file banks the
dichotomy; the Fubini-swap against `μ_c` is the next step.
-/
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod

open Complex Metric MeasureTheory

namespace Bottcher

/-- **Inside.** For `w` strictly inside the disk, the Cauchy-kernel period is `2πi`. -/
theorem period_point_inside {c w : ℂ} {R : ℝ} (h : w ∈ ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹) = 2 * (Real.pi : ℂ) * Complex.I :=
  circleIntegral.integral_sub_inv_of_mem_ball h

/-- **Outside.** For `w` outside the closed disk, the kernel is holomorphic on the disk,
so the period vanishes (Cauchy). -/
theorem period_point_outside {c w : ℂ} {R : ℝ} (h0 : 0 ≤ R) (h : w ∉ closedBall c R) :
    (∮ z in C(c, R), (z - w)⁻¹) = 0 := by
  apply DiffContOnCl.circleIntegral_eq_zero h0
  apply DifferentiableOn.diffContOnCl
  intro z hz
  have hz' : z ∈ closedBall c R := closure_ball_subset_closedBall hz
  have hzw : z ≠ w := fun he => h (he ▸ hz')
  exact (differentiableWithinAt_id.sub_const w).inv (sub_ne_zero.mpr hzw)

/-- **Period formula RHS.** If the measure puts no mass on the circle `C(c,R)`, then the
`μ`-integral of the per-point period equals `2πi` times the enclosed mass:
`∫_K (∮_{C(c,R)} (z-ζ)⁻¹ dz) dμ(ζ) = 2πi · μ(ball c R)`. This is the right-hand side of
`∮_γ dlogφ_c = 2πi ∫ Ind(γ,·) dμ_c` once Fubini swaps the order; with the equilibrium
measure of a full-shift Cantor set and a depth-`n` cylinder it specialises to `2πi/2ⁿ`. -/
theorem period_integral_eq (μ : Measure ℂ) [IsFiniteMeasure μ] {c : ℂ} {R : ℝ}
    (h0 : 0 ≤ R) (hsphere : μ (sphere c R) = 0) :
    ∫ ζ, (∮ z in C(c, R), (z - ζ)⁻¹) ∂μ
      = 2 * (Real.pi : ℂ) * Complex.I * (μ (ball c R)).toReal := by
  -- off the circle, the per-point period agrees with `(2πi)·𝟙_ball`.
  have hae : (fun ζ => ∮ z in C(c, R), (z - ζ)⁻¹)
      =ᵐ[μ] Set.indicator (ball c R) (fun _ => 2 * (Real.pi : ℂ) * Complex.I) := by
    refine ae_iff.mpr (measure_mono_null ?_ hsphere)
    intro ζ hζ
    by_contra hns
    apply hζ
    dsimp only
    have hdist : dist ζ c ≠ R := fun h => hns (Metric.mem_sphere.mpr h)
    rcases lt_or_gt_of_ne hdist with hlt | hgt
    · have hb : ζ ∈ ball c R := Metric.mem_ball.mpr hlt
      rw [period_point_inside hb, Set.indicator_of_mem hb]
    · have hnc : ζ ∉ closedBall c R := fun hc => absurd (Metric.mem_closedBall.mp hc) (not_le.mpr hgt)
      have hnb : ζ ∉ ball c R := fun hb => hnc (ball_subset_closedBall hb)
      rw [period_point_outside h0 hnc, Set.indicator_of_notMem hnb]
  rw [integral_congr_ae hae, integral_indicator_const _ measurableSet_ball, Complex.real_smul]
  simp only [MeasureTheory.measureReal_def]
  ring

/-- **Period formula — Fubini swap.** The contour integral of the `μ`-averaged Cauchy
kernel equals the `μ`-average of the per-point period:
`∮_{C(c,R)} (∫_K (z-ζ)⁻¹ dμ) dz = ∫_K (∮_{C(c,R)} (z-ζ)⁻¹ dz) dμ`.
The joint integrability rides as a hypothesis (it holds when the loop `C(c,R)` is
separated from `supp μ = K_c`, i.e. the loop lies in the basin `Ω_c`). Combined with
`period_integral_eq` this gives the period `2πi·μ(enclosed)`. -/
theorem period_fubini_swap (μ : Measure ℂ) [IsFiniteMeasure μ] {c : ℂ} {R : ℝ}
    (hpi : (0 : ℝ) ≤ 2 * Real.pi)
    (hint : Integrable (Function.uncurry fun (θ : ℝ) (ζ : ℂ) =>
        deriv (circleMap c R) θ • (circleMap c R θ - ζ)⁻¹)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod μ)) :
    (∮ z in C(c, R), ∫ ζ, (z - ζ)⁻¹ ∂μ) = ∫ ζ, (∮ z in C(c, R), (z - ζ)⁻¹) ∂μ := by
  unfold circleIntegral
  simp_rw [← integral_smul]
  rw [intervalIntegral.integral_of_le hpi, integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ζ => ?_))
  dsimp only
  rw [intervalIntegral.integral_of_le hpi]

/-- **Period formula** (`∮_γ dlogφ_c = 2πi·(enclosed mass)`). For a circle separated
from `supp μ` (no mass on it, joint integrability), the contour integral of the
`μ`-averaged Cauchy kernel — which is `d log φ_c` when `μ = μ_c` is the equilibrium
measure (Green potential representation) — equals `2πi` times the enclosed mass.
With `μ_c` the full-shift fair-Bernoulli measure and a depth-`n` Cantor cylinder
enclosed (mass `2⁻ⁿ`), this is the dyadic period `2πi/2ⁿ` — the exact-monodromy
multiplier. -/
theorem period_eq (μ : Measure ℂ) [IsFiniteMeasure μ] {c : ℂ} {R : ℝ}
    (h0 : 0 ≤ R) (hsphere : μ (sphere c R) = 0)
    (hint : Integrable (Function.uncurry fun (θ : ℝ) (ζ : ℂ) =>
        deriv (circleMap c R) θ • (circleMap c R θ - ζ)⁻¹)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod μ)) :
    (∮ z in C(c, R), ∫ ζ, (z - ζ)⁻¹ ∂μ)
      = 2 * (Real.pi : ℂ) * Complex.I * (μ (ball c R)).toReal := by
  rw [period_fubini_swap μ (by positivity) hint, period_integral_eq μ h0 hsphere]

end Bottcher

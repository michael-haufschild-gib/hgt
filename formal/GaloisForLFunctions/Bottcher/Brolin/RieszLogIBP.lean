/-
# Böttcher tower — Brolin GAP-A: log-weighted layer cake toward the fundamental solution

The flux identity `integral_ball_laplacian_eq_boundary_flux` gives, for `r ≥ 0`,
`A(r) := ∫_{ball 0 r} Δφ = ∫₀²π Dφ(z_θ)(z_θ) dθ` (`z_θ = circleMap 0 r θ`).

To reach the centered fundamental solution `∫_ℂ log‖z‖·Δφ = 2π·φ(0)` we use the
**layer-cake** representation `log‖z‖ = log R − ∫_{‖z‖}^R dr/r` (for `φ` supported in
`ball 0 R`), which by Fubini turns the plane integral into `−∫_{(0,R)} A(r)/r dr` — no
singular integration by parts.  Then the flux identity and the fundamental theorem of
calculus on the circle average `M(r) = circleAverage φ 0 r` (`A(r)/r = 2π·M'(r)`,
`M(R)=0`, `M(0)=φ(0)`) finish it.

This file collects the two foundational bricks:
* `circleAverage_zero_radius` — `M(0) = φ(0)` (degenerate circle = its centre).
* `integral_laplacian_eq_zero` — `∫_ℂ Δφ = 0` for compactly supported `φ`, which drops
  straight out of the flux identity: for `r` past the support, the boundary flux `B(r)`
  vanishes because `Dφ = 0` there.
-/
import GaloisForLFunctions.Bottcher.Brolin.RieszFlux
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Laplacian InnerProductSpace Complex MeasureTheory Filter Real
open scoped Laplacian Topology

namespace Bottcher

noncomputable section

/-- **Circle average at radius zero is the centre value:** `M(0) = φ(0)`. -/
theorem circleAverage_zero_radius (φ : ℂ → ℝ) : circleAverage φ 0 0 = φ 0 := by
  rw [circleAverage_congr_sphere (f₂ := fun _ => φ 0) (fun z hz => by
    have hz0 : z = 0 := by simpa using hz
    rw [hz0]), circleAverage_const]

/-- **The total Laplacian of a compactly supported function vanishes:** `∫_ℂ Δφ = 0`.
Proof via the flux identity: past the support radius `R`, `∫_ℂ Δφ = ∫_{ball 0 r} Δφ`
(`Δφ = 0` far out, by locality of `Δ`) `= ∫₀²π Dφ(circleMap 0 r θ)(circleMap 0 r θ) dθ`
(Green flux), and `Dφ = 0` on `‖·‖ = r > R`, so the flux is `0`. -/
theorem integral_laplacian_eq_zero (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) : (∫ z, Δ φ z) = 0 := by
  obtain ⟨R, hR0, hR⟩ := hφc.exists_pos_le_norm
  set r : ℝ := R + 1 with hr
  have hr0 : 0 ≤ r := by positivity
  have hrR : R < r := by linarith
  have hEZ : ∀ z : ℂ, R < ‖z‖ → φ =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
    intro z hz
    refine eventuallyEq_of_mem (s := {x : ℂ | R < ‖x‖}) ?_ (fun x hx => hR x (le_of_lt hx))
    exact (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.ball (0:ℂ) r) (fun z hz => by
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hz
    rw [(laplacian_congr_nhds (hEZ z (by linarith))).eq_of_nhds]; simp)]
  rw [integral_ball_laplacian_eq_boundary_flux φ hφ hr0]
  rw [show (fun θ => fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 r θ)) = fun _ => (0:ℝ) from by
    funext θ
    have hnorm : R < ‖circleMap 0 r θ‖ := by
      rw [norm_circleMap_zero, abs_of_nonneg hr0]; exact hrR
    rw [(hEZ _ hnorm).fderiv_eq]; simp]
  simp

/-- **Circle average vanishes past the support:** if `φ = 0` on the circle `‖z‖ = R`
(`R ≥ 0`) then `M(R) = circleAverage φ 0 R = 0`. -/
theorem circleAverage_eq_zero_of_forall_sphere (φ : ℂ → ℝ) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ z : ℂ, ‖z‖ = R → φ z = 0) : circleAverage φ 0 R = 0 := by
  rw [circleAverage_congr_sphere (f₂ := fun _ => (0:ℝ)) (fun z hz => hR z (by
    rw [mem_sphere_zero_iff_norm, abs_of_nonneg hR0] at hz; exact hz)), circleAverage_const]

/-- **Derivative of the un-normalized circle integral** `G(s) = ∫₀²π φ(circleMap 0 s θ) dθ`,
by differentiation under the integral: `G'(r) = ∫₀²π Dφ(circleMap 0 r θ)(circleMap 0 1 θ) dθ`.
Same machinery as `hasDerivAt_B`: pointwise radial derivative (`hasDerivAt_circleMap_radius`
+ chain rule) with a constant domination bound from compactness. -/
theorem hasDerivAt_circleIntegral (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (r : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ θ in (0:ℝ)..(2*π), φ (circleMap 0 s θ))
      (∫ θ in (0:ℝ)..(2*π), fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 1 θ)) r := by
  set F : ℝ → ℝ → ℝ := fun s θ => φ (circleMap 0 s θ) with hF
  set F' : ℝ → ℝ → ℝ := fun s θ => fderiv ℝ φ (circleMap 0 s θ) (circleMap 0 1 θ) with hF'
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hcfd1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hcF : ∀ x, Continuous (F x) := fun x => hφ.continuous.comp (continuous_circleMap 0 x)
  have hcF' : ∀ x, Continuous (F' x) := fun x =>
    (hcfd1.comp (continuous_circleMap 0 x)).clm_apply (continuous_circleMap 0 1)
  have hcm : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    have heq : (fun p : ℝ × ℝ => circleMap 0 p.1 p.2)
        = fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * I) := by funext p; simp [circleMap]
    rw [heq]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hcF'p : Continuous (fun p : ℝ × ℝ => F' p.1 p.2) :=
    (hcfd1.comp hcm).clm_apply ((continuous_circleMap 0 1).comp continuous_snd)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall r 1).prod
    (isCompact_Icc (a := (0:ℝ)) (b := 2*π))).exists_bound_of_continuousOn hcF'p.continuousOn
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := r) (bound := fun _ => C) (a := 0) (b := 2*π)
    (μ := volume) (s := Metric.ball r 1)
    (Metric.ball_mem_nhds r one_pos)
    (Filter.Eventually.of_forall (fun x => (hcF x).aestronglyMeasurable))
    ((hcF r).intervalIntegrable _ _)
    (hcF' r).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun θ hθ x hx => by
      have hθ2 : θ ∈ Set.Icc (0:ℝ) (2*π) := Set.Ioc_subset_Icc_self (by
        rwa [Set.uIoc_of_le (by positivity)] at hθ)
      exact hC (x, θ) ⟨Metric.ball_subset_closedBall hx, hθ2⟩))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun θ _ x _ => by
      have hz : HasDerivAt (fun s : ℝ => circleMap 0 s θ) (circleMap 0 1 θ) x :=
        hasDerivAt_circleMap_radius θ x
      exact (hφd (circleMap 0 x θ)).hasFDerivAt.comp_hasDerivAt x hz))
  exact key.2

/-- **`M'(r) = (2π)⁻¹·∫₀²π Dφ(circleMap 0 r θ)(circleMap 0 1 θ) dθ`.**  The circle
average `M(r) = circleAverage φ 0 r = (2π)⁻¹·G(r)` differentiates through the constant. -/
theorem hasDerivAt_circleAverage (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (r : ℝ) :
    HasDerivAt (fun s : ℝ => circleAverage φ 0 s)
      ((2*π)⁻¹ • ∫ θ in (0:ℝ)..(2*π), fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 1 θ)) r := by
  have heq : (fun s : ℝ => circleAverage φ 0 s)
      = fun s : ℝ => (2*π)⁻¹ • ∫ θ in (0:ℝ)..(2*π), φ (circleMap 0 s θ) := by
    funext s; rw [circleAverage_def]
  rw [heq]
  exact (hasDerivAt_circleIntegral φ hφ r).const_smul (2*π)⁻¹

/-- `G(0) = ∫₀²π φ(circleMap 0 0 θ) dθ = 2π·φ(0)`. -/
theorem circleIntegral_zero_radius (φ : ℂ → ℝ) :
    (∫ θ in (0:ℝ)..(2*π), φ (circleMap 0 0 θ)) = 2*π * φ 0 := by
  rw [show (fun θ => φ (circleMap 0 0 θ)) = fun _ => φ 0 from by funext θ; simp [circleMap]]
  rw [intervalIntegral.integral_const]; simp [mul_comm]

/-- `G(R) = ∫₀²π φ(circleMap 0 R θ) dθ = 0` when `φ` vanishes on `‖z‖ = R`. -/
theorem circleIntegral_eq_zero_of_forall_sphere (φ : ℂ → ℝ) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ z : ℂ, ‖z‖ = R → φ z = 0) : (∫ θ in (0:ℝ)..(2*π), φ (circleMap 0 R θ)) = 0 := by
  rw [show (fun θ => φ (circleMap 0 R θ)) = fun _ => (0:ℝ) from by
    funext θ; exact hR _ (by rw [norm_circleMap_zero, abs_of_nonneg hR0])]
  simp

/-- **(II) FTC glue.** `∫_{(0,R)} r⁻¹·(∫_{ball 0 r} Δφ) dr = G(R) − G(0)`.  Pointwise the
integrand is the circle-integral derivative `G'(r)` (flux identity `A(r)=B(r)`, then
`Dφ(z)(z) = r·Dφ(z)(circleMap 0 1 θ)` factoring `r = ‖z‖`), and `∫_{(0,R)} G' = G(R)−G(0)`
by the FTC on `hasDerivAt_circleIntegral`. -/
theorem integral_ball_laplacian_div_r (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) {R : ℝ} (hR0 : 0 < R) :
    (∫ r in Set.Ioo 0 R, r⁻¹ * ∫ z in Metric.ball (0:ℂ) r, Δ φ z)
      = (∫ θ in (0:ℝ)..(2*π), φ (circleMap 0 R θ)) - ∫ θ in (0:ℝ)..(2*π), φ (circleMap 0 0 θ) := by
  have hpt : Set.EqOn (fun r => r⁻¹ * ∫ z in Metric.ball (0:ℂ) r, Δ φ z)
      (fun r => ∫ θ in (0:ℝ)..(2*π), fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 1 θ))
      (Set.Ioo 0 R) := by
    intro r hr
    simp only
    rw [integral_ball_laplacian_eq_boundary_flux φ hφ (le_of_lt hr.1)]
    rw [show (fun θ => fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 r θ))
        = fun θ => r • fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 1 θ) from by
      funext θ
      rw [congrArg (fderiv ℝ φ (circleMap 0 r θ)) (show circleMap 0 r θ = r • circleMap 0 1 θ from by
        simp [circleMap, Complex.real_smul]), ContinuousLinearMap.map_smul]]
    rw [intervalIntegral.integral_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hr.1),
      one_mul]
  rw [setIntegral_congr_fun measurableSet_Ioo hpt,
    setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le (le_of_lt hR0)]
  have hcfd1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hcm : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    have heq : (fun p : ℝ × ℝ => circleMap 0 p.1 p.2)
        = fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * I) := by funext p; simp [circleMap]
    rw [heq]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hG'cont : Continuous (fun r => ∫ θ in (0:ℝ)..(2*π),
      fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 1 θ)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      ((hcfd1.comp hcm).clm_apply ((continuous_circleMap 0 1).comp continuous_snd)) 0 (2*π)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hasDerivAt_circleIntegral φ hφ r) (hG'cont.intervalIntegrable 0 R)

end

end Bottcher

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
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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

/-- **Integrability of the layer-cake product integrand** `(r,z) ↦ r⁻¹·1_{‖z‖<r}·Δφ(z)`
on `(0,R) × ℂ`.  Via `integrable_prod_iff`: the inner `z`-slices are integrable (indicator
of the integrable `Δφ`), and the outer `r`-mass is dominated by `M·π·r` (ball-mass bound
`∫_{ball r}‖Δφ‖ ≤ M·πr²` from `Complex.volume_ball`). -/
theorem layerCake_integrable (φ : ℂ → ℝ) (hcΔ : Continuous (Δ φ)) {R M : ℝ}
    (hM : ∀ z, ‖Δ φ z‖ ≤ M) :
    Integrable (Function.uncurry
        (fun (r : ℝ) (z : ℂ) => r⁻¹ • (Metric.ball (0:ℂ) r).indicator (Δ φ) z))
      ((volume.restrict (Set.Ioo 0 R)).prod volume) := by
  set f : ℝ → ℂ → ℝ := fun r z => r⁻¹ • (Metric.ball (0:ℂ) r).indicator (Δ φ) z with hf
  have hmeas : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict (Set.Ioo 0 R)).prod volume) := by
    apply Measurable.aestronglyMeasurable
    have hset : MeasurableSet {q : ℝ × ℂ | ‖q.2‖ < q.1} :=
      (isOpen_lt (continuous_norm.comp continuous_snd) continuous_fst).measurableSet
    have he : (Function.uncurry f)
        = fun q : ℝ × ℂ => q.1⁻¹ • {q : ℝ × ℂ | ‖q.2‖ < q.1}.indicator (fun q => Δ φ q.2) q := by
      funext q
      simp only [hf, Function.uncurry, Set.indicator, Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq]
    rw [he]; exact (measurable_fst.inv).smul ((hcΔ.comp continuous_snd).measurable.indicator hset)
  rw [integrable_prod_iff hmeas]
  refine ⟨Filter.Eventually.of_forall (fun r => ?_), ?_⟩
  · have hΔint : IntegrableOn (Δ φ) (Metric.ball (0:ℂ) r) :=
      (hcΔ.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set
        Metric.ball_subset_closedBall
    exact ((hΔint.integrable_indicator measurableSet_ball).smul r⁻¹)
  · have hbound : ∀ r ∈ Set.Ioo (0:ℝ) R, (∫ z, ‖f r z‖) ≤ M * π * r := by
      intro r hr
      have hΔint : IntegrableOn (Δ φ) (Metric.ball (0:ℂ) r) :=
        (hcΔ.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set
          Metric.ball_subset_closedBall
      have hcInt : IntegrableOn (fun _ : ℂ => M) (Metric.ball (0:ℂ) r) :=
        (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set
          Metric.ball_subset_closedBall
      have hvol : volume.real (Metric.ball (0:ℂ) r) = π * r^(2 : ℕ) := by
        rw [Measure.real, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.coe_toReal,
          NNReal.coe_real_pi, ← ENNReal.ofReal_pow (le_of_lt hr.1),
          ENNReal.toReal_ofReal (by positivity)]; ring
      have hballmass : (∫ z in Metric.ball (0:ℂ) r, ‖Δ φ z‖) ≤ M * (π * r^(2 : ℕ)) := by
        calc (∫ z in Metric.ball (0:ℂ) r, ‖Δ φ z‖)
            ≤ ∫ _ in Metric.ball (0:ℂ) r, M :=
              setIntegral_mono_on hΔint.norm hcInt measurableSet_ball (fun z _ => hM z)
          _ = M * (π * r^(2 : ℕ)) := by rw [setIntegral_const, hvol, smul_eq_mul, mul_comm]
      have hstep : (∫ z, ‖f r z‖) = r⁻¹ * ∫ z in Metric.ball (0:ℂ) r, ‖Δ φ z‖ := by
        have hpt : ∀ z, ‖f r z‖ = r⁻¹ * (Metric.ball (0:ℂ) r).indicator (fun z => ‖Δ φ z‖) z := by
          intro z
          simp only [hf, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr.1)]
          congr 1
          by_cases hz : z ∈ Metric.ball (0:ℂ) r <;> simp [Set.indicator, hz]
        simp_rw [hpt]
        rw [integral_const_mul, integral_indicator measurableSet_ball]
      rw [hstep]
      calc r⁻¹ * ∫ z in Metric.ball (0:ℂ) r, ‖Δ φ z‖
          ≤ r⁻¹ * (M * (π * r^(2 : ℕ))) :=
            mul_le_mul_of_nonneg_left hballmass (le_of_lt (inv_pos.mpr hr.1))
        _ = M * π * r := by field_simp
    apply Integrable.mono' (g := fun r => M * π * r)
    · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ioo_subset_Icc_self
    · exact hmeas.norm.integral_prod_right'
    · exact (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall (fun r hr => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun z => norm_nonneg _))]
        exact hbound r hr))

/-- **The layer-cake Fubini identity** — the single remaining standard analytic fact.
`log‖z‖ = log R − ∫_{‖z‖}^R dr/r` (`φ` supported in `ball 0 R`) plus Fubini
`⟹ ∫_ℂ log‖z‖·Δφ = −∫_{(0,R)} r⁻¹·(∫_{ball 0 r} Δφ) dr`. -/
def LayerCakeIdentity (φ : ℂ → ℝ) (R : ℝ) : Prop :=
  (∫ z, Real.log ‖z‖ * Δ φ z)
    = -(∫ r in Set.Ioo 0 R, r⁻¹ * ∫ z in Metric.ball (0:ℂ) r, Δ φ z)

/-- **Centered fundamental solution, given the layer-cake identity.**  Combining the
layer-cake identity with the FTC glue `integral_ball_laplacian_div_r` and the endpoint
values `G(R)=0`, `G(0)=2π·φ(0)` yields `∫_ℂ log‖z‖·Δφ = 2π·φ(0)`. -/
theorem fundamentalSolution_centered_of_layerCake (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ)
    {R : ℝ} (hR0 : 0 < R) (hRsupp : ∀ z : ℂ, ‖z‖ = R → φ z = 0)
    (hLC : LayerCakeIdentity φ R) : (∫ z, Real.log ‖z‖ * Δ φ z) = 2 * π * φ 0 := by
  rw [hLC, integral_ball_laplacian_div_r φ hφ hR0,
    circleIntegral_eq_zero_of_forall_sphere φ (le_of_lt hR0) hRsupp,
    circleIntegral_zero_radius φ]
  ring

/-- **The centered planar fundamental solution:** `∫_ℂ log‖z‖·Δφ = 2π·φ(0)` for every
`C²` compactly supported `φ`.  Proof: the layer-cake identity holds — extend `A(r)=∫_{ball r}Δφ`
by indicator, swap (`integral_integral_swap`, `layerCake_integrable`), evaluate the inner
`r`-integral a.e. (`∫_{‖z‖}^R r⁻¹ = log R − log‖z‖`), and cancel `log R·∫Δφ = 0`
(`integral_laplacian_eq_zero`) — then `fundamentalSolution_centered_of_layerCake` finishes. -/
theorem fundamentalSolution_centered (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) : (∫ z, Real.log ‖z‖ * Δ φ z) = 2 * π * φ 0 := by
  have hcΔ : Continuous (Δ φ) := by
    have hcont : Continuous (fun x => iteratedFDeriv ℝ 2 φ x) :=
      hφ.continuous_iteratedFDeriv (by norm_num)
    rw [show (Δ φ) = fun x => iteratedFDeriv ℝ 2 φ x ![1, 1] + iteratedFDeriv ℝ 2 φ x ![I, I] from
      laplacian_eq_iteratedFDeriv_complexPlane φ]
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ ![1,1]).continuous.comp hcont).add
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ ![I,I]).continuous.comp hcont)
  obtain ⟨R, hR0, hR⟩ := hφc.exists_pos_le_norm
  have hΔloc : ∀ z : ℂ, R < ‖z‖ → Δ φ z = 0 := by
    intro z hz
    have hEZ : φ =ᶠ[𝓝 z] (fun _ => (0:ℝ)) :=
      eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
        (fun x hx => hR x (le_of_lt hx))
    rw [(laplacian_congr_nhds hEZ).eq_of_nhds]; simp
  have hΔc : HasCompactSupport (Δ φ) := HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall 0 R) (fun z hz => by
      rw [Function.mem_support] at hz; rw [Metric.mem_closedBall, dist_zero_right]
      by_contra h; exact hz (hΔloc z (by linarith [not_le.mp h])))
  obtain ⟨M, hM⟩ := hΔc.exists_bound_of_continuous hcΔ
  have hΔintM : Integrable (Δ φ) := hcΔ.integrable_of_hasCompactSupport hΔc
  set f : ℝ → ℂ → ℝ := fun r z => r⁻¹ • (Metric.ball (0:ℂ) r).indicator (Δ φ) z with hf
  have hfint : Integrable (Function.uncurry f) ((volume.restrict (Set.Ioo 0 R)).prod volume) :=
    layerCake_integrable φ hcΔ hM
  refine fundamentalSolution_centered_of_layerCake φ hφ hR0 (fun z hz => hR z (le_of_eq hz.symm)) ?_
  show (∫ z, Real.log ‖z‖ * Δ φ z) = -(∫ r in Set.Ioo 0 R, r⁻¹ * ∫ z in Metric.ball (0:ℂ) r, Δ φ z)
  have hstep1 : (∫ r in Set.Ioo 0 R, r⁻¹ * ∫ z in Metric.ball (0:ℂ) r, Δ φ z)
      = ∫ r in Set.Ioo 0 R, ∫ z, f r z := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r _
    show r⁻¹ * ∫ z in Metric.ball (0:ℂ) r, Δ φ z = ∫ z, r⁻¹ • (Metric.ball (0:ℂ) r).indicator (Δ φ) z
    rw [integral_smul, integral_indicator measurableSet_ball, smul_eq_mul]
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), 0 < ‖z‖ ∧ ‖z‖ ≠ R := by
    have ha : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := by
      rw [ae_iff]; simp only [not_ne_iff]
      rw [show {z : ℂ | z = 0} = {0} from by ext z; simp]; exact measure_singleton 0
    have hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖z‖ ≠ R := by
      rw [ae_iff]
      rw [show {z : ℂ | ¬ ‖z‖ ≠ R} = Metric.sphere 0 R from by ext z; simp]
      exact MeasureTheory.Measure.addHaar_sphere _ 0 R
    filter_upwards [ha, hb] with z hz hzR using ⟨norm_pos_iff.mpr hz, hzR⟩
  have hinner : (fun z => ∫ r in Set.Ioo 0 R, f r z) =ᵐ[volume]
      fun z => (Real.log R - Real.log ‖z‖) • Δ φ z := by
    filter_upwards [hae] with z ⟨hz0, hzR⟩
    rcases lt_or_gt_of_ne hzR with hlt | hgt
    · have hfe : (fun r => f r z) = fun r => (Set.Ioi ‖z‖).indicator (fun r => r⁻¹ • Δ φ z) r := by
        funext r
        simp only [hf, Set.indicator, Metric.mem_ball, dist_zero_right, Set.mem_Ioi, smul_ite, smul_zero]
      rw [hfe, setIntegral_indicator measurableSet_Ioi,
        show Set.Ioo (0:ℝ) R ∩ Set.Ioi ‖z‖ = Set.Ioo ‖z‖ R from by
          rw [Set.inter_comm, Set.Ioi_inter_Ioo, max_eq_left (norm_nonneg z)],
        integral_smul_const]
      congr 1
      rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le (le_of_lt hlt),
        integral_inv_of_pos hz0 (lt_trans hz0 hlt),
        Real.log_div (ne_of_gt (lt_trans hz0 hlt)) (ne_of_gt hz0)]
    · rw [setIntegral_congr_fun measurableSet_Ioo (fun r hr => by
        show r⁻¹ • (Metric.ball (0:ℂ) r).indicator (Δ φ) z = 0
        rw [Set.indicator_of_notMem (by
          simp only [Metric.mem_ball, dist_zero_right, not_lt]; linarith [hr.2]), smul_zero]),
        integral_zero, hΔloc z hgt, smul_zero]
  rw [hstep1, integral_integral_swap hfint, integral_congr_ae hinner]
  have hmarg : Integrable (fun z => (Real.log R - Real.log ‖z‖) • Δ φ z) :=
    (hfint.swap.integral_prod_left).congr hinner
  have heq2 : (fun z => (Real.log R - Real.log ‖z‖) • Δ φ z)
      = fun z => Real.log R * Δ φ z - Real.log ‖z‖ * Δ φ z := by
    funext z; rw [sub_smul, smul_eq_mul, smul_eq_mul]
  have hlogΔ : Integrable (fun z => Real.log ‖z‖ * Δ φ z) := by
    have h := (hΔintM.const_mul (Real.log R)).sub (heq2 ▸ hmarg)
    exact h.congr (Filter.Eventually.of_forall (fun z => by simp only [Pi.sub_apply]; ring))
  rw [heq2, integral_sub (hΔintM.const_mul _) hlogΔ, integral_const_mul,
    integral_laplacian_eq_zero φ hφ hφc, mul_zero, zero_sub, neg_neg]

/-- **GAP-A fundamental solution discharged:** `FundamentalSolutionProp` holds — the
`(2π)⁻¹Δ log‖·−ρ‖ = δ_ρ` identity, for every `C²` compact-support test function.  Combines
`fundamentalSolution_centered` with the translation reduction `fundamentalSolutionProp_of_center`. -/
theorem fundamentalSolutionProp_holds : FundamentalSolutionProp :=
  fundamentalSolutionProp_of_center fundamentalSolution_centered

end

end Bottcher

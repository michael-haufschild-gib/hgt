/-
# Böttcher tower — Brolin GAP-A: Green's first identity for the circle average

Toward the centered fundamental solution (`RieszFundamental.fundamentalSolutionProp_of_center`
reduces GAP-A to `∫ log‖z‖·Δφ = 2π·φ(0)`), this file builds the flux identity

  `∫_{ball 0 r} Δφ = 2π·r·M'(r)`,   `M(r) := circleAverage φ 0 r`,

i.e. the ball integral of the Laplacian equals the radial flux of the gradient
through the boundary circle (Green's first identity in the plane).

## The crux: rotation-invariance of the Laplacian

The Laplacian is the trace of the second derivative, hence independent of the
orthonormal frame.  Evaluating it in the *rotated* frame `{u, i·u}` (‖u‖ = 1)
splits `Δφ` into a radial (`u`) and a tangential (`i·u`) second derivative — the
planar-polar decomposition, obtained here from Mathlib's general
`laplacian_eq_iteratedFDeriv_orthonormalBasis` applied to the rotation of
`Complex.orthonormalBasisOneI` by `u ∈ Circle`.  This is `laplacian_rotated_frame`.

The remaining assembly (angular periodicity `∫∂²_θ = 0`; differentiation under the
integral for `M'`; polar reduction of the disk integral; FTC in the radius) is
built on top of this decomposition.
-/
import GaloisForLFunctions.Bottcher.Brolin.RieszFundamental
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter Topology MeasureTheory Laplacian InnerProductSpace Complex Real Set
open scoped Laplacian

namespace Bottcher

noncomputable section

/-- **Rotation-invariance of the planar Laplacian.** For any unit vector `u`
(`‖u‖ = 1`), the Laplacian at `p` is the sum of the second derivatives along the
orthonormal frame `{u, i·u}`:
`Δφ(p) = D²φ(p)[u,u] + D²φ(p)[i·u, i·u]`.
This is the polar (radial + tangential) decomposition of the Laplacian, the crux
of the Green's-identity / flux computation.  Proof: the Laplacian is a trace, so
`laplacian_eq_iteratedFDeriv_orthonormalBasis` evaluated in the rotated frame
`rotation u • {1, i}` gives the claim. -/
theorem laplacian_rotated_frame (φ : ℂ → ℝ) (p u : ℂ) (hu : ‖u‖ = 1) :
    Δ φ p = iteratedFDeriv ℝ 2 φ p ![u, u]
      + iteratedFDeriv ℝ 2 φ p ![I * u, I * u] := by
  have hmem : u ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.mpr hu
  have hb := laplacian_eq_iteratedFDeriv_orthonormalBasis φ
    (Complex.orthonormalBasisOneI.map (rotation ⟨u, hmem⟩))
  have h0 : (Complex.orthonormalBasisOneI.map (rotation ⟨u, hmem⟩)) 0 = u := by
    rw [OrthonormalBasis.map_apply, rotation_apply]
    simp [Complex.coe_orthonormalBasisOneI]
  have h1 : (Complex.orthonormalBasisOneI.map (rotation ⟨u, hmem⟩)) 1 = I * u := by
    rw [OrthonormalBasis.map_apply, rotation_apply]
    simp [Complex.coe_orthonormalBasisOneI, mul_comm]
  rw [hb]
  simp only [Fin.sum_univ_two, h0, h1]

/-- **Second-derivative bridge** (brick b2).  The order-2 iterated derivative is
the twice-applied Fréchet second derivative: `D²φ(p)[v,w] = (D(Dφ)(p) v) w`.
Connects the `iteratedFDeriv` form of `laplacian_rotated_frame` to the
`fderiv (fderiv φ)` form used in `tangential_periodicity`. -/
theorem iteratedFDeriv_two_eq_fderiv_fderiv (φ : ℂ → ℝ) (p v w : ℂ) :
    iteratedFDeriv ℝ 2 φ p ![v, w] = (fderiv ℝ (fderiv ℝ φ) p v) w := by
  rw [iteratedFDeriv_two_apply]; rfl

/-- `laplacian_rotated_frame` in the twice-applied-Fréchet form. -/
theorem laplacian_rotated_frame' (φ : ℂ → ℝ) (p u : ℂ) (hu : ‖u‖ = 1) :
    Δ φ p = (fderiv ℝ (fderiv ℝ φ) p u) u
      + (fderiv ℝ (fderiv ℝ φ) p (I * u)) (I * u) := by
  rw [laplacian_rotated_frame φ p u hu, iteratedFDeriv_two_eq_fderiv_fderiv,
    iteratedFDeriv_two_eq_fderiv_fderiv]

/-- **Polar reduction of the disk integral.** The planar integral over the disk
`ball 0 r` becomes the `(ρ,θ)` integral over `(0,r) × (-π,π)` with area weight
`ρ = p.1`.  Proof: extend by `0` (indicator) to the whole plane, apply the polar
change of variables `Complex.integral_comp_polarCoord_symm`, and restrict the
target to the sub-box cut out by `‖symm p‖ = |p.1| < r`. -/
theorem integral_ball_eq_polar (g : ℂ → ℝ) (r : ℝ) :
    (∫ z in Metric.ball (0:ℂ) r, g z) =
      ∫ p in Set.Ioo 0 r ×ˢ Set.Ioo (-π) π, p.1 • g (Complex.polarCoord.symm p) := by
  have hb : MeasurableSet (Metric.ball (0:ℂ) r) := measurableSet_ball
  have hS : MeasurableSet (Set.Ioo 0 r ×ˢ Set.Ioo (-π) π) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hSsub : Set.Ioo 0 r ×ˢ Set.Ioo (-π) π ⊆ Complex.polarCoord.target := by
    rw [Complex.polarCoord_target]; intro p hp; exact ⟨Ioo_subset_Ioi_self hp.1, hp.2⟩
  rw [← integral_indicator hb, ← Complex.integral_comp_polarCoord_symm
    ((Metric.ball (0:ℂ) r).indicator g)]
  calc ∫ p in Complex.polarCoord.target,
          p.1 • (Metric.ball (0:ℂ) r).indicator g (Complex.polarCoord.symm p)
      = ∫ p in Complex.polarCoord.target,
          (Set.Ioo 0 r ×ˢ Set.Ioo (-π) π).indicator
            (fun q => q.1 • g (Complex.polarCoord.symm q)) p := by
        refine setIntegral_congr_fun polarCoord.open_target.measurableSet ?_
        intro p hp
        rw [Complex.polarCoord_target] at hp
        by_cases hpr : p.1 < r
        · have hmem : Complex.polarCoord.symm p ∈ Metric.ball (0:ℂ) r := by
            rw [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp.1]
            exact hpr
          have hpS : p ∈ Set.Ioo 0 r ×ˢ Set.Ioo (-π) π := ⟨⟨hp.1, hpr⟩, hp.2⟩
          show p.1 • (Metric.ball (0:ℂ) r).indicator g (Complex.polarCoord.symm p) = _
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hpS]
        · have hmem : Complex.polarCoord.symm p ∉ Metric.ball (0:ℂ) r := by
            rw [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp.1]
            exact hpr
          have hpS : p ∉ Set.Ioo 0 r ×ˢ Set.Ioo (-π) π := fun h => hpr h.1.2
          show p.1 • (Metric.ball (0:ℂ) r).indicator g (Complex.polarCoord.symm p) = _
          rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hpS, smul_zero]
    _ = ∫ p in Complex.polarCoord.target ∩ (Set.Ioo 0 r ×ˢ Set.Ioo (-π) π),
          p.1 • g (Complex.polarCoord.symm p) := setIntegral_indicator hS
    _ = ∫ p in Set.Ioo 0 r ×ˢ Set.Ioo (-π) π, p.1 • g (Complex.polarCoord.symm p) := by
        rw [Set.inter_eq_right.mpr hSsub]

/-- **Radial first derivative.** Along the ray `s ↦ s·u`, the derivative of `φ` is
the directional derivative `Dφ(ρ·u)(u)`.  A straight-line chain rule: the ray
`s ↦ s • u` has derivative `u` (it is the span-singleton continuous linear map),
composed with `HasFDerivAt φ`. -/
theorem hasDerivAt_radial (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ) (u : ℂ) (ρ : ℝ) :
    HasDerivAt (fun s : ℝ => φ (s • u)) (fderiv ℝ φ (ρ • u) u) ρ := by
  have hcurve : HasDerivAt (fun s : ℝ => s • u) u ρ := by
    have h := ((ContinuousLinearMap.toSpanSingleton ℝ u).hasFDerivAt (x := ρ)).hasDerivAt
    simpa [ContinuousLinearMap.toSpanSingleton_apply] using h
  have hφd : HasFDerivAt φ (fderiv ℝ φ (ρ • u)) (ρ • u) :=
    (hφ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  simpa using hφd.comp_hasDerivAt ρ hcurve

/-- **Radius derivative of `circleMap`.** `∂_r (circleMap 0 r θ) = circleMap 0 1 θ = e^{iθ}`.
The map `r ↦ r·e^{iθ}` is linear in `r`, so its derivative is the unit vector `e^{iθ}`. -/
theorem hasDerivAt_circleMap_radius (θ r : ℝ) :
    HasDerivAt (fun s : ℝ => circleMap 0 s θ) (circleMap 0 1 θ) r := by
  have heq : (fun s : ℝ => circleMap 0 s θ) = fun s : ℝ => (s : ℂ) * Complex.exp (θ * I) := by
    funext s; simp [circleMap]
  rw [heq]
  simpa [circleMap] using (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (Complex.exp (θ * I))

/-- **Radius derivative of the profile** `s ↦ Dφ(circleMap 0 s θ)(circleMap 0 s θ)`
(the `h_diff` ingredient for differentiating `B(r) = 2πr·M'(r)` under the integral).
Product rule via `HasDerivAt.clm_apply` with `∂_s circleMap 0 s θ = circleMap 0 1 θ`. -/
theorem hasDerivAt_radialProfile (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (θ r : ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ φ (circleMap 0 s θ) (circleMap 0 s θ))
      ((fderiv ℝ (fderiv ℝ φ) (circleMap 0 r θ) (circleMap 0 1 θ)) (circleMap 0 r θ)
        + fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 1 θ)) r := by
  have hz : HasDerivAt (fun s : ℝ => circleMap 0 s θ) (circleMap 0 1 θ) r :=
    hasDerivAt_circleMap_radius θ r
  have hfd1 : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hc : HasDerivAt (fun s : ℝ => fderiv ℝ φ (circleMap 0 s θ))
      ((fderiv ℝ (fderiv ℝ φ) (circleMap 0 r θ)) (circleMap 0 1 θ)) r :=
    (hfd1 (circleMap 0 r θ)).hasFDerivAt.comp_hasDerivAt r hz
  exact hc.clm_apply hz

/-- **Tangential periodicity identity** (brick c — the crux).  Averaging over the
circle of radius `r`, the tangential second derivative equals the radial first
derivative applied to the radial vector:
`∫₀²π D²φ(z θ)[z θ·I, z θ·I] dθ = ∫₀²π Dφ(z θ)(z θ) dθ`,  `z θ := circleMap 0 r θ`.
Proof: the integrand difference is `g''(θ)` for `g(θ) = φ(circleMap 0 r θ)`
(computed by the CLM-apply product rule using `z''(θ) = -z(θ)`), and
`∫₀²π g''(θ) dθ = g'(2π) − g'(0) = 0` because `g'` is `2π`-periodic
(`periodic_circleMap`).  This is where the angular `∫ ∂²_θ = 0` cancellation of
the planar Laplacian's tangential part happens. -/
theorem tangential_periodicity (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (r : ℝ) :
    (∫ θ in (0:ℝ)..(2*π),
        (fderiv ℝ (fderiv ℝ φ) (circleMap 0 r θ) (circleMap 0 r θ * I)) (circleMap 0 r θ * I))
      = ∫ θ in (0:ℝ)..(2*π), fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 r θ) := by
  set z : ℝ → ℂ := circleMap 0 r with hzdef
  set G : ℝ → ℝ := fun θ => fderiv ℝ φ (z θ) (z θ * I) with hGdef
  set g2 : ℝ → ℝ := fun θ =>
    (fderiv ℝ (fderiv ℝ φ) (z θ) (z θ * I)) (z θ * I)
      + fderiv ℝ φ (z θ) ((z θ * I) * I) with hg2def
  have hfd1 : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hderiv : ∀ θ, HasDerivAt G (g2 θ) θ := by
    intro θ
    have hz : HasDerivAt z (z θ * I) θ := hasDerivAt_circleMap 0 r θ
    have hc : HasDerivAt (fun t : ℝ => fderiv ℝ φ (z t))
        ((fderiv ℝ (fderiv ℝ φ) (z θ)) (z θ * I)) θ :=
      (hfd1 (z θ)).hasFDerivAt.comp_hasDerivAt θ hz
    have hu : HasDerivAt (fun t : ℝ => z t * I) ((z θ * I) * I) θ := hz.mul_const I
    exact hc.clm_apply hu
  have hcz : Continuous z := continuous_circleMap 0 r
  have hcfd1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hcfd2 : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hint1 : IntervalIntegrable
      (fun θ => (fderiv ℝ (fderiv ℝ φ) (z θ) (z θ * I)) (z θ * I)) volume 0 (2*π) :=
    (((hcfd2.comp hcz).clm_apply (hcz.mul continuous_const)).clm_apply
      (hcz.mul continuous_const)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun θ => fderiv ℝ φ (z θ) ((z θ * I) * I)) volume 0 (2*π) :=
    ((hcfd1.comp hcz).clm_apply ((hcz.mul continuous_const).mul continuous_const)).intervalIntegrable _ _
  have hcg2 : Continuous g2 := by
    apply Continuous.add
    · exact ((hcfd2.comp hcz).clm_apply (hcz.mul continuous_const)).clm_apply (hcz.mul continuous_const)
    · exact (hcfd1.comp hcz).clm_apply ((hcz.mul continuous_const).mul continuous_const)
  have hFTC : (∫ θ in (0:ℝ)..(2*π), g2 θ) = G (2*π) - G 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
      (hcg2.intervalIntegrable _ _)
  have hper : G (2*π) = G 0 := by
    have hz0 : z (2*π) = z 0 := by
      have := (periodic_circleMap 0 r) 0
      simpa [hzdef, zero_add] using this
    simp only [hGdef, hz0]
  rw [hper, sub_self] at hFTC
  rw [intervalIntegral.integral_add hint1 hint2] at hFTC
  have hneg : (∫ θ in (0:ℝ)..(2*π), fderiv ℝ φ (z θ) ((z θ * I) * I))
      = - ∫ θ in (0:ℝ)..(2*π), fderiv ℝ φ (z θ) (z θ) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have hzz : (z θ * I) * I = - z θ := by ring_nf; rw [Complex.I_sq]; ring
    rw [hzz, map_neg]
  rw [hneg] at hFTC
  linarith [hFTC]

/-- **Differentiation under the integral for `B(r) = 2πr·M'(r)`** (brick d-B).
`B(r) = ∫₀²π Dφ(circleMap 0 r θ)(circleMap 0 r θ) dθ` is differentiable in `r`, with
`B'(r) = ∫₀²π ∂_r[Dφ(z)(z)] dθ` (the `hasDerivAt_radialProfile` integrand).  Proof via
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, dominating the
`r`-derivative by a constant obtained from continuity on the compact box
`closedBall r 1 × [0,2π]`. -/
theorem hasDerivAt_B (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (r : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ θ in (0:ℝ)..(2*π), fderiv ℝ φ (circleMap 0 s θ) (circleMap 0 s θ))
      (∫ θ in (0:ℝ)..(2*π),
        (fderiv ℝ (fderiv ℝ φ) (circleMap 0 r θ) (circleMap 0 1 θ)) (circleMap 0 r θ)
          + fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 1 θ)) r := by
  set F : ℝ → ℝ → ℝ := fun s θ => fderiv ℝ φ (circleMap 0 s θ) (circleMap 0 s θ) with hFdef
  set F' : ℝ → ℝ → ℝ := fun s θ =>
    (fderiv ℝ (fderiv ℝ φ) (circleMap 0 s θ) (circleMap 0 1 θ)) (circleMap 0 s θ)
      + fderiv ℝ φ (circleMap 0 s θ) (circleMap 0 1 θ) with hF'def
  have hcfd1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hcfd2 : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hcF : ∀ x, Continuous (F x) := fun x =>
    (hcfd1.comp (continuous_circleMap 0 x)).clm_apply (continuous_circleMap 0 x)
  have hcF' : ∀ x, Continuous (F' x) := fun x => by
    apply Continuous.add
    · exact ((hcfd2.comp (continuous_circleMap 0 x)).clm_apply
        (continuous_circleMap 0 1)).clm_apply (continuous_circleMap 0 x)
    · exact (hcfd1.comp (continuous_circleMap 0 x)).clm_apply (continuous_circleMap 0 1)
  have hcm : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    have heq : (fun p : ℝ × ℝ => circleMap 0 p.1 p.2)
        = fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * I) := by funext p; simp [circleMap]
    rw [heq]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hcF'p : Continuous (fun p : ℝ × ℝ => F' p.1 p.2) := by
    apply Continuous.add
    · exact ((hcfd2.comp hcm).clm_apply ((continuous_circleMap 0 1).comp continuous_snd)).clm_apply hcm
    · exact (hcfd1.comp hcm).clm_apply ((continuous_circleMap 0 1).comp continuous_snd)
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
    (Filter.Eventually.of_forall (fun θ _ x _ => hasDerivAt_radialProfile φ hφ θ x))
  exact key.2

/-- **Shell reduction of the disk integral** (brick d-A).  Fubini + `symm = circleMap`
turn `A(r) = ∫_{ball 0 r} Δφ` into the iterated `∫_{(0,r)} ρ·(∫_{(-π,π)} Δφ(circleMap 0 ρ θ)) dρ`.
Continuity of `Δφ` (`ContDiff ℝ 2`, via `laplacian_eq_iteratedFDeriv_complexPlane`) gives
integrability on the compact box. -/
theorem integral_ball_laplacian_eq_shell (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (r : ℝ) :
    (∫ z in Metric.ball (0:ℂ) r, Δ φ z)
      = ∫ ρ in Set.Ioo 0 r, ρ • ∫ θ in Set.Ioo (-π) π, Δ φ (circleMap 0 ρ θ) := by
  have hcΔ : Continuous (Δ φ) := by
    have hcont : Continuous (fun x => iteratedFDeriv ℝ 2 φ x) :=
      hφ.continuous_iteratedFDeriv (by norm_num)
    rw [show (Δ φ) = fun x => iteratedFDeriv ℝ 2 φ x ![1, 1] + iteratedFDeriv ℝ 2 φ x ![I, I] from
      laplacian_eq_iteratedFDeriv_complexPlane φ]
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ ![1,1]).continuous.comp hcont).add
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ ![I,I]).continuous.comp hcont)
  have hsymm : Continuous (Complex.polarCoord.symm : ℝ × ℝ → ℂ) := by
    have heq : (Complex.polarCoord.symm : ℝ × ℝ → ℂ) = fun p => circleMap 0 p.1 p.2 := by
      funext p; rw [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I,
        Complex.ofReal_cos, Complex.ofReal_sin]
    rw [heq, show (fun p : ℝ × ℝ => circleMap 0 p.1 p.2)
        = fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * I) from by funext p; simp [circleMap]]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  set f : ℝ × ℝ → ℝ := fun p => p.1 • Δ φ (Complex.polarCoord.symm p) with hfdef
  have hcf : Continuous f := continuous_fst.smul (hcΔ.comp hsymm)
  have hInt : IntegrableOn f (Set.Ioo 0 r ×ˢ Set.Ioo (-π) π) := by
    apply (hcf.continuousOn.integrableOn_compact
      ((isCompact_Icc (a := (0:ℝ)) (b := r)).prod (isCompact_Icc (a := -π) (b := π)))).mono_set
    exact Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hfub : (∫ p in Set.Ioo 0 r ×ˢ Set.Ioo (-π) π, f p)
      = ∫ ρ in Set.Ioo 0 r, ∫ θ in Set.Ioo (-π) π, f (ρ, θ) := setIntegral_prod f hInt
  rw [integral_ball_eq_polar (Δ φ) r, hfub]
  refine setIntegral_congr_fun measurableSet_Ioo (fun ρ _ => ?_)
  show (∫ θ in Set.Ioo (-π) π, ρ • Δ φ (Complex.polarCoord.symm (ρ, θ)))
      = ρ • ∫ θ in Set.Ioo (-π) π, Δ φ (circleMap 0 ρ θ)
  rw [integral_smul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  rw [show Complex.polarCoord.symm (ρ, θ) = circleMap 0 ρ θ from by
    rw [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin]]

/-- **Range reconciliation** for the shell integral (brick d-match, step 1).  For a
`2π`-periodic integrand the angular integral over `(-π,π)` (the polar chart range in
`integral_ball_laplacian_eq_shell`) equals the one over `0..2π` (the `circleAverage`
range in `hasDerivAt_B`). -/
theorem integral_Ioo_pi_eq_zero_two_pi {g : ℝ → ℝ} (hper : Function.Periodic g (2*π)) :
    (∫ θ in Set.Ioo (-π) π, g θ) = ∫ θ in (0:ℝ)..(2*π), g θ := by
  have h1 : (∫ θ in Set.Ioo (-π) π, g θ) = ∫ θ in (-π)..π, g θ := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    exact setIntegral_congr_set Ioo_ae_eq_Ioc
  rw [h1]
  have h2 := hper.intervalIntegral_add_eq (-π) 0
  rw [zero_add, show (-π) + 2*π = π by ring] at h2
  rw [h2]

/-- **(d-match): `B'(ρ)` equals the shell integrand** for `ρ > 0`.  The derivative
`B'(ρ) = ∫₀²π F'(ρ,θ)dθ` (from `hasDerivAt_B`) equals `ρ·∫_{(-π,π)} Δφ(circleMap 0 ρ θ)`
(the `integral_ball_laplacian_eq_shell` integrand).  Uses `z = ρ·w` (`w = circleMap 0 1 θ`,
`‖w‖=1`), `ContinuousLinearMap.map_smul` to factor `ρ`, `laplacian_rotated_frame'` (K1′)
pointwise, the range bridge, and `tangential_periodicity` (c) at radius `ρ` divided by `ρ`. -/
theorem hasDerivAt_B_eq_shell (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ θ in (0:ℝ)..(2*π),
        (fderiv ℝ (fderiv ℝ φ) (circleMap 0 ρ θ) (circleMap 0 1 θ)) (circleMap 0 ρ θ)
          + fderiv ℝ φ (circleMap 0 ρ θ) (circleMap 0 1 θ))
      = ρ • ∫ θ in Set.Ioo (-π) π, Δ φ (circleMap 0 ρ θ) := by
  set z : ℝ → ℂ := circleMap 0 ρ with hz
  set w : ℝ → ℂ := circleMap 0 1 with hw
  have hzw : ∀ θ, z θ = ρ • w θ := fun θ => by simp [hz, hw, circleMap, Complex.real_smul]
  have hw1 : ∀ θ, ‖w θ‖ = 1 := fun θ => by
    show ‖circleMap 0 1 θ‖ = 1; rw [norm_circleMap_zero]; norm_num
  set a : ℝ → ℝ := fun θ => (fderiv ℝ (fderiv ℝ φ) (z θ) (w θ)) (w θ) with ha
  set b : ℝ → ℝ := fun θ => (fderiv ℝ (fderiv ℝ φ) (z θ) (I * w θ)) (I * w θ) with hb
  set cc : ℝ → ℝ := fun θ => fderiv ℝ φ (z θ) (w θ) with hcc
  have hcfd1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hcfd2 : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hcz : Continuous z := continuous_circleMap 0 ρ
  have hcw : Continuous w := continuous_circleMap 0 1
  have hca : Continuous a := ((hcfd2.comp hcz).clm_apply hcw).clm_apply hcw
  have hcb : Continuous b :=
    ((hcfd2.comp hcz).clm_apply (continuous_const.mul hcw)).clm_apply (continuous_const.mul hcw)
  have hccc : Continuous cc := (hcfd1.comp hcz).clm_apply hcw
  have hLHS : (∫ θ in (0:ℝ)..(2*π),
      (fderiv ℝ (fderiv ℝ φ) (z θ) (w θ)) (z θ) + fderiv ℝ φ (z θ) (w θ))
      = (ρ • ∫ θ in (0:ℝ)..(2*π), a θ) + ∫ θ in (0:ℝ)..(2*π), cc θ := by
    rw [show (fun θ => (fderiv ℝ (fderiv ℝ φ) (z θ) (w θ)) (z θ) + fderiv ℝ φ (z θ) (w θ))
        = fun θ => ρ • a θ + cc θ from by
      funext θ
      congr 1
      rw [congrArg (fderiv ℝ (fderiv ℝ φ) (z θ) (w θ)) (hzw θ), ContinuousLinearMap.map_smul]]
    rw [intervalIntegral.integral_add ((hca.const_smul ρ).intervalIntegrable _ _)
      (hccc.intervalIntegrable _ _), intervalIntegral.integral_smul]
  have hper : Function.Periodic (fun θ => Δ φ (z θ)) (2*π) :=
    fun θ => congrArg (Δ φ) (by rw [hz]; exact periodic_circleMap 0 ρ θ)
  have hRHS : (ρ • ∫ θ in Set.Ioo (-π) π, Δ φ (z θ))
      = (ρ • ∫ θ in (0:ℝ)..(2*π), a θ) + ρ • ∫ θ in (0:ℝ)..(2*π), b θ := by
    rw [integral_Ioo_pi_eq_zero_two_pi hper]
    rw [show (fun θ => Δ φ (z θ)) = fun θ => a θ + b θ from by
      funext θ; exact laplacian_rotated_frame' φ (z θ) (w θ) (hw1 θ)]
    rw [intervalIntegral.integral_add (hca.intervalIntegrable _ _) (hcb.intervalIntegrable _ _),
      smul_add]
  rw [hLHS, hRHS]
  have hIII : (∫ θ in (0:ℝ)..(2*π), cc θ) = ρ • ∫ θ in (0:ℝ)..(2*π), b θ := by
    have hc := tangential_periodicity φ hφ ρ
    have hcL : (∫ θ in (0:ℝ)..(2*π),
        (fderiv ℝ (fderiv ℝ φ) (z θ) (z θ * I)) (z θ * I))
        = ρ • ρ • ∫ θ in (0:ℝ)..(2*π), b θ := by
      rw [show (fun θ => (fderiv ℝ (fderiv ℝ φ) (z θ) (z θ * I)) (z θ * I))
          = fun θ => ρ • ρ • b θ from by
        funext θ
        have hzi : z θ * I = ρ • (I * w θ) := by rw [hzw θ]; simp only [Complex.real_smul]; ring
        rw [hzi, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul,
          _root_.smul_apply]]
      rw [intervalIntegral.integral_smul, intervalIntegral.integral_smul]
    have hcR : (∫ θ in (0:ℝ)..(2*π), fderiv ℝ φ (z θ) (z θ))
        = ρ • ∫ θ in (0:ℝ)..(2*π), cc θ := by
      rw [show (fun θ => fderiv ℝ φ (z θ) (z θ)) = fun θ => ρ • cc θ from by
        funext θ
        rw [congrArg (fderiv ℝ φ (z θ)) (hzw θ), ContinuousLinearMap.map_smul]]
      rw [intervalIntegral.integral_smul]
    rw [hcL, hcR] at hc
    have hcm : ρ * (ρ * ∫ θ in (0:ℝ)..(2*π), b θ) = ρ * ∫ θ in (0:ℝ)..(2*π), cc θ := by
      simpa [smul_eq_mul] using hc
    have := mul_left_cancel₀ hρ.ne' hcm
    rw [smul_eq_mul]; linarith [this]
  rw [hIII]

/-- **Green's first identity for the planar Laplacian** (the flux identity, brick d
assembled).  For `r ≥ 0`,
`∫_{ball 0 r} Δφ = ∫₀²π Dφ(circleMap 0 r θ)(circleMap 0 r θ) dθ`.
The right side is `2π·r·M'(r)` with `M(r) = circleAverage φ 0 r` (since
`∂_r φ(circleMap 0 r θ) = Dφ(z)(circleMap 0 1 θ)` and `z = r·(circleMap 0 1 θ)`), so this
is the ball-integral-of-Laplacian = boundary-flux statement.  Proof: shell reduction
(`integral_ball_laplacian_eq_shell`) + FTC in `r` (`hasDerivAt_B`, `B 0 = 0`, parametric-
integral continuity) + the shell-equals-derivative match (`hasDerivAt_B_eq_shell`). -/
theorem integral_ball_laplacian_eq_boundary_flux
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ z in Metric.ball (0:ℂ) r, Δ φ z)
      = ∫ θ in (0:ℝ)..(2*π), fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 r θ) := by
  set F' : ℝ → ℝ → ℝ := fun s θ =>
    (fderiv ℝ (fderiv ℝ φ) (circleMap 0 s θ) (circleMap 0 1 θ)) (circleMap 0 s θ)
      + fderiv ℝ φ (circleMap 0 s θ) (circleMap 0 1 θ) with hF'
  have hcfd1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hcfd2 : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hcm : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    have heq : (fun p : ℝ × ℝ => circleMap 0 p.1 p.2)
        = fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * I) := by funext p; simp [circleMap]
    rw [heq]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hcF'p : Continuous (Function.uncurry F') := by
    apply Continuous.add
    · exact ((hcfd2.comp hcm).clm_apply
        ((continuous_circleMap 0 1).comp continuous_snd)).clm_apply hcm
    · exact (hcfd1.comp hcm).clm_apply ((continuous_circleMap 0 1).comp continuous_snd)
  have hB'cont : Continuous (fun ρ => ∫ θ in (0:ℝ)..(2*π), F' ρ θ) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcF'p 0 (2*π)
  have hFTC : (∫ ρ in (0:ℝ)..r, ∫ θ in (0:ℝ)..(2*π), F' ρ θ)
      = (∫ θ in (0:ℝ)..(2*π), fderiv ℝ φ (circleMap 0 r θ) (circleMap 0 r θ))
        - (∫ θ in (0:ℝ)..(2*π), fderiv ℝ φ (circleMap 0 0 θ) (circleMap 0 0 θ)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ρ _ => hasDerivAt_B φ hφ ρ)
      (hB'cont.intervalIntegrable 0 r)
  have hB0 : (∫ θ in (0:ℝ)..(2*π), fderiv ℝ φ (circleMap 0 0 θ) (circleMap 0 0 θ)) = 0 := by
    rw [show (fun θ => fderiv ℝ φ (circleMap 0 0 θ) (circleMap 0 0 θ)) = fun _ => (0:ℝ) from by
      funext θ; simp [circleMap]]
    simp
  rw [hB0, sub_zero] at hFTC
  rw [integral_ball_laplacian_eq_shell φ hφ r, ← hFTC,
    intervalIntegral.integral_of_le hr, ← setIntegral_congr_set Ioo_ae_eq_Ioc]
  refine setIntegral_congr_fun measurableSet_Ioo (fun ρ hρ => ?_)
  exact (hasDerivAt_B_eq_shell φ hφ hρ.1).symm

end

end Bottcher

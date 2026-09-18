import GaloisForLFunctions.RHTower.PrimeGammaCauchyCubicLaplaceGram
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolApertureDefectColligation
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolApertureDampingSemigroup
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolMatrixCompleteColligation
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolMeasurablePairingColligation
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolWardResolvedGeneratorGraph
import GaloisForLFunctions.RHTower.SPEQuantileRieszSourceTransport
import Mathlib.MeasureTheory.Integral.Prod

/-!
# SP-E endpoint ray-Laplace port

The literal SP-E Riesz profile is a finite interval superposition of the Route-P cubic ray
features, evaluated at its signed distance from the physical endpoint.  This has the required
simple endpoint zero and is therefore distinct from the already excluded bulk aperture
superposition.  The theorem is an analytic port only: a source-faithful signed history lift still
has to preserve the free-word action rather than collapse it to this scalar test functional.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-- Integrating the cubic Route-P ray feature over the endpoint scale interval gives the exact
difference of endpoint exponentials. -/
theorem integral_primeGammaCauchyCubicRayFeature_half_one (u : ℝ) :
    (∫ s in (1 / 2 : ℝ)..1, primeGammaCauchyCubicRayFeature s u) =
      Real.exp (-(u / 2)) - Real.exp (-u) := by
  by_cases hu : u = 0
  · simp [hu, primeGammaCauchyCubicRayFeature]
  unfold primeGammaCauchyCubicRayFeature
  rw [intervalIntegral.integral_const_mul]
  have hcomp := intervalIntegral.integral_comp_mul_left
    (fun x : ℝ => Real.exp x) (a := (1 / 2 : ℝ)) (b := 1) (c := -u) (neg_ne_zero.mpr hu)
  have hrewrite : (fun x : ℝ => Real.exp (-(x * u))) =
      fun x => Real.exp ((-u) * x) := by
    funext x
    congr 1
    ring
  rw [hrewrite, hcomp, integral_exp]
  simp only [smul_eq_mul, mul_one]
  change u * ((-u)⁻¹ *
      (Real.exp (-u) - Real.exp ((-u) * (1 / 2)))) =
    Real.exp (-(u / 2)) - Real.exp (-u)
  field_simp [hu]
  ring

/-- Complexified SP-E endpoint ray, viewed as a literal positive-aperture P feature. -/
def primeGammaCauchyCubicComplexRayFeature (s : ℝ) : ℝ → ℂ :=
  fun u => (primeGammaCauchyCubicRayFeature s u : ℂ)

/-- After complexification, the SP-E endpoint ray feature is exactly P-G197's common radial
position-generator mode.  Thus the endpoint port enters the cubic Ward graph carrier directly,
rather than through a bounded base-Hardy surrogate. -/
theorem primeGammaCauchyCubicRayFeature_eq_xiWardResolvedRadialGeneratorMode
    (s u : ℝ) :
    (primeGammaCauchyCubicRayFeature s u : ℂ) =
      _root_.RHTower.xiWardResolvedRadialGeneratorMode (s : ℂ) u := by
  rw [primeGammaCauchyCubicRayFeature,
    _root_.RHTower.xiWardResolvedRadialGeneratorMode,
    _root_.RHTower.xiWardResolvedRadialMode]
  push_cast
  rfl

/-- The complexified SP-E ray is the P-G197 generator mode pointwise. -/
theorem primeGammaCauchyCubicComplexRayFeature_eq_xiWardResolvedRadialGeneratorMode
    (s u : ℝ) :
    primeGammaCauchyCubicComplexRayFeature s u =
      _root_.RHTower.xiWardResolvedRadialGeneratorMode (s : ℂ) u :=
  primeGammaCauchyCubicRayFeature_eq_xiWardResolvedRadialGeneratorMode s u

/-- Complexified endpoint rays are continuous P-aperture data. -/
theorem continuous_primeGammaCauchyCubicComplexRayFeature (s : ℝ) :
    Continuous (primeGammaCauchyCubicComplexRayFeature s) := by
  unfold primeGammaCauchyCubicComplexRayFeature primeGammaCauchyCubicRayFeature
  fun_prop

/-- Every positive-scale complexified endpoint ray has finite P-aperture energy. -/
theorem integrableOn_norm_sq_primeGammaCauchyCubicComplexRayFeature
    (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => ‖primeGammaCauchyCubicComplexRayFeature s u‖ ^ 2) (Ioi 0) := by
  have hbase : IntegrableOn
      (fun u : ℝ => u ^ 2 * Real.exp (-(2 * s) * u)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (2 : ℝ)) (p := (1 : ℝ)) (b := 2 * s)
      (by norm_num) (by norm_num) (by positivity)
    simpa [Real.rpow_two, Real.rpow_one] using h
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro u _
  change u ^ 2 * Real.exp (-(2 * s) * u) =
    ‖primeGammaCauchyCubicComplexRayFeature s u‖ ^ 2
  symm
  rw [primeGammaCauchyCubicComplexRayFeature_eq_xiWardResolvedRadialGeneratorMode,
    _root_.RHTower.norm_xiWardResolvedRadialGeneratorMode_sq]
  congr 2
  ring

/-- Every complexified SP-E endpoint ray is an exact eigenmode of P-G187's literal weighted
aperture shift.  Hence its missing energy is governed by P-G188's physical defect channels, not
by a postulated contraction. -/
theorem primeGammaCauchyCubicRayFeature_forwardDampingShift_eigenmode
    {c L : ℝ} (hc : 0 ≤ c) (hL : 0 < L) (s : ℝ) :
    _root_.RHTower.routePBurnolForwardDampingShift c
        (fun u : ℝ => (primeGammaCauchyCubicRayFeature s u : ℂ)) L =
      Complex.exp (-((c : ℂ) * (s : ℂ))) *
        (primeGammaCauchyCubicRayFeature s L : ℂ) := by
  rw [_root_.RHTower.routePBurnolForwardDampingShift,
    primeGammaCauchyCubicRayFeature, primeGammaCauchyCubicRayFeature]
  push_cast
  have hLc : L + c ≠ 0 := by linarith
  have hLcC : (L : ℂ) + (c : ℂ) ≠ 0 := by exact_mod_cast hLc
  have hscale : ((L : ℂ) / ((L : ℂ) + (c : ℂ))) *
      ((L : ℂ) + (c : ℂ)) = (L : ℂ) := by
    field_simp [hLcC]
  have hexp : -((s : ℂ) * ((L : ℂ) + (c : ℂ))) =
      -((c : ℂ) * (s : ℂ)) + -((s : ℂ) * (L : ℂ)) := by ring
  rw [hexp, Complex.exp_add]
  rw [← mul_assoc, hscale]
  ring

/-- **Exact SP-E/P-G188 defect entry.** Every endpoint ray with positive aperture scale has
P-G188's literal transported, boundary, and tail energy colligation.  The exponential
parameterization makes the theorem premise-free. -/
theorem primeGammaCauchyCubicComplexRayFeature_aperture_energy_colligation (r q : ℝ) :
    _root_.RHTower.routePBurnolApertureEnergy
        (_root_.RHTower.routePBurnolForwardDampingShift (Real.exp r)
          (primeGammaCauchyCubicComplexRayFeature (Real.exp q))) +
      _root_.RHTower.routePBurnolApertureEnergy
        (_root_.RHTower.routePBurnolApertureBoundaryDefect (Real.exp r)
          (primeGammaCauchyCubicComplexRayFeature (Real.exp q))) +
      _root_.RHTower.routePBurnolApertureEnergy
        (_root_.RHTower.routePBurnolApertureTailDefect (Real.exp r)
          (primeGammaCauchyCubicComplexRayFeature (Real.exp q))) =
      _root_.RHTower.routePBurnolApertureEnergy
        (primeGammaCauchyCubicComplexRayFeature (Real.exp q)) := by
  exact _root_.RHTower.routePBurnolApertureDamping_energy_colligation
    (Real.exp_nonneg r)
    (continuous_primeGammaCauchyCubicComplexRayFeature _)
    (integrableOn_norm_sq_primeGammaCauchyCubicComplexRayFeature _ (Real.exp_pos q))

/-- **Exact SP-E/P-G194 signed entry.** P-G188's three defect channels preserve the full
sesquilinear pairing of every two endpoint rays.  This is the usable form for the signed
physical-wall current: its cross terms are retained instead of being replaced by diagonal energy. -/
theorem primeGammaCauchyCubicComplexRayFeature_aperture_pairing_colligation
    (r q₁ q₂ : ℝ) :
    _root_.RHTower.routePBurnolHalfLinePairing
        (_root_.RHTower.routePBurnolForwardDampingShift (Real.exp r)
          (primeGammaCauchyCubicComplexRayFeature (Real.exp q₁)))
        (_root_.RHTower.routePBurnolForwardDampingShift (Real.exp r)
          (primeGammaCauchyCubicComplexRayFeature (Real.exp q₂))) +
      _root_.RHTower.routePBurnolHalfLinePairing
        (_root_.RHTower.routePBurnolApertureBoundaryDefect (Real.exp r)
          (primeGammaCauchyCubicComplexRayFeature (Real.exp q₁)))
        (_root_.RHTower.routePBurnolApertureBoundaryDefect (Real.exp r)
          (primeGammaCauchyCubicComplexRayFeature (Real.exp q₂))) +
      _root_.RHTower.routePBurnolHalfLinePairing
        (_root_.RHTower.routePBurnolApertureTailDefect (Real.exp r)
          (primeGammaCauchyCubicComplexRayFeature (Real.exp q₁)))
        (_root_.RHTower.routePBurnolApertureTailDefect (Real.exp r)
          (primeGammaCauchyCubicComplexRayFeature (Real.exp q₂))) =
      _root_.RHTower.routePBurnolHalfLinePairing
        (primeGammaCauchyCubicComplexRayFeature (Real.exp q₁))
        (primeGammaCauchyCubicComplexRayFeature (Real.exp q₂)) := by
  exact _root_.RHTower.routePBurnolApertureDamping_pairing_colligation
    (Real.exp_nonneg r)
    (continuous_primeGammaCauchyCubicComplexRayFeature _)
    (continuous_primeGammaCauchyCubicComplexRayFeature _)
    (integrableOn_norm_sq_primeGammaCauchyCubicComplexRayFeature _ (Real.exp_pos q₁))
    (integrableOn_norm_sq_primeGammaCauchyCubicComplexRayFeature _ (Real.exp_pos q₂))

/-- The source-forced SP-E profile is precisely a finite positive-scale superposition of the
Route-P ray feature at endpoint distance `log M - h`. -/
theorem speQuantileRieszProfile_eq_endpointRayLaplace
    {M : ℕ} (hM : 0 < M) (h : ℝ) :
    _root_.RHTower.speQuantileRieszProfile M h =
      2 * (M : ℝ) *
        ∫ s in (1 / 2 : ℝ)..1,
          primeGammaCauchyCubicRayFeature s (Real.log M - h) := by
  rw [integral_primeGammaCauchyCubicRayFeature_half_one]
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hsqrt : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMR
  have hhalf : Real.exp (Real.log (M : ℝ) / 2) = Real.sqrt (M : ℝ) := by
    rw [← Real.log_sqrt hMR.le, Real.exp_log hsqrt]
  have hfirst :
      (M : ℝ) * Real.exp (-((Real.log M - h) / 2)) =
        Real.sqrt (M : ℝ) * Real.exp (h / 2) := by
    calc
      (M : ℝ) * Real.exp (-((Real.log M - h) / 2)) =
          Real.exp (Real.log (M : ℝ)) *
            Real.exp (-((Real.log M - h) / 2)) := by rw [Real.exp_log hMR]
      _ = Real.exp (Real.log (M : ℝ) + -((Real.log M - h) / 2)) := by
        rw [← Real.exp_add]
      _ = Real.exp (Real.log (M : ℝ) / 2 + h / 2) := by
        congr 1
        ring
      _ = Real.exp (Real.log (M : ℝ) / 2) * Real.exp (h / 2) := by
        rw [Real.exp_add]
      _ = Real.sqrt (M : ℝ) * Real.exp (h / 2) := by rw [hhalf]
  have hsecond :
      (M : ℝ) * Real.exp (-(Real.log M - h)) = Real.exp h := by
    calc
      (M : ℝ) * Real.exp (-(Real.log M - h)) =
          Real.exp (Real.log (M : ℝ)) * Real.exp (-(Real.log M - h)) := by
            rw [Real.exp_log hMR]
      _ = Real.exp (Real.log (M : ℝ) + -(Real.log M - h)) := by rw [← Real.exp_add]
      _ = Real.exp h := by
        congr 1
        ring
  unfold _root_.RHTower.speQuantileRieszProfile
  calc
    2 * (Real.sqrt (M : ℝ) * Real.exp (h / 2) - Real.exp h) =
        2 * ((M : ℝ) * Real.exp (-((Real.log M - h) / 2)) -
          (M : ℝ) * Real.exp (-(Real.log M - h))) := by rw [hfirst, hsecond]
    _ = 2 * (M : ℝ) *
        (Real.exp (-((Real.log M - h) / 2)) - Real.exp (-(Real.log M - h)) ) := by ring

/-- After the physical-wall change of coordinate `u = log M - h`, the *weighted* SP-E density
is a positive scale superposition of the same P cubic rays, shifted from `[1/2,1]` to
`[1,3/2]`.  The shift is forced by the literal parabolic weight `exp (h/2)`. -/
theorem exp_half_mul_speQuantileRieszProfile_eq_shiftedEndpointRayLaplace
    {M : ℕ} (hM : 0 < M) (h : ℝ) :
    Real.exp (h / 2) * _root_.RHTower.speQuantileRieszProfile M h =
      2 * (M : ℝ) * Real.sqrt (M : ℝ) *
        ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
          primeGammaCauchyCubicRayFeature s (Real.log M - h) := by
  let u : ℝ := Real.log M - h
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hsqrt : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMR
  have hhalf : Real.exp (Real.log (M : ℝ) / 2) = Real.sqrt (M : ℝ) := by
    rw [← Real.log_sqrt hMR.le, Real.exp_log hsqrt]
  have hweight : Real.exp (h / 2) =
      Real.sqrt (M : ℝ) * Real.exp (-(u / 2)) := by
    calc
      Real.exp (h / 2) =
          Real.exp (Real.log (M : ℝ) / 2) * Real.exp (-(u / 2)) := by
            rw [← Real.exp_add]
            congr 1
            dsimp [u]
            ring
      _ = Real.sqrt (M : ℝ) * Real.exp (-(u / 2)) := by rw [hhalf]
  have hshift :
      (∫ s in (1 / 2 : ℝ)..1,
        Real.exp (-(u / 2)) * primeGammaCauchyCubicRayFeature s u) =
      ∫ s in (1 : ℝ)..(3 / 2 : ℝ), primeGammaCauchyCubicRayFeature s u := by
    calc
      (∫ s in (1 / 2 : ℝ)..1,
        Real.exp (-(u / 2)) * primeGammaCauchyCubicRayFeature s u) =
          ∫ s in (1 / 2 : ℝ)..1,
            primeGammaCauchyCubicRayFeature (s + 1 / 2) u := by
              apply intervalIntegral.integral_congr
              intro s _
              unfold primeGammaCauchyCubicRayFeature
              change Real.exp (-(u / 2)) * (u * Real.exp (-(s * u))) =
                u * Real.exp (-((s + 1 / 2) * u))
              calc
                Real.exp (-(u / 2)) * (u * Real.exp (-(s * u))) =
                    u * (Real.exp (-(u / 2)) * Real.exp (-(s * u))) := by ring
                _ = u * Real.exp (-(u / 2) + -(s * u)) := by rw [← Real.exp_add]
                _ = u * Real.exp (-((s + 1 / 2) * u)) := by
                  congr 1
                  ring
      _ = ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
          primeGammaCauchyCubicRayFeature s u := by
            have hlow : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
            have hhigh : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
            simpa only [hlow, hhigh] using
              intervalIntegral.integral_comp_add_right (a := (1 / 2 : ℝ)) (b := 1)
                (fun s : ℝ => primeGammaCauchyCubicRayFeature s u) (1 / 2 : ℝ)
  rw [speQuantileRieszProfile_eq_endpointRayLaplace hM h, hweight]
  calc
    (Real.sqrt (M : ℝ) * Real.exp (-(u / 2))) *
        (2 * (M : ℝ) *
          ∫ s in (1 / 2 : ℝ)..1, primeGammaCauchyCubicRayFeature s u) =
        2 * (M : ℝ) * Real.sqrt (M : ℝ) *
          (Real.exp (-(u / 2)) *
            ∫ s in (1 / 2 : ℝ)..1, primeGammaCauchyCubicRayFeature s u) := by ring
    _ =
        2 * (M : ℝ) * Real.sqrt (M : ℝ) *
          (∫ s in (1 / 2 : ℝ)..1,
            Real.exp (-(u / 2)) * primeGammaCauchyCubicRayFeature s u) := by
              rw [← intervalIntegral.integral_const_mul]
    _ = 2 * (M : ℝ) * Real.sqrt (M : ℝ) *
        ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
          primeGammaCauchyCubicRayFeature s u := by rw [hshift]

/-- **SP-E/P two-port identity.** Every literal oriented SP-E height interval is an exact
P pairing port: after `u = log M - h`, its weighted Riesz transport is the scale integral of
the P cubic ray against its reversed physical interval.  This retains endpoints and orientation;
it does not replace the source interval by a scalar. -/
theorem speQuantileRieszWeightedIntervalIntegral_eq_endpointRayTwoPort
    {M : ℕ} (hM : 0 < M) (a b : ℝ) :
    (∫ h in a..b,
      Real.exp (h / 2) * _root_.RHTower.speQuantileRieszProfile M h) =
      2 * (M : ℝ) * Real.sqrt (M : ℝ) *
        ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
          ∫ u in Real.log M - b..Real.log M - a,
            primeGammaCauchyCubicRayFeature s u := by
  let F : ℝ → ℝ → ℝ := fun h s =>
    primeGammaCauchyCubicRayFeature s (Real.log M - h)
  have hFcont : Continuous (Function.uncurry F) := by
    dsimp only [F, Function.uncurry]
    unfold primeGammaCauchyCubicRayFeature
    fun_prop
  have hFint : IntegrableOn (Function.uncurry F)
      (uIoc a b ×ˢ uIoc (1 : ℝ) (3 / 2 : ℝ)) := by
    have hcompact : IntegrableOn (Function.uncurry F)
        (uIcc a b ×ˢ uIcc (1 : ℝ) (3 / 2 : ℝ)) :=
      hFcont.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
    exact hcompact.mono_set (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  calc
    (∫ h in a..b,
      Real.exp (h / 2) * _root_.RHTower.speQuantileRieszProfile M h) =
        ∫ h in a..b,
          2 * (M : ℝ) * Real.sqrt (M : ℝ) *
            ∫ s in (1 : ℝ)..(3 / 2 : ℝ), F h s := by
              apply intervalIntegral.integral_congr
              intro h _
              simpa only [F] using
                exp_half_mul_speQuantileRieszProfile_eq_shiftedEndpointRayLaplace hM h
    _ = 2 * (M : ℝ) * Real.sqrt (M : ℝ) *
        (∫ h in a..b, ∫ s in (1 : ℝ)..(3 / 2 : ℝ), F h s) := by
          rw [intervalIntegral.integral_const_mul]
    _ = 2 * (M : ℝ) * Real.sqrt (M : ℝ) *
        (∫ s in (1 : ℝ)..(3 / 2 : ℝ), ∫ h in a..b, F h s) := by
          rw [intervalIntegral_intervalIntegral_swap hFint]
    _ = 2 * (M : ℝ) * Real.sqrt (M : ℝ) *
        ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
          ∫ u in Real.log M - b..Real.log M - a,
            primeGammaCauchyCubicRayFeature s u := by
          apply congrArg (fun z : ℝ => 2 * (M : ℝ) * Real.sqrt (M : ℝ) * z)
          apply intervalIntegral.integral_congr
          intro s _
          simpa only [F] using
            intervalIntegral.integral_comp_sub_left
              (fun u : ℝ => primeGammaCauchyCubicRayFeature s u) (Real.log M)

/-- Literal second P-port for a positive endpoint interval.  It is an oriented physical interval,
not an auxiliary test vector. -/
def primeGammaCauchyCubicPositiveIntervalPort (U : ℝ) : ℝ → ℂ :=
  (Ioc (0 : ℝ) U).indicator (fun _ => (1 : ℂ))

/-- The literal finite interval port is measurable on P's physical half-line. -/
theorem aestronglyMeasurable_primeGammaCauchyCubicPositiveIntervalPort (U : ℝ) :
    AEStronglyMeasurable (primeGammaCauchyCubicPositiveIntervalPort U)
      (volume.restrict (Ioi (0 : ℝ))) := by
  exact (measurable_const.indicator measurableSet_Ioc).aestronglyMeasurable.restrict

/-- The literal finite interval port has finite P-aperture energy, with no smoothing of its
two source endpoints. -/
theorem integrableOn_norm_sq_primeGammaCauchyCubicPositiveIntervalPort (U : ℝ) :
    IntegrableOn (fun u : ℝ =>
      ‖primeGammaCauchyCubicPositiveIntervalPort U u‖ ^ 2) (Ioi (0 : ℝ)) := by
  have hnorm : (fun u : ℝ =>
      ‖primeGammaCauchyCubicPositiveIntervalPort U u‖ ^ 2) =
      (Ioc (0 : ℝ) U).indicator (fun _ => (1 : ℝ)) := by
    funext u
    by_cases hu : u ∈ Ioc (0 : ℝ) U <;>
      simp [primeGammaCauchyCubicPositiveIntervalPort, hu]
  rw [hnorm]
  have hglobal : Integrable ((Ioc (0 : ℝ) U).indicator (fun _ => (1 : ℝ))) := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const measure_Ioc_lt_top.ne
  exact hglobal.integrableOn

/-- Reflected finite P port for the part of an SP-E interval beyond its physical wall.  Its scale
is negative before truncation, so this is deliberately a compact defect port rather than a
global P eigenray. -/
def primeGammaCauchyCubicReflectedWallRayPort (s L : ℝ) : ℝ → ℂ :=
  (Ioc (0 : ℝ) L).indicator (primeGammaCauchyCubicComplexRayFeature (-s))

theorem aestronglyMeasurable_primeGammaCauchyCubicReflectedWallRayPort (s L : ℝ) :
    AEStronglyMeasurable (primeGammaCauchyCubicReflectedWallRayPort s L)
      (volume.restrict (Ioi (0 : ℝ))) := by
  exact ((continuous_primeGammaCauchyCubicComplexRayFeature (-s)).measurable.indicator
    measurableSet_Ioc).aestronglyMeasurable.restrict

theorem integrableOn_norm_sq_primeGammaCauchyCubicReflectedWallRayPort (s L : ℝ) :
    IntegrableOn (fun u : ℝ =>
      ‖primeGammaCauchyCubicReflectedWallRayPort s L u‖ ^ 2) (Ioi (0 : ℝ)) := by
  have hnorm : (fun u : ℝ =>
      ‖primeGammaCauchyCubicReflectedWallRayPort s L u‖ ^ 2) =
      (Ioc (0 : ℝ) L).indicator
        (fun u => ‖primeGammaCauchyCubicComplexRayFeature (-s) u‖ ^ 2) := by
    funext u
    by_cases hu : u ∈ Ioc (0 : ℝ) L <;>
      simp [primeGammaCauchyCubicReflectedWallRayPort, hu]
  rw [hnorm]
  have hcont : Continuous (fun u : ℝ =>
      ‖primeGammaCauchyCubicComplexRayFeature (-s) u‖ ^ 2) :=
    ((continuous_primeGammaCauchyCubicComplexRayFeature (-s)).norm.pow 2)
  have hIcc : IntegrableOn (fun u : ℝ =>
      ‖primeGammaCauchyCubicComplexRayFeature (-s) u‖ ^ 2) (Icc (0 : ℝ) L) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hsub : Ioc (0 : ℝ) L ⊆ Icc (0 : ℝ) L := by
    intro u hu
    exact ⟨hu.1.le, hu.2⟩
  exact (hIcc.mono_set hsub).integrable_indicator measurableSet_Ioc |>.integrableOn

/-- A positive endpoint interval is read by the actual P half-line pairing against its literal
indicator port. -/
theorem routePBurnolHalfLinePairing_complexRay_positiveIntervalPort
    (s U : ℝ) (hU : 0 ≤ U) :
    _root_.RHTower.routePBurnolHalfLinePairing
        (primeGammaCauchyCubicComplexRayFeature s)
        (primeGammaCauchyCubicPositiveIntervalPort U) =
      ∫ u in (0 : ℝ)..U, (primeGammaCauchyCubicRayFeature s u : ℂ) := by
  rw [_root_.RHTower.routePBurnolHalfLinePairing]
  calc
    (∫ u : ℝ in Ioi (0 : ℝ),
        star (primeGammaCauchyCubicComplexRayFeature s u) *
          primeGammaCauchyCubicPositiveIntervalPort U u) =
        ∫ u : ℝ in Ioi (0 : ℝ),
          (Ioc (0 : ℝ) U).indicator
            (fun u => (primeGammaCauchyCubicRayFeature s u : ℂ)) u := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro u _
              by_cases hu : u ∈ Ioc (0 : ℝ) U
              · simp [primeGammaCauchyCubicComplexRayFeature,
                  primeGammaCauchyCubicPositiveIntervalPort, hu]
              · simp [primeGammaCauchyCubicPositiveIntervalPort, hu]
    _ = ∫ u : ℝ in Ioi (0 : ℝ) ∩ Ioc 0 U,
        (primeGammaCauchyCubicRayFeature s u : ℂ) := by
          exact setIntegral_indicator measurableSet_Ioc
    _ = ∫ u : ℝ in Ioc (0 : ℝ) U,
        (primeGammaCauchyCubicRayFeature s u : ℂ) := by
          rw [inter_eq_right.mpr Ioc_subset_Ioi_self]
    _ = ∫ u in (0 : ℝ)..U, (primeGammaCauchyCubicRayFeature s u : ℂ) := by
          exact (intervalIntegral.integral_of_le hU).symm

/-- The reflected finite wall ray pairs with the literal interval port as the exact reflected
cubic integral.  Both endpoint marks remain present. -/
theorem routePBurnolHalfLinePairing_reflectedWallRay_positiveIntervalPort
    (s L : ℝ) (hL : 0 ≤ L) :
    _root_.RHTower.routePBurnolHalfLinePairing
        (primeGammaCauchyCubicReflectedWallRayPort s L)
        (primeGammaCauchyCubicPositiveIntervalPort L) =
      ∫ u in (0 : ℝ)..L, (primeGammaCauchyCubicRayFeature (-s) u : ℂ) := by
  rw [_root_.RHTower.routePBurnolHalfLinePairing]
  calc
    (∫ u : ℝ in Ioi (0 : ℝ),
        star (primeGammaCauchyCubicReflectedWallRayPort s L u) *
          primeGammaCauchyCubicPositiveIntervalPort L u) =
        ∫ u : ℝ in Ioi (0 : ℝ),
          (Ioc (0 : ℝ) L).indicator
            (fun u => (primeGammaCauchyCubicRayFeature (-s) u : ℂ)) u := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro u _
              by_cases hu : u ∈ Ioc (0 : ℝ) L
              · simp [primeGammaCauchyCubicReflectedWallRayPort,
                  primeGammaCauchyCubicPositiveIntervalPort,
                  primeGammaCauchyCubicComplexRayFeature, hu]
              · simp [primeGammaCauchyCubicReflectedWallRayPort,
                  primeGammaCauchyCubicPositiveIntervalPort, hu]
    _ = ∫ u : ℝ in Ioi (0 : ℝ) ∩ Ioc 0 L,
        (primeGammaCauchyCubicRayFeature (-s) u : ℂ) := by
          exact setIntegral_indicator measurableSet_Ioc
    _ = ∫ u : ℝ in Ioc (0 : ℝ) L,
        (primeGammaCauchyCubicRayFeature (-s) u : ℂ) := by
          rw [inter_eq_right.mpr Ioc_subset_Ioi_self]
    _ = ∫ u in (0 : ℝ)..L, (primeGammaCauchyCubicRayFeature (-s) u : ℂ) := by
          exact (intervalIntegral.integral_of_le hL).symm

/-- **Literal SP-E/P-G194 interval port.** The polarized P aperture colligation acts on a
positive physical endpoint interval without replacing its indicator by a smooth proxy. -/
theorem primeGammaCauchyCubicComplexRay_positiveIntervalPort_aperture_pairing_colligation
    (r q U : ℝ) :
    _root_.RHTower.routePBurnolHalfLinePairing
        (_root_.RHTower.routePBurnolForwardDampingShift (Real.exp r)
          (primeGammaCauchyCubicComplexRayFeature (Real.exp q)))
        (_root_.RHTower.routePBurnolForwardDampingShift (Real.exp r)
          (primeGammaCauchyCubicPositiveIntervalPort U)) +
      _root_.RHTower.routePBurnolHalfLinePairing
        (_root_.RHTower.routePBurnolApertureBoundaryDefect (Real.exp r)
          (primeGammaCauchyCubicComplexRayFeature (Real.exp q)))
        (_root_.RHTower.routePBurnolApertureBoundaryDefect (Real.exp r)
          (primeGammaCauchyCubicPositiveIntervalPort U)) +
      _root_.RHTower.routePBurnolHalfLinePairing
        (_root_.RHTower.routePBurnolApertureTailDefect (Real.exp r)
          (primeGammaCauchyCubicComplexRayFeature (Real.exp q)))
        (_root_.RHTower.routePBurnolApertureTailDefect (Real.exp r)
          (primeGammaCauchyCubicPositiveIntervalPort U)) =
      _root_.RHTower.routePBurnolHalfLinePairing
        (primeGammaCauchyCubicComplexRayFeature (Real.exp q))
        (primeGammaCauchyCubicPositiveIntervalPort U) := by
  exact _root_.RHTower.routePBurnolApertureDamping_pairing_colligation_of_aestronglyMeasurable
    (Real.exp_nonneg r)
    ((continuous_primeGammaCauchyCubicComplexRayFeature _).aestronglyMeasurable.restrict)
    (aestronglyMeasurable_primeGammaCauchyCubicPositiveIntervalPort U)
    (integrableOn_norm_sq_primeGammaCauchyCubicComplexRayFeature _ (Real.exp_pos q))
    (integrableOn_norm_sq_primeGammaCauchyCubicPositiveIntervalPort U)

/-- **Reflected-wall P-G194 port.** The finite source contribution beyond the SP-E wall is
transported through every literal P aperture channel, even though its reflected ray is not a
global positive-scale eigenmode. -/
theorem primeGammaCauchyCubicReflectedWallRay_positiveIntervalPort_aperture_pairing_colligation
    (r s L : ℝ) :
    _root_.RHTower.routePBurnolHalfLinePairing
        (_root_.RHTower.routePBurnolForwardDampingShift (Real.exp r)
          (primeGammaCauchyCubicReflectedWallRayPort s L))
        (_root_.RHTower.routePBurnolForwardDampingShift (Real.exp r)
          (primeGammaCauchyCubicPositiveIntervalPort L)) +
      _root_.RHTower.routePBurnolHalfLinePairing
        (_root_.RHTower.routePBurnolApertureBoundaryDefect (Real.exp r)
          (primeGammaCauchyCubicReflectedWallRayPort s L))
        (_root_.RHTower.routePBurnolApertureBoundaryDefect (Real.exp r)
          (primeGammaCauchyCubicPositiveIntervalPort L)) +
      _root_.RHTower.routePBurnolHalfLinePairing
        (_root_.RHTower.routePBurnolApertureTailDefect (Real.exp r)
          (primeGammaCauchyCubicReflectedWallRayPort s L))
        (_root_.RHTower.routePBurnolApertureTailDefect (Real.exp r)
          (primeGammaCauchyCubicPositiveIntervalPort L)) =
      _root_.RHTower.routePBurnolHalfLinePairing
        (primeGammaCauchyCubicReflectedWallRayPort s L)
        (primeGammaCauchyCubicPositiveIntervalPort L) := by
  exact _root_.RHTower.routePBurnolApertureDamping_pairing_colligation_of_aestronglyMeasurable
    (Real.exp_nonneg r)
    (aestronglyMeasurable_primeGammaCauchyCubicReflectedWallRayPort s L)
    (aestronglyMeasurable_primeGammaCauchyCubicPositiveIntervalPort L)
    (integrableOn_norm_sq_primeGammaCauchyCubicReflectedWallRayPort s L)
    (integrableOn_norm_sq_primeGammaCauchyCubicPositiveIntervalPort L)

/-- The two pieces of a wall-crossing source slice form a signed direct sum of literal P
colligations.  This is the exact defect architecture forced by the physical wall: neither port
is merged into a surrogate eigenray. -/
theorem primeGammaCauchyCubicCrossingWall_signedTwoPort_aperture_colligation
    {s : ℝ} (hs : 0 < s) (r U V : ℝ) :
    (_root_.RHTower.routePBurnolHalfLinePairing
        (_root_.RHTower.routePBurnolForwardDampingShift (Real.exp r)
          (primeGammaCauchyCubicComplexRayFeature s))
        (_root_.RHTower.routePBurnolForwardDampingShift (Real.exp r)
          (primeGammaCauchyCubicPositiveIntervalPort U)) -
      _root_.RHTower.routePBurnolHalfLinePairing
        (_root_.RHTower.routePBurnolForwardDampingShift (Real.exp r)
          (primeGammaCauchyCubicReflectedWallRayPort s V))
        (_root_.RHTower.routePBurnolForwardDampingShift (Real.exp r)
          (primeGammaCauchyCubicPositiveIntervalPort V))) +
      (_root_.RHTower.routePBurnolHalfLinePairing
        (_root_.RHTower.routePBurnolApertureBoundaryDefect (Real.exp r)
          (primeGammaCauchyCubicComplexRayFeature s))
        (_root_.RHTower.routePBurnolApertureBoundaryDefect (Real.exp r)
          (primeGammaCauchyCubicPositiveIntervalPort U)) -
      _root_.RHTower.routePBurnolHalfLinePairing
        (_root_.RHTower.routePBurnolApertureBoundaryDefect (Real.exp r)
          (primeGammaCauchyCubicReflectedWallRayPort s V))
        (_root_.RHTower.routePBurnolApertureBoundaryDefect (Real.exp r)
          (primeGammaCauchyCubicPositiveIntervalPort V))) +
      (_root_.RHTower.routePBurnolHalfLinePairing
        (_root_.RHTower.routePBurnolApertureTailDefect (Real.exp r)
          (primeGammaCauchyCubicComplexRayFeature s))
        (_root_.RHTower.routePBurnolApertureTailDefect (Real.exp r)
          (primeGammaCauchyCubicPositiveIntervalPort U)) -
      _root_.RHTower.routePBurnolHalfLinePairing
        (_root_.RHTower.routePBurnolApertureTailDefect (Real.exp r)
          (primeGammaCauchyCubicReflectedWallRayPort s V))
        (_root_.RHTower.routePBurnolApertureTailDefect (Real.exp r)
          (primeGammaCauchyCubicPositiveIntervalPort V))) =
      _root_.RHTower.routePBurnolHalfLinePairing
        (primeGammaCauchyCubicComplexRayFeature s)
        (primeGammaCauchyCubicPositiveIntervalPort U) -
      _root_.RHTower.routePBurnolHalfLinePairing
        (primeGammaCauchyCubicReflectedWallRayPort s V)
        (primeGammaCauchyCubicPositiveIntervalPort V) := by
  have hpositive :=
    _root_.RHTower.routePBurnolApertureDamping_pairing_colligation_of_aestronglyMeasurable
      (c := Real.exp r) (f := primeGammaCauchyCubicComplexRayFeature s)
      (g := primeGammaCauchyCubicPositiveIntervalPort U)
      (Real.exp_nonneg r)
      ((continuous_primeGammaCauchyCubicComplexRayFeature s).aestronglyMeasurable.restrict)
      (aestronglyMeasurable_primeGammaCauchyCubicPositiveIntervalPort U)
      (integrableOn_norm_sq_primeGammaCauchyCubicComplexRayFeature s hs)
      (integrableOn_norm_sq_primeGammaCauchyCubicPositiveIntervalPort U)
  have hwall :=
    _root_.RHTower.routePBurnolApertureDamping_pairing_colligation_of_aestronglyMeasurable
      (c := Real.exp r) (f := primeGammaCauchyCubicReflectedWallRayPort s V)
      (g := primeGammaCauchyCubicPositiveIntervalPort V)
      (Real.exp_nonneg r)
      (aestronglyMeasurable_primeGammaCauchyCubicReflectedWallRayPort s V)
      (aestronglyMeasurable_primeGammaCauchyCubicPositiveIntervalPort V)
      (integrableOn_norm_sq_primeGammaCauchyCubicReflectedWallRayPort s V)
      (integrableOn_norm_sq_primeGammaCauchyCubicPositiveIntervalPort V)
  linear_combination hpositive - hwall

/-- At one positive source scale, the signed pair of literal P source pairings is exactly the
two endpoint integrals of the wall-crossing SP-E slice. -/
theorem crossingWallScaleSlice_eq_signedTwoPortSourcePairing
    (s U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    (∫ u in (0 : ℝ)..U, (primeGammaCauchyCubicRayFeature s u : ℂ)) -
      ∫ u in (0 : ℝ)..V, (primeGammaCauchyCubicRayFeature (-s) u : ℂ) =
      _root_.RHTower.routePBurnolHalfLinePairing
        (primeGammaCauchyCubicComplexRayFeature s)
        (primeGammaCauchyCubicPositiveIntervalPort U) -
      _root_.RHTower.routePBurnolHalfLinePairing
        (primeGammaCauchyCubicReflectedWallRayPort s V)
        (primeGammaCauchyCubicPositiveIntervalPort V) := by
  rw [← routePBurnolHalfLinePairing_complexRay_positiveIntervalPort s U hU,
    ← routePBurnolHalfLinePairing_reflectedWallRay_positiveIntervalPort s V hV]

/-- Reflection transfers a negative endpoint-distance interval to a positive finite interval at
the reflected cubic scale.  This is exact orientation data, not a positivity estimate. -/
theorem integral_primeGammaCauchyCubicRayFeature_reflect_negativeInterval
    (s L : ℝ) :
    (∫ u in (-L)..0, primeGammaCauchyCubicRayFeature s u) =
      -∫ u in (0 : ℝ)..L, primeGammaCauchyCubicRayFeature (-s) u := by
  calc
    (∫ u in (-L)..0, primeGammaCauchyCubicRayFeature s u) =
        ∫ u in (0 : ℝ)..L, primeGammaCauchyCubicRayFeature s (-u) := by
          have h := intervalIntegral.integral_comp_neg
            (f := fun u : ℝ => primeGammaCauchyCubicRayFeature s (-u))
            (a := -L) (b := 0)
          simpa only [neg_zero, neg_neg] using h
    _ = ∫ u in (0 : ℝ)..L, -primeGammaCauchyCubicRayFeature (-s) u := by
          apply intervalIntegral.integral_congr
          intro u _
          unfold primeGammaCauchyCubicRayFeature
          dsimp
          have hexp : -(s * -u) = -((-s) * u) := by ring
          rw [hexp]
          ring
    _ = -∫ u in (0 : ℝ)..L, primeGammaCauchyCubicRayFeature (-s) u := by
          rw [intervalIntegral.integral_neg]

/-- The SP-E part lying beyond the physical wall remains a literal finite reflected P port.
It cannot use the global positive-scale P eigenray, but no source term is discarded. -/
theorem speQuantileRieszWeightedWallRemainder_eq_reflectedEndpointPort
    {M : ℕ} (hM : 0 < M) (b : ℝ) :
    (∫ h in Real.log M..b,
      Real.exp (h / 2) * _root_.RHTower.speQuantileRieszProfile M h) =
      -(2 * (M : ℝ) * Real.sqrt (M : ℝ) *
        ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
          ∫ u in (0 : ℝ)..b - Real.log M,
            primeGammaCauchyCubicRayFeature (-s) u) := by
  calc
    (∫ h in Real.log M..b,
      Real.exp (h / 2) * _root_.RHTower.speQuantileRieszProfile M h) =
        2 * (M : ℝ) * Real.sqrt (M : ℝ) *
          ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
            ∫ u in Real.log M - b..0,
              primeGammaCauchyCubicRayFeature s u := by
                rw [speQuantileRieszWeightedIntervalIntegral_eq_endpointRayTwoPort hM
                  (Real.log M) b]
                simp only [sub_self]
    _ = 2 * (M : ℝ) * Real.sqrt (M : ℝ) *
          ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
            -∫ u in (0 : ℝ)..b - Real.log M,
              primeGammaCauchyCubicRayFeature (-s) u := by
                apply congrArg (fun z : ℝ => 2 * (M : ℝ) * Real.sqrt (M : ℝ) * z)
                apply intervalIntegral.integral_congr
                intro s _
                convert integral_primeGammaCauchyCubicRayFeature_reflect_negativeInterval s
                  (b - Real.log M) using 1 ; ring
    _ = -(2 * (M : ℝ) * Real.sqrt (M : ℝ) *
        ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
          ∫ u in (0 : ℝ)..b - Real.log M,
            primeGammaCauchyCubicRayFeature (-s) u) := by
              rw [intervalIntegral.integral_neg]
              ring

/-- The physical-wall split of an oriented SP-E interval.  Its positive piece is a genuine
P half-line two-port over `0 ≤ u ≤ log M - a`; the remaining interval is exactly the wall
remainder and cannot be discarded without an independent source theorem. -/
theorem speQuantileRieszWeightedIntervalIntegral_eq_positiveEndpointPort_add_wallRemainder
    {M : ℕ} (hM : 0 < M) {a : ℝ} (ha : a ≤ Real.log M) (b : ℝ) :
    0 ≤ Real.log M - a ∧
      (∫ h in a..b,
        Real.exp (h / 2) * _root_.RHTower.speQuantileRieszProfile M h) =
        (2 * (M : ℝ) * Real.sqrt (M : ℝ) *
          ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
            ∫ u in (0 : ℝ)..Real.log M - a,
              primeGammaCauchyCubicRayFeature s u) +
        ∫ h in Real.log M..b,
          Real.exp (h / 2) * _root_.RHTower.speQuantileRieszProfile M h := by
  have hWcont : Continuous (fun h : ℝ =>
      Real.exp (h / 2) * _root_.RHTower.speQuantileRieszProfile M h) :=
    (by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).mul
      (_root_.RHTower.continuous_speQuantileRieszProfile M)
  constructor
  · linarith
  · calc
      (∫ h in a..b,
        Real.exp (h / 2) * _root_.RHTower.speQuantileRieszProfile M h) =
          (∫ h in a..Real.log M,
            Real.exp (h / 2) * _root_.RHTower.speQuantileRieszProfile M h) +
          ∫ h in Real.log M..b,
            Real.exp (h / 2) * _root_.RHTower.speQuantileRieszProfile M h := by
              symm
              exact intervalIntegral.integral_add_adjacent_intervals
                (hWcont.intervalIntegrable a (Real.log M))
                (hWcont.intervalIntegrable (Real.log M) b)
      _ = (2 * (M : ℝ) * Real.sqrt (M : ℝ) *
          ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
            ∫ u in (0 : ℝ)..Real.log M - a,
              primeGammaCauchyCubicRayFeature s u) +
          ∫ h in Real.log M..b,
            Real.exp (h / 2) * _root_.RHTower.speQuantileRieszProfile M h := by
              rw [speQuantileRieszWeightedIntervalIntegral_eq_endpointRayTwoPort hM a
                (Real.log M)]
              simp only [sub_self]

/-- A source interval which crosses the physical wall has two—and only two—literal P ports:
the positive-scale eigenray before the wall and the compact reflected ray after it.  Their signed
difference retains both endpoint lengths and the wall orientation. -/
theorem speQuantileRieszWeightedIntervalIntegral_eq_crossingWallTwoPort
    {M : ℕ} (hM : 0 < M) {a b : ℝ}
    (ha : a ≤ Real.log M) (hb : Real.log M ≤ b) :
    0 ≤ Real.log M - a ∧ 0 ≤ b - Real.log M ∧
      (∫ h in a..b,
        Real.exp (h / 2) * _root_.RHTower.speQuantileRieszProfile M h) =
        2 * (M : ℝ) * Real.sqrt (M : ℝ) *
          ((∫ s in (1 : ℝ)..(3 / 2 : ℝ),
              ∫ u in (0 : ℝ)..Real.log M - a,
                primeGammaCauchyCubicRayFeature s u) -
            ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
              ∫ u in (0 : ℝ)..b - Real.log M,
                primeGammaCauchyCubicRayFeature (-s) u) := by
  obtain ⟨hpos, hsplit⟩ :=
    speQuantileRieszWeightedIntervalIntegral_eq_positiveEndpointPort_add_wallRemainder
      hM ha b
  constructor
  · exact hpos
  constructor
  · linarith
  calc
    (∫ h in a..b,
      Real.exp (h / 2) * _root_.RHTower.speQuantileRieszProfile M h) =
        (2 * (M : ℝ) * Real.sqrt (M : ℝ) *
          ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
            ∫ u in (0 : ℝ)..Real.log M - a,
              primeGammaCauchyCubicRayFeature s u) +
          ∫ h in Real.log M..b,
            Real.exp (h / 2) * _root_.RHTower.speQuantileRieszProfile M h := hsplit
    _ = (2 * (M : ℝ) * Real.sqrt (M : ℝ) *
          ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
            ∫ u in (0 : ℝ)..Real.log M - a,
              primeGammaCauchyCubicRayFeature s u) -
        (2 * (M : ℝ) * Real.sqrt (M : ℝ) *
          ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
            ∫ u in (0 : ℝ)..b - Real.log M,
              primeGammaCauchyCubicRayFeature (-s) u) := by
                rw [speQuantileRieszWeightedWallRemainder_eq_reflectedEndpointPort hM b]
                ring
    _ = 2 * (M : ℝ) * Real.sqrt (M : ℝ) *
          ((∫ s in (1 : ℝ)..(3 / 2 : ℝ),
              ∫ u in (0 : ℝ)..Real.log M - a,
                primeGammaCauchyCubicRayFeature s u) -
            ∫ s in (1 : ℝ)..(3 / 2 : ℝ),
              ∫ u in (0 : ℝ)..b - Real.log M,
                primeGammaCauchyCubicRayFeature (-s) u) := by ring

end GaloisForLFunctions.HTGeometry

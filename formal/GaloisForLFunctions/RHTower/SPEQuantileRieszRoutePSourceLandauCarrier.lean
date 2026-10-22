import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePLandauDisk
import GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinResolventExponentialWidth
import GaloisForLFunctions.RHTower.LandauIntegralTransfer
import GaloisForLFunctions.HTGeometry.ClockParametricIntegralHolomorphy

/-!
# Landau carrier measure for the Route P source signal

Let `S(t)` be the unit-Riesz Chebyshev resolvent ray representative
`S(t) = e^(-t) (I(t) - 2/3)` for `t ≥ 0`, with `I` the integrated Chebyshev ray density;
its Laplace transform continues to the Route P source function `R(z)`. For a sign `ε` and a cutoff `T ≥ 0` this module builds the
measure on `(T, ∞)` with density `ε e^(-r t) S(t)`, identifies its complex moment generating
function with the tail Laplace transform `∫_T^∞ e^(-(r - z) t) ε S(t) dt`, and writes that tail
as `ε R(z)` minus an entire head integral over `[0, T]`. Since `R` is analytic on the disk
`|z - 1| ≤ 5/4`, Landau's theorem for nonnegative measures then gives exponential
integrability of order `9/8`.

## Main results

- `complexMGF_id_routePSourceLandauMeasure_eq_tailLaplace`: under the sign hypothesis, the
  complex MGF of the carrier measure at `z` is the tail Laplace transform at `r - z`.
- `routePSourceSignedTailLaplace_eq_continuation_sub_head`: for `T ≥ 0` and `Re z > 1/2`, the
  tail Laplace transform equals `ε R(z)` minus the head integral over `[0, T]`.
- `differentiableOn_routePSourceLandauContinuation_closedBall`: `w ↦ ε R(1 - w) - head(1 - w)`
  is holomorphic on the closed disk `|w| ≤ 5/4`.
- `routePSourceLandauContinuation_eventuallyEq_complexMGF`: near `0` this function coincides with
  the complex MGF of the carrier measure with `r = 1`.
- `integrable_exp_nine_eighth_routePSourceLandauMeasure`: `e^(9t/8)` is integrable against the
  carrier measure with `r = 1`.

## Hypotheses

The holomorphy and Laplace identities are unconditional (with `T ≥ 0` and `Re z > 1/2` where
stated). The measure-theoretic results, in particular the integrability of `e^(9t/8)`, are
conditional on the one-sided sign hypothesis `hpos`: `0 ≤ ε S(t)` for every `t > T`.
-/

open Complex MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- The signed density `ε e^(-r t) S(t)`, where `S` is the unit-Riesz Chebyshev resolvent
ray representative. -/
def routePSourceSignedDensity (epsilon r t : ℝ) : ℝ :=
  epsilon * (Real.exp (-r * t) *
    GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t)

/-- The Landau carrier measure on `(T, ∞)`: Lebesgue measure with density the positive part
of `ε e^(-r t) S(t)`. -/
def routePSourceLandauMeasure (epsilon r T : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi T)).withDensity
    (fun t => ENNReal.ofReal (routePSourceSignedDensity epsilon r t))

theorem measurable_routePSourceSignedDensity (epsilon r : ℝ) :
    Measurable (routePSourceSignedDensity epsilon r) := by
  unfold routePSourceSignedDensity
  exact measurable_const.mul
    ((by fun_prop : Measurable (fun t : ℝ => Real.exp (-r * t))).mul
      GaloisForLFunctions.RHTower.continuous_criticalMellinChebyshevResolventRayRepresentative.measurable)

/-- For `T ≥ 0` and `r > 1/2`, the signed density `ε e^(-r t) S(t)` is integrable on `(T, ∞)`,
by the half-exponential bound on `S`. -/
theorem integrableOn_routePSourceSignedDensity
    (epsilon T r : ℝ) (hT : 0 ≤ T) (hr : 1 / 2 < r) :
    IntegrableOn (routePSourceSignedDensity epsilon r) (Ioi T) := by
  obtain ⟨B, hB0, hB⟩ :=
    GaloisForLFunctions.RHTower.criticalMellinChebyshevResolvent_halfExponentialBounded
  have hfull :=
    GaloisForLFunctions.RHTower.integrableOn_exp_mul_criticalMellinChebyshevResolventRayRepresentative_of_exponentialBound
      hB0 hB hr
  have htail := hfull.mono_set (show Ioi T ⊆ Ioi (0 : ℝ) by
    intro t ht
    exact lt_of_le_of_lt hT ht)
  exact htail.const_mul epsilon

theorem routePSourceSignedDensity_nonneg_ae
    {epsilon r T : ℝ}
    (hpos : ∀ t, T < t →
      0 ≤ epsilon *
        GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t) :
    ∀ᵐ t ∂volume.restrict (Ioi T),
      0 ≤ routePSourceSignedDensity epsilon r t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  unfold routePSourceSignedDensity
  rw [show epsilon * (Real.exp (-r * t) *
      GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t) =
    Real.exp (-r * t) * (epsilon *
      GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t) by ring]
  exact mul_nonneg (Real.exp_pos _).le (hpos t ht)

/-- Assuming `0 ≤ ε S(t)` for `t > T`, with `T ≥ 0` and `r - ρ > 1/2`, the exponential `e^(ρ t)`
is integrable against the carrier measure. -/
theorem integrable_exp_mul_id_routePSourceLandauMeasure
    {epsilon r T rho : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t →
      0 ≤ epsilon *
        GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t)
    (hr : 1 / 2 < r - rho) :
    Integrable (fun t : ℝ => Real.exp (rho * id t))
      (routePSourceLandauMeasure epsilon r T) := by
  have hdens := integrableOn_routePSourceSignedDensity epsilon T (r - rho) hT hr
  have hmeas : AEMeasurable
      (fun t => ENNReal.ofReal (routePSourceSignedDensity epsilon r t))
      (volume.restrict (Ioi T)) :=
    (measurable_routePSourceSignedDensity epsilon r).ennreal_ofReal
      |>.aemeasurable.restrict
  have hnonneg := routePSourceSignedDensity_nonneg_ae hpos (r := r)
  rw [routePSourceLandauMeasure,
    integrable_withDensity_iff_integrable_smul₀' hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply hdens.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with t ht hden
  rw [ENNReal.toReal_ofReal hden]
  simp only [id_eq, smul_eq_mul]
  unfold routePSourceSignedDensity
  rw [show -(r - rho) * t = -r * t + rho * t by ring, Real.exp_add]
  ring

/-- Assuming `0 ≤ ε S(t)` for `t > T`, `T ≥ 0` and `r > 1/2`, the exponent `0` lies in the
interior of the set of exponents with integrable moment generating function. -/
theorem zero_mem_interior_integrableExpSet_routePSourceLandauMeasure
    {epsilon r T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t →
      0 ≤ epsilon *
        GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t)
    (hr : 1 / 2 < r) :
    0 ∈ interior (integrableExpSet id (routePSourceLandauMeasure epsilon r T)) := by
  let delta : ℝ := (r - 1 / 2) / 2
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset
    (Ioo_mem_nhds (a := -delta) (b := delta) (by linarith) (by linarith)) ?_
  intro rho hrho
  exact integrable_exp_mul_id_routePSourceLandauMeasure hT hpos (by
    dsimp only [delta] at hrho
    linarith [hrho.2])

/-- For `T ≥ 0` the carrier measure is concentrated on nonnegative times. -/
theorem id_nonneg_ae_routePSourceLandauMeasure
    {epsilon r T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂routePSourceLandauMeasure epsilon r T, 0 ≤ id t := by
  rw [routePSourceLandauMeasure]
  refine Filter.Eventually.filter_mono
    (MeasureTheory.withDensity_absolutelyContinuous _ _).ae_le ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact le_trans hT ht.le

/-- The tail Laplace transform `∫_T^∞ e^(-z t) ε S(t) dt`. -/
def routePSourceSignedTailLaplace (epsilon T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi T, Complex.exp (-z * (t : ℂ)) *
    ((epsilon *
      GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t : ℝ) : ℂ)

/-- Assuming `0 ≤ ε S(t)` for `t > T`, the complex moment generating function of the carrier
measure at `z` equals the tail Laplace transform at `r - z`. -/
theorem complexMGF_id_routePSourceLandauMeasure_eq_tailLaplace
    {epsilon r T : ℝ}
    (hpos : ∀ t, T < t →
      0 ≤ epsilon *
        GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t)
    (z : ℂ) :
    complexMGF id (routePSourceLandauMeasure epsilon r T) z =
      routePSourceSignedTailLaplace epsilon T ((r : ℂ) - z) := by
  have hmeas : AEMeasurable
      (fun t => ENNReal.ofReal (routePSourceSignedDensity epsilon r t))
      (volume.restrict (Ioi T)) :=
    (measurable_routePSourceSignedDensity epsilon r).ennreal_ofReal
      |>.aemeasurable.restrict
  have hnonneg := routePSourceSignedDensity_nonneg_ae hpos (r := r)
  rw [complexMGF, routePSourceLandauMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold routePSourceSignedTailLaplace
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with t ht hden
  rw [ENNReal.toReal_ofReal hden, Complex.real_smul]
  simp only [id_eq]
  unfold routePSourceSignedDensity
  push_cast
  rw [show
      (epsilon : ℂ) *
          (Complex.exp (-(r : ℂ) * (t : ℂ)) *
            (GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t : ℂ)) *
          Complex.exp (z * (t : ℂ)) =
        (Complex.exp (-(r : ℂ) * (t : ℂ)) * Complex.exp (z * (t : ℂ))) *
          ((epsilon : ℂ) *
            (GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t : ℂ)) by ring]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The head Laplace transform `∫_0^T e^(-z t) ε S(t) dt` over a compact interval. -/
def routePSourceSignedHeadLaplace (epsilon T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..T, Complex.exp (-z * (t : ℂ)) *
    ((epsilon *
      GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t : ℝ) : ℂ)

/-- The head Laplace transform over `[0, T]` is an entire function of `z`. -/
theorem differentiable_routePSourceSignedHeadLaplace (epsilon T : ℝ) :
    Differentiable ℂ (routePSourceSignedHeadLaplace epsilon T) := by
  intro z
  let rho : ℝ := |z.im| + 1
  let rho' : ℝ := |z.im| + 2
  have hrho : rho < rho' := by dsimp only [rho, rho']; linarith
  have hcont : Continuous (fun q : ℝ × ℂ =>
      Complex.exp (-q.2 * (q.1 : ℂ)) *
        ((epsilon *
          GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative q.1 : ℝ) : ℂ)) := by
    have hR : Continuous (fun q : ℝ × ℂ =>
        ((epsilon *
          GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative q.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        (continuous_const.mul
          (GaloisForLFunctions.RHTower.continuous_criticalMellinChebyshevResolventRayRepresentative.comp
            continuous_fst))
    have hExp : Continuous (fun q : ℝ × ℂ =>
        Complex.exp (-q.2 * (q.1 : ℂ))) := by fun_prop
    exact hExp.mul hR
  have hdiff : ∀ t : ℝ, DifferentiableOn ℂ
      (fun w : ℂ => Complex.exp (-w * (t : ℂ)) *
        ((epsilon *
          GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t : ℝ) : ℂ))
      (GaloisForLFunctions.HTGeometry.imStrip rho') := by
    intro t w hw
    exact (by fun_prop : DifferentiableAt ℂ
      (fun w : ℂ => Complex.exp (-w * (t : ℂ)) *
        ((epsilon *
          GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t : ℝ) : ℂ)) w)
      |>.differentiableWithinAt
  have hz : z ∈ GaloisForLFunctions.HTGeometry.imStrip rho := by
    apply GaloisForLFunctions.HTGeometry.mem_imStrip.mpr
    dsimp only [rho]
    linarith
  change DifferentiableAt ℂ
    (fun w => ∫ t in (0 : ℝ)..T,
      Complex.exp (-w * (t : ℂ)) *
        ((epsilon *
          GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t : ℝ) : ℂ)) z
  exact GaloisForLFunctions.HTGeometry.differentiableAt_intervalIntegral_of_holomorphic
    hrho hcont hdiff hz

/-- For `Re z > 1/2`, the kernel `e^(-z t) ε S(t)` is integrable on `(0, ∞)`. -/
theorem integrableOn_routePSourceSignedComplexKernel
    (epsilon : ℝ) {z : ℂ} (hz : 1 / 2 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ)) *
      ((epsilon *
        GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t : ℝ) : ℂ))
      (Ioi 0) := by
  have hreal := integrableOn_routePSourceSignedDensity epsilon 0 z.re le_rfl hz
  refine Integrable.mono' hreal.norm ?_ ?_
  · have hR : Measurable (fun t : ℝ =>
        ((epsilon *
          GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        (measurable_const.mul
          GaloisForLFunctions.RHTower.continuous_criticalMellinChebyshevResolventRayRepresentative.measurable)
    have hExp : Measurable (fun t : ℝ => Complex.exp (-z * (t : ℂ))) := by fun_prop
    exact (hExp.mul hR).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_exp,
      show (-z * (t : ℂ)).re = -z.re * t by simp [mul_re],
      Complex.norm_real]
    simp only [Real.norm_eq_abs]
    unfold routePSourceSignedDensity
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply le_of_eq
    ring

/-- For `T ≥ 0` and `Re z > 1/2`, the tail Laplace transform over `(T, ∞)` equals
`ε R(z)` minus the head transform over `[0, T]`, where `R` is the Route P source continuation. -/
theorem routePSourceSignedTailLaplace_eq_continuation_sub_head
    {epsilon T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : 1 / 2 < z.re) :
    routePSourceSignedTailLaplace epsilon T z =
      (epsilon : ℂ) * routePSourceLaplaceContinuation z -
        routePSourceSignedHeadLaplace epsilon T z := by
  let f : ℝ → ℂ := fun t => Complex.exp (-z * (t : ℂ)) *
    ((epsilon *
      GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t : ℝ) : ℂ)
  have hfull : IntegrableOn f (Ioi 0) :=
    integrableOn_routePSourceSignedComplexKernel epsilon hz
  have hhead : IntegrableOn f (Ioc 0 T) :=
    hfull.mono_set (by intro t ht; exact ht.1)
  have htail : IntegrableOn f (Ioi T) :=
    hfull.mono_set (by intro t ht; exact lt_of_le_of_lt hT ht)
  have hdisj : Disjoint (Ioc (0 : ℝ) T) (Ioi T) := by
    rw [Set.disjoint_left]
    intro t hheadT htailT
    exact (not_lt_of_ge hheadT.2) htailT
  have hsplit := setIntegral_union₀ hdisj.aedisjoint
    measurableSet_Ioi.nullMeasurableSet hhead htail
  rw [Set.Ioc_union_Ioi_eq_Ioi hT] at hsplit
  have hheadEq : routePSourceSignedHeadLaplace epsilon T z =
      ∫ t in Ioc (0 : ℝ) T, f t := by
    unfold routePSourceSignedHeadLaplace
    rw [intervalIntegral.integral_of_le hT]
  have htailEq : routePSourceSignedTailLaplace epsilon T z =
      ∫ t in Ioi T, f t := rfl
  have hfullEq : (∫ t in Ioi (0 : ℝ), f t) =
      (epsilon : ℂ) * routePSourceLaplaceContinuation z := by
    rw [routePSourceLaplaceContinuation_eq_laplace hz]
    unfold GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventLaplace
      ccmAbelLaplaceTail
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [f]
    push_cast
    ring
  rw [← hheadEq, ← htailEq, hfullEq] at hsplit
  linear_combination -hsplit

/-- The candidate continuation `w ↦ ε R(1 - w) - head(1 - w)` of the carrier measure's
complex moment generating function (with `r = 1`). -/
def routePSourceLandauContinuation (epsilon T : ℝ) (w : ℂ) : ℂ :=
  (epsilon : ℂ) * routePSourceLaplaceContinuation ((1 : ℂ) - w) -
    routePSourceSignedHeadLaplace epsilon T ((1 : ℂ) - w)

/-- The candidate continuation is holomorphic on the closed disk `|w| ≤ 5/4`, since `R` is
analytic on `|z - 1| ≤ 5/4` and the head transform is entire. -/
theorem differentiableOn_routePSourceLandauContinuation_closedBall
    (epsilon T : ℝ) :
    DifferentiableOn ℂ (routePSourceLandauContinuation epsilon T)
      (Metric.closedBall 0 (5 / 4 : ℝ)) := by
  intro w hw
  have hwNorm : ‖w‖ ≤ (5 / 4 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hw
  have hshiftMem : (1 : ℂ) - w ∈ Metric.closedBall 1 (5 / 4 : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : (1 : ℂ) - w - 1 = -w := by ring
    rw [heq, norm_neg]
    exact hwNorm
  have hF : DifferentiableAt ℂ routePSourceLaplaceContinuation ((1 : ℂ) - w) :=
    (analyticOnNhd_routePSourceLaplaceContinuation_closedBall_one
      _ hshiftMem).differentiableAt
  have hHead : DifferentiableAt ℂ (routePSourceSignedHeadLaplace epsilon T)
      ((1 : ℂ) - w) := differentiable_routePSourceSignedHeadLaplace epsilon T _
  have hinner : DifferentiableAt ℂ (fun v : ℂ => (1 : ℂ) - v) w := by fun_prop
  have houter : DifferentiableAt ℂ
      (fun s : ℂ => (epsilon : ℂ) * routePSourceLaplaceContinuation s -
        routePSourceSignedHeadLaplace epsilon T s) ((1 : ℂ) - w) :=
    (hF.const_mul (epsilon : ℂ)).sub hHead
  exact (houter.comp w hinner).differentiableWithinAt

/-- Assuming `T ≥ 0` and `0 ≤ ε S(t)` for `t > T`, the candidate continuation agrees near `0`
with the complex moment generating function of the carrier measure with `r = 1`. -/
theorem routePSourceLandauContinuation_eventuallyEq_complexMGF
    {epsilon T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t →
      0 ≤ epsilon *
        GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t) :
    routePSourceLandauContinuation epsilon T =ᶠ[𝓝 0]
      complexMGF id (routePSourceLandauMeasure epsilon 1 T) := by
  have hopen : {w : ℂ | 1 / 2 < ((1 : ℂ) - w).re} ∈ 𝓝 (0 : ℂ) := by
    have hOpen : IsOpen {w : ℂ | 1 / 2 < ((1 : ℂ) - w).re} :=
      isOpen_lt continuous_const
        (Complex.continuous_re.comp (continuous_const.sub continuous_id))
    exact hOpen.mem_nhds (by norm_num)
  filter_upwards [hopen] with w hw
  change (epsilon : ℂ) * routePSourceLaplaceContinuation ((1 : ℂ) - w) -
      routePSourceSignedHeadLaplace epsilon T ((1 : ℂ) - w) =
        complexMGF id (routePSourceLandauMeasure epsilon 1 T) w
  rw [← routePSourceSignedTailLaplace_eq_continuation_sub_head hT hw]
  simpa using
    (complexMGF_id_routePSourceLandauMeasure_eq_tailLaplace
      (r := 1) hpos w).symm

/-- Landau consequence: assuming `T ≥ 0` and the sign condition `0 ≤ ε S(t)` for all `t > T`,
`e^(9t/8)` is integrable against the carrier measure with `r = 1`. -/
theorem integrable_exp_nine_eighth_routePSourceLandauMeasure
    {epsilon T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t →
      0 ≤ epsilon *
        GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t) :
    Integrable (fun t : ℝ => Real.exp ((9 / 8 : ℝ) * id t))
      (routePSourceLandauMeasure epsilon 1 T) := by
  exact landau_complexMGF_integrable_transfer
    (id_nonneg_ae_routePSourceLandauMeasure hT)
    (zero_mem_interior_integrableExpSet_routePSourceLandauMeasure
      hT hpos (r := 1) (by norm_num))
    (R := (5 / 4 : NNReal))
    (by simpa using differentiableOn_routePSourceLandauContinuation_closedBall epsilon T)
    (routePSourceLandauContinuation_eventuallyEq_complexMGF hT hpos)
    (rho := 9 / 8) (by norm_num) (by norm_num)

end
end RHTower

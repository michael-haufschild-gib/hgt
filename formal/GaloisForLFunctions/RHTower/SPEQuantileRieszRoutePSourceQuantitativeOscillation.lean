import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourceNoAnalyticExtension
import GaloisForLFunctions.RHTower.CCM.CCMQuartetPaleyWiener

/-!
# Quantitative two-sided oscillation of the literal Route-P source

The source cannot have either eventual sign even after adding any fixed multiple of
`exp (-t/2)`.  A positive tail of such a perturbation would have a positive-measure
Laplace transform.  Landau transfer through the proved low-height disk extends it past
the Hardy axis; the perturbation pole at `-1/2` lies outside that disk and can be
subtracted.  This contradicts the unconditional nonextension theorem for the literal
source transform.

The resulting excursions are source-only.  They do not control Route-P's two coupled
square debts or provide an ordered-history graph intertwiner.
-/

open Complex MeasureTheory Set Filter Topology ProbabilityTheory
open GaloisForLFunctions.RHTower
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

private def routePSourceFloorPerturbation (epsilon b t : ℝ) : ℝ :=
  epsilon * GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t +
    b * Real.exp (-t / 2)

private theorem continuous_routePSourceFloorPerturbation (epsilon b : ℝ) :
    Continuous (routePSourceFloorPerturbation epsilon b) := by
  unfold routePSourceFloorPerturbation
  have hR :=
    GaloisForLFunctions.RHTower.continuous_criticalMellinChebyshevResolventRayRepresentative
  have hExp : Continuous (fun t : ℝ => Real.exp (-t / 2)) := by fun_prop
  exact (continuous_const.mul hR).add (continuous_const.mul hExp)

private def routePSourceFloorDensity (epsilon b r t : ℝ) : ℝ :=
  Real.exp (-r * t) * routePSourceFloorPerturbation epsilon b t

private def routePSourceFloorMeasure (epsilon b r T : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi T)).withDensity
    (fun t => ENNReal.ofReal (routePSourceFloorDensity epsilon b r t))

private theorem measurable_routePSourceFloorDensity (epsilon b r : ℝ) :
    Measurable (routePSourceFloorDensity epsilon b r) := by
  unfold routePSourceFloorDensity
  exact ((by fun_prop : Measurable (fun t : ℝ => Real.exp (-r * t))).mul
    (continuous_routePSourceFloorPerturbation epsilon b).measurable)

private theorem integrableOn_routePSourceFloorDensity
    (epsilon b T r : ℝ) (hT : 0 ≤ T) (hr : 1 / 2 < r) :
    IntegrableOn (routePSourceFloorDensity epsilon b r) (Ioi T) := by
  have hSigned := integrableOn_routePSourceSignedDensity epsilon T r hT hr
  have hCorr : IntegrableOn
      (fun t : ℝ => b * Real.exp (-(r + 1 / 2) * t)) (Ioi T) :=
    (integrableOn_exp_mul_Ioi (show -(r + 1 / 2) < 0 by linarith) T).const_mul b
  apply (hSigned.add hCorr).congr
  filter_upwards with t
  unfold routePSourceFloorDensity routePSourceFloorPerturbation
    routePSourceSignedDensity
  simp only [Pi.add_apply]
  rw [show -(r + 1 / 2) * t = -r * t + -t / 2 by ring, Real.exp_add]
  ring_nf

private theorem routePSourceFloorDensity_nonneg_ae
    {epsilon b r T : ℝ}
    (hpos : ∀ t, T < t → 0 ≤ routePSourceFloorPerturbation epsilon b t) :
    ∀ᵐ t ∂volume.restrict (Ioi T),
      0 ≤ routePSourceFloorDensity epsilon b r t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  unfold routePSourceFloorDensity
  exact mul_nonneg (Real.exp_pos _).le (hpos t ht)

private theorem integrable_exp_mul_id_routePSourceFloorMeasure
    {epsilon b r T rho : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ routePSourceFloorPerturbation epsilon b t)
    (hr : 1 / 2 < r - rho) :
    Integrable (fun t : ℝ => Real.exp (rho * id t))
      (routePSourceFloorMeasure epsilon b r T) := by
  have hdens := integrableOn_routePSourceFloorDensity epsilon b T (r - rho) hT hr
  have hmeas : AEMeasurable
      (fun t => ENNReal.ofReal (routePSourceFloorDensity epsilon b r t))
      (volume.restrict (Ioi T)) :=
    (measurable_routePSourceFloorDensity epsilon b r).ennreal_ofReal
      |>.aemeasurable.restrict
  have hnonneg := routePSourceFloorDensity_nonneg_ae hpos (r := r)
  rw [routePSourceFloorMeasure,
    integrable_withDensity_iff_integrable_smul₀' hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply hdens.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with t ht hden
  rw [ENNReal.toReal_ofReal hden]
  simp only [id_eq, smul_eq_mul]
  unfold routePSourceFloorDensity
  rw [show -(r - rho) * t = -r * t + rho * t by ring, Real.exp_add]
  ring

private theorem zero_mem_interior_integrableExpSet_routePSourceFloorMeasure
    {epsilon b r T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ routePSourceFloorPerturbation epsilon b t)
    (hr : 1 / 2 < r) :
    0 ∈ interior (integrableExpSet id (routePSourceFloorMeasure epsilon b r T)) := by
  let delta : ℝ := (r - 1 / 2) / 2
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset
    (Ioo_mem_nhds (a := -delta) (b := delta) (by linarith) (by linarith)) ?_
  intro rho hrho
  exact integrable_exp_mul_id_routePSourceFloorMeasure hT hpos (by
    dsimp only [delta] at hrho
    linarith [hrho.2])

private theorem id_nonneg_ae_routePSourceFloorMeasure
    {epsilon b r T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂routePSourceFloorMeasure epsilon b r T, 0 ≤ id t := by
  rw [routePSourceFloorMeasure]
  refine Filter.Eventually.filter_mono
    (MeasureTheory.withDensity_absolutelyContinuous _ _).ae_le ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact le_trans hT ht.le

private def routePSourceFloorTailLaplace (epsilon b T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi T, Complex.exp (-z * (t : ℂ)) *
    (routePSourceFloorPerturbation epsilon b t : ℂ)

private theorem complexMGF_id_routePSourceFloorMeasure_eq_tailLaplace
    {epsilon b r T : ℝ}
    (hpos : ∀ t, T < t → 0 ≤ routePSourceFloorPerturbation epsilon b t)
    (z : ℂ) :
    complexMGF id (routePSourceFloorMeasure epsilon b r T) z =
      routePSourceFloorTailLaplace epsilon b T ((r : ℂ) - z) := by
  have hmeas : AEMeasurable
      (fun t => ENNReal.ofReal (routePSourceFloorDensity epsilon b r t))
      (volume.restrict (Ioi T)) :=
    (measurable_routePSourceFloorDensity epsilon b r).ennreal_ofReal
      |>.aemeasurable.restrict
  have hnonneg := routePSourceFloorDensity_nonneg_ae hpos (r := r)
  rw [complexMGF, routePSourceFloorMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold routePSourceFloorTailLaplace
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with t ht hden
  rw [ENNReal.toReal_ofReal hden, Complex.real_smul]
  simp only [id_eq]
  unfold routePSourceFloorDensity
  push_cast
  calc
    Complex.exp (-(r : ℂ) * (t : ℂ)) *
        (routePSourceFloorPerturbation epsilon b t : ℂ) *
        Complex.exp (z * (t : ℂ)) =
      (Complex.exp (-(r : ℂ) * (t : ℂ)) *
        Complex.exp (z * (t : ℂ))) *
        (routePSourceFloorPerturbation epsilon b t : ℂ) := by ring
    _ = Complex.exp (-((r : ℂ) - z) * (t : ℂ)) *
        (routePSourceFloorPerturbation epsilon b t : ℂ) := by
      have heq : -(r : ℂ) * (t : ℂ) + z * (t : ℂ) =
          -((r : ℂ) - z) * (t : ℂ) := by ring
      rw [← Complex.exp_add, heq]

private def routePSourceFloorHeadLaplace (epsilon b T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..T, Complex.exp (-z * (t : ℂ)) *
    (routePSourceFloorPerturbation epsilon b t : ℂ)

private theorem differentiable_routePSourceFloorHeadLaplace (epsilon b T : ℝ) :
    Differentiable ℂ (routePSourceFloorHeadLaplace epsilon b T) := by
  intro z
  let rho : ℝ := |z.im| + 1
  let rho' : ℝ := |z.im| + 2
  have hrho : rho < rho' := by dsimp only [rho, rho']; linarith
  have hcont : Continuous (fun q : ℝ × ℂ =>
      Complex.exp (-q.2 * (q.1 : ℂ)) *
        (routePSourceFloorPerturbation epsilon b q.1 : ℂ)) := by
    have hQ : Continuous (fun q : ℝ × ℂ =>
        (routePSourceFloorPerturbation epsilon b q.1 : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((continuous_routePSourceFloorPerturbation epsilon b).comp continuous_fst)
    have hExp : Continuous (fun q : ℝ × ℂ =>
        Complex.exp (-q.2 * (q.1 : ℂ))) := by fun_prop
    exact hExp.mul hQ
  have hdiff : ∀ t : ℝ, DifferentiableOn ℂ
      (fun w : ℂ => Complex.exp (-w * (t : ℂ)) *
        (routePSourceFloorPerturbation epsilon b t : ℂ))
      (GaloisForLFunctions.HTGeometry.imStrip rho') := by
    intro t w hw
    exact (by fun_prop : DifferentiableAt ℂ
      (fun w : ℂ => Complex.exp (-w * (t : ℂ)) *
        (routePSourceFloorPerturbation epsilon b t : ℂ)) w)
      |>.differentiableWithinAt
  have hz : z ∈ GaloisForLFunctions.HTGeometry.imStrip rho := by
    apply GaloisForLFunctions.HTGeometry.mem_imStrip.mpr
    dsimp only [rho]
    linarith
  change DifferentiableAt ℂ
    (fun w => ∫ t in (0 : ℝ)..T,
      Complex.exp (-w * (t : ℂ)) *
        (routePSourceFloorPerturbation epsilon b t : ℂ)) z
  exact GaloisForLFunctions.HTGeometry.differentiableAt_intervalIntegral_of_holomorphic
    hrho hcont hdiff hz

private theorem routePSourceFloorKernel_eq_sum
    (epsilon b : ℝ) (z : ℂ) (t : ℝ) :
    Complex.exp (-z * (t : ℂ)) *
        (routePSourceFloorPerturbation epsilon b t : ℂ) =
      Complex.exp (-z * (t : ℂ)) *
          ((epsilon *
            GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t : ℝ) : ℂ) +
        (b : ℂ) * Complex.exp (-((z + 1 / 2) * (t : ℂ))) := by
  unfold routePSourceFloorPerturbation
  push_cast
  have hexp : Complex.exp (-z * (t : ℂ)) *
      Complex.exp (-(t : ℂ) / 2) =
      Complex.exp (-((z + 1 / 2) * (t : ℂ))) := by
    have heq : -z * (t : ℂ) + -(t : ℂ) / 2 =
        -((z + 1 / 2) * (t : ℂ)) := by ring
    rw [← Complex.exp_add, heq]
  calc
    _ =
      Complex.exp (-z * (t : ℂ)) *
          ((epsilon : ℂ) *
            (GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t : ℂ)) +
        (b : ℂ) *
          (Complex.exp (-z * (t : ℂ)) * Complex.exp (-(t : ℂ) / 2)) := by ring
    _ = _ := by rw [hexp]

private theorem integrableOn_routePSourceFloorComplexKernel
    (epsilon b : ℝ) {z : ℂ} (hz : 1 / 2 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ)) *
      (routePSourceFloorPerturbation epsilon b t : ℂ)) (Ioi 0) := by
  have hSigned := integrableOn_routePSourceSignedComplexKernel epsilon hz
  have hCorr : IntegrableOn (fun t : ℝ =>
      (b : ℂ) * Complex.exp (-((z + 1 / 2) * (t : ℂ)))) (Ioi 0) := by
    apply Integrable.const_mul
    exact integrableOn_Ioi_cexp_neg_mul (b := z + 1 / 2) (by
      norm_num [Complex.add_re] at hz ⊢
      linarith)
  apply (hSigned.add hCorr).congr
  filter_upwards with t
  simp only [Pi.add_apply]
  exact (routePSourceFloorKernel_eq_sum epsilon b z t).symm

private theorem routePSourceFloorFullLaplace_eq
    (epsilon b : ℝ) {z : ℂ} (hz : 1 / 2 < z.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-z * (t : ℂ)) *
      (routePSourceFloorPerturbation epsilon b t : ℂ)) =
      (epsilon : ℂ) * routePSourceLaplaceContinuation z +
        (b : ℂ) / (z + 1 / 2) := by
  have hSigned := integrableOn_routePSourceSignedComplexKernel epsilon hz
  have hCorr : IntegrableOn (fun t : ℝ =>
      (b : ℂ) * Complex.exp (-((z + 1 / 2) * (t : ℂ)))) (Ioi 0) := by
    apply Integrable.const_mul
    exact integrableOn_Ioi_cexp_neg_mul (b := z + 1 / 2) (by
      norm_num [Complex.add_re] at hz ⊢
      linarith)
  have hEq : (∫ t in Ioi (0 : ℝ), Complex.exp (-z * (t : ℂ)) *
      (routePSourceFloorPerturbation epsilon b t : ℂ)) =
      (∫ t in Ioi (0 : ℝ), Complex.exp (-z * (t : ℂ)) *
        ((epsilon *
          GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t : ℝ) : ℂ)) +
      ∫ t in Ioi (0 : ℝ),
        (b : ℂ) * Complex.exp (-((z + 1 / 2) * (t : ℂ))) := by
    rw [← integral_add hSigned hCorr]
    apply integral_congr_ae
    filter_upwards with t
    exact routePSourceFloorKernel_eq_sum epsilon b z t
  rw [hEq, integral_const_mul, integral_Ioi_cexp_neg_mul (b := z + 1 / 2) (by
    norm_num [Complex.add_re] at hz ⊢
    linarith)]
  have hSource :
      (∫ t in Ioi (0 : ℝ), Complex.exp (-z * (t : ℂ)) *
        ((epsilon *
          GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t : ℝ) : ℂ)) =
      (epsilon : ℂ) * routePSourceLaplaceContinuation z := by
    rw [routePSourceLaplaceContinuation_eq_laplace hz]
    unfold GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventLaplace
      ccmAbelLaplaceTail
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    push_cast
    ring
  rw [hSource]
  ring

private theorem routePSourceFloorTailLaplace_eq_continuation_sub_head
    {epsilon b T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : 1 / 2 < z.re) :
    routePSourceFloorTailLaplace epsilon b T z =
      (epsilon : ℂ) * routePSourceLaplaceContinuation z +
        (b : ℂ) / (z + 1 / 2) -
        routePSourceFloorHeadLaplace epsilon b T z := by
  let f : ℝ → ℂ := fun t => Complex.exp (-z * (t : ℂ)) *
    (routePSourceFloorPerturbation epsilon b t : ℂ)
  have hfull : IntegrableOn f (Ioi 0) :=
    integrableOn_routePSourceFloorComplexKernel epsilon b hz
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
  have hheadEq : routePSourceFloorHeadLaplace epsilon b T z =
      ∫ t in Ioc (0 : ℝ) T, f t := by
    unfold routePSourceFloorHeadLaplace
    rw [intervalIntegral.integral_of_le hT]
  have htailEq : routePSourceFloorTailLaplace epsilon b T z =
      ∫ t in Ioi T, f t := rfl
  have hfullEq : (∫ t in Ioi (0 : ℝ), f t) =
      (epsilon : ℂ) * routePSourceLaplaceContinuation z +
        (b : ℂ) / (z + 1 / 2) :=
    routePSourceFloorFullLaplace_eq epsilon b hz
  rw [← hheadEq, ← htailEq, hfullEq] at hsplit
  linear_combination -hsplit

private def routePSourceFloorLandauContinuation (epsilon b T : ℝ) (w : ℂ) : ℂ :=
  (epsilon : ℂ) * routePSourceLaplaceContinuation ((1 : ℂ) - w) +
    (b : ℂ) / (((1 : ℂ) - w) + 1 / 2) -
    routePSourceFloorHeadLaplace epsilon b T ((1 : ℂ) - w)

private theorem differentiableOn_routePSourceFloorLandauContinuation_closedBall
    (epsilon b T : ℝ) :
    DifferentiableOn ℂ (routePSourceFloorLandauContinuation epsilon b T)
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
  have hden : ((1 : ℂ) - w) + 1 / 2 ≠ 0 := by
    apply ne_zero_of_re_pos
    have hre := Complex.re_le_norm w
    norm_num [Complex.add_re, Complex.sub_re] at hre ⊢
    linarith
  have hCorr : DifferentiableAt ℂ (fun s : ℂ =>
      (b : ℂ) / (s + 1 / 2)) ((1 : ℂ) - w) := by
    fun_prop (disch := assumption)
  have hHead : DifferentiableAt ℂ (routePSourceFloorHeadLaplace epsilon b T)
      ((1 : ℂ) - w) := differentiable_routePSourceFloorHeadLaplace epsilon b T _
  have hinner : DifferentiableAt ℂ (fun v : ℂ => (1 : ℂ) - v) w := by fun_prop
  have houter : DifferentiableAt ℂ
      (fun s : ℂ => (epsilon : ℂ) * routePSourceLaplaceContinuation s +
        (b : ℂ) / (s + 1 / 2) - routePSourceFloorHeadLaplace epsilon b T s)
      ((1 : ℂ) - w) :=
    ((hF.const_mul (epsilon : ℂ)).add hCorr).sub hHead
  exact (houter.comp w hinner).differentiableWithinAt

private theorem routePSourceFloorLandauContinuation_eventuallyEq_complexMGF
    {epsilon b T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ routePSourceFloorPerturbation epsilon b t) :
    routePSourceFloorLandauContinuation epsilon b T =ᶠ[𝓝 0]
      complexMGF id (routePSourceFloorMeasure epsilon b 1 T) := by
  have hopen : {w : ℂ | 1 / 2 < ((1 : ℂ) - w).re} ∈ 𝓝 (0 : ℂ) := by
    have hOpen : IsOpen {w : ℂ | 1 / 2 < ((1 : ℂ) - w).re} :=
      isOpen_lt continuous_const
        (Complex.continuous_re.comp (continuous_const.sub continuous_id))
    exact hOpen.mem_nhds (by norm_num)
  filter_upwards [hopen] with w hw
  change (epsilon : ℂ) * routePSourceLaplaceContinuation ((1 : ℂ) - w) +
      (b : ℂ) / (((1 : ℂ) - w) + 1 / 2) -
      routePSourceFloorHeadLaplace epsilon b T ((1 : ℂ) - w) =
        complexMGF id (routePSourceFloorMeasure epsilon b 1 T) w
  rw [← routePSourceFloorTailLaplace_eq_continuation_sub_head hT hw]
  simpa using
    (complexMGF_id_routePSourceFloorMeasure_eq_tailLaplace
      (r := 1) hpos w).symm

private theorem integrable_exp_nine_eighth_routePSourceFloorMeasure
    {epsilon b T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ routePSourceFloorPerturbation epsilon b t) :
    Integrable (fun t : ℝ => Real.exp ((9 / 8 : ℝ) * id t))
      (routePSourceFloorMeasure epsilon b 1 T) := by
  exact landau_complexMGF_integrable_transfer
    (id_nonneg_ae_routePSourceFloorMeasure hT)
    (zero_mem_interior_integrableExpSet_routePSourceFloorMeasure
      hT hpos (r := 1) (by norm_num))
    (R := (5 / 4 : NNReal))
    (by simpa using
      differentiableOn_routePSourceFloorLandauContinuation_closedBall epsilon b T)
    (routePSourceFloorLandauContinuation_eventuallyEq_complexMGF hT hpos)
    (rho := 9 / 8) (by norm_num) (by norm_num)

private theorem routePSourceFloorMeasure_moments_below_nine_eighth
    {epsilon b T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ routePSourceFloorPerturbation epsilon b t) :
    Iio (9 / 8 : ℝ) ⊆
      interior (integrableExpSet id (routePSourceFloorMeasure epsilon b 1 T)) := by
  apply interior_maximal ?_ isOpen_Iio
  intro rho hrho
  have hbig := integrable_exp_nine_eighth_routePSourceFloorMeasure hT hpos
  refine Integrable.mono' hbig ?_ ?_
  · exact (Real.measurable_exp.comp (measurable_const.mul measurable_id))
      |>.aestronglyMeasurable
  · filter_upwards [id_nonneg_ae_routePSourceFloorMeasure hT] with t ht
    simp only [id_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hrho.le ht)

private theorem analyticOnNhd_routePSourceFloorMGF
    {epsilon b T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ routePSourceFloorPerturbation epsilon b t) :
    AnalyticOnNhd ℂ (complexMGF id (routePSourceFloorMeasure epsilon b 1 T))
      {w : ℂ | w.re < 9 / 8} := by
  intro w hw
  exact analyticAt_complexMGF
    (routePSourceFloorMeasure_moments_below_nine_eighth hT hpos hw)

private def routePSourceLaplaceUnderFloor (epsilon b T : ℝ) (z : ℂ) : ℂ :=
  (complexMGF id (routePSourceFloorMeasure epsilon b 1 T) ((1 : ℂ) - z) +
    routePSourceFloorHeadLaplace epsilon b T z -
    (b : ℂ) / (z + 1 / 2)) / (epsilon : ℂ)

private theorem analyticOnNhd_routePSourceLaplaceUnderFloor
    {epsilon b T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ routePSourceFloorPerturbation epsilon b t)
    (hepsilon : epsilon ≠ 0) :
    AnalyticOnNhd ℂ (routePSourceLaplaceUnderFloor epsilon b T)
      {z : ℂ | -(1 / 8 : ℝ) < z.re} := by
  intro z hz
  change -(1 / 8 : ℝ) < z.re at hz
  have hshift : ((1 : ℂ) - z).re < 9 / 8 := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hMGF : AnalyticAt ℂ
      (complexMGF id (routePSourceFloorMeasure epsilon b 1 T)) ((1 : ℂ) - z) :=
    analyticOnNhd_routePSourceFloorMGF hT hpos _ hshift
  have haffine : AnalyticAt ℂ (fun w : ℂ => (1 : ℂ) - w) z := by fun_prop
  have hcomp : AnalyticAt ℂ (fun w : ℂ =>
      complexMGF id (routePSourceFloorMeasure epsilon b 1 T) ((1 : ℂ) - w)) z :=
    hMGF.comp haffine
  have hhead : AnalyticAt ℂ (routePSourceFloorHeadLaplace epsilon b T) z :=
    (differentiable_routePSourceFloorHeadLaplace epsilon b T).analyticAt z
  have hden : z + 1 / 2 ≠ 0 := by
    apply ne_zero_of_re_pos
    norm_num [Complex.add_re]
    linarith
  have hCorr : AnalyticAt ℂ (fun w : ℂ => (b : ℂ) / (w + 1 / 2)) z :=
    analyticAt_const.div (analyticAt_id.add analyticAt_const) hden
  have hene : (epsilon : ℂ) ≠ 0 := by exact_mod_cast hepsilon
  exact ((hcomp.add hhead).sub hCorr).div analyticAt_const hene

private theorem routePSourceLaplaceUnderFloor_eq_continuation
    {epsilon b T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ routePSourceFloorPerturbation epsilon b t)
    (hepsilon : epsilon ≠ 0)
    {z : ℂ} (hz : 1 / 2 < z.re) :
    routePSourceLaplaceUnderFloor epsilon b T z =
      routePSourceLaplaceContinuation z := by
  have hene : (epsilon : ℂ) ≠ 0 := by exact_mod_cast hepsilon
  have hmgf := complexMGF_id_routePSourceFloorMeasure_eq_tailLaplace
    (r := 1) hpos ((1 : ℂ) - z)
  have hmgf' : complexMGF id (routePSourceFloorMeasure epsilon b 1 T)
      ((1 : ℂ) - z) = routePSourceFloorTailLaplace epsilon b T z := by
    have hcoord : ((1 : ℝ) : ℂ) - ((1 : ℂ) - z) = z := by
      push_cast
      ring
    simpa only [hcoord] using hmgf
  have htail := routePSourceFloorTailLaplace_eq_continuation_sub_head
    (epsilon := epsilon) (b := b) (T := T) hT hz
  unfold routePSourceLaplaceUnderFloor
  rw [hmgf', htail]
  field_simp [hene]
  ring

private theorem not_eventual_routePSourceFloor
    (epsilon b T : ℝ) (hT : 0 ≤ T) (hepsilon : epsilon ≠ 0)
    (hpos : ∀ t, T < t → 0 ≤ routePSourceFloorPerturbation epsilon b t) :
    False := by
  exact no_routePSourceLaplace_analytic_extension_past_axis
    (routePSourceLaplaceUnderFloor epsilon b T)
    (analyticOnNhd_routePSourceLaplaceUnderFloor hT hpos hepsilon)
    (fun z hz => routePSourceLaplaceUnderFloor_eq_continuation
      hT hpos hepsilon hz)

theorem routePSource_cofinal_below_negative_sqrt_floor (B T : ℝ) :
    ∃ t : ℝ, T < t ∧
      GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t <
        -B * Real.exp (-t / 2) := by
  by_contra h
  push Not at h
  let T₀ := max 0 T
  have hT₀ : 0 ≤ T₀ := le_max_left _ _
  have hpos : ∀ t, T₀ < t → 0 ≤ routePSourceFloorPerturbation 1 B t := by
    intro t ht
    have htT : T < t := lt_of_le_of_lt (le_max_right _ _) ht
    have hbound := h t htT
    unfold routePSourceFloorPerturbation
    linarith
  exact not_eventual_routePSourceFloor 1 B T₀ hT₀ (by norm_num) hpos

theorem routePSource_cofinal_above_positive_sqrt_floor (B T : ℝ) :
    ∃ t : ℝ, T < t ∧
      B * Real.exp (-t / 2) <
        GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t := by
  by_contra h
  push Not at h
  let T₀ := max 0 T
  have hT₀ : 0 ≤ T₀ := le_max_left _ _
  have hpos : ∀ t, T₀ < t → 0 ≤ routePSourceFloorPerturbation (-1) B t := by
    intro t ht
    have htT : T < t := lt_of_le_of_lt (le_max_right _ _) ht
    have hbound := h t htT
    unfold routePSourceFloorPerturbation
    linarith
  exact not_eventual_routePSourceFloor (-1) B T₀ hT₀ (by norm_num) hpos

end
end RHTower

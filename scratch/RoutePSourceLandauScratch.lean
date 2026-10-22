import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePLandauDisk
import GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinResolventExponentialWidth
import GaloisForLFunctions.RHTower.LandauIntegralTransfer
import GaloisForLFunctions.HTGeometry.ClockParametricIntegralHolomorphy

open Complex MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

private def routePSourceSignedDensity (epsilon r t : ℝ) : ℝ :=
  epsilon * (Real.exp (-r * t) *
    GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t)

private def routePSourceLandauMeasure (epsilon r T : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi T)).withDensity
    (fun t => ENNReal.ofReal (routePSourceSignedDensity epsilon r t))

private theorem measurable_routePSourceSignedDensity (epsilon r : ℝ) :
    Measurable (routePSourceSignedDensity epsilon r) := by
  unfold routePSourceSignedDensity
  exact measurable_const.mul
    ((by fun_prop : Measurable (fun t : ℝ => Real.exp (-r * t))).mul
      GaloisForLFunctions.RHTower.continuous_criticalMellinChebyshevResolventRayRepresentative.measurable)

private theorem integrableOn_routePSourceSignedDensity
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

private theorem routePSourceSignedDensity_nonneg_ae
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

private theorem integrable_exp_mul_id_routePSourceLandauMeasure
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

private theorem zero_mem_interior_integrableExpSet_routePSourceLandauMeasure
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

private theorem id_nonneg_ae_routePSourceLandauMeasure
    {epsilon r T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂routePSourceLandauMeasure epsilon r T, 0 ≤ id t := by
  rw [routePSourceLandauMeasure]
  refine Filter.Eventually.filter_mono
    (MeasureTheory.withDensity_absolutelyContinuous _ _).ae_le ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact le_trans hT ht.le

private def routePSourceSignedTailLaplace (epsilon T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi T, Complex.exp (-z * (t : ℂ)) *
    ((epsilon *
      GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t : ℝ) : ℂ)

private theorem complexMGF_id_routePSourceLandauMeasure_eq_tailLaplace
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

private def routePSourceSignedHeadLaplace (epsilon T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..T, Complex.exp (-z * (t : ℂ)) *
    ((epsilon *
      GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t : ℝ) : ℂ)

private theorem differentiable_routePSourceSignedHeadLaplace (epsilon T : ℝ) :
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

private theorem integrableOn_routePSourceSignedComplexKernel
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

private theorem routePSourceSignedTailLaplace_eq_continuation_sub_head
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

private def routePSourceLandauContinuation (epsilon T : ℝ) (w : ℂ) : ℂ :=
  (epsilon : ℂ) * routePSourceLaplaceContinuation ((1 : ℂ) - w) -
    routePSourceSignedHeadLaplace epsilon T ((1 : ℂ) - w)

private theorem differentiableOn_routePSourceLandauContinuation_closedBall
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

private theorem routePSourceLandauContinuation_eventuallyEq_complexMGF
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

private theorem integrable_exp_nine_eighth_routePSourceLandauMeasure
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

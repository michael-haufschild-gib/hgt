import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourceLandauCarrier

/-!
# Constant-shift positive carrier for the literal Route P source

An eventual one-sided bound for the source makes its constant-shifted tail a
nonnegative measure. Its Laplace transform is source-faithful on the original
convergence half-plane. Landau transfer extends that positive tail to every
strictly positive real Laplace parameter, and its reconstructed source
continuation is analytic on `Re z > 0` under the bound. This is conditional
analytic leverage, not an unconditional source bound or RH proof.
-/

open Complex MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

abbrev routePSourceRay (t : ℝ) : ℝ :=
  GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t

def routePShiftedDensity (epsilon B r t : ℝ) : ℝ :=
  Real.exp (-r * t) * (epsilon * routePSourceRay t + B)

def routePShiftedMeasure (epsilon B r T : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi T)).withDensity
    (fun t => ENNReal.ofReal (routePShiftedDensity epsilon B r t))

theorem measurable_routePShiftedDensity (epsilon B r : ℝ) :
    Measurable (routePShiftedDensity epsilon B r) := by
  unfold routePShiftedDensity
  exact (by fun_prop : Measurable (fun t : ℝ => Real.exp (-r * t))).mul
    ((measurable_const.mul
      GaloisForLFunctions.RHTower.continuous_criticalMellinChebyshevResolventRayRepresentative.measurable).add
      measurable_const)

theorem integrableOn_routePShiftedDensity
    (epsilon B T r : ℝ) (hT : 0 ≤ T) (hr : 1 / 2 < r) :
    IntegrableOn (routePShiftedDensity epsilon B r) (Ioi T) := by
  have hsrc : IntegrableOn
      (fun t : ℝ => Real.exp (-r * t) * (epsilon * routePSourceRay t)) (Ioi T) := by
    have h := integrableOn_routePSourceSignedDensity epsilon T r hT hr
    apply h.congr
    filter_upwards with t
    dsimp [routePSourceSignedDensity, routePSourceRay]
    ring
  have hconst : IntegrableOn
      (fun t : ℝ => Real.exp (-r * t) * B) (Ioi T) := by
    have h := (exp_neg_integrableOn_Ioi T (by linarith : 0 < r)).mul_const B
    change Integrable (fun t : ℝ => Real.exp (-r * t) * B)
      (volume.restrict (Ioi T))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hsum := hsrc.add hconst
  apply hsum.congr
  filter_upwards with t
  dsimp [routePShiftedDensity]
  ring

theorem routePShiftedDensity_nonneg_ae
    {epsilon B r T : ℝ}
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B) :
    ∀ᵐ t ∂volume.restrict (Ioi T),
      0 ≤ routePShiftedDensity epsilon B r t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.exp_pos _).le (hpos t ht)

theorem integrable_exp_mul_id_routePShiftedMeasure
    {epsilon B r T rho : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B)
    (hr : 1 / 2 < r - rho) :
    Integrable (fun t : ℝ => Real.exp (rho * id t))
      (routePShiftedMeasure epsilon B r T) := by
  have hdens := integrableOn_routePShiftedDensity epsilon B T (r - rho) hT hr
  have hmeas : AEMeasurable
      (fun t => ENNReal.ofReal (routePShiftedDensity epsilon B r t))
      (volume.restrict (Ioi T)) :=
    (measurable_routePShiftedDensity epsilon B r).ennreal_ofReal
      |>.aemeasurable.restrict
  have hnonneg := routePShiftedDensity_nonneg_ae (r := r) hpos
  rw [routePShiftedMeasure,
    integrable_withDensity_iff_integrable_smul₀' hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply hdens.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with t ht hden
  rw [ENNReal.toReal_ofReal hden]
  simp only [id_eq, smul_eq_mul]
  unfold routePShiftedDensity
  rw [show -(r - rho) * t = -r * t + rho * t by ring, Real.exp_add]
  ring

theorem zero_mem_interior_integrableExpSet_routePShiftedMeasure
    {epsilon B r T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B)
    (hr : 1 / 2 < r) :
    0 ∈ interior (integrableExpSet id (routePShiftedMeasure epsilon B r T)) := by
  let delta : ℝ := (r - 1 / 2) / 2
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset
    (Ioo_mem_nhds (a := -delta) (b := delta) (by linarith) (by linarith)) ?_
  intro rho hrho
  exact integrable_exp_mul_id_routePShiftedMeasure hT hpos (by
    dsimp only [delta] at hrho
    linarith [hrho.2])

theorem id_nonneg_ae_routePShiftedMeasure
    {epsilon B T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂routePShiftedMeasure epsilon B 1 T, 0 ≤ id t := by
  rw [routePShiftedMeasure]
  refine Filter.Eventually.filter_mono
    (MeasureTheory.withDensity_absolutelyContinuous _ _).ae_le ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact le_trans hT ht.le

def routePShiftedTailLaplace
    (epsilon B T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi T, Complex.exp (-z * (t : ℂ)) *
    (((epsilon * routePSourceRay t + B : ℝ) : ℂ))

theorem complexMGF_id_routePShiftedMeasure_eq_tailLaplace
    {epsilon B r T : ℝ}
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B)
    (w : ℂ) :
    complexMGF id (routePShiftedMeasure epsilon B r T) w =
      routePShiftedTailLaplace epsilon B T ((r : ℂ) - w) := by
  have hmeas : AEMeasurable
      (fun t => ENNReal.ofReal (routePShiftedDensity epsilon B r t))
      (volume.restrict (Ioi T)) :=
    (measurable_routePShiftedDensity epsilon B r).ennreal_ofReal
      |>.aemeasurable.restrict
  have hnonneg := routePShiftedDensity_nonneg_ae (r := r) hpos
  rw [complexMGF, routePShiftedMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold routePShiftedTailLaplace
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with t ht hden
  rw [ENNReal.toReal_ofReal hden, Complex.real_smul]
  simp only [id_eq]
  unfold routePShiftedDensity
  push_cast
  rw [show
      (Complex.exp (-(r : ℂ) * (t : ℂ)) *
          ((epsilon : ℂ) * (routePSourceRay t : ℂ) + (B : ℂ))) *
          Complex.exp (w * (t : ℂ)) =
        (Complex.exp (-(r : ℂ) * (t : ℂ)) *
          Complex.exp (w * (t : ℂ))) *
          ((epsilon : ℂ) * (routePSourceRay t : ℂ) + (B : ℂ)) by ring]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem routePShiftedTailLaplace_eq_continuation_sub_head
    {epsilon B T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : 1 / 2 < z.re) :
    routePShiftedTailLaplace epsilon B T z =
      (epsilon : ℂ) * routePSourceLaplaceContinuation z -
        routePSourceSignedHeadLaplace epsilon T z +
        (B : ℂ) * Complex.exp (-z * (T : ℂ)) / z := by
  have hzpos : 0 < z.re := by linarith
  have hzneg : (-z).re < 0 := by simp [hzpos]
  have hconstExp :
      (∫ t in Ioi T, Complex.exp (-z * (t : ℂ))) =
        Complex.exp (-z * (T : ℂ)) / z := by
    simpa using (integral_exp_mul_complex_Ioi (a := -z) hzneg T)
  have hsrcInt : IntegrableOn
      (fun t : ℝ => Complex.exp (-z * (t : ℂ)) *
        ((epsilon * routePSourceRay t : ℝ) : ℂ)) (Ioi T) := by
    have h := integrableOn_routePSourceSignedComplexKernel epsilon hz
    exact h.mono_set (by intro t ht; exact lt_of_le_of_lt hT ht)
  have hconstInt : IntegrableOn
      (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (B : ℂ)) (Ioi T) := by
    change Integrable
      (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (B : ℂ))
      (volume.restrict (Ioi T))
    simpa using (integrableOn_exp_mul_complex_Ioi hzneg T).mul_const (B : ℂ)
  have hsplit : routePShiftedTailLaplace epsilon B T z =
      routePSourceSignedTailLaplace epsilon T z +
        (B : ℂ) * (∫ t in Ioi T, Complex.exp (-z * (t : ℂ))) := by
    unfold routePShiftedTailLaplace routePSourceSignedTailLaplace
    calc
      (∫ t in Ioi T, Complex.exp (-z * (t : ℂ)) *
        (((epsilon * routePSourceRay t + B : ℝ) : ℂ))) =
          ∫ t in Ioi T,
            (Complex.exp (-z * (t : ℂ)) *
                ((epsilon * routePSourceRay t : ℝ) : ℂ) +
              Complex.exp (-z * (t : ℂ)) * (B : ℂ)) := by
                apply integral_congr_ae
                filter_upwards with t
                push_cast
                ring
      _ = _ := by
        rw [integral_add hsrcInt hconstInt, integral_mul_const]
        ring
  rw [hsplit, routePSourceSignedTailLaplace_eq_continuation_sub_head hT hz,
    hconstExp]
  ring

def routePShiftedContinuation (epsilon B T : ℝ) (w : ℂ) : ℂ :=
  routePSourceLandauContinuation epsilon T w +
    (B : ℂ) * Complex.exp (-((1 : ℂ) - w) * (T : ℂ)) / ((1 : ℂ) - w)

theorem differentiableOn_routePShiftedContinuation_closedBall
    (epsilon B T : ℝ) {R : NNReal} (hR : (R : ℝ) < 1) :
    DifferentiableOn ℂ (routePShiftedContinuation epsilon B T)
      (Metric.closedBall 0 (R : ℝ)) := by
  have hbase : DifferentiableOn ℂ (routePSourceLandauContinuation epsilon T)
      (Metric.closedBall 0 (R : ℝ)) :=
    (differentiableOn_routePSourceLandauContinuation_closedBall epsilon T).mono (by
      intro w hw
      simp only [Metric.mem_closedBall, dist_zero_right] at hw ⊢
      exact hw.trans (by linarith))
  have hcorrection : DifferentiableOn ℂ
      (fun w : ℂ => (B : ℂ) *
        Complex.exp (-((1 : ℂ) - w) * (T : ℂ)) / ((1 : ℂ) - w))
      (Metric.closedBall 0 (R : ℝ)) := by
    intro w hw
    have hwNorm : ‖w‖ ≤ (R : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    have hden : (1 : ℂ) - w ≠ 0 := by
      intro hzero
      have hw1 : w = 1 := (sub_eq_zero.mp hzero).symm
      rw [hw1] at hwNorm
      simp at hwNorm
      linarith
    have hnum : DifferentiableAt ℂ
        (fun v : ℂ => (B : ℂ) *
          Complex.exp (-((1 : ℂ) - v) * (T : ℂ))) w := by fun_prop
    have hdenfun : DifferentiableAt ℂ
        (fun v : ℂ => (1 : ℂ) - v) w := by fun_prop
    exact (hnum.div hdenfun hden).differentiableWithinAt
  change DifferentiableOn ℂ
    (routePSourceLandauContinuation epsilon T +
      fun w : ℂ => (B : ℂ) *
        Complex.exp (-((1 : ℂ) - w) * (T : ℂ)) / ((1 : ℂ) - w))
    (Metric.closedBall 0 (R : ℝ))
  exact hbase.add hcorrection

theorem routePShiftedContinuation_eventuallyEq_complexMGF
    {epsilon B T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B) :
    routePShiftedContinuation epsilon B T =ᶠ[𝓝 0]
      complexMGF id (routePShiftedMeasure epsilon B 1 T) := by
  have hopen : {w : ℂ | 1 / 2 < ((1 : ℂ) - w).re} ∈ 𝓝 (0 : ℂ) := by
    have hOpen : IsOpen {w : ℂ | 1 / 2 < ((1 : ℂ) - w).re} :=
      isOpen_lt continuous_const
        (Complex.continuous_re.comp (continuous_const.sub continuous_id))
    exact hOpen.mem_nhds (by norm_num)
  filter_upwards [hopen] with w hw
  have hmgf := complexMGF_id_routePShiftedMeasure_eq_tailLaplace
    (r := 1) hpos w
  have htail := routePShiftedTailLaplace_eq_continuation_sub_head
    (epsilon := epsilon) (B := B) (T := T) hT hw
  have hcoord : ((1 : ℝ) : ℂ) - w = (1 : ℂ) - w := by push_cast; ring
  rw [hcoord] at hmgf
  unfold routePShiftedContinuation
  rw [hmgf, htail]
  unfold routePSourceLandauContinuation
  ring

theorem integrable_exp_below_one_routePShiftedMeasure
    {epsilon B T rho : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    Integrable (fun t : ℝ => Real.exp (rho * id t))
      (routePShiftedMeasure epsilon B 1 T) := by
  let R : NNReal := ⟨(rho + 1) / 2, by linarith⟩
  have hR : (R : ℝ) < 1 := by
    change (rho + 1) / 2 < 1
    linarith
  have hrhoR : rho < (R : ℝ) := by
    change rho < (rho + 1) / 2
    linarith
  exact landau_complexMGF_integrable_transfer
    (id_nonneg_ae_routePShiftedMeasure hT)
    (zero_mem_interior_integrableExpSet_routePShiftedMeasure
      hT hpos (r := 1) (by norm_num))
    (R := R)
    (differentiableOn_routePShiftedContinuation_closedBall epsilon B T hR)
    (routePShiftedContinuation_eventuallyEq_complexMGF hT hpos)
    hrho0 hrhoR

theorem routePShiftedMeasure_moments_below_one
    {epsilon B T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B) :
    Iio (1 : ℝ) ⊆
      interior (integrableExpSet id (routePShiftedMeasure epsilon B 1 T)) := by
  apply interior_maximal ?_ isOpen_Iio
  intro rho hrho
  let rho' : ℝ := max rho 0
  have hrho0' : 0 ≤ rho' := le_max_right rho 0
  have hrho1' : rho' < 1 := by
    dsimp [rho']
    exact max_lt hrho (by norm_num)
  have hrhole : rho ≤ rho' := le_max_left rho 0
  have hbig := integrable_exp_below_one_routePShiftedMeasure
    hT hpos hrho0' hrho1'
  refine Integrable.mono' hbig ?_ ?_
  · exact (Real.measurable_exp.comp (measurable_const.mul measurable_id))
      |>.aestronglyMeasurable
  · filter_upwards [id_nonneg_ae_routePShiftedMeasure hT] with t ht
    simp only [id_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hrhole ht)

theorem analyticOnNhd_routePShiftedMGF
    {epsilon B T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B) :
    AnalyticOnNhd ℂ (complexMGF id (routePShiftedMeasure epsilon B 1 T))
      {w : ℂ | w.re < 1} := by
  intro w hw
  exact analyticAt_complexMGF
    (routePShiftedMeasure_moments_below_one hT hpos hw)

def routePSourceLaplaceUnderShift
    (epsilon B T : ℝ) (z : ℂ) : ℂ :=
  (complexMGF id (routePShiftedMeasure epsilon B 1 T) ((1 : ℂ) - z) +
    routePSourceSignedHeadLaplace epsilon T z -
    (B : ℂ) * Complex.exp (-z * (T : ℂ)) / z) / (epsilon : ℂ)

theorem analyticOnNhd_routePSourceLaplaceUnderShift
    {epsilon B T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B)
    (hepsilon : epsilon ≠ 0) :
    AnalyticOnNhd ℂ (routePSourceLaplaceUnderShift epsilon B T)
      {z : ℂ | 0 < z.re} := by
  intro z hz
  change 0 < z.re at hz
  have hshift : ((1 : ℂ) - z).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hMGF : AnalyticAt ℂ
      (complexMGF id (routePShiftedMeasure epsilon B 1 T)) ((1 : ℂ) - z) :=
    analyticOnNhd_routePShiftedMGF hT hpos _ hshift
  have haffine : AnalyticAt ℂ (fun w : ℂ => (1 : ℂ) - w) z := by fun_prop
  have hcomp : AnalyticAt ℂ (fun w : ℂ =>
      complexMGF id (routePShiftedMeasure epsilon B 1 T) ((1 : ℂ) - w)) z :=
    hMGF.comp haffine
  have hhead : AnalyticAt ℂ (routePSourceSignedHeadLaplace epsilon T) z :=
    (differentiable_routePSourceSignedHeadLaplace epsilon T).analyticAt z
  have hnum : AnalyticAt ℂ
      (fun w : ℂ => (B : ℂ) * Complex.exp (-w * (T : ℂ))) z := by fun_prop
  have hz0 : z ≠ 0 := ne_zero_of_re_pos hz
  have hcorr : AnalyticAt ℂ
      (fun w : ℂ => (B : ℂ) * Complex.exp (-w * (T : ℂ)) / w) z :=
    hnum.div analyticAt_id hz0
  have heps : (epsilon : ℂ) ≠ 0 := by exact_mod_cast hepsilon
  change AnalyticAt ℂ
    (fun w : ℂ =>
      (complexMGF id (routePShiftedMeasure epsilon B 1 T) ((1 : ℂ) - w) +
        routePSourceSignedHeadLaplace epsilon T w -
        (B : ℂ) * Complex.exp (-w * (T : ℂ)) / w) / (epsilon : ℂ)) z
  exact ((hcomp.add hhead).sub hcorr).div analyticAt_const heps

theorem routePSourceLaplaceUnderShift_eq_continuation
    {epsilon B T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ epsilon * routePSourceRay t + B)
    (hepsilon : epsilon ≠ 0)
    {z : ℂ} (hz : 1 / 2 < z.re) :
    routePSourceLaplaceUnderShift epsilon B T z =
      routePSourceLaplaceContinuation z := by
  have heps : (epsilon : ℂ) ≠ 0 := by exact_mod_cast hepsilon
  have hz0 : z ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hmgf := complexMGF_id_routePShiftedMeasure_eq_tailLaplace
    (r := 1) hpos ((1 : ℂ) - z)
  have htail := routePShiftedTailLaplace_eq_continuation_sub_head
    (epsilon := epsilon) (B := B) (T := T) hT hz
  have hcoord : ((1 : ℝ) : ℂ) - ((1 : ℂ) - z) = z := by push_cast; ring
  rw [hcoord] at hmgf
  unfold routePSourceLaplaceUnderShift
  rw [hmgf, htail]
  field_simp [heps, hz0]
  ring

end
end RHTower

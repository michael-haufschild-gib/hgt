import GaloisForLFunctions.RHTower.ThetaGaussianCovarianceMeasure

/-! The literal diagonal covariance has an adverse integrated contribution.
The lost sign is exactly the positive variance of the quadratic source profile. -/

noncomputable section
open Set MeasureTheory Filter Topology
namespace RHTower.ThetaGaussianCoarea

local notation "c" => thetaCuspLogCurvature

theorem coareaMass_eq_centerKernel : coareaMass=thetaTailFirstMomentKernel 0 0 := by
  have h := thetaTailFirstMomentKernel_commonShift_eq_tail 0 0 0
  simp only [add_zero] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards with t
  unfold coareaWeight thetaTailCommonTranslationIntegrand
  ring

/-- The weighted time chart is exactly the original center coarea density. -/
theorem coarea_integral_chart (f : ℝ → ℝ) :
    (∫ u in Ioi 0, density 0 0 u*f u)=
      (∫ t in Ioi 0, coareaWeight t*f (t^2))/thetaCuspFullSource 0^2 := by
  have hinj : InjOn (coordinate 0 0) (Ioi 0) := by
    intro a ha b hb he
    have h := congrArg (shift 0 0) he
    simpa only [shift_coordinate (le_refl 0) (le_refl 0) ha.le,
      shift_coordinate (le_refl 0) (le_refl 0) hb.le] using h
  have himage : coordinate 0 0 '' Ioi 0=Ioi 0 := by
    ext u
    constructor
    · rintro ⟨t,ht,rfl⟩
      have ht0 : (0:ℝ) < t := ht
      simpa only [coordinate,add_zero,mem_Ioi] using mul_pos ht0 ht0
    · intro hu
      exact ⟨shift 0 0 u,shift_pos (le_refl 0) (le_refl 0) hu,coordinate_shift hu.le⟩
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t (_ : t ∈ Ioi (0:ℝ)) => (coordinate_hasDerivAt 0 0 t).hasDerivWithinAt)
    hinj (fun u => density 0 0 u*f u)
  rw [himage] at he
  rw [he,← integral_div]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0:ℝ) < t := ht
  rw [smul_eq_mul,abs_of_pos (by linarith : (0:ℝ)+0+2*t>0),density_eq,
    shift_coordinate (le_refl 0) (le_refl 0) ht.le]
  simp only [zero_add,coordinate,add_zero]
  unfold coareaWeight
  simp only [pow_two]
  ring

/-- No alternative measure is introduced by the time-chart covariance. -/
theorem coareaAverage_eq_densityAverage (f : ℝ → ℝ) :
    coareaAverage (fun t => f (t^2))=
      (∫ u in Ioi 0, density 0 0 u*f u)/(∫ u in Ioi 0, density 0 0 u) := by
  rw [coarea_integral_chart,integral_density (le_refl 0) (le_refl 0),← coareaMass_eq_centerKernel]
  unfold coareaAverage
  field_simp [(thetaCuspFullSource_pos_all 0).ne',coareaMass_pos.ne']

def diagonalScoreCovariance (x : ℝ) : ℝ :=
  coareaAverage (fun t => amplitude x (t^2)*covarianceScore x (t^2))-
    coareaAverage (fun t => amplitude x (t^2))*coareaAverage (fun t => covarianceScore x (t^2))

theorem diagonalScoreCovariance_eq (x : ℝ) : diagonalScoreCovariance x=
    (∫ u in Ioi 0, density 0 0 u*(amplitude x u*covarianceScore x u))/(∫ u in Ioi 0, density 0 0 u)-
      ((∫ u in Ioi 0, density 0 0 u*amplitude x u)/(∫ u in Ioi 0, density 0 0 u))*
        ((∫ u in Ioi 0, density 0 0 u*covarianceScore x u)/(∫ u in Ioi 0, density 0 0 u)) := by
  unfold diagonalScoreCovariance
  rw [coareaAverage_eq_densityAverage (fun u => amplitude x u*covarianceScore x u),
    coareaAverage_eq_densityAverage (amplitude x),coareaAverage_eq_densityAverage (covarianceScore x)]

private theorem defect_measurable (x : ℝ) : Measurable (amplitudeDefect x) := by
  exact ((continuous_const.sub ((amplitude_continuous x).comp (continuous_id.pow 2))).div_const
    (x^2)).measurable

private theorem score_measurable (x : ℝ) : Measurable (scoreDefect x) := by
  have hp : Continuous thetaCuspLogDecaySlope := continuous_iff_continuousAt.mpr
    fun t => (hasDerivAt_thetaCuspLogDecaySlope t).continuousAt
  have hs : Continuous (fun t : ℝ => shift x 0 (t^2)) := by
    unfold shift length
    fun_prop
  have hl : Continuous (fun t : ℝ => length x 0 (t^2)) := by unfold length; fun_prop
  have hL : Measurable (fun t => leftDerivative x 0 (t^2)) := by
    unfold leftDerivative
    have hpx := (hp.comp ((continuous_const (y := x)).add hs)).measurable
    have hps := (hp.comp ((continuous_const (y := (0:ℝ))).add hs)).measurable
    exact (hpx.sub measurable_const).sub
      ((hs.measurable.mul (hpx.add hps)).div hl.measurable)
  exact (((((amplitude_continuous x).comp (continuous_id.pow 2)).measurable).mul
    (measurable_const.add (measurable_const.mul hL))).sub measurable_const).div_const (x^2)

private theorem weighted_integrable {f : ℝ → ℝ} {M : ℝ} (hm : Measurable f)
    (hb : ∀ t : ℝ, 0 < t → |f t| ≤ M*(1+c (t+1)^2)) :
    IntegrableOn (fun t => coareaWeight t*f t) (Ioi 0) := by
  apply (coareaEnvelope_integrable.const_mul M).mono'
    ((coareaWeight_continuous.measurable.mul hm).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖coareaWeight t*f t‖ ≤ _
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (coareaWeight_pos ht)]
  nlinarith only [mul_le_mul_of_nonneg_left (hb t ht) (coareaWeight_pos ht).le]

private theorem weighted_limit {F : ℝ → ℝ → ℝ} {f : ℝ → ℝ} {M : ℝ}
    (hm : ∀ x, Measurable (F x))
    (hb : ∀ x, 0 < x → x ≤ 1 → ∀ t, 0 < t → |F x t| ≤ M*(1+c (t+1)^2))
    (hl : ∀ t, 0 < t → Tendsto (fun x => F x t) (𝓝[>] 0) (𝓝 (f t))) :
    Tendsto (fun x => coareaAverage (F x)) (𝓝[>] 0) (𝓝 (coareaAverage f)) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0:ℝ))) (fun t => M*(coareaWeight t*(1+c (t+1)^2)))
    (Eventually.of_forall fun x => (coareaWeight_continuous.measurable.mul (hm x)).aestronglyMeasurable)
    (show ∀ᶠ x : ℝ in 𝓝[>] 0, ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      ‖coareaWeight t*F x t‖ ≤ M*(coareaWeight t*(1+c (t+1)^2)) from by
      filter_upwards [eventually_small_positive_nodes] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (coareaWeight_pos ht)]
      nlinarith only [mul_le_mul_of_nonneg_left (hb x hx.1 hx.2 t ht) (coareaWeight_pos ht).le])
    (coareaEnvelope_integrable.const_mul M)
    (show ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      Tendsto (fun x => coareaWeight t*F x t) (𝓝[>] 0) (𝓝 (coareaWeight t*f t)) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hl t ht).const_mul _)
  exact h.div_const coareaMass

private theorem defect_bound {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (t : ℝ) (ht : 0 < t) :
    |amplitudeDefect x t| ≤ 1*(1+c (t+1)^2) := by
  have h := amplitudeDefect_bound hx hx1 ht
  nlinarith only [h,sq_nonneg (c (t+1)-1/2)]

private theorem score_bound {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (t : ℝ) (ht : 0 < t) :
    |scoreDefect x t| ≤ 2*(1+c (t+1)^2) := by
  have h := scoreDefect_bound hx hx1 ht
  nlinarith only [h,sq_nonneg (c (t+1)-1/2)]

private theorem product_bound {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (t : ℝ) (ht : 0 < t) :
    |amplitudeDefect x t*scoreDefect x t| ≤ 2*(1+c (t+1)^2) := by
  rw [abs_mul]
  have hm := mul_le_mul (amplitudeDefect_bound hx hx1 ht) (scoreDefect_bound hx hx1 ht)
    (abs_nonneg _) (thetaCuspLogCurvature_pos (t+1)).le
  nlinarith only [hm]

theorem coareaAverage_amplitudeDefect_limit :
    Tendsto (fun x => coareaAverage (amplitudeDefect x)) (𝓝[>] 0) (𝓝 (coareaAverage quadraticProfile)) :=
  weighted_limit defect_measurable (fun _ hx hx1 => defect_bound hx hx1)
    (fun _ ht => amplitudeDefect_limit ht)

theorem coareaAverage_scoreDefect_limit :
    Tendsto (fun x => coareaAverage (scoreDefect x)) (𝓝[>] 0) (𝓝 (coareaAverage quadraticProfile)) :=
  weighted_limit score_measurable (fun _ hx hx1 => score_bound hx hx1)
    (fun _ ht => scoreDefect_limit ht)

theorem coareaAverage_defectProduct_limit :
    Tendsto (fun x => coareaAverage (fun t => amplitudeDefect x t*scoreDefect x t))
      (𝓝[>] 0) (𝓝 (coareaAverage (fun t => quadraticProfile t^2))) := by
  apply weighted_limit (fun x => (defect_measurable x).mul (score_measurable x))
    (fun _ hx hx1 => product_bound hx hx1)
  intro t ht
  simpa only [pow_two,Pi.mul_apply] using (amplitudeDefect_limit ht).mul (scoreDefect_limit ht)

theorem quadraticVariance_eq : quadraticVariance=
    coareaAverage (fun t => quadraticProfile t^2)-(coareaAverage quadraticProfile)^2 := by
  let m := coareaAverage quadraticProfile
  have hi : (fun t => coareaWeight t*(quadraticProfile t-m)^2)=
      (fun t => (coareaWeight t*quadraticProfile t^2-2*m*(coareaWeight t*quadraticProfile t))+
        m^2*coareaWeight t) := by funext t; ring
  have hs : IntegrableOn (fun t => coareaWeight t*quadraticProfile t^2-
      2*m*(coareaWeight t*quadraticProfile t)) (Ioi 0) := by
    convert! coareaWeight_profile_sq_integrable.sub
      (coareaWeight_profile_integrable.const_mul (2*m)) using 1
  change (∫ t in Ioi 0, coareaWeight t*(quadraticProfile t-m)^2)/coareaMass=_
  rw [hi,integral_add hs
    (coareaWeight_integrable.const_mul (m^2)),
    integral_sub coareaWeight_profile_sq_integrable (coareaWeight_profile_integrable.const_mul (2*m)),
    integral_const_mul,integral_const_mul]
  change ((∫ t in Ioi 0, coareaWeight t*quadraticProfile t^2)-
    2*m*(∫ t in Ioi 0, coareaWeight t*quadraticProfile t)+m^2*coareaMass)/coareaMass=_
  unfold m coareaAverage
  field_simp [coareaMass_pos.ne']
  ring

theorem diagonalScoreCovariance_defects {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    diagonalScoreCovariance x/x^4=
      -coareaAverage (fun t => amplitudeDefect x t*scoreDefect x t)+
        coareaAverage (amplitudeDefect x)*coareaAverage (scoreDefect x) := by
  have hD := weighted_integrable (defect_measurable x) (defect_bound hx hx1)
  have hE := weighted_integrable (score_measurable x) (score_bound hx hx1)
  have hDE : IntegrableOn (fun t => coareaWeight t*(amplitudeDefect x t*scoreDefect x t)) (Ioi 0) := by
    simpa only [Pi.mul_apply] using weighted_integrable
      ((defect_measurable x).mul (score_measurable x)) (product_bound hx hx1)
  have hsum : IntegrableOn (fun t => coareaWeight t+x^2*(coareaWeight t*scoreDefect x t)) (Ioi 0) := by
    convert! coareaWeight_integrable.add (hE.const_mul (x^2)) using 1
  have hdiff : IntegrableOn (fun t => (coareaWeight t+x^2*(coareaWeight t*scoreDefect x t))-
      x^2*(coareaWeight t*amplitudeDefect x t)) (Ioi 0) := by
    convert! hsum.sub (hD.const_mul (x^2)) using 1
  have hA (t : ℝ) : amplitude x (t^2)=1-x^2*amplitudeDefect x t := by
    unfold amplitudeDefect
    field_simp [hx.ne']
    ring
  have hB (t : ℝ) : covarianceScore x (t^2)=1+x^2*scoreDefect x t := by
    unfold scoreDefect
    field_simp [hx.ne']
    ring
  have hIA : (∫ t in Ioi 0, coareaWeight t*amplitude x (t^2))=
      coareaMass-x^2*(∫ t in Ioi 0, coareaWeight t*amplitudeDefect x t) := by
    simp_rw [hA,show ∀ t : ℝ, coareaWeight t*(1-x^2*amplitudeDefect x t)=
      coareaWeight t-x^2*(coareaWeight t*amplitudeDefect x t) by intro t; ring]
    rw [integral_sub coareaWeight_integrable (hD.const_mul _),integral_const_mul]
    rfl
  have hIB : (∫ t in Ioi 0, coareaWeight t*covarianceScore x (t^2))=
      coareaMass+x^2*(∫ t in Ioi 0, coareaWeight t*scoreDefect x t) := by
    simp_rw [hB,show ∀ t : ℝ, coareaWeight t*(1+x^2*scoreDefect x t)=
      coareaWeight t+x^2*(coareaWeight t*scoreDefect x t) by intro t; ring]
    rw [integral_add coareaWeight_integrable (hE.const_mul _),integral_const_mul]
    rfl
  have hIP : (∫ t in Ioi 0, coareaWeight t*(amplitude x (t^2)*covarianceScore x (t^2)))=
      coareaMass+x^2*(∫ t in Ioi 0, coareaWeight t*scoreDefect x t)-
        x^2*(∫ t in Ioi 0, coareaWeight t*amplitudeDefect x t)-
        x^4*(∫ t in Ioi 0, coareaWeight t*(amplitudeDefect x t*scoreDefect x t)) := by
    simp_rw [hA,hB,show ∀ t : ℝ,
      coareaWeight t*((1-x^2*amplitudeDefect x t)*(1+x^2*scoreDefect x t))=
      ((coareaWeight t+x^2*(coareaWeight t*scoreDefect x t))-
        x^2*(coareaWeight t*amplitudeDefect x t))-
        x^4*(coareaWeight t*(amplitudeDefect x t*scoreDefect x t)) by intro t; ring]
    rw [integral_sub hdiff (hDE.const_mul _),
      integral_sub hsum (hD.const_mul _),
      integral_add coareaWeight_integrable (hE.const_mul _),
      integral_const_mul,integral_const_mul,integral_const_mul]
    rfl
  unfold diagonalScoreCovariance coareaAverage
  rw [hIA,hIB,hIP]
  field_simp [hx.ne',coareaMass_pos.ne']
  ring

/-- The complete half-line covariance contribution has an exact negative variance limit. -/
theorem diagonalScoreCovariance_ratio_limit :
    Tendsto (fun x => diagonalScoreCovariance x/x^4) (𝓝[>] 0) (𝓝 (-quadraticVariance)) := by
  have h := coareaAverage_defectProduct_limit.neg.add
    (coareaAverage_amplitudeDefect_limit.mul coareaAverage_scoreDefect_limit)
  rw [quadraticVariance_eq]
  have he : (fun x => diagonalScoreCovariance x/x^4) =ᶠ[𝓝[>] 0]
      (fun x => -coareaAverage (fun t => amplitudeDefect x t*scoreDefect x t)+
        coareaAverage (amplitudeDefect x)*coareaAverage (scoreDefect x)) := by
    filter_upwards [eventually_small_positive_nodes] with x hx
    exact diagonalScoreCovariance_defects hx.1 hx.2
  apply Filter.Tendsto.congr' he.symm
  convert! h using 1
  ring

theorem diagonalScoreCovariance_eventually_neg :
    ∀ᶠ x : ℝ in 𝓝[>] 0, diagonalScoreCovariance x < 0 := by
  have h := diagonalScoreCovariance_ratio_limit.eventually
    (gt_mem_nhds (neg_lt_zero.mpr quadraticVariance_pos))
  filter_upwards [eventually_small_positive_nodes,h] with x hx hneg
  have he := (div_lt_iff₀ (pow_pos hx.1 4)).mp hneg
  simpa only [zero_mul] using he

end RHTower.ThetaGaussianCoarea

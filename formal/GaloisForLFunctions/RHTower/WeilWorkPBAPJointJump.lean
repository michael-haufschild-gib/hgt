import GaloisForLFunctions.RHTower.WeilWorkPBAPJointEnergy
import GaloisForLFunctions.RHTower.WeilPositivitySummableWeightsObstruction

/-!
# Physical jump formulas for actual paired Weil tests

The Gamma integral has its exact physical autocorrelation normalization and is
integrable at the origin. Both signed poles have their physical cosh formula.
The actual cosine/sine pair has a literal real correlation, and the separated
modulation kernel is strictly positive. The full-energy consequence is proved
in `WeilWorkPBAPJointModulation`.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

private theorem kernel_support_bound (f : WeilTestFn) :
    ∃ a : ℝ, tsupport f.1 ⊆ Icc (-a) a := by
  obtain ⟨a, ha⟩ := WeilSpectral.exists_abs_bound_of_hasCompactSupport f.2.2
  exact ⟨a, tsupport_subset_of_vanish
    (fun u hu => by by_contra h; exact (not_le_of_gt hu) (ha u h))⟩

private theorem kernel_real_corr_neg (f : ℝ → ℂ) (y : ℝ) :
    (EF.weilTest f f (-y)).re = (EF.weilTest f f y).re := by
  rw [weilTest_self_neg, Complex.conj_re]

private theorem kernel_fourier_mass (f : WeilTestFn) :
    (∫ t : ℝ, ‖paperFT f.1 t‖^2) = 2*Real.pi*testMass f.1 := by
  obtain ⟨a, ha⟩ := kernel_support_bound f
  have h := integral_normSq_paperFT_mul_cos_eq f.2.1 ha 0
  calc
    _ = Real.pi*(testMass f.1+testMass f.1) := by
      simpa only [mul_zero, Real.cos_zero, mul_one, neg_zero,
        autocorr_zero_eq_testMass, Complex.add_re, Complex.ofReal_re] using h
    _ = _ := by ring

private theorem kernel_cosine_defect (f : WeilTestFn) (y : ℝ) :
    (∫ t : ℝ, ‖paperFT f.1 t‖^2 * (1-Real.cos (t*y))) =
      2*Real.pi*(testMass f.1-(EF.weilTest f.1 f.1 y).re) := by
  obtain ⟨a, ha⟩ := kernel_support_bound f
  have hF := integrable_normSq_paperFT f.2.1 ha
  have hc : Integrable (fun t : ℝ => ‖paperFT f.1 t‖^2 * Real.cos (t*y)) := by
    apply hF.mul_bdd (c := 1)
    · exact (by fun_prop : Continuous fun t : ℝ => Real.cos (t*y)).aestronglyMeasurable
    · filter_upwards with t
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t*y)
  simp_rw [mul_sub, mul_one]
  rw [integral_sub hF hc, kernel_fourier_mass,
    integral_normSq_paperFT_mul_cos_eq f.2.1 ha,
    Complex.add_re, kernel_real_corr_neg]
  ring

/-- Gamma's actual physical jump density is integrable, including the origin. -/
theorem integrable_testGamma_jump (f : WeilTestFn) :
    IntegrableOn (fun t : ℝ => archJump t *
      (testMass f.1-(EF.weilTest f.1 f.1 (t/2)).re)) (Ioi 0) := by
  obtain ⟨a, ha⟩ := kernel_support_bound f
  let c : ℝ := (Complex.digamma (1/4)).re - Real.log Real.pi
  let J : ℝ → ℝ := fun tau => ∫ t in Ioi (0:ℝ),
    archJump t * (1-Real.cos (tau/2*t))
  have hA (tau : ℝ) : archimedeanWeilSymbol (tau/(2*Real.pi)) = c+J tau :=
    archimedeanWeilSymbol_eq_jump tau
  have hF := integrable_normSq_paperFT f.2.1 ha
  have hFA := integrable_normSq_paperFT_mul_arch f.2.1 ha
  have hFJ : Integrable (fun tau : ℝ => ‖paperFT f.1 tau‖^2 * J tau) := by
    refine (hFA.sub (hF.const_mul c)).congr (Eventually.of_forall fun tau => ?_)
    simp only [Pi.sub_apply, hA]
    ring
  let H : ℝ → ℝ → ℝ := fun tau t =>
    ‖paperFT f.1 tau‖^2 * (archJump t * (1-Real.cos (tau/2*t)))
  have hHnn (tau : ℝ) (t : ℝ) (ht : t ∈ Ioi (0:ℝ)) : 0 ≤ H tau t :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (archJump_nonneg ht)
      (by linarith [Real.cos_le_one (tau/2*t)]))
  have hmeasF : Measurable (fun tau : ℝ => ‖paperFT f.1 tau‖^2) :=
    ((continuous_paperFT_real_of_integrable
      (f.2.1.continuous.integrable_of_hasCompactSupport f.2.2)).norm.pow 2).measurable
  have hmeasW : Measurable archJump := by unfold archJump; fun_prop
  have hHm : AEStronglyMeasurable (Function.uncurry H)
      (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine Measurable.aestronglyMeasurable ?_
    exact (hmeasF.comp measurable_fst).mul ((hmeasW.comp measurable_snd).mul
      (measurable_const.sub (Real.continuous_cos.measurable.comp
        ((measurable_fst.div_const 2).mul measurable_snd))))
  have hint : Integrable (Function.uncurry H)
      (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff hHm]
    refine ⟨Eventually.of_forall (fun tau => ?_), ?_⟩
    · dsimp only [Function.uncurry_apply_pair, H]
      exact (integrableOn_archJump_mul (tau/2)).const_mul _
    · refine hFJ.congr (Eventually.of_forall fun tau => ?_)
      dsimp only [J, H, Function.uncurry_apply_pair]
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      exact (Real.norm_of_nonneg (hHnn tau t ht)).symm
  have hi := hint.integral_prod_right.const_mul (1/(2*Real.pi))
  apply hi.congr
  filter_upwards with t
  have he : (∫ tau : ℝ, H tau t) =
      archJump t * (2*Real.pi*(testMass f.1-(EF.weilTest f.1 f.1 (t/2)).re)) := by
    rw [show H = fun (tau t : ℝ) => archJump t *
      (‖paperFT f.1 tau‖^2*(1-Real.cos (tau*(t/2)))) by
        funext tau t
        dsimp only [H]
        rw [show tau/2*t=tau*(t/2) by ring]
        ring,
      integral_const_mul, kernel_cosine_defect]
  change (1/(2*Real.pi))*(∫ tau : ℝ, H tau t) = _
  rw [he]
  field_simp

/-- Full normalized Gamma energy in literal physical autocorrelations. -/
theorem testGamma_eq_jump (f : WeilTestFn) :
    testGamma f.1 = ((Complex.digamma (1/4)).re - Real.log Real.pi)*testMass f.1 +
      ∫ t in Ioi (0:ℝ), archJump t *
        (testMass f.1-(EF.weilTest f.1 f.1 (t/2)).re) := by
  obtain ⟨a, ha⟩ := kernel_support_bound f
  unfold testGamma
  simp_rw [← archimedeanWeilSymbol_paper]
  rw [integral_normSq_mul_arch_eq_jump f.2.1 ha, kernel_fourier_mass, mul_add]
  have hinner (t : ℝ) :
      (∫ tau : ℝ, ‖paperFT f.1 tau‖^2 * (1-Real.cos (tau/2*t))) =
        2*Real.pi*(testMass f.1-(EF.weilTest f.1 f.1 (t/2)).re) := by
    simpa only [div_mul_eq_mul_div, mul_div_assoc] using kernel_cosine_defect f (t/2)
  simp_rw [hinner]
  rw [← integral_const_mul]
  have he : (∫ t in Ioi (0:ℝ), (1/(2*Real.pi)) *
      (archJump t*(2*Real.pi*(testMass f.1-(EF.weilTest f.1 f.1 (t/2)).re)))) =
      ∫ t in Ioi (0:ℝ), archJump t*(testMass f.1-(EF.weilTest f.1 f.1 (t/2)).re) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    field_simp
  rw [he]
  congr 1
  field_simp

private theorem archJump_strictAnti_pos {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    archJump y < archJump x := by
  have hy : 0 < y := hx.trans hxy
  have hdx : 0 < 1-Real.exp (-x) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hdy : 0 < 1-Real.exp (-y) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hn : Real.exp (-(y/4)) < Real.exp (-(x/4)) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hd : 1-Real.exp (-x) < 1-Real.exp (-y) := by
    have := Real.exp_lt_exp.mpr (show -y < -x by linarith)
    linarith
  unfold archJump
  rw [div_lt_div_iff₀ hdy hdx]
  have h1 := mul_pos (sub_pos.mpr hn) hdx
  have h2 := mul_pos (Real.exp_pos (-(x/4))) (sub_pos.mpr hd)
  nlinarith

/-- The literal weight remaining after separating both clusters and both poles. -/
def jointModulationKernel (L y : ℝ) : ℝ :=
  4*archJump (2*y)-2*(archJump (2*(L+y))+archJump (2*(L-y)))+
    8*(Real.cosh (L/2)-1)*Real.cosh (y/2)

theorem jointModulationKernel_pos {L y : ℝ} (hy : 0 < y) (hL : 2*y < L) :
    0 < jointModulationKernel L y := by
  have hp := archJump_strictAnti_pos (show 0 < 2*y by linarith)
    (show 2*y < 2*(L+y) by linarith)
  have hm := archJump_strictAnti_pos (show 0 < 2*y by linarith)
    (show 2*y < 2*(L-y) by linarith)
  have hc : 0 ≤ 8*(Real.cosh (L/2)-1)*Real.cosh (y/2) :=
    mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.one_le_cosh _)))
      (Real.cosh_pos _).le
  unfold jointModulationKernel
  linarith

/-- Both signed poles as one literal physical integral. -/
theorem testPole_eq_integral_cosh (f : WeilTestFn) :
    testPole f.1 = ∫ u : ℝ, 2*Real.cosh (u/2)*(EF.weilTest f.1 f.1 u).re := by
  let k := EF.weilTest f.1 f.1
  have hk := WeilSpectral.admissible_weilTest f.2.1 f.2.2
  let w : ℝ → ℂ := fun u => ((Real.exp (u/2)+Real.exp (-(u/2)) : ℝ) : ℂ)
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hint (z : ℂ) : Integrable (fun u : ℝ => k u * cexp (I*z*u)) :=
    (hk.cont.mul (by fun_prop)).integrable_of_hasCompactSupport hk.supp.mul_right
  have hgi : Integrable (fun u : ℝ => k u*w u) :=
    (hk.cont.mul hw).integrable_of_hasCompactSupport hk.supp.mul_right
  have hexp (u : ℝ) : w u = cexp (I*(I/2)*u)+cexp (I*(-I/2)*u) := by
    dsimp only [w]
    push_cast
    rw [add_comm]
    congr 1
    · congr 1; ring_nf; rw [I_sq]; ring
    · congr 1; ring_nf; rw [I_sq]; ring
  have hsum : paperFT k (I/2)+paperFT k (-I/2) = ∫ u : ℝ, k u*w u := by
    unfold paperFT
    rw [← integral_add (hint _) (hint _)]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by dsimp only; rw [hexp]; ring
  change (paperFT k (I/2)+paperFT k (-I/2)).re = _
  rw [hsum]
  calc
    _ = ∫ u : ℝ, (k u*w u).re := (Complex.reCLM.integral_comp_comm hgi).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun u => by
        dsimp only
        simp only [w, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero, Real.cosh_eq]
        dsimp only [k]
        ring

theorem testGamma_eq_jump_scaled (f : WeilTestFn) :
    testGamma f.1 = ((Complex.digamma (1/4)).re-Real.log Real.pi)*testMass f.1 +
      2*∫ y in Ioi (0:ℝ), archJump (2*y)*
        (testMass f.1-(EF.weilTest f.1 f.1 y).re) := by
  rw [testGamma_eq_jump]
  have h := integral_comp_mul_left_Ioi
    (fun t : ℝ => archJump t*(testMass f.1-(EF.weilTest f.1 f.1 (t/2)).re))
    0 (show (0:ℝ) < 2 by norm_num)
  have hscale (x : ℝ) : 2*x/2=x := by ring
  norm_num only [hscale, mul_zero, smul_eq_mul] at h
  linarith

theorem integrable_testGamma_jump_scaled (f : WeilTestFn) :
    IntegrableOn (fun y : ℝ => archJump (2*y)*
      (testMass f.1-(EF.weilTest f.1 f.1 y).re)) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun t : ℝ => archJump t*(testMass f.1-(EF.weilTest f.1 f.1 (t/2)).re))
    0 (show (0:ℝ) < 2 by norm_num)).mpr
      (by simpa only [mul_zero] using integrable_testGamma_jump f)
  have hscale (x : ℝ) : 2*x/2=x := by ring
  simpa only [hscale] using h

private theorem modulation_pair_testMass (f : JointSmoothTest) (T : ℝ) :
    testMass (cosineProfile f.1.1 T)+testMass (sineProfile f.1.1 T)=testMass f.1.1 := by
  have h := weilTest_cosine_sine_add f.2.continuous f.1.2.2 T 0
  simp only [mul_zero, Real.cos_zero, Complex.ofReal_one, one_mul,
    autocorr_zero_eq_testMass] at h
  exact_mod_cast h

private theorem modulation_pair_real_corr (f : JointSmoothTest) (T y : ℝ) :
    (EF.weilTest (cosineProfile f.1.1 T) (cosineProfile f.1.1 T) y).re+
      (EF.weilTest (sineProfile f.1.1 T) (sineProfile f.1.1 T) y).re=
        Real.cos (T*y)*(EF.weilTest f.1.1 f.1.1 y).re := by
  have h := congrArg Complex.re (weilTest_cosine_sine_add f.2.continuous f.1.2.2 T y)
  simpa only [Complex.add_re, Complex.re_ofReal_mul] using h

/-- The variable-frequency increment is integrable despite the Gamma singularity. -/
theorem integrable_modulation_jump (f : JointSmoothTest) (T : ℝ) :
    IntegrableOn (fun y : ℝ => archJump (2*y)*(EF.weilTest f.1.1 f.1.1 y).re*
      (1-Real.cos (T*y))) (Ioi 0) := by
  let fc := cosineProfileTest f T
  let fs := sineProfileTest f T
  have h := ((integrable_testGamma_jump_scaled fc.1).add
    (integrable_testGamma_jump_scaled fs.1)).sub (integrable_testGamma_jump_scaled f.1)
  apply h.congr
  filter_upwards with y
  change archJump (2*y)*(testMass (cosineProfile f.1.1 T)-
      (EF.weilTest (cosineProfile f.1.1 T) (cosineProfile f.1.1 T) y).re)+
    archJump (2*y)*(testMass (sineProfile f.1.1 T)-
      (EF.weilTest (sineProfile f.1.1 T) (sineProfile f.1.1 T) y).re)-
    archJump (2*y)*(testMass f.1.1-(EF.weilTest f.1.1 f.1.1 y).re)=_
  have hm := modulation_pair_testMass f T
  have hc := modulation_pair_real_corr f T y
  linear_combination archJump (2*y)*hm-archJump (2*y)*hc

def jointPairRealCorr (f : JointSmoothTest) (L T y : ℝ) : ℝ :=
  2*(EF.weilTest f.1.1 f.1.1 y).re*Real.cos (T*y)-
    (EF.weilTest f.1.1 f.1.1 (y-L)).re*Real.cos (T*(y-L))-
    (EF.weilTest f.1.1 f.1.1 (y+L)).re*Real.cos (T*(y+L))

theorem jointPairRealCorr_eq (f : JointSmoothTest) (L T y : ℝ) :
    jointPairRealCorr f L T y =
      (EF.weilTest (clusterDifference (cosineProfile f.1.1 T) L)
        (clusterDifference (cosineProfile f.1.1 T) L) y).re+
      (EF.weilTest (clusterDifference (sineProfile f.1.1 T) L)
        (clusterDifference (sineProfile f.1.1 T) L) y).re := by
  have hc := congrArg Complex.re (weilTest_clusterDifference
    (contDiff_cosineProfile f.2 T).continuous
    (hasCompactSupport_cosineProfile f.1.2.2 T) L y)
  have hs := congrArg Complex.re (weilTest_clusterDifference
    (contDiff_sineProfile f.2 T).continuous
    (hasCompactSupport_sineProfile f.1.2.2 T) L y)
  norm_num [Complex.mul_re] at hc hs
  have h0 := modulation_pair_real_corr f T y
  have hm := modulation_pair_real_corr f T (y-L)
  have hp := modulation_pair_real_corr f T (y+L)
  unfold jointPairRealCorr
  linear_combination -hc-hs-2*h0+hm+hp

end RHTower.WeilWorkPBAP

import GaloisForLFunctions.RHTower.ChiCubicNormalizedPhysical
import GaloisForLFunctions.RHTower.ChiCubicKernelFrequencyDecay
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Rapid exterior decay of the actual physical cubic jets

The literal normalized physical kernel has phase
`2*pi*N*(P-R*y)*(Q-R*x)/R` on the fixed amplitude cube. Outside the
positive stationary box, one complete row gradient controls both physical
coordinates. Actual polynomial-window derivative budgets and repeated
integration by parts give all-order decay. Compact domination admits every
pure jet and both Fubini orders before using cancellation.

For the selected shrinking cutoff `delta=N^(-3/4)`, every fixed pure
coordinate derivative and polynomial spatial weight has arbitrary power
saving in `N`. No analytic budget, cancellation estimate or RH premise is
assumed. The logarithmic fractional transfer remains a separate obligation.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology ContDiff
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

private theorem parameter_derivative_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) {f : E→ℝ→ℂ} {z : E×ℝ}
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) z) :
    ContDiffAt ℝ ∞ (fun w : E×ℝ => iteratedDeriv k (f w.1) w.2) z := by
  induction k with
  | zero =>
    change ContDiffAt ℝ ∞ (fun w : E×ℝ => f w.1 w.2) z at hf
    simpa only [iteratedDeriv_zero] using hf
  | succ k ih =>
    have hcomp : ContDiffAt ℝ ∞
        (fun w : (E×ℝ)×ℝ => iteratedDeriv k (f w.1.1) w.2) (z,z.2) :=
      ih.comp (z,z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞
        (fun w : E×ℝ => fderiv ℝ (iteratedDeriv k (f w.1)) w.2) z :=
      hcomp.fderiv contDiffAt_snd (by simp)
    simpa only [iteratedDeriv_succ,deriv] using hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))

private def jetParameterBox : Set (ℝ×(ℝ×ℝ)) :=
  Icc (-1 : ℝ) 1 ×ˢ (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2)
private def windowJetCore (j : ℕ) (θ : ℝ×(ℝ×ℝ)) (p : ℝ) : ℂ :=
  ((θ.1*p+θ.2.1 : ℝ) : ℂ)^j*(bagPhysicalHeightWindow (θ.2.2*p) : ℂ)

private theorem window_jet_core_smooth (j : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (windowJetCore j)) := by
  have hW : ContDiff ℝ ∞ (bagPhysicalHeightWindow : ℝ→ℝ) := bagPhysicalHeightWindow.contDiff
  have hlin : ContDiff ℝ ∞ (fun z : (ℝ×(ℝ×ℝ))×ℝ => z.1.1*z.2+z.1.2.1) := by fun_prop
  have harg : ContDiff ℝ ∞ (fun z : (ℝ×(ℝ×ℝ))×ℝ => z.1.2.2*z.2) := by fun_prop
  exact ((Complex.ofRealCLM.contDiff.comp hlin).pow j).mul
    (Complex.ofRealCLM.contDiff.comp (hW.comp harg))

private theorem window_jet_core_bounds (j n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀θ∈jetParameterBox, ∀p∈Icc (1 : ℝ) 2,
      ‖iteratedDeriv n (windowJetCore j θ) p‖ ≤ C := by
  have hc : Continuous (fun z : (ℝ×(ℝ×ℝ))×ℝ => iteratedDeriv n (windowJetCore j z.1) z.2) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (parameter_derivative_smooth n (window_jet_core_smooth j).contDiffAt).continuousAt)
  have hK : IsCompact (jetParameterBox ×ˢ Icc (1 : ℝ) 2) :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod isCompact_Icc
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0+1,by positivity,fun θ hθ p hp => ?_⟩
  exact (hC (θ,p) ⟨hθ,hp⟩).trans (by linarith [le_max_left C 0])

private theorem derivative_off_box {f : ℝ→ℂ}
    (hf : ∀x : ℝ, x∉Icc (1 : ℝ) 2 → f x=0) (n : ℕ)
    {x : ℝ} (hx : x∉Icc (1 : ℝ) 2) : iteratedDeriv n f x=0 := by
  have hs : tsupport f⊆Icc (1 : ℝ) 2 :=
    closure_minimal (Function.support_subset_iff'.mpr hf) isClosed_Icc
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have hn : x∉Function.support (iteratedFDeriv ℝ n f) :=
    fun h => hx (hs (support_iteratedFDeriv_subset n h))
  simp [Function.notMem_support.mp hn]

private theorem window_jet_slice_budgets (j n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1}, ∀θ : {t : ℝ×(ℝ×ℝ) // t∈jetParameterBox},
      Integrable (iteratedDeriv n (fun p => bagCubicNormalizedSlice δ.1 h.1 p*windowJetCore j θ.1 p)) ∧
      (∫p : ℝ, ‖iteratedDeriv n (fun p => bagCubicNormalizedSlice δ.1 h.1 p*windowJetCore j θ.1 p) p‖)
        ≤ C/δ.1^(n-1) := by
  choose A hA hAb using bagCubicNormalizedSlice_derivative_budgets
  choose B hB hBb using window_jet_core_bounds j
  let C := ∑i∈Finset.range (n+1), (n.choose i : ℝ)*A i*B (n-i)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i).le) (hB (n-i)).le)
  refine ⟨C+1,by positivity,fun δ h θ => ?_⟩
  let F := bagCubicNormalizedSlice δ.1 h.1
  let G := windowJetCore j θ.1
  have hF := (bagCubicNormalizedSlice_properties δ h).1
  have hG : ContDiff ℝ ∞ G :=
    (window_jet_core_smooth j).comp (contDiff_const.prodMk contDiff_id)
  have hz (p : ℝ) (hp : p∉Icc (1 : ℝ) 2) : F p*G p=0 := by
    change bagCubicNormalizedSlice δ.1 h.1 p*_=0
    rw [(bagCubicNormalizedSlice_properties δ h).2 p hp,zero_mul]
  have hs : HasCompactSupport (fun p => F p*G p) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (Function.support_subset_iff'.mpr hz)
  have hi : Integrable (iteratedDeriv n (fun p => F p*G p)) :=
    GaloisForLFunctions.HTGeometry.integrable_iteratedDeriv_of_hasCompactSupport
      ((hF.mul hG).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))) hs le_rfl
  refine ⟨hi,?_⟩
  let M : ℝ→ℝ := fun p => ∑i∈Finset.range (n+1), (n.choose i : ℝ)*‖iteratedDeriv i F p‖*B (n-i)
  have hMi (i : ℕ) : Integrable (fun p : ℝ => (n.choose i : ℝ)*‖iteratedDeriv i F p‖*B (n-i)) :=
    ((hAb i δ h).1.const_mul _).mul_const _
  have hM : Integrable M := integrable_finsetSum _ (fun i _ => hMi i)
  have hpw (p : ℝ) : ‖iteratedDeriv n (fun p => F p*G p) p‖ ≤ M p := by
    by_cases hp : p∈Icc (1 : ℝ) 2
    · change ‖iteratedDeriv n (F*G) p‖ ≤ _
      rw [iteratedDeriv_mul (hF.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt
        (hG.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).contDiffAt]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => ?_))
      simp only [norm_mul,Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (hBb (n-i) θ.1 θ.2 p hp) (by positivity)
    · rw [derivative_off_box hz n hp,norm_zero]
      exact Finset.sum_nonneg (fun i _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (hB (n-i)).le)
  calc (∫p : ℝ, ‖iteratedDeriv n (fun p => F p*G p) p‖)
      ≤ ∫p : ℝ, M p := integral_mono hi.norm hM hpw
    _ = ∑i∈Finset.range (n+1), (n.choose i : ℝ)*(∫p : ℝ, ‖iteratedDeriv i F p‖)*B (n-i) := by
      rw [integral_finsetSum _ (fun i _ => hMi i)]
      simp only [integral_mul_const,integral_const_mul]
    _ ≤ ∑i∈Finset.range (n+1), (n.choose i : ℝ)*(A i/δ.1^(n-1))*B (n-i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hpow : δ.1^(n-1) ≤ δ.1^(i-1) := pow_le_pow_of_le_one δ.2.1.le
        (by linarith only [δ.2.2]) (Nat.sub_le_sub_right hin 1)
      have hb : (∫p : ℝ, ‖iteratedDeriv i F p‖) ≤ A i/δ.1^(n-1) :=
        (hAb i δ h).2.trans (div_le_div_of_nonneg_left (hA i).le (pow_pos δ.2.1 _) hpow)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)) (hB (n-i)).le
    _ = C/δ.1^(n-1) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (C+1)/δ.1^(n-1) := div_le_div_of_nonneg_right (by linarith) (pow_pos δ.2.1 _).le

private theorem normalized_slice_norm_le_one
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1}) (x : ℝ) :
    ‖bagCubicNormalizedSlice δ.1 h.1 x‖ ≤ 1 := by
  by_cases hx : x∈Icc (1 : ℝ) 2
  · have hd : 1 ≤ 1+h.1*Real.log x := by nlinarith [mul_nonneg h.2.1 (Real.log_nonneg hx.1)]
    have hc := (bagCubicControlledCutoff_properties δ).2.2.1 x
    change ‖(bagCubicControlledCutoff δ.1 x : ℂ)*
      (smoothAFECutoff x/((1+h.1*Real.log x : ℝ) : ℂ))‖ ≤ 1
    simp only [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans hd),abs_of_nonneg hc.1]
    have hv : ‖smoothAFECutoff x‖/(1+h.1*Real.log x) ≤ 1 :=
      (div_le_one (by linarith)).mpr ((norm_smoothAFECutoff_le_one (zero_lt_one.trans_le hx.1)).trans hd)
    exact (mul_le_mul hc.2 hv (by positivity) zero_le_one).trans_eq (by ring)
  · rw [(bagCubicNormalizedSlice_properties δ h).2 x hx,norm_zero]
    norm_num

private def physicalCube : Set (ℝ×(ℝ×ℝ)) :=
  Icc (1 : ℝ) 2 ×ˢ (Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2)
private def cubeMajorant : ℝ×(ℝ×ℝ)→ℝ := physicalCube.indicator (fun _ => 1)
private theorem cube_measurable : MeasurableSet physicalCube :=
  measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)
private theorem cube_majorant_integrable : Integrable cubeMajorant := by
  have hi : IntegrableOn (fun _ : ℝ×(ℝ×ℝ) => (1 : ℝ)) physicalCube :=
    integrableOn_const (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).measure_lt_top.ne
  exact hi.integrable_indicator cube_measurable
private theorem cube_majorant_nonneg (z : ℝ×(ℝ×ℝ)) : 0 ≤ cubeMajorant z :=
  indicator_nonneg (fun _ _ => zero_le_one) z

private def spatialStage (δ h N x y : ℝ) (z : ℝ×(ℝ×ℝ)) : ℂ :=
  bagCubicNormalizedSlice δ h z.2.2*bagCubicNormalizedSlice δ h z.2.1*
    star (bagCubicNormalizedSlice δ h z.1)/(z.1 : ℂ)*
    (bagPhysicalHeightWindow (z.2.2*z.2.1/z.1) : ℂ)*
    bourgainOscillation (2*Real.pi*N*((z.2.2-z.1*y)*(z.2.1-z.1*x)/z.1))
private def spatialJetFactor (N y : ℝ) (z : ℝ×(ℝ×ℝ)) : ℂ :=
  Complex.I*((2*Real.pi*N*(-z.2.2+y*z.1) : ℝ) : ℂ)
private def spatialJetStage (j : ℕ) (δ h N x y : ℝ) (z : ℝ×(ℝ×ℝ)) : ℂ :=
  (spatialJetFactor N y z)^j*spatialStage δ h N x y z
private def physicalJet (j : ℕ) (δ h N x y : ℝ) : ℂ :=
  (2*Real.pi*N : ℂ)*∫z : ℝ×(ℝ×ℝ), spatialJetStage j δ h N x y z

private theorem spatial_stage_measurable
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1}) (N x y : ℝ) (j : ℕ) :
    Measurable (spatialJetStage j δ.1 h.1 N x y) := by
  have hF := (bagCubicNormalizedSlice_properties δ h).1.continuous.measurable
  have hW : Measurable (bagPhysicalHeightWindow : ℝ→ℝ) :=
    (show ContDiff ℝ ∞ (bagPhysicalHeightWindow : ℝ→ℝ) from bagPhysicalHeightWindow.contDiff).continuous.measurable
  unfold spatialJetStage spatialJetFactor spatialStage bourgainOscillation
  fun_prop

private theorem spatial_stage_norm_bound
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1}) (N x y : ℝ) (z : ℝ×(ℝ×ℝ)) :
    ‖spatialStage δ.1 h.1 N x y z‖ ≤ cubeMajorant z := by
  let F := bagCubicNormalizedSlice δ.1 h.1
  have hb := normalized_slice_norm_le_one δ h
  have hz := (bagCubicNormalizedSlice_properties δ h).2
  by_cases hmem : z∈physicalCube
  · have hr : 1 ≤ z.1 := hmem.1.1
    have hd : 1 ≤ |z.1| := hr.trans (le_abs_self _)
    have hp : ‖F z.2.2‖*‖F z.2.1‖*‖F z.1‖ ≤ 1 := by
      calc ‖F z.2.2‖*‖F z.2.1‖*‖F z.1‖ ≤ 1*1*1 := by gcongr <;> apply hb
        _ = 1 := by norm_num
    have hq : (‖F z.2.2‖*‖F z.2.1‖*‖F z.1‖)/|z.1| ≤ 1 :=
      (div_le_one (by linarith)).mpr (hp.trans hd)
    simp only [spatialStage,norm_mul,norm_div,norm_star,Complex.norm_real,Real.norm_eq_abs,
      norm_bourgainOscillation,mul_one,cubeMajorant,indicator_of_mem hmem,
      abs_of_nonneg bagPhysicalHeightWindow.nonneg]
    exact (mul_le_mul hq bagPhysicalHeightWindow.le_one bagPhysicalHeightWindow.nonneg zero_le_one).trans_eq (by ring)
  · rw [cubeMajorant,indicator_of_notMem hmem]
    have he : spatialStage δ.1 h.1 N x y z=0 := by
      by_cases hr : z.1∈Icc (1 : ℝ) 2
      · by_cases hq : z.2.1∈Icc (1 : ℝ) 2
        · have hp : z.2.2∉Icc (1 : ℝ) 2 := fun hp => hmem ⟨hr,hq,hp⟩
          simp only [spatialStage,hz _ hp,zero_mul,zero_div]
        · simp only [spatialStage,hz _ hq,mul_zero,zero_mul,zero_div]
      · simp only [spatialStage,hz _ hr,star_zero,mul_zero,zero_div,zero_mul]
    rw [he,norm_zero]

private theorem jet_factor_bound (N : {r : ℝ // 0<r}) (y : ℝ) (z : ℝ×(ℝ×ℝ))
    (hz : z∈physicalCube) : ‖spatialJetFactor N.1 y z‖ ≤ 4*Real.pi*N.1*(1+|y|) := by
  have hN := N.2
  have hp0 : 0 ≤ z.2.2 := zero_le_one.trans hz.2.2.1
  have hr0 : 0 ≤ z.1 := zero_le_one.trans hz.1.1
  have hb : |-z.2.2+y*z.1| ≤ 2+2*|y| := by
    calc |-z.2.2+y*z.1| ≤ |-z.2.2|+|y*z.1| := abs_add_le _ _
      _ = z.2.2+|y| * z.1 := by rw [abs_neg,abs_mul,abs_of_nonneg hp0,abs_of_nonneg hr0]
      _ ≤ 2+2*|y| := by nlinarith [hz.2.2.2,hz.1.2,abs_nonneg y]
  simp only [spatialJetFactor,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  calc |2| * |Real.pi| * |N.1| * |-z.2.2+y*z.1|
      = (2*Real.pi*N.1)*|-z.2.2+y*z.1| := by rw [abs_of_pos (by norm_num : (0 : ℝ)<2),abs_of_pos Real.pi_pos,abs_of_pos N.2]
    _ ≤ (2*Real.pi*N.1)*(2+2*|y|) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

private theorem spatial_jet_stage_norm_bound
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (N : {r : ℝ // 0<r}) (x y : ℝ) (j : ℕ) (z : ℝ×(ℝ×ℝ)) :
    ‖spatialJetStage j δ.1 h.1 N.1 x y z‖ ≤ (4*Real.pi*N.1*(1+|y|))^j*cubeMajorant z := by
  have hN := N.2
  by_cases hz : z∈physicalCube
  · rw [spatialJetStage,norm_mul,norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (jet_factor_bound N y z hz) j)
      (spatial_stage_norm_bound δ h N.1 x y z) (norm_nonneg _) (by positivity)
  · have hh := spatial_stage_norm_bound δ h N.1 x y z
    rw [cubeMajorant,indicator_of_notMem hz] at hh ⊢
    have hzero : spatialStage δ.1 h.1 N.1 x y z=0 := norm_le_zero_iff.mp hh
    simp only [spatialJetStage,hzero,mul_zero,norm_zero,le_refl]

private theorem spatial_jet_stage_integrable
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (N : {r : ℝ // 0<r}) (x y : ℝ) (j : ℕ) :
    Integrable (spatialJetStage j δ.1 h.1 N.1 x y) :=
  (cube_majorant_integrable.const_mul _).mono' (spatial_stage_measurable δ h N.1 x y j).aestronglyMeasurable
    (Eventually.of_forall (spatial_jet_stage_norm_bound δ h N x y j))

private theorem spatial_jet_stage_hasDerivAt (δ h N x y : ℝ) (j : ℕ) (z : ℝ×(ℝ×ℝ)) :
    HasDerivAt (fun x : ℝ => spatialJetStage j δ h N x y z)
      (spatialJetStage (j+1) δ h N x y z) x := by
  by_cases hr : z.1=0
  · have he (t : ℝ) : spatialJetStage j δ h N t y z=0 := by
      simp only [spatialJetStage,spatialStage,hr,Complex.ofReal_zero,div_zero,zero_mul,mul_zero]
    have he' : spatialJetStage (j+1) δ h N x y z=0 := by
      simp only [spatialJetStage,spatialStage,hr,Complex.ofReal_zero,div_zero,zero_mul,mul_zero]
    simp_rw [he,he']
    exact hasDerivAt_const _ _
  have hd : HasDerivAt (fun t : ℝ => 2*Real.pi*N*((z.2.2-z.1*y)*(z.2.1-z.1*t)/z.1))
      (2*Real.pi*N*(-z.2.2+y*z.1)) x := by
    convert! (((((hasDerivAt_id x).const_mul z.1).const_sub z.2.1).const_mul (z.2.2-z.1*y)).div_const z.1).const_mul (2*Real.pi*N) using 1
    field_simp
    ring
  have he := ((hd.ofReal_comp.const_mul Complex.I).cexp).const_mul
    ((spatialJetFactor N y z)^j*(bagCubicNormalizedSlice δ h z.2.2*bagCubicNormalizedSlice δ h z.2.1*
      star (bagCubicNormalizedSlice δ h z.1)/(z.1 : ℂ)*(bagPhysicalHeightWindow (z.2.2*z.2.1/z.1) : ℂ)))
  convert! he using 1
  · funext t
    simp only [spatialJetStage,spatialStage,bourgainOscillation]
    ring
  · simp only [spatialJetStage,spatialStage,spatialJetFactor,bourgainOscillation,pow_succ]
    ring

private theorem physical_jet_hasDerivAt
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (N : {r : ℝ // 0<r}) (x y : ℝ) (j : ℕ) :
    HasDerivAt (fun t : ℝ => physicalJet j δ.1 h.1 N.1 t y)
      (physicalJet (j+1) δ.1 h.1 N.1 x y) x := by
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t z => spatialJetStage j δ.1 h.1 N.1 t y z)
    (F' := fun t z => spatialJetStage (j+1) δ.1 h.1 N.1 t y z)
    (bound := fun z => (4*Real.pi*N.1*(1+|y|))^(j+1)*cubeMajorant z)
    (s := Set.univ) (x₀ := x) (μ := volume) (by simp)
    (Eventually.of_forall (fun t => (spatial_stage_measurable δ h N.1 t y j).aestronglyMeasurable))
    (spatial_jet_stage_integrable δ h N x y j)
    (spatial_stage_measurable δ h N.1 x y (j+1)).aestronglyMeasurable
    (Eventually.of_forall (fun z t _ => spatial_jet_stage_norm_bound δ h N t y (j+1) z))
    (cube_majorant_integrable.const_mul _)
    (Eventually.of_forall (fun z t _ => spatial_jet_stage_hasDerivAt δ.1 h.1 N.1 t y j z))
  exact hd.2.const_mul (2*Real.pi*N.1 : ℂ)

private theorem physical_jet_zero_eq
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (N : {r : ℝ // 0<r}) (x y : ℝ) :
    physicalJet 0 δ.1 h.1 N.1 x y=bagCubicNormalizedPhysicalKernel δ.1 h.1 N.1 x y := by
  have hi : Integrable (spatialStage δ.1 h.1 N.1 x y) := by
    have hh := spatial_jet_stage_integrable δ h N x y 0
    change Integrable (fun z => spatialJetStage 0 δ.1 h.1 N.1 x y z) at hh
    simpa only [spatialJetStage,pow_zero,one_mul] using hh
  have he : (∫z : ℝ×(ℝ×ℝ), spatialStage δ.1 h.1 N.1 x y z)=
      ∫r : ℝ,∫q : ℝ,∫p : ℝ, spatialStage δ.1 h.1 N.1 x y (r,q,p) := by
    change (∫z : ℝ×(ℝ×ℝ), spatialStage δ.1 h.1 N.1 x y z ∂volume.prod volume)=_
    rw [integral_prod _ hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_right_ae] with r hr
    exact integral_prod _ hr
  simp only [physicalJet,spatialJetStage,pow_zero,one_mul]
  rw [he]
  rfl

private theorem physical_iterated_deriv
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (N : {r : ℝ // 0<r}) (y : ℝ) (j : ℕ) :
    iteratedDeriv j (fun x : ℝ => bagCubicNormalizedPhysicalKernel δ.1 h.1 N.1 x y)=
      (fun x : ℝ => physicalJet j δ.1 h.1 N.1 x y) := by
  induction j with
  | zero =>
    rw [iteratedDeriv_zero]
    exact funext (fun x => (physical_jet_zero_eq δ h N x y).symm)
  | succ j ih =>
    rw [iteratedDeriv_succ,ih]
    exact funext (fun x => (physical_jet_hasDerivAt δ h N x y j).deriv)

private theorem window_jet_oscillation (j n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1}, ∀θ : {t : ℝ×(ℝ×ℝ) // t∈jetParameterBox},
      ∀ξ : ℝ, ξ≠0 →
      ‖∫p : ℝ, bagCubicNormalizedSlice δ.1 h.1 p*windowJetCore j θ.1 p*bourgainOscillation (-ξ*p)‖
        ≤ C/δ.1^(n-1)/|ξ|^n := by
  obtain ⟨C,hC,hCb⟩ := window_jet_slice_budgets j n
  refine ⟨C,hC,fun δ h θ ξ hξ => ?_⟩
  let f := fun p => bagCubicNormalizedSlice δ.1 h.1 p*windowJetCore j θ.1 p
  have hG : ContDiff ℝ ∞ (windowJetCore j θ.1) :=
    (window_jet_core_smooth j).comp (contDiff_const.prodMk contDiff_id)
  have hf : ContDiff ℝ (n : ℕ) f :=
    ((bagCubicNormalizedSlice_properties δ h).1.mul hG).of_le
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hs : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (Function.support_subset_iff'.mpr (fun p hp => by
      dsimp only [f]
      rw [(bagCubicNormalizedSlice_properties δ h).2 p hp,zero_mul]))
  have hh := GaloisForLFunctions.HTGeometry.norm_integral_mul_cexp_le_of_iteratedDeriv n hf
    (fun i hi => GaloisForLFunctions.HTGeometry.integrable_iteratedDeriv_of_hasCompactSupport hf hs hi) hξ
  have he (p : ℝ) : Complex.exp (-((ξ : ℂ)*(p : ℂ))*Complex.I)=bourgainOscillation (-ξ*p) := by
    unfold bourgainOscillation
    congr 1
    push_cast
    ring
  simp_rw [he] at hh
  exact hh.trans (div_le_div_of_nonneg_right (hCb δ h θ).2 (pow_nonneg (abs_nonneg _) _))

private theorem linear_polynomial_oscillation (j n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1}, ∀M : {r : ℝ // 1 ≤ r},
      ∀α β k ξ : ℝ, |α| ≤ M.1 → |β| ≤ 2*M.1 → |k| ≤ 2 → ξ≠0 →
      ‖∫p : ℝ, bagCubicNormalizedSlice δ.1 h.1 p*((α*p+β : ℝ) : ℂ)^j*
        (bagPhysicalHeightWindow (k*p) : ℂ)*bourgainOscillation (-ξ*p)‖
        ≤ C*M.1^j/δ.1^(n-1)/|ξ|^n := by
  obtain ⟨C,hC,hCb⟩ := window_jet_oscillation j n
  refine ⟨C,hC,fun δ h M α β k ξ hα hβ hk hξ => ?_⟩
  have hM : 0<M.1 := zero_lt_one.trans_le M.2
  let θ : {t : ℝ×(ℝ×ℝ) // t∈jetParameterBox} := ⟨(α/M.1,β/M.1,k),by
    refine ⟨abs_le.mp ?_,abs_le.mp ?_,abs_le.mp hk⟩
    · rw [abs_div,abs_of_pos hM]
      exact (div_le_one hM).mpr hα
    · rw [abs_div,abs_of_pos hM]
      exact (div_le_iff₀ hM).mpr hβ⟩
  have hlin (p : ℝ) : ((α*p+β : ℝ) : ℂ)=(M.1 : ℂ)*((θ.1.1*p+θ.1.2.1 : ℝ) : ℂ) := by
    rw [←Complex.ofReal_mul]
    congr 1
    dsimp only [θ]
    field_simp
  have he : (∫p : ℝ, bagCubicNormalizedSlice δ.1 h.1 p*((α*p+β : ℝ) : ℂ)^j*
      (bagPhysicalHeightWindow (k*p) : ℂ)*bourgainOscillation (-ξ*p))=
      (M.1 : ℂ)^j*∫p : ℝ, bagCubicNormalizedSlice δ.1 h.1 p*windowJetCore j θ.1 p*bourgainOscillation (-ξ*p) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    rw [hlin,mul_pow]
    dsimp only [windowJetCore,θ]
    ring
  rw [he,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM]
  calc M.1^j*‖∫p : ℝ, bagCubicNormalizedSlice δ.1 h.1 p*windowJetCore j θ.1 p*bourgainOscillation (-ξ*p)‖
      ≤ M.1^j*(C/δ.1^(n-1)/|ξ|^n) :=
        mul_le_mul_of_nonneg_left (hCb δ h θ ξ hξ) (pow_nonneg hM.le _)
    _ = _ := by ring

private theorem phase_add (s t : ℝ) :
    bourgainOscillation (s+t)=bourgainOscillation s*bourgainOscillation t := by
  simp only [bourgainOscillation,Complex.ofReal_add,mul_add,Complex.exp_add]

private def polynomialRow (j : ℕ) (δ h α β k ξ : ℝ) : ℂ :=
  ∫p : ℝ, bagCubicNormalizedSlice δ h p*((α*p+β : ℝ) : ℂ)^j*
    (bagPhysicalHeightWindow (k*p) : ℂ)*bourgainOscillation (-ξ*p)

private theorem p_row_identity (j : ℕ) (δ h N x y q r : ℝ) :
    (∫p : ℝ, spatialJetStage j δ h N x y (r,q,p))=
      (Complex.I*((2*Real.pi*N : ℝ) : ℂ))^j*
      (bagCubicNormalizedSlice δ h q*star (bagCubicNormalizedSlice δ h r)/(r : ℂ))*
      bourgainOscillation (2*Real.pi*N*y*(r*x-q))*
      polynomialRow j δ h (-1) (y*r) (q/r) (2*Real.pi*N*(x-q/r)) := by
  by_cases hr : r=0
  · simp only [hr,spatialJetStage,spatialStage,Complex.ofReal_zero,div_zero,
      zero_mul,mul_zero,integral_zero]
  rw [polynomialRow,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  have hphase : bourgainOscillation (2*Real.pi*N*((p-r*y)*(q-r*x)/r))=
      bourgainOscillation (2*Real.pi*N*y*(r*x-q))*
      bourgainOscillation (-(2*Real.pi*N*(x-q/r))*p) := by
    rw [←phase_add]
    congr 1
    field_simp
    ring
  have hw : p*q/r=(q/r)*p := by ring
  have hfac : Complex.I*((2*Real.pi*N*(-p+y*r) : ℝ) : ℂ)=
      (Complex.I*((2*Real.pi*N : ℝ) : ℂ))*((-p+y*r : ℝ) : ℂ) := by
    push_cast
    ring
  simp only [spatialJetStage,spatialStage,spatialJetFactor,hphase,hw,hfac,mul_pow]
  push_cast
  ring

private theorem q_row_identity (j : ℕ) (δ h N x y p r : ℝ) :
    (∫q : ℝ, spatialJetStage j δ h N x y (r,q,p))=
      (Complex.I*((2*Real.pi*N : ℝ) : ℂ))^j*
      (bagCubicNormalizedSlice δ h p*star (bagCubicNormalizedSlice δ h r)/(r : ℂ))*
      bourgainOscillation (2*Real.pi*N*x*(r*y-p))*
      polynomialRow j δ h 0 (-p+y*r) (p/r) (2*Real.pi*N*(y-p/r)) := by
  by_cases hr : r=0
  · simp only [hr,spatialJetStage,spatialStage,Complex.ofReal_zero,div_zero,
      zero_mul,mul_zero,integral_zero]
  rw [polynomialRow,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  have hphase : bourgainOscillation (2*Real.pi*N*((p-r*y)*(q-r*x)/r))=
      bourgainOscillation (2*Real.pi*N*x*(r*y-p))*
      bourgainOscillation (-(2*Real.pi*N*(y-p/r))*q) := by
    rw [←phase_add]
    congr 1
    field_simp
    ring
  have hw : p*q/r=(p/r)*q := by ring
  have hfac : Complex.I*((2*Real.pi*N*(-p+y*r) : ℝ) : ℂ)=
      (Complex.I*((2*Real.pi*N : ℝ) : ℂ))*((-p+y*r : ℝ) : ℂ) := by
    push_cast
    ring
  simp only [spatialJetStage,spatialStage,spatialJetFactor,hphase,hw,hfac,mul_pow]
  push_cast
  ring

private theorem physical_jet_nested
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (N : {r : ℝ // 0<r}) (x y : ℝ) (j : ℕ) :
    physicalJet j δ.1 h.1 N.1 x y=
      (2*Real.pi*N.1 : ℂ)*∫r : ℝ,∫q : ℝ,∫p : ℝ,
        spatialJetStage j δ.1 h.1 N.1 x y (r,q,p) := by
  have hi := spatial_jet_stage_integrable δ h N x y j
  unfold physicalJet
  congr 1
  change (∫z : ℝ×(ℝ×ℝ), spatialJetStage j δ.1 h.1 N.1 x y z ∂volume.prod volume)=_
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with r hr
  exact integral_prod _ hr

private theorem physical_jet_swapped
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (N : {r : ℝ // 0<r}) (x y : ℝ) (j : ℕ) :
    physicalJet j δ.1 h.1 N.1 x y=
      (2*Real.pi*N.1 : ℂ)*∫r : ℝ,∫p : ℝ,∫q : ℝ,
        spatialJetStage j δ.1 h.1 N.1 x y (r,q,p) := by
  have hi := spatial_jet_stage_integrable δ h N x y j
  rw [physical_jet_nested δ h N x y j]
  congr 1
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with r hr
  exact integral_integral_swap hr

private theorem ratio_in_box (p r : {t : ℝ // t∈Icc (1 : ℝ) 2}) :
    p.1/r.1∈Icc (1/2 : ℝ) 2 := by
  have hr : 0<r.1 := zero_lt_one.trans_le r.2.1
  constructor
  · apply (le_div_iff₀ hr).mpr
    linarith [r.2.2,p.2.1]
  · apply (div_le_iff₀ hr).mpr
    linarith [r.2.1,p.2.2]

private theorem nonstationary_direction (x y : {t : ℝ // 0<t})
    (hout : ¬(x.1∈Icc (1/4 : ℝ) 4 ∧ y.1∈Icc (1/4 : ℝ) 4)) :
    (∀q r : {t : ℝ // t∈Icc (1 : ℝ) 2}, (1+x.1+y.1)/36 ≤ |x.1-q.1/r.1|) ∨
    (∀p r : {t : ℝ // t∈Icc (1 : ℝ) 2}, (1+x.1+y.1)/36 ≤ |y.1-p.1/r.1|) := by
  by_cases hx : 4 ≤ x.1
  · by_cases hxy : y.1 ≤ x.1
    · left
      intro q r
      have hb := ratio_in_box q r
      calc (1+x.1+y.1)/36 ≤ x.1-q.1/r.1 := by linarith [hb.1,hb.2]
        _ ≤ |x.1-q.1/r.1| := le_abs_self _
    · right
      intro p r
      have hb := ratio_in_box p r
      calc (1+x.1+y.1)/36 ≤ y.1-p.1/r.1 := by linarith [hb.1,hb.2]
        _ ≤ |y.1-p.1/r.1| := le_abs_self _
  · by_cases hy : 4 ≤ y.1
    · right
      intro p r
      have hb := ratio_in_box p r
      calc (1+x.1+y.1)/36 ≤ y.1-p.1/r.1 := by linarith [hb.1,hb.2]
        _ ≤ |y.1-p.1/r.1| := le_abs_self _
    · have hsmall : x.1<1/4 ∨ y.1<1/4 := by
        by_contra hn
        push Not at hn
        exact hout ⟨⟨hn.1,le_of_not_ge hx⟩,⟨hn.2,le_of_not_ge hy⟩⟩
      rcases hsmall with hsmall | hsmall
      · left
        intro q r
        have hb := ratio_in_box q r
        calc (1+x.1+y.1)/36 ≤ -(x.1-q.1/r.1) := by linarith [hb.1,hb.2]
          _ ≤ |x.1-q.1/r.1| := neg_le_abs _
      · right
        intro p r
        have hb := ratio_in_box p r
        calc (1+x.1+y.1)/36 ≤ -(y.1-p.1/r.1) := by linarith [hb.1,hb.2]
          _ ≤ |y.1-p.1/r.1| := neg_le_abs _

private theorem row_factor_bound (j : ℕ) (L : {t : ℝ // 0<t})
    (r : {t : ℝ // t∈Icc (1 : ℝ) 2}) (u v z : ℂ) (c S : ℝ)
    (hz : ‖z‖ ≤ S) :
    ‖(Complex.I*(L.1 : ℂ))^j*(u*star v/(r.1 : ℂ))*bourgainOscillation c*z‖
      ≤ ‖u‖*‖v‖*(L.1^j*S) := by
  have hr : 0<r.1 := zero_lt_one.trans_le r.2.1
  have hfrac : ‖u‖*‖v‖/r.1 ≤ ‖u‖*‖v‖ := by
    apply (div_le_iff₀ hr).mpr
    exact le_mul_of_one_le_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) r.2.1
  simp only [norm_mul,norm_pow,Complex.norm_I,one_mul,norm_div,norm_star,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos L.2,abs_of_pos hr,
    norm_bourgainOscillation,mul_one]
  calc
    L.1^j*(‖u‖*‖v‖/r.1)*‖z‖ ≤ L.1^j*(‖u‖*‖v‖)*S := by
      apply mul_le_mul _ hz (norm_nonneg _)
        (mul_nonneg (pow_nonneg L.2.le j) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      exact mul_le_mul_of_nonneg_left hfrac (pow_nonneg L.2.le j)
    _ = _ := by ring

private theorem nested_integral_bound {F : ℝ→ℂ} {A S : ℝ}
    (hF : Integrable (fun t : ℝ => ‖F t‖)) (hA : 0 ≤ A)
    (hmass : (∫t : ℝ, ‖F t‖) ≤ A) (hS : 0 ≤ S)
    (G : ℝ→ℝ→ℂ) (hG : ∀r q : ℝ, ‖G r q‖ ≤ ‖F q‖*‖F r‖*S) :
    ‖∫r : ℝ,∫q : ℝ, G r q‖ ≤ A^2*S := by
  have hinner (r : ℝ) : ‖∫q : ℝ, G r q‖ ≤ A*‖F r‖*S := by
    calc ‖∫q : ℝ, G r q‖ ≤ ∫q : ℝ, ‖F q‖*‖F r‖*S :=
        norm_integral_le_of_norm_le ((hF.mul_const _).mul_const _) (Eventually.of_forall (hG r))
      _ = (∫q : ℝ, ‖F q‖)*‖F r‖*S := by rw [integral_mul_const,integral_mul_const]
      _ ≤ A*‖F r‖*S := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmass (norm_nonneg _)) hS
  calc ‖∫r : ℝ,∫q : ℝ, G r q‖ ≤ ∫r : ℝ, A*‖F r‖*S :=
      norm_integral_le_of_norm_le ((hF.const_mul _).mul_const _) (Eventually.of_forall hinner)
    _ = A*(∫r : ℝ, ‖F r‖)*S := by rw [integral_mul_const,integral_const_mul]
    _ ≤ A*A*S := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hA) hS
    _ = _ := by ring

private theorem physical_jet_nonstationary_bound (j n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1}, ∀N d : {r : ℝ // 0<r}, ∀x y : ℝ,
      ((∀q r : {t : ℝ // t∈Icc (1 : ℝ) 2}, d.1 ≤ |x-q.1/r.1|) ∨
       (∀p r : {t : ℝ // t∈Icc (1 : ℝ) 2}, d.1 ≤ |y-p.1/r.1|)) →
      ‖physicalJet j δ.1 h.1 N.1 x y‖ ≤
        C*(2*Real.pi*N.1)^(j+1)*(1+|y|)^j/δ.1^(n-1)/(2*Real.pi*N.1*d.1)^n := by
  obtain ⟨B,hB,hBb⟩ := linear_polynomial_oscillation j n
  obtain ⟨A,hA,hAb⟩ := bagCubicNormalizedSlice_derivative_budgets 0
  refine ⟨A^2*B,by positivity,fun δ h N d x y hg => ?_⟩
  let F := bagCubicNormalizedSlice δ.1 h.1
  let L := 2*Real.pi*N.1
  have hL : 0<L := mul_pos (mul_pos (by norm_num) Real.pi_pos) N.2
  let M : {t : ℝ // 1 ≤ t} := ⟨1+|y|,by linarith [abs_nonneg y]⟩
  let S := B*M.1^j/δ.1^(n-1)/(L*d.1)^n
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact div_nonneg
      (div_nonneg (mul_nonneg hB.le (pow_nonneg (zero_le_one.trans M.2) _)) (pow_pos δ.2.1 _).le)
      (pow_pos (mul_pos hL d.2) _).le
  have hm : Integrable (fun t : ℝ => ‖F t‖) ∧ (∫t : ℝ, ‖F t‖) ≤ A := by
    simpa only [iteratedDeriv_zero,Nat.zero_sub,pow_zero,div_one] using hAb δ h
  have hrow (α β k t : ℝ) (hα : |α| ≤ M.1) (hβ : |β| ≤ 2*M.1)
      (hk : |k| ≤ 2) (ht : d.1 ≤ |t|) :
      ‖polynomialRow j δ.1 h.1 α β k (L*t)‖ ≤ S := by
    have ht0 : t≠0 := abs_pos.mp (d.2.trans_le ht)
    have hh := hBb δ h M α β k (L*t) hα hβ hk (mul_ne_zero hL.ne' ht0)
    change ‖polynomialRow j δ.1 h.1 α β k (L*t)‖ ≤ _ at hh
    rw [abs_mul,abs_of_pos hL] at hh
    exact hh.trans (div_le_div_of_nonneg_left
      (div_nonneg (mul_nonneg hB.le (pow_nonneg (zero_le_one.trans M.2) _)) (pow_pos δ.2.1 _).le)
      (pow_pos (mul_pos hL d.2) _)
      (pow_le_pow_left₀ (mul_pos hL d.2).le (mul_le_mul_of_nonneg_left ht hL.le) n))
  have hk (q r : {t : ℝ // t∈Icc (1 : ℝ) 2}) : |q.1/r.1| ≤ 2 := by
    have hb := ratio_in_box q r
    rw [abs_of_nonneg (by linarith [hb.1] : 0 ≤ q.1/r.1)]
    exact hb.2
  have hpy (p r : {t : ℝ // t∈Icc (1 : ℝ) 2}) : |-p.1+y*r.1| ≤ 2*M.1 := by
    calc |-p.1+y*r.1| ≤ |-p.1|+|y*r.1| := abs_add_le _ _
      _ = p.1+|y| * r.1 := by rw [abs_neg,abs_mul,
        abs_of_nonneg (zero_le_one.trans p.2.1),abs_of_nonneg (zero_le_one.trans r.2.1)]
      _ ≤ 2*M.1 := by dsimp only [M]; nlinarith [p.2.2,r.2.2,abs_nonneg y]
  have hbound : ‖physicalJet j δ.1 h.1 N.1 x y‖ ≤ L*(A^2*(L^j*S)) := by
    rcases hg with hg | hg
    · have hrows (r q : ℝ) :
          ‖∫p : ℝ, spatialJetStage j δ.1 h.1 N.1 x y (r,q,p)‖ ≤ ‖F q‖*‖F r‖*(L^j*S) := by
        rw [p_row_identity]
        by_cases hr : r∈Icc (1 : ℝ) 2
        · by_cases hq : q∈Icc (1 : ℝ) 2
          · have hβ : |y*r| ≤ 2*M.1 := by
              rw [abs_mul,abs_of_nonneg (zero_le_one.trans hr.1)]
              dsimp only [M]
              nlinarith [hr.2,abs_nonneg y]
            have hh := hrow (-1) (y*r) (q/r) (x-q/r)
              (by simpa only [abs_neg,abs_one] using M.2) hβ (hk ⟨q,hq⟩ ⟨r,hr⟩) (hg ⟨q,hq⟩ ⟨r,hr⟩)
            exact row_factor_bound j ⟨L,hL⟩ ⟨r,hr⟩ (F q) (F r) _ _ S hh
          · have hz : F q=0 := (bagCubicNormalizedSlice_properties δ h).2 q hq
            change ‖_* (F q*star (F r)/(r : ℂ))*_*_‖ ≤ _
            simp only [hz,zero_mul,zero_div,mul_zero,norm_zero,le_refl]
        · have hz : F r=0 := (bagCubicNormalizedSlice_properties δ h).2 r hr
          change ‖_* (F q*star (F r)/(r : ℂ))*_*_‖ ≤ _
          simp only [hz,star_zero,mul_zero,zero_div,zero_mul,norm_zero,le_refl]
      rw [physical_jet_nested δ h N x y j,norm_mul]
      have hnorm : ‖(2*Real.pi*N.1 : ℂ)‖=L := by
        have he : (2*Real.pi*N.1 : ℂ)=((2*Real.pi*N.1 : ℝ) : ℂ) := by push_cast; rfl
        rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left
        (nested_integral_bound hm.1 hA.le hm.2 (mul_nonneg (pow_nonneg hL.le _) hS) _ hrows) hL.le
    · have hrows (r p : ℝ) :
          ‖∫q : ℝ, spatialJetStage j δ.1 h.1 N.1 x y (r,q,p)‖ ≤ ‖F p‖*‖F r‖*(L^j*S) := by
        rw [q_row_identity]
        by_cases hr : r∈Icc (1 : ℝ) 2
        · by_cases hp : p∈Icc (1 : ℝ) 2
          · have hh := hrow 0 (-p+y*r) (p/r) (y-p/r)
              (by rw [abs_zero]; exact zero_le_one.trans M.2)
              (hpy ⟨p,hp⟩ ⟨r,hr⟩) (hk ⟨p,hp⟩ ⟨r,hr⟩) (hg ⟨p,hp⟩ ⟨r,hr⟩)
            exact row_factor_bound j ⟨L,hL⟩ ⟨r,hr⟩ (F p) (F r) _ _ S hh
          · have hz : F p=0 := (bagCubicNormalizedSlice_properties δ h).2 p hp
            change ‖_* (F p*star (F r)/(r : ℂ))*_*_‖ ≤ _
            simp only [hz,zero_mul,zero_div,mul_zero,norm_zero,le_refl]
        · have hz : F r=0 := (bagCubicNormalizedSlice_properties δ h).2 r hr
          change ‖_* (F p*star (F r)/(r : ℂ))*_*_‖ ≤ _
          simp only [hz,star_zero,mul_zero,zero_div,zero_mul,norm_zero,le_refl]
      rw [physical_jet_swapped δ h N x y j,norm_mul]
      have hnorm : ‖(2*Real.pi*N.1 : ℂ)‖=L := by
        have he : (2*Real.pi*N.1 : ℂ)=((2*Real.pi*N.1 : ℝ) : ℂ) := by push_cast; rfl
        rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left
        (nested_integral_bound hm.1 hA.le hm.2 (mul_nonneg (pow_nonneg hL.le _) hS) _ hrows) hL.le
  refine hbound.trans_eq ?_
  dsimp only [L,S,M]
  rw [pow_succ]
  ring

private theorem normalized_physical_symmetry
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (N : {r : ℝ // 0<r}) (x y : ℝ) :
    bagCubicNormalizedPhysicalKernel δ.1 h.1 N.1 x y=
      bagCubicNormalizedPhysicalKernel δ.1 h.1 N.1 y x := by
  rw [←physical_jet_zero_eq δ h N x y,←physical_jet_zero_eq δ h N y x,
    physical_jet_swapped δ h N x y 0,physical_jet_nested δ h N y x 0]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with r
  apply integral_congr_ae
  filter_upwards [] with p
  apply integral_congr_ae
  filter_upwards [] with q
  simp only [spatialJetStage,pow_zero,one_mul,spatialStage]
  rw [mul_comm q p,mul_comm (q-r*x) (p-r*y)]
  ring

private theorem physical_exterior_x_decay (j n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1}, ∀N x y : {r : ℝ // 0<r},
      ¬(x.1∈Icc (1/4 : ℝ) 4 ∧ y.1∈Icc (1/4 : ℝ) 4) →
      N.1^n*(1+x.1+y.1)^n*
        ‖iteratedDeriv j (fun t : ℝ => bagCubicNormalizedPhysicalKernel δ.1 h.1 N.1 t y.1) x.1‖ ≤
        C*N.1^(j+1)*(1+x.1+y.1)^j/δ.1^(n-1) := by
  obtain ⟨B,hB,hBb⟩ := physical_jet_nonstationary_bound j n
  let c := 2*Real.pi/36
  have hc : 0<c := by dsimp only [c]; positivity
  refine ⟨B*(2*Real.pi)^(j+1)/c^n,by positivity,fun δ h N x y hout => ?_⟩
  let w := 1+x.1+y.1
  have hw : 0<w := by dsimp only [w]; linarith [x.2,y.2]
  let d : {r : ℝ // 0<r} := ⟨w/36,div_pos hw (by norm_num)⟩
  have hL : 0<2*Real.pi*N.1 := mul_pos (mul_pos (by norm_num) Real.pi_pos) N.2
  have hh := hBb δ h N d x.1 y.1 (nonstationary_direction x y hout)
  have hh' := (le_div_iff₀ (pow_pos (mul_pos hL d.2) n)).mp hh
  have hden : (2*Real.pi*N.1*d.1)^n=c^n*N.1^n*w^n := by
    rw [←mul_pow,←mul_pow]
    congr 1
    dsimp only [c,d]
    ring
  rw [hden] at hh'
  have hs : (N.1^n*w^n*‖physicalJet j δ.1 h.1 N.1 x.1 y.1‖)*c^n ≤
      B*(2*Real.pi*N.1)^(j+1)*(1+|y.1|)^j/δ.1^(n-1) := by
    convert! hh' using 1
    ring
  have hb := (le_div_iff₀ (pow_pos hc n)).mpr hs
  have hm : (1+|y.1|)^j ≤ w^j := by
    apply pow_le_pow_left₀ (by positivity)
    rw [abs_of_pos y.2]
    dsimp only [w]
    linarith [x.2]
  rw [physical_iterated_deriv δ h N y.1 j]
  refine hb.trans ?_
  calc (B*(2*Real.pi*N.1)^(j+1)*(1+|y.1|)^j/δ.1^(n-1))/c^n
      ≤ (B*(2*Real.pi*N.1)^(j+1)*w^j/δ.1^(n-1))/c^n := by
        apply div_le_div_of_nonneg_right _ (pow_pos hc _).le
        apply div_le_div_of_nonneg_right _ (pow_pos δ.2.1 _).le
        exact mul_le_mul_of_nonneg_left hm (mul_nonneg hB.le (pow_pos hL _).le)
    _ = _ := by simp only [mul_pow]; ring

/-- All-order exterior decay for the literal physical kernel and both pure coordinate jets.
Only structural scale and spatial-domain restrictions occur in the statement. -/
theorem bagCubicNormalizedPhysicalKernel_exterior_decay (j n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1}, ∀N : {r : ℝ // 0<r},
      ∀z : {z : ℝ×ℝ // 0<z.1 ∧ 0<z.2 ∧
        ¬(z.1∈Icc (1/4 : ℝ) 4 ∧ z.2∈Icc (1/4 : ℝ) 4)},
      N.1^n*(1+z.1.1+z.1.2)^n*
        max ‖iteratedDeriv j (fun t : ℝ => bagCubicNormalizedPhysicalKernel δ.1 h.1 N.1 t z.1.2) z.1.1‖
          ‖iteratedDeriv j (fun t : ℝ => bagCubicNormalizedPhysicalKernel δ.1 h.1 N.1 z.1.1 t) z.1.2‖ ≤
        C*N.1^(j+1)*(1+z.1.1+z.1.2)^j/δ.1^(n-1) := by
  obtain ⟨C,hC,hCb⟩ := physical_exterior_x_decay j n
  refine ⟨C,hC,fun δ h N z => ?_⟩
  have hx := hCb δ h N ⟨z.1.1,z.2.1⟩ ⟨z.1.2,z.2.2.1⟩ z.2.2.2
  have hy := hCb δ h N ⟨z.1.2,z.2.2.1⟩ ⟨z.1.1,z.2.1⟩ (fun hh => z.2.2.2 ⟨hh.2,hh.1⟩)
  have hfun : (fun t : ℝ => bagCubicNormalizedPhysicalKernel δ.1 h.1 N.1 z.1.1 t)=
      (fun t : ℝ => bagCubicNormalizedPhysicalKernel δ.1 h.1 N.1 t z.1.1) :=
    funext (normalized_physical_symmetry δ h N z.1.1)
  have hw : 1+z.1.2+z.1.1=1+z.1.1+z.1.2 := by ring
  change N.1^n*(1+z.1.2+z.1.1)^n*_ ≤ C*N.1^(j+1)*(1+z.1.2+z.1.1)^j/δ.1^(n-1) at hy
  rw [hw] at hy
  rw [hfun]
  by_cases hxy :
      ‖iteratedDeriv j (fun t : ℝ => bagCubicNormalizedPhysicalKernel δ.1 h.1 N.1 t z.1.2) z.1.1‖ ≤
      ‖iteratedDeriv j (fun t : ℝ => bagCubicNormalizedPhysicalKernel δ.1 h.1 N.1 t z.1.1) z.1.2‖
  · rw [max_eq_right hxy]
    exact hy
  · rw [max_eq_left (le_of_not_ge hxy)]
    exact hx

private theorem selected_parameters_eventually :
    ∀ᶠ N : ℝ in atTop, 1<N ∧ N^(-(3/4 : ℝ))∈Ioo (0 : ℝ) (1/2) ∧
      1/Real.log N∈Icc (0 : ℝ) 1 := by
  have hd := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<3/4)
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    hd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with N hN hdN
  have hN1 : 1<N := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) hN
  have hN0 : 0<N := zero_lt_one.trans hN1
  have hL : 1 ≤ Real.log N := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hN
  exact ⟨hN1,⟨Real.rpow_pos_of_pos hN0 _,hdN⟩,
    div_nonneg zero_le_one (by linarith),
    (div_le_iff₀ (Real.log_pos hN1)).mpr (by simpa using hL)⟩

private theorem selected_tail_power (j k m : ℕ) (N : {r : ℝ // 1<r}) :
    N.1^k*N.1^(j+1) ≤ (N.1^(-(3/4 : ℝ)))^(4*(j+k+m+1)-1)*N.1^(4*(j+k+m+1)) := by
  have hN : 0<N.1 := zero_lt_one.trans N.2
  let n := 4*(j+k+m+1)
  have hn : 1 ≤ n := by dsimp only [n]; omega
  have he : (N.1^(-(3/4 : ℝ)))^(n-1)*N.1^n=
      N.1^(-(3/4 : ℝ)*((n-1 : ℕ) : ℝ)+(n : ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le,←Real.rpow_natCast,←Real.rpow_add hN]
  have he' : N.1^k*N.1^(j+1)=N.1^((k : ℝ)+((j+1 : ℕ) : ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_natCast,←Real.rpow_add hN]
  change N.1^k*N.1^(j+1) ≤ (N.1^(-(3/4 : ℝ)))^(n-1)*N.1^n
  rw [he,he']
  apply Real.rpow_le_rpow_of_exponent_le N.2.le
  rw [Nat.cast_sub hn]
  dsimp only [n]
  push_cast
  linarith

/-- Every fixed pure jet and polynomial spatial weight has arbitrary power saving
outside the positive stationary box, for the actual shrinking-cutoff family. -/
theorem bagCubicNormalizedPhysicalKernel_selected_exterior_decay (j m k : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℝ in atTop,
      ∀z : {z : ℝ×ℝ // 0<z.1 ∧ 0<z.2 ∧
        ¬(z.1∈Icc (1/4 : ℝ) 4 ∧ z.2∈Icc (1/4 : ℝ) 4)},
      N^k*(1+z.1.1+z.1.2)^m*
        max ‖iteratedDeriv j (fun t : ℝ => bagCubicNormalizedPhysicalKernel
            (N^(-(3/4 : ℝ))) (1/Real.log N) N t z.1.2) z.1.1‖
          ‖iteratedDeriv j (fun t : ℝ => bagCubicNormalizedPhysicalKernel
            (N^(-(3/4 : ℝ))) (1/Real.log N) N z.1.1 t) z.1.2‖ ≤ C := by
  let n := 4*(j+k+m+1)
  obtain ⟨C,hC,hCb⟩ := bagCubicNormalizedPhysicalKernel_exterior_decay j n
  refine ⟨C,hC,?_⟩
  filter_upwards [selected_parameters_eventually] with N hpars
  intro z
  have hN : 0<N := zero_lt_one.trans hpars.1
  let δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)} := ⟨N^(-(3/4 : ℝ)),hpars.2.1⟩
  let h : {r : ℝ // r∈Icc (0 : ℝ) 1} := ⟨1/Real.log N,hpars.2.2⟩
  let w := 1+z.1.1+z.1.2
  let a := max ‖iteratedDeriv j (fun t : ℝ => bagCubicNormalizedPhysicalKernel δ.1 h.1 N t z.1.2) z.1.1‖
    ‖iteratedDeriv j (fun t : ℝ => bagCubicNormalizedPhysicalKernel δ.1 h.1 N z.1.1 t) z.1.2‖
  have hw : 1 ≤ w := by dsimp only [w]; linarith [z.2.1,z.2.2.1]
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hn : m+j ≤ n := by dsimp only [n]; omega
  have hwp : w^(m+j) ≤ w^n := pow_le_pow_right₀ hw hn
  have hscale : N^k*N^(j+1) ≤ δ.1^(n-1)*N^n := selected_tail_power j k m ⟨N,hpars.1⟩
  have hb : N^n*w^n*a ≤ C*N^(j+1)*w^j/δ.1^(n-1) := hCb δ h ⟨N,hN⟩ z
  have hD : 0<δ.1^(n-1)*N^n*w^n := mul_pos (mul_pos (pow_pos δ.2.1 _) (pow_pos hN _)) (pow_pos hw0 _)
  change N^k*w^m*a ≤ C
  apply (mul_le_mul_iff_right₀ hD).mp
  calc (δ.1^(n-1)*N^n*w^n)*(N^k*w^m*a)
      = (N^k*w^m*δ.1^(n-1))*(N^n*w^n*a) := by ring
    _ ≤ (N^k*w^m*δ.1^(n-1))*(C*N^(j+1)*w^j/δ.1^(n-1)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C*(N^k*N^(j+1))*w^(m+j) := by
      rw [pow_add]
      field_simp [δ.2.1.ne']
      ring
    _ ≤ C*(δ.1^(n-1)*N^n)*w^n := by
      apply mul_le_mul _ hwp (pow_nonneg hw0.le _) (by positivity)
      exact mul_le_mul_of_nonneg_left hscale hC.le
    _ = (δ.1^(n-1)*N^n*w^n)*C := by ring

end RHTower.BAGTrace

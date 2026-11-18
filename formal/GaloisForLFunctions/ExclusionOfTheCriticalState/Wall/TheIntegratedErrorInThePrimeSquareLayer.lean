import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheLogarithmicLocationsOfThePrimeMassBins
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePrimeNumberTheoremOnTheState
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheFirstAbsoluteMomentOfStateIncrements

/-!
# Integrated error of the prime-square layer

A displacement of a Chebyshev mass bin costs the translation modulus of the
profile in the time integral. The reciprocal weight costs its first absolute
moment. Both errors are integrable on the logarithmic mass axis.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry

private def translationCost (g : ℝ → ℝ) (d : ℝ) : ℝ := ∫ u : ℝ, |g u-g (u+d)|

private theorem translationCost_neg (g : ℝ → ℝ) (d : ℝ) :
    translationCost g (-d) = translationCost g d := by
  change (∫ u, |g u-g (u+-d)|) = _
  rw [← integral_add_right_eq_self (fun u : ℝ => |g u-g (u+-d)|) d]
  simp only [add_neg_cancel_right,translationCost]
  exact integral_congr_ae (Eventually.of_forall fun u => abs_sub_comm _ _)

private theorem state_translationCost {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (he : F =ᵐ[volume] Φ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ d : ℝ, |d| < ε → translationCost Φ d ≤ Real.sqrt |d| := by
  have eq (d : ℝ) : translationCost F d = translationCost Φ d := by
    apply integral_congr_ae
    filter_upwards [he,(measurePreserving_add_right volume d).quasiMeasurePreserving.ae_eq_comp he]
      with u hu hv
    change F (u+d) = Φ (u+d) at hv
    rw [hu,hv]
  obtain ⟨ε,hε,h⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    ((criticalState_tendsto_L1_increment_div_sqrt hW ht hF).eventually_lt_const zero_lt_one)
  refine ⟨ε,hε,fun d hd => ?_⟩
  by_cases hz : d=0
  · simp [translationCost,hz]
  have hp := abs_pos.mpr hz
  have hc := (div_lt_iff₀ (Real.sqrt_pos.mpr hp)).mp (h ⟨hp,hd⟩)
  rw [one_mul] at hc
  have ha : translationCost Φ d = translationCost F |d| := by
    rw [eq]
    rcases le_or_gt 0 d with hd | hd
    · rw [abs_of_nonneg hd]
    · rw [abs_of_neg hd,translationCost_neg]
  exact ha.le.trans hc.le

private theorem bin_slice_bound {g : ℝ → ℝ} (hg : Integrable g) (v l w : ℝ) :
    (∫ t : ℝ, |w*g (t-l)-g (t-v)|) ≤
      |w-1|*(∫ u, |g u|)+translationCost g (l-v) := by
  have h1 : Integrable (fun t : ℝ => g (t-l)) := hg.comp_sub_right l
  have h2 : Integrable (fun t : ℝ => g (t-v)) := hg.comp_sub_right v
  have h := integral_mono ((h1.const_mul w).sub h2).abs
    ((h1.abs.const_mul |w-1|).add (h1.sub h2).abs) (fun t => by
      change |w*g (t-l)-g (t-v)| ≤ |w-1|*|g (t-l)|+|g (t-l)-g (t-v)|
      rw [← abs_mul,show w*g (t-l)-g (t-v)=(w-1)*g (t-l)+(g (t-l)-g (t-v)) by ring]
      exact abs_add_le ..)
  refine h.trans_eq ?_
  change (∫ t : ℝ, |w-1|*|g (t-l)|+|g (t-l)-g (t-v)|) = _
  rw [integral_add (h1.abs.const_mul _) (h1.sub h2).abs,integral_const_mul]
  have tr (f : ℝ → ℝ) : (∫ t : ℝ, f (t-l)) = ∫ t, f t := by
    simpa only [sub_eq_add_neg] using integral_add_right_eq_self f (-l)
  rw [tr (fun t => |g t|)]
  congr 1
  change _ = ∫ u : ℝ, |g u-g (u+(l-v))|
  rw [← tr (fun u => |g u-g (u+(l-v))|)]
  exact integral_congr_ae (Eventually.of_forall fun t => by rw [show t-l+(l-v)=t-v by ring])

private theorem squareLayer_mass_coordinates {g : ℝ → ℝ} (hg : Continuous g)
    (hs : ∀ u, 0 ≤ u → g u=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |g u| ≤ C*Real.exp (2*u))
    {t : ℝ} (ht : 0 ≤ t) :
    primePowerLayer g 2 t = (∫ v, squareBinWeight v*g (t-squareBinLocation v))/2 := by
  let f := fun v : ℝ => squareBinWeight v*g (t-squareBinLocation v)
  rw [primeSquareLayer_eq_bin_integral hg hs hC hb ht]
  calc _ = ∫ r : ℝ, f (2*r) := by
             refine integral_congr_ae (Eventually.of_forall fun r => ?_)
             simp only [f,squareBinWeight,squareBinLocation,show 2*r/2=r by ring]
    _ = _ := by
             rw [Measure.integral_comp_mul_left,smul_eq_mul,abs_of_pos (by norm_num : (0:ℝ)<2⁻¹)]
             ring

private def binDifference (g : ℝ → ℝ) (v t : ℝ) : ℝ :=
  squareBinWeight v*g (t-squareBinLocation v)-g (t-v)

private theorem late_bin_cost {g : ℝ → ℝ} (hg : Integrable g)
    {ε : ℝ} (hε : 0 < ε) (hd : ∀ d : ℝ, |d| < ε → translationCost g d ≤ Real.sqrt |d|) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ v : ℝ in atTop, squareBinLocation v ≤ v+1 ∧
      (∫ t, |binDifference g v t|) ≤ K*Real.exp ((-1/40)*v) := by
  obtain ⟨B,hB,h⟩ := exists_squareBin_displacement
  let M := ∫ u, |g u|
  have hM : 0 ≤ M := integral_nonneg fun _ => abs_nonneg _
  have he : Tendsto (fun v : ℝ => B*Real.exp (-v/20)) atTop (𝓝 0) := by
    have h0 := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
      (by norm_num : (-1/20:ℝ)<0))
    have eq (v : ℝ) : (-1/20)*v= -v/20 := by ring
    simpa only [eq,mul_zero,Function.comp_apply] using h0.const_mul B
  refine ⟨B*M+Real.sqrt B,by positivity,?_⟩
  filter_upwards [h,he.eventually_lt_const hε,he.eventually_lt_const zero_lt_one,
    eventually_ge_atTop (0:ℝ)] with v hv hsmall hone hv0
  have hloc := (le_abs_self (squareBinLocation v-v)).trans (hv.1.trans hone.le)
  refine ⟨by linarith only [hloc],?_⟩
  have hterm := (hd _ (hv.1.trans_lt hsmall)).trans (Real.sqrt_le_sqrt hv.1)
  have heq : Real.sqrt (Real.exp (-v/20))=Real.exp ((-1/40)*v) := by
    rw [show -v/20=((-1/40)*v)+((-1/40)*v) by ring,Real.exp_add,← sq,
      Real.sqrt_sq (Real.exp_pos _).le]
  rw [Real.sqrt_mul hB,heq] at hterm
  have hle : Real.exp (-v/20) ≤ Real.exp ((-1/40)*v) :=
    Real.exp_le_exp.mpr (by linarith only [hv0])
  apply (bin_slice_bound hg v (squareBinLocation v) (squareBinWeight v)).trans
  calc _ ≤ (B*Real.exp ((-1/40)*v))*M + Real.sqrt B*Real.exp ((-1/40)*v) :=
             add_le_add (mul_le_mul_of_nonneg_right (hv.2.trans (mul_le_mul_of_nonneg_left hle hB)) hM) hterm
    _ = _ := by ring

private theorem integrated_square_error {g : ℝ → ℝ} (hc : Continuous g) (hg : Integrable g)
    (hs : ∀ u, 0 ≤ u → g u=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |g u| ≤ C*Real.exp (2*u))
    {ε : ℝ} (hε : 0 < ε) (hd : ∀ d : ℝ, |d| < ε → translationCost g d ≤ Real.sqrt |d|) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ V : ℝ in atTop,
      let E := fun t : ℝ => primePowerLayer g 2 t-(∫ u, g u)/2
      IntegrableOn E (Ioi (V+1)) ∧
        (∫ t in Ioi (V+1), |E t|) ≤ B*Real.exp ((-1/40)*V) := by
  obtain ⟨K,hK,hcost⟩ := late_bin_cost hg hε hd
  obtain ⟨a,ha⟩ := eventually_atTop.1 hcost
  refine ⟨20*K,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop a,eventually_ge_atTop (0:ℝ)] with V hV hV0
  let μ := (volume : Measure ℝ).restrict (Ioi V)
  let H := fun z : ℝ × ℝ => binDifference g z.1 z.2
  let G := fun t : ℝ => ∫ v, binDifference g v t ∂μ
  have hm : Measurable H := by
    dsimp only [H,binDifference]
    exact ((measurable_squareBinWeight.comp measurable_fst).mul (hc.measurable.comp
      (measurable_snd.sub (monotone_squareBinLocation.measurable.comp measurable_fst)))).sub
      (hc.measurable.comp (measurable_snd.sub measurable_fst))
  have hExp := (integrableOn_exp_mul_Ioi (by norm_num : (-1/40:ℝ)<0) V).const_mul K
  have hpoint : ∀ᵐ v ∂μ, (∫ t, ‖H (v,t)‖) ≤ K*Real.exp ((-1/40)*v) := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := V))] with v hv
    simpa only [H,Real.norm_eq_abs] using (ha v (hV.trans (le_of_lt hv))).2
  have hi : Integrable H (μ.prod volume) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).2
    refine ⟨Eventually.of_forall fun v => ((hg.comp_sub_right _).const_mul _).sub
      (hg.comp_sub_right _),hExp.mono' hm.aestronglyMeasurable.norm.integral_prod_right' ?_⟩
    filter_upwards [hpoint] with v hv
    rwa [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  have hiG : Integrable G := hi.integral_prod_right
  have hglobal : (∫ t, |G t|) ≤ (40*K)*Real.exp ((-1/40)*V) := by
    calc _ ≤ ∫ t, ∫ v, ‖H (v,t)‖ ∂μ := integral_mono hiG.abs hi.integral_norm_prod_right
               (fun t => norm_integral_le_integral_norm (fun v => H (v,t)))
      _ = ∫ v, ∫ t, ‖H (v,t)‖ ∂μ := (integral_integral_swap (f := fun v t => ‖H (v,t)‖) hi.norm).symm
      _ ≤ ∫ v, K*Real.exp ((-1/40)*v) ∂μ := integral_mono_ae hi.integral_norm_prod_left hExp hpoint
      _ = _ := by
        dsimp only [μ]
        rw [integral_const_mul,integral_exp_mul_Ioi (by norm_num : (-1/40:ℝ)<0)]
        ring
  have heq : ∀ᵐ t ∂volume.restrict (Ioi (V+1)),
      primePowerLayer g 2 t-(∫ u, g u)/2=G t/2 := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := V+1)),
      ae_restrict_of_ae hi.prod_left_ae] with t ht hrow
    have htv : V+1<t := ht
    have hz (v : ℝ) (hv : v ∉ Ioi V) : binDifference g v t=0 := by
      have hv' : v ≤ V := le_of_not_gt hv
      have hL := (monotone_squareBinLocation hv').trans (ha V hV).1
      rw [binDifference,hs _ (by linarith only [htv,hL]),hs _ (by linarith only [htv,hv']),mul_zero,sub_zero]
    have hfull : Integrable (fun v => binDifference g v t) := by
      have hcut := (integrable_indicator_iff measurableSet_Ioi).2
        (show IntegrableOn (fun v => binDifference g v t) (Ioi V) from hrow)
      exact hcut.congr (Eventually.of_forall fun v => by
        by_cases hv : v ∈ Ioi V
        · exact indicator_of_mem hv _
        · rw [indicator_of_notMem hv,hz v hv])
    have hread : G t=∫ v, binDifference g v t :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hz
    have hsum := integral_add hfull (hg.comp_sub_left t)
    change (∫ v, binDifference g v t+g (t-v)) =
      (∫ v, binDifference g v t)+(∫ v, g (t-v)) at hsum
    simp only [binDifference,sub_add_cancel] at hsum
    rw [integral_sub_left_eq_self] at hsum
    rw [squareLayer_mass_coordinates hc hs hC hb (by linarith only [hV0,htv]),hread]
    change _ = (∫ v, squareBinWeight v*g (t-squareBinLocation v)-g (t-v))/2
    linarith only [hsum]
  refine ⟨(hiG.div_const 2).integrableOn.congr heq.symm,?_⟩
  calc _ = ∫ t in Ioi (V+1), |G t|/2 := integral_congr_ae (heq.mono fun t ht => by
               rw [ht,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)])
    _ ≤ ∫ t, |G t|/2 := setIntegral_le_integral (hiG.abs.div_const 2)
             (Eventually.of_forall fun t => div_nonneg (abs_nonneg _) (by norm_num))
    _ = (∫ t, |G t|)/2 := by rw [integral_div]
    _ ≤ _ := (div_le_div_of_nonneg_right hglobal (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)

end GaloisForLFunctions.ExclusionOfTheCriticalState

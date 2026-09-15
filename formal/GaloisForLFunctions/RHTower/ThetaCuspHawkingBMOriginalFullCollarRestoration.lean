import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalFullMetricCollar

open Set Filter Topology MeasureTheory Complex
namespace RHTower.D4BMOriginalFullCollarRestoration
open D4BMJointSource D4BMModularCore D4BMJointWave D4BMLaplaceRadial
open D4BMOriginalFullMetricCollar D4BMOriginalFullMetricDifference
open D4BMOriginalCanonicalForcingMatch D4BMOriginalForcingJointHorizon
open D4BMOriginalMetricHorizon D4BMOriginalCornerForcing
noncomputable section
set_option autoImplicit false
private abbrev mu (q : XiZeroCopy) := D4BMLeftModeRadialEquation.eigenvalue q
private abbrev grad (q : XiZeroCopy) (br : Bool) :=
  reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1

private theorem kernel_continuous (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) :
    ContinuousOn (forcingKernel q br amp K w) (Iio (0:ℝ)) := by
  have hu : Continuous radialUnit := continuous_iff_continuousAt.mpr
    (fun x => (radialUnit_hasDerivAt x).continuousAt)
  have hp : Continuous (fun x : ℝ => power (2*physicalRate q br) (1+radialUnit x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (continuousAt_ofReal_cpow_const (1+radialUnit x) (2*physicalRate q br)
      (Or.inr (radialUnit_add_one_pos x).ne')).comp_of_eq
        (continuous_const.add hu).continuousAt rfl
  have hF : Continuous (fun x : ℝ => forcingProfile (physicalRate q br) amp 1 K (radialUnit x)) := by
    unfold forcingProfile
    fun_prop
  intro x hx
  have hn := ((normalizable_derivatives_continued (w:=w) (chi:=physicalRadialFrequency q)
    (horizonCoordinate_interior x hx)).1.continuousAt).comp_of_eq
      (horizonCoordinate_hasDerivAt x).continuousAt rfl
  exact (((show Continuous (fun x : ℝ => Complex.exp (w*(x:ℂ))) by fun_prop).continuousAt.mul
    hF.continuousAt).mul hn).continuousWithinAt

private def kernelDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (k x : ℝ) : ℂ :=
  kernelCut q br amp w (Real.exp k) x-physicalSelfSourceCoefficient q*forcingKernel q br amp (grad q br) w x

private theorem kernel_difference_continuous (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (k : ℝ) :
    ContinuousOn (kernelDifference q br amp w k) (Iio (0:ℝ)) := by
  have h1 := kernel_continuous q br amp (grad q br) w
  have h2 := kernel_continuous q br amp (grad q br+1) w
  have h := ((h1.const_mul (firstWeight q (Real.exp k))).add
    (h2.const_mul (secondWeight q (Real.exp k)))).sub (h1.const_mul (physicalSelfSourceCoefficient q))
  exact h.congr (fun x _ => by rw [kernelDifference,kernel_two_kernels];rfl)

private theorem forcing_moment_kernel (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b L k : ℝ) :
    forcingMoment q br amp w a b L k=
      mu q*w*(∫ p in a..b,Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p)*
        kernelDifference q br amp w k (-L/2) := by
  unfold forcingMoment
  simp_rw [original_forcing_error_kernel]
  rw [intervalIntegral.integral_mul_const]
  unfold kernelDifference
  ring

/-- The literal forcing moment has compact radial admission before it is
split from the original full metric integral. -/
theorem forcing_moment_radial_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (a b k A B : ℝ) (hA : 0<A) (hAB : A≤B) :
    IntervalIntegrable (fun L => forcingMoment q br amp w a b L k) volume A B := by
  have hx : MapsTo (fun L : ℝ => -L/2) (Icc A B) (Iio (0:ℝ)) := by
    intro L hL
    have hLp := hA.trans_le hL.1
    change -L/2<0
    linarith
  have hc := (kernel_difference_continuous q br amp w k).comp
    (show ContinuousOn (fun L : ℝ => -L/2) (Icc A B) by fun_prop) hx
  have hi : IntervalIntegrable (fun L => kernelDifference q br amp w k (-L/2)) volume A B :=
    hc.intervalIntegrable_of_Icc hAB
  have he : (fun L => forcingMoment q br amp w a b L k)=fun L =>
      (mu q*w*(∫ p in a..b,Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p))*
        kernelDifference q br amp w k (-L/2) := funext (fun L => forcing_moment_kernel q br amp w a b L k)
  rw [he]
  exact hi.const_mul _

/-- The entire actual finite metric discrepancy is separately radially
admitted. This is required before separating the physical forcing term. -/
theorem full_metric_radial_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ L0 : ℝ,0<L0 ∧ ∀ a b k A B : ℝ,
      0<a → a≤b → 0≤k → 4≤Real.exp k → L0≤A → A≤B →
      IntervalIntegrable (fun L => metricDifference q br amp w a b L k) volume A B := by
  obtain ⟨G,hG,hg⟩ := metric_source_boundary_integrable q br amp
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨L0,hL0,h⟩ := hg w hwi hw
  refine ⟨L0,hL0,?_⟩
  intro a b k A B ha hab hk hk4 hA hAB
  have hi := (h a b k A B ha hab hk hk4 hA hAB).add
    (forcing_moment_radial_integrable q br amp w a b k A B (hL0.trans_le hA) hAB)
  simpa only [Pi.add_apply,sub_add_cancel] using hi

/-- The original one-half collar Jacobian turns the entire forcing moment
into the unchanged canonical radial kernel discrepancy. -/
theorem forcing_moment_collar (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b k A B : ℝ) :
    (∫ L in A..B,forcingMoment q br amp w a b L k)/2=
      mu q*w*(∫ p in a..b,Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p)*
        (∫ x in -B/2..-A/2,kernelDifference q br amp w k x) := by
  simp_rw [forcing_moment_kernel]
  rw [intervalIntegral.integral_const_mul]
  have he : (fun L : ℝ => kernelDifference q br amp w k (-L/2))=
      fun L => kernelDifference q br amp w k (L*(-(1/2:ℝ))) := by
    funext L
    congr 1
    ring
  rw [he,intervalIntegral.integral_comp_mul_right _ (by norm_num : -(1/2:ℝ)≠0)]
  have hA : A*(-(1/2:ℝ))=-A/2 := by ring
  have hB : B*(-(1/2:ℝ))=-B/2 := by ring
  rw [hA,hB]
  have hs : (∫ x in -A/2..-B/2,kernelDifference q br amp w k x)=
      -(∫ x in -B/2..-A/2,kernelDifference q br amp w k x) := intervalIntegral.integral_symm _ _
  rw [hs]
  norm_num [smul_eq_mul]
  ring

/-- The canonical forcing counterterm at the actual radial cutoff and the
same finite cusp height; its two angular weights are retained unchanged. -/
def forcingCountertermDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b L k : ℝ) : ℂ :=
  mu q*w*(∫ p in a..b,Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p)*
    ((firstWeight q (Real.exp k)-physicalSelfSourceCoefficient q)*
        canonicalForcingCounterterm q br amp (grad q br) w (horizonCoordinate (-L/2))+
      secondWeight q (Real.exp k)*canonicalForcingCounterterm q br amp (grad q br+1) w (horizonCoordinate (-L/2)))

/-- Complete original finite metric collar discrepancy with its derived
source/boundary leading trace and source-fixed canonical forcing counterterms. -/
def fullCollarDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a b A L k : ℝ) : ℂ :=
  ((∫ X in A..L,metricDifference q br amp w a b X k)-(L-A)•metricTrace q br amp w a b k)/2-
    forcingCountertermDifference q br amp w a b L k


private theorem kernel_difference_integral (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (k A B : ℝ) (hA : 0<A) (hB : 0<B) :
    (∫ x in -B/2..-A/2,kernelDifference q br amp w k x)=
      (∫ x in -B/2..-A/2,kernelCut q br amp w (Real.exp k) x)-
        physicalSelfSourceCoefficient q*(∫ x in -B/2..-A/2,forcingKernel q br amp (grad q br) w x) := by
  have hsub : uIcc (-B/2) (-A/2)⊆Iio (0:ℝ) := by
    intro x hx
    exact lt_of_le_of_lt hx.2 (max_lt (by linarith) (by linarith))
  have h1 : IntervalIntegrable (forcingKernel q br amp (grad q br) w) volume (-B/2) (-A/2) :=
    ((kernel_continuous q br amp (grad q br) w).mono hsub).intervalIntegrable
  have h2 : IntervalIntegrable (forcingKernel q br amp (grad q br+1) w) volume (-B/2) (-A/2) :=
    ((kernel_continuous q br amp (grad q br+1) w).mono hsub).intervalIntegrable
  have hi : IntervalIntegrable (kernelCut q br amp w (Real.exp k)) volume (-B/2) (-A/2) := by
    have ht := (h1.const_mul (firstWeight q (Real.exp k))).add (h2.const_mul (secondWeight q (Real.exp k)))
    exact ht.congr (fun x _ => (kernel_two_kernels q br amp w (Real.exp k) x).symm)
  unfold kernelDifference
  rw [intervalIntegral.integral_sub hi (h1.const_mul _),intervalIntegral.integral_const_mul]

private theorem horizon_depth_tendsto :
    Tendsto (fun L : ℝ => horizonCoordinate (-L/2)) atTop (𝓝[>] (0:ℝ)) := by
  have hx : Tendsto (fun L : ℝ => -L/2) atTop atBot := by
    apply tendsto_atBot.mpr
    intro x
    filter_upwards [eventually_ge_atTop (-2*x)] with L hL
    linarith
  exact D4BMFundamentalNorm.horizonCoordinate_tendsto_positive.comp hx

/-- The complete original metric collar, including every temporal endpoint,
all four boundary transfers and the source-fixed forcing counterterms, has
independent horizon/cusp restoration uniformly over all positive time intervals.
This is a collar theorem: the outer region and the static-time corner still
need to be joined to this physical expression before full QNM matching. -/
theorem full_metric_collar_joint_restoration (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ A : ℝ,0<A ∧
      ∀ T : ℝ×ℝ→{v : ℝ×ℝ // 0<v.1 ∧ v.1≤v.2},
        Tendsto (fun z : ℝ×ℝ => fullCollarDifference q br amp w (T z).val.1 (T z).val.2 A z.1 z.2)
          ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  obtain ⟨G1,hG1,h1⟩ := metric_source_boundary_joint_limit q br amp
  obtain ⟨G2,_,h2⟩ := full_metric_radial_integrable q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1≤w.re := by linarith [le_max_right G1 G2]
  have hwr : -2<w.re := by linarith [le_max_left G1 G2]
  obtain ⟨L1,hL1,hl1⟩ := h1 w hwi hw1
  obtain ⟨L2,hL2,hl2⟩ := h2 w hwi hw2
  obtain ⟨B,hB,hBh,hforce⟩ := canonical_forcing_difference_joint_limit q br amp w hwi hwr
  have hsmall : ∀ᶠ L : ℝ in atTop,horizonCoordinate (-L/2)<B :=
    (horizon_depth_tendsto.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hB)
  obtain ⟨D,hD⟩ := eventually_atTop.mp hsmall
  let A := max L1 (max L2 D)
  have hA1 : L1≤A := le_max_left _ _
  have hA2 : L2≤A := (le_max_left L2 D).trans (le_max_right _ _)
  have hDA : D≤A := (le_max_right L2 D).trans (le_max_right _ _)
  have hA : 0<A := hL1.trans_le hA1
  have hAb : horizonCoordinate (-A/2)∈Ioo (0:ℝ) 1 := horizonCoordinate_interior _ (by linarith)
  refine ⟨A,hA,?_⟩
  intro T
  let M : ℝ×ℝ→Ici A := fun z => ⟨max A z.1,show A ≤ max A z.1 from le_max_left _ _⟩
  have hs := hl1 A hA1 ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) Prod.snd tendsto_snd T M
  have hmap : Tendsto (fun z : ℝ×ℝ => (horizonCoordinate (-z.1/2),z.2))
      ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) ((𝓝[>] (0:ℝ)) ×ˢ (atTop : Filter ℝ)) :=
    (horizon_depth_tendsto.comp tendsto_fst).prodMk tendsto_snd
  have hf := (hforce (horizonCoordinate (-A/2)) hAb.1 (hD A hDA).le).comp hmap
  obtain ⟨C,hC,hc⟩ := source_onset_interval_bound q br w hwr
  have hmul : Tendsto (fun z : ℝ×ℝ =>
      mu q*w*(∫ p in (T z).val.1..(T z).val.2,Complex.exp (-w*(p:ℂ))*timeOnset (2*physicalRate q br) p)*
        canonicalForcingDifferenceCut q br amp w (horizonCoordinate (-A/2)) (horizonCoordinate (-z.1/2),z.2))
      ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
    have hlim := hf.norm.const_mul (‖mu q*w‖*C)
    simp only [norm_zero,mul_zero] at hlim
    apply squeeze_zero_norm (fun z => ?_) hlim
    rw [norm_mul,norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (hc _ _ (T z).property.1.le (T z).property.2) (norm_nonneg _)) (norm_nonneg _)
  have hsum := hs.add hmul
  simp only [zero_add] at hsum
  apply hsum.congr'
  have hcut : ∀ᶠ z : ℝ×ℝ in ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)),
      A≤z.1 ∧ 0≤z.2 ∧ 4≤Real.exp z.2 :=
    (tendsto_fst.eventually (eventually_ge_atTop A)).and
      (tendsto_snd.eventually ((eventually_ge_atTop (0:ℝ)).and
        (Real.tendsto_exp_atTop.eventually (eventually_ge_atTop (4:ℝ)))))
  filter_upwards [hcut] with z hz
  have hZ : 0<z.1 := hA.trans_le hz.1
  have hM : (M z:ℝ)=z.1 := max_eq_right hz.1
  have hi := hl2 (T z).val.1 (T z).val.2 z.2 A z.1 (T z).property.1 (T z).property.2 hz.2.1 hz.2.2 hA2 hz.1
  have hfi := forcing_moment_radial_integrable q br amp w (T z).val.1 (T z).val.2 z.2 A z.1 hA hz.1
  have he := forcing_moment_collar q br amp w (T z).val.1 (T z).val.2 z.2 A z.1
  rw [kernel_difference_integral q br amp w z.2 A z.1 hA hZ] at he
  rw [hM,intervalIntegral.integral_sub hi hfi]
  unfold fullCollarDifference forcingCountertermDifference canonicalForcingDifferenceCut
  rw [tortoiseOf_horizonCoordinate (by linarith : -z.1/2<0),
    tortoiseOf_horizonCoordinate (by linarith : -A/2<0)]
  linear_combination -he

end
end RHTower.D4BMOriginalFullCollarRestoration

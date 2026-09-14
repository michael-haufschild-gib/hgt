import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCircleEquation

/-!
The original causal scalar period is identified before temporal transformation.
The full cutoff circle kernel admits Fubini against the unchanged physical
reader on every finite null source rectangle. The source integral transports
all three original correction coefficients into their native radial responses;
restoration cancels them and retains the complete original onset lift.
The exact finite-height error is the remaining original cusp tail. One
integrable envelope gives uniform restoration on bounded null rectangles
and compact original-time integration for every polynomial moment. All
angular remainder jets also have uniform rapid cusp decay on those rectangles.
No unbounded horizon/time interchange or full metric matching is asserted.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped ContDiff
open GaloisForLFunctions.HTGeometry ScalarTwoJet
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMOriginalCausalPeriod
open D4BMJointSource D4BMNativeCircle D4BMNativeCuspJets D4BMNativeResponse
open D4BMOriginalCirclePeriod D4BMOriginalCircleEquation D4BMOriginalScalarRestoration
open D4BMOriginalCausalRestoration D4BMOriginalCausalPotential D4BMGlobalAngularResponse D4BMModularCore
open D4BMCausalKernel D4BMCausalCusp

private theorem coordinates_continuous : Continuous coordinates := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact UpperHalfPlane.continuous_re
  · exact UpperHalfPlane.continuous_im

private theorem scalar_continuous (u : ℂ) :
    Continuous (fun z : UpperHalfPlane => scalar u (coordinates z)) :=
  (D4BMAngularSeries.cuspLeg_contDiffOn .scalar u).continuousOn.comp_continuous
    coordinates_continuous (fun z => z.im_pos)

private theorem cutoffPower_continuous (k : ℂ) :
    Continuous (fun z : UpperHalfPlane => cutoffPower k (coordinates z)) := by
  have hp : Continuous (fun z : UpperHalfPlane => (z.im:ℂ)^k) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr z.im_pos.ne')).comp
      UpperHalfPlane.continuous_im.continuousAt
  exact (sourceCutoff_smooth.continuous.comp coordinates_continuous).mul hp

private theorem radius_continuous (p r : ℝ) : Continuous (fun v : ℝ × ℝ => radius p r v.1 v.2) := by
  apply Real.continuousOn_arcosh.comp_continuous
  · unfold invariant
    apply Continuous.max continuous_const
    apply Continuous.div <;> try fun_prop
    intro z
    exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  · intro z; exact le_max_left (1:ℝ) _
private theorem weight_continuous (s amp : ℂ) : Continuous (fun v : ℝ × ℝ => sourceWeight s amp v.1 v.2) := by
  have h₁ := (timeReducedCoefficient_joint_continuous s amp).comp
    (show Continuous (fun v : ℝ × ℝ => ((v.1+v.2)/2,min ((v.1-v.2)/2) 0)) by fun_prop)
  have h₂ := (timeReducedCoefficient_joint_continuous s amp).comp
    (show Continuous (fun v : ℝ × ℝ => ((v.1+v.2)/2,min (-((v.1-v.2)/2)) 0)) by fun_prop)
  exact h₁.sub h₂
private theorem circle_continuous (a : ℂ) : Continuous (powerCircle a) := by
  have hk : ContinuousOn (legendreKernel (-a)) (Ioi 0) := fun d hd =>
    ((legendreKernel_derivatives (-a) hd).1.continuousAt).continuousWithinAt
  have h := hk.comp_continuous Real.continuous_cosh (fun d => Real.cosh_pos d)
  simpa only [Function.comp_def,← powerCircle_eq_legendre] using h
private theorem cutoff_continuous (q : XiZeroCopy) :
    Continuous (fun v : ℝ × UpperHalfPlane => cutoffResidual q v.1 v.2) := by
  have hn : Continuous (fun v : ℝ × ℝ × ℝ => mean q v.1 v.2.1 v.2.2) := (nativeMean_joint_smooth q).continuous
  have hc : Continuous (fun v : ℝ × UpperHalfPlane => (v.1,v.2.re,Real.log v.2.im)) :=
    continuous_fst.prodMk ((UpperHalfPlane.continuous_re.comp continuous_snd).prodMk
      ((UpperHalfPlane.continuous_im.comp continuous_snd).log (fun v => v.2.im_pos.ne')))
  have hm : Continuous (fun v : ℝ × UpperHalfPlane => mean q v.1 v.2.re (Real.log v.2.im)) := by
    simpa only [Function.comp_def] using hn.comp hc
  apply hm.sub
  apply continuous_finsetSum
  intro i _
  exact ((circle_continuous _).comp continuous_fst |>.const_mul _).mul
    ((cutoffPower_continuous (principalExponent q i)).comp continuous_snd)
private theorem cutoff_eq_native (q : XiZeroCopy) (d : ℝ) (z : UpperHalfPlane) :
    cutoffResidual q d z=nativeCutoffResidual q d z := by
  simp only [cutoffResidual,nativeCutoffResidual,transportedPrincipal,Real.exp_log z.im_pos,
    Finset.mul_sum,coefficient,cutoffPower]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change _=cutoff (coordinates z)*(principalAmplitude q i*(z.im:ℂ)^principalExponent q i*powerCircle (principalExponent q i) d)
  change principalAmplitude q i*powerCircle (principalExponent q i) d*(cutoff (coordinates z)*(z.im:ℂ)^principalExponent q i)=_
  ring
private theorem cutoff_eq_jet (q : XiZeroCopy) (d : ℝ) (z : UpperHalfPlane) :
    cutoffResidual q d z=nativeJet [] (residualField q) ![d,z.re,Real.log z.im] := by
  simp only [nativeJet,residualField,Matrix.cons_val,Real.exp_log z.im_pos,cutoffResidual,
    powerCutoffHeight,cutoffPower,coordinates,cutoff]
private theorem cutoff_reader_bound (q : XiZeroCopy) (D : Ici (0:ℝ)) :
    ∃ K : ℝ, Integrable (fun z => K*‖physicalDualDensity q z‖) measure ∧
      ∀ᵐ z ∂measure, ∀ d ∈ Icc (0:ℝ) D,
        ‖scalar (physicalAngularParameter q) (coordinates z)*cutoffResidual q d z‖ ≤ K*‖physicalDualDensity q z‖ := by
  obtain ⟨K,hK⟩ := residualJet_height_bound q [] D
  refine ⟨K,((MemLp.integrable (by norm_num) (physicalDualDensity_memLp q)).norm).const_mul K,?_⟩
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  intro d hd
  rw [cutoff_eq_jet]
  have he : scalar (physicalAngularParameter q) (coordinates z)*nativeJet [] (residualField q) ![d,z.re,Real.log z.im]=
      physicalDualDensity q z*((z.im:ℂ)*nativeJet [] (residualField q) ![d,z.re,Real.log z.im]) := by
    dsimp [physicalDualDensity]
    field_simp [Complex.ofReal_ne_zero.mpr z.im_pos.ne']
  rw [he,norm_mul,mul_comm K]
  exact mul_le_mul_of_nonneg_left (hK d hd z hz) (norm_nonneg _)

private def sourceMeasure (p r : ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc (0:ℝ) p)).prod (volume.restrict (Ioc (0:ℝ) r))
private instance sourceMeasure_finite (p r : ℝ) : IsFiniteMeasure (sourceMeasure p r) := by
  unfold sourceMeasure
  infer_instance
private theorem sourceMeasure_mem (p r : ℝ) :
    ∀ᵐ v ∂sourceMeasure p r, v ∈ Icc (0:ℝ) p ×ˢ Icc (0:ℝ) r := by
  have h : ∀ᵐ v ∂sourceMeasure p r, v ∈ Ioc (0:ℝ) p ×ˢ Ioc (0:ℝ) r := by
    unfold sourceMeasure
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  filter_upwards [h] with v hv
  exact ⟨⟨hv.1.1.le,hv.1.2⟩,⟨hv.2.1.le,hv.2.2⟩⟩
private theorem continuous_source_integrable {F : (ℝ × ℝ) → ℂ} (hF : Continuous F) (p r : ℝ) :
    Integrable F (sourceMeasure p r) := by
  have h : IntegrableOn F (Icc (0:ℝ) p ×ˢ Icc (0:ℝ) r) ((volume : Measure ℝ).prod volume) :=
    hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  unfold sourceMeasure
  rw [Measure.prod_restrict]
  exact h.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
private theorem source_integral {F : (ℝ × ℝ) → ℂ} (hF : Continuous F) (p r : Ici (0:ℝ)) :
    (∫ v, F v ∂sourceMeasure p r) = ∫ a in (0:ℝ)..p.val, ∫ b in (0:ℝ)..r.val, F (a,b) := by
  have h := continuous_source_integrable hF p r
  change Integrable F ((volume.restrict (Ioc (0:ℝ) p.val)).prod (volume.restrict (Ioc (0:ℝ) r.val))) at h
  unfold sourceMeasure
  rw [integral_prod _ h]
  simp only [intervalIntegral.integral_of_le p.property,intervalIntegral.integral_of_le r.property]

private def integrand (q : XiZeroCopy) (s amp : ℂ) (p r : ℝ)
    (v : ℝ × ℝ) (z : UpperHalfPlane) : ℂ :=
  scalar (physicalAngularParameter q) (coordinates z)*cutoffResidual q (radius p r v.1 v.2) z*sourceWeight s amp v.1 v.2
private theorem integrand_continuous (q : XiZeroCopy) (s amp : ℂ) (p r : ℝ) :
    Continuous (Function.uncurry (integrand q s amp p r)) := by
  have hK := (cutoff_continuous q).comp (((radius_continuous p r).comp continuous_fst).prodMk continuous_snd)
  exact (((scalar_continuous (physicalAngularParameter q)).comp continuous_snd).mul hK).mul
    ((weight_continuous s amp).comp continuous_fst)
private theorem integrand_integrable (q : XiZeroCopy) (s amp : ℂ) (p r : Ici (0:ℝ)) :
    Integrable (Function.uncurry (integrand q s amp p r)) ((sourceMeasure p r).prod measure) := by
  have hc : IsCompact (Icc (0:ℝ) p.val ×ˢ Icc (0:ℝ) r.val) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨D,hD⟩ := hc.exists_bound_of_continuousOn (radius_continuous p r).continuousOn
  obtain ⟨K,hKi,hK⟩ := cutoff_reader_bound q ⟨max D 0,by change 0 ≤ max D 0; exact le_max_right _ _⟩
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuousOn (weight_continuous s amp).continuousOn
  let B' := max B 0
  have hBi : Integrable (fun z => (K*‖physicalDualDensity q z‖)*B') measure := hKi.mul_const B'
  apply (hBi.comp_snd (sourceMeasure p r)).mono' (integrand_continuous q s amp p r).aestronglyMeasurable
  have hmeas : MeasurableSet {x : (ℝ × ℝ) × UpperHalfPlane |
      ‖integrand q s amp p r x.1 x.2‖ ≤ (K*‖physicalDualDensity q x.2‖)*B'} := by
    apply measurableSet_le (integrand_continuous q s amp p r).norm.measurable
    have hdensity : Continuous (physicalDualDensity q) := by
      have hy : Continuous (fun z : UpperHalfPlane => (z.im:ℂ)) :=
        Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im
      exact (hy.inv₀ (fun z => Complex.ofReal_ne_zero.mpr z.im_pos.ne')).mul
        (scalar_continuous (physicalAngularParameter q))
    exact ((continuous_const.mul (hdensity.comp continuous_snd).norm).mul continuous_const).measurable
  apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
  filter_upwards [sourceMeasure_mem p r] with v hv
  filter_upwards [hK] with z hz
  have hd0 : 0 ≤ radius p r v.1 v.2 := Real.arcosh_nonneg (le_max_left _ _)
  have hd : radius p r v.1 v.2 ≤ max D 0 := by
    exact (le_abs_self _).trans ((hD v hv).trans (le_max_left _ _))
  have hb : ‖sourceWeight s amp v.1 v.2‖ ≤ B' := (hB v hv).trans (le_max_left _ _)
  change ‖scalar (physicalAngularParameter q) (coordinates z)*cutoffResidual q (radius p r v.1 v.2) z*sourceWeight s amp v.1 v.2‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (hz _ ⟨hd0,hd⟩) hb (norm_nonneg _) (by
    exact (norm_nonneg _).trans (hz _ ⟨hd0,hd⟩))
private theorem cutoff_integral_value (q : XiZeroCopy) (d : Ici (0:ℝ)) :
    (∫ z, scalar (physicalAngularParameter q) (coordinates z)*cutoffResidual q d z ∂measure) =
      physicalSelfSourceCoefficient q*powerCircle (readerExponent q) d+
        ∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
          physicalAngularGap q q i*coefficient q d i := by
  have h := original_circle_period q d
  change _-_= _ at h
  linear_combination h

private theorem scalar_radius (nu : ℂ) {p r a b : ℝ} (ha : a ≤ p) (hb : b ≤ r) :
    riemannKernel nu ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)=legendreKernel nu (Real.cosh (radius p r a b)) := by
  have hc : |(p-r)/2-(a-b)/2| ≤ (p+r-a-b)/2 := by rw [abs_le]; constructor <;> linarith
  rw [radius,Real.cosh_arcosh (le_max_left _ _),max_eq_right (invariant_causal ⟨_,_,_,hc⟩)]
  rfl
private theorem radius_integral (nu s amp : ℂ) (p r : Ici (0:ℝ)) :
    (1/4:ℂ)*(∫ v, powerCircle (-nu) (radius p r v.1 v.2)*sourceWeight s amp v.1 v.2 ∂sourceMeasure p r)=
      radialResponse nu s amp ((p+r)/2) ((p-r)/2) := by
  have hc : Continuous (fun v : ℝ × ℝ => powerCircle (-nu) (radius p r v.1 v.2)*sourceWeight s amp v.1 v.2) :=
    ((circle_continuous (-nu)).comp (radius_continuous p r)).mul (weight_continuous s amp)
  rw [source_integral hc p r,radialResponse_null_native nu s amp p.property r.property]
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  apply intervalIntegral.integral_congr
  intro b hb
  dsimp only
  rw [powerCircle_eq_legendre,neg_neg,scalar_radius nu
    (show a ≤ p.val from (show a ∈ Icc 0 p.val by simpa only [uIcc_of_le (show 0 ≤ p.val from p.property)] using ha).2)
    (show b ≤ r.val from (show b ∈ Icc 0 r.val by simpa only [uIcc_of_le (show 0 ≤ r.val from r.property)] using hb).2)]
  rfl

private theorem residual_integral (q : XiZeroCopy) (s amp : ℂ) (p r : Ici (0:ℝ)) (z : UpperHalfPlane) :
    fullNullResidual q s amp p r z.re (Real.log z.im)=
      (1/4:ℂ)*∫ v, cutoffResidual q (radius p r v.1 v.2) z*sourceWeight s amp v.1 v.2 ∂sourceMeasure p r := by
  have hc : Continuous (fun v : ℝ × ℝ => cutoffResidual q (radius p r v.1 v.2) z*sourceWeight s amp v.1 v.2) :=
    ((cutoff_continuous q).comp ((radius_continuous p r).prodMk continuous_const)).mul (weight_continuous s amp)
  rw [source_integral hc p r,fullNullResidual_eq_nativeResidualIntegral]
  simp_rw [cutoff_eq_native]
  rfl

/-- The original full causal residual and physical scalar admit Fubini over their
actual finite null rectangle; all three cutoff channels remain in the kernel. -/
private theorem original_residual_reader_integral (q : XiZeroCopy) (s amp : ℂ) (p r : Ici (0:ℝ)) :
    (∫ z, scalar (physicalAngularParameter q) (coordinates z)*
      fullNullResidual q s amp p r z.re (Real.log z.im) ∂measure) =
        (1/4:ℂ)*∫ v, (∫ z, integrand q s amp p r v z ∂measure) ∂sourceMeasure p r := by
  have he (z : UpperHalfPlane) : scalar (physicalAngularParameter q) (coordinates z)*
      fullNullResidual q s amp p r z.re (Real.log z.im)=
        (1/4:ℂ)*∫ v, integrand q s amp p r v z ∂sourceMeasure p r := by
    rw [residual_integral]
    have h (v : ℝ × ℝ) : integrand q s amp p r v z=
        scalar (physicalAngularParameter q) (coordinates z)*
          (cutoffResidual q (radius p r v.1 v.2) z*sourceWeight s amp v.1 v.2) := by
      dsimp only [integrand]; ring
    simp_rw [h]
    rw [integral_const_mul]
    ring
  simp_rw [he]
  rw [integral_const_mul,← integral_integral_swap (integrand_integrable q s amp p r)]

private theorem coefficient_integral (q : XiZeroCopy) (s amp : ℂ) (i : Fin 3) (p r : Ici (0:ℝ)) :
    (1/4:ℂ)*(∫ v, coefficient q (radius p r v.1 v.2) i*sourceWeight s amp v.1 v.2 ∂sourceMeasure p r)=
      principalNullResponse q s amp i p r := by
  have he (v : ℝ × ℝ) : coefficient q (radius p r v.1 v.2) i*sourceWeight s amp v.1 v.2=
      principalAmplitude q i*(powerCircle (principalExponent q i) (radius p r v.1 v.2)*sourceWeight s amp v.1 v.2) := by
    dsimp only [coefficient]; ring
  simp_rw [he]
  rw [integral_const_mul]
  have h := radius_integral (-principalExponent q i) s amp p r
  simp only [neg_neg] at h
  unfold principalNullResponse
  linear_combination principalAmplitude q i*h

/-- The exact physical reading of the complete native causal residual restores to
its original scalar radial response; no nonzero-source premise is required. -/
theorem original_native_period (q : XiZeroCopy) (s amp : ℂ) (p r : Ici (0:ℝ)) :
    (∫ z, scalar (physicalAngularParameter q) (coordinates z)*
      fullNullResidual q s amp p r z.re (Real.log z.im) ∂measure)-
        (∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
          physicalAngularGap q q i*principalNullResponse q s amp i p r)=
      physicalSelfSourceCoefficient q*radialResponse (-readerExponent q) s amp ((p+r)/2) ((p-r)/2) := by
  let c (i : Fin 3) := scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/physicalAngularGap q q i
  let K (v : ℝ × ℝ) := powerCircle (readerExponent q) (radius p r v.1 v.2)*sourceWeight s amp v.1 v.2
  let B (i : Fin 3) (v : ℝ × ℝ) := coefficient q (radius p r v.1 v.2) i*sourceWeight s amp v.1 v.2
  have hK : Integrable K (sourceMeasure p r) := continuous_source_integrable
    (((circle_continuous _).comp (radius_continuous p r)).mul (weight_continuous s amp)) p r
  have hB (i : Fin 3) : Integrable (B i) (sourceMeasure p r) := continuous_source_integrable
    ((((circle_continuous _).comp (radius_continuous p r)).const_mul _).mul (weight_continuous s amp)) p r
  have hv (v : ℝ × ℝ) : (∫ z, integrand q s amp p r v z ∂measure)=
      physicalSelfSourceCoefficient q*K v+∑ i : Fin 3, c i*B i v := by
    have hd : 0 ≤ radius p r v.1 v.2 := Real.arcosh_nonneg (le_max_left _ _)
    unfold integrand
    rw [integral_mul_const,cutoff_integral_value q ⟨_,hd⟩]
    dsimp only [K,B,c]
    rw [add_mul,Finset.sum_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  rw [original_residual_reader_integral]
  simp_rw [hv]
  rw [integral_add (hK.const_mul _) (integrable_finsetSum Finset.univ (fun i _ => (hB i).const_mul _)),
    integral_const_mul,integral_finsetSum Finset.univ (fun i _ => (hB i).const_mul _)]
  simp_rw [integral_const_mul]
  have hk := radius_integral (-readerExponent q) s amp p r
  simp only [neg_neg] at hk
  have hb (i : Fin 3) : (1/4:ℂ)*(∫ v, B i v ∂sourceMeasure p r)=principalNullResponse q s amp i p r :=
    coefficient_integral q s amp i p r
  have he : (1/4:ℂ)*(physicalSelfSourceCoefficient q*(∫ v, K v ∂sourceMeasure p r)+
      ∑ i : Fin 3, c i*(∫ v, B i v ∂sourceMeasure p r))=
        physicalSelfSourceCoefficient q*((1/4:ℂ)*(∫ v, K v ∂sourceMeasure p r))+
          ∑ i : Fin 3, c i*((1/4:ℂ)*(∫ v, B i v ∂sourceMeasure p r)) := by
    rw [mul_add,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  rw [he]
  simp_rw [hb]
  rw [show (1/4:ℂ)*(∫ v, K v ∂sourceMeasure p r)=
    radialResponse (-readerExponent q) s amp ((p+r)/2) ((p-r)/2) from hk]
  change _+_-_= _
  ring

/-- The original causal height finite part equals the original scalar radial
response plus its complete onset lift, with the original source coefficient. -/
theorem original_causal_finitePart_radial (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : Ici (0:ℝ)) :
    Tendsto (fun Y => truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
      originalPotential q branch amp p r z.re (Real.log z.im)) Y-
      principalCounterterm q (D4BMOriginalCuspJets.coefficient q branch amp p r) Y) atTop
      (𝓝 (physicalSelfSourceCoefficient q*(radialResponse (-readerExponent q) (physicalRate q branch) amp
        ((p+r)/2) ((p-r)/2)+nullLift (physicalRate q branch) amp p r))) := by
  have h := original_causal_restoration q branch amp p r
  rw [original_native_period] at h
  have he : physicalSelfSourceCoefficient q*radialResponse (-readerExponent q) (physicalRate q branch) amp
      ((p+r)/2) ((p-r)/2)+nullLift (physicalRate q branch) amp p r*physicalSelfSourceCoefficient q =
      physicalSelfSourceCoefficient q*(radialResponse (-readerExponent q) (physicalRate q branch) amp
        ((p+r)/2) ((p-r)/2)+nullLift (physicalRate q branch) amp p r) := by ring
  rwa [he] at h


private theorem radius_joint_continuous :
    Continuous (fun z : (ℝ×ℝ)×(ℝ×ℝ) => radius z.1.1 z.1.2 z.2.1 z.2.2) := by
  apply Real.continuousOn_arcosh.comp_continuous
  · unfold invariant
    apply Continuous.max continuous_const
    apply Continuous.div <;> try fun_prop
    intro z
    exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  · intro z
    change (1:ℝ) ≤ max 1 _
    exact le_max_left _ _

private theorem compact_source_bounds (s amp : ℂ) (T : Ici (0:ℝ)) :
    ∃ D : Ici (0:ℝ), ∃ B : ℝ, 0≤B ∧
      ∀ p∈Icc 0 T.val, ∀ r∈Icc 0 T.val, ∀ a∈Icc 0 p, ∀ b∈Icc 0 r,
        radius p r a b≤D.val ∧ ‖sourceWeight s amp a b‖≤B := by
  let box : Set (ℝ×ℝ) := Icc 0 T.val ×ˢ Icc 0 T.val
  have hc : IsCompact box := isCompact_Icc.prod isCompact_Icc
  obtain ⟨D,hD⟩ := (hc.prod hc).exists_bound_of_continuousOn radius_joint_continuous.continuousOn
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuousOn (weight_continuous s amp).continuousOn
  refine ⟨⟨max D 0,by change 0 ≤ max D 0; exact le_max_right _ _⟩,
    max B 0,le_max_right _ _,?_⟩
  intro p hp r hr a ha b hb
  have hab : (a,b)∈box := ⟨⟨ha.1,ha.2.trans hp.2⟩,⟨hb.1,hb.2.trans hr.2⟩⟩
  constructor
  · exact (le_abs_self _).trans ((hD ((p,r),(a,b)) ⟨⟨hp,hr⟩,hab⟩).trans (le_max_left _ _))
  · exact (hB (a,b) hab).trans (le_max_left _ _)

private theorem lift_compact_bound (s amp : ℂ) (T : Ici (0:ℝ)) :
    ∃ L : ℝ, 0≤L ∧ ∀ p∈Icc 0 T.val, ∀ r∈Icc 0 T.val, ‖nullLift s amp p r‖≤L := by
  have hL : Continuous (radialLift s 0 amp 1) :=
    continuous_iff_continuousAt.mpr (fun t => (radialLift_hasDerivAt s 0 amp 1 t).continuousAt)
  have hO : Continuous (timeOnset (2*s)) :=
    continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt (2*s) p).continuousAt)
  have hc : Continuous (fun v : ℝ×ℝ => nullLift s amp v.1 v.2) := by
    exact (hL.comp (show Continuous (fun v : ℝ×ℝ => (v.1-v.2)/2) by fun_prop)).mul
      (hO.comp continuous_fst)
  obtain ⟨L,hL⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s:=Icc (0:ℝ) T.val ×ˢ Icc (0:ℝ) T.val) hc.continuousOn
  exact ⟨max L 0,le_max_right _ _,fun p hp r hr => (hL (p,r) ⟨hp,hr⟩).trans (le_max_left _ _)⟩

private theorem residual_reader_value (q : XiZeroCopy) (s amp : ℂ)
    (p r : Ici (0:ℝ)) (z : UpperHalfPlane) :
    scalar (physicalAngularParameter q) (coordinates z)*fullNullResidual q s amp p r z.re (Real.log z.im)=
      (1/4:ℂ)*∫ a in (0:ℝ)..p.val, ∫ b in (0:ℝ)..r.val, integrand q s amp p r (a,b) z := by
  have hc : Continuous (fun v : ℝ×ℝ => integrand q s amp p r v z) := by
    exact (continuous_const.mul ((cutoff_continuous q).comp
      ((radius_continuous p r).prodMk continuous_const))).mul (weight_continuous s amp)
  rw [← source_integral hc p r,residual_integral]
  have he (v : ℝ×ℝ) : integrand q s amp p r v z=
      scalar (physicalAngularParameter q) (coordinates z)*
        (cutoffResidual q (radius p r v.1 v.2) z*sourceWeight s amp v.1 v.2) := by
    dsimp only [integrand]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  ring

/-- One original angular majorant controls the complete causal residual for
all target points of the bounded null rectangle, including its edges. -/
theorem original_nativeResidual_uniform_bound (q : XiZeroCopy) (s amp : ℂ) (T : Ici (0:ℝ)) :
    ∃ B : ℝ, 0≤B ∧ ∀ᵐ z ∂measure, ∀ p∈Icc 0 T.val, ∀ r∈Icc 0 T.val,
      ‖scalar (physicalAngularParameter q) (coordinates z)*fullNullResidual q s amp p r z.re (Real.log z.im)‖≤
        B*‖physicalDualDensity q z‖ := by
  obtain ⟨D,C,hC,hgeom⟩ := compact_source_bounds s amp T
  obtain ⟨K,hKi,hK⟩ := cutoff_reader_bound q D
  let K' := max K 0
  have hK0 : 0≤K' := le_max_right _ _
  have hT : 0 ≤ T.val := T.property
  refine ⟨K'*C*T.val*T.val,by positivity,?_⟩
  filter_upwards [hK] with z hz
  intro p hp r hr
  let M := K'*‖physicalDualDensity q z‖*C
  have hM : 0≤M := by dsimp [M]; positivity
  have hi (a : ℝ) (ha : a∈Icc 0 p) (b : ℝ) (hb : b∈Icc 0 r) :
      ‖integrand q s amp p r (a,b) z‖≤M := by
    obtain ⟨hd,hc⟩ := hgeom p hp r hr a ha b hb
    have hkc := (hz (radius p r a b) ⟨Real.arcosh_nonneg (le_max_left _ _),hd⟩).trans
      (mul_le_mul_of_nonneg_right (le_max_left K 0) (norm_nonneg _))
    change ‖(scalar (physicalAngularParameter q) (coordinates z)*cutoffResidual q (radius p r a b) z)*
      sourceWeight s amp a b‖≤M
    rw [norm_mul]
    exact mul_le_mul hkc hc (norm_nonneg _) (by positivity)
  have hinner (a : ℝ) (ha : a∈uIoc (0:ℝ) p) :
      ‖∫ b in (0:ℝ)..r, integrand q s amp p r (a,b) z‖≤M*r := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=(0:ℝ)) (b:=r) (C:=M) (fun b hb =>
        hi a (by rw [uIoc_of_le hp.1] at ha;exact ⟨ha.1.le,ha.2⟩)
          b (by rw [uIoc_of_le hr.1] at hb;exact ⟨hb.1.le,hb.2⟩))
    simpa only [sub_zero,abs_of_nonneg hr.1] using hh
  have houter := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=p) (C:=M*r) hinner
  simp only [sub_zero,abs_of_nonneg hp.1] at houter
  rw [residual_reader_value q s amp ⟨p,hp.1⟩ ⟨r,hr.1⟩]
  calc
    _ ≤ ‖∫ a in (0:ℝ)..p,∫ b in (0:ℝ)..r,integrand q s amp p r (a,b) z‖ := by
      rw [norm_mul]
      apply mul_le_of_le_one_left (norm_nonneg _)
      norm_num
    _ ≤ M*r*p := houter
    _ ≤ M*T.val*T.val := mul_le_mul (mul_le_mul_of_nonneg_left hr.2 hM)
      hp.2 hp.1 (mul_nonneg hM hT)
    _ = _ := by dsimp [M];ring

/-- The complete original cutoff source, including its unchanged onset lift,
has a single integrable angular envelope over each bounded causal rectangle. -/
theorem originalCutoffResidual_uniform_dominating (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (T : Ici (0:ℝ)) :
    ∃ G : UpperHalfPlane → ℝ, Integrable G measure ∧ (∀ z,0≤G z) ∧
      ∀ᵐ z ∂measure, ∀ p∈Icc 0 T.val, ∀ r∈Icc 0 T.val,
        ‖scalar (physicalAngularParameter q) (coordinates z)*originalCutoffResidual q branch amp p r z‖≤G z := by
  obtain ⟨B,hB,hbound⟩ := original_nativeResidual_uniform_bound q (physicalRate q branch) amp T
  obtain ⟨L,hL,hlift⟩ := lift_compact_bound (physicalRate q branch) amp T
  let G := fun z => B*‖physicalDualDensity q z‖+
    L*‖scalar (physicalAngularParameter q) (coordinates z)*squareResidual q (coordinates z)‖
  have hG : Integrable G measure :=
    (((MemLp.integrable (by norm_num) (physicalDualDensity_memLp q)).norm).const_mul B).add
      ((scalar_squareResidual_integrable q (physicalAngularParameter q)).norm.const_mul L)
  refine ⟨G,hG,fun z => by dsimp [G];positivity,?_⟩
  filter_upwards [hbound] with z hz
  intro p hp r hr
  rw [originalCutoffResidual_decomposition,mul_add]
  have he : scalar (physicalAngularParameter q) (coordinates z)*
      (nullLift (physicalRate q branch) amp p r*squareResidual q (coordinates z))=
      nullLift (physicalRate q branch) amp p r*
        (scalar (physicalAngularParameter q) (coordinates z)*squareResidual q (coordinates z)) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (hz p hp r hr) (by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hlift p hp r hr) (norm_nonneg _)))

/-- Literal original scalar period at finite height, with its prescribed
three principal counterterms and no change of source or cutoff. -/
def originalFiniteHeightPeriod (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r Y : ℝ) : ℂ :=
  truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
    originalPotential q branch amp p r z.re (Real.log z.im)) Y-
    principalCounterterm q (D4BMOriginalCuspJets.coefficient q branch amp p r) Y

/-- The restored original causal radial response, including the onset lift. -/
def originalRadialPeriod (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p r : ℝ) : ℂ :=
  physicalSelfSourceCoefficient q*(radialResponse (-readerExponent q) (physicalRate q branch) amp
    ((p+r)/2) ((p-r)/2)+nullLift (physicalRate q branch) amp p r)

private theorem original_finiteHeight_eq_residual (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (p r : Ici (0:ℝ)) (Y : ℝ) (hY : 4 ≤ Y) :
    originalFiniteHeightPeriod q branch amp p r Y =
      truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
        originalCutoffResidual q branch amp p r z) Y-
      ∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
        physicalAngularGap q q i*D4BMOriginalCuspJets.coefficient q branch amp p r i := by
  let b := D4BMOriginalCuspJets.coefficient q branch amp p r
  have hR := originalCutoffResidual_scalar_integrable q branch amp p r
  have hp (i : Fin 3) : IntegrableOn (fun z : UpperHalfPlane =>
      scalar (physicalAngularParameter q) (coordinates z)*
        cutoffPower (principalExponent q i) (coordinates z)) {z : UpperHalfPlane | z.im ≤ Y} measure :=
    truncated_integrable _ ((scalar_continuous (physicalAngularParameter q)).mul
      (cutoffPower_continuous (principalExponent q i))) Y
  have hv (z : UpperHalfPlane) : scalar (physicalAngularParameter q) (coordinates z)*
      originalPotential q branch amp p r z.re (Real.log z.im)=
    scalar (physicalAngularParameter q) (coordinates z)*originalCutoffResidual q branch amp p r z+
      ∑ i : Fin 3, b i*(scalar (physicalAngularParameter q) (coordinates z)*
        cutoffPower (principalExponent q i) (coordinates z)) := by
    simp only [originalCutoffResidual,mul_sub,Finset.mul_sum]
    have he : (∑ i : Fin 3, scalar (physicalAngularParameter q) (coordinates z)*
        (b i*cutoffPower (principalExponent q i) (coordinates z)))=
        ∑ i : Fin 3, b i*(scalar (physicalAngularParameter q) (coordinates z)*
          cutoffPower (principalExponent q i) (coordinates z)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    change _ = _-(∑ i : Fin 3, scalar (physicalAngularParameter q) (coordinates z)*
      (b i*cutoffPower (principalExponent q i) (coordinates z)))+_
    rw [he,sub_add_cancel]
  have hs := principal_sum_restoration q b Y hY
  unfold originalFiniteHeightPeriod truncatedIntegral
  simp_rw [hv]
  rw [integral_add hR.integrableOn (integrable_finsetSum (Finset.univ : Finset (Fin 3))
    (fun i _ => (hp i).const_mul (b i))),
    integral_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => (hp i).const_mul (b i))]
  simp_rw [integral_const_mul]
  change _+_-_= _-_
  dsimp only [truncatedIntegral] at hs
  linear_combination hs

/-- Exact finite-height error of the actual original period. All transported
principal terms cancel; the error is precisely the full original cusp tail. -/
theorem original_finiteHeight_sub_radial (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r : Ici (0:ℝ)) (Y : ℝ) (hY : 4 ≤ Y) :
    originalFiniteHeightPeriod q branch amp p r Y-originalRadialPeriod q branch amp p r=
      -(∫ z in {z : UpperHalfPlane | Y < z.im},
        scalar (physicalAngularParameter q) (coordinates z)*originalCutoffResidual q branch amp p r z ∂measure) := by
  have he := tendsto_nhds_unique (original_causal_finitePart q branch amp p r)
    (original_causal_finitePart_radial q branch amp p r)
  change _=originalRadialPeriod q branch amp p r at he
  rw [original_finiteHeight_eq_residual q branch amp p r Y hY,← he]
  have hm : MeasurableSet {z : UpperHalfPlane | z.im ≤ Y} :=
    measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const
  have hc := setIntegral_compl hm (originalCutoffResidual_scalar_integrable q branch amp p r)
  simp only [compl_setOf,not_le] at hc
  rw [hc]
  change _-_-(_-_)= -(_-_)
  dsimp only [truncatedIntegral]
  ring

private theorem real_height_tail_tendsto (G : UpperHalfPlane → ℝ) (hG : Integrable G measure) :
    Tendsto (fun Y : ℝ => ∫ z in {z : UpperHalfPlane | Y < z.im},G z ∂measure) atTop (𝓝 0) := by
  have hm (Y : ℝ) : MeasurableSet {z : UpperHalfPlane | z.im ≤ Y} :=
    measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const
  have hu : (⋃ Y : ℝ, {z : UpperHalfPlane | z.im ≤ Y})=univ := by
    ext z
    simp only [mem_iUnion,mem_setOf_eq,mem_univ,iff_true]
    exact ⟨z.im,le_rfl⟩
  have hmono : Monotone (fun Y : ℝ => {z : UpperHalfPlane | z.im ≤ Y}) :=
    fun _ _ hab _ hz => hz.trans hab
  have h := tendsto_setIntegral_of_monotone (μ:=measure) (f:=G) hm hmono
    (by simpa only [hu,integrableOn_univ] using hG)
  simp only [hu,setIntegral_univ] at h
  have he (Y : ℝ) : (∫ z in {z : UpperHalfPlane | Y < z.im},G z ∂measure)=
      (∫ z,G z ∂measure)-(∫ z in {z : UpperHalfPlane | z.im ≤ Y},G z ∂measure) := by
    simpa only [compl_setOf,not_le] using setIntegral_compl (hm Y) hG
  simp_rw [he]
  have hc : Tendsto (fun _ : ℝ => ∫ z,G z ∂measure) atTop (𝓝 (∫ z,G z ∂measure)) := tendsto_const_nhds
  simpa only [sub_self] using hc.sub h

/-- A single vanishing real tail bounds the literal finite-height error at
every point of a bounded null rectangle. This is uniform cusp restoration
of the original field, without a supplied domination premise. -/
theorem original_finiteHeight_uniform_error (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (T : Ici (0:ℝ)) :
    ∃ e : ℝ → ℝ, (∀ Y,0 ≤ e Y) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ Y,4 ≤ Y → ∀ p∈Icc 0 T.val, ∀ r∈Icc 0 T.val,
        ‖originalFiniteHeightPeriod q branch amp p r Y-originalRadialPeriod q branch amp p r‖ ≤ e Y := by
  obtain ⟨G,hG,hpos,hbound⟩ := originalCutoffResidual_uniform_dominating q branch amp T
  refine ⟨fun Y => ∫ z in {z : UpperHalfPlane | Y < z.im},G z ∂measure,
    fun Y => integral_nonneg hpos,real_height_tail_tendsto G hG,?_⟩
  intro Y hY p hp r hr
  rw [original_finiteHeight_sub_radial q branch amp ⟨p,hp.1⟩ ⟨r,hr.1⟩ Y hY,norm_neg]
  apply norm_integral_le_of_norm_le hG.integrableOn
  exact (ae_restrict_of_ae hbound).mono (fun z hz => hz p hp r hr)

private theorem lift_joint_continuous (s amp : ℂ) :
    Continuous (fun v : ℝ×ℝ => nullLift s amp v.1 v.2) := by
  have hL : Continuous (radialLift s 0 amp 1) :=
    continuous_iff_continuousAt.mpr (fun t => (radialLift_hasDerivAt s 0 amp 1 t).continuousAt)
  have hO : Continuous (timeOnset (2*s)) :=
    continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt (2*s) p).continuousAt)
  exact (hL.comp (show Continuous (fun v : ℝ×ℝ => (v.1-v.2)/2) by fun_prop)).mul
    (hO.comp continuous_fst)

private theorem reader_integral_time_continuous (q : XiZeroCopy) (s amp : ℂ) (x : ℝ)
    (z : UpperHalfPlane) :
    Continuous (fun p : ℝ => (1/4:ℂ)*∫ a in (0:ℝ)..p,
      ∫ b in (0:ℝ)..(p-2*x),integrand q s amp p (p-2*x) (a,b) z) := by
  have hrad : Continuous (fun v : (ℝ×ℝ)×ℝ => radius v.1.1 (v.1.1-2*x) v.1.2 v.2) :=
    radius_joint_continuous.comp
      (g:=fun v : (ℝ×ℝ)×(ℝ×ℝ) => radius v.1.1 v.1.2 v.2.1 v.2.2)
      (f:=fun v : (ℝ×ℝ)×ℝ => ((v.1.1,v.1.1-2*x),(v.1.2,v.2)))
      (show Continuous (fun v : (ℝ×ℝ)×ℝ =>
      ((v.1.1,v.1.1-2*x),(v.1.2,v.2))) by fun_prop)
  have hi : Continuous (fun v : (ℝ×ℝ)×ℝ =>
      integrand q s amp v.1.1 (v.1.1-2*x) (v.1.2,v.2) z) :=
    (continuous_const.mul ((cutoff_continuous q).comp (hrad.prodMk continuous_const))).mul
      ((weight_continuous s amp).comp (show Continuous (fun v : (ℝ×ℝ)×ℝ => (v.1.2,v.2)) by fun_prop))
  have hin : Continuous (fun v : ℝ×ℝ =>
      ∫ b in (0:ℝ)..(v.1-2*x),integrand q s amp v.1 (v.1-2*x) (v.2,b) z) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f:=fun v : ℝ×ℝ => fun b => integrand q s amp v.1 (v.1-2*x) (v.2,b) z)
      hi (by fun_prop)
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f:=fun p a => ∫ b in (0:ℝ)..(p-2*x),integrand q s amp p (p-2*x) (a,b) z)
    hin continuous_id).const_mul (1/4:ℂ)

private theorem original_residual_time_continuousOn (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (a b x : ℝ) (ha : 0 ≤ a) (hx : x ≤ 0) (z : UpperHalfPlane) :
    ContinuousOn (fun p => scalar (physicalAngularParameter q) (coordinates z)*
      originalCutoffResidual q branch amp p (p-2*x) z) (Icc a b) := by
  have hL : Continuous (fun p : ℝ => nullLift (physicalRate q branch) amp p (p-2*x)) :=
    (lift_joint_continuous (physicalRate q branch) amp).comp
      (g:=fun v : ℝ×ℝ => nullLift (physicalRate q branch) amp v.1 v.2)
      (f:=fun p : ℝ => (p,p-2*x)) (show Continuous (fun p : ℝ => (p,p-2*x)) by fun_prop)
  have hc := ((reader_integral_time_continuous q (physicalRate q branch) amp x z).add
    (hL.mul_const (scalar (physicalAngularParameter q) (coordinates z)*squareResidual q (coordinates z))))
  apply hc.continuousOn.congr
  intro p hp
  have hp0 : 0 ≤ p := ha.trans hp.1
  have hr0 : 0 ≤ p-2*x := by linarith
  dsimp only [Pi.add_apply]
  rw [originalCutoffResidual_decomposition,mul_add,
    residual_reader_value q (physicalRate q branch) amp ⟨p,hp0⟩ ⟨p-2*x,hr0⟩]
  ring

private theorem originalRadialPeriod_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    Continuous (fun v : ℝ×ℝ => originalRadialPeriod q branch amp v.1 v.2) := by
  have hR := (radialResponse_continuous (-readerExponent q) (physicalRate q branch) amp).comp
    (show Continuous (fun v : ℝ×ℝ => ((v.1+v.2)/2,(v.1-v.2)/2)) by fun_prop)
  exact (hR.add (lift_joint_continuous _ _)).const_mul (physicalSelfSourceCoefficient q)

private theorem time_rectangle (a b x p : ℝ) (ha : 0 ≤ a) (hx : x ≤ 0) (hp : p∈Icc a b) :
    p∈Icc 0 (b-2*x) ∧ p-2*x∈Icc 0 (b-2*x) := by
  constructor <;> constructor <;> linarith [hp.1,hp.2]

/-- Actual finite-height source periods are continuous in the original ingoing
clock on compact causal intervals, including the onset endpoint. -/
theorem originalFiniteHeightPeriod_time_continuousOn (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (a b x Y : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hx : x ≤ 0) (hY : 4 ≤ Y) :
    ContinuousOn (fun p => originalFiniteHeightPeriod q branch amp p (p-2*x) Y) (Icc a b) := by
  let T : Ici (0:ℝ) := ⟨b-2*x,by change 0 ≤ b-2*x; linarith⟩
  obtain ⟨G,hG,_,hbound⟩ := originalCutoffResidual_uniform_dominating q branch amp T
  have hc : ContinuousOn (fun p => ∫ z in {z : UpperHalfPlane | Y < z.im},
      scalar (physicalAngularParameter q) (coordinates z)*
        originalCutoffResidual q branch amp p (p-2*x) z ∂measure) (Icc a b) := by
    apply continuousOn_of_dominated (bound:=G)
    · intro p hp
      obtain ⟨hp',hr'⟩ := time_rectangle a b x p ha hx hp
      exact (originalCutoffResidual_scalar_integrable q branch amp
        ⟨p,hp'.1⟩ ⟨p-2*x,hr'.1⟩).integrableOn.aestronglyMeasurable
    · intro p hp
      obtain ⟨hp',hr'⟩ := time_rectangle a b x p ha hx hp
      exact (ae_restrict_of_ae hbound).mono (fun z hz => hz p hp' (p-2*x) hr')
    · exact hG.integrableOn
    · exact Filter.Eventually.of_forall (original_residual_time_continuousOn q branch amp a b x ha hx)
  have hr := (originalRadialPeriod_continuous q branch amp).comp
    (show Continuous (fun p : ℝ => (p,p-2*x)) by fun_prop)
  apply (hr.continuousOn.sub hc).congr
  intro p hp
  obtain ⟨hp',hr'⟩ := time_rectangle a b x p ha hx hp
  have he := original_finiteHeight_sub_radial q branch amp ⟨p,hp'.1⟩ ⟨p-2*x,hr'.1⟩ Y hY
  dsimp only [Pi.sub_apply,Function.comp_def]
  linear_combination he

/-- Compact original-clock integration commutes with the prescribed cusp
restoration for every polynomial time moment and temporal frequency. The actual source, original smooth
cutoff, three counterterms and full onset lift are retained. -/
theorem original_compact_time_moment_restoration (q : XiZeroCopy) (branch : Bool) (amp w : ℂ) (n : ℕ)
    (a b x : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hx : x ≤ 0) :
    Tendsto (fun Y => ∫ p in a..b,((p:ℂ)^n*Complex.exp (-w*(p:ℂ)))*
      originalFiniteHeightPeriod q branch amp p (p-2*x) Y) atTop
      (𝓝 (∫ p in a..b,((p:ℂ)^n*Complex.exp (-w*(p:ℂ)))*originalRadialPeriod q branch amp p (p-2*x))) := by
  let T : Ici (0:ℝ) := ⟨b-2*x,by change 0 ≤ b-2*x; linarith⟩
  obtain ⟨e,he0,he,hbound⟩ := original_finiteHeight_uniform_error q branch amp T
  have hw : Continuous (fun p : ℝ => (p:ℂ)^n*Complex.exp (-w*(p:ℂ))) := by fun_prop
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s:=Icc a b) hw.continuousOn
  let C' := max C 0
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hce : Tendsto (fun Y => C'*e Y) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.const_mul C'
  have hlim : TendstoUniformlyOn
      (fun (Y p : ℝ) => ((p:ℂ)^n*Complex.exp (-w*(p:ℂ)))*originalFiniteHeightPeriod q branch amp p (p-2*x) Y)
      (fun p : ℝ => ((p:ℂ)^n*Complex.exp (-w*(p:ℂ)))*originalRadialPeriod q branch amp p (p-2*x)) atTop (Icc a b) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [eventually_ge_atTop (4:ℝ),hce.eventually (gt_mem_nhds hε)] with Y hY hsmall
    intro p hp
    obtain ⟨hp',hr'⟩ := time_rectangle a b x p ha hx hp
    rw [dist_comm,dist_eq_norm,← mul_sub,norm_mul]
    exact (mul_le_mul ((hC p hp).trans (le_max_left _ _))
      (hbound Y hY p hp' (p-2*x) hr') (norm_nonneg _) hC0).trans_lt hsmall
  apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
  · filter_upwards [eventually_ge_atTop (4:ℝ)] with Y hY
    rw [uIcc_of_le hab]
    convert! hw.continuousOn.mul
      (originalFiniteHeightPeriod_time_continuousOn q branch amp a b x Y ha hab hx hY) using 1
  · simpa only [uIcc_of_le hab] using hlim

/-- The zeroth-moment compact cusp/time interchange for the original source. -/
theorem original_compact_time_restoration (q : XiZeroCopy) (branch : Bool) (amp w : ℂ)
    (a b x : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hx : x ≤ 0) :
    Tendsto (fun Y => ∫ p in a..b,Complex.exp (-w*(p:ℂ))*
      originalFiniteHeightPeriod q branch amp p (p-2*x) Y) atTop
      (𝓝 (∫ p in a..b,Complex.exp (-w*(p:ℂ))*originalRadialPeriod q branch amp p (p-2*x))) := by
  simpa only [pow_zero,one_mul] using
    original_compact_time_moment_restoration q branch amp w 0 a b x ha hab hx

/-- Every angular jet of the complete original source has arbitrary cusp
decay uniformly over bounded null targets and all horizontal positions.
The original onset lift is included in the same bound. -/
theorem original_remainder_jet_compact_rapid_bound (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (word : List (Fin 2)) (N : ℕ) (T : Ici (0:ℝ)) :
    ∃ D B : ℝ, 0 ≤ D ∧ 0 ≤ B ∧
      ∀ p∈Icc 0 T.val, ∀ r∈Icc 0 T.val, ∀ X k : ℝ, D ≤ k →
        ‖D4BMSquareCuspJets.coordinateJet word (D4BMOriginalCuspJets.remainder q branch amp p r) ![X,k]‖ ≤
          B*Real.exp ((N:ℝ)*(D-k)) := by
  obtain ⟨D,B,hD,hB,hresponse⟩ := responseRemainder_jet_uniform_bound q (physicalRate q branch) amp word N T
  obtain ⟨A,hA,hnative⟩ := nativeCuspJet_rapid_bound q (word.map Fin.succ) N
    ⟨D,by change 0 ≤ D;exact hD⟩
  obtain ⟨L,hL,hlift⟩ := lift_compact_bound (physicalRate q branch) amp T
  refine ⟨D,B+L*A,hD,by positivity,?_⟩
  intro p hp r hr X k hk
  have hn := hnative 0 X k le_rfl hD hk
  rw [D4BMOriginalCuspJets.original_remainder_jet]
  calc
    _ ≤ ‖D4BMSquareCuspJets.coordinateJet word
        (responseRemainder q (physicalRate q branch) amp p r) ![X,k]‖+
      ‖nullLift (physicalRate q branch) amp p r*
        nativeJet (word.map Fin.succ) (D4BMNativeAngularCurrent.nativeRemainder q) ![0,X,k]‖ := norm_add_le _ _
    _ ≤ B*Real.exp ((N:ℝ)*(D-k))+L*(A*Real.exp ((N:ℝ)*(D-k))) := by
      apply add_le_add (hresponse p hp r hr X k hk)
      rw [norm_mul]
      exact mul_le_mul (hlift p hp r hr) hn (norm_nonneg _) hL
    _ = _ := by ring

end RHTower.D4BMOriginalCausalPeriod

import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCircleEquation

/-!
The original causal scalar period is identified before temporal transformation.
The full cutoff circle kernel admits Fubini against the unchanged physical
reader on every finite null source rectangle. The source integral transports
all three original correction coefficients into their native radial responses;
restoration cancels them and retains the complete original onset lift.
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

end RHTower.D4BMOriginalCausalPeriod

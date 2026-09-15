import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalSourceTailCollar

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalSourceTailAdmission
open D4BMJointSource D4BMModularCore D4BMOriginalReaderCuspBounds D4BMOriginalAngularReaderBounds
open D4BMOriginalCausalPotential D4BMOriginalCausalPeriod D4BMOriginalCausalRestoration
open D4BMOriginalScalarRestoration D4BMGlobalAngularResponse D4BMOriginalBaseCircleJets
open D4BMOriginalSourceTailCollar D4BMJointWave D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false

private theorem original_joint_continuousAt (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (v : (ℝ×ℝ)×UpperHalfPlane) (hL : 0<v.1.1) (hp : 0<v.1.2) :
    ContinuousAt (fun t : (ℝ×ℝ)×UpperHalfPlane =>
      originalPotential q br amp t.1.2 (t.1.2+t.1.1) t.2.re (Real.log t.2.im)) v := by
  let F := fun t : (ℝ×ℝ)×UpperHalfPlane =>
    (![t.1.2,t.1.2+t.1.1,t.2.re,Real.log t.2.im]:Fin 4→ℝ)
  have hc : Continuous F := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_snd.comp continuous_fst
    · exact (continuous_snd.comp continuous_fst).add (continuous_fst.comp continuous_fst)
    · exact UpperHalfPlane.continuous_re.comp continuous_snd
    · exact (UpperHalfPlane.continuous_im.comp continuous_snd).log (fun t => t.2.im_pos.ne')
  have h := (D4BMOriginalSpacetimeRegularity.originalPotential_smooth q br amp (F v)
    hp (show v.1.2<v.1.2+v.1.1 by linarith)).continuousAt
  have hcomp := h.comp hc.continuousAt
  simpa only [F,Function.comp_def,Matrix.cons_val] using hcomp

private theorem lift_continuous (s amp : ℂ) : Continuous (radialLift s 0 amp 1) :=
  continuous_iff_continuousAt.mpr (fun x => (radialLift_hasDerivAt s 0 amp 1 x).continuousAt)

private theorem onset_continuous (s : ℂ) : Continuous (timeOnset (2*s)) :=
  continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt (2*s) p).continuousAt)

private theorem response_joint_continuous (nu s amp : ℂ) :
    Continuous (fun v : ℝ×ℝ => D4BMNativeResponse.radialResponse nu s amp
      ((v.2+(v.2+v.1))/2) ((v.2-(v.2+v.1))/2)) := by
  have h := (D4BMNativeResponse.radialResponse_continuous nu s amp).comp
    (show Continuous (fun v : ℝ×ℝ => ((v.2+(v.2+v.1))/2,(v.2-(v.2+v.1))/2)) by fun_prop)
  simpa only [Function.comp_def] using h

private theorem principal_coefficient_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) (i : Fin 3) :
    Continuous (fun v : ℝ×ℝ => D4BMOriginalCuspJets.coefficient q br amp v.2 (v.2+v.1) i) := by
  let s := physicalRate q br
  have hR := response_joint_continuous (-principalExponent q i) s amp
  have hA := lift_continuous s amp
  have hB := onset_continuous s
  have hL := (hA.comp (show Continuous (fun v : ℝ×ℝ => (v.2-(v.2+v.1))/2) by fun_prop)).mul
    (hB.comp continuous_snd)
  have h := (hR.const_mul (principalAmplitude q i)).add (hL.mul_const (principalAmplitude q i))
  simpa only [D4BMOriginalCuspJets.coefficient,D4BMNativeResponse.principalNullResponse,
    nullLift,Function.comp_def,Pi.add_def,Pi.mul_def,s] using h

private theorem reader_continuousAt (q : XiZeroCopy) (w : ℂ) (L : ℝ) (hL : 0<L) :
    ContinuousAt (reader q w) L := by
  have hx : -L/2<0 := by linarith
  have hc := (horizonCoordinate_hasDerivAt (-L/2)).continuousAt.comp_of_eq
    (show ContinuousAt (fun l : ℝ => -l/2) L by fun_prop) rfl
  have hn := (normalizable_derivatives_continued (w:=w) (chi:=physicalRadialFrequency q)
    (horizonCoordinate_interior (-L/2) hx)).1.continuousAt.comp_of_eq hc rfl
  have h := (show ContinuousAt (fun l : ℝ => Complex.exp (w*((-l/2:ℝ):ℂ))) L by fun_prop).mul hn
  exact h

/-- Joint admission comes from the original physical spacetime field and the
unchanged three principal channels, with no measurability assumption. -/
theorem tail_density_joint_continuousAt (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (v : (ℝ×ℝ)×UpperHalfPlane) (hL : 0<v.1.1) (hp : 0<v.1.2) :
    ContinuousAt (fun t : (ℝ×ℝ)×UpperHalfPlane => tailDensity q br amp w t.1.2 t.1.1 t.2) v := by
  have hP : Continuous (fun t : (ℝ×ℝ)×UpperHalfPlane =>
      ∑ i : Fin 3,D4BMOriginalCuspJets.coefficient q br amp t.1.2 (t.1.2+t.1.1) i*
        Complex.exp (principalExponent q i*(Real.log t.2.im:ℂ))) := by
    apply continuous_finsetSum
    intro i _
    exact ((principal_coefficient_continuous q br amp i).comp continuous_fst).mul
      (continuous_const.mul (Complex.continuous_ofReal.comp
        ((UpperHalfPlane.continuous_im.comp continuous_snd).log (fun t => t.2.im_pos.ne')))).cexp
  have hS := (original_joint_continuousAt q br amp v hL hp).sub hP.continuousAt
  have hn := (reader_continuousAt q w v.1.1 hL).comp
    (f:=fun t : (ℝ×ℝ)×UpperHalfPlane => t.1.1) (x:=v)
    (continuous_fst.comp continuous_fst).continuousAt
  have ht : ContinuousAt (fun t : (ℝ×ℝ)×UpperHalfPlane => Complex.exp (-w*(t.1.2:ℂ))) v := by fun_prop
  have hxy : Continuous (fun t : (ℝ×ℝ)×UpperHalfPlane => (![t.2.re,t.2.im]:Fin 2→ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact UpperHalfPlane.continuous_re.comp continuous_snd
    · exact UpperHalfPlane.continuous_im.comp continuous_snd
  have hg := (D4BMAngularSeries.cuspLeg_contDiffOn .scalar (physicalAngularParameter q)).continuousOn.comp_continuous
    hxy (fun t => t.2.im_pos)
  have h := ((ht.mul hn).mul hS).mul hg.continuousAt
  convert h using 1
  funext t
  simp only [tailDensity,sourceJet,baseOperator,D4BMOriginalCuspJets.remainder,
    D4BMOriginalCuspJets.principal,angularJet,Bool.false_eq_true,if_false,Matrix.cons_val,
    Real.exp_log t.2.im_pos,Pi.mul_apply,Pi.sub_apply,Function.comp_def,D4BMLiteralCusp.scalar]

def jointMeasure (L0 k : ℝ) : Measure ((ℝ×ℝ)×UpperHalfPlane) :=
  (volume.restrict (Ioi L0 ×ˢ Ioi (0:ℝ))).prod (measure.restrict (tailSet k))

private theorem joint_set_measurable (L0 k : ℝ) :
    MeasurableSet ((Ioi L0 ×ˢ Ioi (0:ℝ)) ×ˢ tailSet k) :=
  (measurableSet_Ioi.prod measurableSet_Ioi).prod
    (measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable)

private theorem tail_joint_measurable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (L0 k : ℝ) (hL0 : 0≤L0) :
    AEStronglyMeasurable (fun v : (ℝ×ℝ)×UpperHalfPlane => tailDensity q br amp w v.1.2 v.1.1 v.2)
      (jointMeasure L0 k) := by
  unfold jointMeasure
  rw [Measure.prod_restrict]
  apply ContinuousOn.aestronglyMeasurable _ (joint_set_measurable L0 k)
  intro v hv
  exact (tail_density_joint_continuousAt q br amp w v (hL0.trans_lt hv.1.1) hv.1.2).continuousWithinAt

/-- The complete leading scalar tail is jointly measurable in source time and
angular position, derived as the actual physical collar limit. -/
theorem horizon_joint_measurable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ L0 k : ℝ,0≤k →
      AEStronglyMeasurable (fun v : (ℝ×ℝ)×UpperHalfPlane => horizonTailDensity q br amp w v.1.2 v.2)
        (jointMeasure L0 k) := by
  obtain ⟨G,hG,hg⟩ := source_tail_density_error q br amp 0
  refine ⟨G,hG,?_⟩
  intro w hwi hw L0 k hk
  obtain ⟨C,hC,hc⟩ := hg w hwi hw
  have hm (r : ℝ) : AEStronglyMeasurable
      (fun v : (ℝ×ℝ)×UpperHalfPlane => tailDensity q br amp w v.1.2 (Real.exp r) v.2) (jointMeasure L0 k) := by
    unfold jointMeasure
    rw [Measure.prod_restrict]
    apply ContinuousOn.aestronglyMeasurable _ (joint_set_measurable L0 k)
    intro v hv
    have h := (tail_density_joint_continuousAt q br amp w ((Real.exp r,v.1.2),v.2) (Real.exp_pos r) hv.1.2).comp
      (f:=fun t : (ℝ×ℝ)×UpperHalfPlane => ((Real.exp r,t.1.2),t.2)) (x:=v)
      (show ContinuousAt (fun t : (ℝ×ℝ)×UpperHalfPlane => ((Real.exp r,t.1.2),t.2)) v by fun_prop)
    exact h.continuousWithinAt
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℝ) hm
  unfold jointMeasure
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (joint_set_measurable L0 k)] with v hv
  have hlim : Tendsto (fun L : ℝ => tailDensity q br amp w v.1.2 L v.2) atTop
      (𝓝 (horizonTailDensity q br amp w v.1.2 v.2)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have ht : Tendsto (fun L : ℝ => C*Real.exp (-L)*Real.exp (-v.1.2)) atTop (𝓝 0) := by
      simpa only [mul_zero,zero_mul] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C).mul_const (Real.exp (-v.1.2))
    apply squeeze_zero' (Eventually.of_forall (fun L => norm_nonneg _)) _ ht
    filter_upwards [hc] with L hL
    simpa only [Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero,mul_one] using
      hL v.1.2 k hv.1.2 hk v.2 hv.2
  exact hlim.comp Real.tendsto_exp_atTop

/-- One admitted product remainder for the unbounded physical time/horizon
collar and the whole original cusp tail. This justifies angular/time/radial
Fubini; a norm estimate alone would not supply this statement. -/
theorem joint_tail_error_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ L0 : ℝ,0<L0 ∧ ∀ k : ℝ,0≤k →
      Integrable (fun v : (ℝ×ℝ)×UpperHalfPlane =>
        tailDensity q br amp w v.1.2 v.1.1 v.2-horizonTailDensity q br amp w v.1.2 v.2) (jointMeasure L0 k) := by
  obtain ⟨G1,hG1,h1⟩ := source_tail_density_error q br amp 0
  obtain ⟨G2,_,h2⟩ := horizon_joint_measurable q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1≤w.re := by linarith [le_max_right G1 G2]
  obtain ⟨C,hC,hc⟩ := h1 w hwi hw1
  obtain ⟨L1,hL1⟩ := eventually_atTop.mp hc
  let L0 := max L1 1
  have hL0 : 0<L0 := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  refine ⟨L0,hL0,?_⟩
  intro k hk
  have hm : AEStronglyMeasurable (fun v : (ℝ×ℝ)×UpperHalfPlane =>
      tailDensity q br amp w v.1.2 v.1.1 v.2-horizonTailDensity q br amp w v.1.2 v.2) (jointMeasure L0 k) := by
    simpa only [Pi.sub_def] using
      (tail_joint_measurable q br amp w L0 k hL0.le).sub (h2 w hwi hw2 L0 k hk)
  have hL : IntegrableOn (fun L : ℝ => Real.exp (-L)) (Ioi L0) volume := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a:=(-1:ℝ)) (by norm_num) L0
  have hp : IntegrableOn (fun p : ℝ => Real.exp (-p)) (Ioi (0:ℝ)) volume := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a:=(-1:ℝ)) (by norm_num) 0
  have hLP : Integrable (fun v : ℝ×ℝ => C*(Real.exp (-v.1)*Real.exp (-v.2)))
      (volume.restrict (Ioi L0 ×ˢ Ioi (0:ℝ))) := by
    have h := (hL.mul_prod hp).const_mul C
    simpa only [IntegrableOn,Measure.prod_restrict,Measure.volume_eq_prod] using h
  have hi : Integrable (fun v : (ℝ×ℝ)×UpperHalfPlane => C*(Real.exp (-v.1.1)*Real.exp (-v.1.2)))
      (jointMeasure L0 k) := by
    have h := hLP.mul_prod (integrable_const (1:ℝ) : Integrable (fun _ : UpperHalfPlane => (1:ℝ))
      (measure.restrict (tailSet k)))
    simpa only [mul_one,jointMeasure] using h
  apply hi.mono' hm
  unfold jointMeasure
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (joint_set_measurable L0 k)] with v hv
  have h := hL1 v.1.1 ((le_max_left L1 1).trans hv.1.1.le) v.1.2 k hv.1.2 hk v.2 hv.2
  simpa only [Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero,mul_one,mul_assoc] using h

/-- The original scalar-period discrepancy minus its retained horizon trace
is absolutely integrable on the unbounded time/horizon product. -/
theorem original_period_error_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ L0 : ℝ,0<L0 ∧ ∀ k : ℝ,0≤k → 4≤Real.exp k →
      IntegrableOn (fun v : ℝ×ℝ => originalPeriodError q br amp w v.2 v.1 k-
        horizonPeriodError q br amp w v.2 k) (Ioi L0 ×ˢ Ioi (0:ℝ)) volume := by
  obtain ⟨G1,hG1,h1⟩ := joint_tail_error_integrable q br amp
  obtain ⟨G2,_,h2⟩ := horizon_tail_integrable q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1≤w.re := by linarith [le_max_right G1 G2]
  obtain ⟨L0,hL0,hL⟩ := h1 w hwi hw1
  refine ⟨L0,hL0,?_⟩
  intro k hk hk4
  have h := (hL k hk).integral_prod_left.neg
  apply h.congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with v hv
  have hp : 0<v.2 := hv.2
  have hvL : 0<v.1 := hL0.trans hv.1
  simp only [Pi.neg_apply]
  rw [original_period_error_tail q br amp w v.2 v.1 k hp hvL hk4,horizonPeriodError,
    integral_sub (tail_density_integrable q br amp w v.2 v.1 k hp hvL hk4) (h2 w hwi hw2 v.2 k hp hk hk4)]
  ring

end
end RHTower.D4BMOriginalSourceTailAdmission

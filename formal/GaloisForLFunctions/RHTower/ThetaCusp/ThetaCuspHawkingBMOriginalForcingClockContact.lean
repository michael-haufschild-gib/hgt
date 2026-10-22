import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalFullStaticCollar

open Set Filter Topology MeasureTheory Complex
namespace RHTower.D4BMOriginalForcingClockContact
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMLaplaceRadial D4BMModularCore
open D4BMOriginalCanonicalHorizon D4BMOriginalMetricHorizon
open D4BMOriginalCornerForcing D4BMOriginalReaderCuspBounds
open D4BMOriginalCanonicalForcingMatch D4BMOriginalStaticForcingTriangle
open D4BMOriginalStaticForcingPrimitive D4BMOriginalForcingJointHorizon
noncomputable section
set_option autoImplicit false

/-- The forcing logarithm has exactly the original horizon coefficient, with
the sign and factor one-half fixed by the tortoise-coordinate Jacobian. -/
theorem forcing_logarithm_coefficient (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) :
    oppositeValue q br amp K w=
      -(horizonReader q w*forcingProfile (physicalRate q br) amp 1 K 1)/2 := by
  have hg : ContinuousAt (gaussProfile q (-w)) 0 := by
    exact (gaussFactor_derivatives_continued (w:= -w) (chi:=physicalRadialFrequency q)
      (z:=0) false (by simp)).1.comp_ofReal.continuousAt
  have hs := (sourceRemainder_continuous (physicalRate q br) w amp 1 K 1).continuousAt (x:=0)
  have hc : ContinuousAt (oppositeProfile q br amp K w) 0 :=
    (hg.mul hs).const_mul (oppositeCoefficient q w)
  have he : oppositeValue q br amp K w=oppositeProfile q br amp K w 0 :=
    (hc.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
  rw [he]
  simp only [oppositeProfile,oppositeCoefficient,gaussProfile,Complex.ofReal_zero,
    gaussFactor_zero,one_mul,remainderProfile,sourceRemainder,sub_zero,Real.sqrt_one,
    one_add_one_eq_two,mul_one,forcingProfile,Complex.ofReal_one,one_pow,horizonReader]
  have hpow : power (2*physicalRate q br-w) 2=
      power (-w) 2*power (2*physicalRate q br) 2 := by
    unfold power
    rw [show 2*physicalRate q br-w=(-w)+(2*physicalRate q br) by ring]
    exact Complex.cpow_add (-w) (2*physicalRate q br) (by norm_num)
  rw [hpow]
  ring

/-- The opposite-branch horizon coefficient of each original forcing kernel. -/
def horizonForcing (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) : ℂ :=
  horizonReader q w*forcingProfile (physicalRate q br) amp 1 K 1

/-- Removing its fixed linear horizon term leaves the canonical counterterm
bounded on the entire exterior. This is the convergence-half-plane contact
estimate, not a change of the canonical coefficient family. -/
theorem forcing_counterterm_linear_bound (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    (hw : 0 ≤ w.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, x < 0 →
      ‖canonicalForcingCounterterm q br amp K w (horizonCoordinate x)+
        horizonForcing q br amp K w*(x:ℂ)‖ ≤ B := by
  let c := incomingValue q br amp K w
  let d := incomingSlope q br amp K w
  let e := oppositeValue q br amp K w
  let B := ‖c‖/‖w‖+‖d‖/‖w+1‖+2*‖e‖*Real.log 2
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨B,by dsimp [B];positivity,?_⟩
  intro x hx
  have hz := horizonCoordinate_interior x hx
  have hu := radialUnit_bounds x hx
  have hlog : Real.log (horizonCoordinate x)=2*x+2*Real.log (1+radialUnit x) := by
    rw [horizonCoordinate_factor,Real.log_pow,
      Real.log_mul (Real.exp_ne_zero _) (radialUnit_add_one_pos x).ne',Real.log_exp]
    ring
  have hl0 : 0 ≤ Real.log (1+radialUnit x) := Real.log_nonneg (by linarith [hu.1])
  have hlb : Real.log (1+radialUnit x) ≤ Real.log 2 :=
    Real.log_le_log (radialUnit_add_one_pos x) (by linarith [hu.2])
  have hp (v : ℂ) (hv : 0 ≤ v.re) : ‖(horizonCoordinate x:ℂ)^v‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hz.1]
    exact Real.rpow_le_one hz.1.le hz.2.le hv
  have hc : horizonForcing q br amp K w= -2*e := by
    dsimp [horizonForcing,e]
    rw [forcing_logarithm_coefficient]
    ring
  have heq : canonicalForcingCounterterm q br amp K w (horizonCoordinate x)+
      horizonForcing q br amp K w*(x:ℂ)=
        c*(horizonCoordinate x:ℂ)^w/w+d*(horizonCoordinate x:ℂ)^(w+1)/(w+1)+
          2*e*(Real.log (1+radialUnit x):ℂ) := by
    rw [canonicalForcingCounterterm,D4BMOriginalMetricRadial.forcingCounterterm,hlog,hc]
    push_cast
    dsimp only [c,d,e]
    ring
  rw [heq]
  apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
  have h0 : ‖c*(horizonCoordinate x:ℂ)^w/w‖ ≤ ‖c‖/‖w‖ := by
    rw [norm_div,norm_mul]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg c) (hp w hw)) (norm_nonneg _)
  have h1 : ‖d*(horizonCoordinate x:ℂ)^(w+1)/(w+1)‖ ≤ ‖d‖/‖w+1‖ := by
    rw [norm_div,norm_mul]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (norm_nonneg d) (hp (w+1) (by simpa using (show 0 ≤ w.re+1 by linarith))))
      (norm_nonneg _)
  have h2 : ‖2*e*(Real.log (1+radialUnit x):ℂ)‖ ≤ 2*‖e‖*Real.log 2 := by
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hl0]
    norm_num only [norm_ofNat]
    exact mul_le_mul_of_nonneg_left hlb (by positivity)
  exact add_le_add (add_le_add h0 h1) h2

/-- The actual two finite-height weights, applied to the original horizon kernels. -/
def horizonForcingDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (k : ℝ) : ℂ :=
  (firstWeight q (Real.exp k)-physicalSelfSourceCoefficient q)*
    horizonForcing q br amp (D4BMOriginalForcingJointHorizon.gradient q br) w+
  secondWeight q (Real.exp k)*horizonForcing q br amp (D4BMOriginalForcingJointHorizon.gradient q br+1) w

theorem horizon_forcing_difference_tendsto (q : XiZeroCopy) (br : Bool) (amp w : ℂ) :
    Tendsto (horizonForcingDifference q br amp w) atTop (𝓝 0) := by
  change Tendsto (fun k : ℝ =>
    (firstWeight q (Real.exp k)-physicalSelfSourceCoefficient q)*
      horizonForcing q br amp (D4BMOriginalForcingJointHorizon.gradient q br) w+
    secondWeight q (Real.exp k)*
      horizonForcing q br amp (D4BMOriginalForcingJointHorizon.gradient q br+1) w)
    atTop (𝓝 (0:ℂ))
  have h := (((weights_limit q).1.sub_const (physicalSelfSourceCoefficient q)).mul_const
    (horizonForcing q br amp (D4BMOriginalForcingJointHorizon.gradient q br) w)).add
      ((weights_limit q).2.mul_const (horizonForcing q br amp (D4BMOriginalForcingJointHorizon.gradient q br+1) w))
  simpa only [sub_self,zero_mul,zero_add] using h

/-- The discrepancy's canonical counterterm agrees with its literal horizon
linear term up to one uniformly cusp-small bounded function. -/
theorem forcing_counterterm_uniform_linear (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 0 ≤ w.re) :
    ∃ η : ℝ→ℝ, (∀ k,0 ≤ η k) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ k x : ℝ,x < 0 → ‖forcingCountertermDifference q br amp w k x+
        horizonForcingDifference q br amp w k*(x:ℂ)‖ ≤ η k := by
  obtain ⟨B,hB,hb⟩ := forcing_counterterm_linear_bound q br amp (D4BMOriginalForcingJointHorizon.gradient q br) w hw
  obtain ⟨D,hD,hd⟩ := forcing_counterterm_linear_bound q br amp (D4BMOriginalForcingJointHorizon.gradient q br+1) w hw
  let η := fun k : ℝ => ‖firstWeight q (Real.exp k)-physicalSelfSourceCoefficient q‖*B+
    ‖secondWeight q (Real.exp k)‖*D
  refine ⟨η,fun k => by dsimp [η];positivity,?_,?_⟩
  · have ht := (((weights_limit q).1.sub_const (physicalSelfSourceCoefficient q)).norm.mul_const B).add
      ((weights_limit q).2.norm.mul_const D)
    simpa only [sub_self,norm_zero,zero_mul,zero_add] using ht
  · intro k x hx
    have he : forcingCountertermDifference q br amp w k x+horizonForcingDifference q br amp w k*(x:ℂ)=
        (firstWeight q (Real.exp k)-physicalSelfSourceCoefficient q)*
          (canonicalForcingCounterterm q br amp (D4BMOriginalForcingJointHorizon.gradient q br) w (horizonCoordinate x)+
            horizonForcing q br amp (D4BMOriginalForcingJointHorizon.gradient q br) w*(x:ℂ))+
        secondWeight q (Real.exp k)*
          (canonicalForcingCounterterm q br amp (D4BMOriginalForcingJointHorizon.gradient q br+1) w (horizonCoordinate x)+
            horizonForcing q br amp (D4BMOriginalForcingJointHorizon.gradient q br+1) w*(x:ℂ)) := by
      unfold forcingCountertermDifference horizonForcingDifference
      ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hb x hx) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hd x hx) (norm_nonneg _))

/-- The forcing's literal horizon contribution on the original causal
triangle: its unchanged horizon density times the available radial length. -/
def horizonTriangle (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a ξ b T k : ℝ) : ℂ :=
  ∫ p in a..max a (T+b),onsetDensity q br w p*
    (horizonForcingDifference q br amp w k*((b-max ξ (p-T):ℝ):ℂ))

/-- The canonical moving counterterm and the physical horizon triangle
have uniformly vanishing cusp discrepancy. The interface's finite term is
retained in the bound, so no normalization at the upper endpoint is imposed. -/
theorem static_counterterm_horizon_matching (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 0 ≤ w.re) (b : ℝ) (hb : b < 0) :
    ∃ η : ℝ→ℝ, (∀ k,0 ≤ η k) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ a ξ T k : ℝ,0 ≤ a → ξ ≤ b →
        ‖staticForcingCounterterm q br amp w a ξ b T k-
          horizonTriangle q br amp w a ξ b T k‖ ≤ η k := by
  obtain ⟨η,hη,hηlim,hbound⟩ := forcing_counterterm_uniform_linear q br amp w hw
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  have hi : IntegrableOn (onsetDensity q br w) (Ioi (0:ℝ)) :=
    timeOnset_integrable (2*physicalRate q br) w (by linarith)
  have hin : IntegrableOn (fun p => ‖onsetDensity q br w p‖) (Ioi (0:ℝ)) := hi.norm
  let M := ∫ p in Ioi (0:ℝ),‖onsetDensity q br w p‖
  have hM : 0 ≤ M := integral_nonneg (fun _ => norm_nonneg _)
  let δ := fun k : ℝ => η k+‖horizonForcingDifference q br amp w k‖*‖(b:ℂ)‖
  have hδ (k : ℝ) : 0 ≤ δ k := add_nonneg (hη k) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [norm_zero,zero_mul,add_zero] using
      hηlim.add ((horizon_forcing_difference_tendsto q br amp w).norm.mul_const ‖(b:ℂ)‖)
  refine ⟨fun k => M*δ k,fun k => mul_nonneg hM (hδ k),?_,?_⟩
  · simpa only [mul_zero] using hδlim.const_mul M
  · intro a ξ T k ha hξ
    by_cases hT : T+b ≤ a
    · simp only [staticForcingCounterterm,horizonTriangle,max_eq_left hT,
        intervalIntegral.integral_same,sub_self,norm_zero]
      exact mul_nonneg hM (hδ k)
    · have hau : a ≤ T+b := (lt_of_not_ge hT).le
      have hf : Continuous (onsetDensity q br w) := by
        have ho : Continuous (timeOnset (2*physicalRate q br)) :=
          continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt _ p).continuousAt)
        unfold onsetDensity
        fun_prop
      have hmap : MapsTo (fun p : ℝ => max ξ (p-T)) (Icc a (T+b)) (Iio (0:ℝ)) := by
        intro p hp
        exact (max_le hξ (by linarith [hp.2])).trans_lt hb
      have hc := (forcing_counterterm_difference_continuous q br amp w k).comp
        (show ContinuousOn (fun p : ℝ => max ξ (p-T)) (Icc a (T+b)) by fun_prop) hmap
      have hict : IntervalIntegrable (fun p => onsetDensity q br w p*
          forcingCountertermDifference q br amp w k (max ξ (p-T))) volume a (T+b) :=
        (hf.continuousOn.mul hc).intervalIntegrable_of_Icc hau
      have hiH : IntervalIntegrable (fun p => onsetDensity q br w p*
          (horizonForcingDifference q br amp w k*((b-max ξ (p-T):ℝ):ℂ))) volume a (T+b) :=
        (hf.mul (show Continuous (fun p : ℝ =>
          horizonForcingDifference q br amp w k*((b-max ξ (p-T):ℝ):ℂ)) by fun_prop)).intervalIntegrable _ _
      unfold staticForcingCounterterm horizonTriangle
      rw [max_eq_right hau,← intervalIntegral.integral_sub hict hiH]
      have hfg : IntervalIntegrable (fun p => ‖onsetDensity q br w p‖*δ k) volume a (T+b) := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hau]
        exact (hin.mono_set (fun p hp => ha.trans_lt hp.1)).mul_const _
      have hpbound (p : ℝ) (hp : p ∈ Ioc a (T+b)) :
          ‖onsetDensity q br w p*forcingCountertermDifference q br amp w k (max ξ (p-T))-
            onsetDensity q br w p*(horizonForcingDifference q br amp w k*((b-max ξ (p-T):ℝ):ℂ))‖ ≤
              ‖onsetDensity q br w p‖*δ k := by
        have hx : max ξ (p-T) < 0 := (max_le hξ (by linarith [hp.2])).trans_lt hb
        have halg : forcingCountertermDifference q br amp w k (max ξ (p-T))-
            horizonForcingDifference q br amp w k*((b-max ξ (p-T):ℝ):ℂ)=
          (forcingCountertermDifference q br amp w k (max ξ (p-T))+
            horizonForcingDifference q br amp w k*(max ξ (p-T):ℝ))-
              horizonForcingDifference q br amp w k*(b:ℂ) := by push_cast;ring
        rw [← mul_sub,halg,norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by rw [norm_mul];exact add_le_add (hbound k _ hx) le_rfl)
      apply (intervalIntegral.norm_integral_le_of_norm_le hau
        (Eventually.of_forall hpbound) hfg).trans
      rw [intervalIntegral.integral_mul_const]
      apply mul_le_mul_of_nonneg_right _ (hδ k)
      rw [intervalIntegral.integral_of_le hau]
      exact setIntegral_mono_set hi.norm (Eventually.of_forall (fun _ => norm_nonneg _))
        (Eventually.of_forall (fun p hp => ha.trans_lt hp.1))

/-- The actual moving forcing cut matches its literal horizon triangle under
independent cusp, time and horizon removal, with all contacts derived from
the original canonical coefficient family. -/
theorem static_forcing_horizon_matching (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hwi : w.im ≠ 0) (hw : 0 ≤ w.re) :
    ∃ B : ℝ,0 < B ∧ B ≤ 1/2 ∧ ∀ b : ℝ,b < 0 → horizonCoordinate b ≤ B →
      ∃ η : ℝ→ℝ,(∀ k,0 ≤ η k) ∧ Tendsto η atTop (𝓝 0) ∧
        ∀ a ξ T k : ℝ,0 ≤ a → ξ ≤ b →
          ‖staticForcingCut q br amp w a ξ b T k-horizonTriangle q br amp w a ξ b T k‖ ≤ η k := by
  obtain ⟨B,hB,hBh,h⟩ := D4BMOriginalStaticForcingRestoration.static_forcing_uniform_restoration
    q br amp w hwi (by linarith)
  refine ⟨B,hB,hBh,?_⟩
  intro b hb hbB
  obtain ⟨η,hη,hηlim,hηbound⟩ := h b hb hbB
  obtain ⟨δ,hδ,hδlim,hδbound⟩ := static_counterterm_horizon_matching q br amp w hw b hb
  refine ⟨fun k => η k+δ k,fun k => add_nonneg (hη k) (hδ k),?_,?_⟩
  · simpa only [add_zero] using hηlim.add hδlim
  · intro a ξ T k ha hξ
    exact (norm_sub_le_norm_sub_add_norm_sub _
      (staticForcingCounterterm q br amp w a ξ b T k) _).trans
        (add_le_add (hηbound a ξ T k ha hξ) (hδbound a ξ T k ha hξ))

/-- The complete original moving metric discrepancy after its actual
source/boundary mass and literal forcing horizon triangle are removed. -/
def physicalStaticDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a A B T k : ℝ) : ℂ :=
  (∫ L in A..B,D4BMOriginalFullMetricCollar.metricDifference q br amp w a (max a (T-L/2)) L k)/2-
    (max a (T-A/2)-max a (T-B/2))•D4BMOriginalStaticTracePrimitive.traceMass q br amp w k a-
    D4BMLeftModeRadialEquation.eigenvalue q*w*horizonTriangle q br amp w a (-B/2) (-A/2) T k

/-- Full finite-cusp moving metric restoration with its physical horizon
contacts. The canonical forcing subtraction is proved to give this same
contact, uniformly over arbitrary onset, terminal and horizon cutoffs. -/
theorem full_static_horizon_restoration (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0 ≤ G ∧ ∀ w : ℂ,w.im ≠ 0 → G+1 ≤ w.re →
      ∃ A0 : ℝ,0 < A0 ∧ ∀ A : ℝ,A0 ≤ A →
        ∃ η : ℝ→ℝ,(∀ k,0 ≤ η k) ∧ Tendsto η atTop (𝓝 0) ∧
          ∀ a B T k : ℝ,0 < a → A ≤ B → 0 ≤ k → 4 ≤ Real.exp k →
            IntervalIntegrable (fun L => D4BMOriginalFullMetricCollar.metricDifference q br amp w
              a (max a (T-L/2)) L k) volume A B ∧
            ‖physicalStaticDifference q br amp w a A B T k‖ ≤ η k := by
  obtain ⟨G,hG,h⟩ := D4BMOriginalFullStaticCollar.full_static_metric_collar_restoration q br amp
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨A0,hA0,hA⟩ := h w hwi hw
  refine ⟨A0,hA0,?_⟩
  intro A hAA
  obtain ⟨η,hη,hηlim,hηbound⟩ := hA A hAA
  obtain ⟨δ,hδ,hδlim,hδbound⟩ := static_counterterm_horizon_matching q br amp w
    (by linarith) (-A/2) (by linarith)
  let m := D4BMLeftModeRadialEquation.eigenvalue q*w
  refine ⟨fun k => η k+‖m‖*δ k,fun k => add_nonneg (hη k) (mul_nonneg (norm_nonneg _) (hδ k)),?_,?_⟩
  · simpa only [mul_zero,add_zero] using hηlim.add (hδlim.const_mul ‖m‖)
  · intro a B T k ha hAB hk hk4
    obtain ⟨hi,hb⟩ := hηbound a B T k ha hAB hk hk4
    refine ⟨hi,?_⟩
    have he : physicalStaticDifference q br amp w a A B T k=
        D4BMOriginalFullStaticCollar.fullStaticDifference q br amp w a A B T k+
          m*(staticForcingCounterterm q br amp w a (-B/2) (-A/2) T k-
            horizonTriangle q br amp w a (-B/2) (-A/2) T k) := by
      unfold physicalStaticDifference D4BMOriginalFullStaticCollar.fullStaticDifference
      dsimp only [m]
      ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    exact add_le_add hb (mul_le_mul_of_nonneg_left
      (hδbound a (-B/2) T k ha.le (by linarith)) (norm_nonneg _))

end
end RHTower.D4BMOriginalForcingClockContact

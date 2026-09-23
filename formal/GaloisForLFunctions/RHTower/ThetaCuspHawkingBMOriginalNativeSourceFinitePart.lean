import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCanonicalMetricAction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalPhysicalSourceAction

open Set Filter Topology MeasureTheory Metric
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial D4BMModularCore D4BMJointSource GaloisForLFunctions.HTGeometry
open D4BMOriginalMetricHorizon D4BMOriginalCanonicalHorizon D4BMOriginalCanonicalRestoration D4BMOriginalCornerForcing
noncomputable section
set_option autoImplicit false

/-- The original forcing pullback is the bare literal source overlap, with
 its original sign and radial Jacobian. -/
theorem nativeForcing_pullback_eq_bare_source (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    pullback q br amp K w z=-(normalizable w (physicalRadialFrequency q) z*
      sourceProfile (physicalRate q br) w amp 1 K 1 z/(z:ℂ)) := by
  have hu := radialUnit_eq_sqrt (tortoiseOf z) (tortoiseOf_neg hz)
  rw [horizonCoordinate_tortoiseOf hz] at hu
  have hr : (Real.sqrt (1-z):ℂ)^(2 : ℕ)=1-(z:ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hz.2.le)
  have hz0 : (z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.1.ne'
  have hr0 : (Real.sqrt (1-z):ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (sub_pos.mpr hz.2)).ne'
  rw [sourceProfile_tortoiseFactor _ _ _ _ _ _ hz]
  dsimp only [pullback,forcingKernel]
  rw [horizonCoordinate_tortoiseOf hz,hu]
  simp only [forcingProfile,sourceRemainder,sub_zero,mul_one,hr]
  field_simp [hz0,hr0]

theorem nativeForcing_pullback_continuousOn (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) :
    ContinuousOn (pullback q br amp K w) (Ioo (0:ℝ) 1) := by
  intro z hz
  have hn := (normalizable_derivatives_continued (w:=w) (chi:=physicalRadialFrequency q) hz).1.continuousAt
  have hp : ContinuousAt (sourceProfile (physicalRate q br) w amp 1 K 1) z :=
    ((power_derivatives (w/2) hz.1).1.continuousAt).mul
      (sourceRemainder_continuous (physicalRate q br) w amp 1 K 1).continuousAt
  have h : ContinuousWithinAt (fun t : ℝ => -(normalizable w (physicalRadialFrequency q) t*
      sourceProfile (physicalRate q br) w amp 1 K 1 t/(t:ℂ))) (Ioo (0:ℝ) 1) z :=
    ((hn.mul hp).div Complex.continuous_ofReal.continuousAt
    (Complex.ofReal_ne_zero.mpr hz.1.ne')).neg.continuousWithinAt
  exact h.congr (fun t ht => nativeForcing_pullback_eq_bare_source q br amp K w ht)
    (nativeForcing_pullback_eq_bare_source q br amp K w hz)

theorem nativeForcing_pullback_frequency_entire (q : XiZeroCopy) (br : Bool) (amp K : ℂ)
    {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) : Differentiable ℂ (fun w => pullback q br amp K w z) := by
  have h := (((normalizable_frequency_entire (physicalRadialFrequency q) hz).mul
    (sourceProfile_frequency_entire (physicalRate q br) amp 1 K 1 hz.1)).div_const (z:ℂ)).neg
  have heq : (fun w => pullback q br amp K w z)=(fun w => -(normalizable w (physicalRadialFrequency q) z*
      sourceProfile (physicalRate q br) w amp 1 K 1 z/(z:ℂ))) :=
    funext (fun w => nativeForcing_pullback_eq_bare_source q br amp K w hz)
  rw [heq]
  exact h

/-- A common bound for the actual forcing through the outer endpoint. -/
theorem nativeForcing_outer_uniform_bound (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    {b : ℝ} (hb : 0<b) (hb1 : b<1) :
    ∃ C : ℝ,0≤C ∧ ∀ u∈ball w 1,∀ z∈Ioo b 1,‖pullback q br amp K u z‖≤C := by
  obtain ⟨C,hC,hB⟩ := outerSource_uniform_bound (physicalRate q br) (physicalRadialFrequency q) amp 1 K w hb hb1
  refine ⟨C/b,div_nonneg hC hb.le,?_⟩
  intro u hu z hz
  have hz0 := hb.trans hz.1
  rw [nativeForcing_pullback_eq_bare_source q br amp K u ⟨hz0,hz.2⟩,
    norm_neg,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz0]
  exact (div_le_div_of_nonneg_right (hB u hu z ⟨hz.1.le,hz.2.le⟩) hz0.le).trans
    (div_le_div_of_nonneg_left hC hb hz.1.le)

/-- The admitted native forcing outside an arbitrary interior interface. -/
def nativeForcingOuterIntegral (q : XiZeroCopy) (br : Bool) (amp K : ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  ∫ z in Ioo b (1:ℝ),pullback q br amp K w z

theorem nativeForcing_outer_integrable (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    {b : ℝ} (hb : 0<b) (hb1 : b<1) : IntegrableOn (pullback q br amp K w) (Ioo b (1:ℝ)) := by
  obtain ⟨C,_,hB⟩ := nativeForcing_outer_uniform_bound q br amp K w hb hb1
  have hi : IntegrableOn (fun _ : ℝ => C) (Ioo b (1:ℝ)) := integrableOn_const (by simp)
  refine hi.mono' ?_ ?_
  · exact ((nativeForcing_pullback_continuousOn q br amp K w).mono
      (fun _ hz => ⟨hb.trans hz.1,hz.2⟩)).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact hB w (mem_ball_self (by norm_num)) z hz

theorem nativeForcingOuterIntegral_entire (q : XiZeroCopy) (br : Bool) (amp K : ℂ)
    {b : ℝ} (hb : 0<b) (hb1 : b<1) : Differentiable ℂ (nativeForcingOuterIntegral q br amp K b) := by
  intro w
  obtain ⟨C,_,hB⟩ := nativeForcing_outer_uniform_bound q br amp K w hb hb1
  let F : ℂ→ℝ→ℂ := fun u => (Ioo b (1:ℝ)).indicator (pullback q br amp K u)
  let bound : ℝ→ℝ := (Ioo b (1:ℝ)).indicator (fun _ => C)
  have hm (u : ℂ) (_hu : u∈ball w 1) : AEStronglyMeasurable (F u) volume := by
    apply (aestronglyMeasurable_indicator_iff measurableSet_Ioo).mpr
    exact ((nativeForcing_pullback_continuousOn q br amp K u).mono
      (fun _ hz => ⟨hb.trans hz.1,hz.2⟩)).aestronglyMeasurable measurableSet_Ioo
  have hd (z : ℝ) : DifferentiableOn ℂ (fun u => F u z) (ball w 1) := by
    intro u hu
    by_cases hz : z∈Ioo b (1:ℝ)
    · simp only [F,indicator_of_mem hz]
      exact (nativeForcing_pullback_frequency_entire q br amp K ⟨hb.trans hz.1,hz.2⟩ u).differentiableWithinAt
    · simp only [F,indicator_of_notMem hz]
      fun_prop
  have hbound (z : ℝ) (u : ℂ) (hu : u∈ball w 1) : ‖F u z‖≤bound z := by
    by_cases hz : z∈Ioo b (1:ℝ)
    · simpa only [F,bound,indicator_of_mem hz] using hB u hu z hz
    · simp only [F,bound,indicator_of_notMem hz,norm_zero,le_refl]
  have hi : Integrable bound volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp))
  have h := differentiableAt_integral_of_cauchy_dominated (by norm_num : (0:ℝ)<1) hm hd hbound hi
  simpa only [F,nativeForcingOuterIntegral,integral_indicator measurableSet_Ioo] using! h

/-- The literal full native forcing cutoff uses the source's canonical
 incoming value, incoming slope and opposite value. -/
def nativeForcingSourceCutoff (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) (e : ℝ) : ℂ :=
  (∫ z in e..(1:ℝ),pullback q br amp K w z)-
    incomingValue q br amp K w*(e:ℂ)^w/w-
    incomingSlope q br amp K w*(e:ℂ)^(w+1)/(w+1)-
    oppositeValue q br amp K w*(Real.log e:ℂ)

/-- One source value, defined by the actual cutoff independently of any interface. -/
def nativeForcingSourceFinitePart (q : XiZeroCopy) (br : Bool) (amp K w : ℂ) : ℂ :=
  limUnder (𝓝[>] (0:ℝ)) (nativeForcingSourceCutoff q br amp K w)

theorem nativeForcingSourceCutoff_split (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    {e b : ℝ} (he : 0<e) (heb : e≤b) (hb1 : b<1) :
    nativeForcingSourceCutoff q br amp K w e=
      ((∫ z in e..b,pullback q br amp K w z)-
        incomingValue q br amp K w*(e:ℂ)^w/w-
        incomingSlope q br amp K w*(e:ℂ)^(w+1)/(w+1)-
        oppositeValue q br amp K w*(Real.log e:ℂ))+nativeForcingOuterIntegral q br amp K b w := by
  have hI : IntervalIntegrable (pullback q br amp K w) volume e b := by
    apply ContinuousOn.intervalIntegrable
    apply (nativeForcing_pullback_continuousOn q br amp K w).mono
    rw [uIcc_of_le heb]
    exact fun z hz => ⟨he.trans_le hz.1,hz.2.trans_lt hb1⟩
  have hO : IntervalIntegrable (pullback q br amp K w) volume b 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hb1.le).mpr
      (nativeForcing_outer_integrable q br amp K w (he.trans_le heb) hb1)
  have heq := intervalIntegral.integral_add_adjacent_intervals hI hO
  rw [intervalIntegral.integral_of_le hb1.le,integral_Ioc_eq_integral_Ioo] at heq
  rw [nativeForcingSourceCutoff,← heq,nativeForcingOuterIntegral]
  ring

/-- The original two-branch forcing restoration glues to the whole source
 cutoff and supplies its local analytic representatives. -/
theorem nativeForcingSource_local_data (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) :
    ∃ R B : ℝ,0<R ∧ 0<B ∧ B≤1/2 ∧ ∀ b : ℝ,0<b → b≤B →
      AnalyticAt ℂ (fun u => horizonFinitePart q br amp K
        (incomingValue q br amp K) (incomingSlope q br amp K) (oppositeValue q br amp K) b u+
        nativeForcingOuterIntegral q br amp K b u) w ∧
      ∀ u∈ball w R,Tendsto (nativeForcingSourceCutoff q br amp K u) (𝓝[>] (0:ℝ))
        (𝓝 (horizonFinitePart q br amp K
          (incomingValue q br amp K) (incomingSlope q br amp K) (oppositeValue q br amp K) b u+
          nativeForcingOuterIntegral q br amp K b u)) := by
  obtain ⟨R,B,hR,hB,hBh,h⟩ := canonical_horizon_restoration q br amp K w hw hwr
  refine ⟨R,B,hR,hB,hBh,?_⟩
  intro b hb hbB
  have hb1 : b<1 := by linarith
  refine ⟨((h b hb hbB).1).add ((nativeForcingOuterIntegral_entire q br amp K hb hb1).analyticAt w),?_⟩
  intro u hu
  have ht := ((h b hb hbB).2 u hu).add_const (nativeForcingOuterIntegral q br amp K b u)
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsGT hb] with e he
  exact (nativeForcingSourceCutoff_split q br amp K u he.1 he.2.le hb1).symm

/-- The native forcing finite part is analytic throughout the QNM strip;
 its opposite-branch logarithm has not been discarded. -/
theorem nativeForcingSourceFinitePart_analyticAt (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) : AnalyticAt ℂ (nativeForcingSourceFinitePart q br amp K) w := by
  obtain ⟨R,B,hR,hB,_,h⟩ := nativeForcingSource_local_data q br amp K w hw hwr
  obtain ⟨ha,hlim⟩ := h B hB le_rfl
  apply ha.congr
  filter_upwards [ball_mem_nhds w hR] with u hu
  exact (hlim u hu).limUnder_eq.symm

theorem nativeForcingSourceCutoff_tendsto (q : XiZeroCopy) (br : Bool) (amp K w : ℂ)
    (hw : w.im≠0) (hwr : -2<w.re) : Tendsto (nativeForcingSourceCutoff q br amp K w)
      (𝓝[>] (0:ℝ)) (𝓝 (nativeForcingSourceFinitePart q br amp K w)) := by
  obtain ⟨R,B,hR,hB,_,h⟩ := nativeForcingSource_local_data q br amp K w hw hwr
  have ht := (h B hB le_rfl).2 w (mem_ball_self hR)
  simpa only [nativeForcingSourceFinitePart,ht.limUnder_eq] using ht

end
end RHTower.D4BMOriginalSourceResolvent

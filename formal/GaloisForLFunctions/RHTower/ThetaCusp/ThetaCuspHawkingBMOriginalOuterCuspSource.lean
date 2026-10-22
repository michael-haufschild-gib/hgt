import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalCausalCuspGrowth
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalSourceTailAdmission
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalSourceRadialRestoration
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMReducedOuterPairing

/-! Finite-cusp scalar-period control on the complete finite outer interval. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalOuterCuspSource
open D4BMJointSource D4BMModularCore D4BMLaplaceRadial D4BMJointWave
open D4BMOriginalReaderCuspBounds D4BMOriginalAngularReaderBounds
open D4BMOriginalCausalCuspGrowth D4BMOriginalSourceTailCollar D4BMOriginalSourceTailAdmission
noncomputable section
set_option autoImplicit false

/-- The unchanged normalizable reader is bounded through the outer endpoint. -/
theorem outer_reader_bound (q : XiZeroCopy) (w : ℂ) (A : ℝ) (hA : 0<A) (hw : 0≤w.re) :
    ∃ C : ℝ,0≤C ∧ ∀ L∈Ioc (0:ℝ) A,‖reader q w L‖≤C := by
  obtain ⟨C,hC,h⟩ := tortoiseNormalizable_outer_uniform_bound w (physicalRadialFrequency q)
    (show -(A+1)/2<0 by linarith)
  refine ⟨C,hC,?_⟩
  intro L hL
  have hx : -L/2∈Ioo (-(A+1)/2) (0:ℝ) := ⟨by linarith [hL.2],by linarith [hL.1]⟩
  have he : ‖Complex.exp (w*((-L/2:ℝ):ℂ))‖≤1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hw hx.2.le
  rw [reader,norm_mul]
  calc
    _ ≤ 1*‖tortoiseMode true w (physicalRadialFrequency q) (-L/2)‖ :=
      mul_le_mul_of_nonneg_right he (norm_nonneg _)
    _ ≤ C := by simpa [tortoiseMode,radialMode] using h w (Metric.mem_ball_self (by norm_num)) (-L/2) hx

/-- The actual scalar-period tail has an integrable time envelope uniform
through every finite outer interval and over its unbounded angular tail. -/
theorem outer_tail_density_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∀ A : ℝ,0<A →
      ∃ C : ℝ,0≤C ∧ ∀ L∈Ioc (0:ℝ) A,∀ p k : ℝ,0≤p → 0≤k →
        ∀ z∈tailSet k,‖tailDensity q br amp w p L z‖≤
          C*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨G,hG,hg⟩ := source_jet_damped q br amp 0 (N+1)
  obtain ⟨D,hD,hd⟩ := angularJet_bound q false
  refine ⟨G,hG,?_⟩
  intro w hw A hA
  obtain ⟨B,hB,hb⟩ := hg w hw
  obtain ⟨R,hR,hr⟩ := outer_reader_bound q w A hA (by linarith)
  refine ⟨R*B*D,by positivity,?_⟩
  intro L hL p k hp hk z hz
  let t := Real.log z.im
  have ht : k≤t := by
    have h := Real.log_le_log (Real.exp_pos k) hz.le
    simpa only [Real.log_exp] using h
  have ht0 : 0≤t := hk.trans ht
  have he : tailDensity q br amp w p L z=reader q w L*
      (Complex.exp (-w*(p:ℂ))*sourceJet q br amp 0 p L z.re t)*angularJet q false z.re t := by
    unfold tailDensity
    dsimp [t]
    ring
  rw [he,norm_mul,norm_mul]
  calc
    _ ≤ R*(B*Real.exp (-((N+1:ℕ):ℝ)*t)*Real.exp (-p))*(D*Real.exp t) :=
      mul_le_mul (mul_le_mul (hr L hL) (hb p L z.re t hp hL.1 ht0) (norm_nonneg _) hR)
        (hd z.re t ht0) (norm_nonneg _) (by positivity)
    _ = R*B*D*Real.exp (-(N:ℝ)*t)*Real.exp (-p) := by
      rw [show R*(B*Real.exp (-((N+1:ℕ):ℝ)*t)*Real.exp (-p))*(D*Real.exp t)=
        R*B*D*(Real.exp (-((N+1:ℕ):ℝ)*t)*Real.exp t)*Real.exp (-p) by ring,← Real.exp_add]
      congr 3
      push_cast
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht (neg_nonpos.mpr (Nat.cast_nonneg N)))

/-- The literal finite-height source-period error is uniformly small on the
outer interval, with the original angular measure and time damping. -/
theorem outer_period_error_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∀ A : ℝ,0<A →
      ∃ C : ℝ,0≤C ∧ ∀ L∈Ioc (0:ℝ) A,∀ p k : ℝ,0<p → 0≤k → 4≤Real.exp k →
        ‖originalPeriodError q br amp w p L k‖≤C*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨G,hG,hg⟩ := outer_tail_density_bound q br amp N
  refine ⟨G,hG,?_⟩
  intro w hw A hA
  obtain ⟨C,hC,hc⟩ := hg w hw A hA
  refine ⟨C*measure.real univ,by positivity,?_⟩
  intro L hL p k hp hk hk4
  rw [original_period_error_tail q br amp w p L k hp hL.1 hk4,norm_neg]
  let B := C*Real.exp (-(N:ℝ)*k)*Real.exp (-p)
  have hB : 0≤B := by dsimp [B]; positivity
  have hm : MeasurableSet (tailSet k) := measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable
  have h := norm_integral_le_of_norm_le (integrable_const B : Integrable (fun _ : UpperHalfPlane => B) (measure.restrict (tailSet k))) (by
    filter_upwards [ae_restrict_mem hm] with z hz
    exact hc L hL p k hp.le hk z hz)
  simp only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ] at h
  calc
    _ ≤ measure.real (tailSet k)*B := h
    _ ≤ measure.real univ*B := mul_le_mul_of_nonneg_right (measureReal_mono (μ:=measure) (subset_univ _)) hB
    _ = _ := by dsimp [B];ring

/-- Original source-period error is jointly continuous throughout positive
outer depth and source time, with a uniform cusp-tail majorant. -/
theorem outer_period_joint_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∀ A : ℝ,0<A → ∀ k : ℝ,0≤k → 4≤Real.exp k →
      ContinuousOn (fun v : ℝ×ℝ => originalPeriodError q br amp w v.2 v.1 k)
        (Ioc (0:ℝ) A ×ˢ Ioi 0) := by
  obtain ⟨G,hG,hg⟩ := outer_tail_density_bound q br amp 0
  refine ⟨G,hG,?_⟩
  intro w hw A hA k hk hk4
  obtain ⟨C,hC,hc⟩ := hg w hw A hA
  let S := Ioc (0:ℝ) A ×ˢ Ioi (0:ℝ)
  have hm : MeasurableSet (tailSet k) := measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable
  have hbound (v : ℝ×ℝ) (hv : v∈S) (z : UpperHalfPlane) (hz : z∈tailSet k) :
      ‖tailDensity q br amp w v.2 v.1 z‖≤C := by
    have h := hc v.1 hv.1 v.2 k hv.2.le hk z hz
    simp only [Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero,mul_one] at h
    exact h.trans (mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (show 0≤v.2 from hv.2.le))))
  have hi : ContinuousOn (fun v : ℝ×ℝ => ∫ z in tailSet k,tailDensity q br amp w v.2 v.1 z ∂measure) S := by
    apply continuousOn_of_dominated
      (fun v hv => (tail_density_integrable q br amp w v.2 v.1 k hv.2 hv.1.1 hk4).aestronglyMeasurable)
      (bound:=fun _ => C) _ (integrable_const _) _
    · intro v hv
      filter_upwards [ae_restrict_mem hm] with z hz
      exact hbound v hv z hz
    · apply Filter.Eventually.of_forall
      intro z v hv
      exact ((tail_density_joint_continuousAt q br amp w (v,z) hv.1.1 hv.2).comp
        (f:=fun t : ℝ×ℝ => (t,z)) (show ContinuousAt (fun t : ℝ×ℝ => (t,z)) v by fun_prop)).continuousWithinAt
  exact hi.neg.congr (fun v hv => original_period_error_tail q br amp w v.2 v.1 k hv.2 hv.1.1 hk4)

/-- Both original temporal endpoints and the full time moment have a uniform
outer bound after the actual scalar-period tail has been retained. -/
theorem outer_source_functional_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∀ A : ℝ,0<A →
      ∃ C : ℝ,0≤C ∧ ∀ L∈Ioc (0:ℝ) A,∀ a b k : ℝ,0<a → a≤b → 0≤k → 4≤Real.exp k →
        ‖D4BMOriginalSourceRadialRestoration.sourceFunctional q br amp w a b L k‖≤C*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G,hG,hg⟩ := outer_period_error_bound q br amp N
  refine ⟨G,hG,?_⟩
  intro w hw A hA
  obtain ⟨C,hC,hc⟩ := hg w hw A hA
  let mu := D4BMLeftModeRadialEquation.eigenvalue q
  refine ⟨‖mu*(mu-2)‖*(2+‖2*w‖)*C,by positivity,?_⟩
  intro L hL a b k ha hab hk hk4
  let E := C*Real.exp (-(N:ℝ)*k)
  have hE : 0≤E := by dsimp [E];positivity
  have hbnd (p : ℝ) (hp : a≤p) : ‖originalPeriodError q br amp w p L k‖≤E :=
    (hc L hL p k (ha.trans_le hp) hk hk4).trans
      (mul_le_of_le_one_right hE (Real.exp_le_one_iff.mpr (by linarith)))
  have hi : ‖∫ p in a..b,originalPeriodError q br amp w p L k‖≤E := by
    have h := D4BMOriginalSourceRadialRestoration.exponential_interval_bound
      (fun p => originalPeriodError q br amp w p L k) E a b hE hab
      (fun p hp => hc L hL p k (ha.trans_le hp.1) hk hk4)
    exact h.trans (mul_le_of_le_one_right hE (Real.exp_le_one_iff.mpr (by linarith)))
  rw [D4BMOriginalSourceRadialRestoration.sourceFunctional,norm_mul]
  calc
    _ ≤ ‖mu*(mu-2)‖*((E+E)+‖2*w‖*E) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
        (add_le_add ((norm_sub_le _ _).trans (add_le_add (hbnd b hab) (hbnd a le_rfl)))
          ((norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left hi (norm_nonneg _))))) (norm_nonneg _)
    _ = _ := by dsimp [E]; ring

private theorem source_functional_continuous {q : XiZeroCopy} {br : Bool} {amp w : ℂ}
    {A k a : ℝ} (ha : 0<a)
    (hc : ContinuousOn (fun v : ℝ×ℝ => originalPeriodError q br amp w v.2 v.1 k)
      (Ioc (0:ℝ) A ×ˢ Ioi 0)) (b : ℝ→ℝ) (hb : Continuous b)
    (hab : ∀ L : ℝ,a≤b L) :
    ContinuousOn (fun L => D4BMOriginalSourceRadialRestoration.sourceFunctional q br amp w a (b L) L k)
      (Ioc (0:ℝ) A) := by
  let F := fun L : Ioc (0:ℝ) A => fun p : ℝ => originalPeriodError q br amp w (max a p) L.val k
  have hF : Continuous (Function.uncurry F) := by
    exact hc.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_const.max continuous_snd))
      (fun v => ⟨v.1.property,ha.trans_le (le_max_left _ _)⟩)
  have hi : Continuous (fun L : Ioc (0:ℝ) A => ∫ p in a..b L.val,F L p) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF (hb.comp continuous_subtype_val)
  have hT := hF.comp (continuous_id.prodMk (hb.comp continuous_subtype_val))
  have hA := hF.comp (continuous_id.prodMk (continuous_const (y:=a)))
  apply continuousOn_iff_continuous_restrict.mpr
  apply (((hT.sub hA).add (hi.const_mul (2*w))).const_mul
    (D4BMLeftModeRadialEquation.eigenvalue q*(D4BMLeftModeRadialEquation.eigenvalue q-2))).congr
  intro L
  have hI : (∫ p in a..b L.val,F L p)=∫ p in a..b L.val,originalPeriodError q br amp w p L.val k := by
    apply intervalIntegral.integral_congr
    intro p hp
    have hp' : a≤p := (show p∈Icc a (b L.val) by simpa only [uIcc_of_le (hab L.val)] using hp).1
    exact congrArg (fun t => originalPeriodError q br amp w t L.val k) (max_eq_right hp')
  change (D4BMLeftModeRadialEquation.eigenvalue q*(D4BMLeftModeRadialEquation.eigenvalue q-2))*
    (F L (b L.val)-F L a+2*w*(∫ p in a..b L.val,F L p))=_
  rw [hI]
  simp only [F,max_self,max_eq_right (hab L.val),D4BMOriginalSourceRadialRestoration.sourceFunctional]
  rfl

/-- The complete source contribution on the original static-time triangle is
separately admitted up to the outer endpoint and tends to zero uniformly in
the independent onset and terminal-time cutoffs. -/
theorem outer_static_source_restoration (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∀ A : ℝ,0<A →
      ∃ C : ℝ,0≤C ∧ ∀ a T k : ℝ,0<a → 0≤k → 4≤Real.exp k →
        IntervalIntegrable (fun L => D4BMOriginalSourceRadialRestoration.sourceFunctional
          q br amp w a (max a (T-L/2)) L k) volume 0 A ∧
        ‖∫ L in (0:ℝ)..A,D4BMOriginalSourceRadialRestoration.sourceFunctional
          q br amp w a (max a (T-L/2)) L k/2‖≤C*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G1,hG1,h1⟩ := outer_source_functional_bound q br amp N
  obtain ⟨G2,hG2,h2⟩ := outer_period_joint_continuous q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hw A hA
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1≤w.re := by linarith [le_max_right G1 G2]
  obtain ⟨C,hC,hc⟩ := h1 w hw1 A hA
  refine ⟨A*C/2,by positivity,?_⟩
  intro a T k ha hk hk4
  let f := fun L => D4BMOriginalSourceRadialRestoration.sourceFunctional q br amp w a (max a (T-L/2)) L k
  have hf : ContinuousOn f (Ioc (0:ℝ) A) :=
    source_functional_continuous ha (h2 w hw2 A hA k hk hk4)
      (fun L => max a (T-L/2)) (by fun_prop) (fun _ => le_max_left _ _)
  have hb (L : ℝ) (hL : L∈Ioc (0:ℝ) A) : ‖f L‖≤C*Real.exp (-(N:ℝ)*k) :=
    hc L hL a (max a (T-L/2)) k ha (le_max_left _ _) hk hk4
  constructor
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hA.le).mpr
    apply (integrable_const (C*Real.exp (-(N:ℝ)*k))).mono' (hf.aestronglyMeasurable measurableSet_Ioc)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
    exact hb L hL
  · have hi := intervalIntegral.norm_integral_le_of_norm_le (μ:=volume) hA.le
      (Filter.Eventually.of_forall (fun L (hL : L∈Ioc (0:ℝ) A) => hb L hL)) (intervalIntegrable_const)
    rw [intervalIntegral.integral_div,norm_div]
    have htwo : ‖(2:ℂ)‖=(2:ℝ) := by norm_num
    rw [htwo]
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hi
    calc
      _ ≤ (A*(C*Real.exp (-(N:ℝ)*k)))/2 := div_le_div_of_nonneg_right hi (by norm_num)
      _ = _ := by ring

end
end RHTower.D4BMOriginalOuterCuspSource

import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalForcingClockContact

open Set Filter Topology MeasureTheory Complex
namespace RHTower.D4BMOriginalStaticPhysicalMass
open D4BMJointSource D4BMModularCore D4BMLaplaceRadial
open D4BMOriginalStaticForcingTriangle D4BMOriginalForcingClockContact
noncomputable section
set_option autoImplicit false

/-- Actual radial length available to source time `p` inside the static cut. -/
def radialWindow (ξ b T p : ℝ) : ℝ := max 0 (b-max ξ (p-T))

private theorem window_nonneg (ξ b T p : ℝ) : 0 ≤ radialWindow ξ b T p := le_max_left _ _

private theorem window_le (ξ b T p : ℝ) (hξ : ξ ≤ b) : radialWindow ξ b T p ≤ b-ξ := by
  exact max_le (sub_nonneg.mpr hξ) (sub_le_sub_left (le_max_left _ _) _)

private theorem window_length (a ξ b T : ℝ) (hξ : ξ ≤ b) :
    radialWindow ξ b T a=max a (T+b)-max a (T+ξ) := by
  simp only [radialWindow,max_def]
  split_ifs <;> linarith

/-- Moving the source time by `p-a` changes available radial length by at
most `p-a`, independently of both radial ends and the static time cut. -/
private theorem window_variation (a ξ b T p : ℝ) (ha : 0 ≤ a) (hap : a ≤ p) :
    |radialWindow ξ b T p-radialWindow ξ b T a| ≤ p := by
  have hm : max ξ (a-T) ≤ max ξ (p-T) := max_le_max_left ξ (by linarith)
  have hW : radialWindow ξ b T p ≤ radialWindow ξ b T a :=
    max_le_max_left 0 (sub_le_sub_left hm b)
  have hn : max ξ (p-T) ≤ max ξ (a-T)+(p-a) := by
    apply max_le
    · linarith [le_max_left ξ (a-T)]
    · linarith [le_max_right ξ (a-T)]
  have hd : radialWindow ξ b T a ≤ radialWindow ξ b T p+(p-a) := by
    apply max_le
    · linarith [window_nonneg ξ b T p]
    · have hb : b-max ξ (p-T) ≤ radialWindow ξ b T p := le_max_right _ _
      linarith
  rw [abs_of_nonpos (sub_nonpos.mpr hW)]
  linarith

private theorem onset_continuous (q : XiZeroCopy) (br : Bool) (w : ℂ) :
    Continuous (onsetDensity q br w) := by
  have h : Continuous (timeOnset (2*physicalRate q br)) :=
    continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt _ p).continuousAt)
  unfold onsetDensity
  fun_prop

/-- The first absolute moment of the literal damped causal onset is admitted. -/
theorem onset_first_moment_integrable (q : XiZeroCopy) (br : Bool) (w : ℂ)
    (hw : 0 ≤ w.re) :
    IntegrableOn (fun p : ℝ => p*‖onsetDensity q br w p‖) (Ioi 0) := by
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  have hc : 0 < w.re-(2*physicalRate q br).re := by linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p:=1)
    (show (-1:ℝ)<(1:ℝ) by norm_num) (by norm_num) hc
  have hi : IntegrableOn (fun p : ℝ => p*Real.exp (-(w.re-(2*physicalRate q br).re)*p)) (Ioi 0) := by
    simpa only [Real.rpow_one] using h
  apply hi.mono' ((continuous_id.mul (onset_continuous q br w).norm).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  have ht : ‖(Real.smoothTransition p:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg p)]
      using Real.smoothTransition.le_one p
  have he : ‖onsetDensity q br w p‖ ≤ Real.exp (-(w.re-(2*physicalRate q br).re)*p) := by
    unfold onsetDensity timeOnset
    rw [norm_mul,norm_mul]
    have hE (v : ℂ) : ‖Complex.exp (v*(p:ℂ))‖=Real.exp (v.re*p) := by
      rw [Complex.norm_exp];congr 1;simp
    rw [hE,hE]
    calc
      _ ≤ Real.exp ((-w).re*p)*Real.exp ((2*physicalRate q br).re*p) :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (Real.exp_nonneg _) ht) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add];congr 1;simp only [Complex.neg_re];ring
  change ‖p*‖onsetDensity q br w p‖‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp.le (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left he hp.le

def onsetMass (q : XiZeroCopy) (br : Bool) (w : ℂ) (a : ℝ) : ℂ :=
  ∫ p in Ioi a,onsetDensity q br w p

private theorem window_integrable (q : XiZeroCopy) (br : Bool) (w : ℂ)
    (hw : 0 ≤ w.re) (a ξ b T : ℝ) (ha : 0 ≤ a) (hξ : ξ ≤ b) :
    IntegrableOn (fun p => onsetDensity q br w p*(radialWindow ξ b T p:ℂ)) (Ioi a) := by
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  have hi : IntegrableOn (onsetDensity q br w) (Ioi a) :=
    (timeOnset_integrable (2*physicalRate q br) w (by linarith)).mono_set (Ioi_subset_Ioi ha)
  apply hi.mul_bdd (c:=b-ξ) (by unfold radialWindow;fun_prop)
  exact ae_of_all _ (fun p => by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (window_nonneg ξ b T p)]
    exact window_le ξ b T p hξ)

/-- Finite causal geometry expressed as the actual half-line occupation integral. -/
theorem horizon_triangle_window (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 0 ≤ w.re) (a ξ b T k : ℝ) (ha : 0 ≤ a) (hξ : ξ ≤ b) :
    horizonTriangle q br amp w a ξ b T k=
      horizonForcingDifference q br amp w k*
        ∫ p in Ioi a,onsetDensity q br w p*(radialWindow ξ b T p:ℂ) := by
  let u := max a (T+b)
  have hau : a ≤ u := le_max_left _ _
  have hi := window_integrable q br w hw a ξ b T ha hξ
  have hzero : (∫ p in Ioi u,onsetDensity q br w p*(radialWindow ξ b T p:ℂ))=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    change u < p at hp
    have hu : T+b ≤ u := le_max_right _ _
    have hb : b ≤ max ξ (p-T) := le_max_of_le_right (by linarith)
    change onsetDensity q br w p*(radialWindow ξ b T p:ℂ)=0
    have hz : radialWindow ξ b T p=0 := max_eq_left (sub_nonpos.mpr hb)
    rw [hz,Complex.ofReal_zero,mul_zero]
  have he := intervalIntegral.integral_interval_add_Ioi hi (hi.mono_set (Ioi_subset_Ioi hau))
  rw [hzero,add_zero] at he
  rw [← he,← intervalIntegral.integral_const_mul]
  by_cases hT : T+b ≤ a
  · simp only [horizonTriangle,u,max_eq_left hT,intervalIntegral.integral_same]
  · have hTa : a ≤ T+b := (lt_of_not_ge hT).le
    unfold horizonTriangle
    dsimp only [u]
    rw [max_eq_right hTa]
    apply intervalIntegral.integral_congr
    intro p hp
    have hp' : p ∈ Icc a (T+b) := by simpa only [uIcc_of_le hTa] using hp
    have hb : max ξ (p-T) ≤ b := max_le hξ (by linarith [hp'.2])
    have hW : radialWindow ξ b T p=b-max ξ (p-T) := max_eq_right (sub_nonneg.mpr hb)
    change onsetDensity q br w p*(horizonForcingDifference q br amp w k*((b-max ξ (p-T):ℝ):ℂ))=
      horizonForcingDifference q br amp w k*(onsetDensity q br w p*(radialWindow ξ b T p:ℂ))
    rw [hW]
    ring

/-- A single actual onset mass removes the forcing horizon term with error
controlled by the onset's first moment, uniformly over all physical cutoffs. -/
theorem horizon_triangle_mass_bound (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 0 ≤ w.re) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ a ξ b T k : ℝ,0 ≤ a → ξ ≤ b →
      ‖horizonTriangle q br amp w a ξ b T k-
        (max a (T+b)-max a (T+ξ))•
          (horizonForcingDifference q br amp w k*onsetMass q br w a)‖ ≤
            ‖horizonForcingDifference q br amp w k‖*M := by
  let M := ∫ p in Ioi (0:ℝ),p*‖onsetDensity q br w p‖
  have hM : 0 ≤ M := setIntegral_nonneg measurableSet_Ioi (fun p hp => mul_nonneg hp.le (norm_nonneg _))
  refine ⟨M,hM,?_⟩
  intro a ξ b T k ha hξ
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  have hi : IntegrableOn (onsetDensity q br w) (Ioi a) :=
    (timeOnset_integrable (2*physicalRate q br) w (by linarith)).mono_set (Ioi_subset_Ioi ha)
  have hW := window_integrable q br w hw a ξ b T ha hξ
  have hI := onset_first_moment_integrable q br w hw
  have hIa := hI.mono_set (Ioi_subset_Ioi ha)
  have he : horizonTriangle q br amp w a ξ b T k-
      (max a (T+b)-max a (T+ξ))•
        (horizonForcingDifference q br amp w k*onsetMass q br w a)=
      horizonForcingDifference q br amp w k*
        ∫ p in Ioi a,onsetDensity q br w p*
          ((radialWindow ξ b T p-radialWindow ξ b T a:ℝ):ℂ) := by
    rw [horizon_triangle_window q br amp w hw a ξ b T k ha hξ]
    have hsub := integral_sub hW (hi.mul_const (radialWindow ξ b T a:ℂ))
    have hrep : (∫ p in Ioi a,onsetDensity q br w p*((radialWindow ξ b T p-radialWindow ξ b T a:ℝ):ℂ))=
        (∫ p in Ioi a,onsetDensity q br w p*(radialWindow ξ b T p:ℂ))-
          (∫ p in Ioi a,onsetDensity q br w p)*(radialWindow ξ b T a:ℂ) := by
      rw [← integral_mul_const,← hsub]
      apply integral_congr_ae
      exact ae_of_all _ (fun p => by push_cast;ring)
    rw [hrep,window_length a ξ b T hξ]
    simp only [onsetMass,Complex.real_smul]
    ring
  rw [he,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_integral_le_of_norm_le hIa ?_).trans
  · exact setIntegral_mono_set hI
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp;exact mul_nonneg hp.le (norm_nonneg _))
      (ae_of_all _ (fun p hp => ha.trans_lt hp))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (window_variation a ξ b T p ha hp.le) (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- The complete horizon mass discrepancy at the original positive onset.
Both the source/boundary mass and forcing mass come from the same finite
cusp-height physical field. -/
def metricHorizonMassDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (k a : ℝ) : ℂ :=
  D4BMOriginalStaticTracePrimitive.traceMass q br amp w k a+
    D4BMLeftModeRadialEquation.eigenvalue q*w*
      horizonForcingDifference q br amp w k*onsetMass q br w a

def massRestoredStaticDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (a A B T k : ℝ) : ℂ :=
  (∫ L in A..B,D4BMOriginalFullMetricCollar.metricDifference q br amp w
    a (max a (T-L/2)) L k)/2-
      (max a (T-A/2)-max a (T-B/2))•metricHorizonMassDifference q br amp w k a

/-- The full original static metric collar admits a single physical temporal
mass subtraction. Its remaining angular discrepancy vanishes uniformly over
independent onset, time and horizon cutoffs, at every sufficiently deep fixed
interface on the derived convergence half-plane. -/
theorem full_static_physical_mass_restoration (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0 ≤ G ∧ ∀ w : ℂ,w.im ≠ 0 → G+1 ≤ w.re →
      ∃ A0 : ℝ,0 < A0 ∧ ∀ A : ℝ,A0 ≤ A →
        ∃ η : ℝ→ℝ,(∀ k,0 ≤ η k) ∧ Tendsto η atTop (𝓝 0) ∧
          ∀ a B T k : ℝ,0 < a → A ≤ B → 0 ≤ k → 4 ≤ Real.exp k →
            IntervalIntegrable (fun L => D4BMOriginalFullMetricCollar.metricDifference q br amp w
              a (max a (T-L/2)) L k) volume A B ∧
            ‖massRestoredStaticDifference q br amp w a A B T k‖ ≤ η k := by
  obtain ⟨G,hG,h⟩ := full_static_horizon_restoration q br amp
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨A0,hA0,hA⟩ := h w hwi hw
  obtain ⟨M,hM,hMbound⟩ := horizon_triangle_mass_bound q br amp w (by linarith)
  let m := D4BMLeftModeRadialEquation.eigenvalue q*w
  refine ⟨A0,hA0,?_⟩
  intro A hAA
  obtain ⟨η,hη,hηlim,hηbound⟩ := hA A hAA
  refine ⟨fun k => η k+‖m‖*(‖horizonForcingDifference q br amp w k‖*M),
    fun k => add_nonneg (hη k) (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) hM)),?_,?_⟩
  · simpa only [norm_zero,zero_mul,mul_zero,add_zero] using
      hηlim.add (((horizon_forcing_difference_tendsto q br amp w).norm.mul_const M).const_mul ‖m‖)
  · intro a B T k ha hAB hk hk4
    obtain ⟨hi,hb⟩ := hηbound a B T k ha hAB hk hk4
    refine ⟨hi,?_⟩
    have he : massRestoredStaticDifference q br amp w a A B T k=
        physicalStaticDifference q br amp w a A B T k+
          m*(horizonTriangle q br amp w a (-B/2) (-A/2) T k-
            (max a (T+(-A/2))-max a (T+(-B/2)))•
              (horizonForcingDifference q br amp w k*onsetMass q br w a)) := by
      simp only [massRestoredStaticDifference,metricHorizonMassDifference,
        physicalStaticDifference,Complex.real_smul,m,sub_eq_add_neg,neg_div]
      ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    exact add_le_add hb (mul_le_mul_of_nonneg_left
      (hMbound a (-B/2) (-A/2) T k ha.le (by linarith)) (norm_nonneg _))

end
end RHTower.D4BMOriginalStaticPhysicalMass

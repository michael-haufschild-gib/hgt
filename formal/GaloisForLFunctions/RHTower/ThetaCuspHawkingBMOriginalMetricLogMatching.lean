import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalMetricTraceDecay
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalTemporalCorner

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalMetricLogMatching
open D4BMJointSource D4BMModularCore D4BMLaplaceRadial
open D4BMOriginalFullMetricCollar D4BMOriginalFullCollarRestoration
open D4BMOriginalMetricTraceDecay D4BMOriginalTemporalCorner
noncomputable section
set_option autoImplicit false

/-- Exact conversion at the unchanged physical horizon coordinate. -/
theorem original_log_coordinate (A L : ℝ) :
    (L-A)/2+Real.log (horizonCoordinate (-L/2))/2=
      Real.log (1+radialUnit (-L/2))-A/2 := by
  rw [horizonCoordinate_factor,Real.log_pow,
    Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (radialUnit_add_one_pos (-L/2))),Real.log_exp]
  ring

/-- The finite coordinate conversion has the original fixed log-two limit. -/
theorem original_log_coordinate_limit (A : ℝ) :
    Tendsto (fun L : ℝ => (L-A)/2+Real.log (horizonCoordinate (-L/2))/2)
      atTop (𝓝 (Real.log 2-A/2)) := by
  have h := (original_radial_log_shift.comp
    (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2))).sub_const (A/2)
  apply h.congr
  intro L
  change L/2+Real.log (horizonCoordinate (-(L/2)))/2-A/2=
    (L-A)/2+Real.log (horizonCoordinate (-L/2))/2
  rw [neg_div]
  ring

/-- Uniform vanishing of the complete retained trace under arbitrary temporal
cutoffs; no assertion that the finite-height trace itself vanishes. -/
theorem metric_trace_joint_limit (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re →
      ∀ {ι : Type*} (l : Filter ι) (K : ι→ℝ),Tendsto K l atTop →
      ∀ T : ι→{v : ℝ×ℝ // 0<v.1 ∧ v.1≤v.2},
        Tendsto (fun z => metricTrace q br amp w (T z).val.1 (T z).val.2 (K z)) l (𝓝 0) := by
  obtain ⟨G,hG,hg⟩ := metric_trace_decay q br amp 1
  refine ⟨G,hG,?_⟩
  intro w hw ι l K hK T
  obtain ⟨C,hC,hc⟩ := hg w hw
  have hlim : Tendsto (fun z => C*Real.exp (-K z)) l (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C).comp hK
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hK.eventually (eventually_ge_atTop (0:ℝ))] with z hz
  simpa only [Nat.cast_one,neg_one_mul] using hc (T z).val.1 (T z).val.2 (K z) (T z).property.1 (T z).property.2 hz

/-- The full finite original metric discrepancy with literal logarithmic
horizon subtraction and the same source-fixed forcing counterterms. -/
def logarithmicCollarDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (a b A L k : ℝ) : ℂ :=
  (∫ X in A..L,metricDifference q br amp w a b X k)/2+
    (Real.log (horizonCoordinate (-L/2)):ℂ)*metricTrace q br amp w a b k/2-
      forcingCountertermDifference q br amp w a b L k

/-- Exact finite-cutoff identity; the retained normalization cannot be chosen
independently of the physical coordinate. -/
theorem logarithmic_collar_identity (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (a b A L k : ℝ) :
    logarithmicCollarDifference q br amp w a b A L k=
      fullCollarDifference q br amp w a b A L k+
        (((L-A)/2+Real.log (horizonCoordinate (-L/2))/2:ℝ):ℂ)*metricTrace q br amp w a b k := by
  unfold logarithmicCollarDifference fullCollarDifference
  simp only [Complex.real_smul,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_ofNat]
  ring

/-- The complete rectangular original metric collar matches the literal
logarithmic horizon prescription under independent horizon and cusp removal,
with both temporal endpoints arbitrary and all forcing counterterms retained. -/
theorem full_metric_logarithmic_restoration (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ A : ℝ,0<A ∧
      ∀ T : ℝ×ℝ→{v : ℝ×ℝ // 0<v.1 ∧ v.1≤v.2},
        Tendsto (fun z : ℝ×ℝ => logarithmicCollarDifference q br amp w
          (T z).val.1 (T z).val.2 A z.1 z.2)
          ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  obtain ⟨G1,hG1,h1⟩ := full_metric_collar_joint_restoration q br amp
  obtain ⟨G2,_,h2⟩ := metric_trace_joint_limit q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  obtain ⟨A,hA,ha⟩ := h1 w hwi (by linarith [le_max_left G1 G2])
  refine ⟨A,hA,?_⟩
  intro T
  have ht := h2 w (by linarith [le_max_right G1 G2])
    ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) Prod.snd tendsto_snd T
  have hs := ((original_log_coordinate_limit A).ofReal.comp tendsto_fst).mul ht
  simp only [mul_zero] at hs
  have h := (ha T).add hs
  simp only [zero_add] at h
  apply h.congr
  intro z
  exact (logarithmic_collar_identity q br amp w (T z).val.1 (T z).val.2 A z.1 z.2).symm

end
end RHTower.D4BMOriginalMetricLogMatching

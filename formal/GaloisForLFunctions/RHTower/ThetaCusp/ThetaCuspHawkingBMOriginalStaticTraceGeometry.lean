import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalStaticTracePrimitive

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalStaticTraceGeometry
open D4BMJointSource D4BMModularCore D4BMOriginalStaticTracePrimitive
open D4BMOriginalFullMetricCollar D4BMOriginalSourceRadialRestoration D4BMOriginalBoundaryRestoration
noncomputable section
set_option autoImplicit false

private theorem clamped_integral (f : ℝ→ℂ) (a r s : ℝ) (hrs : r  ≤  s) (hfa : f a=0)
    (hi : ∀ u v : ℝ,a ≤ u → u ≤ v → IntervalIntegrable f volume u v) :
    IntervalIntegrable (fun b => f (max a b)) volume r s ∧
      (∫ b in r..s,f (max a b))=∫ b in max a r..max a s,f b := by
  let g := fun b => f (max a b)
  have hz (b : ℝ) (hb : b ≤ a) : g b=0 := by dsimp [g];rw [max_eq_left hb,hfa]
  have he (b : ℝ) (hb : a ≤ b) : g b=f b := by dsimp [g];rw [max_eq_right hb]
  have below (c d : ℝ) (hcd : c ≤ d) (hda : d ≤ a) :
      IntervalIntegrable g volume c d ∧ (∫ b in c..d,g b)=0 := by
    constructor
    · apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:ℂ)) volume c d).congr
      intro b hb
      have hb' : b∈Ioc c d := by simpa only [uIoc_of_le hcd] using hb
      exact (hz b (hb'.2.trans hda)).symm
    · calc
        _ = ∫ b in c..d,(0:ℂ) := by
          apply intervalIntegral.integral_congr
          intro b hb
          have hb' : b∈Icc c d := by simpa only [uIcc_of_le hcd] using hb
          exact hz b (hb'.2.trans hda)
        _ = 0 := by simp
  have above (c d : ℝ) (hac : a ≤ c) (hcd : c ≤ d) :
      IntervalIntegrable g volume c d ∧ (∫ b in c..d,g b)=∫ b in c..d,f b := by
    constructor
    · apply (hi c d hac hcd).congr
      intro b hb
      have hb' : b∈Ioc c d := by simpa only [uIoc_of_le hcd] using hb
      exact (he b (hac.trans hb'.1.le)).symm
    · apply intervalIntegral.integral_congr
      intro b hb
      have hb' : b∈Icc c d := by simpa only [uIcc_of_le hcd] using hb
      exact he b (hac.trans hb'.1)
  by_cases hsa : s ≤ a
  · have h := below r s hrs hsa
    simpa only [max_eq_left hsa,max_eq_left (hrs.trans hsa),intervalIntegral.integral_same] using h
  · have has : a ≤ s := le_of_lt (lt_of_not_ge hsa)
    by_cases har : a ≤ r
    · simpa only [max_eq_right har,max_eq_right has] using above r s har hrs
    · have hra : r ≤ a := le_of_lt (lt_of_not_ge har)
      obtain ⟨hil,hel⟩ := below r a hra le_rfl
      obtain ⟨hir,her⟩ := above a s le_rfl has
      refine ⟨hil.trans hir,?_⟩
      rw [max_eq_left hra,max_eq_right has,← intervalIntegral.integral_add_adjacent_intervals hil hir,hel,zero_add]
      exact her

private theorem collar_change_of_variables (f : ℝ→ℂ) (A B T : ℝ) :
    (∫ L in A..B,f (T-L/2))/2=∫ p in (T-B/2)..(T-A/2),f p := by
  have he : (fun L : ℝ => f (T-L/2))=fun L => f (T+(-(1/2:ℝ))*L) := by
    funext L
    congr 1
    ring
  rw [he,intervalIntegral.integral_comp_add_mul f (by norm_num : -(1/2:ℝ)≠0) T]
  rw [show T+(-(1/2:ℝ))*A=T-A/2 by ring,show T+(-(1/2:ℝ))*B=T-B/2 by ring]
  have hs : (∫ p in (T-A/2)..(T-B/2),f p)=-(∫ p in (T-B/2)..(T-A/2),f p) :=
    intervalIntegral.integral_symm _ _
  rw [hs]
  norm_num [smul_eq_mul]

private theorem collar_admission (f : ℝ→ℂ) (A B T : ℝ)
    (hi : IntervalIntegrable f volume (T-B/2) (T-A/2)) :
    IntervalIntegrable (fun L => f (T-L/2)) volume A B := by
  have h := (hi.symm.comp_sub_left T).comp_mul_left (c:=(1/2:ℝ))
  rw [show (T-(T-A/2))/(1/2:ℝ)=A by ring,show (T-(T-B/2))/(1/2:ℝ)=B by ring] at h
  have he : (fun L : ℝ => f (T-L/2))=fun L => f (T-(1/2:ℝ)*L) := by
    funext L
    congr 1
    ring
  rw [he]
  exact h

/-- The actual complete horizon trace integrated on the original truncated
static-time triangle, with its original radial one-half Jacobian. -/
def staticTraceCollar (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a A B T k : ℝ) : ℂ :=
  (∫ L in A..B,metricTrace q br amp w a (max a (T-L/2)) k)/2

/-- The original static geometry preserves both corner endpoints, even when
the terminal cutoff intersects the radial collar. The integrand is admitted
before the change of variables or any separation of its trace. -/
theorem static_trace_identity (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0 ≤ G ∧ ∀ w : ℂ,w.im≠0 → G+1 ≤ w.re → ∀ a A B T k : ℝ,
      0<a → A ≤ B → 0 ≤ k → 4 ≤ Real.exp k →
      IntervalIntegrable (fun L => metricTrace q br amp w a (max a (T-L/2)) k) volume A B ∧
      staticTraceCollar q br amp w a A B T k=
        (max a (T-A/2)-max a (T-B/2))•traceMass q br amp w k a+
          traceCorner q br amp w k (max a (T-A/2))-traceCorner q br amp w k (max a (T-B/2)) := by
  obtain ⟨G,hG,hg⟩ := trace_two_endpoint_identity q br amp
  refine ⟨G,hG,?_⟩
  intro w hwi hw a A B T k ha hAB hk hk4
  have hi := hg w hwi hw
  have hf0 : metricTrace q br amp w a a k=0 := by
    simp [metricTrace,horizonSourceFunctional,horizonBoundary]
  have hraw : T-B/2 ≤ T-A/2 := by linarith
  obtain ⟨hadmit,hchange⟩ := clamped_integral (fun b => metricTrace q br amp w a b k) a
    (T-B/2) (T-A/2) hraw hf0 (fun u v hau huv => (hi a u v k ha hau huv hk hk4).1)
  refine ⟨collar_admission (fun b => metricTrace q br amp w a (max a b) k) A B T hadmit,?_⟩
  rw [staticTraceCollar,collar_change_of_variables (fun b => metricTrace q br amp w a (max a b) k),hchange]
  exact (hi a (max a (T-B/2)) (max a (T-A/2)) k ha (le_max_left _ _)
    (max_le_max_left a hraw) hk hk4).2

/-- The entire retained static-time horizon trace restores uniformly after
its original source-derived mass subtraction, for arbitrary independent
terminal, radial and onset cutoffs in their positive physical domain. -/
theorem static_trace_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0 ≤ G ∧ ∀ w : ℂ,w.im≠0 → G+1 ≤ w.re → ∃ C : ℝ,0 ≤ C ∧ ∀ a A B T k : ℝ,
      0<a → A ≤ B → 0 ≤ k → 4 ≤ Real.exp k →
      IntervalIntegrable (fun L => metricTrace q br amp w a (max a (T-L/2)) k) volume A B ∧
      ‖staticTraceCollar q br amp w a A B T k-
        (max a (T-A/2)-max a (T-B/2))•traceMass q br amp w k a‖ ≤ C*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G1,hG1,h1⟩ := static_trace_identity q br amp
  obtain ⟨G2,_,h2⟩ := trace_corner_decay q br amp N
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  obtain ⟨C,hC,hc⟩ := h2 w (by linarith [le_max_right G1 G2])
  refine ⟨2*C,by positivity,?_⟩
  intro a A B T k ha hAB hk hk4
  refine ⟨(h1 w hwi (by linarith [le_max_left G1 G2]) a A B T k ha hAB hk hk4).1,?_⟩
  rw [(h1 w hwi (by linarith [le_max_left G1 G2]) a A B T k ha hAB hk hk4).2]
  have he : (max a (T-A/2)-max a (T-B/2))•traceMass q br amp w k a+
      traceCorner q br amp w k (max a (T-A/2))-traceCorner q br amp w k (max a (T-B/2))-
      (max a (T-A/2)-max a (T-B/2))•traceMass q br amp w k a=
      traceCorner q br amp w k (max a (T-A/2))-traceCorner q br amp w k (max a (T-B/2)) := by abel
  rw [he]
  have hb (p : ℝ) (hp : 0<p) : ‖traceCorner q br amp w k p‖ ≤ C*Real.exp (-(N:ℝ)*k) :=
    (hc p k hp hk).trans ((mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (by linarith : -p ≤ 0)) (by positivity)).trans_eq (mul_one _))
  exact (norm_sub_le _ _).trans ((add_le_add (hb _ (ha.trans_le (le_max_left _ _)))
    (hb _ (ha.trans_le (le_max_left _ _)))).trans_eq (by ring))

end
end RHTower.D4BMOriginalStaticTraceGeometry

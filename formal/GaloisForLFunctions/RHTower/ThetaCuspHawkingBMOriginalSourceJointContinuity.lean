import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalSourceRadialRestoration

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalSourceJointContinuity
open D4BMJointSource D4BMModularCore D4BMOriginalSourceTailCollar D4BMOriginalSourceTailAdmission
noncomputable section
set_option autoImplicit false

private theorem continuous_clamped {f : ℝ×ℝ→ℂ} {L0 a : ℝ} (ha : 0<a)
    (hf : ContinuousOn f (Ici L0 ×ˢ Ioi 0)) :
    Continuous (fun v : ℝ×ℝ => f (max L0 v.1,max a v.2)) := by
  rw [← continuousOn_univ]
  have hc : ContinuousOn (fun v : ℝ×ℝ => (max L0 v.1,max a v.2)) univ := by fun_prop
  have hm : MapsTo (fun v : ℝ×ℝ => (max L0 v.1,max a v.2)) univ (Ici L0 ×ˢ Ioi 0) := by
    intro v _
    change L0 ≤ max L0 v.1 ∧ 0 < max a v.2
    exact ⟨le_max_left _ _,ha.trans_le (le_max_left _ _)⟩
  exact hf.comp hc hm

/-- The literal scalar-period discrepancy is jointly continuous in positive
source time and horizon depth in the derived convergence chamber. The angular
integral has actual admission and one uniform dominating density. -/
theorem period_joint_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ L0 : ℝ,0<L0 ∧ ∀ k : ℝ,0≤k → 4≤Real.exp k →
      ContinuousOn (fun v : ℝ×ℝ => originalPeriodError q br amp w v.2 v.1 k) (Ici L0 ×ˢ Ioi 0) := by
  obtain ⟨G1,hG1,h1⟩ := source_tail_density_error q br amp 0
  obtain ⟨G2,_,h2⟩ := horizon_tail_density_bound q br amp 0
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1≤w.re := by linarith [le_max_right G1 G2]
  obtain ⟨C,hC,hc⟩ := h1 w hwi hw1
  obtain ⟨B,hB,hb⟩ := h2 w hw2
  obtain ⟨D,hD⟩ := eventually_atTop.mp hc
  let L0 := max D 1
  have hL0 : 0<L0 := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  refine ⟨L0,hL0,?_⟩
  intro k hk hk4
  let S := Ici L0 ×ˢ Ioi (0:ℝ)
  have hm : MeasurableSet (tailSet k) := measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable
  have hbound (v : ℝ×ℝ) (hv : v∈S) (z : UpperHalfPlane) (hz : z∈tailSet k) :
      ‖tailDensity q br amp w v.2 v.1 z‖≤C+B := by
    have hvL : 0<v.1 := hL0.trans_le hv.1
    have hvp : 0<v.2 := hv.2
    have he := hD v.1 ((le_max_left D 1).trans hv.1) v.2 k hv.2 hk z hz
    have hh := hb v.2 k hv.2 hk z hz
    simp only [Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero,mul_one] at he hh
    have ep : Real.exp (-v.2)≤1 := Real.exp_le_one_iff.mpr (by linarith [hvp])
    have eL : Real.exp (-v.1)≤1 := Real.exp_le_one_iff.mpr (by linarith)
    have he' : ‖tailDensity q br amp w v.2 v.1 z-horizonTailDensity q br amp w v.2 z‖≤C := by
      calc
        _ ≤ C*Real.exp (-v.1)*Real.exp (-v.2) := he
        _ ≤ C*1*1 := by gcongr
        _ = C := by ring
    have hh' : ‖horizonTailDensity q br amp w v.2 z‖≤B :=
      hh.trans ((mul_le_mul_of_nonneg_left ep hB).trans_eq (mul_one B))
    calc
      _ = ‖(tailDensity q br amp w v.2 v.1 z-horizonTailDensity q br amp w v.2 z)+
          horizonTailDensity q br amp w v.2 z‖ := by rw [sub_add_cancel]
      _ ≤ ‖tailDensity q br amp w v.2 v.1 z-horizonTailDensity q br amp w v.2 z‖+
          ‖horizonTailDensity q br amp w v.2 z‖ := norm_add_le _ _
      _ ≤ C+B := add_le_add he' hh'
  have hi : ContinuousOn (fun v : ℝ×ℝ => ∫ z in tailSet k,tailDensity q br amp w v.2 v.1 z ∂measure) S := by
    apply continuousOn_of_dominated
      (fun v hv => (tail_density_integrable q br amp w v.2 v.1 k hv.2 (hL0.trans_le hv.1) hk4).aestronglyMeasurable)
      (bound:=fun _ => C+B) _ (integrable_const _) _
    · intro v hv
      filter_upwards [ae_restrict_mem hm] with z hz
      exact hbound v hv z hz
    · apply Filter.Eventually.of_forall
      intro z v hv
      exact ((tail_density_joint_continuousAt q br amp w (v,z) (hL0.trans_le hv.1) hv.2).comp
        (f:=fun t : ℝ×ℝ => (t,z)) (show ContinuousAt (fun t : ℝ×ℝ => (t,z)) v by fun_prop)).continuousWithinAt
  exact hi.neg.congr (fun v hv => (original_period_error_tail q br amp w v.2 v.1 k hv.2
    (hL0.trans_le hv.1) hk4))

/-- Every continuous physical temporal endpoint moving through the radial
collar has genuine source-period admission, including affine static-time cuts. -/
theorem moving_endpoint_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ L0 : ℝ,0<L0 ∧
      ∀ (k A B : ℝ) (p : ℝ→ℝ),0≤k → 4≤Real.exp k → L0≤A → A≤B →
      ContinuousOn p (Icc A B) → (∀ L∈Icc A B,0<p L) →
      IntervalIntegrable (fun L => originalPeriodError q br amp w (p L) L k) volume A B := by
  obtain ⟨G,hG,hg⟩ := period_joint_continuous q br amp
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨L0,hL0,h⟩ := hg w hwi hw
  refine ⟨L0,hL0,?_⟩
  intro k A B p hk hk4 hA hAB hp hp0
  have hc := (h k hk hk4).comp (continuousOn_id.prodMk hp)
    (fun L hL => show (L,p L)∈Ici L0 ×ˢ Ioi (0:ℝ) from ⟨hA.trans hL.1,hp0 L hL⟩)
  exact hc.intervalIntegrable_of_Icc hAB


/-- The complete source endpoint/moment functional is radially admitted on
the actual static-time triangle. Clamping its upper endpoint to its lower
endpoint gives the empty physical time interval beyond that triangle. -/
theorem static_source_radial_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ L0 : ℝ,0<L0 ∧
      ∀ k A B a T : ℝ,0≤k → 4≤Real.exp k → L0≤A → A≤B → 0<a →
      IntervalIntegrable (fun L => D4BMOriginalSourceRadialRestoration.sourceFunctional
        q br amp w a (max a (T-L/2)) L k) volume A B := by
  obtain ⟨G,hG,hg⟩ := period_joint_continuous q br amp
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨L0,hL0,h⟩ := hg w hwi hw
  refine ⟨L0,hL0,?_⟩
  intro k A B a T hk hk4 hA hAB ha
  let F := fun L p : ℝ => originalPeriodError q br amp w (max a p) (max L0 L) k
  let u := fun L : ℝ => max a (T-L/2)
  have hu : Continuous u := by dsimp [u];fun_prop
  have hc : Continuous (fun v : ℝ×ℝ => F v.1 v.2) := by
    simpa only [F] using continuous_clamped ha (h k hk hk4)
  have hi : Continuous (fun L : ℝ => ∫ p in a..u L,F L p) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (f:=F) hc hu
  have ht := hc.comp (continuous_id.prodMk hu)
  have hb := hc.comp (continuous_id.prodMk (continuous_const (y:=a)))
  let m := D4BMLeftModeRadialEquation.eigenvalue q
  have hs := ((ht.sub hb).add (hi.const_mul (2*w))).const_mul (m*(m-2))
  have heq : ContinuousOn (fun L => D4BMOriginalSourceRadialRestoration.sourceFunctional
      q br amp w a (u L) L k) (Icc A B) := by
    apply hs.continuousOn.congr
    intro L hL
    have hL0L : L0≤L := hA.trans hL.1
    have hE (p : ℝ) (hp : a≤p) : F L p=originalPeriodError q br amp w p L k := by
      dsimp [F]
      rw [max_eq_right hp,max_eq_right hL0L]
    have hau : a≤u L := le_max_left _ _
    have hI : (∫ p in a..u L,F L p)=(∫ p in a..u L,originalPeriodError q br amp w p L k) := by
      apply intervalIntegral.integral_congr
      intro p hp
      have hp' : p∈Icc a (u L) := by simpa only [uIcc_of_le hau] using hp
      exact hE p hp'.1
    symm
    change m*(m-2)*(F L (u L)-F L a+2*w*(∫ p in a..u L,F L p))=_
    rw [hE (u L) hau,hE a le_rfl,hI]
    rfl
  exact heq.intervalIntegrable_of_Icc hAB

end
end RHTower.D4BMOriginalSourceJointContinuity

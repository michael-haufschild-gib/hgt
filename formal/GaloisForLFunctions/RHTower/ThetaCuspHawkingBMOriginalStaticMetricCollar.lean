import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalStaticTraceGeometry
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalSourceJointContinuity

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalStaticMetricCollar
open D4BMJointSource D4BMModularCore D4BMOriginalStaticTraceGeometry D4BMOriginalStaticTracePrimitive
open D4BMOriginalFullMetricCollar D4BMOriginalFullMetricDifference D4BMOriginalCompleteTransfer
open D4BMOriginalSourceRadialRestoration D4BMOriginalBoundaryRadialAdmission
noncomputable section
set_option autoImplicit false

private theorem clamped_period_continuous (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hwi : w.im≠0) (k A a : ℝ) (hA : 0<A) (ha : 0<a) (j : Fin 4) :
    Continuous (fun v : ℝ×ℝ => ∫ x in (-1/2:ℝ)..1/2,
      radialTransfer q br amp w j (max a v.2) (max A v.1) x k) := by
  have hc : Continuous (fun v : (ℝ×ℝ)×ℝ =>
      radialTransfer q br amp w j (max a v.1.2) (max A v.1.1) v.2 k) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have h := radial_transfer_joint_continuousAt q br amp w hwi k j
      (max A v.1.1,(max a v.1.2,v.2)) (hA.trans_le (le_max_left _ _)) (ha.trans_le (le_max_left _ _))
    exact h.comp (f:=fun v : (ℝ×ℝ)×ℝ => (max A v.1.1,(max a v.1.2,v.2)))
      (show ContinuousAt (fun v : (ℝ×ℝ)×ℝ => (max A v.1.1,(max a v.1.2,v.2))) v by fun_prop)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc (-1/2) (1/2)

/-- All original boundary endpoint and moment terms remain jointly admitted
on the actual moving static-time domain. The clamps used in the continuity
proof agree with the physical fields everywhere on this collar. -/
theorem static_boundary_radial_continuous (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hwi : w.im≠0) (k A B a T : ℝ) (hA : 0<A) (ha : 0<a) :
    ContinuousOn (fun L => radialBoundary q br amp w a (max a (T-L/2)) L k) (Icc A B) := by
  let P := fun (j : Fin 4) (L p : ℝ) => ∫ x in (-1/2:ℝ)..1/2,
    radialTransfer q br amp w j (max a p) (max A L) x k
  let u := fun L : ℝ => max a (T-L/2)
  let m := D4BMLeftModeRadialEquation.eigenvalue q
  have hu : Continuous u := by dsimp [u];fun_prop
  have hP (j : Fin 4) : Continuous (fun v : ℝ×ℝ => P j v.1 v.2) :=
    clamped_period_continuous q br amp w hwi k A a hA ha j
  have hI (j : Fin 4) : Continuous (fun L : ℝ => ∫ p in a..u L,P j L p) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (hP j) hu
  have hE := (hP 0).comp (continuous_id.prodMk hu)
  have hE0 := (hP 0).comp (continuous_id.prodMk (continuous_const (y:=a)))
  have hc := ((hE.sub hE0).const_mul (-(m-2))).add
    (((((hI 1).const_mul m).sub (hI 2)).sub ((hI 0).const_mul (2*(m-2)))).sub (hI 3) |>.const_mul w)
  apply hc.continuousOn.congr
  intro L hL
  have hEeq (j : Fin 4) (p : ℝ) (hp : a≤p) : P j L p=
      ∫ x in (-1/2:ℝ)..1/2,radialTransfer q br amp w j p L x k := by
    dsimp [P]
    rw [max_eq_right hp,max_eq_right hL.1]
  have hau : a≤u L := le_max_left _ _
  have hIeq (j : Fin 4) : (∫ p in a..u L,P j L p)=
      ∫ p in a..u L,∫ x in (-1/2:ℝ)..1/2,radialTransfer q br amp w j p L x k := by
    apply intervalIntegral.integral_congr
    intro p hp
    have hp' : p∈Icc a (u L) := by simpa only [uIcc_of_le hau] using hp
    exact hEeq j p hp'.1
  symm
  change -(m-2)*(P 0 L (u L)-P 0 L a)+w*(m*(∫ p in a..u L,P 1 L p)-
    (∫ p in a..u L,P 2 L p)-2*(m-2)*(∫ p in a..u L,P 0 L p)-(∫ p in a..u L,P 3 L p))=_
  rw [hEeq 0 (u L) hau,hEeq 0 a le_rfl,hIeq 1,hIeq 2,hIeq 0,hIeq 3]
  rfl

theorem static_boundary_radial_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hwi : w.im≠0) (k A B a T : ℝ) (hA : 0<A) (hAB : A≤B) (ha : 0<a) :
    IntervalIntegrable (fun L => radialBoundary q br amp w a (max a (T-L/2)) L k) volume A B :=
  (static_boundary_radial_continuous q br amp w hwi k A B a T hA ha).intervalIntegrable_of_Icc hAB

/-- Separate radial admission of the complete original moving metric density
with its literal forcing moment retained on the other side of the identity. -/
theorem static_metric_source_boundary_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ L0 : ℝ,0<L0 ∧ ∀ a A B T k : ℝ,
      0<a → L0≤A → A≤B → 0≤k → 4≤Real.exp k →
      IntervalIntegrable (fun L => metricDifference q br amp w a (max a (T-L/2)) L k-
        forcingMoment q br amp w a (max a (T-L/2)) L k) volume A B := by
  obtain ⟨G,hG,hg⟩ := D4BMOriginalSourceJointContinuity.static_source_radial_integrable q br amp
  refine ⟨G,hG,?_⟩
  intro w hwi hw
  obtain ⟨L0,hL0,h⟩ := hg w hwi hw
  refine ⟨L0,hL0,?_⟩
  intro a A B T k ha hA hAB hk hk4
  have hi := (h k A B a T hk hk4 hA hAB ha).add
    (static_boundary_radial_integrable q br amp w hwi k A B a T (hL0.trans_le hA) hAB ha)
  apply hi.congr
  intro L hL
  have hL' : L∈Ioc A B := by simpa only [uIoc_of_le hAB] using hL
  have hm := original_full_metric_difference q br amp w hwi a (max a (T-L/2)) L k
    ha (le_max_left _ _) ((hL0.trans_le hA).trans hL'.1) hk4
  change metricDifference q br amp w a (max a (T-L/2)) L k=
    sourceFunctional q br amp w a (max a (T-L/2)) L k+
      forcingMoment q br amp w a (max a (T-L/2)) L k+radialBoundary q br amp w a (max a (T-L/2)) L k at hm
  dsimp only
  rw [hm]
  ring

/-- The source/boundary part of the actual moving metric collar, with its
source-derived mass term and both temporal endpoints kept in the physical cut. -/
def staticMetricDifference (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a A B T k : ℝ) : ℂ :=
  (∫ L in A..B,metricDifference q br amp w a (max a (T-L/2)) L k-
    forcingMoment q br amp w a (max a (T-L/2)) L k)/2-
    (max a (T-A/2)-max a (T-B/2))•traceMass q br amp w k a

/-- The complete actual source/boundary metric discrepancy restores on the
original moving static-time collar. Its bound is uniform over arbitrary
positive onset, terminal and radial cutoffs, with no relative cutoff rates. -/
theorem static_metric_source_boundary_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ C L0 : ℝ,0≤C ∧ 0<L0 ∧
      ∀ a A B T k : ℝ,0<a → L0≤A → A≤B → 0≤k → 4≤Real.exp k →
        ‖staticMetricDifference q br amp w a A B T k‖≤C*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G1,hG1,h1⟩ := metric_error_bound q br amp N
  obtain ⟨G2,_,h2⟩ := static_metric_source_boundary_integrable q br amp
  obtain ⟨G3,_,h3⟩ := static_trace_bound q br amp N
  refine ⟨max G1 (max G2 G3),le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  obtain ⟨C,hC,hc⟩ := h1 w hwi (by linarith [le_max_left G1 (max G2 G3)])
  obtain ⟨D,hD⟩ := eventually_atTop.mp hc
  obtain ⟨L2,hL2,hi⟩ := h2 w hwi (by linarith [(le_max_left G2 G3).trans (le_max_right G1 (max G2 G3))])
  obtain ⟨E,hE,he⟩ := h3 w hwi (by linarith [(le_max_right G2 G3).trans (le_max_right G1 (max G2 G3))])
  let L0 := max D L2
  have hL0 : 0<L0 := hL2.trans_le (le_max_right _ _)
  refine ⟨C+E,L0,add_nonneg hC hE,hL0,?_⟩
  intro a A B T k ha hA hAB hk hk4
  have hAp := hL0.trans_le hA
  have hIA := hi a A B T k ha ((le_max_right D L2).trans hA) hAB hk hk4
  obtain ⟨hIH,htrace⟩ := he a A B T k ha hAB hk hk4
  have herror : ‖∫ L in A..B,metricError q br amp w a (max a (T-L/2)) L k‖≤C*Real.exp (-(N:ℝ)*k) := by
    have hb := exponential_interval_bound (fun L => metricError q br amp w a (max a (T-L/2)) L k)
      (C*Real.exp (-(N:ℝ)*k)) A B (by positivity) hAB (fun L hL => by
        have h := hD L ((le_max_left D L2).trans (hA.trans hL.1)) a (max a (T-L/2)) k
          ha (le_max_left _ _) hk hk4
        simpa only [mul_comm,mul_left_comm,mul_assoc] using h)
    exact hb.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith : -A≤0))
      (by positivity)).trans_eq (mul_one _))
  have hdiv : ‖(∫ L in A..B,metricError q br amp w a (max a (T-L/2)) L k)/2‖≤C*Real.exp (-(N:ℝ)*k) := by
    rw [norm_div,Complex.norm_ofNat]
    exact (div_le_div_of_nonneg_right herror (by norm_num)).trans (by nlinarith [Real.exp_nonneg (-(N:ℝ)*k)])
  have hsplit : staticMetricDifference q br amp w a A B T k=
      (∫ L in A..B,metricError q br amp w a (max a (T-L/2)) L k)/2+
        (staticTraceCollar q br amp w a A B T k-
          (max a (T-A/2)-max a (T-B/2))•traceMass q br amp w k a) := by
    unfold staticMetricDifference metricError staticTraceCollar
    rw [intervalIntegral.integral_sub hIA hIH]
    ring
  rw [hsplit]
  exact (norm_add_le _ _).trans ((add_le_add hdiv htrace).trans_eq (by ring))

end
end RHTower.D4BMOriginalStaticMetricCollar

import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringKernel
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCoprimeSource
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Complex

/-! Uniform complex-period kernel estimates realize the continued lattice
response in the actual Mayer disc algebra. The bounded head and exponentially
decaying tail have Banach-valued Mellin transforms. -/

open Complex Set Filter Metric Topology MeasureTheory Asymptotics
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerScatteringKernel
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringMellin

private theorem period_mem {z : ℂ} (hz : z ∈ outer) :
    1+z ∈ closedBall (2 : ℂ) (3/2 : ℝ) := by
  rw [mem_closedBall,dist_eq_norm]
  have he : (1+z)-2=z-1 := by ring
  rw [he]
  simpa only [outer,mem_closedBall,dist_eq_norm] using hz

private theorem period_re_pos {z : ℂ} (hz : z ∈ outer) : 0 < (1+z).re := by
  have hr := (neg_le_abs (z-1).re).trans (Complex.abs_re_le_norm (z-1))
  have hd : ‖z-1‖ ≤ (3/2 : ℝ) := by simpa only [outer,mem_closedBall,dist_eq_norm] using hz
  simp only [Complex.sub_re,Complex.one_re] at hr
  simp only [Complex.add_re,Complex.one_re]
  linarith only [hr,hd]

private theorem head_differentiableOn (t : ℝ) :
    DifferentiableOn ℂ (fun z : ℂ => regularKernel (1+z) ((|t| : ℝ) : ℂ)) outer := by
  intro z hz
  exact ((analyticAt_regularKernel_period (period_re_pos hz) (abs_nonneg t)).comp
    (f := fun z : ℂ => 1+z) (analyticAt_const.add analyticAt_id)).differentiableAt.differentiableWithinAt

private theorem tail_differentiableOn (t : ℝ) :
    DifferentiableOn ℂ (fun z : ℂ => kernel (1+z) ((max 1 t : ℝ) : ℂ)) outer := by
  intro z hz
  have ht : 0 < max 1 t := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact ((analyticAt_kernel_period (period_re_pos hz) ht).comp
    (f := fun z : ℂ => 1+z) (analyticAt_const.add analyticAt_id)).differentiableAt.differentiableWithinAt

/-- Actual regular head kernel; absolute value extends it continuously to negative inputs. -/
def headDisc (t : ℝ) : DiscSpace :=
  ofHolomorphic (fun z => regularKernel (1+z) ((|t| : ℝ) : ℂ))
    (head_differentiableOn t).continuousOn ((head_differentiableOn t).mono ball_subset_closedBall)

/-- Actual tail kernel, continuously held fixed below the tail cutoff. -/
def tailDisc (t : ℝ) : DiscSpace :=
  ofHolomorphic (fun z => kernel (1+z) ((max 1 t : ℝ) : ℂ))
    (tail_differentiableOn t).continuousOn ((tail_differentiableOn t).mono ball_subset_closedBall)

@[simp] theorem headDisc_apply (t : ℝ) (z : Disc) :
    (headDisc t).1 z=regularKernel (1+z.1) ((|t| : ℝ) : ℂ) := rfl

@[simp] theorem tailDisc_apply (t : ℝ) (z : Disc) :
    (tailDisc t).1 z=kernel (1+z.1) ((max 1 t : ℝ) : ℂ) := rfl

/-- Joint continuity of the regular kernel gives continuity in the actual uniform disc norm. -/
theorem continuous_headDisc : Continuous headDisc := by
  have hv : Continuous (fun t => (headDisc t).1) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply continuous_iff_continuousAt.mpr
    intro p
    have h := continuousAt_regularKernel (period_re_pos p.2.property) (abs_nonneg p.1)
    change ContinuousAt (fun q : ℝ × Disc => regularKernel (1+q.2.1) ((|q.1| : ℝ) : ℂ)) p
    exact h.comp (f := fun q : ℝ × Disc => (1+q.2.1,|q.1|)) (x := p) (by fun_prop)
  exact hv.subtype_mk (fun t => (headDisc t).property)

/-- Joint continuity of the tail kernel also holds in the uniform disc norm. -/
theorem continuous_tailDisc : Continuous tailDisc := by
  have hv : Continuous (fun t => (tailDisc t).1) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply continuous_iff_continuousAt.mpr
    intro p
    have ht : 0 < max 1 p.1 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have h := continuousAt_kernel (period_re_pos p.2.property) ht
    change ContinuousAt (fun q : ℝ × Disc => kernel (1+q.2.1) ((max 1 q.1 : ℝ) : ℂ)) p
    exact h.comp (f := fun q : ℝ × Disc => (1+q.2.1,max 1 q.1)) (x := p) (by fun_prop)
  exact hv.subtype_mk (fun t => (tailDisc t).property)

/-- A single uniform disc norm bounds the entire regular Mellin head. -/
theorem headDisc_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖headDisc t‖ ≤ C := by
  obtain ⟨C,hC⟩ := regularKernel_uniform_bound
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro t ht
  change ‖(headDisc t).1‖ ≤ _
  apply (ContinuousMap.norm_le _ (le_max_right _ _)).mpr
  intro z
  rw [headDisc_apply,abs_of_nonneg ht.1]
  exact (hC (1+z.1) (period_mem z.property) t ht).trans (le_max_left _ _)

/-- The actual disc-valued tail has one exponential norm majorant. -/
theorem tailDisc_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ‖tailDisc t‖ ≤ C*Real.exp (-t/2) := by
  obtain ⟨C,hC,hbound⟩ := kernel_uniform_tail_bound
  refine ⟨C,hC,?_⟩
  intro t ht
  change ‖(tailDisc t).1‖ ≤ _
  apply (ContinuousMap.norm_le _ (mul_nonneg hC.le (Real.exp_pos _).le)).mpr
  intro z
  rw [tailDisc_apply,max_eq_right ht]
  exact hbound (1+z.1) (period_mem z.property) t ht

/-- Supported regular head for the Banach-valued Mellin transform. -/
def headInput : ℝ → DiscSpace := Set.indicator (Ioc (0 : ℝ) 1) headDisc

/-- Supported exponentially decaying tail for the Banach-valued Mellin transform. -/
def tailInput : ℝ → DiscSpace := Set.indicator (Ioi (1 : ℝ)) tailDisc

private theorem integrableOn_headInput : IntegrableOn headInput (Ioi (0 : ℝ)) := by
  have hi : IntegrableOn headDisc (Ioc (0 : ℝ) 1) :=
    (continuous_headDisc.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      (fun t ht => ⟨ht.1.le,ht.2⟩)
  rw [headInput,IntegrableOn,integrable_indicator_iff measurableSet_Ioc,
    IntegrableOn,Measure.restrict_restrict measurableSet_Ioc,
    show Ioc (0 : ℝ) 1 ∩ Ioi (0 : ℝ)=Ioc (0 : ℝ) 1 from
      Set.inter_eq_left.mpr (fun t ht => ht.1)]
  exact hi

private theorem decay_rewrite (t : ℝ) : -t/2=-(1/2 : ℝ)*t := by ring

private theorem integrableOn_tailInput : IntegrableOn tailInput (Ioi (0 : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := tailDisc_uniform_bound
  have hdom : IntegrableOn (fun t : ℝ => C*Real.exp (-(1/2 : ℝ)*t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi (0 : ℝ) (b := 1/2) (by norm_num)).const_mul C
  refine Integrable.mono' hdom
    (continuous_tailDisc.aestronglyMeasurable.indicator measurableSet_Ioi) ?_
  filter_upwards with t
  by_cases ht : t ∈ Ioi (1 : ℝ)
  · rw [tailInput,Set.indicator_of_mem ht]
    simpa only [decay_rewrite] using hbound t ht.le
  · rw [tailInput,Set.indicator_of_notMem ht,norm_zero]
    exact mul_nonneg hC.le (Real.exp_pos _).le

private theorem headInput_top (a : ℝ) :
    headInput =O[atTop] fun t : ℝ => t^(-a) := by
  refine Filter.EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  exact Set.indicator_of_notMem (fun hmem : t ∈ Ioc (0 : ℝ) 1 => not_le.mpr ht hmem.2) _

private theorem headInput_zero :
    headInput =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t^(-(0 : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := headDisc_uniform_bound
  refine Asymptotics.isBigO_iff.mpr ⟨C,?_⟩
  filter_upwards with t
  simp only [neg_zero,Real.rpow_zero,norm_one,mul_one]
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · rw [headInput,Set.indicator_of_mem ht]
    exact hbound t ⟨ht.1.le,ht.2⟩
  · rw [headInput,Set.indicator_of_notMem ht,norm_zero]
    exact hC

private theorem tailInput_top :
    tailInput =O[atTop] fun t : ℝ => Real.exp (-(1/2 : ℝ)*t) := by
  obtain ⟨C,hC,hbound⟩ := tailDisc_uniform_bound
  refine Asymptotics.isBigO_iff.mpr ⟨C,?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have htI : t ∈ Ioi (1 : ℝ) := ht
  rw [tailInput,Set.indicator_of_mem htI,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  simpa only [decay_rewrite] using hbound t ht.le

private theorem tailInput_zero :
    tailInput =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t^(-(0 : ℝ)) := by
  refine Filter.EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
  exact Set.indicator_of_notMem (fun hmem : t ∈ Ioi (1 : ℝ) => not_lt.mpr ht.2.le hmem) _

/-- The regular head is absolutely Mellin integrable in the disc norm. -/
theorem mellinConvergent_headInput {w : ℂ} (hw : 0 < w.re) :
    MellinConvergent headInput w :=
  mellinConvergent_of_isBigO_rpow
    (fun _ _ => ⟨Ioi 0,self_mem_nhdsWithin,integrableOn_headInput⟩)
    (headInput_top (w.re+1)) (by linarith only [hw]) headInput_zero hw

/-- The exponentially decaying tail is absolutely Mellin integrable in the disc norm. -/
theorem mellinConvergent_tailInput {w : ℂ} (hw : 0 < w.re) :
    MellinConvergent tailInput w :=
  mellinConvergent_of_isBigO_rpow_exp (by norm_num : (0 : ℝ) < 1/2)
    (fun _ _ => ⟨Ioi 0,self_mem_nhdsWithin,integrableOn_tailInput⟩)
    tailInput_top tailInput_zero hw

/-- Evaluation commutes with the absolutely convergent regular head integral. -/
theorem headMellin_apply {w : ℂ} (hw : 0 < w.re) (z : Disc) :
    (mellin headInput w).1 z=
      ∫ t in Ioc (0 : ℝ) 1, (t : ℂ)^(w-1)*regularKernel (1+z.1) (t : ℂ) := by
  change evaluation z (mellin headInput w)=_
  rw [mellin,← (evaluation z).integral_comp_comm (mellinConvergent_headInput hw)]
  have he : (fun t : ℝ => evaluation z ((t : ℂ)^(w-1) • headInput t))=
      Set.indicator (Ioc (0 : ℝ) 1)
        (fun t : ℝ => (t : ℂ)^(w-1)*regularKernel (1+z.1) (t : ℂ)) := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · simp only [headInput,Set.indicator_of_mem ht,map_smul,evaluation_apply,
        headDisc_apply,abs_of_nonneg ht.1.le,smul_eq_mul]
    · simp only [headInput,Set.indicator_of_notMem ht,smul_zero,map_zero]
  rw [he,integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_left.mpr (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from fun t ht => ht.1)]

/-- Evaluation commutes with the absolutely convergent exponential tail integral. -/
theorem tailMellin_apply {w : ℂ} (hw : 0 < w.re) (z : Disc) :
    (mellin tailInput w).1 z=
      ∫ t in Ioi (1 : ℝ), (t : ℂ)^(w-1)*kernel (1+z.1) (t : ℂ) := by
  change evaluation z (mellin tailInput w)=_
  rw [mellin,← (evaluation z).integral_comp_comm (mellinConvergent_tailInput hw)]
  have he : (fun t : ℝ => evaluation z ((t : ℂ)^(w-1) • tailInput t))=
      Set.indicator (Ioi (1 : ℝ))
        (fun t : ℝ => (t : ℂ)^(w-1)*kernel (1+z.1) (t : ℂ)) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp only [tailInput,Set.indicator_of_mem ht,map_smul,evaluation_apply,
        tailDisc_apply,max_eq_right (le_of_lt (show (1 : ℝ) < t from ht)),smul_eq_mul]
    · simp only [tailInput,Set.indicator_of_notMem ht,smul_zero,map_zero]
  rw [he,integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_left.mpr (show Ioi (1 : ℝ) ⊆ Ioi 0 from
      fun t ht => show (0 : ℝ) < t from lt_trans zero_lt_one ht)]

/-- The actual disc-valued head Mellin transform is holomorphic on the right half-plane. -/
theorem differentiableAt_headMellin {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (mellin headInput) w :=
  mellin_differentiableAt_of_isBigO_rpow
    (fun _ _ => ⟨Ioi 0,self_mem_nhdsWithin,integrableOn_headInput⟩)
    (headInput_top (w.re+1)) (by linarith only [hw]) headInput_zero hw

/-- The actual disc-valued tail Mellin transform is holomorphic on the same half-plane. -/
theorem differentiableAt_tailMellin {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (mellin tailInput) w :=
  mellin_differentiableAt_of_isBigO_rpow_exp (by norm_num : (0 : ℝ) < 1/2)
    (fun _ _ => ⟨Ioi 0,self_mem_nhdsWithin,integrableOn_tailInput⟩)
    tailInput_top tailInput_zero hw

/-- Continued lattice response, with the sole explicit source pole at two. -/
def state (w : ℂ) : DiscSpace :=
  (Complex.Gamma w)⁻¹ •
    ((2/(w-2)) • MayerCoprimeSource.endpoint 1+mellin headInput w+mellin tailInput w)

/-- Scalar evaluation of the continued disc-valued response. -/
theorem state_apply {w : ℂ} (hw : 0 < w.re) (z : Disc) :
    (state w).1 z=(Complex.Gamma w)⁻¹ *
      ((2/(w-2))*(1+z.1)⁻¹+
        (∫ t in Ioc (0 : ℝ) 1, (t : ℂ)^(w-1)*regularKernel (1+z.1) (t : ℂ))+
        (∫ t in Ioi (1 : ℝ), (t : ℂ)^(w-1)*kernel (1+z.1) (t : ℂ))) := by
  change evaluation z (state w)=_
  simp only [state,map_smul,map_add,evaluation_apply,MayerCoprimeSource.endpoint_apply,
    Complex.cpow_neg_one,smul_eq_mul,headMellin_apply hw,tailMellin_apply hw]

/-- The continued response is holomorphic in the actual disc norm away from its pole at two. -/
theorem analyticAt_state {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2) :
    AnalyticAt ℂ state w := by
  have hG : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n hn
    have hr := congrArg Complex.re hn
    simp only [Complex.neg_re,Complex.natCast_re] at hr
    linarith only [hr,hw,Nat.cast_nonneg (α := ℝ) n]
  have hGa : AnalyticAt ℂ Complex.Gamma w :=
    (Meromorphic.Gamma w).analyticAt (Complex.continuousAt_Gamma _ hG)
  have hhalf : {v : ℂ | 0 < v.re} ∈ 𝓝 w :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw
  have hH : AnalyticAt ℂ (mellin headInput) w :=
    (show DifferentiableOn ℂ (mellin headInput) {v : ℂ | 0 < v.re} from
      fun v hv => (differentiableAt_headMellin hv).differentiableWithinAt).analyticAt hhalf
  have hT : AnalyticAt ℂ (mellin tailInput) w :=
    (show DifferentiableOn ℂ (mellin tailInput) {v : ℂ | 0 < v.re} from
      fun v hv => (differentiableAt_tailMellin hv).differentiableWithinAt).analyticAt hhalf
  exact (hGa.inv (Complex.Gamma_ne_zero hG)).smul
    (((analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hw2)).smul
      analyticAt_const).add hH |>.add hT)

#print axioms continuous_headDisc
#print axioms continuous_tailDisc
#print axioms headDisc_uniform_bound
#print axioms tailDisc_uniform_bound
#print axioms mellinConvergent_headInput
#print axioms mellinConvergent_tailInput
#print axioms headMellin_apply
#print axioms tailMellin_apply
#print axioms state_apply
#print axioms differentiableAt_headMellin
#print axioms differentiableAt_tailMellin
#print axioms analyticAt_state
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringMellin

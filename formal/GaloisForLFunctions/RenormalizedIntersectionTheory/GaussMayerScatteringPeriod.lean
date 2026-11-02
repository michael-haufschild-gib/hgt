import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringState

/-! Inversion of the real period exchanges the two boundary Barnes cones
of the actual Mayer scattering state. Pole clearing continues the resulting
reciprocity and the three-term Lewis relation through the full source half-plane. -/

open Complex Set Filter Metric Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerScatteringMellin MayerScatteringState
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringPeriod

/-- Real periods whose translated points belong to the actual closed Mayer disc. -/
def periodSegment : Set ℝ := Icc (1/2) (7/2)

private theorem period_point_mem {a : ℝ} (ha : a ∈ periodSegment) :
    (a : ℂ)-1 ∈ outer := by
  have he : ((a : ℂ)-1)-1=((a-2 : ℝ) : ℂ) := by push_cast; ring
  rw [outer,mem_closedBall,dist_eq_norm,he,Complex.norm_real,Real.norm_eq_abs,abs_le]
  constructor <;> linarith only [ha.1,ha.2]

/-- The actual real-period value, using the existing disc representative. -/
def periodValue (w : ℂ) (a : ℝ) : ℂ := plane (state w) ((a : ℂ)-1)

private def clearedPeriod (w : ℂ) (a : ℝ) : ℂ := plane (clearedState w) ((a : ℂ)-1)

private def periodPoint (a : ℝ) (ha : a ∈ periodSegment) : Disc :=
  ⟨(a : ℂ)-1,period_point_mem ha⟩

private theorem periodValue_evaluation (w : ℂ) {a : ℝ} (ha : a ∈ periodSegment) :
    periodValue w a=evaluation (periodPoint a ha) (state w) :=
  plane_eq (state w) (periodPoint a ha)

private theorem clearedPeriod_evaluation (w : ℂ) {a : ℝ} (ha : a ∈ periodSegment) :
    clearedPeriod w a=evaluation (periodPoint a ha) (clearedState w) :=
  plane_eq (clearedState w) (periodPoint a ha)

private theorem analyticAt_clearedPeriod {w : ℂ} (hw : 0 < w.re)
    {a : ℝ} (ha : a ∈ periodSegment) :
    AnalyticAt ℂ (fun v => clearedPeriod v a) w := by
  have he : (fun v => clearedPeriod v a)=
      fun v => evaluation (periodPoint a ha) (clearedState v) :=
    funext (fun v => clearedPeriod_evaluation v ha)
  rw [he]
  have hd : DifferentiableOn ℂ (fun v => evaluation (periodPoint a ha) (clearedState v))
      {v : ℂ | 0 < v.re} := by
    intro v hv
    exact ((differentiableAt_const (evaluation (periodPoint a ha))).clm_apply
      (analyticAt_clearedState hv).differentiableAt).differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw)

private theorem clearedPeriod_eq {w : ℂ} (hw2 : w ≠ 2) {a : ℝ} (ha : a ∈ periodSegment) :
    clearedPeriod w a=(w-2)*periodValue w a := by
  rw [clearedPeriod_evaluation w ha,clearedState_eq hw2,map_smul,
    ← periodValue_evaluation w ha,smul_eq_mul]

/-- In the absolute chamber, the real period value is the sum of its two boundary Barnes series. -/
theorem periodValue_barnes {w : ℂ} (hw : 2 < w.re) {a : ℝ} (ha : a ∈ periodSegment) :
    periodValue w a=barnesDoubleZeta a 1 w 1+barnesDoubleZeta a 1 w (a : ℂ) := by
  rw [periodValue_evaluation w ha,evaluation_apply]
  have hz : (periodPoint a ha).1=((a-1 : ℝ) : ℂ) := by
    change (a : ℂ)-1=((a-1 : ℝ) : ℂ)
    push_cast; rfl
  rw [MayerScatteringChamber.state_apply_real hw (periodPoint a ha) (a-1) hz,
    show (1+(a-1) : ℝ)=a by ring]

/-- Scaling the reciprocal cone and swapping its lattice coordinates gives the original cone. -/
private theorem barnes_reciprocal_scale {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (w : ℂ) :
    (a : ℂ)^(-w)*barnesDoubleZeta (1/a) 1 w (x : ℂ)=
      barnesDoubleZeta a 1 w ((a*x : ℝ) : ℂ) := by
  rw [barnesDoubleZeta,barnesDoubleZeta,← tsum_mul_left,
    ← (Equiv.prodComm ℕ ℕ).tsum_eq
      (fun p => (((a*x : ℝ) : ℂ)+(barnesLattice a 1 p : ℂ))^(-w))]
  apply tsum_congr
  intro p
  have hb : 0 ≤ x+barnesLattice (1/a) 1 p :=
    (add_pos_of_pos_of_nonneg hx
      (barnesLattice_nonneg (one_div_pos.mpr ha).le zero_le_one p)).le
  have hr : a*(x+barnesLattice (1/a) 1 p)=a*x+barnesLattice a 1 p.swap := by
    simp only [barnesLattice,Prod.fst_swap,Prod.snd_swap,mul_one]
    field_simp [ha.ne']; ring
  have hc : (x : ℂ)+(barnesLattice (1/a) 1 p : ℂ)=
      ((x+barnesLattice (1/a) 1 p : ℝ) : ℂ) := by push_cast; rfl
  rw [hc,← Complex.mul_cpow_ofReal_nonneg ha.le hb,← Complex.ofReal_mul,hr]
  simp only [Complex.ofReal_add,Equiv.prodComm_apply]

private theorem reciprocal_segment {a : ℝ} (ha : a ∈ Icc (1/2 : ℝ) 2) :
    a ∈ periodSegment ∧ 1/a ∈ periodSegment := by
  have hp : 0 < a := by linarith only [ha.1]
  refine ⟨⟨ha.1,by linarith only [ha.2]⟩,⟨?_,?_⟩⟩
  · apply (le_div_iff₀ hp).mpr
    linarith only [ha.2]
  · have hi : 1/a ≤ 2 := (div_le_iff₀ hp).mpr (by linarith only [ha.1])
    linarith only [hi]

/-- Literal inversion reciprocity of the convergent actual scattering state. -/
theorem reciprocity_absolute {w : ℂ} (hw : 2 < w.re)
    {a : ℝ} (ha : a ∈ Icc (1/2 : ℝ) 2) :
    periodValue w a=(a : ℂ)^(-w)*periodValue w (1/a) := by
  have hp : 0 < a := by linarith only [ha.1]
  obtain ⟨har,hair⟩ := reciprocal_segment ha
  have h1 := barnes_reciprocal_scale hp zero_lt_one w
  have hi := barnes_reciprocal_scale hp (one_div_pos.mpr hp) w
  have he : a*(1/a)=1 := by field_simp [hp.ne']
  rw [mul_one,Complex.ofReal_one] at h1
  rw [he,Complex.ofReal_one] at hi
  rw [periodValue_barnes hw har,periodValue_barnes hw hair,mul_add,h1,hi,add_comm]

private def reciprocalDefect (a : ℝ) (w : ℂ) : ℂ :=
  clearedPeriod w a-(a : ℂ)^(-w)*clearedPeriod w (1/a)

private theorem analyticOn_reciprocalDefect {a : ℝ} (ha : a ∈ Icc (1/2 : ℝ) 2) :
    AnalyticOnNhd ℂ (reciprocalDefect a) {w : ℂ | 0 < w.re} := by
  have hp : 0 < a := by linarith only [ha.1]
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hd : Differentiable ℂ (fun w : ℂ => (a : ℂ)^(-w)) := by
    simp only [Complex.cpow_def_of_ne_zero ha0]
    fun_prop
  obtain ⟨har,hair⟩ := reciprocal_segment ha
  have hf : DifferentiableOn ℂ (reciprocalDefect a) {w : ℂ | 0 < w.re} := by
    intro w hw
    exact ((analyticAt_clearedPeriod hw har).differentiableAt.sub
      ((hd w).mul (analyticAt_clearedPeriod hw hair).differentiableAt)).differentiableWithinAt
  exact hf.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

private theorem reciprocalDefect_absolute {w : ℂ} (hw : 2 < w.re)
    {a : ℝ} (ha : a ∈ Icc (1/2 : ℝ) 2) : reciprocalDefect a w=0 := by
  have hw2 : w ≠ 2 := by intro he; norm_num [he] at hw
  obtain ⟨har,hair⟩ := reciprocal_segment ha
  rw [reciprocalDefect,clearedPeriod_eq hw2 har,clearedPeriod_eq hw2 hair,
    reciprocity_absolute hw ha]
  ring

/-- The filled reciprocity identity holds throughout the source half-plane. -/
private theorem reciprocalDefect_zero {w : ℂ} (hw : 0 < w.re)
    {a : ℝ} (ha : a ∈ Icc (1/2 : ℝ) 2) : reciprocalDefect a w=0 := by
  have he : reciprocalDefect a =ᶠ[𝓝 (3 : ℂ)] 0 := by
    have ho : IsOpen {v : ℂ | 2 < v.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (3 : ℂ) ∈ {v : ℂ | 2 < v.re} by norm_num)] with v hv
    exact reciprocalDefect_absolute hv ha
  exact (analyticOn_reciprocalDefect ha).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    MayerCofactorContinuation.rightHalfPlane_preconnected (by norm_num) he hw

/-- Inversion reciprocity for the actual continued state, including the source parameter one. -/
theorem reciprocity {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2)
    {a : ℝ} (ha : a ∈ Icc (1/2 : ℝ) 2) :
    periodValue w a=(a : ℂ)^(-w)*periodValue w (1/a) := by
  obtain ⟨har,hair⟩ := reciprocal_segment ha
  have he := reciprocalDefect_zero hw ha
  rw [reciprocalDefect,clearedPeriod_eq hw2 har,clearedPeriod_eq hw2 hair] at he
  apply mul_left_cancel₀ (sub_ne_zero.mpr hw2)
  linear_combination he

/-- Evaluation of the convergent transfer series at a real period. -/
private theorem transfer_hasSum {w : ℂ} (hw : 1 < w.re) (f : DiscSpace)
    {a : ℝ} (ha : a ∈ periodSegment) :
    HasSum (fun j : ℕ => ((j : ℂ)+(a : ℂ))^(-w)*
      plane f (((j : ℂ)+(a : ℂ))⁻¹))
      (evaluation (periodPoint a ha) (regularized w (zero_lt_one.trans hw) f)) := by
  have h := (evaluation (periodPoint a ha)).hasSum
    ((ContinuousLinearMap.apply ℂ DiscSpace f).hasSum
      (summable_norm_branch hw).of_norm.hasSum)
  rw [← regularized_eq_tsum_branch hw] at h
  change HasSum (fun j : ℕ => evaluation (periodPoint a ha)
    (branch w (zero_lt_one.trans hw) (j+1) (by omega) f))
    (evaluation (periodPoint a ha) (regularized w (zero_lt_one.trans hw) f)) at h
  convert h using 1
  ext j
  rw [evaluation_apply,branch_apply]
  congr 2 <;> push_cast <;> dsimp [periodPoint] <;> ring

private theorem shift_segments {a : ℝ} (ha : a ∈ Icc (1 : ℝ) 2) :
    a ∈ periodSegment ∧ a+1 ∈ periodSegment ∧
      1+1/a ∈ Icc (1/2 : ℝ) 2 := by
  have hp : 0 < a := lt_of_lt_of_le zero_lt_one ha.1
  have hi : 1/a ≤ 1 := (div_le_iff₀ hp).mpr (by linarith only [ha.1])
  have hi0 := one_div_pos.mpr hp
  exact ⟨⟨by linarith only [ha.1],by linarith only [ha.2]⟩,
    ⟨by linarith only [ha.1],by linarith only [ha.2]⟩,
    ⟨by linarith only [hi0],by linarith only [hi]⟩⟩

/-- Translating the real argument removes exactly the first Gauss branch. -/
private theorem transfer_shift {w : ℂ} (hw : 1 < w.re) (f : DiscSpace)
    {a : ℝ} (ha : a ∈ Icc (1 : ℝ) 2) :
    evaluation (periodPoint a (shift_segments ha).1) (regularized w (zero_lt_one.trans hw) f)=
      (a : ℂ)^(-w)*plane f ((a : ℂ)⁻¹)+
        evaluation (periodPoint (a+1) (shift_segments ha).2.1)
          (regularized w (zero_lt_one.trans hw) f) := by
  have h := transfer_hasSum hw f (shift_segments ha).1
  have h' := transfer_hasSum hw f (shift_segments ha).2.1
  rw [← h.tsum_eq,h.summable.tsum_eq_zero_add,← h'.tsum_eq]
  simp only [Nat.cast_zero,zero_add]
  congr 1
  apply tsum_congr
  intro j
  congr 2 <;> push_cast <;> ring

/-- Constant forcing cancels between adjacent real periods. -/
private theorem period_shift_absolute {w : ℂ} (hw : 2 < w.re)
    {a : ℝ} (ha : a ∈ Icc (1 : ℝ) 2) :
    periodValue w a=periodValue w (a+1)+(a : ℂ)^(-w)*periodValue w (1+1/a) := by
  obtain ⟨har,has,hi⟩ := shift_segments ha
  have hw1 : 1 < w.re := by linarith only [hw]
  have h := congrArg (evaluation (periodPoint a har)) (state_equation_absolute hw)
  have h' := congrArg (evaluation (periodPoint (a+1) has)) (state_equation_absolute hw)
  rw [map_sub,map_smul,source_eq (zero_lt_one.trans hw1)] at h h'
  have ht := transfer_shift hw1 (state w) ha
  rw [periodValue_evaluation w har,periodValue_evaluation w has]
  have he : periodValue w (1+1/a)=plane (state w) ((a : ℂ)⁻¹) := by
    unfold periodValue
    congr 1
    push_cast
    ring
  rw [he]
  have hc : evaluation (periodPoint a har) (constant 1)=
      evaluation (periodPoint (a+1) has) (constant 1) := rfl
  rw [hc] at h
  linear_combination h-h'+ht

/-- The three-term Lewis relation holds for the actual convergent period function. -/
theorem three_term_absolute {w : ℂ} (hw : 2 < w.re)
    {a : ℝ} (ha : a ∈ Icc (1 : ℝ) 2) :
    periodValue w a=periodValue w (a+1)+
      ((a+1 : ℝ) : ℂ)^(-w)*periodValue w (a/(a+1)) := by
  have hp : 0 < a := lt_of_lt_of_le zero_lt_one ha.1
  have hi : 0 < 1+1/a := add_pos zero_lt_one (one_div_pos.mpr hp)
  have hp1 : a+1 ≠ 0 := ne_of_gt (by linarith only [hp])
  have he : 1/(1+1/a)=a/(a+1) := by field_simp [hp.ne',hp1]
  have hm : a*(1+1/a)=a+1 := by field_simp [hp.ne']
  rw [period_shift_absolute hw ha,reciprocity_absolute hw (shift_segments ha).2.2,
    he,← mul_assoc,← Complex.mul_cpow_ofReal_nonneg hp.le hi.le,← Complex.ofReal_mul,hm]

private theorem fraction_segment {a : ℝ} (ha : a ∈ Icc (1 : ℝ) 2) :
    a/(a+1) ∈ periodSegment := by
  have hp : 0 < a+1 := by linarith only [ha.1]
  constructor
  · exact (le_div_iff₀ hp).mpr (by linarith only [ha.1])
  · exact (div_le_iff₀ hp).mpr (by linarith only [ha.1])

private def threeTermDefect (a : ℝ) (w : ℂ) : ℂ :=
  clearedPeriod w a-clearedPeriod w (a+1)-
    ((a+1 : ℝ) : ℂ)^(-w)*clearedPeriod w (a/(a+1))

private theorem analyticOn_threeTermDefect {a : ℝ} (ha : a ∈ Icc (1 : ℝ) 2) :
    AnalyticOnNhd ℂ (threeTermDefect a) {w : ℂ | 0 < w.re} := by
  have hp : 0 < a+1 := by linarith only [ha.1]
  have ha0 : ((a+1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hd : Differentiable ℂ (fun w : ℂ => ((a+1 : ℝ) : ℂ)^(-w)) := by
    simp only [Complex.cpow_def_of_ne_zero ha0]
    fun_prop
  obtain ⟨har,has,_⟩ := shift_segments ha
  have hf : DifferentiableOn ℂ (threeTermDefect a) {w : ℂ | 0 < w.re} := by
    intro w hw
    exact (((analyticAt_clearedPeriod hw har).differentiableAt.sub
      (analyticAt_clearedPeriod hw has).differentiableAt).sub
      ((hd w).mul (analyticAt_clearedPeriod hw (fraction_segment ha)).differentiableAt)).differentiableWithinAt
  exact hf.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

private theorem threeTermDefect_absolute {w : ℂ} (hw : 2 < w.re)
    {a : ℝ} (ha : a ∈ Icc (1 : ℝ) 2) : threeTermDefect a w=0 := by
  have hw2 : w ≠ 2 := by intro he; norm_num [he] at hw
  obtain ⟨har,has,_⟩ := shift_segments ha
  rw [threeTermDefect,clearedPeriod_eq hw2 har,clearedPeriod_eq hw2 has,
    clearedPeriod_eq hw2 (fraction_segment ha),three_term_absolute hw ha]
  ring

private theorem threeTermDefect_zero {w : ℂ} (hw : 0 < w.re)
    {a : ℝ} (ha : a ∈ Icc (1 : ℝ) 2) : threeTermDefect a w=0 := by
  have he : threeTermDefect a =ᶠ[𝓝 (3 : ℂ)] 0 := by
    have ho : IsOpen {v : ℂ | 2 < v.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (3 : ℂ) ∈ {v : ℂ | 2 < v.re} by norm_num)] with v hv
    exact threeTermDefect_absolute hv ha
  exact (analyticOn_threeTermDefect ha).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    MayerCofactorContinuation.rightHalfPlane_preconnected (by norm_num) he hw

/-- The actual continued state obeys the three-term Lewis relation throughout the source half-plane. -/
theorem three_term {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2)
    {a : ℝ} (ha : a ∈ Icc (1 : ℝ) 2) :
    periodValue w a=periodValue w (a+1)+
      ((a+1 : ℝ) : ℂ)^(-w)*periodValue w (a/(a+1)) := by
  obtain ⟨har,has,_⟩ := shift_segments ha
  have he := threeTermDefect_zero hw ha
  rw [threeTermDefect,clearedPeriod_eq hw2 har,clearedPeriod_eq hw2 has,
    clearedPeriod_eq hw2 (fraction_segment ha)] at he
  apply mul_left_cancel₀ (sub_ne_zero.mpr hw2)
  linear_combination he

#print axioms three_term_absolute
#print axioms three_term

#print axioms periodValue_barnes
#print axioms reciprocity_absolute
#print axioms reciprocity
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringPeriod

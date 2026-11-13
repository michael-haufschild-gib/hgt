import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import GaloisForLFunctions.HTGeometry.HardyBoundary.WeightedL2Fatou
import GaloisForLFunctions.HTGeometry.L2PairingEnergy
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Continuity of weighted L² moments

Square-root multipliers make bounded weighted moments continuous.
Uniform tails remove the weight cap, while square-root coordinates turn
vanishing weighted error into convergence of the full moments.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry

/-- Every bounded nonnegative weight has finite moment on L². -/
theorem integrable_bounded_weight_norm_sq {w : ℝ → ℝ} (hwm : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) {C : ℝ} (hwC : ∀ x, w x ≤ C)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable (fun x => w x * ‖f x‖ ^ 2) := by
  have hi : Integrable (fun x => ‖f x‖ ^ 2) :=
    (Lp.memLp f).integrable_norm_pow (by norm_num)
  apply (hi.const_mul C).mono'
    (hwm.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable f).norm.pow 2))
  exact Eventually.of_forall fun x => by
    dsimp only [Pi.mul_apply, Pi.pow_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 x) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hwC x) (sq_nonneg _)

/-- The moment of a bounded nonnegative weight is a continuous quadratic form. -/
theorem continuous_bounded_weight_norm_sq {w : ℝ → ℝ} (hwm : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) {C : ℝ} (hwC : ∀ x, w x ≤ C) :
    Continuous (fun f : Lp ℂ 2 (volume : Measure ℝ) => ∫ x, w x * ‖f x‖ ^ 2) := by
  let φ : ℝ → ℂ := fun x => (Real.sqrt (w x) : ℂ)
  have hφ : Measurable φ := by fun_prop
  have hφC (x : ℝ) : ‖φ x‖ ≤ Real.sqrt C := by
    dsimp only [φ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hwC x)
  let T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
    lpBoundedMulCLM hφ (Real.sqrt_nonneg C) hφC
  have he (f : Lp ℂ 2 (volume : Measure ℝ)) : (∫ x, w x * ‖f x‖ ^ 2) = ‖T f‖ ^ 2 := by
    rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq volume]
    apply integral_congr_ae
    filter_upwards [lpBoundedMulCLM_coeFn hφ (Real.sqrt_nonneg C) hφC f] with x hx
    change w x * ‖f x‖ ^ 2 = ‖T f x‖ ^ 2
    change T f x = φ x * f x at hx
    rw [hx, norm_mul]
    dsimp only [φ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (hw0 x)]
  have heq : (fun f : Lp ℂ 2 (volume : Measure ℝ) => ∫ x, w x * ‖f x‖ ^ 2) =
      fun f => ‖T f‖ ^ 2 :=
    funext he
  rw [heq]
  exact T.continuous.norm.pow 2

#print axioms continuous_bounded_weight_norm_sq
/-- Capping a nonnegative weight loses at most its superlevel tail moment. -/
theorem bounded_weight_cap_error {w : ℝ → ℝ} (hwm : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) {T : ℝ} (hT : 0 ≤ T) (f : Lp ℂ 2 (volume : Measure ℝ))
    (hwi : Integrable (fun x => w x * ‖f x‖ ^ 2)) :
    0 ≤ (∫ x, w x * ‖f x‖ ^ 2) - (∫ x, min (w x) T * ‖f x‖ ^ 2) ∧
      (∫ x, w x * ‖f x‖ ^ 2) - (∫ x, min (w x) T * ‖f x‖ ^ 2) ≤
        ∫ x in {x | T < w x}, w x * ‖f x‖ ^ 2 := by
  have hcap : Integrable (fun x => min (w x) T * ‖f x‖ ^ 2) :=
    integrable_bounded_weight_norm_sq (hwm.min measurable_const)
      (fun x => le_min (hw0 x) hT) (fun x => min_le_right (w x) T) f
  have hs : MeasurableSet {x | T < w x} := measurableSet_lt measurable_const hwm
  rw [← integral_sub hwi hcap]
  constructor
  · exact integral_nonneg fun x => sub_nonneg.mpr
      (mul_le_mul_of_nonneg_right (min_le_left (w x) T) (sq_nonneg _))
  · rw [← integral_indicator hs]
    apply integral_mono (hwi.sub hcap) (hwi.indicator hs)
    intro x
    dsimp only [Pi.sub_apply]
    by_cases hx : T < w x
    · rw [Set.indicator_of_mem (s := {x | T < w x}) hx,
        min_eq_right hx.le]
      exact sub_le_self _ (mul_nonneg hT (sq_nonneg _))
    · rw [Set.indicator_of_notMem (s := {x | T < w x}) hx,
        min_eq_left (le_of_not_gt hx), sub_self]

#print axioms bounded_weight_cap_error

/-- Strong L² convergence and uniform weighted tails imply convergence of the full moments. -/
theorem tendsto_weighted_norm_sq_of_uniform_tails
    {f : ℕ → Lp ℂ 2 (volume : Measure ℝ)} {g : Lp ℂ 2 (volume : Measure ℝ)}
    (hf : Tendsto f atTop (𝓝 g))
    {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hwi : ∀ n, Integrable (fun x => w x * ‖f n x‖ ^ 2))
    {M : ℝ} (hbound : ∀ n, (∫ x, w x * ‖f n x‖ ^ 2) ≤ M)
    (htail : ∀ ε > 0, ∃ T : ℝ, 0 ≤ T ∧
      ∀ n, (∫ x in {x | T < w x}, w x * ‖f n x‖ ^ 2) ≤ ε) :
    Integrable (fun x => w x * ‖g x‖ ^ 2) ∧
      Tendsto (fun n => ∫ x, w x * ‖f n x‖ ^ 2) atTop
        (𝓝 (∫ x, w x * ‖g x‖ ^ 2)) := by
  have hg := GaloisForLFunctions.HTGeometry.weighted_norm_sq_of_L2_limit
    hf hwm hw0 hwi tendsto_const_nhds hbound
  refine ⟨hg.1, Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  obtain ⟨T, hT, hTbound⟩ := htail (ε / 4) (by linarith only [hε])
  have hs : MeasurableSet {x | T < w x} := measurableSet_lt measurable_const hwm
  let wt : ℝ → ℝ := {x | T < w x}.indicator w
  have hwtm : Measurable wt := hwm.indicator hs
  have hwt0 (x : ℝ) : 0 ≤ wt x := by
    by_cases hx : T < w x
    · simpa only [wt, Set.indicator_of_mem (s := {x | T < w x}) hx] using hw0 x
    · simp only [wt, Set.indicator_of_notMem (s := {x | T < w x}) hx, le_refl]
  have he (u : Lp ℂ 2 (volume : Measure ℝ)) : (fun x => wt x * ‖u x‖ ^ 2) =
      {x | T < w x}.indicator (fun x => w x * ‖u x‖ ^ 2) := by
    funext x
    by_cases hx : T < w x
    · simp only [wt, Set.indicator_of_mem (s := {x | T < w x}) hx]
    · simp only [wt, Set.indicator_of_notMem (s := {x | T < w x}) hx, zero_mul]
  have hwti (n : ℕ) : Integrable (fun x => wt x * ‖f n x‖ ^ 2) := by
    rw [he]
    exact (hwi n).indicator hs
  have hwtbound (n : ℕ) : (∫ x, wt x * ‖f n x‖ ^ 2) ≤ ε / 4 := by
    rw [he, integral_indicator hs]
    exact hTbound n
  have hgt := (GaloisForLFunctions.HTGeometry.weighted_norm_sq_of_L2_limit
    hf hwtm hwt0 hwti tendsto_const_nhds hwtbound).2
  rw [he, integral_indicator hs] at hgt
  have hcap := (continuous_bounded_weight_norm_sq (hwm.min measurable_const)
    (fun x => le_min (hw0 x) hT) (fun x => min_le_right (w x) T)).tendsto g |>.comp hf
  filter_upwards [Metric.tendsto_nhds.mp hcap (ε / 2) (by linarith only [hε])] with n hn
  rw [Real.dist_eq] at hn ⊢
  dsimp only [Function.comp_apply] at hn
  have hncap := bounded_weight_cap_error hwm hw0 hT (f n) (hwi n)
  have hgcap := bounded_weight_cap_error hwm hw0 hT g hg.1
  have hnerr := hncap.2.trans (hTbound n)
  have hgerr := hgcap.2.trans hgt
  obtain ⟨hnlo, hnhi⟩ := abs_lt.mp hn
  apply abs_lt.mpr
  constructor <;> linarith only [hε, hncap.1, hgcap.1, hnerr, hgerr, hnlo, hnhi]

#print axioms tendsto_weighted_norm_sq_of_uniform_tails

private theorem memLp_sqrt_weight_mul {w : ℝ → ℝ} (hwm : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (f : Lp ℂ 2 (volume : Measure ℝ))
    (hi : Integrable (fun x => w x * ‖f x‖ ^ 2)) :
    MemLp (fun x => (Real.sqrt (w x) : ℂ) * f x) 2 volume := by
  have hroot : Measurable (fun x => (Real.sqrt (w x) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (Real.continuous_sqrt.measurable.comp hwm)
  have hm : AEStronglyMeasurable (fun x => (Real.sqrt (w x) : ℂ) * f x) :=
    hroot.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply hi.congr
  exact Eventually.of_forall fun x => by
    change w x * ‖f x‖ ^ 2 = ‖(Real.sqrt (w x) : ℂ) * f x‖ ^ 2
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw0 x)]

/-- Vanishing weighted square error implies convergence of the weighted square moments. -/
theorem tendsto_weighted_norm_sq_of_difference
    {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    {f : ℕ → Lp ℂ 2 (volume : Measure ℝ)} {g : Lp ℂ 2 (volume : Measure ℝ)}
    (hfi : ∀ n, Integrable (fun x => w x * ‖f n x‖ ^ 2))
    (hgi : Integrable (fun x => w x * ‖g x‖ ^ 2))
    (hdiff : Tendsto (fun n => ∫ x, w x * ‖f n x - g x‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, w x * ‖f n x‖ ^ 2) atTop (𝓝 (∫ x, w x * ‖g x‖ ^ 2)) := by
  have hf2 (n : ℕ) := memLp_sqrt_weight_mul hwm hw0 (f n) (hfi n)
  have hg2 := memLp_sqrt_weight_mul hwm hw0 g hgi
  let U : ℕ → Lp ℂ 2 (volume : Measure ℝ) :=
    fun n => (hf2 n).toLp (fun x => (Real.sqrt (w x) : ℂ) * f n x)
  let v : Lp ℂ 2 (volume : Measure ℝ) :=
    hg2.toLp (fun x => (Real.sqrt (w x) : ℂ) * g x)
  have hn (n : ℕ) : ‖U n‖ ^ 2 = ∫ x, w x * ‖f n x‖ ^ 2 := by
    rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq volume]
    apply integral_congr_ae
    filter_upwards [(hf2 n).coeFn_toLp] with x hx
    change U n x = (Real.sqrt (w x) : ℂ) * f n x at hx
    rw [hx, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw0 x)]
  have hv : ‖v‖ ^ 2 = ∫ x, w x * ‖g x‖ ^ 2 := by
    rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq volume]
    apply integral_congr_ae
    filter_upwards [hg2.coeFn_toLp] with x hx
    change v x = (Real.sqrt (w x) : ℂ) * g x at hx
    rw [hx, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw0 x)]
  have hd (n : ℕ) : ‖U n - v‖ ^ 2 = ∫ x, w x * ‖f n x - g x‖ ^ 2 := by
    rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq volume]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (U n) v, (hf2 n).coeFn_toLp, hg2.coeFn_toLp]
      with x hx hf hg
    change U n x = (Real.sqrt (w x) : ℂ) * f n x at hf
    change v x = (Real.sqrt (w x) : ℂ) * g x at hg
    rw [hx]
    dsimp only [Pi.sub_apply]
    rw [hf, hg, ← mul_sub, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw0 x)]
  have hU : Tendsto U atTop (𝓝 v) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hdiff.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with n hn
    rw [← hd n] at hn
    rw [dist_eq_norm]
    nlinarith only [hn, hε, norm_nonneg (U n - v)]
  have h := hU.norm.pow 2
  simpa only [hn, hv] using h

#print axioms tendsto_weighted_norm_sq_of_difference
end GaloisForLFunctions.HTGeometry

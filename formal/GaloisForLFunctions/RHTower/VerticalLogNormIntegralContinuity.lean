import GaloisForLFunctions.RHTower.EntireWeightedLittlewoodRectangle
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuity of vertical logarithmic norm integrals

An entire nonzero function may vanish on a vertical slice, so pointwise continuity of its
logarithmic norm is insufficient. Finite zero peeling reduces every compact rectangle to finitely
many explicit logarithmic root kernels plus a uniformly nonvanishing analytic cofactor. The root
kernels are locally dominated by an integrable logarithmic singularity, and the cofactor is bounded
on the rectangle. Consequently the vertical logarithmic norm integral is continuous as the real
part of the slice moves, including through slices containing zeros.
-/

open Complex MeasureTheory Set Filter intervalIntegral
open scoped Interval

namespace RHTower

noncomputable section

private theorem intervalIntegrable_abs_log_abs_sub (a b shift : ℝ) :
    IntervalIntegrable (fun t : ℝ => |Real.log (|t - shift|)|) volume a b := by
  rw [show a = (a - shift) + shift by ring,
    show b = (b - shift) + shift by ring]
  apply IntervalIntegrable.comp_sub_right (f := fun t : ℝ => |Real.log (|t|)|) _ shift
  simpa [Real.log_abs] using
    (intervalIntegral.intervalIntegrable_log' (a := a - shift) (b := b - shift)).abs

theorem continuousAt_verticalIntegral_log_norm_sub
    (rho : ℂ) (T₁ T₂ c₀ : ℝ) :
    ContinuousAt (fun c : ℝ =>
      ∫ t in T₁..T₂, Real.log ‖(c : ℂ) + (t : ℂ) * I - rho‖) c₀ := by
  let M : ℝ := 3 + |c₀ - rho.re| + |T₁ - rho.im| + |T₂ - rho.im|
  let bound : ℝ → ℝ := fun t => Real.log M + |Real.log (|t - rho.im|)|
  have hM1 : 1 ≤ M := by
    dsimp only [M]
    nlinarith [abs_nonneg (c₀ - rho.re), abs_nonneg (T₁ - rho.im),
      abs_nonneg (T₂ - rho.im)]
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hboundInt : IntervalIntegrable bound volume T₁ T₂ := by
    exact intervalIntegrable_const.add
      (intervalIntegrable_abs_log_abs_sub T₁ T₂ rho.im)
  apply continuousAt_of_dominated_interval (μ := volume) (bound := bound)
  · filter_upwards with c
    have hcont : Continuous fun t : ℝ =>
        (c : ℂ) + (t : ℂ) * I - rho := by fun_prop
    exact (Real.measurable_log.comp hcont.norm.measurable).aestronglyMeasurable.restrict
  · filter_upwards [Metric.ball_mem_nhds c₀ zero_lt_one] with c hc
    filter_upwards [volume.ae_ne (rho.im : ℝ)] with t ht _htI
    change |Real.log ‖(c : ℂ) + (t : ℂ) * I - rho‖| ≤ bound t
    have hcabs : |c - c₀| < 1 := by simpa [Real.dist_eq] using hc
    have htM : |t - rho.im| ≤ |T₁ - rho.im| + |T₂ - rho.im| := by
      by_cases hT : T₁ ≤ T₂
      · have htI : t ∈ Set.Ioc T₁ T₂ := by simpa [Set.uIoc_of_le hT] using _htI
        have habs := abs_le_max_abs_abs
          (sub_le_sub_right htI.1.le rho.im)
          (sub_le_sub_right htI.2 rho.im)
        exact habs.trans (max_le
          (le_add_of_nonneg_right (abs_nonneg (T₂ - rho.im)))
          (le_add_of_nonneg_left (abs_nonneg (T₁ - rho.im))))
      · have htI : t ∈ Set.Ioc T₂ T₁ := by
          simpa [Set.uIoc_of_ge (le_of_not_ge hT)] using _htI
        have habs := abs_le_max_abs_abs
          (sub_le_sub_right htI.1.le rho.im)
          (sub_le_sub_right htI.2 rho.im)
        exact habs.trans (max_le
          (le_add_of_nonneg_left (abs_nonneg (T₁ - rho.im)))
          (le_add_of_nonneg_right (abs_nonneg (T₂ - rho.im))))
    have hnormM : ‖(c : ℂ) + (t : ℂ) * I - rho‖ ≤ M := by
      have hre : |c - rho.re| ≤ |c - c₀| + |c₀ - rho.re| := by
        exact abs_sub_le c c₀ rho.re
      have hnorm : ‖(c : ℂ) + (t : ℂ) * I - rho‖ ≤
          |c - rho.re| + |t - rho.im| := by
        have hz : (c : ℂ) + (t : ℂ) * I - rho =
            ((c - rho.re : ℝ) : ℂ) + ((t - rho.im : ℝ) : ℂ) * I := by
          apply Complex.ext <;> simp
        rw [hz]
        calc
          ‖((c - rho.re : ℝ) : ℂ) + ((t - rho.im : ℝ) : ℂ) * I‖ ≤
              ‖((c - rho.re : ℝ) : ℂ)‖ + ‖((t - rho.im : ℝ) : ℂ) * I‖ :=
            norm_add_le _ _
          _ = |c - rho.re| + |t - rho.im| := by
            rw [Complex.norm_real, norm_mul, Complex.norm_real, norm_I, mul_one,
              Real.norm_eq_abs, Real.norm_eq_abs]
      dsimp only [M]
      linarith
    have hnormPos : 0 < ‖(c : ℂ) + (t : ℂ) * I - rho‖ := by
      rw [norm_pos_iff]
      intro hz
      have him := congrArg Complex.im hz
      exact ht (sub_eq_zero.mp (by simpa using him))
    by_cases hnorm1 : 1 ≤ ‖(c : ℂ) + (t : ℂ) * I - rho‖
    · rw [abs_of_nonneg (Real.log_nonneg hnorm1)]
      exact (Real.log_le_log hnormPos hnormM).trans
        (le_add_of_nonneg_right (abs_nonneg _))
    · have hnormlt : ‖(c : ℂ) + (t : ℂ) * I - rho‖ < 1 := lt_of_not_ge hnorm1
      have hvpos : 0 < |t - rho.im| := abs_pos.mpr (sub_ne_zero.mpr ht)
      have hvnorm : |t - rho.im| ≤ ‖(c : ℂ) + (t : ℂ) * I - rho‖ := by
        have him : ((c : ℂ) + (t : ℂ) * I - rho).im = t - rho.im := by simp
        rw [← him]
        exact Complex.abs_im_le_norm _
      have hlogv : Real.log |t - rho.im| ≤
          Real.log ‖(c : ℂ) + (t : ℂ) * I - rho‖ :=
        Real.log_le_log hvpos hvnorm
      have hlognorm : Real.log ‖(c : ℂ) + (t : ℂ) * I - rho‖ < 0 :=
        Real.log_neg hnormPos hnormlt
      have hlogvneg : Real.log |t - rho.im| < 0 := lt_of_le_of_lt hlogv hlognorm
      rw [abs_of_neg hlognorm]
      change -Real.log ‖(c : ℂ) + (t : ℂ) * I - rho‖ ≤
        Real.log M + |Real.log (|t - rho.im|)|
      rw [abs_of_neg hlogvneg]
      nlinarith [Real.log_nonneg hM1]
  · exact hboundInt
  · filter_upwards [volume.ae_ne (rho.im : ℝ)] with t ht _htI
    have hne : ‖(c₀ : ℂ) + (t : ℂ) * I - rho‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      intro hz
      have him := congrArg Complex.im hz
      exact ht (sub_eq_zero.mp (by simpa using him))
    have hinner : ContinuousAt (fun c : ℝ =>
        ‖(c : ℂ) + (t : ℂ) * I - rho‖) c₀ := by fun_prop
    exact ContinuousAt.comp_of_eq (Real.continuousAt_log hne) hinner rfl

private theorem continuousAt_finset_sum'
    {α X : Type*} [TopologicalSpace X] (s : Finset α)
    (F : α → X → ℝ) (x₀ : X)
    (hF : ∀ a ∈ s, ContinuousAt (F a) x₀) :
    ContinuousAt (fun x => ∑ a ∈ s, F a x) x₀ := by
  exact tendsto_finsetSum s hF

theorem continuousAt_verticalIntegral_log_norm_of_entire
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∃ z : ℂ, f z ≠ 0) (T₁ T₂ c₀ : ℝ) :
    ContinuousAt (fun c : ℝ =>
      ∫ t in T₁..T₂, Real.log ‖f ((c : ℂ) + (t : ℂ) * I)‖) c₀ := by
  classical
  let K : Set ℂ := uIcc (c₀ - 1) (c₀ + 1) ×ℂ uIcc T₁ T₂
  have hKcompact : IsCompact K := isCompact_uIcc.reProdIm isCompact_uIcc
  let z₁ : ℂ := ((c₀ - 1 : ℝ) : ℂ) + T₁ * I
  let z₂ : ℂ := ((c₀ + 1 : ℝ) : ℂ) + T₂ * I
  let hfinite : {z ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) |
      f z = 0}.Finite := entire_zeros_closedRectangle_finite hf hne z₁ z₂
  let Z : Finset ℂ := hfinite.toFinset
  have hmem (z : ℂ) : z ∈ Z ↔ z ∈ K ∧ f z = 0 := by
    change z ∈ hfinite.toFinset ↔ _
    rw [Set.Finite.mem_toFinset, Set.mem_sep_iff]
    simp [K, z₁, z₂]
  obtain ⟨m, h, hhan, hm, hh0, hfact⟩ := exists_finite_peel isOpen_univ
    hf Z (by simp) (fun w _ => analyticOrderAt_ne_top_of_entire_exists_ne_zero hf hne w)
  have hhK : ∀ z ∈ K, h z ≠ 0 := by
    intro z hzK hhzero
    have hf0 : f z = 0 := by
      rw [hfact z (Set.mem_univ z), hhzero, mul_zero]
    exact hh0 z ((hmem z).mpr ⟨hzK, hf0⟩) hhzero
  have hhcont : Continuous h := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (hhan z (Set.mem_univ z)).continuousAt
  have hloghcont : ContinuousOn (fun z => Real.log ‖h z‖) K := by
    intro z hz
    have hncont : ContinuousAt (fun w => ‖h w‖) z := hhcont.continuousAt.norm
    exact (ContinuousAt.comp_of_eq
      (Real.continuousAt_log (norm_ne_zero_iff.mpr (hhK z hz))) hncont rfl).continuousWithinAt
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hloghcont
  have hcofCont : ContinuousAt (fun c : ℝ =>
      ∫ t in T₁..T₂, Real.log ‖h ((c : ℂ) + (t : ℂ) * I)‖) c₀ := by
    apply continuousAt_of_dominated_interval (μ := volume) (bound := fun _ => C)
    · filter_upwards with c
      exact (Real.measurable_log.comp
        (hhcont.comp (by fun_prop : Continuous fun t : ℝ =>
          (c : ℂ) + (t : ℂ) * I)).norm.measurable).aestronglyMeasurable.restrict
    · filter_upwards [Metric.ball_mem_nhds c₀ zero_lt_one] with c hc
      filter_upwards with t htI
      have hcabs : |c - c₀| < 1 := by simpa [Real.dist_eq] using hc
      have hzK : (c : ℂ) + (t : ℂ) * I ∈ K := by
        dsimp only [K]
        apply Complex.mem_reProdIm.mpr
        constructor
        · rw [uIcc_of_le (by linarith : c₀ - 1 ≤ c₀ + 1)]
          constructor <;> simp <;> linarith [abs_lt.mp hcabs]
        · simpa using (uIoc_subset_uIcc htI)
      simpa [Real.norm_eq_abs] using hC ((c : ℂ) + (t : ℂ) * I) hzK
    · exact intervalIntegrable_const
    · filter_upwards with t htI
      have hzK : (c₀ : ℂ) + (t : ℂ) * I ∈ K := by
        dsimp only [K]
        apply Complex.mem_reProdIm.mpr
        constructor
        · rw [uIcc_of_le (by linarith : c₀ - 1 ≤ c₀ + 1)]
          simp
        · simpa using (uIoc_subset_uIcc htI)
      have hinner : ContinuousAt (fun c : ℝ =>
          ‖h ((c : ℂ) + (t : ℂ) * I)‖) c₀ := by fun_prop
      exact ContinuousAt.comp_of_eq
        (Real.continuousAt_log (norm_ne_zero_iff.mpr (hhK _ hzK))) hinner rfl
  have hrootCont : ∀ w ∈ Z, ContinuousAt (fun c : ℝ =>
      (m w : ℝ) *
        ∫ t in T₁..T₂, Real.log ‖(c : ℂ) + (t : ℂ) * I - w‖) c₀ := by
    intro w _
    exact (continuousAt_verticalIntegral_log_norm_sub w T₁ T₂ c₀).const_mul (m w : ℝ)
  have hsumCont : ContinuousAt (fun c : ℝ =>
      ∑ w ∈ Z, (m w : ℝ) *
        ∫ t in T₁..T₂, Real.log ‖(c : ℂ) + (t : ℂ) * I - w‖) c₀ :=
    continuousAt_finset_sum' Z (fun w (c : ℝ) => (m w : ℝ) *
      ∫ t in T₁..T₂, Real.log ‖(c : ℂ) + (t : ℂ) * I - w‖) c₀ hrootCont
  have hrightCont : ContinuousAt (fun c : ℝ =>
      (∑ w ∈ Z, (m w : ℝ) *
        ∫ t in T₁..T₂, Real.log ‖(c : ℂ) + (t : ℂ) * I - w‖) +
      ∫ t in T₁..T₂, Real.log ‖h ((c : ℂ) + (t : ℂ) * I)‖) c₀ :=
    hsumCont.add hcofCont
  apply hrightCont.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds c₀ zero_lt_one] with c hc
  have hcabs : |c - c₀| < 1 := by simpa [Real.dist_eq] using hc
  have hrootInt : ∀ w ∈ Z, IntervalIntegrable (fun t : ℝ =>
      (m w : ℝ) * Real.log ‖(c : ℂ) + (t : ℂ) * I - w‖) volume T₁ T₂ := by
    intro w _
    apply IntervalIntegrable.const_mul
    have hmer : MeromorphicOn (fun t : ℝ =>
        (c : ℂ) + (t : ℂ) * I - w) (uIcc T₁ T₂) := by
      intro t _
      exact (analyticAt_const.add
        ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const) |>.sub
          analyticAt_const).meromorphicAt
    exact hmer.intervalIntegrable_log_norm
  have hsumInt : IntervalIntegrable (fun t : ℝ =>
      ∑ w ∈ Z, (m w : ℝ) * Real.log ‖(c : ℂ) + (t : ℂ) * I - w‖)
      volume T₁ T₂ := by
    have heq : (fun t : ℝ =>
        ∑ w ∈ Z, (m w : ℝ) * Real.log ‖(c : ℂ) + (t : ℂ) * I - w‖) =
        ∑ w ∈ Z, (fun t : ℝ =>
          (m w : ℝ) * Real.log ‖(c : ℂ) + (t : ℂ) * I - w‖) := by
      funext t
      simp
    rw [heq]
    exact IntervalIntegrable.sum Z hrootInt
  have hcofInt : IntervalIntegrable (fun t : ℝ =>
      Real.log ‖h ((c : ℂ) + (t : ℂ) * I)‖) volume T₁ T₂ := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hzK : (c : ℂ) + (t : ℂ) * I ∈ K := by
      dsimp only [K]
      apply Complex.mem_reProdIm.mpr
      constructor
      · rw [uIcc_of_le (by linarith : c₀ - 1 ≤ c₀ + 1)]
        constructor <;> simp <;> linarith [abs_lt.mp hcabs]
      · simpa using ht
    have hinner : ContinuousAt (fun u : ℝ =>
        ‖h ((c : ℂ) + (u : ℂ) * I)‖) t := by fun_prop
    exact (ContinuousAt.comp_of_eq
      (Real.continuousAt_log (norm_ne_zero_iff.mpr (hhK _ hzK))) hinner rfl).continuousWithinAt
  have hae : ∀ᵐ t ∂volume, t ∈ Ι T₁ T₂ →
      Real.log ‖f ((c : ℂ) + (t : ℂ) * I)‖ =
        (∑ w ∈ Z, (m w : ℝ) *
          Real.log ‖(c : ℂ) + (t : ℂ) * I - w‖) +
        Real.log ‖h ((c : ℂ) + (t : ℂ) * I)‖ := by
    filter_upwards [(eventually_all_finset Z).2 (fun w _ => volume.ae_ne w.im)] with t ht
    intro htI
    let z : ℂ := (c : ℂ) + (t : ℂ) * I
    have hzK : z ∈ K := by
      dsimp only [K]
      rw [Complex.mem_reProdIm]
      rw [uIcc_of_le (by linarith : c₀ - 1 ≤ c₀ + 1)]
      constructor
      · dsimp only [z]
        constructor <;> simp <;> linarith [abs_lt.mp hcabs]
      · dsimp only [z]
        simpa using (uIoc_subset_uIcc htI)
    have hzw : ∀ w ∈ Z, z - w ≠ 0 := by
      intro w hw hzero
      have him := congrArg Complex.im hzero
      exact ht w hw (sub_eq_zero.mp (by simpa [z] using him))
    have hprodne : (∏ w ∈ Z, ‖z - w‖ ^ m w) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro w hw
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hzw w hw))
    have hhne : ‖h z‖ ≠ 0 := norm_ne_zero_iff.mpr (hhK z hzK)
    have hnorm : ‖f z‖ = (∏ w ∈ Z, ‖z - w‖ ^ m w) * ‖h z‖ := by
      rw [hfact z (Set.mem_univ z), norm_mul, norm_prod]
      congr 1
      refine Finset.prod_congr rfl ?_
      intro w _
      rw [norm_pow]
    dsimp only [z] at hnorm ⊢
    rw [hnorm, Real.log_mul hprodne hhne,
      Real.log_prod (fun w hw => Finset.prod_ne_zero_iff.mp hprodne w hw)]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro w _
    rw [Real.log_pow]
  rw [intervalIntegral.integral_congr_ae hae,
    intervalIntegral.integral_add hsumInt hcofInt,
    intervalIntegral.integral_finsetSum hrootInt]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro w _
  rw [intervalIntegral.integral_const_mul]

end

end RHTower



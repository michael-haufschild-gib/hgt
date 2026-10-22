import GaloisForLFunctions.RHTower.Suzuki.SuzukiCCMMixedScrewWeilBridge
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewOperatorSymmetry
import GaloisForLFunctions.RHTower.Suzuki.SuzukiDirichletFormCore
import GaloisForLFunctions.RHTower.Suzuki.SuzukiOneSidedFourierLaplace
import GaloisForLFunctions.HTGeometry.BoundedPerturbedFriedrichsFormCore
import Mathlib.Analysis.Normed.Operator.Banach

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

local instance (a : SuzukiPositiveAperture) : CompleteSpace (SuzukiApertureZeroMean a) :=
  (suzukiApertureZeroMean_isClosed a).completeSpace_coe

/-- The exact primitive lift into the CCM form domain is bounded. -/
def suzukiAperturePrimitiveCCMFormCLM (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] CCMArchimedeanFormDomain a :=
  ContinuousLinearMap.ofSeqClosedGraph (g := suzukiAperturePrimitiveCCMFormLM a) (by
    intro u x y hux huy
    apply suzukiWeilIntervalFormEmbedding_injective a
    have hy : Tendsto
        (fun n => suzukiWeilIntervalFormEmbedding a
          (suzukiAperturePrimitiveCCMFormLM a (u n)))
        atTop (𝓝 (suzukiWeilIntervalFormEmbedding a y)) :=
      ((suzukiWeilIntervalFormEmbedding a).continuous.tendsto y).comp huy
    have hx : Tendsto
        (fun n => suzukiAperturePrimitiveCLM a (u n))
        atTop (𝓝 (suzukiAperturePrimitiveCLM a x)) :=
      ((suzukiAperturePrimitiveCLM a).continuous.tendsto x).comp hux
    change Tendsto (fun n => suzukiAperturePrimitive a.1 (u n)) atTop
      (𝓝 (suzukiAperturePrimitive a.1 x)) at hx
    have hlim : suzukiWeilIntervalFormEmbedding a y =
        suzukiAperturePrimitive a.1 x := by
      apply tendsto_nhds_unique hy
      simpa only [suzukiAperturePrimitiveCCMFormLM_apply,
        suzukiWeilIntervalFormEmbedding_primitiveCCMFormVector] using hx
    rw [hlim]
    exact (suzukiWeilIntervalFormEmbedding_primitiveCCMFormVector a x).symm)

@[simp]
theorem suzukiAperturePrimitiveCCMFormCLM_apply
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    suzukiAperturePrimitiveCCMFormCLM a f =
      suzukiAperturePrimitiveCCMFormVector a f := rfl

/-- The exact restricted Weil form pulled back to derivative coordinates. -/
def suzukiPrimitiveWeilSourceOperator (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  (suzukiAperturePrimitiveCCMFormCLM a)† ∘L
      suzukiAperturePrimitiveCCMFormCLM a +
    (suzukiAperturePrimitiveCLM a)† ∘L
      suzukiWeilIntervalBoundedRemainder a ∘L
        suzukiAperturePrimitiveCLM a

theorem inner_suzukiPrimitiveWeilSourceOperator
    (a : SuzukiPositiveAperture)
    (f g : SuzukiApertureIntervalL2 a.1) :
    inner ℂ f (suzukiPrimitiveWeilSourceOperator a g) =
      suzukiWeilIntervalForm a
        (suzukiAperturePrimitiveCCMFormVector a f)
        (suzukiAperturePrimitiveCCMFormVector a g) := by
  simp only [suzukiPrimitiveWeilSourceOperator,
    add_apply, inner_add_right,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  rw [suzukiWeilIntervalForm,
    suzukiWeilIntervalFormEmbedding_primitiveCCMFormVector,
    suzukiWeilIntervalFormEmbedding_primitiveCCMFormVector]
  change inner ℂ (suzukiAperturePrimitiveCCMFormVector a f)
      (suzukiAperturePrimitiveCCMFormVector a g) +
      inner ℂ (suzukiAperturePrimitive a.1 f)
        (suzukiWeilIntervalBoundedRemainder a
          (suzukiAperturePrimitive a.1 g)) = _
  congr 1
  exact ((suzukiWeilIntervalBoundedRemainder_isSelfAdjoint a).isSymmetric
    (suzukiAperturePrimitive a.1 f)
    (suzukiAperturePrimitive a.1 g)).symm

/-! Strict-interior smooth density infrastructure. -/

/-- Radius increasing from zero to the aperture while remaining strictly inside it. -/
def suzukiInteriorCutoffRadius (a : SuzukiPositiveAperture) (n : ℕ) : ℝ :=
  a.1 - a.1 / ((n : ℝ) + 1)

theorem suzukiInteriorCutoffRadius_nonneg
    (a : SuzukiPositiveAperture) (n : ℕ) :
    0 ≤ suzukiInteriorCutoffRadius a n := by
  unfold suzukiInteriorCutoffRadius
  have hn : 1 ≤ (n : ℝ) + 1 := by
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hdiv : a.1 / ((n : ℝ) + 1) ≤ a.1 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [a.2]
  linarith

theorem suzukiInteriorCutoffRadius_lt
    (a : SuzukiPositiveAperture) (n : ℕ) :
    suzukiInteriorCutoffRadius a n < a.1 := by
  unfold suzukiInteriorCutoffRadius
  have : 0 < a.1 / ((n : ℝ) + 1) :=
    div_pos a.2 (by positivity)
  linarith

theorem tendsto_suzukiInteriorCutoffRadius (a : SuzukiPositiveAperture) :
    Tendsto (suzukiInteriorCutoffRadius a) atTop (𝓝 a.1) := by
  have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmul : Tendsto (fun n : ℕ =>
      a.1 * (1 / ((n : ℝ) + 1))) atTop (𝓝 (a.1 * 0)) :=
    tendsto_const_nhds.mul hzero
  have hconst : Tendsto (fun _ : ℕ => a.1) atTop (𝓝 a.1) :=
    tendsto_const_nhds
  change Tendsto (fun n : ℕ => a.1 - a.1 / ((n : ℝ) + 1))
    atTop (𝓝 a.1)
  simpa only [suzukiInteriorCutoffRadius, mul_zero, sub_zero,
    div_eq_mul_inv, one_div, one_mul] using hconst.sub hmul

/-- Two-sided smooth cutoff with a strict support margin. -/
def suzukiInteriorSmoothCutoff
    (a : SuzukiPositiveAperture) (n : ℕ) (t : ℝ) : ℂ :=
  suzukiUpperSmoothCutoff (suzukiInteriorCutoffRadius a n) n t *
    suzukiUpperSmoothCutoff (suzukiInteriorCutoffRadius a n) n (-t)

theorem measurable_suzukiInteriorSmoothCutoff
    (a : SuzukiPositiveAperture) (n : ℕ) :
    Measurable (suzukiInteriorSmoothCutoff a n) := by
  exact (measurable_suzukiUpperSmoothCutoff _ _).mul
    ((measurable_suzukiUpperSmoothCutoff _ _).comp measurable_neg)

theorem contDiff_suzukiInteriorSmoothCutoff
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiInteriorSmoothCutoff a n) := by
  exact (contDiff_suzukiUpperSmoothCutoff _ _).mul
    ((contDiff_suzukiUpperSmoothCutoff _ _).comp (by fun_prop))

theorem norm_suzukiInteriorSmoothCutoff_le_one
    (a : SuzukiPositiveAperture) (n : ℕ) (t : ℝ) :
    ‖suzukiInteriorSmoothCutoff a n t‖ ≤ 1 := by
  rw [suzukiInteriorSmoothCutoff, norm_mul]
  calc
    _ ≤ 1 * 1 := mul_le_mul
      (norm_suzukiUpperSmoothCutoff_le_one _ _ _)
      (norm_suzukiUpperSmoothCutoff_le_one _ _ _)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem support_suzukiInteriorSmoothCutoff_subset
    (a : SuzukiPositiveAperture) (n : ℕ) :
    Function.support (suzukiInteriorSmoothCutoff a n) ⊆
      Ioo (-(suzukiInteriorCutoffRadius a n))
        (suzukiInteriorCutoffRadius a n) := by
  intro t ht
  change suzukiInteriorSmoothCutoff a n t ≠ 0 at ht
  have hne₁ : suzukiUpperSmoothCutoff
      (suzukiInteriorCutoffRadius a n) n t ≠ 0 := by
    intro hz
    exact ht (by simp [suzukiInteriorSmoothCutoff, hz])
  have hne₂ : suzukiUpperSmoothCutoff
      (suzukiInteriorCutoffRadius a n) n (-t) ≠ 0 := by
    intro hz
    exact ht (by simp [suzukiInteriorSmoothCutoff, hz])
  constructor
  · have hnot : ¬suzukiInteriorCutoffRadius a n ≤ -t := by
      intro h
      exact hne₂ (suzukiUpperSmoothCutoff_eq_zero_of_le _ _ h)
    linarith
  · exact lt_of_not_ge fun h =>
      hne₁ (suzukiUpperSmoothCutoff_eq_zero_of_le _ _ h)

theorem tsupport_suzukiInteriorSmoothCutoff_subset
    (a : SuzukiPositiveAperture) (n : ℕ) :
    tsupport (suzukiInteriorSmoothCutoff a n) ⊆
      Icc (-(suzukiInteriorCutoffRadius a n))
        (suzukiInteriorCutoffRadius a n) :=
  closure_minimal
    (support_suzukiInteriorSmoothCutoff_subset a n |>.trans Ioo_subset_Icc_self)
    isClosed_Icc

theorem tsupport_suzukiInteriorSmoothCutoff_subset_aperture
    (a : SuzukiPositiveAperture) (n : ℕ) :
    tsupport (suzukiInteriorSmoothCutoff a n) ⊆ Ioo (-a.1) a.1 := by
  intro t ht
  have h := tsupport_suzukiInteriorSmoothCutoff_subset a n ht
  have hr := suzukiInteriorCutoffRadius_lt a n
  constructor <;> linarith [h.1, h.2]

theorem hasCompactSupport_suzukiInteriorSmoothCutoff
    (a : SuzukiPositiveAperture) (n : ℕ) :
    HasCompactSupport (suzukiInteriorSmoothCutoff a n) := by
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (tsupport_suzukiInteriorSmoothCutoff_subset a n)

theorem tendsto_suzukiInteriorSmoothCutoff
    (a : SuzukiPositiveAperture) (t : ℝ) :
    Tendsto (fun n => suzukiInteriorSmoothCutoff a n t) atTop
      (𝓝 ((Ioo (-a.1) a.1).indicator (fun _ => (1 : ℂ)) t)) := by
  by_cases ht : t ∈ Ioo (-a.1) a.1
  · rw [indicator_of_mem ht]
    let A₁ : ℝ := (t + a.1) / 2
    let A₂ : ℝ := (-t + a.1) / 2
    have htA₁ : t < A₁ := by dsimp [A₁]; linarith [ht.2]
    have hA₁a : A₁ < a.1 := by dsimp [A₁]; linarith [ht.2]
    have hntA₂ : -t < A₂ := by dsimp [A₂]; linarith [ht.1]
    have hA₂a : A₂ < a.1 := by dsimp [A₂]; linarith [ht.1]
    obtain ⟨N₁ : ℕ, hN₁⟩ := exists_nat_gt (1 / (A₁ - t))
    obtain ⟨N₂ : ℕ, hN₂⟩ := exists_nat_gt (1 / (A₂ + t))
    have hr₁ := (tendsto_suzukiInteriorCutoffRadius a).eventually_const_lt hA₁a
    have hr₂ := (tendsto_suzukiInteriorCutoffRadius a).eventually_const_lt hA₂a
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop N₁, eventually_ge_atTop N₂, hr₁, hr₂]
      with n hn₁ hn₂ hrad₁ hrad₂
    have hn₁' : (N₁ : ℝ) ≤ n := by exact_mod_cast hn₁
    have hn₂' : (N₂ : ℝ) ≤ n := by exact_mod_cast hn₂
    have harg₁ : 1 ≤ (A₁ - t) * ((n : ℝ) + 1) := by
      have : 1 / (A₁ - t) < (n : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ (sub_pos.mpr htA₁)] at this
      linarith
    have harg₂ : 1 ≤ (A₂ + t) * ((n : ℝ) + 1) := by
      have : 1 / (A₂ + t) < (n : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ (by linarith [hntA₂])] at this
      linarith
    have hwide₁ : 1 ≤
        (suzukiInteriorCutoffRadius a n - t) * ((n : ℝ) + 1) := by
      have hn : 0 ≤ (n : ℝ) + 1 := by positivity
      nlinarith
    have hwide₂ : 1 ≤
        (suzukiInteriorCutoffRadius a n + t) * ((n : ℝ) + 1) := by
      have hn : 0 ≤ (n : ℝ) + 1 := by positivity
      nlinarith
    simp only [suzukiInteriorSmoothCutoff, suzukiUpperSmoothCutoff]
    rw [Real.smoothTransition.one_of_one_le hwide₁,
      Real.smoothTransition.one_of_one_le (by simpa [sub_neg_eq_add] using hwide₂)]
    norm_num
  · rw [indicator_of_notMem ht]
    apply tendsto_nhds_of_eventually_eq
    filter_upwards with n
    simp only [mem_Ioo, not_and_or, not_lt] at ht
    rcases ht with hleft | hright
    · have hzero : suzukiUpperSmoothCutoff
          (suzukiInteriorCutoffRadius a n) n (-t) = 0 :=
        suzukiUpperSmoothCutoff_eq_zero_of_le _ _
          (by linarith [suzukiInteriorCutoffRadius_lt a n])
      simp [suzukiInteriorSmoothCutoff, hzero]
    · have hzero : suzukiUpperSmoothCutoff
          (suzukiInteriorCutoffRadius a n) n t = 0 :=
        suzukiUpperSmoothCutoff_eq_zero_of_le _ _
          (by linarith [suzukiInteriorCutoffRadius_lt a n])
      simp [suzukiInteriorSmoothCutoff, hzero]

/-- Whole-line multiplier by the strict-interior smooth cutoff. -/
def suzukiInteriorSmoothCutoffMul
    (a : SuzukiPositiveAperture) (n : ℕ) : SoninL2 →L[ℂ] SoninL2 :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (measurable_suzukiInteriorSmoothCutoff a n) (C := 1) (by norm_num)
    (norm_suzukiInteriorSmoothCutoff_le_one a n)

/-- Whole-line multiplier by the open aperture. -/
def suzukiOpenApertureCutoff (a : SuzukiPositiveAperture) :
    SoninL2 →L[ℂ] SoninL2 :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (measurable_const.indicator measurableSet_Ioo) (C := 1) (by norm_num)
    (fun t => by
      by_cases ht : t ∈ Ioo (-a.1) a.1
      · rw [indicator_of_mem ht, norm_one]
      · rw [indicator_of_notMem ht, norm_zero]
        norm_num)

theorem suzukiOpenApertureCutoff_eq_suzukiCutoff
    (a : SuzukiPositiveAperture) (q : SoninL2) :
    suzukiOpenApertureCutoff a q = suzukiCutoff a.1 q := by
  apply Lp.ext
  filter_upwards [
    lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
      (measurable_const.indicator measurableSet_Ioo) (C := 1) (by norm_num)
      (fun t => by
        by_cases ht : t ∈ Ioo (-a.1) a.1
        · rw [indicator_of_mem ht, norm_one]
        · rw [indicator_of_notMem ht, norm_zero]
          norm_num) q,
    indicatorCutoff_ae (Icc (-a.1) a.1) measurableSet_Icc q,
    volume.ae_ne (-a.1), volume.ae_ne a.1] with t hopen hclosed hleft hright
  change suzukiOpenApertureCutoff a q t =
    (Ioo (-a.1) a.1).indicator (fun _ => (1 : ℂ)) t * q t at hopen
  change suzukiCutoff a.1 q t =
    (Icc (-a.1) a.1).indicator (fun y => q y) t at hclosed
  rw [hopen]
  change (Ioo (-a.1) a.1).indicator (fun _ => (1 : ℂ)) t * q t = _
  rw [show suzukiCutoff a.1 q t =
      (Icc (-a.1) a.1).indicator (fun y => q y) t by
    simpa only [suzukiCutoff] using hclosed]
  have hmem : t ∈ Icc (-a.1) a.1 ↔ t ∈ Ioo (-a.1) a.1 := by
    constructor
    · intro ht
      exact ⟨lt_of_le_of_ne ht.1 (Ne.symm hleft),
        lt_of_le_of_ne ht.2 hright⟩
    · intro ht
      exact Ioo_subset_Icc_self ht
  by_cases ht : t ∈ Ioo (-a.1) a.1
  · have ht' : t ∈ Icc (-a.1) a.1 := hmem.mpr ht
    simp [ht, ht']
  · have ht' : t ∉ Icc (-a.1) a.1 := fun h => ht (hmem.mp h)
    simp [ht, ht']

/-- Strict smooth cutoff multipliers converge strongly to the aperture projection. -/
theorem tendsto_suzukiInteriorSmoothCutoffMul
    (a : SuzukiPositiveAperture) (q : SoninL2) :
    Tendsto (fun n => suzukiInteriorSmoothCutoffMul a n q) atTop
      (𝓝 (suzukiCutoff a.1 q)) := by
  have h := tendsto_lpBoundedMulCLM_apply
    (fun n => measurable_suzukiInteriorSmoothCutoff a n)
    (measurable_const.indicator measurableSet_Ioo)
    (by norm_num)
    (fun n => norm_suzukiInteriorSmoothCutoff_le_one a n)
    (fun t => by
      by_cases ht : t ∈ Ioo (-a.1) a.1
      · rw [indicator_of_mem ht, norm_one]
      · rw [indicator_of_notMem ht, norm_zero]
        norm_num)
    (tendsto_suzukiInteriorSmoothCutoff a) q
  change Tendsto (fun n => suzukiInteriorSmoothCutoffMul a n q) atTop
    (𝓝 (suzukiOpenApertureCutoff a q)) at h
  rw [suzukiOpenApertureCutoff_eq_suzukiCutoff a q] at h
  exact h

/-- Strict-interior compact-smooth functions are dense in the fixed space of the aperture
projection. -/
theorem exists_suzukiInteriorCompactSmoothL2_dist_lt
    (a : SuzukiPositiveAperture) {q : SoninL2}
    (hq : suzukiCutoff a.1 q = q) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : ℝ → ℂ) (hcompact : HasCompactSupport g)
        (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g) (r : ℝ),
      0 ≤ r ∧ r < a.1 ∧
        Function.support g ⊆ Ioo (-r) r ∧
        tsupport g ⊆ Icc (-r) r ∧
        dist q (suzukiComplexTestL2 g hsmooth hcompact) < ε := by
  let T : ℕ → SoninL2 →L[ℂ] SoninL2 :=
    fun n => suzukiInteriorSmoothCutoffMul a n
  have hTq : Tendsto (fun n => T n q) atTop (𝓝 q) := by
    have hconv := tendsto_suzukiInteriorSmoothCutoffMul a q
    rw [hq] at hconv
    exact hconv
  obtain ⟨n, hn⟩ : ∃ n : ℕ, dist q (T n q) < ε / 2 := by
    obtain ⟨N, hN⟩ :=
      (Metric.tendsto_atTop.1 hTq) (ε / 2) (by linarith)
    exact ⟨N, by simpa [dist_comm] using hN N le_rfl⟩
  let D : Set SoninL2 :=
    {v | ∃ g : ℝ → ℂ, (v : ℝ → ℂ) =ᵐ[volume] g ∧
      HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g}
  have hD : Dense D := by
    simpa only [D] using
      (MeasureTheory.Lp.dense_hasCompactSupport_contDiff
        (F := ℂ) (μ := (volume : Measure ℝ)) (p := 2) (by norm_num))
  obtain ⟨v, hvD, hv⟩ := hD.exists_dist_lt q (show 0 < ε / 2 by linarith)
  obtain ⟨g, hvg, hgcompact, hgsmooth⟩ := hvD
  let g' : ℝ → ℂ := fun t => suzukiInteriorSmoothCutoff a n t * g t
  have hg'smooth : ContDiff ℝ (⊤ : ℕ∞) g' :=
    (contDiff_suzukiInteriorSmoothCutoff a n).mul hgsmooth
  have hg'compact : HasCompactSupport g' := hgcompact.mul_left
  have hg'support : Function.support g' ⊆
      Ioo (-(suzukiInteriorCutoffRadius a n))
        (suzukiInteriorCutoffRadius a n) :=
    fun t ht => support_suzukiInteriorSmoothCutoff_subset a n (by
      intro hzero
      exact ht (by simp [g', hzero]))
  have hg'tsupport : tsupport g' ⊆
      Icc (-(suzukiInteriorCutoffRadius a n))
        (suzukiInteriorCutoffRadius a n) :=
    (tsupport_mul_subset_left (f := suzukiInteriorSmoothCutoff a n) (g := g)).trans
      (tsupport_suzukiInteriorSmoothCutoff_subset a n)
  have hTv : T n v = suzukiComplexTestL2 g' hg'smooth hg'compact := by
    apply Lp.ext
    filter_upwards [
      lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
        (measurable_suzukiInteriorSmoothCutoff a n) (C := 1) (by norm_num)
        (norm_suzukiInteriorSmoothCutoff_le_one a n) v,
      hvg,
      suzukiComplexTestL2_coeFn g' hg'smooth hg'compact
    ] with t hmul hbase hout
    change suzukiInteriorSmoothCutoffMul a n v t =
      suzukiInteriorSmoothCutoff a n t * v t at hmul
    change suzukiInteriorSmoothCutoffMul a n v t =
      suzukiComplexTestL2 g' hg'smooth hg'compact t
    rw [hmul, hbase, hout]
  refine ⟨g', hg'compact, hg'smooth, suzukiInteriorCutoffRadius a n,
    suzukiInteriorCutoffRadius_nonneg a n,
    suzukiInteriorCutoffRadius_lt a n, hg'support, hg'tsupport, ?_⟩
  rw [← hTv]
  have hnormT : ‖T n‖ ≤ 1 :=
    norm_lpBoundedMulCLM_le (measurable_suzukiInteriorSmoothCutoff a n)
      (by norm_num) (norm_suzukiInteriorSmoothCutoff_le_one a n)
  have hmap : dist (T n q) (T n v) ≤ dist q v := by
    calc
      dist (T n q) (T n v) ≤ ‖T n‖ * dist q v := (T n).dist_le_opNorm q v
      _ ≤ 1 * dist q v :=
        mul_le_mul_of_nonneg_right hnormT dist_nonneg
      _ = dist q v := one_mul _
  calc
    dist q (T n v) ≤ dist q (T n q) + dist (T n q) (T n v) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hn (hmap.trans_lt hv)
    _ = ε := by ring

/-- A strict-interior smooth whole-line vector bundled in the aperture Hilbert space. -/
def suzukiInteriorSmoothApertureVector
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g) (hcompact : HasCompactSupport g)
    (hinterior : tsupport g ⊆ Ioo (-a.1) a.1) :
    suzukiApertureHilbert a :=
  ⟨suzukiComplexTestL2 g hsmooth hcompact, by
    rw [suzukiApertureHilbert, physicalForbidden, LinearMap.mem_range]
    refine ⟨suzukiComplexTestL2 g hsmooth hcompact, ?_⟩
    apply Lp.ext
    filter_upwards [indicatorCutoff_ae (centralInterval a.1)
        (measurableSet_centralInterval a.1)
        (suzukiComplexTestL2 g hsmooth hcompact),
      suzukiComplexTestL2_coeFn g hsmooth hcompact] with x hcut hg
    change (indicatorCutoff (centralInterval a.1)
        (measurableSet_centralInterval a.1)
        (suzukiComplexTestL2 g hsmooth hcompact) : SoninL2) x =
      (suzukiComplexTestL2 g hsmooth hcompact : SoninL2) x
    rw [hcut]
    by_cases hx : x ∈ centralInterval a.1
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hg]
      symm
      apply Function.notMem_support.mp
      intro hxg
      exact hx (by simpa [centralInterval] using
        Ioo_subset_Icc_self (hinterior (subset_tsupport g hxg)))⟩

theorem suzukiApertureZeroExtendL2_restrict_interiorSmooth
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g) (hcompact : HasCompactSupport g)
    (hinterior : tsupport g ⊆ Ioo (-a.1) a.1) :
    suzukiApertureZeroExtendL2
        (suzukiApertureRestrictL2 a.1
          (suzukiComplexTestL2 g hsmooth hcompact)) =
      suzukiComplexTestL2 g hsmooth hcompact := by
  exact suzukiApertureZeroExtendL2_restrict_eq a
    (suzukiInteriorSmoothApertureVector a g hsmooth hcompact hinterior)

theorem dist_restrict_interiorSmooth
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1)
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g)
    (hinterior : tsupport g ⊆ Ioo (-a.1) a.1) :
    dist f (suzukiApertureRestrictL2 a.1
        (suzukiComplexTestL2 g hsmooth hcompact)) =
      dist (suzukiApertureZeroExtendL2 f)
        (suzukiComplexTestL2 g hsmooth hcompact) := by
  rw [dist_eq_norm, dist_eq_norm, ← norm_suzukiApertureZeroExtendL2]
  have hsub : suzukiApertureZeroExtendL2
      (f - suzukiApertureRestrictL2 a.1
        (suzukiComplexTestL2 g hsmooth hcompact)) =
      suzukiApertureZeroExtendL2 f -
        suzukiApertureZeroExtendL2
          (suzukiApertureRestrictL2 a.1
            (suzukiComplexTestL2 g hsmooth hcompact)) := by
    exact congrArg Subtype.val
      (map_sub (suzukiApertureZeroExtendLinearIsometry a) f
        (suzukiApertureRestrictL2 a.1
          (suzukiComplexTestL2 g hsmooth hcompact)))
  rw [hsub, suzukiApertureZeroExtendL2_restrict_interiorSmooth
    a g hsmooth hcompact hinterior]

open GaloisForLFunctions.HTGeometry

/-- Fixed unit-mass smooth bump in the middle half of the aperture. -/
def suzukiInteriorMeanBump (a : SuzukiPositiveAperture) : ℝ → ℂ :=
  complexBumpMollifier (div_pos a.2 (by norm_num : (0 : ℝ) < 2))

theorem contDiff_suzukiInteriorMeanBump (a : SuzukiPositiveAperture) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiInteriorMeanBump a) :=
  contDiff_complexBumpMollifier _

theorem hasCompactSupport_suzukiInteriorMeanBump (a : SuzukiPositiveAperture) :
    HasCompactSupport (suzukiInteriorMeanBump a) :=
  hasCompactSupport_complexBumpMollifier _

theorem support_suzukiInteriorMeanBump_subset (a : SuzukiPositiveAperture) :
    Function.support (suzukiInteriorMeanBump a) ⊆ Ioo (-(a.1 / 2)) (a.1 / 2) := by
  intro x hx
  have hxreal : bumpMollifier
      (div_pos a.2 (by norm_num : (0 : ℝ) < 2)) x ≠ 0 := by
    intro hz
    exact hx (by simp [suzukiInteriorMeanBump, complexBumpMollifier, hz])
  have hball : x ∈ Metric.ball (0 : ℝ) (a.1 / 2) := by
    change x ∈ Metric.ball (0 : ℝ)
      (widthBump (div_pos a.2 (by norm_num : (0 : ℝ) < 2))).rOut
    rw [← (widthBump
      (div_pos a.2 (by norm_num : (0 : ℝ) < 2))).support_normed_eq
        (μ := (volume : Measure ℝ))]
    exact hxreal
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hball
  exact abs_lt.mp hball

theorem tsupport_suzukiInteriorMeanBump_subset (a : SuzukiPositiveAperture) :
    tsupport (suzukiInteriorMeanBump a) ⊆ Icc (-(a.1 / 2)) (a.1 / 2) :=
  closure_minimal
    (support_suzukiInteriorMeanBump_subset a |>.trans Ioo_subset_Icc_self)
    isClosed_Icc

theorem integral_suzukiInteriorMeanBump (a : SuzukiPositiveAperture) :
    (∫ x : ℝ, suzukiInteriorMeanBump a x) = 1 := by
  change (∫ x : ℝ, ((bumpMollifier
    (div_pos a.2 (by norm_num : (0 : ℝ) < 2)) x : ℝ) : ℂ)) = 1
  have h := congrArg (fun x : ℝ => (x : ℂ))
    (integral_bumpMollifier
      (div_pos a.2 (by norm_num : (0 : ℝ) < 2)))
  exact (integral_ofReal (𝕜 := ℂ)).trans h

/-- Exact unit-mass correction of a smooth interior test. -/
def suzukiMeanCorrectedInteriorTest
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => g x - (∫ t : ℝ, g t) * suzukiInteriorMeanBump a x

theorem integral_suzukiMeanCorrectedInteriorTest
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgintegrable : Integrable g) :
    (∫ x : ℝ, suzukiMeanCorrectedInteriorTest a g x) = 0 := by
  have hrho : Integrable (suzukiInteriorMeanBump a) :=
    (contDiff_suzukiInteriorMeanBump a).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_suzukiInteriorMeanBump a)
  have hmul : Integrable (fun x : ℝ =>
      (∫ t : ℝ, g t) * suzukiInteriorMeanBump a x) :=
    hrho.const_mul _
  change (∫ x : ℝ, g x -
    (∫ t : ℝ, g t) * suzukiInteriorMeanBump a x) = 0
  rw [integral_sub hgintegrable hmul, integral_const_mul,
    integral_suzukiInteriorMeanBump, mul_one, sub_self]

theorem contDiff_suzukiMeanCorrectedInteriorTest
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgsmooth : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiMeanCorrectedInteriorTest a g) := by
  exact hgsmooth.sub
    ((contDiff_const.mul (contDiff_suzukiInteriorMeanBump a)))

theorem hasCompactSupport_suzukiMeanCorrectedInteriorTest
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgcompact : HasCompactSupport g) :
    HasCompactSupport (suzukiMeanCorrectedInteriorTest a g) := by
  exact hgcompact.sub
    ((hasCompactSupport_suzukiInteriorMeanBump a).mul_left)

theorem support_suzukiMeanCorrectedInteriorTest_subset
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ) (r : ℝ)
    (hgsupport : Function.support g ⊆ Ioo (-r) r) :
    Function.support (suzukiMeanCorrectedInteriorTest a g) ⊆
      Ioo (-(max r (a.1 / 2))) (max r (a.1 / 2)) := by
  intro x hx
  by_contra hout
  have hnotg : x ∉ Ioo (-r) r := by
    intro hxin
    apply hout
    exact ⟨lt_of_le_of_lt (neg_le_neg (le_max_left _ _)) hxin.1,
      lt_of_lt_of_le hxin.2 (le_max_left _ _)⟩
  have hnotrho : x ∉ Ioo (-(a.1 / 2)) (a.1 / 2) := by
    intro hxin
    apply hout
    exact ⟨lt_of_le_of_lt (neg_le_neg (le_max_right _ _)) hxin.1,
      lt_of_lt_of_le hxin.2 (le_max_right _ _)⟩
  have hgzero : g x = 0 := Function.notMem_support.mp
    (fun hxg => hnotg (hgsupport hxg))
  have hrhozero : suzukiInteriorMeanBump a x = 0 :=
    Function.notMem_support.mp
      (fun hxrho => hnotrho (support_suzukiInteriorMeanBump_subset a hxrho))
  exact hx (by simp [suzukiMeanCorrectedInteriorTest, hgzero, hrhozero])

theorem tsupport_suzukiMeanCorrectedInteriorTest_subset
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ) (r : ℝ)
    (hgtsupport : tsupport g ⊆ Icc (-r) r) :
    tsupport (suzukiMeanCorrectedInteriorTest a g) ⊆
      Icc (-(max r (a.1 / 2))) (max r (a.1 / 2)) := by
  change tsupport (fun x => g x -
    (∫ t : ℝ, g t) * suzukiInteriorMeanBump a x) ⊆ _
  refine (tsupport_sub g (fun x =>
    (∫ t : ℝ, g t) * suzukiInteriorMeanBump a x)).trans ?_
  apply union_subset
  · intro x hx
    have h := hgtsupport hx
    exact ⟨le_trans (neg_le_neg (le_max_left _ _)) h.1,
      le_trans h.2 (le_max_left _ _)⟩
  · intro x hx
    have hx' : x ∈ tsupport (suzukiInteriorMeanBump a) :=
      tsupport_mul_subset_right
        (f := fun _ : ℝ => (∫ t : ℝ, g t))
        (g := suzukiInteriorMeanBump a) hx
    have h := tsupport_suzukiInteriorMeanBump_subset a hx'
    exact ⟨le_trans (neg_le_neg (le_max_right _ _)) h.1,
      le_trans h.2 (le_max_right _ _)⟩

theorem suzukiMeanCorrectionRadius_nonneg
    (a : SuzukiPositiveAperture) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ max r (a.1 / 2) :=
  le_trans hr (le_max_left _ _)

theorem suzukiMeanCorrectionRadius_lt
    (a : SuzukiPositiveAperture) {r : ℝ} (hr : r < a.1) :
    max r (a.1 / 2) < a.1 := by
  rw [max_lt_iff]
  exact ⟨hr, by linarith [a.2]⟩

/-- Compact primitive of a smooth zero-mass test. -/
def suzukiSmoothIntegralPrimitive (r : ℝ) (φ : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x in (-r)..t, φ x

theorem hasDerivAt_suzukiSmoothIntegralPrimitive
    (r : ℝ) (φ : ℝ → ℂ) (hφcontinuous : Continuous φ) (t : ℝ) :
    HasDerivAt (suzukiSmoothIntegralPrimitive r φ) (φ t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    (hφcontinuous.intervalIntegrable _ _)
    (hφcontinuous.stronglyMeasurableAtFilter (μ := volume) (l := 𝓝 t))
    hφcontinuous.continuousAt

theorem deriv_suzukiSmoothIntegralPrimitive
    (r : ℝ) (φ : ℝ → ℂ) (hφcontinuous : Continuous φ) (t : ℝ) :
    deriv (suzukiSmoothIntegralPrimitive r φ) t = φ t :=
  (hasDerivAt_suzukiSmoothIntegralPrimitive r φ hφcontinuous t).deriv

theorem contDiff_suzukiSmoothIntegralPrimitive
    (r : ℝ) (φ : ℝ → ℂ) (hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiSmoothIntegralPrimitive r φ) := by
  refine contDiff_infty_iff_deriv.mpr ⟨fun t =>
    (hasDerivAt_suzukiSmoothIntegralPrimitive r φ hφsmooth.continuous t).differentiableAt,
    ?_⟩
  rw [show deriv (suzukiSmoothIntegralPrimitive r φ) = φ by
    funext t
    exact deriv_suzukiSmoothIntegralPrimitive r φ hφsmooth.continuous t]
  exact hφsmooth

theorem suzukiSmoothIntegralPrimitive_eq_zero_of_le_neg
    {r : ℝ} {φ : ℝ → ℂ} (hφsupport : Function.support φ ⊆ Ioo (-r) r)
    {t : ℝ} (ht : t ≤ -r) :
    suzukiSmoothIntegralPrimitive r φ t = 0 := by
  rw [suzukiSmoothIntegralPrimitive, intervalIntegral.integral_of_ge ht]
  apply neg_eq_zero.mpr
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
  apply Function.notMem_support.mp
  intro hxφ
  have hi := hφsupport hxφ
  linarith [hx.2, hi.1]

theorem suzukiSmoothIntegralPrimitive_eq_zero_of_ge
    {r : ℝ} {φ : ℝ → ℂ} (hφsupport : Function.support φ ⊆ Ioo (-r) r)
    (hφintegral : (∫ x : ℝ, φ x) = 0) {t : ℝ} (ht : r ≤ t) :
    suzukiSmoothIntegralPrimitive r φ t = 0 := by
  calc
    suzukiSmoothIntegralPrimitive r φ t = ∫ x : ℝ, φ x := by
      apply intervalIntegral.integral_eq_integral_of_support_subset
      intro x hx
      have hi := hφsupport hx
      exact ⟨hi.1, hi.2.le.trans ht⟩
    _ = 0 := hφintegral

theorem support_suzukiSmoothIntegralPrimitive_subset
    {r : ℝ} {φ : ℝ → ℂ} (hφsupport : Function.support φ ⊆ Ioo (-r) r)
    (hφintegral : (∫ x : ℝ, φ x) = 0) :
    Function.support (suzukiSmoothIntegralPrimitive r φ) ⊆ Icc (-r) r := by
  intro t ht
  change suzukiSmoothIntegralPrimitive r φ t ≠ 0 at ht
  by_contra hout
  simp only [mem_Icc, not_and_or, not_le] at hout
  rcases hout with hleft | hright
  · exact ht (suzukiSmoothIntegralPrimitive_eq_zero_of_le_neg hφsupport hleft.le)
  · exact ht (suzukiSmoothIntegralPrimitive_eq_zero_of_ge
      hφsupport hφintegral hright.le)

theorem hasCompactSupport_suzukiSmoothIntegralPrimitive
    {r : ℝ} {φ : ℝ → ℂ} (hφsupport : Function.support φ ⊆ Ioo (-r) r)
    (hφintegral : (∫ x : ℝ, φ x) = 0) :
    HasCompactSupport (suzukiSmoothIntegralPrimitive r φ) := by
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal
      (support_suzukiSmoothIntegralPrimitive_subset hφsupport hφintegral)
      isClosed_Icc)

theorem hasCompactSupport_of_support_subset_Ioo
    {r : ℝ} {φ : ℝ → ℂ} (hφsupport : Function.support φ ⊆ Ioo (-r) r) :
    HasCompactSupport φ := by
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal (hφsupport.trans Ioo_subset_Icc_self) isClosed_Icc)

theorem tsupport_suzukiSmoothIntegralPrimitive_subset
    {r : ℝ} {φ : ℝ → ℂ} (hφsupport : Function.support φ ⊆ Ioo (-r) r)
    (hφintegral : (∫ x : ℝ, φ x) = 0) :
    tsupport (suzukiSmoothIntegralPrimitive r φ) ⊆ Icc (-r) r :=
  closure_minimal
    (support_suzukiSmoothIntegralPrimitive_subset hφsupport hφintegral)
    isClosed_Icc

/-- Strict-interior smooth source obtained by integrating a smooth zero-mass test. -/
def suzukiSmoothIntegralPrimitiveSource
    (a : SuzukiPositiveAperture) (r : ℝ) (hr : r < a.1)
    (φ : ℝ → ℂ) (hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφsupport : Function.support φ ⊆ Ioo (-r) r)
    (hφintegral : (∫ x : ℝ, φ x) = 0) :
    CCMComplexSmoothInteriorSource a where
  toFun := suzukiSmoothIntegralPrimitive r φ
  smooth := contDiff_suzukiSmoothIntegralPrimitive r φ hφsmooth
  hasCompactSupport :=
    hasCompactSupport_suzukiSmoothIntegralPrimitive hφsupport hφintegral
  tsupport_subset := by
    intro x hx
    have hi := tsupport_suzukiSmoothIntegralPrimitive_subset hφsupport hφintegral hx
    exact ⟨lt_of_lt_of_le (neg_lt_neg hr) hi.1,
      lt_of_le_of_lt hi.2 hr⟩

theorem suzukiSmoothIntegralPrimitiveSource_toDerivativeZeroMean
    (a : SuzukiPositiveAperture) (r : ℝ) (hr : r < a.1)
    (φ : ℝ → ℂ) (hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφsupport : Function.support φ ⊆ Ioo (-r) r)
    (hφintegral : (∫ x : ℝ, φ x) = 0) :
    ((suzukiSmoothIntegralPrimitiveSource a r hr φ hφsmooth hφsupport hφintegral
        ).toDerivativeZeroMean : SuzukiApertureIntervalL2 a.1) =
      suzukiApertureRestrictL2 a.1
        (suzukiComplexTestL2 φ hφsmooth
          (hasCompactSupport_of_support_subset_Ioo hφsupport)) := by
  apply Lp.ext
  let u := suzukiSmoothIntegralPrimitiveSource a r hr φ hφsmooth hφsupport hφintegral
  let test : SoninL2 := suzukiComplexTestL2 φ hφsmooth
    (hasCompactSupport_of_support_subset_Ioo hφsupport)
  have htestSub : (fun x : SuzukiApertureInterval a.1 => test (x : ℝ)) =ᵐ[volume]
      fun x => φ (x : ℝ) :=
    (ae_restrict_iff_subtype measurableSet_Icc).mp (ae_restrict_of_ae
      (suzukiComplexTestL2_coeFn φ hφsmooth
        (hasCompactSupport_of_support_subset_Ioo hφsupport)))
  filter_upwards [u.toDerivativeZeroMean_coeFn,
    suzukiApertureRestrictL2_coeFn a.1 test,
    suzukiApertureRestrictRepresentative_ae a.1 test,
    htestSub]
      with x hleft hrestrict hrep htest
  change ((u.toDerivativeZeroMean : SuzukiApertureZeroMean a) :
      SuzukiApertureIntervalL2 a.1) x =
    suzukiApertureRestrictL2 a.1 test x
  rw [hleft, hrestrict, hrep, htest]
  exact deriv_suzukiSmoothIntegralPrimitive r φ hφsmooth.continuous (x : ℝ)

theorem suzukiApertureIntervalMean_restrict_interiorSmooth
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g) (hcompact : HasCompactSupport g)
    (hinterior : tsupport g ⊆ Ioo (-a.1) a.1) :
    suzukiApertureIntervalMean a
        (suzukiApertureRestrictL2 a.1
          (suzukiComplexTestL2 g hsmooth hcompact)) =
      ∫ x : ℝ, g x := by
  let G : SuzukiApertureIntervalL2 a.1 :=
    suzukiApertureRestrictL2 a.1 (suzukiComplexTestL2 g hsmooth hcompact)
  have hbridge := integral_suzukiApertureZeroExtend_mul a.1 G (fun _ => (1 : ℂ))
  simp only [mul_one] at hbridge
  have hzeroL2 := suzukiApertureZeroExtendL2_restrict_interiorSmooth
    a g hsmooth hcompact hinterior
  have hwhole : (suzukiApertureZeroExtend G : ℝ → ℂ) =ᵐ[volume] g := by
    have hzeroCoe := suzukiApertureZeroExtendL2_coeFn G
    have htestCoe := suzukiComplexTestL2_coeFn g hsmooth hcompact
    have hL2 : ((suzukiApertureZeroExtendL2 G : SoninL2) : ℝ → ℂ) =ᵐ[volume]
        (suzukiComplexTestL2 g hsmooth hcompact : SoninL2) := by
      rw [hzeroL2]
    exact hzeroCoe.symm.trans (hL2.trans htestCoe)
  rw [suzukiApertureIntervalMean]
  exact hbridge.symm.trans (integral_congr_ae hwhole)

theorem suzukiComplexTestL2_meanCorrected_eq
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgsmooth : ContDiff ℝ (⊤ : ℕ∞) g) (hgcompact : HasCompactSupport g) :
    suzukiComplexTestL2 (suzukiMeanCorrectedInteriorTest a g)
        (contDiff_suzukiMeanCorrectedInteriorTest a g hgsmooth)
        (hasCompactSupport_suzukiMeanCorrectedInteriorTest a g hgcompact) =
      suzukiComplexTestL2 g hgsmooth hgcompact -
        (∫ x : ℝ, g x) •
          suzukiComplexTestL2 (suzukiInteriorMeanBump a)
            (contDiff_suzukiInteriorMeanBump a)
            (hasCompactSupport_suzukiInteriorMeanBump a) := by
  apply Lp.ext
  filter_upwards [suzukiComplexTestL2_coeFn
      (suzukiMeanCorrectedInteriorTest a g)
      (contDiff_suzukiMeanCorrectedInteriorTest a g hgsmooth)
      (hasCompactSupport_suzukiMeanCorrectedInteriorTest a g hgcompact),
    suzukiComplexTestL2_coeFn g hgsmooth hgcompact,
    suzukiComplexTestL2_coeFn (suzukiInteriorMeanBump a)
      (contDiff_suzukiInteriorMeanBump a)
      (hasCompactSupport_suzukiInteriorMeanBump a),
    Lp.coeFn_smul (∫ x : ℝ, g x)
      (suzukiComplexTestL2 (suzukiInteriorMeanBump a)
        (contDiff_suzukiInteriorMeanBump a)
        (hasCompactSupport_suzukiInteriorMeanBump a)),
    Lp.coeFn_sub (suzukiComplexTestL2 g hgsmooth hgcompact)
      ((∫ x : ℝ, g x) •
        suzukiComplexTestL2 (suzukiInteriorMeanBump a)
          (contDiff_suzukiInteriorMeanBump a)
          (hasCompactSupport_suzukiInteriorMeanBump a))]
      with x hcorr hg hrho hsmul hsub
  rw [hcorr, hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hg, hrho]
  rfl

theorem dist_suzukiComplexTestL2_meanCorrected
    (a : SuzukiPositiveAperture) (g : ℝ → ℂ)
    (hgsmooth : ContDiff ℝ (⊤ : ℕ∞) g) (hgcompact : HasCompactSupport g) :
    dist (suzukiComplexTestL2 g hgsmooth hgcompact)
        (suzukiComplexTestL2 (suzukiMeanCorrectedInteriorTest a g)
          (contDiff_suzukiMeanCorrectedInteriorTest a g hgsmooth)
          (hasCompactSupport_suzukiMeanCorrectedInteriorTest a g hgcompact)) =
      ‖∫ x : ℝ, g x‖ *
      ‖suzukiComplexTestL2 (suzukiInteriorMeanBump a)
          (contDiff_suzukiInteriorMeanBump a)
          (hasCompactSupport_suzukiInteriorMeanBump a)‖ := by
  rw [suzukiComplexTestL2_meanCorrected_eq a g hgsmooth hgcompact,
    dist_eq_norm]
  have hsub : suzukiComplexTestL2 g hgsmooth hgcompact -
      (suzukiComplexTestL2 g hgsmooth hgcompact -
        (∫ x : ℝ, g x) •
          suzukiComplexTestL2 (suzukiInteriorMeanBump a)
            (contDiff_suzukiInteriorMeanBump a)
            (hasCompactSupport_suzukiInteriorMeanBump a)) =
      (∫ x : ℝ, g x) •
        suzukiComplexTestL2 (suzukiInteriorMeanBump a)
          (contDiff_suzukiInteriorMeanBump a)
          (hasCompactSupport_suzukiInteriorMeanBump a) := by
    abel
  rw [hsub, norm_smul]

theorem suzukiApertureL2ToL1Bound_nonneg (a : ℝ) :
    0 ≤ suzukiApertureL2ToL1Bound a := by
  unfold suzukiApertureL2ToL1Bound
  exact ENNReal.toReal_nonneg

theorem norm_integral_interiorSmooth_le
    (a : SuzukiPositiveAperture) (f : SuzukiApertureZeroMean a)
    (g : ℝ → ℂ) (hgsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgcompact : HasCompactSupport g)
    (hginterior : tsupport g ⊆ Ioo (-a.1) a.1) :
    ‖∫ x : ℝ, g x‖ ≤ suzukiApertureL2ToL1Bound a.1 *
      dist (suzukiApertureZeroExtendL2
          (f : SuzukiApertureIntervalL2 a.1))
        (suzukiComplexTestL2 g hgsmooth hgcompact) := by
  let G : SuzukiApertureIntervalL2 a.1 :=
    suzukiApertureRestrictL2 a.1 (suzukiComplexTestL2 g hgsmooth hgcompact)
  have hfmean : suzukiApertureIntervalMean a
      (f : SuzukiApertureIntervalL2 a.1) = 0 :=
    (mem_suzukiApertureZeroMean_iff a _).mp f.2
  have hGmean := suzukiApertureIntervalMean_restrict_interiorSmooth
    a g hgsmooth hgcompact hginterior
  have hdiff : suzukiApertureIntervalMean a
      (G - (f : SuzukiApertureIntervalL2 a.1)) = ∫ x : ℝ, g x := by
    rw [← inner_suzukiApertureIntervalOne, inner_sub_right,
      inner_suzukiApertureIntervalOne, inner_suzukiApertureIntervalOne,
      hfmean, sub_zero]
    exact hGmean
  rw [← hdiff, suzukiApertureIntervalMean]
  calc
    ‖∫ x : SuzukiApertureInterval a.1,
        (G - (f : SuzukiApertureIntervalL2 a.1)) x ∂volume‖ ≤
        ∫ x : SuzukiApertureInterval a.1,
          ‖(G - (f : SuzukiApertureIntervalL2 a.1)) x‖ ∂volume :=
      norm_integral_le_integral_norm _
    _ ≤ suzukiApertureL2ToL1Bound a.1 *
        ‖G - (f : SuzukiApertureIntervalL2 a.1)‖ :=
      integral_norm_suzukiAperture_le a.1 _
    _ = suzukiApertureL2ToL1Bound a.1 *
        dist (suzukiApertureZeroExtendL2
            (f : SuzukiApertureIntervalL2 a.1))
          (suzukiComplexTestL2 g hgsmooth hgcompact) := by
      congr 1
      calc
        ‖G - (f : SuzukiApertureIntervalL2 a.1)‖ =
            dist G (f : SuzukiApertureIntervalL2 a.1) :=
          (dist_eq_norm _ _).symm
        _ = dist (f : SuzukiApertureIntervalL2 a.1) G := dist_comm _ _
        _ = _ := dist_restrict_interiorSmooth a
          (f : SuzukiApertureIntervalL2 a.1) g hgsmooth hgcompact hginterior

/-- Derivatives of strict-interior complex smooth sources are dense in Suzuki's exact zero-mean
aperture space. -/
theorem denseRange_ccmComplexSmoothInteriorSource_toDerivativeZeroMean
    (a : SuzukiPositiveAperture) :
    DenseRange (fun u : CCMComplexSmoothInteriorSource a =>
      u.toDerivativeZeroMean) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  let q : SoninL2 := suzukiApertureZeroExtendL2
    (f : SuzukiApertureIntervalL2 a.1)
  let ρ : SoninL2 := suzukiComplexTestL2 (suzukiInteriorMeanBump a)
    (contDiff_suzukiInteriorMeanBump a)
    (hasCompactSupport_suzukiInteriorMeanBump a)
  let C : ℝ := suzukiApertureL2ToL1Bound a.1
  let K : ℝ := C * ‖ρ‖
  have hC : 0 ≤ C := suzukiApertureL2ToL1Bound_nonneg a.1
  have hK : 0 ≤ K := mul_nonneg hC (norm_nonneg ρ)
  let δ : ℝ := ε / (2 * (1 + K))
  have hden : 0 < 2 * (1 + K) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hq : suzukiCutoff a.1 q = q :=
    suzukiApertureZeroExtendL2_cutoff (f : SuzukiApertureIntervalL2 a.1)
  obtain ⟨g, hgcompact, hgsmooth, r, hr0, hra, hgsupport, hgtsupport, hdist⟩ :=
    exists_suzukiInteriorCompactSmoothL2_dist_lt a hq hδ
  have hginterior : tsupport g ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    have hi := hgtsupport hx
    exact ⟨lt_of_lt_of_le (neg_lt_neg hra) hi.1,
      lt_of_le_of_lt hi.2 hra⟩
  let φ : ℝ → ℂ := suzukiMeanCorrectedInteriorTest a g
  let R : ℝ := max r (a.1 / 2)
  have hR0 : 0 ≤ R := suzukiMeanCorrectionRadius_nonneg a hr0
  have hRa : R < a.1 := suzukiMeanCorrectionRadius_lt a hra
  have hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ :=
    contDiff_suzukiMeanCorrectedInteriorTest a g hgsmooth
  have hφcompact : HasCompactSupport φ :=
    hasCompactSupport_suzukiMeanCorrectedInteriorTest a g hgcompact
  have hφsupport : Function.support φ ⊆ Ioo (-R) R :=
    support_suzukiMeanCorrectedInteriorTest_subset a g r hgsupport
  have hφtsupport : tsupport φ ⊆ Icc (-R) R :=
    tsupport_suzukiMeanCorrectedInteriorTest_subset a g r hgtsupport
  have hφinterior : tsupport φ ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    have hi := hφtsupport hx
    exact ⟨lt_of_lt_of_le (neg_lt_neg hRa) hi.1,
      lt_of_le_of_lt hi.2 hRa⟩
  have hφintegral : (∫ x : ℝ, φ x) = 0 :=
    integral_suzukiMeanCorrectedInteriorTest a g
      (hgsmooth.continuous.integrable_of_hasCompactSupport hgcompact)
  let u : CCMComplexSmoothInteriorSource a :=
    suzukiSmoothIntegralPrimitiveSource a R hRa φ hφsmooth hφsupport hφintegral
  refine ⟨u, ?_⟩
  have hderivative := suzukiSmoothIntegralPrimitiveSource_toDerivativeZeroMean
    a R hRa φ hφsmooth hφsupport hφintegral
  have hfirst : dist (f : SuzukiApertureIntervalL2 a.1)
      (suzukiApertureRestrictL2 a.1
        (suzukiComplexTestL2 g hgsmooth hgcompact)) =
      dist q (suzukiComplexTestL2 g hgsmooth hgcompact) :=
    dist_restrict_interiorSmooth a (f : SuzukiApertureIntervalL2 a.1)
      g hgsmooth hgcompact hginterior
  have hsecond : dist
      (suzukiApertureRestrictL2 a.1
        (suzukiComplexTestL2 g hgsmooth hgcompact))
      (suzukiApertureRestrictL2 a.1
        (suzukiComplexTestL2 φ hφsmooth hφcompact)) =
      dist (suzukiComplexTestL2 g hgsmooth hgcompact)
        (suzukiComplexTestL2 φ hφsmooth hφcompact) := by
    have h := dist_restrict_interiorSmooth a
      (suzukiApertureRestrictL2 a.1
        (suzukiComplexTestL2 g hgsmooth hgcompact))
      φ hφsmooth hφcompact hφinterior
    rw [suzukiApertureZeroExtendL2_restrict_interiorSmooth
      a g hgsmooth hgcompact hginterior] at h
    exact h
  have hcorr : dist (suzukiComplexTestL2 g hgsmooth hgcompact)
      (suzukiComplexTestL2 φ hφsmooth hφcompact) =
      ‖∫ x : ℝ, g x‖ * ‖ρ‖ := by
    exact dist_suzukiComplexTestL2_meanCorrected a g hgsmooth hgcompact
  have hmean := norm_integral_interiorSmooth_le
    a f g hgsmooth hgcompact hginterior
  have hcorrLe : dist (suzukiComplexTestL2 g hgsmooth hgcompact)
      (suzukiComplexTestL2 φ hφsmooth hφcompact) ≤
      K * dist q (suzukiComplexTestL2 g hgsmooth hgcompact) := by
    rw [hcorr]
    calc
      ‖∫ x : ℝ, g x‖ * ‖ρ‖ ≤
          (C * dist q (suzukiComplexTestL2 g hgsmooth hgcompact)) * ‖ρ‖ :=
        mul_le_mul_of_nonneg_right hmean (norm_nonneg ρ)
      _ = K * dist q (suzukiComplexTestL2 g hgsmooth hgcompact) := by
        ring
  have htotal : dist (f : SuzukiApertureIntervalL2 a.1)
      (suzukiApertureRestrictL2 a.1
        (suzukiComplexTestL2 φ hφsmooth hφcompact)) < ε := by
    calc
      dist (f : SuzukiApertureIntervalL2 a.1)
          (suzukiApertureRestrictL2 a.1
            (suzukiComplexTestL2 φ hφsmooth hφcompact)) ≤
          dist (f : SuzukiApertureIntervalL2 a.1)
              (suzukiApertureRestrictL2 a.1
                (suzukiComplexTestL2 g hgsmooth hgcompact)) +
            dist (suzukiApertureRestrictL2 a.1
                (suzukiComplexTestL2 g hgsmooth hgcompact))
              (suzukiApertureRestrictL2 a.1
                (suzukiComplexTestL2 φ hφsmooth hφcompact)) :=
        dist_triangle _ _ _
      _ = dist q (suzukiComplexTestL2 g hgsmooth hgcompact) +
          dist (suzukiComplexTestL2 g hgsmooth hgcompact)
            (suzukiComplexTestL2 φ hφsmooth hφcompact) := by
        rw [hfirst, hsecond]
      _ ≤ (1 + K) * dist q
          (suzukiComplexTestL2 g hgsmooth hgcompact) := by
        calc
          _ ≤ dist q (suzukiComplexTestL2 g hgsmooth hgcompact) +
              K * dist q (suzukiComplexTestL2 g hgsmooth hgcompact) :=
            add_le_add_right hcorrLe _
          _ = _ := by ring
      _ < (1 + K) * δ :=
        mul_lt_mul_of_pos_left hdist (by positivity)
      _ = ε / 2 := by
        dsimp [δ]
        field_simp
      _ < ε := by linarith
  change dist (f : SuzukiApertureIntervalL2 a.1)
    (u.toDerivativeZeroMean : SuzukiApertureIntervalL2 a.1) < ε
  rw [hderivative]
  exact htotal

theorem suzukiWeilIntervalFormEmbedding_complexSmooth
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    suzukiWeilIntervalFormEmbedding a u.toCCMFormVector =
      suzukiApertureRestrictL2 a.1
        (suzukiComplexTestL2 u u.smooth u.hasCompactSupport) := by
  apply (suzukiApertureL2Equiv a).injective
  change (suzukiApertureL2Equiv a)
      ((suzukiApertureL2Equiv a).symm
        (ccmArchimedeanFormToAperture a u.toCCMFormVector)) =
    (suzukiApertureL2Equiv a)
      (suzukiApertureRestrictL2 a.1
        (suzukiComplexTestL2 u u.smooth u.hasCompactSupport))
  rw [(suzukiApertureL2Equiv a).apply_symm_apply]
  apply Subtype.ext
  change (ccmArchimedeanFormToAperture a u.toCCMFormVector).1 =
    suzukiApertureZeroExtendL2
      (suzukiApertureRestrictL2 a.1
        (suzukiComplexTestL2 u u.smooth u.hasCompactSupport))
  rw [suzukiApertureZeroExtendL2_restrict_interiorSmooth
    a u u.smooth u.hasCompactSupport u.tsupport_subset]
  apply Lp.ext
  exact u.toCCMFormVector_physical_coeFn.trans
    (suzukiComplexTestL2_coeFn u u.smooth u.hasCompactSupport).symm

theorem CCMComplexSmoothInteriorSource.toCCMFormVector_eq_primitive
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    u.toCCMFormVector =
      suzukiAperturePrimitiveCCMFormVector a
        (u.toDerivativeZeroMean : SuzukiApertureIntervalL2 a.1) := by
  apply suzukiWeilIntervalFormEmbedding_injective a
  rw [suzukiWeilIntervalFormEmbedding_complexSmooth,
    suzukiWeilIntervalFormEmbedding_primitiveCCMFormVector]
  change suzukiApertureRestrictL2 a.1
      (suzukiComplexTestL2 u u.smooth u.hasCompactSupport) =
    suzukiAperturePrimitive a.1
      (suzukiSmoothDerivativeCoordinate a u u.smooth u.hasCompactSupport)
  exact (suzukiAperturePrimitive_smoothDerivativeCoordinate
    a u u.smooth u.hasCompactSupport u.tsupport_subset).symm

/-- Pullback Weil operator compressed to Suzuki's zero-mean derivative space. -/
def suzukiPrimitiveWeilZeroMeanOperator (a : SuzukiPositiveAperture) :
    SuzukiApertureZeroMean a →L[ℂ] SuzukiApertureZeroMean a :=
  suzukiApertureZeroMeanProjection a ∘L
    suzukiPrimitiveWeilSourceOperator a ∘L
      (SuzukiApertureZeroMean a).subtypeL

theorem inner_suzukiPrimitiveWeilZeroMeanOperator
    (a : SuzukiPositiveAperture) (f g : SuzukiApertureZeroMean a) :
    inner ℂ f (suzukiPrimitiveWeilZeroMeanOperator a g) =
      inner ℂ (f : SuzukiApertureIntervalL2 a.1)
        (suzukiPrimitiveWeilSourceOperator a
          (g : SuzukiApertureIntervalL2 a.1)) := by
  change inner ℂ f
      ((SuzukiApertureZeroMean a).orthogonalProjectionOnto
        (suzukiPrimitiveWeilSourceOperator a
          (g : SuzukiApertureIntervalL2 a.1))) = _
  exact (SuzukiApertureZeroMean a).inner_orthogonalProjectionOnto_eq_of_mem_left
    f (suzukiPrimitiveWeilSourceOperator a
      (g : SuzukiApertureIntervalL2 a.1))

theorem inner_suzukiPrimitiveWeilSourceOperator_eq_screw_complexSmooth
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) :
    inner ℂ u.toDerivativeZeroMean
        (suzukiPrimitiveWeilZeroMeanOperator a v.toDerivativeZeroMean) =
      inner ℂ u.toDerivativeZeroMean
        (suzukiScrewZeroMeanOperator a v.toDerivativeZeroMean) := by
  rw [inner_suzukiPrimitiveWeilZeroMeanOperator,
    inner_suzukiPrimitiveWeilSourceOperator,
    suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm,
    ← u.toCCMFormVector_eq_primitive,
    ← v.toCCMFormVector_eq_primitive,
    ccmRestrictedWeilForm_complexSmooth_eq_screwOperator]

/-- Exact operator equality extending Suzuki's smooth Weil identity to every zero-mean `L²`
derivative coordinate. -/
theorem suzukiPrimitiveWeilZeroMeanOperator_eq_screw
    (a : SuzukiPositiveAperture) :
    suzukiPrimitiveWeilZeroMeanOperator a = suzukiScrewZeroMeanOperator a := by
  let D : Set (SuzukiApertureZeroMean a) :=
    Set.range (fun u : CCMComplexSmoothInteriorSource a => u.toDerivativeZeroMean)
  have hD : Dense D :=
    denseRange_ccmComplexSmoothInteriorSource_toDerivativeZeroMean a
  have heq : Set.EqOn (suzukiPrimitiveWeilZeroMeanOperator a)
      (suzukiScrewZeroMeanOperator a) D := by
    intro x hx
    obtain ⟨v, rfl⟩ := hx
    apply sub_eq_zero.mp
    apply hD.eq_zero_of_inner_right ℂ
    intro y hy
    obtain ⟨u, rfl⟩ := hy
    rw [inner_sub_right,
      inner_suzukiPrimitiveWeilSourceOperator_eq_screw_complexSmooth]
    exact sub_self _
  apply ContinuousLinearMap.ext
  intro x
  have hfun := Continuous.ext_on hD
    (suzukiPrimitiveWeilZeroMeanOperator a).continuous
    (suzukiScrewZeroMeanOperator a).continuous heq
  exact congrFun hfun x

/-- Suzuki's mixed Lemma 3.1 identity on the full zero-mean derivative space. -/
theorem ccmRestrictedWeilForm_primitive_eq_screw
    (a : SuzukiPositiveAperture) (f g : SuzukiApertureZeroMean a) :
    ccmRestrictedWeilForm a
        (suzukiAperturePrimitiveCCMFormVector a
          (f : SuzukiApertureIntervalL2 a.1))
        (suzukiAperturePrimitiveCCMFormVector a
          (g : SuzukiApertureIntervalL2 a.1)) =
      inner ℂ f (suzukiScrewZeroMeanOperator a g) := by
  calc
    ccmRestrictedWeilForm a
        (suzukiAperturePrimitiveCCMFormVector a
          (f : SuzukiApertureIntervalL2 a.1))
        (suzukiAperturePrimitiveCCMFormVector a
          (g : SuzukiApertureIntervalL2 a.1)) =
        suzukiWeilIntervalForm a
          (suzukiAperturePrimitiveCCMFormVector a
            (f : SuzukiApertureIntervalL2 a.1))
          (suzukiAperturePrimitiveCCMFormVector a
            (g : SuzukiApertureIntervalL2 a.1)) :=
      (suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm a _ _).symm
    _ = inner ℂ (f : SuzukiApertureIntervalL2 a.1)
          (suzukiPrimitiveWeilSourceOperator a
            (g : SuzukiApertureIntervalL2 a.1)) :=
      (inner_suzukiPrimitiveWeilSourceOperator a _ _).symm
    _ = inner ℂ f (suzukiPrimitiveWeilZeroMeanOperator a g) :=
      (inner_suzukiPrimitiveWeilZeroMeanOperator a f g).symm
    _ = inner ℂ f (suzukiScrewZeroMeanOperator a g) := by
      rw [suzukiPrimitiveWeilZeroMeanOperator_eq_screw]

/-- The self-adjoint restricted Weil realization is formally self-adjoint on its operator
domain. -/
theorem suzukiWeilFriedrichsOperator_isFormalAdjoint
    (a : SuzukiPositiveAperture) :
    (suzukiWeilFriedrichsOperator a).IsFormalAdjoint
      (suzukiWeilFriedrichsOperator a) := by
  have hself := suzukiWeilFriedrichsOperator_isSelfAdjoint a
  have hle : suzukiWeilFriedrichsOperator a ≤
      (suzukiWeilFriedrichsOperator a).adjoint := le_of_eq hself.symm
  intro x y
  let xAdj : (suzukiWeilFriedrichsOperator a).adjoint.domain :=
    ⟨(x : SuzukiApertureIntervalL2 a.1), hle.1 x.property⟩
  have hxApply : suzukiWeilFriedrichsOperator a x =
      (suzukiWeilFriedrichsOperator a).adjoint xAdj := hle.2 rfl
  rw [hxApply]
  exact LinearPMap.adjoint_isFormalAdjoint hself.dense_domain xAdj y

/-- Pairing a Dirichlet primitive against the Weil representative recovers the exact
restricted Weil form. -/
theorem inner_suzukiDirichletInverse_primitiveWeilRepresentative
    (a : SuzukiPositiveAperture) (f g : SuzukiApertureZeroMean a) :
    inner ℂ (suzukiDirichletInverseCLM a f)
        (suzukiAperturePrimitiveWeilRepresentative a
          (g : SuzukiApertureIntervalL2 a.1)) =
      ccmRestrictedWeilForm a
        (suzukiAperturePrimitiveCCMFormVector a
          (f : SuzukiApertureIntervalL2 a.1))
        (suzukiAperturePrimitiveCCMFormVector a
          (g : SuzukiApertureIntervalL2 a.1)) := by
  let xf : (suzukiWeilFriedrichsOperator a).domain :=
    ⟨suzukiAperturePrimitive a.1
        (f : SuzukiApertureIntervalL2 a.1),
      suzukiWeilFriedrichsOperator_primitive_mem_domain a
        (f : SuzukiApertureIntervalL2 a.1)⟩
  let xg : (suzukiWeilFriedrichsOperator a).domain :=
    ⟨suzukiAperturePrimitive a.1
        (g : SuzukiApertureIntervalL2 a.1),
      suzukiWeilFriedrichsOperator_primitive_mem_domain a
        (g : SuzukiApertureIntervalL2 a.1)⟩
  have hsym := suzukiWeilFriedrichsOperator_isFormalAdjoint a xf xg
  have hrep := suzukiAperturePrimitiveWeilRepresentative_represents_form
    a (f : SuzukiApertureIntervalL2 a.1)
      (suzukiAperturePrimitiveCCMFormVector a
        (g : SuzukiApertureIntervalL2 a.1))
  change inner ℂ (suzukiAperturePrimitive a.1
      (f : SuzukiApertureIntervalL2 a.1))
      (suzukiAperturePrimitiveWeilRepresentative a
        (g : SuzukiApertureIntervalL2 a.1)) = _
  calc
    inner ℂ (suzukiAperturePrimitive a.1
        (f : SuzukiApertureIntervalL2 a.1))
        (suzukiAperturePrimitiveWeilRepresentative a
          (g : SuzukiApertureIntervalL2 a.1)) =
        inner ℂ (suzukiAperturePrimitiveWeilRepresentative a
          (f : SuzukiApertureIntervalL2 a.1))
          (suzukiAperturePrimitive a.1
            (g : SuzukiApertureIntervalL2 a.1)) := by
      rw [← suzukiWeilFriedrichsOperator_primitive_apply a
        (f : SuzukiApertureIntervalL2 a.1),
        ← suzukiWeilFriedrichsOperator_primitive_apply a
          (g : SuzukiApertureIntervalL2 a.1)]
      exact hsym.symm
    _ = suzukiWeilIntervalForm a
        (suzukiAperturePrimitiveCCMFormVector a
          (f : SuzukiApertureIntervalL2 a.1))
        (suzukiAperturePrimitiveCCMFormVector a
          (g : SuzukiApertureIntervalL2 a.1)) := by
      rw [suzukiWeilIntervalForm]
      simpa only [suzukiWeilIntervalFormEmbedding_primitiveCCMFormVector] using hrep.symm
    _ = ccmRestrictedWeilForm a
        (suzukiAperturePrimitiveCCMFormVector a
          (f : SuzukiApertureIntervalL2 a.1))
        (suzukiAperturePrimitiveCCMFormVector a
          (g : SuzukiApertureIntervalL2 a.1)) :=
      suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm a _ _

/-- The maximal-adjoint screw witness is exactly the Friedrichs Weil representative on every
zero-mean derivative coordinate. -/
theorem suzukiRawScrewAdjointWitness_eq_primitiveWeilRepresentative
    (a : SuzukiPositiveAperture) (g : SuzukiApertureZeroMean a) :
    suzukiRawScrewAdjointWitness a
        (g : SuzukiApertureIntervalL2 a.1) =
      suzukiAperturePrimitiveWeilRepresentative a
        (g : SuzukiApertureIntervalL2 a.1) := by
  apply sub_eq_zero.mp
  apply (dense_suzukiDirichletInverseCLM_range a).eq_zero_of_inner_right ℂ
  intro x hx
  obtain ⟨f, rfl⟩ := hx
  rw [inner_sub_right]
  change inner ℂ (suzukiDirichletInverseCLM a f)
      (suzukiRawScrewAdjointWitness a
        (g : SuzukiApertureIntervalL2 a.1)) -
      inner ℂ (suzukiDirichletInverseCLM a f)
        (suzukiAperturePrimitiveWeilRepresentative a
          (g : SuzukiApertureIntervalL2 a.1)) = 0
  rw [inner_suzukiDirichletInverse_rawScrewAdjointWitness,
    inner_suzukiDirichletInverse_primitiveWeilRepresentative,
    ccmRestrictedWeilForm_primitive_eq_screw]
  exact sub_self _

/-- Suzuki's literal natural operator `B_a = D† G_a D` is a graph restriction of the
restricted-Weil Friedrichs operator `A_a`. -/
theorem suzukiDirichletScrewOperator_le_weilFriedrichsOperator
    (a : SuzukiPositiveAperture) :
    suzukiDirichletScrewOperator a ≤ suzukiWeilFriedrichsOperator a := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxnat : x ∈ suzukiDirichletScrewNaturalDomain a := by
      simpa only [suzukiDirichletScrewOperator_domain] using hx
    have hxD : x ∈ (suzukiDirichletDerivative a).domain := by
      rw [← suzukiDirichletScrewNaturalDomain_eq_H01 a]
      exact hxnat
    let xd : (suzukiDirichletDerivative a).domain :=
      ⟨x, hxD⟩
    exact suzukiWeilFriedrichsOperator_dirichletDomain_mem a xd
  · intro x y hxy
    have hxnat : (x : SuzukiApertureIntervalL2 a.1) ∈
        suzukiDirichletScrewNaturalDomain a := by
      simpa only [suzukiDirichletScrewOperator_domain] using x.property
    have hxD : (x : SuzukiApertureIntervalL2 a.1) ∈
        (suzukiDirichletDerivative a).domain := by
      rw [← suzukiDirichletScrewNaturalDomain_eq_H01 a]
      exact hxnat
    let xd : (suzukiDirichletDerivative a).domain :=
      ⟨(x : SuzukiApertureIntervalL2 a.1), hxD⟩
    let g : SuzukiApertureZeroMean a :=
      (suzukiDirichletInverseRangeEquiv a).symm
        (suzukiDirichletDomainToH01 a xd)
    have hg : (g : SuzukiApertureIntervalL2 a.1) =
        suzukiDirichletDomainDerivativeCoordinate a xd := rfl
    have hxmem : (x : SuzukiApertureIntervalL2 a.1) ∈
        (suzukiWeilFriedrichsOperator a).domain :=
      suzukiWeilFriedrichsOperator_dirichletDomain_mem a xd
    have hy : y =
        (⟨(x : SuzukiApertureIntervalL2 a.1), hxmem⟩ :
          (suzukiWeilFriedrichsOperator a).domain) :=
      Subtype.ext hxy.symm
    rw [hy, suzukiDirichletScrewOperator_apply_eq_adjointWitness]
    change suzukiRawScrewAdjointWitness a
        (suzukiDirichletDomainDerivativeCoordinate a xd) =
      suzukiWeilFriedrichsOperator a ⟨(x : SuzukiApertureIntervalL2 a.1), hxmem⟩
    have heqA :
        (⟨(x : SuzukiApertureIntervalL2 a.1), hxmem⟩ :
          (suzukiWeilFriedrichsOperator a).domain) =
        ⟨xd.1, suzukiWeilFriedrichsOperator_dirichletDomain_mem a xd⟩ :=
      Subtype.ext rfl
    rw [heqA, suzukiWeilFriedrichsOperator_dirichletDomain_apply,
      ← hg, suzukiRawScrewAdjointWitness_eq_primitiveWeilRepresentative]
    rfl

/-- Exact mean of the constant derivative coordinate on Suzuki's aperture. -/
theorem suzukiApertureIntervalMean_one
    (a : SuzukiPositiveAperture) :
    suzukiApertureIntervalMean a (suzukiApertureIntervalOne a) =
      (2 * a.1 : ℂ) := by
  rw [suzukiApertureIntervalMean]
  calc
    (∫ x : SuzukiApertureInterval a.1,
        (suzukiApertureIntervalOne a) x ∂volume) =
        ∫ _x : SuzukiApertureInterval a.1, (1 : ℂ) ∂volume := by
      apply integral_congr_ae
      exact suzukiApertureIntervalOne_coeFn a
    _ = (2 * a.1 : ℂ) := by
      rw [integral_const]
      simp only [Measure.real]
      rw [volume_suzukiApertureInterval_univ a]
      have hnonneg : 0 ≤ 2 * a.1 := by linarith [a.2]
      rw [ENNReal.toReal_ofReal hnonneg]
      norm_num

theorem suzukiApertureIntervalMean_one_ne_zero
    (a : SuzukiPositiveAperture) :
    suzukiApertureIntervalMean a (suzukiApertureIntervalOne a) ≠ 0 := by
  rw [suzukiApertureIntervalMean_one]
  exact mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
    (Complex.ofReal_ne_zero.mpr a.2.ne')

/-- A primitive with nonzero endpoint jump belongs to `D(A_a)` but not to Suzuki's Dirichlet
domain. -/
theorem suzukiAperturePrimitive_one_not_mem_dirichletDomain
    (a : SuzukiPositiveAperture) :
    suzukiAperturePrimitive a.1 (suzukiApertureIntervalOne a) ∉
      (suzukiDirichletDerivative a).domain := by
  rw [suzukiDirichletDerivative_domain]
  intro hmem
  obtain ⟨g, hg⟩ := hmem
  have hcoordinate : (g : SuzukiApertureIntervalL2 a.1) =
      suzukiApertureIntervalOne a := by
    apply suzukiAperturePrimitiveCLM_injective a
    exact hg
  have hzero : suzukiApertureIntervalMean a
      (g : SuzukiApertureIntervalL2 a.1) = 0 :=
    (mem_suzukiApertureZeroMean_iff a _).mp g.property
  have hmean := congrArg (suzukiApertureIntervalMean a) hcoordinate
  rw [hzero] at hmean
  exact suzukiApertureIntervalMean_one_ne_zero a hmean.symm

/-- Paper's strict-domain assertion: `D(B_a)=H₀¹(-a,a)` is properly contained in
`D(A_a)`. -/
theorem suzukiDirichletScrewOperator_domain_lt_weilFriedrichsOperator_domain
    (a : SuzukiPositiveAperture) :
    (suzukiDirichletScrewOperator a).domain <
      (suzukiWeilFriedrichsOperator a).domain := by
  apply lt_of_le_of_ne
  · exact (suzukiDirichletScrewOperator_le_weilFriedrichsOperator a).1
  · intro heq
    have hA : suzukiAperturePrimitive a.1 (suzukiApertureIntervalOne a) ∈
        (suzukiWeilFriedrichsOperator a).domain :=
      suzukiWeilFriedrichsOperator_primitive_mem_domain a
        (suzukiApertureIntervalOne a)
    have hB : suzukiAperturePrimitive a.1 (suzukiApertureIntervalOne a) ∈
        (suzukiDirichletScrewOperator a).domain := by
      rw [heq]
      exact hA
    apply suzukiAperturePrimitive_one_not_mem_dirichletDomain a
    rw [← suzukiDirichletScrewNaturalDomain_eq_H01 a,
      ← suzukiDirichletScrewOperator_domain a]
    exact hB

/-- Suzuki's symmetric natural operator `B_a` genuinely fails to be self-adjoint. -/
theorem suzukiDirichletScrewOperator_not_isSelfAdjoint
    (a : SuzukiPositiveAperture) :
    ¬ IsSelfAdjoint (suzukiDirichletScrewOperator a) := by
  intro hBself
  have hBA := suzukiDirichletScrewOperator_le_weilFriedrichsOperator a
  have hformal : (suzukiDirichletScrewOperator a).IsFormalAdjoint
      (suzukiWeilFriedrichsOperator a) := by
    intro x y
    let xa : (suzukiWeilFriedrichsOperator a).domain :=
      ⟨(x : SuzukiApertureIntervalL2 a.1), hBA.1 x.property⟩
    have hxApply : suzukiDirichletScrewOperator a x =
        suzukiWeilFriedrichsOperator a xa := hBA.2 rfl
    rw [hxApply]
    exact suzukiWeilFriedrichsOperator_isFormalAdjoint a xa y
  have hABadj : suzukiWeilFriedrichsOperator a ≤
      (suzukiDirichletScrewOperator a).adjoint :=
    hformal.le_adjoint hBself.dense_domain
  rw [LinearPMap.isSelfAdjoint_def] at hBself
  rw [hBself] at hABadj
  have heq : suzukiDirichletScrewOperator a =
      suzukiWeilFriedrichsOperator a := le_antisymm hBA hABadj
  have hdomains := congrArg LinearPMap.domain heq
  exact (suzukiDirichletScrewOperator_domain_lt_weilFriedrichsOperator_domain a).ne
    hdomains

end RHTower

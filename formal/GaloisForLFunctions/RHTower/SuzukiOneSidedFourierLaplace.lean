import GaloisForLFunctions.RHTower.SoninLogShellCocycle
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# One-sided Fourier--Laplace evaluation on Suzuki's logarithmic carrier

Suzuki's proof of Lemma 4.3 uses complex Fourier transforms of arbitrary `L²` functions supported
on a half-line.  Such transforms are not ordinary `L¹` Fourier integrals on the boundary, but every
strict upper-half-plane value is a bounded Hilbert-space evaluation.  This module constructs those
evaluations on the exact logarithmic carrier.

For `Im z > 0`, the upper-supported evaluation is

`q ↦ ∫_{t ≤ A} exp(-I z t) q(t) dt`,

and the lower-supported evaluation is

`q ↦ ∫_{t ≥ B} exp(I z t) q(t) dt`.

The exponential test vectors are proved to lie in `L²`; no pointwise decay of the source is
assumed.  The module also proves density, inside the sharp upper-support subspace, of compactly
supported smooth sources with the same one-sided support.  That is the support-preserving density
step needed to pass Suzuki's literal-kernel formula from `C_c^∞` to arbitrary `L²(0,a)` data.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

/-! ## Sharp and smooth one-sided cutoffs -/

/-- Cutoff onto a right logarithmic half-line. -/
def logLowerHalflineCutoff (b : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (Ici b) measurableSet_Ici

/-- Smooth cutoff which is zero on `[A,∞)` and tends pointwise to `1_{(-∞,A)}` as `n → ∞`. -/
def suzukiUpperSmoothCutoff (A : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  Real.smoothTransition ((A - t) * (n + 1))

theorem measurable_suzukiUpperSmoothCutoff (A : ℝ) (n : ℕ) :
    Measurable (suzukiUpperSmoothCutoff A n) := by
  exact (Complex.continuous_ofReal.comp
    (Real.smoothTransition.continuous.comp
      ((continuous_const.sub continuous_id).mul continuous_const))).measurable

theorem norm_suzukiUpperSmoothCutoff_le_one (A : ℝ) (n : ℕ) (t : ℝ) :
    ‖suzukiUpperSmoothCutoff A n t‖ ≤ 1 := by
  rw [suzukiUpperSmoothCutoff, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem contDiff_suzukiUpperSmoothCutoff (A : ℝ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiUpperSmoothCutoff A n) := by
  show ContDiff ℝ (⊤ : ℕ∞)
    fun t : ℝ => ((Real.smoothTransition ((A - t) * (n + 1)) : ℝ) : ℂ)
  exact Complex.ofRealCLM.contDiff.comp
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem suzukiUpperSmoothCutoff_eq_zero_of_le
    (A : ℝ) (n : ℕ) {t : ℝ} (hA : A ≤ t) :
    suzukiUpperSmoothCutoff A n t = 0 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hz : Real.smoothTransition ((A - t) * (n + 1)) = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hA) hn)
  show ((Real.smoothTransition ((A - t) * (n + 1)) : ℝ) : ℂ) = 0
  rw [hz, Complex.ofReal_zero]

theorem tendsto_suzukiUpperSmoothCutoff (A t : ℝ) :
    Tendsto (fun n : ℕ => suzukiUpperSmoothCutoff A n t) atTop
      (nhds ((Iio A).indicator (fun _ => (1 : ℂ)) t)) := by
  by_cases ht : t < A
  · rw [Set.indicator_of_mem (show t ∈ Iio A from ht)]
    have hpos : 0 < A - t := sub_pos.mpr ht
    have hevent : ∀ᶠ n : ℕ in atTop, 1 ≤ (A - t) * (n + 1) := by
      obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (1 / (A - t))
      filter_upwards [eventually_ge_atTop N] with n hn
      have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hn1 : (1 : ℝ) / (A - t) < n + 1 := by linarith
      rw [div_lt_iff₀ hpos] at hn1
      linarith
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [hevent] with n hn
    rw [suzukiUpperSmoothCutoff, Real.smoothTransition.one_of_one_le hn,
      Complex.ofReal_one]
  · rw [Set.indicator_of_notMem (show t ∉ Iio A from ht)]
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [] with n
    exact suzukiUpperSmoothCutoff_eq_zero_of_le A n (le_of_not_gt ht)

/-- Smooth upper cutoffs converge strongly to the sharp open-half-line cutoff. -/
theorem tendsto_suzukiUpperSmoothCutoff_mul
    (A : ℝ) (q : SoninL2) :
    Tendsto
      (fun n => lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
        (measurable_suzukiUpperSmoothCutoff A n) (C := 1) (by norm_num)
        (norm_suzukiUpperSmoothCutoff_le_one A n) q)
      atTop
      (nhds (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
        (measurable_const.indicator measurableSet_Iio) (C := 1) (by norm_num)
        (fun t => by
          by_cases ht : t ∈ Iio A
          · rw [Set.indicator_of_mem ht, norm_one]
          · rw [Set.indicator_of_notMem ht, norm_zero]
            norm_num) q)) := by
  exact tendsto_lpBoundedMulCLM_apply
    (fun n => measurable_suzukiUpperSmoothCutoff A n)
    (measurable_const.indicator measurableSet_Iio)
    (by norm_num) (fun n => norm_suzukiUpperSmoothCutoff_le_one A n)
    (fun t => by
          by_cases ht : t ∈ Iio A
          · rw [Set.indicator_of_mem ht, norm_one]
          · rw [Set.indicator_of_notMem ht, norm_zero]
            norm_num)
    (tendsto_suzukiUpperSmoothCutoff A) q

/-- The open and closed upper-half-line multipliers agree in `L²`. -/
theorem suzukiOpenUpperCutoff_eq_logHalflineCutoff (A : ℝ) :
    lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
        (measurable_const.indicator measurableSet_Iio) (C := 1) (by norm_num)
        (fun t => by
          by_cases ht : t ∈ Iio A
          · rw [Set.indicator_of_mem ht, norm_one]
          · rw [Set.indicator_of_notMem ht, norm_zero]
            norm_num) =
      logHalflineCutoff A := by
  apply ContinuousLinearMap.ext
  intro q
  apply Lp.ext
  filter_upwards [
    lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
      (measurable_const.indicator measurableSet_Iio) (C := 1) (by norm_num)
      (fun t => by
          by_cases ht : t ∈ Iio A
          · rw [Set.indicator_of_mem ht, norm_one]
          · rw [Set.indicator_of_notMem ht, norm_zero]
            norm_num) q,
    indicatorCutoff_ae (Iic A) measurableSet_Iic q,
    compl_mem_ae_iff.mpr (show (volume : Measure ℝ) {A} = 0 by simp)
  ] with t hopen hclosed ht
  rw [hopen]
  change (Iio A).indicator (fun _ => (1 : ℂ)) t * q t = logHalflineCutoff A q t
  rw [show logHalflineCutoff A q t = (Iic A).indicator (fun y => q y) t by
    simpa [logHalflineCutoff] using hclosed]
  have hne : t ≠ A := by simpa [Set.mem_singleton_iff] using ht
  by_cases hlt : t < A
  · have hle : t ≤ A := hlt.le
    simp [hlt, hle]
  · have hnle : ¬t ≤ A := fun hle => hne (le_antisymm hle (le_of_not_gt hlt))
    simp [hlt, hnle]

/-! ## Support-preserving compact-smooth density -/

/-- `L²` class of a compactly supported smooth function, without imposing any Suzuki-specific
decay data.  Compact support supplies every exponential decay condition when the function is later
inserted into the literal Hankel core. -/
def suzukiOneSidedCompactSmoothL2
    (g : ℝ → ℂ) (hcompact : HasCompactSupport g)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g) : SoninL2 :=
  (hsmooth.continuous.memLp_of_hasCompactSupport hcompact).toLp g

theorem suzukiOneSidedCompactSmoothL2_ae
    (g : ℝ → ℂ) (hcompact : HasCompactSupport g)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g) :
    (suzukiOneSidedCompactSmoothL2 g hcompact hsmooth : ℝ → ℂ) =ᵐ[volume] g :=
  (hsmooth.continuous.memLp_of_hasCompactSupport hcompact).coeFn_toLp

/-- Smooth compactly supported functions which vanish on `[A,∞)` are dense in the exact fixed
space of the sharp upper-half-line projection.  This is the source-faithful density theorem needed
to extend Suzuki's literal `C_c∞` Hankel formula to every `L²(0,a)` source. -/
theorem exists_suzukiOneSidedCompactSmoothL2_dist_lt
    {A : ℝ} {q : SoninL2} (hq : logHalflineCutoff A q = q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : ℝ → ℂ) (hcompact : HasCompactSupport g)
        (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g),
      (∀ t, A ≤ t → g t = 0) ∧
        dist q (suzukiOneSidedCompactSmoothL2 g hcompact hsmooth) < ε := by
  let T : ℕ → SoninL2 →L[ℂ] SoninL2 := fun n =>
    lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
      (measurable_suzukiUpperSmoothCutoff A n) (C := 1) (by norm_num)
      (norm_suzukiUpperSmoothCutoff_le_one A n)
  have hTq : Tendsto (fun n => T n q) atTop (nhds q) := by
    have hconv := tendsto_suzukiUpperSmoothCutoff_mul A q
    rw [suzukiOpenUpperCutoff_eq_logHalflineCutoff A, hq] at hconv
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
  let g' : ℝ → ℂ := fun t => suzukiUpperSmoothCutoff A n t * g t
  have hg'smooth : ContDiff ℝ (⊤ : ℕ∞) g' :=
    (contDiff_suzukiUpperSmoothCutoff A n).mul hgsmooth
  have hg'compact : HasCompactSupport g' := by
    change HasCompactSupport (suzukiUpperSmoothCutoff A n * g)
    exact hgcompact.mul_left
  have hg'zero : ∀ t, A ≤ t → g' t = 0 := by
    intro t ht
    change suzukiUpperSmoothCutoff A n t * g t = 0
    rw [suzukiUpperSmoothCutoff_eq_zero_of_le A n ht, zero_mul]
  have hTv : T n v = suzukiOneSidedCompactSmoothL2 g' hg'compact hg'smooth := by
    apply Lp.ext
    filter_upwards [
      lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
        (measurable_suzukiUpperSmoothCutoff A n) (C := 1) (by norm_num)
        (norm_suzukiUpperSmoothCutoff_le_one A n) v,
      hvg,
      suzukiOneSidedCompactSmoothL2_ae g' hg'compact hg'smooth
    ] with t hmul hbase hout
    change T n v t = suzukiOneSidedCompactSmoothL2 g' hg'compact hg'smooth t
    rw [hmul, hbase, hout]
  refine ⟨g', hg'compact, hg'smooth, hg'zero, ?_⟩
  rw [← hTv]
  have hnormT : ‖T n‖ ≤ 1 :=
    norm_lpBoundedMulCLM_le (measurable_suzukiUpperSmoothCutoff A n)
      (by norm_num) (norm_suzukiUpperSmoothCutoff_le_one A n)
  have hmap : dist (T n q) (T n v) ≤ dist q v := by
    calc
      dist (T n q) (T n v) ≤ ‖T n‖ * dist q v := (T n).dist_le_opNorm q v
      _ ≤ 1 * dist q v :=
        mul_le_mul_of_nonneg_right hnormT (dist_nonneg.trans_eq rfl)
      _ = dist q v := one_mul _
  calc
    dist q (T n v) ≤ dist q (T n q) + dist (T n q) (T n v) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hn (hmap.trans_lt hv)
    _ = ε := by ring

/-! ## Upper-supported bounded Fourier--Laplace evaluation -/

/-- Raw Hilbert feature for `∫_{t≤A} exp(-I z t) q(t) dt`. -/
def suzukiUpperFourierLaplaceFeatureRaw (A : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (Iic A).indicator (fun t : ℝ => Complex.exp (I * star z * (t : ℂ))) t

theorem suzukiUpperFourierLaplaceFeatureRaw_memLp
    (A : ℝ) {z : ℂ} (hz : 0 < z.im) :
    MemLp (suzukiUpperFourierLaplaceFeatureRaw A z) 2 volume := by
  have hmeas : AEStronglyMeasurable (suzukiUpperFourierLaplaceFeatureRaw A z) volume :=
    ((by fun_prop : Continuous fun t : ℝ => Complex.exp (I * star z * (t : ℂ)))
      |>.aestronglyMeasurable.indicator measurableSet_Iic)
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have heq : (fun t : ℝ => ‖suzukiUpperFourierLaplaceFeatureRaw A z t‖ ^ 2) =
      (Iic A).indicator (fun t : ℝ => Real.exp ((2 * z.im) * t)) := by
    funext t
    by_cases ht : t ∈ Iic A
    · rw [suzukiUpperFourierLaplaceFeatureRaw, indicator_of_mem ht,
        indicator_of_mem ht, Complex.norm_exp, ← Real.exp_nat_mul]
      congr 1
      simp only [mul_re, I_re, RCLike.star_def, Complex.conj_re, I_im,
        Complex.conj_im, ofReal_re, ofReal_im]
      ring
    · simp [suzukiUpperFourierLaplaceFeatureRaw, ht]
  rw [heq, integrable_indicator_iff measurableSet_Iic]
  exact integrableOn_exp_mul_Iic (by linarith) A

/-- `L²` feature representing upper-supported Fourier--Laplace evaluation. -/
def suzukiUpperFourierLaplaceFeature (A : ℝ) (z : ℂ) (hz : 0 < z.im) : SoninL2 :=
  (suzukiUpperFourierLaplaceFeatureRaw_memLp A hz).toLp
    (suzukiUpperFourierLaplaceFeatureRaw A z)

/-- Bounded Fourier--Laplace evaluation on the upper half-line `(-∞,A]`. -/
def suzukiUpperFourierLaplaceCLM (A : ℝ) (z : ℂ) (hz : 0 < z.im) :
    SoninL2 →L[ℂ] ℂ :=
  innerSL ℂ (suzukiUpperFourierLaplaceFeature A z hz)

theorem suzukiUpperFourierLaplaceCLM_eq_integral
    (A : ℝ) (z : ℂ) (hz : 0 < z.im) (q : SoninL2) :
    suzukiUpperFourierLaplaceCLM A z hz q =
      ∫ t : ℝ, (Iic A).indicator
        (fun t : ℝ => Complex.exp (-I * z * (t : ℂ)) * q t) t := by
  rw [suzukiUpperFourierLaplaceCLM, innerSL_apply_apply, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have hfeature := (suzukiUpperFourierLaplaceFeatureRaw_memLp A hz).coeFn_toLp
  filter_upwards [hfeature] with t ht
  rw [show suzukiUpperFourierLaplaceFeature A z hz t =
      suzukiUpperFourierLaplaceFeatureRaw A z t by
    simpa [suzukiUpperFourierLaplaceFeature] using ht]
  by_cases hmem : t ∈ Iic A
  · rw [suzukiUpperFourierLaplaceFeatureRaw, indicator_of_mem hmem,
      indicator_of_mem hmem, RCLike.inner_apply]
    rw [← Complex.exp_conj]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.star_def,
      Complex.conj_conj]
    ring
  · rw [suzukiUpperFourierLaplaceFeatureRaw, indicator_of_notMem hmem,
      indicator_of_notMem hmem, RCLike.inner_apply, map_zero, mul_zero]

/-! ## Lower-supported bounded Fourier--Laplace evaluation -/

/-- Raw Hilbert feature for `∫_{t≥B} exp(I z t) q(t) dt`. -/
def suzukiLowerFourierLaplaceFeatureRaw (B : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (Ici B).indicator (fun t : ℝ => Complex.exp (-I * star z * (t : ℂ))) t

theorem suzukiLowerFourierLaplaceFeatureRaw_memLp
    (B : ℝ) {z : ℂ} (hz : 0 < z.im) :
    MemLp (suzukiLowerFourierLaplaceFeatureRaw B z) 2 volume := by
  have hmeas : AEStronglyMeasurable (suzukiLowerFourierLaplaceFeatureRaw B z) volume :=
    ((by fun_prop : Continuous fun t : ℝ => Complex.exp (-I * star z * (t : ℂ)))
      |>.aestronglyMeasurable.indicator measurableSet_Ici)
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have heq : (fun t : ℝ => ‖suzukiLowerFourierLaplaceFeatureRaw B z t‖ ^ 2) =
      (Ici B).indicator (fun t : ℝ => Real.exp ((-2 * z.im) * t)) := by
    funext t
    by_cases ht : t ∈ Ici B
    · rw [suzukiLowerFourierLaplaceFeatureRaw, indicator_of_mem ht,
        indicator_of_mem ht, Complex.norm_exp, ← Real.exp_nat_mul]
      congr 1
      have hre : (-I * star z * (t : ℂ)).re = -(z.im * t) := by
        simp [Complex.mul_re]
      rw [hre]
      ring
    · simp [suzukiLowerFourierLaplaceFeatureRaw, ht]
  rw [heq, integrable_indicator_iff measurableSet_Ici,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_mul_Ioi (by linarith) B

/-- `L²` feature representing lower-supported Fourier--Laplace evaluation. -/
def suzukiLowerFourierLaplaceFeature (B : ℝ) (z : ℂ) (hz : 0 < z.im) : SoninL2 :=
  (suzukiLowerFourierLaplaceFeatureRaw_memLp B hz).toLp
    (suzukiLowerFourierLaplaceFeatureRaw B z)

/-- Bounded Fourier--Laplace evaluation on the lower half-line `[B,∞)`. -/
def suzukiLowerFourierLaplaceCLM (B : ℝ) (z : ℂ) (hz : 0 < z.im) :
    SoninL2 →L[ℂ] ℂ :=
  innerSL ℂ (suzukiLowerFourierLaplaceFeature B z hz)

theorem suzukiLowerFourierLaplaceCLM_eq_integral
    (B : ℝ) (z : ℂ) (hz : 0 < z.im) (q : SoninL2) :
    suzukiLowerFourierLaplaceCLM B z hz q =
      ∫ t : ℝ, (Ici B).indicator
        (fun t : ℝ => Complex.exp (I * z * (t : ℂ)) * q t) t := by
  rw [suzukiLowerFourierLaplaceCLM, innerSL_apply_apply, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have hfeature := (suzukiLowerFourierLaplaceFeatureRaw_memLp B hz).coeFn_toLp
  filter_upwards [hfeature] with t ht
  rw [show suzukiLowerFourierLaplaceFeature B z hz t =
      suzukiLowerFourierLaplaceFeatureRaw B z t by
    simpa [suzukiLowerFourierLaplaceFeature] using ht]
  by_cases hmem : t ∈ Ici B
  · rw [suzukiLowerFourierLaplaceFeatureRaw, indicator_of_mem hmem,
      indicator_of_mem hmem, RCLike.inner_apply]
    rw [← Complex.exp_conj]
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal,
      Complex.star_def, Complex.conj_conj]
    ring
  · rw [suzukiLowerFourierLaplaceFeatureRaw, indicator_of_notMem hmem,
      indicator_of_notMem hmem, RCLike.inner_apply, map_zero, mul_zero]

end RHTower

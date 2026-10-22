import GaloisForLFunctions.RHTower.CCM.CCMParityTopLayerEvenFloor
import GaloisForLFunctions.RHTower.CCM.CCMParityQuartetOddTest

/-!
# Smooth tests from a smooth model, under a finite top layer

Let `W` be a smooth real function with `|W| ≤ D` and `|W'| ≤ D'` on `[−a, a]`, and let
`W_a = W · 1_{(−a, a)}` (`truncModel`). The smooth cutoffs `χ` of the isolated-quartet odd test give
smooth interior sources `v_n = W χ_n` (`modelTestSeq`) with

* `v_n → W_a` pointwise off `|x| = a`, dominated by `D · 1_{[−a,a]}`;
* `∫ |v_n'| ≤ 2aD' + 2D` uniformly (`integral_norm_deriv_modelTestSource_le`).

So transforms and masses converge, and the critical-line part of the zero sum stays bounded by
`(2aD' + 2D)² Σ_q |z_q|^{−2}`.

**Theorem** (`exists_smooth_below_model`). Under a finite top layer, if
`Σ_{off-line} Re(Ŵ_a(−z) conj Ŵ_a(−z̄)) + (2aD' + 2D)² Σ_q |z_q|^{−2} < c ∫ W_a²`, then some smooth
source has Rayleigh quotient below `c`.
-/

open Matrix Complex Filter Topology MeasureTheory Set
open RHTower.CCMParityQuartet RHTower.CCMParityCauchy GaloisForLFunctions.HTGeometry

namespace RHTower.CCMParityTopLayer

noncomputable section

variable {m : ℕ}

/-- The model truncated to `(−a, a)`. -/
def truncModel (W : ℝ → ℝ) (a : ℝ) (x : ℝ) : ℝ := (Ioo (-a) a).indicator W x

/-- The smooth test `v(x) = W(x) χ(x)` with cutoff radius `b = a − 3ε`. -/
def modelTestSource (W : ℝ → ℝ) (hW : ContDiff ℝ (⊤ : ℕ∞) W) (a : SuzukiPositiveAperture)
    {ε : ℝ} (hε : 0 < ε) (hεa : 4 * ε < a.1) : CCMComplexSmoothInteriorSource a where
  toFun x := ((W x * cutoff hε (a.1 - 3 * ε) x : ℝ) : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp (hW.mul (contDiff_cutoff hε _))
  hasCompactSupport := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -a.1) (b := a.1)) ?_
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hK
    apply hx
    have hxa : a.1 < |x| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hK
      rcases hK with h | h
      · rw [abs_of_neg (by linarith [a.2])]; linarith
      · rw [abs_of_pos (by linarith [a.2])]; exact h
    rw [cutoff_eq_zero hε (by linarith) (by linarith)]
    simp
  tsupport_subset := by
    have hsupp : Function.support (fun x => ((W x * cutoff hε (a.1 - 3 * ε) x : ℝ) : ℂ))
        ⊆ Icc (-(a.1 - ε)) (a.1 - ε) := by
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hK
      apply hx
      have hxa : a.1 - ε < |x| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hK
        rcases hK with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact h
      rw [cutoff_eq_zero hε (by linarith) (by linarith)]
      simp
    refine (closure_minimal hsupp isClosed_Icc).trans ?_
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem modelTestSource_apply (W : ℝ → ℝ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (a : SuzukiPositiveAperture) {ε : ℝ} (hε : 0 < ε) (hεa : 4 * ε < a.1) (x : ℝ) :
    (modelTestSource W hW a hε hεa : ℝ → ℂ) x =
      ((W x * cutoff hε (a.1 - 3 * ε) x : ℝ) : ℂ) := rfl

theorem deriv_modelTestSource (W : ℝ → ℝ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (a : SuzukiPositiveAperture) {ε : ℝ} (hε : 0 < ε) (hεa : 4 * ε < a.1) (x : ℝ) :
    deriv (modelTestSource W hW a hε hεa : ℝ → ℂ) x =
      ((deriv W x * cutoff hε (a.1 - 3 * ε) x +
        W x * (bumpMollifier hε (x + (a.1 - 3 * ε)) -
          bumpMollifier hε (x - (a.1 - 3 * ε))) : ℝ) : ℂ) := by
  have hWd : HasDerivAt W (deriv W x) x :=
    (hW.differentiable (by simp)).differentiableAt.hasDerivAt
  have h := (hWd.mul (hasDerivAt_cutoff hε (a.1 - 3 * ε) x)).ofReal_comp
  exact h.deriv

/-- `∫ |v'| ≤ 2aD' + 2D`, uniformly in `ε`. -/
theorem integral_norm_deriv_modelTestSource_le (W : ℝ → ℝ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (a : SuzukiPositiveAperture) {D D' : ℝ} (hD : ∀ x ∈ Icc (-a.1) a.1, |W x| ≤ D)
    (hD' : ∀ x ∈ Icc (-a.1) a.1, |deriv W x| ≤ D') {ε : ℝ} (hε : 0 < ε) (hεa : 4 * ε < a.1) :
    ∫ x, ‖deriv (modelTestSource W hW a hε hεa : ℝ → ℂ) x‖ ≤ 2 * a.1 * D' + 2 * D := by
  set b := a.1 - 3 * ε with hb
  have ha : 0 < a.1 := a.2
  have h0 : (0 : ℝ) ∈ Icc (-a.1) a.1 := ⟨by linarith, by linarith⟩
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0 h0)
  have hD'0 : 0 ≤ D' := (abs_nonneg _).trans (hD' 0 h0)
  set B : ℝ → ℝ := fun x => (Icc (-a.1) a.1).indicator (fun _ => D') x +
    D * |bumpMollifier hε (x + b) - bumpMollifier hε (x - b)| with hB
  have hint2 : Integrable fun x => |bumpMollifier hε (x + b) - bumpMollifier hε (x - b)| :=
    ((integrable_bumpMollifier hε).comp_add_right b).sub
      ((integrable_bumpMollifier hε).comp_sub_right b) |>.abs
  have hint1 : Integrable fun x => (Icc (-a.1) a.1).indicator (fun _ => D') x :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have hBint : Integrable B := hint1.add (hint2.const_mul _)
  have hpt : ∀ x, ‖deriv (modelTestSource W hW a hε hεa : ℝ → ℂ) x‖ ≤ B x := by
    intro x
    rw [deriv_modelTestSource, Complex.norm_real, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    simp only [hB]
    by_cases hx : x ∈ Icc (-a.1) a.1
    · gcongr ?_ + ?_
      · rw [Set.indicator_of_mem hx, abs_mul,
          abs_of_nonneg (cutoff_nonneg hε (by linarith) x)]
        calc |deriv W x| * cutoff hε b x ≤ D' * 1 :=
              mul_le_mul (hD' x hx) (cutoff_le_one hε (by linarith) x)
                (cutoff_nonneg hε (by linarith) x) hD'0
          _ = D' := mul_one _
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hD x hx) (abs_nonneg _)
    · have hxa : a.1 < |x| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
        rcases hx with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact h
      have h1 : bumpMollifier hε (x + b) = 0 := by
        apply bumpMollifier_eq_zero hε
        rcases le_abs'.mp hxa.le with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have h2 : bumpMollifier hε (x - b) = 0 := by
        apply bumpMollifier_eq_zero hε
        rcases le_abs'.mp hxa.le with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [cutoff_eq_zero hε (by linarith) (by linarith), h1, h2, Set.indicator_of_notMem hx]
      simp
  calc ∫ x, ‖deriv (modelTestSource W hW a hε hεa : ℝ → ℂ) x‖ ≤ ∫ x, B x :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hBint
          (Filter.Eventually.of_forall hpt)
    _ = D' * (2 * a.1) +
          D * ∫ x, |bumpMollifier hε (x + b) - bumpMollifier hε (x - b)| := by
        rw [integral_add hint1 (hint2.const_mul _), integral_const_mul,
          integral_indicator measurableSet_Icc, setIntegral_const]
        rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
        ring
    _ ≤ D' * (2 * a.1) + D * 2 := by
        gcongr
        exact integral_abs_deriv_cutoff_le hε b
    _ = 2 * a.1 * D' + 2 * D := by ring

/-- The smooth tests with cutoff width `a/(n+6)`. -/
def modelTestSeq (W : ℝ → ℝ) (hW : ContDiff ℝ (⊤ : ℕ∞) W) (a : SuzukiPositiveAperture)
    (n : ℕ) : CCMComplexSmoothInteriorSource a :=
  modelTestSource W hW a (seqWidth_pos a n) (four_mul_seqWidth_lt a n)

theorem norm_modelTestSeq_le (W : ℝ → ℝ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (a : SuzukiPositiveAperture) {D : ℝ} (hD : ∀ x ∈ Icc (-a.1) a.1, |W x| ≤ D) (n : ℕ)
    (x : ℝ) :
    ‖(modelTestSeq W hW a n : ℝ → ℂ) x‖ ≤ (Icc (-a.1) a.1).indicator (fun _ => D) x := by
  set ε := a.1 / ((n : ℝ) + 6) with hε_def
  have hε := seqWidth_pos a n
  have h4 := four_mul_seqWidth_lt a n
  rw [modelTestSeq, modelTestSource_apply, Complex.norm_real, Real.norm_eq_abs]
  by_cases hx : x ∈ Icc (-a.1) a.1
  · rw [Set.indicator_of_mem hx, abs_mul, abs_of_nonneg (cutoff_nonneg hε (by linarith) x)]
    calc |W x| * cutoff hε (a.1 - 3 * ε) x ≤ D * 1 :=
          mul_le_mul (hD x hx) (cutoff_le_one hε (by linarith) x)
            (cutoff_nonneg hε (by linarith) x) ((abs_nonneg _).trans (hD x hx))
      _ = D := mul_one _
  · rw [Set.indicator_of_notMem hx]
    have hxa : a.1 < |x| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith [a.2])]; linarith
      · rw [abs_of_pos (by linarith [a.2])]; exact h
    rw [cutoff_eq_zero hε (by linarith) (by linarith)]
    simp

theorem tendsto_modelTestSeq (W : ℝ → ℝ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (a : SuzukiPositiveAperture) {x : ℝ} (hx : |x| ≠ a.1) :
    Tendsto (fun n => (modelTestSeq W hW a n : ℝ → ℂ) x) atTop
      (𝓝 ((truncModel W a.1 x : ℝ) : ℂ)) := by
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have hgap : 0 < a.1 - |x| := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (5 * a.1 / (a.1 - |x|))
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hε := seqWidth_pos a n
    have hn' : (5 * a.1 / (a.1 - |x|)) < (n : ℝ) + 6 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hcut : |x| ≤ a.1 - 3 * (a.1 / ((n : ℝ) + 6)) - 2 * (a.1 / ((n : ℝ) + 6)) := by
      have hpos : (0 : ℝ) < (n : ℝ) + 6 := by positivity
      rw [div_lt_iff₀ hgap] at hn'
      have : 5 * (a.1 / ((n : ℝ) + 6)) ≤ a.1 - |x| := by
        rw [mul_div_assoc', div_le_iff₀ hpos]
        nlinarith
      linarith
    have hxI : x ∈ Ioo (-a.1) a.1 := abs_lt.mp hlt
    rw [modelTestSeq, modelTestSource_apply, cutoff_eq_one hε hcut, mul_one, truncModel,
      Set.indicator_of_mem hxI]
  · have hxI : x ∉ Ioo (-a.1) a.1 := fun h => by
      have := abs_lt.mpr ⟨h.1, h.2⟩
      linarith
    apply tendsto_const_nhds.congr'
    filter_upwards with n
    have hε := seqWidth_pos a n
    have h4 := four_mul_seqWidth_lt a n
    rw [modelTestSeq, modelTestSource_apply, truncModel, Set.indicator_of_notMem hxI,
      cutoff_eq_zero hε (by linarith) (by linarith)]
    simp

theorem tendsto_testTransform_modelTestSeq (W : ℝ → ℝ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (a : SuzukiPositiveAperture) {D : ℝ} (hD : ∀ x ∈ Icc (-a.1) a.1, |W x| ≤ D) (w : ℂ) :
    Tendsto (fun n => testTransform (modelTestSeq W hW a n) w) atTop
      (𝓝 (testTransform (fun x => ((truncModel W a.1 x : ℝ) : ℂ)) w)) := by
  unfold testTransform
  set E : ℝ := Real.exp (a.1 * |w.im|) with hE
  apply tendsto_integral_of_dominated_convergence
    (fun x => (Icc (-a.1) a.1).indicator (fun _ => D * E) x)
  · intro n
    exact ((modelTestSeq W hW a n).continuous.mul (by fun_prop)).aestronglyMeasurable
  · exact (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  · intro n
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul]
    have h1 := norm_modelTestSeq_le W hW a hD n x
    by_cases hx : x ∈ Icc (-a.1) a.1
    · rw [Set.indicator_of_mem hx] at h1 ⊢
      have h2 : ‖Complex.exp (Complex.I * w * (x : ℂ))‖ ≤ E := by
        rw [Complex.norm_exp, hE]
        apply Real.exp_le_exp.mpr
        have hre : (Complex.I * w * (x : ℂ)).re = -(w.im * x) := by
          simp [Complex.mul_re, Complex.mul_im]
        rw [hre]
        have hx' : |x| ≤ a.1 := abs_le.mpr ⟨hx.1, hx.2⟩
        have h1 : -(w.im * x) ≤ |w.im * x| := neg_le_abs _
        rw [abs_mul] at h1
        nlinarith [abs_nonneg w.im]
      exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    · rw [Set.indicator_of_notMem hx] at h1 ⊢
      have : ‖(modelTestSeq W hW a n : ℝ → ℂ) x‖ = 0 := le_antisymm h1 (norm_nonneg _)
      rw [this, zero_mul]
  · filter_upwards [ae_ne_abs a.1] with x hx
    exact (tendsto_modelTestSeq W hW a hx).mul_const _

theorem tendsto_integral_norm_sq_modelTestSeq (W : ℝ → ℝ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (a : SuzukiPositiveAperture) {D : ℝ} (hD : ∀ x ∈ Icc (-a.1) a.1, |W x| ≤ D) :
    Tendsto (fun n => ∫ x, ‖(modelTestSeq W hW a n : ℝ → ℂ) x‖ ^ 2) atTop
      (𝓝 (∫ x, truncModel W a.1 x ^ 2)) := by
  have hlim : (fun x => truncModel W a.1 x ^ 2) = fun x => ‖((truncModel W a.1 x : ℝ) : ℂ)‖ ^ 2 := by
    funext x; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hlim]
  apply tendsto_integral_of_dominated_convergence
    (fun x => (Icc (-a.1) a.1).indicator (fun _ => D ^ 2) x)
  · intro n
    exact ((modelTestSeq W hW a n).continuous.norm.pow 2).aestronglyMeasurable
  · exact (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  · intro n
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := norm_modelTestSeq_le W hW a hD n x
    by_cases hx : x ∈ Icc (-a.1) a.1
    · rw [Set.indicator_of_mem hx] at h1 ⊢
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    · rw [Set.indicator_of_notMem hx] at h1 ⊢
      have : ‖(modelTestSeq W hW a n : ℝ → ℂ) x‖ = 0 := le_antisymm h1 (norm_nonneg _)
      rw [this]
      norm_num
  · filter_upwards [ae_ne_abs a.1] with x hx
    exact ((tendsto_modelTestSeq W hW a hx).norm).pow 2

/-! ## Upper bound for the zero sum and the smooth test below a level -/

/-- **Upper bound for the zero sum.** The source quadratic of a smooth source is at most its
off-line part plus `K² Σ_q |z_q|^{−2}`, `K = ∫ |u'|`. -/
theorem sourceQuadratic_le_offLine_add {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector ≤
      ∑ q ∈ h.offLine, (zeroSumTerm u (xiSpectralPoint q)).re +
        (∫ x, ‖deriv (u : ℝ → ℂ) x‖) ^ 2 *
          ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  classical
  have hu1 : ContDiff ℝ 1 (u : ℝ → ℂ) := u.smooth.of_le (by exact_mod_cast le_top)
  set K := ∫ x, ‖deriv (u : ℝ → ℂ) x‖ with hK
  set T : XiZeroCopy → ℂ := fun q => zeroSumTerm u (xiSpectralPoint q) with hT
  have hsumm : Summable T := summable_zeroSumTerm u
  have hsumm_re : Summable fun q => (T q).re := Complex.reCLM.summable hsumm
  set g : XiZeroCopy → ℝ := fun q => if q ∈ h.offLine then (T q).re else 0 with hg
  have hgsupp : ∀ q ∉ h.offLine, g q = 0 := fun q hq => by simp [hg, hq]
  have hgsum : Summable g := summable_of_ne_finset_zero hgsupp
  have hS : Summable fun q : XiZeroCopy => K ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) :=
    xiSpectralPoint_inv_sq_summable.mul_left _
  have hle : ∀ q, (T q).re ≤ g q + K ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
    intro q
    simp only [hg]
    split_ifs with hq
    · have : 0 ≤ K ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by positivity
      linarith
    · have him : (xiSpectralPoint q).im = 0 := by
        by_contra hne
        exact hq (h.mem_offLine.mpr hne)
      rw [zero_add]
      exact re_zeroSumTerm_le_of_im_eq_zero hu1 u.hasCompactSupport him
        (xiSpectralPoint_ne_zero q)
  rw [sourceQuadratic_eq_re_tsum, Complex.re_tsum hsumm]
  calc ∑' q, (T q).re ≤ ∑' q, (g q + K ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) :=
        hsumm_re.tsum_le_tsum hle (hgsum.add hS)
    _ = ∑' q, g q + ∑' q, K ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := hgsum.tsum_add hS
    _ = ∑ q ∈ h.offLine, (T q).re +
          K ^ 2 * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
        rw [tsum_eq_sum hgsupp, tsum_mul_left]
        congr 1
        exact Finset.sum_congr rfl fun q hq => by simp [hg, hq]

/-- **A smooth test below a given level.** -/
theorem exists_smooth_below_model {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    (a : SuzukiPositiveAperture) (W : ℝ → ℝ) (hW : ContDiff ℝ (⊤ : ℕ∞) W) {D D' : ℝ}
    (hD : ∀ x ∈ Icc (-a.1) a.1, |W x| ≤ D) (hD' : ∀ x ∈ Icc (-a.1) a.1, |deriv W x| ≤ D')
    {c : ℝ}
    (hlt : ∑ q ∈ h.offLine,
          (zeroSumTerm (fun x => ((truncModel W a.1 x : ℝ) : ℂ)) (xiSpectralPoint q)).re +
        (2 * a.1 * D' + 2 * D) ^ 2 * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) <
      c * ∫ x, truncModel W a.1 x ^ 2) :
    ∃ v : CCMComplexSmoothInteriorSource a,
      ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector <
        c * ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 := by
  set K : ℝ := 2 * a.1 * D' + 2 * D with hK
  set S : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  set X : ℝ := ∑ q ∈ h.offLine,
    (zeroSumTerm (fun x => ((truncModel W a.1 x : ℝ) : ℂ)) (xiSpectralPoint q)).re with hX
  have hbound : ∀ n, ccmRestrictedWeilSourceQuadratic a (modelTestSeq W hW a n).toCCMFormVector ≤
      ∑ q ∈ h.offLine, (zeroSumTerm (modelTestSeq W hW a n) (xiSpectralPoint q)).re +
        K ^ 2 * S := by
    intro n
    refine (sourceQuadratic_le_offLine_add h (modelTestSeq W hW a n)).trans ?_
    have hK1 : (∫ x, ‖deriv (modelTestSeq W hW a n : ℝ → ℂ) x‖) ≤ K :=
      integral_norm_deriv_modelTestSource_le W hW a hD hD' _ _
    have hK0 : 0 ≤ ∫ x, ‖deriv (modelTestSeq W hW a n : ℝ → ℂ) x‖ :=
      integral_nonneg fun _ => norm_nonneg _
    have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hK0 hK1 2) hS0
    linarith
  have hterm : ∀ z : ℂ, Tendsto (fun n => (zeroSumTerm (modelTestSeq W hW a n) z).re) atTop
      (𝓝 (zeroSumTerm (fun x => ((truncModel W a.1 x : ℝ) : ℂ)) z).re) := by
    intro z
    unfold zeroSumTerm
    exact Complex.continuous_re.continuousAt.tendsto.comp
      ((tendsto_testTransform_modelTestSeq W hW a hD (-z)).mul
        ((Complex.continuous_conj.tendsto _).comp
          (tendsto_testTransform_modelTestSeq W hW a hD (-(starRingEnd ℂ) z))))
  have hconv : Tendsto (fun n =>
      (∑ q ∈ h.offLine, (zeroSumTerm (modelTestSeq W hW a n) (xiSpectralPoint q)).re +
        K ^ 2 * S) - c * ∫ x, ‖(modelTestSeq W hW a n : ℝ → ℂ) x‖ ^ 2) atTop
      (𝓝 ((X + K ^ 2 * S) - c * ∫ x, truncModel W a.1 x ^ 2)) :=
    ((tendsto_finsetSum _ fun q _ => hterm _).add_const _).sub
      ((tendsto_integral_norm_sq_modelTestSeq W hW a hD).const_mul c)
  have hneg : (X + K ^ 2 * S) - c * ∫ x, truncModel W a.1 x ^ 2 < 0 := by linarith
  obtain ⟨n, hn⟩ := (hconv.eventually (gt_mem_nhds hneg)).exists
  refine ⟨modelTestSeq W hW a n, ?_⟩
  rw [norm_sq_toAperture_toCCMFormVector]
  have := hbound n
  linarith

end

end RHTower.CCMParityTopLayer

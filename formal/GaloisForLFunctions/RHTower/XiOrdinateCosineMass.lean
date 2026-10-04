import GaloisForLFunctions.HTGeometry.OneSubCosKernelIntegral
import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.XiZeroCountRVMRemainder
import GaloisForLFunctions.RHTower.XiOrderedPositiveZeros
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap

/-!
# The ordinate cosine mass `Σ_ρ (1 - cos(T/γ_ρ))`

For a multiplicity copy `q` of a `ξ`-zero `ρ = β + iγ` write `γ_q = Im ρ`.  Every copy has
`|γ_q| > 4` (the source height gap `γ² > 41/2`) and `Σ_q γ_q⁻² < ∞`.  The cosine mass

```text
A(T) = Σ_q (1 - cos(T/γ_q))
```

is therefore absolutely convergent, and

```text
|A(T) - (T/2) log T| ≤ C T          (T ≥ 2π),
```

unconditionally.  The proof is Abel summation against the copy count `#{q : |γ_q| ≤ y} = 2N(y)`,
the Riemann–von Mangoldt law `N = Q + O(log)` with `Q(y) = (y/2π) log(y/2πe) + 7/8`, an
integration by parts moving the derivative onto `Q' = (log y - log 2π)/(2π)`, and the inversion
substitution `y = T/x`, which turns the smooth term into `(T/π)∫_0^{T/4} k(x) log(T/(2πx)) dx`
with `k(x) = (1 - cos x)/x²`.  The kernel mass `∫_0^∞ k = π/2` gives the leading coefficient
`(T/π)(π/2) = T/2`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The ordinate of a multiplicity copy of a `ξ`-zero. -/
def xiCopyOrdinate (q : XiZeroCopy) : ℝ := ((q.1 : ℂ)).im

theorem four_lt_abs_xiCopyOrdinate (q : XiZeroCopy) : 4 < |xiCopyOrdinate q| := by
  have h := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have h16 : (4 : ℝ) ^ 2 < |xiCopyOrdinate q| ^ 2 := by
    rw [sq_abs]; unfold xiCopyOrdinate; linarith
  exact lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) h16

theorem xiCopyOrdinate_ne_zero (q : XiZeroCopy) : xiCopyOrdinate q ≠ 0 := by
  intro h
  have := four_lt_abs_xiCopyOrdinate q
  rw [h, abs_zero] at this
  linarith

/-- The inverse squared ordinates are summable. -/
theorem summable_inv_sq_xiCopyOrdinate :
    Summable (fun q : XiZeroCopy => 1 / xiCopyOrdinate q ^ 2) := by
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_)
    (xiSpectralPoint_inv_sq_summable.mul_left 4)
  have hγ := four_lt_abs_xiCopyOrdinate q
  have hstrip := xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support q.1)
  have hα : ‖xiSpectralPoint q‖ ≤ 2 * |xiCopyOrdinate q| := by
    rw [norm_xiSpectralPoint]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hre : |((q.1 : ℂ) - 1 / 2).re| ≤ 1 / 2 := by
      rw [Complex.sub_re, show ((1 / 2 : ℂ)).re = 1 / 2 by norm_num, abs_le]
      constructor <;> linarith [hstrip.1, hstrip.2]
    have him : ((q.1 : ℂ) - 1 / 2).im = xiCopyOrdinate q := by
      simp [xiCopyOrdinate]
    rw [him]
    linarith
  have hαpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.2 (xiSpectralPoint_ne_zero q)
  have hsq : ‖xiSpectralPoint q‖ ^ 2 ≤ 4 * xiCopyOrdinate q ^ 2 := by
    have := pow_le_pow_left₀ hαpos.le hα 2
    rw [mul_pow, sq_abs] at this
    linarith
  have hγ2 : 0 < xiCopyOrdinate q ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (xiCopyOrdinate_ne_zero q)))
  rw [div_le_iff₀ hγ2]
  calc (1 : ℝ) = 4 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) * (‖xiSpectralPoint q‖ ^ 2 / 4) := by
        field_simp
    _ ≤ 4 * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) * xiCopyOrdinate q ^ 2 := by
        gcongr
        linarith

/-- The ordinate cosine mass `A(T) = Σ_q (1 - cos(T/γ_q))`. -/
def xiOrdinateCosineMass (T : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, (1 - Real.cos (T / xiCopyOrdinate q))

theorem summable_xiOrdinateCosine (T : ℝ) :
    Summable (fun q : XiZeroCopy => 1 - Real.cos (T / xiCopyOrdinate q)) := by
  refine Summable.of_nonneg_of_le (fun q => one_sub_cos_nonneg _) (fun q => ?_)
    (summable_inv_sq_xiCopyOrdinate.mul_left (T ^ 2 / 2))
  calc 1 - Real.cos (T / xiCopyOrdinate q) ≤ (T / xiCopyOrdinate q) ^ 2 / 2 := by
        linarith [Real.one_sub_sq_div_two_le_cos (x := T / xiCopyOrdinate q)]
    _ = T ^ 2 / 2 * (1 / xiCopyOrdinate q ^ 2) := by ring

/-! ## Windows of copies -/

theorem tendsto_xiCopiesBand_zero_atTop :
    Tendsto (fun Y : ℝ => xiCopiesBand 0 Y) atTop atTop := by
  classical
  rw [tendsto_atTop]
  intro s
  filter_upwards [eventually_ge_atTop (∑ q ∈ s, |xiCopyOrdinate q|)] with Y hY
  intro q hq
  rw [mem_xiCopiesBand]
  refine ⟨abs_pos.2 (xiCopyOrdinate_ne_zero q), ?_⟩
  exact (Finset.single_le_sum (f := fun q => |xiCopyOrdinate q|) (fun _ _ => abs_nonneg _) hq).trans
    hY

theorem tendsto_xiOrdinateCosine_window (T : ℝ) :
    Tendsto (fun Y : ℝ => ∑ q ∈ xiCopiesBand 0 Y, (1 - Real.cos (T / xiCopyOrdinate q)))
      atTop (𝓝 (xiOrdinateCosineMass T)) :=
  ((summable_xiOrdinateCosine T).hasSum).comp tendsto_xiCopiesBand_zero_atTop

/-- The copy count below a height is twice the zero-counting function. -/
theorem card_xiCopiesBand_zero_eq {y : ℝ} (hy : 0 ≤ y) :
    ((xiCopiesBand 0 y).card : ℝ) = 2 * (xiZeroCount y : ℝ) := by
  have h := xiSymmetricMass_diff_eq_card (le_refl (0 : ℝ)) hy
  rw [xiSymmetricMass_eq_two_mul_pos hy, xiSymmetricMass_eq_two_mul_pos le_rfl,
    ← xiZeroCount_eq_pos_sum hy, ← xiZeroCount_eq_pos_sum le_rfl, xiZeroCount_zero] at h
  have h' : ((xiCopiesBand 0 y).card : ℤ) = 2 * xiZeroCount y := by linarith
  exact_mod_cast h'

/-! ## The cosine profile and its derivative -/

/-- The derivative weight `g_T(y) = (T/y²) sin(T/y)` of `1 - cos(T/y)`. -/
def xiCosineWeight (T y : ℝ) : ℝ := T / y ^ 2 * Real.sin (T / y)

theorem hasDerivAt_one_sub_cos_div {T y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 - Real.cos (T / y)) (-xiCosineWeight T y) y := by
  have hinv : HasDerivAt (fun y : ℝ => T / y) (-T / y ^ 2) y := by
    have h := (hasDerivAt_inv hy).const_mul T
    have e1 : (fun y : ℝ => T * y⁻¹) = fun y => T / y := by funext x; rw [div_eq_mul_inv]
    have e2 : T * -(y ^ 2)⁻¹ = -T / y ^ 2 := by ring
    rw [e1, e2] at h
    exact h
  have h := (hinv.cos).const_sub 1
  have e3 : -(-Real.sin (T / y) * (-T / y ^ 2)) = -xiCosineWeight T y := by
    unfold xiCosineWeight; ring
  rw [e3] at h
  exact h

theorem continuousOn_xiCosineWeight (T : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (xiCosineWeight T) (Icc a b) := by
  unfold xiCosineWeight
  have hne : ∀ y ∈ Icc a b, y ≠ 0 := fun y hy => (ha.trans_le hy.1).ne'
  apply ContinuousOn.mul
  · exact continuousOn_const.div (continuousOn_pow 2) fun y hy => pow_ne_zero 2 (hne y hy)
  · exact Real.continuous_sin.comp_continuousOn
      (continuousOn_const.div continuousOn_id hne : ContinuousOn (fun y : ℝ => T / y) _)

theorem abs_xiCosineWeight_le {T y : ℝ} (hT : 0 ≤ T) (hy : 0 < y) :
    |xiCosineWeight T y| ≤ T / y ^ 2 := by
  unfold xiCosineWeight
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ T / y ^ 2)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)

/-- **Abel window identity.**  For `Y ≥ 4`,
`Σ_{|γ_q| ≤ Y} (1 - cos(T/γ_q)) = 2N(Y)(1 - cos(T/Y)) + ∫_4^Y g_T(y)·2N(y) dy`. -/
theorem xiOrdinateCosine_window_eq (T : ℝ) {Y : ℝ} (hY : 4 ≤ Y) :
    ∑ q ∈ xiCopiesBand 0 Y, (1 - Real.cos (T / xiCopyOrdinate q)) =
      2 * (xiZeroCount Y : ℝ) * (1 - Real.cos (T / Y)) +
        ∫ y in (4 : ℝ)..Y, xiCosineWeight T y * (2 * (xiZeroCount y : ℝ)) := by
  classical
  have habs : ∀ q : XiZeroCopy, Real.cos (T / xiCopyOrdinate q) =
      Real.cos (T / |xiCopyOrdinate q|) := by
    intro q
    rcases le_or_gt 0 (xiCopyOrdinate q) with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, div_neg, Real.cos_neg]
  simp_rw [habs]
  have hmem : ∀ q ∈ xiCopiesBand 0 Y, (4 : ℝ) < |xiCopyOrdinate q| ∧ |xiCopyOrdinate q| ≤ Y := by
    intro q hq
    exact ⟨four_lt_abs_xiCopyOrdinate q, (mem_xiCopiesBand.1 hq).2⟩
  have habel := sum_eq_card_mul_add_integral_count (xiCopiesBand 0 Y)
    (fun q => |xiCopyOrdinate q|) hmem (φ := fun y => 1 - Real.cos (T / y))
    (g := xiCosineWeight T)
    (fun y hy => hasDerivAt_one_sub_cos_div (by linarith [hy.1]))
    (continuousOn_xiCosineWeight T (by norm_num))
  rw [habel, card_xiCopiesBand_zero_eq (by linarith)]
  congr 1
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le hY] at hy
  have hfilter : ((xiCopiesBand 0 Y).filter fun q => |xiCopyOrdinate q| ≤ y) =
      xiCopiesBand 0 y := by
    ext q
    simp only [Finset.mem_filter, mem_xiCopiesBand]
    unfold xiCopyOrdinate
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hy.2⟩, h2⟩
  rw [hfilter, card_xiCopiesBand_zero_eq (by linarith [hy.1])]

/-! ## The smooth counting term -/

/-- The derivative of the smooth Riemann–von Mangoldt count, `(log y - log 2π)/(2π)`. -/
def xiSmoothCountDeriv (y : ℝ) : ℝ := (Real.log y - Real.log (2 * Real.pi)) / (2 * Real.pi)

theorem hasDerivAt_routeKSmoothRVMCount {y : ℝ} (hy : 0 < y) :
    HasDerivAt routeKSmoothRVMCount (xiSmoothCountDeriv y) y := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hb : routeKRVMBase = 2 * Real.pi * Real.exp 1 := rfl
  have hlogb : Real.log routeKRVMBase = Real.log (2 * Real.pi) + 1 := by
    rw [hb, Real.log_mul hpi.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have hlog : HasDerivAt (fun y => Real.log (y / routeKRVMBase)) (1 / y) y := by
    have h1 : HasDerivAt (fun y : ℝ => y / routeKRVMBase) (1 / routeKRVMBase) y :=
      (hasDerivAt_id' y).div_const _
    have h := h1.log (div_pos hy routeKRVMBase_pos).ne'
    have e : 1 / routeKRVMBase / (y / routeKRVMBase) = 1 / y := by
      field_simp [routeKRVMBase_pos.ne']
    rw [e] at h
    exact h
  have h2 : HasDerivAt (fun y : ℝ => y / (2 * Real.pi)) (1 / (2 * Real.pi)) y :=
    (hasDerivAt_id' y).div_const _
  have h := (h2.mul hlog).add_const (7 / 8 : ℝ)
  have e : 1 / (2 * Real.pi) * Real.log (y / routeKRVMBase) + y / (2 * Real.pi) * (1 / y) =
      xiSmoothCountDeriv y := by
    unfold xiSmoothCountDeriv
    rw [Real.log_div hy.ne' routeKRVMBase_pos.ne', hlogb]
    field_simp
    ring
  rw [e] at h
  exact h

theorem continuousOn_routeKSmoothRVMCount_Ioi :
    ContinuousOn routeKSmoothRVMCount (Ioi 0) := fun _ hy =>
  (hasDerivAt_routeKSmoothRVMCount hy).continuousAt.continuousWithinAt

theorem continuousOn_xiSmoothCountDeriv {a b : ℝ} (ha : 0 < a) :
    ContinuousOn xiSmoothCountDeriv (Icc a b) := by
  unfold xiSmoothCountDeriv
  exact ((Real.continuousOn_log.mono fun y hy => (ha.trans_le hy.1).ne').sub
    continuousOn_const).div_const _

/-- The Riemann–von Mangoldt remainder is at most `C √y` on `[4, ∞)`. -/
theorem exists_abs_xiZeroCount_sub_smooth_le_sqrt :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 4 ≤ y →
      |(xiZeroCount y : ℝ) - routeKSmoothRVMCount y| ≤ C * Real.sqrt y := by
  obtain ⟨C, hC, T₀, hT₀, hrvm⟩ := exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  have hcont : ContinuousOn routeKSmoothRVMCount (Icc 4 T₀) :=
    continuousOn_routeKSmoothRVMCount_Ioi.mono fun y hy => by
      simp only [mem_Ioi]; linarith [hy.1]
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 4 ⟨le_rfl, hT₀⟩)
  set D : ℝ := (xiZeroCount T₀ : ℝ) + B with hD
  have hN0 : ∀ y, 0 ≤ (xiZeroCount y : ℝ) := fun y => by exact_mod_cast xiZeroCount_nonneg y
  have hD0 : 0 ≤ D := by have := hN0 T₀; linarith
  refine ⟨max (2 * C) D, le_max_of_le_right hD0, fun y hy => ?_⟩
  have hsqrt2 : 2 ≤ Real.sqrt y := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hy
  rcases le_or_gt T₀ y with hyT | hyT
  · have hlog : Real.log y ≤ 2 * Real.sqrt y := by
      have := Real.log_le_rpow_div (x := y) (by linarith) (ε := 1 / 2) (by norm_num)
      rw [Real.sqrt_eq_rpow]; linarith
    calc |(xiZeroCount y : ℝ) - routeKSmoothRVMCount y| ≤ C * Real.log y := hrvm y hyT
      _ ≤ C * (2 * Real.sqrt y) := mul_le_mul_of_nonneg_left hlog hC.le
      _ = 2 * C * Real.sqrt y := by ring
      _ ≤ max (2 * C) D * Real.sqrt y :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  · have hNle : (xiZeroCount y : ℝ) ≤ xiZeroCount T₀ := by
      exact_mod_cast xiZeroCount_mono hyT.le
    have hQ : |routeKSmoothRVMCount y| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB y ⟨hy, hyT.le⟩
    calc |(xiZeroCount y : ℝ) - routeKSmoothRVMCount y|
        ≤ |(xiZeroCount y : ℝ)| + |routeKSmoothRVMCount y| := abs_sub _ _
      _ ≤ D := by
          rw [abs_of_nonneg (hN0 y), hD]; linarith
      _ ≤ D * Real.sqrt y := by nlinarith
      _ ≤ max (2 * C) D * Real.sqrt y :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)

/-! ## The smooth main term -/

private theorem log_two_pi_lt_two : Real.log (2 * Real.pi) < 2 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  nlinarith

private theorem log_two_pi_pos : 0 < Real.log (2 * Real.pi) :=
  Real.log_pos (by nlinarith [Real.pi_gt_three])

private theorem sqrt_div_sq_eq_rpow {y : ℝ} (hy : 0 < y) :
    Real.sqrt y / y ^ 2 = y ^ (-3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, show (-3 / 2 : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub hy,
    Real.rpow_two]

private theorem two_le_sqrt {y : ℝ} (hy : 4 ≤ y) : 2 ≤ Real.sqrt y := by
  rw [show (2 : ℝ) = Real.sqrt 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt hy

private theorem log_le_two_sqrt {y : ℝ} (hy : 0 ≤ y) : Real.log y ≤ 2 * Real.sqrt y := by
  have := Real.log_le_rpow_div (x := y) hy (ε := 1 / 2) (by norm_num)
  rw [Real.sqrt_eq_rpow]; linarith

theorem abs_xiSmoothCountDeriv_le {y : ℝ} (hy : 4 ≤ y) :
    |xiSmoothCountDeriv y| ≤ Real.sqrt y := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hs := two_le_sqrt hy
  have hl := log_le_two_sqrt (y := y) (by linarith)
  have hl2 := log_two_pi_lt_two
  have hl3 := log_two_pi_pos
  unfold xiSmoothCountDeriv
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), div_le_iff₀ (by positivity)]
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_xiSmoothCountDeriv_mul_le {T y : ℝ} (hy : 4 ≤ y) :
    |xiSmoothCountDeriv y * (1 - Real.cos (T / y))| ≤ T ^ 2 * y ^ (-3 / 2 : ℝ) := by
  have hy0 : 0 < y := by linarith
  rw [abs_mul, abs_of_nonneg (one_sub_cos_nonneg _), ← sqrt_div_sq_eq_rpow hy0]
  have h1 := abs_xiSmoothCountDeriv_le hy
  have h2 : 1 - Real.cos (T / y) ≤ T ^ 2 / y ^ 2 := by
    have : 1 - Real.cos (T / y) ≤ (T / y) ^ 2 / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := T / y)]
    rw [div_pow] at this
    have : 0 ≤ T ^ 2 / y ^ 2 := by positivity
    linarith
  calc |xiSmoothCountDeriv y| * (1 - Real.cos (T / y)) ≤ Real.sqrt y * (T ^ 2 / y ^ 2) :=
        mul_le_mul h1 h2 (one_sub_cos_nonneg _) (Real.sqrt_nonneg _)
    _ = T ^ 2 * (Real.sqrt y / y ^ 2) := by ring

theorem integrableOn_xiSmoothCountDeriv_mul (T : ℝ) :
    IntegrableOn (fun y => xiSmoothCountDeriv y * (1 - Real.cos (T / y))) (Ioi 4) := by
  have hb : IntegrableOn (fun y : ℝ => T ^ 2 * y ^ (-3 / 2 : ℝ)) (Ioi 4) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul _
  refine Integrable.mono' hb ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have hne : ∀ y ∈ Ioi (4 : ℝ), y ≠ 0 := fun y hy => by
      simp only [mem_Ioi] at hy; linarith
    unfold xiSmoothCountDeriv
    apply ContinuousOn.mul
    · exact ((Real.continuousOn_log.mono hne).sub continuousOn_const).div_const _
    · exact continuousOn_const.sub (Real.continuous_cos.comp_continuousOn
        (continuousOn_const.div continuousOn_id hne : ContinuousOn (fun y : ℝ => T / y) _))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs]
    exact abs_xiSmoothCountDeriv_mul_le (le_of_lt hy)

/-- The smooth main term `J(T) = 2∫_{y>4} Q'(y)(1 - cos(T/y)) dy`. -/
def xiOrdinateSmoothTerm (T : ℝ) : ℝ :=
  2 * ∫ y in Ioi 4, xiSmoothCountDeriv y * (1 - Real.cos (T / y))

/-- The absolute logarithmic moment `∫_0^∞ k(x)|log x| dx` of the kernel. -/
def oneSubCosLogMoment : ℝ := ∫ x in Ioi 0, |oneSubCosKernel x * Real.log x|

theorem oneSubCosLogMoment_nonneg : 0 ≤ oneSubCosLogMoment :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => abs_nonneg _

/-- The inversion substitution evaluates the smooth term against the kernel `k`. -/
theorem xiOrdinateSmoothTerm_eq {T : ℝ} (hT : 0 < T) :
    xiOrdinateSmoothTerm T = T / Real.pi *
      ((Real.log T - Real.log (2 * Real.pi)) * (∫ x in Ioc 0 (T / 4), oneSubCosKernel x) -
        ∫ x in Ioc 0 (T / 4), oneSubCosKernel x * Real.log x) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold xiOrdinateSmoothTerm
  rw [← integral_Ici_eq_integral_Ioi, integral_Ici_eq_integral_Ioc_inv hT (by norm_num : (0 : ℝ) < 4)]
  have hk : IntegrableOn oneSubCosKernel (Ioc 0 (T / 4)) :=
    integrable_oneSubCosKernel.integrableOn
  have hkl : IntegrableOn (fun x => oneSubCosKernel x * Real.log x) (Ioc 0 (T / 4)) :=
    integrableOn_oneSubCosKernel_mul_log.mono_set Ioc_subset_Ioi_self
  have hpt : ∀ x ∈ Ioc (0 : ℝ) (T / 4),
      T / x ^ 2 * (xiSmoothCountDeriv (T / x) * (1 - Real.cos (T / (T / x)))) =
        T / (2 * Real.pi) * ((Real.log T - Real.log (2 * Real.pi)) * oneSubCosKernel x -
          oneSubCosKernel x * Real.log x) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    rw [show T / (T / x) = x by field_simp, xiSmoothCountDeriv,
      Real.log_div hT.ne' hx0.ne', oneSubCosKernel]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_const_mul,
    integral_sub (hk.const_mul _) hkl, integral_const_mul, ← mul_assoc,
    show (2 : ℝ) * (T / (2 * Real.pi)) = T / Real.pi by field_simp]

theorem integral_Ioc_oneSubCosKernel {U : ℝ} (hU : 0 < U) :
    ∫ x in Ioc 0 U, oneSubCosKernel x = Real.pi / 2 - (∫ x in Ioi U, oneSubCosKernel x) := by
  have h := setIntegral_union (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := U)) measurableSet_Ioi
    (integrable_oneSubCosKernel.integrableOn) (integrable_oneSubCosKernel.integrableOn)
    (f := oneSubCosKernel) (μ := volume)
  rw [Ioc_union_Ioi_eq_Ioi hU.le, integral_Ioi_oneSubCosKernel] at h
  linarith

/-- The smooth term is `(T/2) log T + O(T)`. -/
theorem abs_xiOrdinateSmoothTerm_sub_le {T : ℝ} (hT : 2 * Real.pi ≤ T) :
    |xiOrdinateSmoothTerm T - T / 2 * Real.log T| ≤
      (Real.log (2 * Real.pi) / 2 + 3 + oneSubCosLogMoment / Real.pi) * T := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hT0 : 0 < T := by linarith
  have hU : 0 < T / 4 := by positivity
  rw [xiOrdinateSmoothTerm_eq hT0, integral_Ioc_oneSubCosKernel hU]
  set τ := ∫ x in Ioi (T / 4), oneSubCosKernel x with hτ
  set Λ := ∫ x in Ioc 0 (T / 4), oneSubCosKernel x * Real.log x with hΛ
  set L := Real.log T - Real.log (2 * Real.pi) with hL
  have hτ0 : 0 ≤ τ := setIntegral_nonneg measurableSet_Ioi fun x _ => oneSubCosKernel_nonneg x
  have hτ1 : τ ≤ 8 / T := by
    have := integral_Ioi_oneSubCosKernel_le hU
    rw [show 2 / (T / 4) = 8 / T by field_simp; ring] at this
    exact this
  have hL0 : 0 ≤ L := by
    rw [hL, sub_nonneg]; exact Real.log_le_log (by positivity) hT
  have hLT : L ≤ T := by
    have h1 := Real.log_le_sub_one_of_pos hT0
    have h2 := log_two_pi_pos
    rw [hL]; linarith
  have hΛ : |Λ| ≤ oneSubCosLogMoment := by
    rw [hΛ, oneSubCosLogMoment]
    refine (abs_integral_le_integral_abs).trans ?_
    exact setIntegral_mono_set integrableOn_oneSubCosKernel_mul_log.abs
      (Eventually.of_forall fun _ => abs_nonneg _) Ioc_subset_Ioi_self.eventuallyLE
  have hLog : Real.log T = L + Real.log (2 * Real.pi) := by rw [hL]; ring
  have hexpr : T / Real.pi * (L * (Real.pi / 2 - τ) - Λ) - T / 2 * Real.log T =
      -(T / 2 * Real.log (2 * Real.pi)) - T / Real.pi * L * τ - T / Real.pi * Λ := by
    rw [hLog]; field_simp; ring
  rw [hexpr]
  have hLτ : T / Real.pi * L * τ ≤ 3 * T := by
    have h1 : T / Real.pi * L * τ ≤ T / Real.pi * L * (8 / T) :=
      mul_le_mul_of_nonneg_left hτ1 (by positivity)
    have h2 : T / Real.pi * L * (8 / T) = 8 * L / Real.pi := by field_simp
    rw [h2] at h1
    have h3 : 8 * L / Real.pi ≤ 3 * T := by
      rw [div_le_iff₀ hpi]; nlinarith
    linarith
  have hLτ0 : 0 ≤ T / Real.pi * L * τ := by positivity
  have hΛT : |T / Real.pi * Λ| ≤ T / Real.pi * oneSubCosLogMoment := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < T / Real.pi)]
    exact mul_le_mul_of_nonneg_left hΛ (by positivity)
  have hlp := log_two_pi_pos
  calc |-(T / 2 * Real.log (2 * Real.pi)) - T / Real.pi * L * τ - T / Real.pi * Λ|
      ≤ |T / 2 * Real.log (2 * Real.pi)| + |T / Real.pi * L * τ| + |T / Real.pi * Λ| := by
        have := abs_sub (-(T / 2 * Real.log (2 * Real.pi)) - T / Real.pi * L * τ)
          (T / Real.pi * Λ)
        have := abs_sub (-(T / 2 * Real.log (2 * Real.pi))) (T / Real.pi * L * τ)
        rw [abs_neg] at this
        linarith
    _ ≤ T / 2 * Real.log (2 * Real.pi) + 3 * T + T / Real.pi * oneSubCosLogMoment := by
        rw [abs_of_nonneg (by positivity : 0 ≤ T / 2 * Real.log (2 * Real.pi)),
          abs_of_nonneg hLτ0]
        linarith
    _ = (Real.log (2 * Real.pi) / 2 + 3 + oneSubCosLogMoment / Real.pi) * T := by ring

/-! ## The asymptotic law -/

/-- **Ordinate cosine-mass asymptotic.**  Unconditionally,
`|Σ_q (1 - cos(T/γ_q)) - (T/2) log T| ≤ C T` for every `T ≥ 2π`. -/
theorem exists_abs_xiOrdinateCosineMass_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 * Real.pi ≤ T →
      |xiOrdinateCosineMass T - T / 2 * Real.log T| ≤ C * T := by
  obtain ⟨C₁, hC₁, hE⟩ := exists_abs_xiZeroCount_sub_smooth_le_sqrt
  set K₀ : ℝ := Real.log (2 * Real.pi) / 2 + 3 + oneSubCosLogMoment / Real.pi with hK₀
  have hK₀0 : 0 ≤ K₀ := by
    have := oneSubCosLogMoment_nonneg
    have := log_two_pi_pos
    have := Real.pi_pos
    positivity
  set Q := routeKSmoothRVMCount
  refine ⟨4 * C₁ + K₀ + |Q 4|, by positivity, fun T hT => ?_⟩
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hT0 : 0 < T := by linarith
  have hT4 : 4 ≤ T := by linarith
  set N : ℝ → ℝ := fun y => (xiZeroCount y : ℝ) with hNdef
  set φ : ℝ → ℝ := fun y => 1 - Real.cos (T / y) with hφdef
  set g : ℝ → ℝ := xiCosineWeight T with hgdef
  set J := xiOrdinateSmoothTerm T with hJdef
  have hNmono : Monotone N := fun a b hab => by
    simp only [hNdef]; exact_mod_cast xiZeroCount_mono hab
  -- the window remainder
  set r : ℝ → ℝ := fun Y => (∑ q ∈ xiCopiesBand 0 Y, (1 - Real.cos (T / xiCopyOrdinate q))) -
    T / 2 * Real.log T with hrdef
  set b : ℝ → ℝ := fun Y => |2 * (N Y - Q Y) * φ Y| +
    |2 * (∫ y in (4 : ℝ)..Y, xiSmoothCountDeriv y * φ y) - J| with hbdef
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => one_sub_cos_nonneg _
  have hφ2 : ∀ y, φ y ≤ 2 := fun y => by simp only [hφdef]; linarith [Real.neg_one_le_cos (T / y)]
  -- decomposition on each window
  have hdecomp : ∀ Y, 4 ≤ Y → |r Y| ≤ b Y + 4 * C₁ * T + 4 * |Q 4| + K₀ * T := by
    intro Y hY
    have hwin := xiOrdinateCosine_window_eq T hY
    have hgc : ContinuousOn g (uIcc 4 Y) := by
      rw [uIcc_of_le hY]; exact continuousOn_xiCosineWeight T (by norm_num)
    have hQc : ContinuousOn Q (uIcc 4 Y) := by
      rw [uIcc_of_le hY]
      exact continuousOn_routeKSmoothRVMCount_Ioi.mono fun y hy => by
        simp only [mem_Ioi]; linarith [hy.1]
    have hNint : IntervalIntegrable N volume 4 Y := hNmono.intervalIntegrable
    have hgN : IntervalIntegrable (fun y => N y * g y) volume 4 Y := hNint.mul_continuousOn hgc
    have hgQ : IntervalIntegrable (fun y => g y * Q y) volume 4 Y :=
      (hgc.mul hQc).intervalIntegrable
    -- integration by parts for the smooth count
    have hibp : ∫ y in (4 : ℝ)..Y, g y * Q y =
        Q 4 * φ 4 - Q Y * φ Y + ∫ y in (4 : ℝ)..Y, xiSmoothCountDeriv y * φ y := by
      have hu : ∀ x ∈ uIcc (4 : ℝ) Y, HasDerivAt Q (xiSmoothCountDeriv x) x := by
        intro x hx; rw [uIcc_of_le hY] at hx
        exact hasDerivAt_routeKSmoothRVMCount (by linarith [hx.1])
      have hv : ∀ x ∈ uIcc (4 : ℝ) Y, HasDerivAt φ (-g x) x := by
        intro x hx; rw [uIcc_of_le hY] at hx
        exact hasDerivAt_one_sub_cos_div (by linarith [hx.1])
      have hu' : IntervalIntegrable xiSmoothCountDeriv volume 4 Y := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hY]; exact continuousOn_xiSmoothCountDeriv (by norm_num)
      have hv' : IntervalIntegrable (fun x => -g x) volume 4 Y := hgc.neg.intervalIntegrable
      have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
      have hneg : (∫ y in (4 : ℝ)..Y, Q y * -g y) = -∫ y in (4 : ℝ)..Y, g y * Q y := by
        rw [← intervalIntegral.integral_neg]
        congr 1; funext y; ring
      rw [hneg] at h
      linarith
    -- the remainder integral
    have hEint : |∫ y in (4 : ℝ)..Y, g y * (N y - Q y)| ≤ 2 * C₁ * T := by
      have hbnd : IntervalIntegrable (fun y : ℝ => T * C₁ * y ^ (-3 / 2 : ℝ)) volume 4 Y := by
        apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.mul continuousOn_const
        exact fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inl (by
          rw [uIcc_of_le hY] at hy; linarith [hy.1]))).continuousWithinAt
      have h1 := intervalIntegral.norm_integral_le_of_norm_le hY (f := fun y => g y * (N y - Q y))
        (g := fun y : ℝ => T * C₁ * y ^ (-3 / 2 : ℝ)) (Eventually.of_forall fun y hy => by
          have hy4 : 4 ≤ y := hy.1.le
          have hy0 : 0 < y := by linarith
          rw [Real.norm_eq_abs, abs_mul]
          calc |g y| * |N y - Q y| ≤ T / y ^ 2 * (C₁ * Real.sqrt y) :=
                mul_le_mul (abs_xiCosineWeight_le hT0.le hy0) (hE y hy4) (abs_nonneg _)
                  (by positivity)
            _ = T * C₁ * (Real.sqrt y / y ^ 2) := by ring
            _ = T * C₁ * y ^ (-3 / 2 : ℝ) := by rw [sqrt_div_sq_eq_rpow hy0]) hbnd
      have h2 : (∫ y in (4 : ℝ)..Y, T * C₁ * y ^ (-3 / 2 : ℝ)) ≤ 2 * C₁ * T := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hY]
        have hI : (∫ y in Ioc (4 : ℝ) Y, y ^ (-3 / 2 : ℝ)) ≤ ∫ y in Ioi (4 : ℝ), y ^ (-3 / 2 : ℝ) :=
          setIntegral_mono_set (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num))
            (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
                exact Real.rpow_nonneg (by simp only [mem_Ioi] at hy; linarith) _)
            Ioc_subset_Ioi_self.eventuallyLE
        rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)] at hI
        have h4 : (4 : ℝ) ^ (-3 / 2 + 1 : ℝ) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
        have h4' : 0 ≤ (4 : ℝ) ^ (-3 / 2 + 1 : ℝ) := Real.rpow_nonneg (by norm_num) _
        have hI' : (∫ y in Ioc (4 : ℝ) Y, y ^ (-3 / 2 : ℝ)) ≤ 2 := by
          have : -(4 : ℝ) ^ (-3 / 2 + 1 : ℝ) / (-3 / 2 + 1) = 2 * (4 : ℝ) ^ (-3 / 2 + 1 : ℝ) := by
            norm_num
          rw [this] at hI; linarith
        have hTC : 0 ≤ T * C₁ := by positivity
        nlinarith
      rw [← Real.norm_eq_abs]
      linarith
    have hsplit : (∫ y in (4 : ℝ)..Y, g y * (2 * N y)) =
        2 * (∫ y in (4 : ℝ)..Y, g y * (N y - Q y)) + 2 * ∫ y in (4 : ℝ)..Y, g y * Q y := by
      have hgE : IntervalIntegrable (fun y => g y * (N y - Q y)) volume 4 Y := by
        have := hgN.sub hgQ
        refine this.congr fun y _ => ?_
        ring
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add (hgE.const_mul 2) (hgQ.const_mul 2)]
      congr 1; funext y; ring
    have hrY : r Y = 2 * (N Y - Q Y) * φ Y + 2 * (∫ y in (4 : ℝ)..Y, g y * (N y - Q y)) +
        2 * Q 4 * φ 4 + (2 * (∫ y in (4 : ℝ)..Y, xiSmoothCountDeriv y * φ y) - J) +
        (J - T / 2 * Real.log T) := by
      simp only [hrdef]
      rw [hwin]
      change 2 * N Y * φ Y + (∫ y in (4 : ℝ)..Y, g y * (2 * N y)) - T / 2 * Real.log T = _
      rw [hsplit, hibp]
      ring
    have hJ : |J - T / 2 * Real.log T| ≤ K₀ * T := by
      rw [hJdef, hK₀]; exact abs_xiOrdinateSmoothTerm_sub_le hT
    have hQ4 : |2 * Q 4 * φ 4| ≤ 4 * |Q 4| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hφ0 4), abs_two]
      nlinarith [hφ2 4, hφ0 4, abs_nonneg (Q 4)]
    rw [hrY]
    have habs := abs_add_le (2 * (N Y - Q Y) * φ Y + 2 * (∫ y in (4 : ℝ)..Y, g y * (N y - Q y)) +
        2 * Q 4 * φ 4 + (2 * (∫ y in (4 : ℝ)..Y, xiSmoothCountDeriv y * φ y) - J))
      (J - T / 2 * Real.log T)
    have h3 := abs_add_le (2 * (N Y - Q Y) * φ Y + 2 * (∫ y in (4 : ℝ)..Y, g y * (N y - Q y)) +
        2 * Q 4 * φ 4) (2 * (∫ y in (4 : ℝ)..Y, xiSmoothCountDeriv y * φ y) - J)
    have h4 := abs_add_le (2 * (N Y - Q Y) * φ Y + 2 * (∫ y in (4 : ℝ)..Y, g y * (N y - Q y)))
      (2 * Q 4 * φ 4)
    have h5 := abs_add_le (2 * (N Y - Q Y) * φ Y) (2 * (∫ y in (4 : ℝ)..Y, g y * (N y - Q y)))
    have h6 : |2 * (∫ y in (4 : ℝ)..Y, g y * (N y - Q y))| ≤ 4 * C₁ * T := by
      rw [abs_mul, abs_two]; linarith
    simp only [hbdef]
    linarith
  -- the auxiliary terms vanish
  have hb0 : Tendsto b atTop (𝓝 0) := by
    have h1 : Tendsto (fun Y => |2 * (N Y - Q Y) * φ Y|) atTop (𝓝 0) := by
      have hlim : Tendsto (fun Y : ℝ => C₁ * T ^ 2 * Y ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).const_mul
          (C₁ * T ^ 2)
      refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hlim
      filter_upwards [eventually_ge_atTop (4 : ℝ)] with Y hY
      have hY0 : 0 < Y := by linarith
      have hφY : φ Y ≤ T ^ 2 / (2 * Y ^ 2) := by
        have : 1 - Real.cos (T / Y) ≤ (T / Y) ^ 2 / 2 := by
          linarith [Real.one_sub_sq_div_two_le_cos (x := T / Y)]
        simp only [hφdef]
        rw [div_pow] at this
        calc 1 - Real.cos (T / Y) ≤ T ^ 2 / Y ^ 2 / 2 := this
          _ = T ^ 2 / (2 * Y ^ 2) := by ring
      rw [abs_mul, abs_mul, abs_two, abs_of_nonneg (hφ0 Y)]
      calc 2 * |N Y - Q Y| * φ Y ≤ 2 * (C₁ * Real.sqrt Y) * (T ^ 2 / (2 * Y ^ 2)) := by
            gcongr
            · exact hφ0 Y
            · exact hE Y hY
        _ = C₁ * T ^ 2 * (Real.sqrt Y / Y ^ 2) := by field_simp
        _ = C₁ * T ^ 2 * Y ^ (-(3 / 2 : ℝ)) := by
            rw [sqrt_div_sq_eq_rpow hY0]; norm_num
    have h2 : Tendsto (fun Y => |2 * (∫ y in (4 : ℝ)..Y, xiSmoothCountDeriv y * φ y) - J|)
        atTop (𝓝 0) := by
      have h := (intervalIntegral_tendsto_integral_Ioi 4 (integrableOn_xiSmoothCountDeriv_mul T)
        tendsto_id).const_mul 2
      have h' := (h.sub_const J).abs
      simp only [hJdef, xiOrdinateSmoothTerm, sub_self, abs_zero] at h'
      exact h'
    have h := h1.add h2
    rw [add_zero] at h
    exact h
  have hr : Tendsto r atTop (𝓝 (xiOrdinateCosineMass T - T / 2 * Real.log T)) :=
    (tendsto_xiOrdinateCosine_window T).sub_const _
  have hlim : Tendsto (fun Y => |r Y| - b Y) atTop
      (𝓝 (|xiOrdinateCosineMass T - T / 2 * Real.log T| - 0)) := hr.abs.sub hb0
  rw [sub_zero] at hlim
  have hle : ∀ᶠ Y in atTop, |r Y| - b Y ≤ 4 * C₁ * T + 4 * |Q 4| + K₀ * T :=
    (eventually_ge_atTop 4).mono fun Y hY => by linarith [hdecomp Y hY]
  have hfin := le_of_tendsto hlim hle
  have hQ : 4 * |Q 4| ≤ |Q 4| * T := by nlinarith [abs_nonneg (Q 4)]
  nlinarith

/-- The cosine mass per unit clock is `(1/2) log T + O(1)`. -/
theorem exists_abs_xiOrdinateCosineMass_div_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 * Real.pi ≤ T →
      |xiOrdinateCosineMass T / T - Real.log T / 2| ≤ C := by
  obtain ⟨C, hC, h⟩ := exists_abs_xiOrdinateCosineMass_sub_le
  refine ⟨C, hC, fun T hT => ?_⟩
  have hT0 : 0 < T := by nlinarith [Real.pi_pos]
  have heq : xiOrdinateCosineMass T / T - Real.log T / 2 =
      (xiOrdinateCosineMass T - T / 2 * Real.log T) / T := by field_simp
  rw [heq, abs_div, abs_of_pos hT0, div_le_iff₀ hT0]
  exact h T hT

end RHTower

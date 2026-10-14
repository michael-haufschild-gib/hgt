import GaloisForLFunctions.RHTower.CosDilationKernelMellinInversion
import GaloisForLFunctions.RHTower.CosDilationMediumSupportRigidity
import GaloisForLFunctions.RHTower.CosDilationShortSupportRigidity
import GaloisForLFunctions.RHTower.BoundedSupportFourierUncertainty

/-!
# Doubly blind cores: the pole term is a distance to cosine self-duality

Let `f` be smooth and supported in `[α, β]`, `0 < α ≤ β`, with dilation autocorrelation
`A_f(r) = ∫_0^∞ f(y) f(ry) dy`, half-line cosine transform `Cf`, cosine–dilation kernel
`Ψ_f(x) = ∫_0^∞ f(y) Cf(x/y) dy/y`, and inverted cosine transform `JCf(y) = Cf(1/y)/y`
(`invertedCosTransform`).  Call `f` *doubly blind* if `A_f(n) = 0` and `Ψ_f(n) = 0` for every
integer `|n| ≥ 2`: the multiplicative autocorrelation vanishes at the integers `n ≥ 2`, and so does
its Fourier transform.

**Theorem** (`cosDilationKernel_zero_eq_integral_sq_sub_inverted`).  For a doubly blind core,
`Ψ_f(0) = ∫_0^∞ (f(y) − JCf(y))² dy`.  Since `Ψ_f(0) = Cf(0) ∫_0^∞ f(y)/y dy` is the pole term of
the associated Weil test, the pole term of a doubly blind test is the squared distance of `f` from
its inverted cosine transform.

**Corollary** (`eq_zero_of_doublyBlind_of_integral_eq_zero`).  A doubly blind core with
`∫_0^∞ f = 0` vanishes identically.

Proof.  Poisson periodization at `x = 0` (`tsum_dilationAutocorr_abs_eq`) gives
`2A_f(1) = Ψ_f(0) + 2Ψ_f(1)`.  Plancherel for the even extension gives `∫_0^∞ (Cf)² = ∫_0^∞ f²`, and
the substitution `w = 1/y` gives `∫_0^∞ (JCf)² = ∫_0^∞ (Cf)²`.  As `A_f(1) = ∫ f²` and
`Ψ_f(1) = ∫ f · JCf`, expanding the square gives the identity.  If the pole vanishes, `JCf = f` on
`(0, ∞)`, so `Cf(w) = w f(1/w) = 0` for `w > 1/α`.  A compactly supported function whose Fourier
transform vanishes on an interval has vanishing Fourier transform
(`fourier_eq_zero_of_ae_zero_on_Ioo`), so `Cf = 0` and `f = JCf = 0`.
-/

open MeasureTheory Set Real Complex
open scoped FourierTransform ContDiff SchwartzMap

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ}

/-- The inverted cosine transform `JCf(y) = Cf(1/y)/y`. -/
def invertedCosTransform (f : ℝ → ℝ) (y : ℝ) : ℝ := halfLineCosTransform f y⁻¹ / y

theorem halfLineCosTransform_neg (f : ℝ → ℝ) (w : ℝ) :
    halfLineCosTransform f (-w) = halfLineCosTransform f w := by
  have h : ∀ z : ℝ, Real.cos (2 * π * (z * -w)) = Real.cos (2 * π * (z * w)) := fun z => by
    rw [show 2 * π * (z * -w) = -(2 * π * (z * w)) by ring, Real.cos_neg]
  simp only [halfLineCosTransform, h]

theorem eq_zero_of_not_mem_Icc {α β : ℝ} (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {y : ℝ}
    (hy : y ∉ Icc α β) : f y = 0 := by
  by_contra h
  exact hy (hsupp y h)

/-- The cosine transform squared, as the norm square of the Fourier transform of the even
extension. -/
theorem norm_fourier_halfLineEvenExtSchwartz_sq (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (w : ℝ) :
    ‖(𝓕 (halfLineEvenExtSchwartz hf hsupp) : 𝓢(ℝ, ℂ)) w‖ ^ 2 = halfLineCosTransform f w ^ 2 := by
  rw [← congrFun (halfLineCosTransform_eq_fourier hf hα hsupp) w, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

theorem integrable_halfLineCosTransform_sq (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    Integrable fun w => halfLineCosTransform f w ^ 2 := by
  set F : 𝓢(ℝ, ℂ) := 𝓕 (halfLineEvenExtSchwartz hf hsupp)
  have h := (F.memLp (2 : ℕ) volume).integrable_norm_pow (by norm_num)
  exact h.congr (Filter.Eventually.of_forall fun w =>
    norm_fourier_halfLineEvenExtSchwartz_sq hf hα hsupp w)

/-- **Plancherel on the half-line**: `∫_0^∞ (Cf)² = ∫_0^∞ f²`. -/
theorem integral_Ioi_halfLineCosTransform_sq (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ∫ w in Ioi 0, halfLineCosTransform f w ^ 2 = ∫ y in Ioi 0, f y ^ 2 := by
  have hP := SchwartzMap.integral_norm_sq_fourier (halfLineEvenExtSchwartz hf hsupp)
  simp only [norm_fourier_halfLineEvenExtSchwartz_sq hf hα hsupp, halfLineEvenExtSchwartz_apply,
    halfLineEvenExt, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hP
  have hcross : ∀ t, f t * f (-t) = 0 := fun t => by
    by_cases ht : f t = 0
    · rw [ht, zero_mul]
    · have h1 := (hsupp t ht).1
      have : f (-t) = 0 := eq_zero_of_not_mem_Icc hsupp fun h => by linarith [h.1]
      rw [this, mul_zero]
  have hsq : ∀ t, (f t + f (-t)) ^ 2 = f t ^ 2 + f (-t) ^ 2 := fun t => by
    have := hcross t
    nlinarith
  simp only [hsq] at hP
  have hcont : Continuous f := hf.continuous
  have hi1 : Integrable fun t => f t ^ 2 :=
    ((hcont.pow 2).continuousOn.integrableOn_compact isCompact_Icc
      ).integrable_of_forall_notMem_eq_zero (s := Icc α β) fun t ht => by
        simp [eq_zero_of_not_mem_Icc hsupp ht]
  have hi2 : Integrable fun t => f (-t) ^ 2 := hi1.comp_neg
  rw [integral_add hi1 hi2, integral_neg_eq_self (fun t => f t ^ 2)] at hP
  have heven : (∫ w, halfLineCosTransform f w ^ 2) =
      2 * ∫ w in Ioi 0, halfLineCosTransform f w ^ 2 := by
    rw [← integral_comp_abs (f := fun w => halfLineCosTransform f w ^ 2)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    rcases le_total 0 w with h | h
    · simp [abs_of_nonneg h]
    · simp [abs_of_nonpos h, halfLineCosTransform_neg]
  have hf0 : (∫ y in Ioi 0, f y ^ 2) = ∫ y, f y ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      rw [eq_zero_of_not_mem_Icc hsupp fun h => hy (lt_of_lt_of_le hα h.1)]
      ring
  rw [heven] at hP
  rw [hf0]
  linarith

theorem integrableOn_halfLineCosTransform_sq (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    IntegrableOn (fun w => halfLineCosTransform f w ^ 2) (Ioi 0) :=
  (integrable_halfLineCosTransform_sq hf hα hsupp).integrableOn

theorem inverted_sq_eq_smul (y : ℝ) (hy : 0 < y) :
    invertedCosTransform f y ^ 2 =
      (|(-1 : ℝ)| * y ^ ((-1 : ℝ) - 1)) • halfLineCosTransform f (y ^ (-1 : ℝ)) ^ 2 := by
  rw [invertedCosTransform, smul_eq_mul, Real.rpow_neg_one, abs_neg, abs_one, one_mul,
    show (-1 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg hy.le, div_pow]
  rw [show (y : ℝ) ^ (2 : ℝ) = y ^ (2 : ℕ) by norm_cast]
  field_simp

/-- **Inversion is unitary**: `∫_0^∞ (JCf)² = ∫_0^∞ (Cf)²`. -/
theorem integral_Ioi_invertedCosTransform_sq (f : ℝ → ℝ) :
    ∫ y in Ioi 0, invertedCosTransform f y ^ 2 = ∫ w in Ioi 0, halfLineCosTransform f w ^ 2 := by
  rw [← integral_comp_rpow_Ioi (fun w => halfLineCosTransform f w ^ 2)
    (by norm_num : (-1 : ℝ) ≠ 0)]
  exact setIntegral_congr_fun measurableSet_Ioi fun y hy => inverted_sq_eq_smul y hy

theorem integrableOn_invertedCosTransform_sq (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    IntegrableOn (fun y => invertedCosTransform f y ^ 2) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_rpow_iff (fun w => halfLineCosTransform f w ^ 2)
    (by norm_num : (-1 : ℝ) ≠ 0)).mpr (integrableOn_halfLineCosTransform_sq hf hα hsupp)
  exact h.congr_fun (fun y hy => (inverted_sq_eq_smul y hy).symm) measurableSet_Ioi

theorem continuousOn_invertedCosTransform (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ContinuousOn (invertedCosTransform f) (Ioi 0) := by
  have hC : Continuous fun w => halfLineCosTransform f w := by
    have h := continuous_halfLineCosTransform hf hα hsupp
    exact Complex.continuous_re.comp h |>.congr fun w => by simp
  intro y hy
  have hy0 : y ≠ 0 := (ne_of_lt hy).symm
  exact ((hC.continuousAt.comp (continuousAt_inv₀ hy0)).div continuousAt_id hy0).continuousWithinAt

theorem integrableOn_mul_invertedCosTransform (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    IntegrableOn (fun y => f y * invertedCosTransform f y) (Ioi 0) := by
  have hsub : Icc α β ⊆ Ioi 0 := fun y hy => lt_of_lt_of_le hα hy.1
  have hcont : ContinuousOn (fun y => f y * invertedCosTransform f y) (Icc α β) :=
    hf.continuous.continuousOn.mul ((continuousOn_invertedCosTransform hf hα hsupp).mono hsub)
  refine (hcont.integrableOn_compact isCompact_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi
    fun y hy => ?_
  rw [eq_zero_of_not_mem_Icc hsupp hy.2, zero_mul]

theorem integrableOn_sq_of_support (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    IntegrableOn (fun y => f y ^ 2) (Ioi 0) :=
  ((hf.continuous.pow 2).continuousOn.integrableOn_compact (isCompact_Icc (a := α) (b := β))
    ).of_forall_sdiff_eq_zero measurableSet_Ioi fun y (hy : y ∈ Ioi 0 \ Icc α β) => by
      simp [eq_zero_of_not_mem_Icc hsupp hy.2]

theorem cosDilationKernel_one_eq_integral_mul_inverted (f : ℝ → ℝ) :
    cosDilationKernel f 1 = ∫ y in Ioi 0, f y * invertedCosTransform f y := by
  unfold cosDilationKernel invertedCosTransform
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [one_div, mul_div_assoc]

theorem dilationAutocorr_one_eq_setIntegral_sq (f : ℝ → ℝ) :
    dilationAutocorr f 1 = ∫ y in Ioi 0, f y ^ 2 := by
  unfold dilationAutocorr
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [one_mul, sq]

/-- **Periodization at the origin**: for a doubly blind core, `2A_f(1) = Ψ_f(0) + 2Ψ_f(1)`. -/
theorem two_mul_dilationAutocorr_one_eq_of_doublyBlind (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hA : ∀ n : ℕ, 2 ≤ n → dilationAutocorr f n = 0)
    (hΨ : ∀ n : ℤ, 2 ≤ |n| → cosDilationKernel f n = 0) :
    2 * dilationAutocorr f 1 = cosDilationKernel f 0 + 2 * cosDilationKernel f 1 := by
  have hP := tsum_dilationAutocorr_abs_eq hf.continuous hα hαβ hsupp hΨ 0
  have hf0 : f 0 = 0 := eq_zero_of_not_mem_Icc hsupp fun h => by linarith [h.1]
  have hA0 : dilationAutocorr f 0 = 0 := by
    unfold dilationAutocorr
    simp [hf0]
  have hval : ∀ k : ℤ, k ∉ ({-1, 1} : Finset ℤ) →
      ((dilationAutocorr f |(0 : ℝ) + (k : ℝ)| : ℝ) : ℂ) = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [zero_add]
    rcases eq_or_ne k 0 with rfl | hk0
    · simp [hA0]
    · have habs : |(k : ℝ)| = ((k.natAbs : ℕ) : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [habs, hA k.natAbs (by omega), Complex.ofReal_zero]
  rw [tsum_eq_sum (s := ({-1, 1} : Finset ℤ)) hval, Finset.sum_pair (by norm_num)] at hP
  simp only [zero_add, Int.cast_neg, Int.cast_one, abs_neg, abs_one, mul_zero, Real.cos_zero,
    mul_one] at hP
  have hR : dilationAutocorr f 1 + dilationAutocorr f 1 =
      cosDilationKernel f 0 + 2 * cosDilationKernel f 1 := by exact_mod_cast hP
  linarith

/-- **The pole term of a doubly blind core is a squared distance**:
`Ψ_f(0) = ∫_0^∞ (f(y) − JCf(y))² dy`. -/
theorem cosDilationKernel_zero_eq_integral_sq_sub_inverted (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hA : ∀ n : ℕ, 2 ≤ n → dilationAutocorr f n = 0)
    (hΨ : ∀ n : ℤ, 2 ≤ |n| → cosDilationKernel f n = 0) :
    cosDilationKernel f 0 = ∫ y in Ioi 0, (f y - invertedCosTransform f y) ^ 2 := by
  have h1 := integrableOn_sq_of_support hf hsupp
  have h2 := integrableOn_mul_invertedCosTransform hf hα hsupp
  have h3 := integrableOn_invertedCosTransform_sq hf hα hsupp
  have hexp : ∀ y, (f y - invertedCosTransform f y) ^ 2 =
      f y ^ 2 - 2 * (f y * invertedCosTransform f y) + invertedCosTransform f y ^ 2 :=
    fun y => by ring
  have h12 : IntegrableOn (fun y => f y ^ 2 - 2 * (f y * invertedCosTransform f y)) (Ioi 0) :=
    h1.sub (h2.const_mul 2)
  have h2' : IntegrableOn (fun y => 2 * (f y * invertedCosTransform f y)) (Ioi 0) := h2.const_mul 2
  simp only [hexp]
  rw [integral_add h12 h3, integral_sub h1 h2',
    integral_const_mul, ← cosDilationKernel_one_eq_integral_mul_inverted,
    integral_Ioi_invertedCosTransform_sq, integral_Ioi_halfLineCosTransform_sq hf hα hsupp,
    ← dilationAutocorr_one_eq_setIntegral_sq]
  linarith [two_mul_dilationAutocorr_one_eq_of_doublyBlind hf hα hαβ hsupp hA hΨ]

/-- The pole term of a doubly blind core is nonnegative. -/
theorem cosDilationKernel_zero_nonneg_of_doublyBlind (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hA : ∀ n : ℕ, 2 ≤ n → dilationAutocorr f n = 0)
    (hΨ : ∀ n : ℤ, 2 ≤ |n| → cosDilationKernel f n = 0) :
    0 ≤ cosDilationKernel f 0 := by
  rw [cosDilationKernel_zero_eq_integral_sq_sub_inverted hf hα hαβ hsupp hA hΨ]
  exact setIntegral_nonneg measurableSet_Ioi fun y _ => sq_nonneg _

/-- **Doubly blind cores with vanishing pole term are zero.**  If `Ψ_f(0) = 0` (for instance
`∫_0^∞ f = 0`), a doubly blind core vanishes identically. -/
theorem eq_zero_of_doublyBlind_of_cosDilationKernel_zero (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hA : ∀ n : ℕ, 2 ≤ n → dilationAutocorr f n = 0)
    (hΨ : ∀ n : ℤ, 2 ≤ |n| → cosDilationKernel f n = 0) (h0 : cosDilationKernel f 0 = 0)
    (y : ℝ) : f y = 0 := by
  have hid := cosDilationKernel_zero_eq_integral_sq_sub_inverted hf hα hαβ hsupp hA hΨ
  rw [h0] at hid
  have hint : IntegrableOn (fun y => (f y - invertedCosTransform f y) ^ 2) (Ioi 0) := by
    have h1 := integrableOn_sq_of_support hf hsupp
    have h2 := integrableOn_mul_invertedCosTransform hf hα hsupp
    have h3 := integrableOn_invertedCosTransform_sq hf hα hsupp
    refine ((h1.sub (h2.const_mul 2)).add h3).congr_fun (fun y _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun y => sq_nonneg _) hint).mp hid.symm
  have hae' : f =ᵐ[volume.restrict (Ioi 0)] invertedCosTransform f := by
    filter_upwards [hae] with y hy
    have : (f y - invertedCosTransform f y) ^ 2 = 0 := hy
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
  have hEq : EqOn f (invertedCosTransform f) (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq hae' isOpen_Ioi hf.continuous.continuousOn
      (continuousOn_invertedCosTransform hf hα hsupp)
  -- the cosine transform vanishes beyond `1/α`
  have hCvan : ∀ w, α⁻¹ < w → halfLineCosTransform f w = 0 := by
    intro w hw
    have hw0 : 0 < w := lt_trans (inv_pos.mpr hα) hw
    have hwi : w⁻¹ < α := by
      rw [inv_lt_comm₀ hw0 hα]
      exact hw
    have h := hEq (show w⁻¹ ∈ Ioi 0 from inv_pos.mpr hw0)
    rw [eq_zero_of_not_mem_Icc hsupp fun h' => by linarith [h'.1], invertedCosTransform,
      inv_inv] at h
    have hw0' : w⁻¹ ≠ 0 := inv_ne_zero hw0.ne'
    rcases div_eq_zero_iff.mp h.symm with h' | h'
    · exact h'
    · exact absurd h' hw0'
  have hE : Integrable (halfLineEvenExt f) := (halfLineEvenExtSchwartz hf hsupp).integrable
  have hEsupp : ∀ᵐ x ∂volume, x ∉ Icc (-β) β → halfLineEvenExt f x = 0 := by
    refine Filter.Eventually.of_forall fun x hx => ?_
    have h1 : f x = 0 := eq_zero_of_not_mem_Icc hsupp fun h => hx ⟨by linarith [h.1], h.2⟩
    have h2 : f (-x) = 0 := eq_zero_of_not_mem_Icc hsupp fun h =>
      hx ⟨by linarith [h.2], by linarith [h.1]⟩
    simp [halfLineEvenExt, h1, h2]
  have hFzero := fourier_eq_zero_of_ae_zero_on_Ioo hE hEsupp
    (show α⁻¹ < α⁻¹ + 1 by linarith)
    (Filter.Eventually.of_forall fun w hw => by
      rw [fourier_halfLineEvenExt hf hα hsupp w, hCvan w hw.1, Complex.ofReal_zero])
  have hCzero : ∀ w, halfLineCosTransform f w = 0 := fun w => by
    have := hFzero w
    rw [fourier_halfLineEvenExt hf hα hsupp w] at this
    exact_mod_cast this
  rcases lt_or_ge 0 y with hy | hy
  · rw [hEq hy, invertedCosTransform, hCzero, zero_div]
  · exact eq_zero_of_not_mem_Icc hsupp fun h => by linarith [h.1]

/-- **Mean-zero doubly blind cores are zero.** -/
theorem eq_zero_of_doublyBlind_of_integral_eq_zero (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hA : ∀ n : ℕ, 2 ≤ n → dilationAutocorr f n = 0)
    (hΨ : ∀ n : ℤ, 2 ≤ |n| → cosDilationKernel f n = 0) (h0 : ∫ y in Ioi (0 : ℝ), f y = 0)
    (y : ℝ) : f y = 0 :=
  eq_zero_of_doublyBlind_of_cosDilationKernel_zero hf hα hαβ hsupp hA hΨ
    (cosDilationKernel_zero_of_integral_eq_zero h0) y

end

end RHTower

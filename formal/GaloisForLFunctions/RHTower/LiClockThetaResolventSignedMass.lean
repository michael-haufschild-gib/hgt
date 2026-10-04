import GaloisForLFunctions.RHTower.LiClockThetaResolventSignChange
import GaloisForLFunctions.RHTower.ProfileRenewalLogKernel
import GaloisForLFunctions.RHTower.XiReciprocalTranslationSeamNormLaw
import GaloisForLFunctions.RHTower.XiHeatShellMinimum
import GaloisForLFunctions.HTGeometry.QuasiPolynomialLaplaceCalculus

/-!
# The exact signed-mass threshold of the theta resolvent

Let `β = sup_q |Im α_q⁻¹|`.  Square summability of the reciprocal frequencies makes the supremum a
maximum, `0 ≤ β < 1/300`, and `β = 0` exactly under the Riemann hypothesis.  The zeros of
`Φ(1/p)` are `p = ∓i α_q⁻¹`, so some reciprocal zero `p₀ ≠ 0` lies on the line `Re p = β`.

For every `p > β` the contour growth of `r = -u''` gives `∫_0^∞ e^{-pt}|r| < ∞`, and the complex
Laplace transform `H(z) = ∫_0^∞ e^{-zt} r(t) dt` satisfies the undivided identity
`(1 - H(z)) Φ(1/z) = 1` on `Re z > β` (convolution theorem and `K̂ = Φ(1/z) - 1`).  If
`∫_0^∞ e^{-βt}|r|` were finite, `H` would stay bounded near `p₀` while `Φ(1/z) → 0`, contradicting
the identity.  Hence `e^{-pt}|r|` is integrable exactly when `p > β`.

Writing `r = r₊ - r₋`, the causal equation gives `r₊ + r₊ ⋆ K = K + r₋ + r₋ ⋆ K`, so for `p > 0`
each weighted signed part is integrable exactly when the other is; for `p ≤ 0` a finite signed mass
would bound every weighted mass of the other part and make `r` ordinarily integrable.  Therefore
`e^{-pt} r₊` and `e^{-pt} r₋` are integrable exactly when `p > β`, both ordinary signed masses are
infinite, and both signs of `r` occur at arbitrarily large clocks.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The threshold -/

theorem exists_isMax_abs_im_inv_xiSpectralPoint :
    ∃ q₀ : XiZeroCopy, ∀ q : XiZeroCopy,
      |((xiSpectralPoint q)⁻¹).im| ≤ |((xiSpectralPoint q₀)⁻¹).im| := by
  by_cases hall : ∀ q : XiZeroCopy, ((xiSpectralPoint q)⁻¹).im = 0
  · obtain ⟨q₁⟩ := nonempty_xiZeroCopy
    exact ⟨q₁, fun q => by rw [hall q, hall q₁]⟩
  · simp only [not_forall] at hall
    obtain ⟨q₁, hq₁⟩ := hall
    set a := |((xiSpectralPoint q₁)⁻¹).im|
    have ha : 0 < a := abs_pos.2 hq₁
    have hev : ∀ᶠ q in cofinite, ‖(xiSpectralPoint q)⁻¹‖ ^ (2 : ℕ) < a ^ 2 :=
      summable_norm_inv_xiSpectralPoint_sq.tendsto_cofinite_zero.eventually_lt_const (by positivity)
    have hfin := Filter.eventually_cofinite.1 hev
    have hmem : q₁ ∈ hfin.toFinset := by
      refine hfin.mem_toFinset.2 ?_
      simp only [mem_setOf_eq, not_lt]
      exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2
    obtain ⟨q₀, -, hmax⟩ := hfin.toFinset.exists_max_image
      (fun q => |((xiSpectralPoint q)⁻¹).im|) ⟨q₁, hmem⟩
    refine ⟨q₀, fun q => ?_⟩
    by_cases hq : q ∈ hfin.toFinset
    · exact hmax q hq
    · have hq' : ‖(xiSpectralPoint q)⁻¹‖ ^ (2 : ℕ) < a ^ 2 := by
        by_contra h
        exact hq (hfin.mem_toFinset.2 h)
      have hw : ‖(xiSpectralPoint q)⁻¹‖ < a := by nlinarith [norm_nonneg (xiSpectralPoint q)⁻¹]
      exact ((Complex.abs_im_le_norm _).trans hw.le).trans (hmax q₁ hmem)

/-- The signed-mass threshold `β = sup_q |Im α_q⁻¹|`. -/
def liClockThetaResolventThreshold : ℝ := ⨆ q : XiZeroCopy, |((xiSpectralPoint q)⁻¹).im|

/-- **The threshold is attained.** -/
theorem liClockThetaResolventThreshold_spec :
    ∃ q₀ : XiZeroCopy, liClockThetaResolventThreshold = |((xiSpectralPoint q₀)⁻¹).im| ∧
      ∀ q : XiZeroCopy, |((xiSpectralPoint q)⁻¹).im| ≤ liClockThetaResolventThreshold := by
  obtain ⟨q₀, h⟩ := exists_isMax_abs_im_inv_xiSpectralPoint
  have hbdd : BddAbove (Set.range fun q : XiZeroCopy => |((xiSpectralPoint q)⁻¹).im|) :=
    ⟨_, Set.forall_mem_range.2 h⟩
  have heq : liClockThetaResolventThreshold = |((xiSpectralPoint q₀)⁻¹).im| :=
    le_antisymm (ciSup_le h) (le_ciSup hbdd q₀)
  exact ⟨q₀, heq, fun q => heq ▸ h q⟩

theorem abs_im_inv_xiSpectralPoint_le_threshold (q : XiZeroCopy) :
    |((xiSpectralPoint q)⁻¹).im| ≤ liClockThetaResolventThreshold :=
  liClockThetaResolventThreshold_spec.choose_spec.2 q

theorem liClockThetaResolventThreshold_nonneg : 0 ≤ liClockThetaResolventThreshold := by
  obtain ⟨q₀, h, -⟩ := liClockThetaResolventThreshold_spec
  rw [h]; exact abs_nonneg _

theorem liClockThetaResolventThreshold_lt : liClockThetaResolventThreshold < 1 / 300 := by
  obtain ⟨q₀, h, -⟩ := liClockThetaResolventThreshold_spec
  rw [h]; exact abs_im_inv_xiSpectralPoint_lt_one_div_threeHundred q₀

/-- **`β = 0` is the Riemann hypothesis.** -/
theorem liClockThetaResolventThreshold_eq_zero_iff :
    liClockThetaResolventThreshold = 0 ↔ RiemannHypothesis := by
  rw [xiSpectralPoint_im_eq_zero_iff_rh]
  have him : ∀ q : XiZeroCopy, ((xiSpectralPoint q)⁻¹).im = 0 ↔ (xiSpectralPoint q).im = 0 := by
    intro q
    have hn : Complex.normSq (xiSpectralPoint q) ≠ 0 :=
      (Complex.normSq_pos.2 (xiSpectralPoint_ne_zero' q)).ne'
    rw [Complex.inv_im, div_eq_zero_iff, neg_eq_zero, or_iff_left hn]
  constructor
  · intro h q
    rw [← him]
    have := abs_im_inv_xiSpectralPoint_le_threshold q
    rw [h] at this
    exact abs_nonpos_iff.1 this
  · intro h
    obtain ⟨q₀, hq₀, -⟩ := liClockThetaResolventThreshold_spec
    rw [hq₀, (him q₀).2 (h q₀), abs_zero]

theorem liClockThetaResolventThreshold_pos_of_not_rh (h : ¬ RiemannHypothesis) :
    0 < liClockThetaResolventThreshold :=
  lt_of_le_of_ne liClockThetaResolventThreshold_nonneg fun h0 =>
    h (liClockThetaResolventThreshold_eq_zero_iff.1 h0.symm)

theorem liClockThetaGenerator_neg (z : ℂ) : liClockThetaGenerator (-z) = liClockThetaGenerator z := by
  unfold liClockThetaGenerator
  exact tsum_congr fun j => by rw [Even.neg_pow ⟨j, by ring⟩]

/-- **A reciprocal zero on the threshold line.** -/
theorem exists_liClockThetaGenerator_inv_eq_zero_re_eq_threshold :
    ∃ p₀ : ℂ, p₀ ≠ 0 ∧ p₀.re = liClockThetaResolventThreshold ∧
      liClockThetaGenerator p₀⁻¹ = 0 := by
  obtain ⟨q₀, hq₀, -⟩ := liClockThetaResolventThreshold_spec
  set α := xiSpectralPoint q₀
  have hα : α ≠ 0 := xiSpectralPoint_ne_zero' q₀
  have hΦ : liClockThetaGenerator (Complex.I * α) = 0 := by
    rw [liClockThetaGenerator_eq_XiC, show -Complex.I * (Complex.I * α) = α by
      rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]]
    rw [XiC_xiSpectralPoint_eq_zero q₀, zero_div]
  rcases le_total 0 (α⁻¹).im with h | h
  · refine ⟨-Complex.I * α⁻¹, by simp [hα], ?_, ?_⟩
    · rw [hq₀, abs_of_nonneg h]; simp
    · rw [mul_inv, inv_inv, inv_neg, Complex.inv_I, neg_neg]; exact hΦ
  · refine ⟨Complex.I * α⁻¹, by simp [hα], ?_, ?_⟩
    · rw [hq₀, abs_of_nonpos h]; simp
    · rw [mul_inv, inv_inv, Complex.inv_I, ← liClockThetaGenerator_neg, neg_mul, neg_neg]
      exact hΦ

/-! ## Integrability above the threshold -/

/-- **Upper admission.**  `∫_0^∞ e^{-pt}|r(t)| dt < ∞` for every `p > β`. -/
theorem integrableOn_exp_mul_abs_liClockThetaResolvent {p : ℝ}
    (hp : liClockThetaResolventThreshold < p) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * |liClockThetaResolvent t|) (Ioi 0) := by
  have hβ0 := liClockThetaResolventThreshold_nonneg
  have hβ := liClockThetaResolventThreshold_lt
  set δ := min ((liClockThetaResolventThreshold + p) / 2) 1
  have hβδ : liClockThetaResolventThreshold < δ := lt_min (by linarith) (by linarith)
  have hδp : δ < p := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨C, hC⟩ := exists_abs_iteratedDeriv_liClockThetaCausalInverse_le hβ0
    abs_im_inv_xiSpectralPoint_le_threshold hβδ ((min_le_right _ _).trans (by norm_num)) 2
  have hg : IntegrableOn (fun t => C * Real.exp (-(p - δ) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul C
  refine hg.mono' ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(p * t))).mul
    continuous_liClockThetaResolvent.abs).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  have hr : |liClockThetaResolvent t| ≤ C * Real.exp (δ * |t|) := by
    have := hC t
    rwa [iteratedDeriv_two_liClockThetaCausalInverse, abs_neg] at this
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_abs]
  calc Real.exp (-(p * t)) * |liClockThetaResolvent t| ≤
      Real.exp (-(p * t)) * (C * Real.exp (δ * |t|)) :=
        mul_le_mul_of_nonneg_left hr (Real.exp_pos _).le
    _ = C * Real.exp (-(p - δ) * t) := by
        rw [abs_of_pos ht', mul_left_comm, ← Real.exp_add]; ring_nf

/-- **Growth at every rate above the threshold.**  For every `δ > β` and every `m`,
`|r^{(m)}(t)| ≤ C e^{δ|t|}` at every real clock. -/
theorem exists_abs_iteratedDeriv_liClockThetaResolvent_le {δ : ℝ}
    (hδ : liClockThetaResolventThreshold < δ) (m : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, |iteratedDeriv m liClockThetaResolvent t| ≤ C * Real.exp (δ * |t|) := by
  have hβ0 := liClockThetaResolventThreshold_nonneg
  have hβ := liClockThetaResolventThreshold_lt
  obtain ⟨C, hC⟩ := exists_abs_iteratedDeriv_liClockThetaCausalInverse_le hβ0
    abs_im_inv_xiSpectralPoint_le_threshold (lt_min hδ (by linarith) : _ < min δ 1)
    ((min_le_right _ _).trans (by norm_num)) (m + 2)
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans (hC 0)
    simpa using this
  refine ⟨C, fun t => ?_⟩
  rw [iteratedDeriv_liClockThetaResolvent, abs_neg]
  refine (hC t).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0)
  exact mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)

/-! ## The complex Laplace identity -/

/-- The complex Laplace transform of `r`. -/
def liClockThetaResolventLaplace (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * t)) * (liClockThetaResolvent t : ℂ)

private theorem integrableOn_cexp_mul_of_real {f : ℝ → ℝ} (hf : Continuous f) {z : ℂ}
    (h : IntegrableOn (fun t : ℝ => Real.exp (-(z.re * t)) * |f t|) (Ioi 0)) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(z * t)) * (f t : ℂ)) (Ioi 0) := by
  refine h.mono' ((by fun_prop : Continuous fun t : ℝ => Complex.exp (-(z * t))).mul
    (Complex.continuous_ofReal.comp hf)).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => ?_
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  simp

/-- `K̂(z) = Φ(1/z) - 1` for every complex `z` with `Re z > 0`. -/
theorem integral_Ioi_cexp_mul_liClockThetaKernel {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * t)) * (liClockThetaKernel t : ℂ) =
      liClockThetaGenerator z⁻¹ - 1 := by
  set F : ℕ → ℝ → ℂ := fun k t => (liClockThetaGeneratorCoeff (k + 1) : ℂ) *
    ((t : ℂ) ^ (2 * k + 1) * Complex.exp (-(z * t)) / ((2 * k + 1).factorial : ℂ)) with hFdef
  have hint : ∀ k, Integrable (F k) (volume.restrict (Ioi 0)) := fun k =>
    ((QuasiPolynomial.integrableOn_pow_mul_cexp (2 * k + 1) hz).div_const _).const_mul _
  have hnorm : ∀ k, ∫ t in Ioi (0 : ℝ), ‖F k t‖ =
      liClockThetaGeneratorCoeff (k + 1) * ((z.re) ^ (2 * k + 2))⁻¹ := by
    intro k
    rw [← integral_Ioi_dividedPowerFn_mul_exp_neg (2 * k + 1) hz, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) ≤ t := le_of_lt ht
    simp only [hFdef, norm_mul, norm_div, Complex.norm_real, Complex.norm_natCast, norm_pow,
      Complex.norm_exp, Real.norm_eq_abs, abs_of_pos (liClockThetaGeneratorCoeff_pos _),
      abs_of_nonneg ht', dividedPowerFn]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    ring
  have hsum : Summable fun k => ∫ t in Ioi (0 : ℝ), ‖F k t‖ := by
    simp_rw [hnorm]
    exact (hasSum_integral_Ioi_liClockThetaKernel_mul_exp_neg hz).summable
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hval : ∀ k, ∫ t in Ioi (0 : ℝ), F k t =
      (liClockThetaGeneratorCoeff (k + 1) : ℂ) * (z⁻¹) ^ (2 * k + 2) := by
    intro k
    simp only [hFdef]
    rw [integral_const_mul, integral_div, QuasiPolynomial.integral_pow_mul_cexp (2 * k + 1) hz]
    have hf : ((2 * k + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [inv_pow, show 2 * k + 1 + 1 = 2 * k + 2 by ring]
    field_simp
  have hfun : (fun t : ℝ => ∑' k, F k t) =
      fun t : ℝ => Complex.exp (-(z * t)) * (liClockThetaKernel t : ℂ) := by
    funext t
    unfold liClockThetaKernel oddFactorialSeries
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    simp only [hFdef]
    push_cast
    ring
  simp_rw [hval] at h
  rw [hfun] at h
  rw [← h.tsum_eq]
  unfold liClockThetaGenerator
  have hs : Summable fun j : ℕ => (liClockThetaGeneratorCoeff j : ℂ) * z⁻¹ ^ (2 * j) :=
    (summable_norm_liClockThetaGeneratorTerm z⁻¹).of_norm
  rw [hs.tsum_eq_zero_add]
  simp only [liClockThetaGeneratorCoeff_zero, Complex.ofReal_one, mul_zero, pow_zero, mul_one]
  rw [add_sub_cancel_left]
  exact tsum_congr fun k => by rw [show 2 * (k + 1) = 2 * k + 2 by ring]

/-- **Undivided Laplace identity.**  `(1 - H(z)) Φ(1/z) = 1` for every `Re z > β`. -/
theorem one_sub_liClockThetaResolventLaplace_mul {z : ℂ}
    (hz : liClockThetaResolventThreshold < z.re) :
    (1 - liClockThetaResolventLaplace z) * liClockThetaGenerator z⁻¹ = 1 := by
  have hz0 : 0 < z.re := liClockThetaResolventThreshold_nonneg.trans_lt hz
  have hfi := integrableOn_exp_mul_abs_liClockThetaResolvent hz
  have hKi : IntegrableOn (fun t : ℝ => Real.exp (-(z.re * t)) * |liClockThetaKernel t|) (Ioi 0) :=
    (integrableOn_liClockThetaKernel_mul_exp_neg hz0).congr_fun (fun t ht => by
      rw [abs_of_nonneg (liClockThetaKernel_nonneg (le_of_lt ht)), mul_comm]) measurableSet_Ioi
  have hconv := integral_Ioi_cexp_mul_volterraConv continuous_liClockThetaResolvent
    continuous_liClockThetaKernel hfi hKi
  have hrc := integrableOn_cexp_mul_of_real continuous_liClockThetaResolvent hfi
  have hKc := integrableOn_cexp_mul_of_real continuous_liClockThetaKernel hKi
  have hsub : (fun t : ℝ => Complex.exp (-(z * t)) *
      (volterraConv liClockThetaResolvent liClockThetaKernel t : ℂ)) =
      fun t : ℝ => Complex.exp (-(z * t)) * (liClockThetaKernel t : ℂ) -
        Complex.exp (-(z * t)) * (liClockThetaResolvent t : ℂ) := by
    funext t
    have := liClockThetaResolvent_volterra t
    rw [show volterraConv liClockThetaResolvent liClockThetaKernel t =
      liClockThetaKernel t - liClockThetaResolvent t by linarith]
    push_cast; ring
  rw [hsub, integral_sub hKc hrc, integral_Ioi_cexp_mul_liClockThetaKernel hz0] at hconv
  unfold liClockThetaResolventLaplace
  linear_combination hconv

private theorem complex_integral_eq_ofReal' (p : ℝ) (f : ℝ → ℝ) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-((p : ℂ) * t)) * (f t : ℂ) =
      ((∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * f t : ℝ) : ℂ) := by
  have h1 : ∫ t in Ioi (0 : ℝ), Complex.exp (-((p : ℂ) * t)) * (f t : ℂ) =
      ∫ t in Ioi (0 : ℝ), ((Real.exp (-(p * t)) * f t : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by push_cast; ring_nf
  rw [h1]
  exact integral_ofReal

/-- **Real Laplace identity above the threshold.**  `∫_0^∞ e^{-pt} r = 1 - 1/Φ(1/p)`,
`Φ(1/p) = 1 + K̂(p) > 1`, for every real `p > β`. -/
theorem integral_exp_mul_liClockThetaResolvent {p : ℝ} (hp : liClockThetaResolventThreshold < p) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaResolvent t =
      1 - 1 / (1 + ∫ t in Ioi (0 : ℝ), liClockThetaKernel t * Real.exp (-(p * t))) := by
  have hp0 : 0 < p := liClockThetaResolventThreshold_nonneg.trans_lt hp
  have h := one_sub_liClockThetaResolventLaplace_mul (z := (p : ℂ)) (by simpa using hp)
  have hK := integral_Ioi_liClockThetaKernel_mul_exp_neg_eq hp0
  unfold liClockThetaResolventLaplace at h
  rw [complex_integral_eq_ofReal', show liClockThetaGenerator ((p : ℂ)⁻¹) =
    ((1 + ∫ t in Ioi (0 : ℝ), liClockThetaKernel t * Real.exp (-(p * t)) : ℝ) : ℂ) by
      push_cast; rw [hK]; ring] at h
  have h' : (1 - ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaResolvent t) *
      (1 + ∫ t in Ioi (0 : ℝ), liClockThetaKernel t * Real.exp (-(p * t))) = 1 := by
    exact_mod_cast h
  have hKpos : 0 ≤ ∫ t in Ioi (0 : ℝ), liClockThetaKernel t * Real.exp (-(p * t)) :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (liClockThetaKernel_nonneg (le_of_lt ht)) (Real.exp_pos _).le
  field_simp
  linarith

theorem integral_exp_mul_liClockThetaResolvent_mem_Icc {p : ℝ}
    (hp : liClockThetaResolventThreshold < p) :
    0 ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaResolvent t ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaResolvent t ≤ 1 := by
  rw [integral_exp_mul_liClockThetaResolvent hp]
  have hKpos : 0 ≤ ∫ t in Ioi (0 : ℝ), liClockThetaKernel t * Real.exp (-(p * t)) :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (liClockThetaKernel_nonneg (le_of_lt ht)) (Real.exp_pos _).le
  have h1 : 1 / (1 + ∫ t in Ioi (0 : ℝ), liClockThetaKernel t * Real.exp (-(p * t))) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have h2 : 0 ≤ 1 / (1 + ∫ t in Ioi (0 : ℝ), liClockThetaKernel t * Real.exp (-(p * t))) := by
    positivity
  constructor <;> linarith

/-- **Under `β = 0` the signed Laplace mass tends to one.** -/
theorem tendsto_integral_exp_mul_liClockThetaResolvent_of_threshold_eq_zero
    (h0 : liClockThetaResolventThreshold = 0) :
    Tendsto (fun p => ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaResolvent t)
      (𝓝[>] 0) (𝓝 1) := by
  have hc1 := liClockThetaGeneratorCoeff_one_pos
  have hsq : Tendsto (fun p : ℝ => p ^ 2 / liClockThetaGeneratorCoeff 1) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun p : ℝ => p ^ 2 / liClockThetaGeneratorCoeff 1) (𝓝 0) (𝓝 0) := by
      have h := ((continuous_pow 2).div_const (liClockThetaGeneratorCoeff 1)).tendsto 0
      simpa using h
    exact this.mono_left nhdsWithin_le_nhds
  have hlow : Tendsto (fun p : ℝ => (1 : ℝ) - p ^ 2 / liClockThetaGeneratorCoeff 1) (𝓝[>] 0)
      (𝓝 1) := by simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hsq
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with p hp
    have hp' : liClockThetaResolventThreshold < p := by rw [h0]; exact hp
    have hp0 : (0 : ℝ) < p := hp
    rw [integral_exp_mul_liClockThetaResolvent hp']
    have hK := liClockThetaGeneratorCoeff_one_div_sq_le_integral hp0
    have hKp : 0 < 1 + ∫ t in Ioi (0 : ℝ), liClockThetaKernel t * Real.exp (-(p * t)) := by
      have : 0 ≤ liClockThetaGeneratorCoeff 1 * (p ^ 2)⁻¹ := by positivity
      linarith
    have : 1 / (1 + ∫ t in Ioi (0 : ℝ), liClockThetaKernel t * Real.exp (-(p * t))) ≤
        p ^ 2 / liClockThetaGeneratorCoeff 1 := by
      rw [div_le_div_iff₀ hKp hc1, one_mul]
      have h2 : liClockThetaGeneratorCoeff 1 ≤ (∫ t in Ioi (0 : ℝ), liClockThetaKernel t *
          Real.exp (-(p * t))) * p ^ 2 := by
        have := mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ p ^ 2)
        rwa [mul_assoc, inv_mul_cancel₀ (by positivity), mul_one] at this
      nlinarith
    linarith
  · filter_upwards [self_mem_nhdsWithin] with p hp
    have hp' : liClockThetaResolventThreshold < p := by rw [h0]; exact hp
    exact (integral_exp_mul_liClockThetaResolvent_mem_Icc hp').2

/-! ## The critical divergence -/

/-- **The critical weighted integral diverges.**  `∫_0^∞ e^{-βt}|r(t)| dt = ∞`. -/
theorem not_integrableOn_exp_threshold_mul_abs_liClockThetaResolvent :
    ¬ IntegrableOn (fun t => Real.exp (-(liClockThetaResolventThreshold * t)) *
      |liClockThetaResolvent t|) (Ioi 0) := by
  intro hint
  set β := liClockThetaResolventThreshold
  set M := ∫ t in Ioi (0 : ℝ), Real.exp (-(β * t)) * |liClockThetaResolvent t|
  have hM : 0 ≤ M := setIntegral_nonneg measurableSet_Ioi fun t _ =>
    mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  obtain ⟨p₀, hp₀, hre, hzero⟩ := exists_liClockThetaGenerator_inv_eq_zero_re_eq_threshold
  have hcont : ContinuousAt (fun z : ℂ => liClockThetaGenerator z⁻¹) p₀ :=
    (differentiable_liClockThetaGenerator.continuous.continuousAt).comp (continuousAt_inv₀ hp₀)
  have hpath : Tendsto (fun ε : ℝ => p₀ + (ε : ℂ)) (𝓝[>] 0) (𝓝 p₀) := by
    have : Tendsto (fun ε : ℝ => p₀ + (ε : ℂ)) (𝓝 0) (𝓝 p₀) := by
      have h := (tendsto_const_nhds (x := p₀)).add (Complex.continuous_ofReal.tendsto (0 : ℝ))
      simp only [Complex.ofReal_zero, add_zero] at h
      exact h
    exact this.mono_left nhdsWithin_le_nhds
  have htend := (hcont.tendsto.comp hpath)
  rw [hzero] at htend
  have htend' : Tendsto (fun ε : ℝ => ‖liClockThetaGenerator (p₀ + (ε : ℂ))⁻¹‖) (𝓝[>] 0)
      (𝓝 0) := by simpa using htend.norm
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, ‖liClockThetaGenerator (p₀ + (ε : ℂ))⁻¹‖ < 1 / (2 + M) :=
    htend'.eventually (gt_mem_nhds (div_pos one_pos (by linarith)))
  obtain ⟨ε, hsmall, hε⟩ := (hev.and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hε : (0 : ℝ) < ε := hε
  set z := p₀ + (ε : ℂ)
  have hzre : β < z.re := by simp only [z, Complex.add_re, Complex.ofReal_re, hre]; linarith
  have hid := one_sub_liClockThetaResolventLaplace_mul hzre
  have hH : ‖liClockThetaResolventLaplace z‖ ≤ M := by
    unfold liClockThetaResolventLaplace
    refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on ?_ hint measurableSet_Ioi fun t ht => ?_
    · exact (integrableOn_cexp_mul_of_real continuous_liClockThetaResolvent
        (integrableOn_exp_mul_abs_liClockThetaResolvent hzre)).norm
    · have ht' : (0 : ℝ) ≤ t := le_of_lt ht
      rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (abs_nonneg _)
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero]
      nlinarith
  have hnorm := congrArg norm hid
  rw [norm_mul, norm_one] at hnorm
  have h1 : ‖1 - liClockThetaResolventLaplace z‖ ≤ 1 + M :=
    (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have h2 : ‖1 - liClockThetaResolventLaplace z‖ * ‖liClockThetaGenerator z⁻¹‖ ≤
      (1 + M) * (1 / (2 + M)) :=
    mul_le_mul h1 hsmall.le (norm_nonneg _) (by positivity)
  have h3 : (1 + M) * (1 / (2 + M)) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]; linarith
  linarith

/-- **Exact absolute threshold.**  `e^{-pt}|r|` is integrable on `(0,∞)` iff `p > β`, for every
real `p`. -/
theorem integrableOn_exp_mul_abs_liClockThetaResolvent_iff (p : ℝ) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * |liClockThetaResolvent t|) (Ioi 0) ↔
      liClockThetaResolventThreshold < p := by
  refine ⟨fun h => ?_, integrableOn_exp_mul_abs_liClockThetaResolvent⟩
  by_contra hp
  simp only [not_lt] at hp
  refine not_integrableOn_exp_threshold_mul_abs_liClockThetaResolvent (h.mono' ?_ ?_)
  · exact ((by fun_prop : Continuous fun t : ℝ =>
      Real.exp (-(liClockThetaResolventThreshold * t))).mul
      continuous_liClockThetaResolvent.abs).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) ≤ t := le_of_lt ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_abs]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) (abs_nonneg _)

/-! ## Signed parts -/

/-- The positive part `r₊ = max(r, 0)`. -/
def liClockThetaResolventPos (t : ℝ) : ℝ := max (liClockThetaResolvent t) 0

/-- The negative part `r₋ = max(-r, 0)`. -/
def liClockThetaResolventNeg (t : ℝ) : ℝ := max (-liClockThetaResolvent t) 0

theorem continuous_liClockThetaResolventPos : Continuous liClockThetaResolventPos :=
  continuous_liClockThetaResolvent.max continuous_const

theorem continuous_liClockThetaResolventNeg : Continuous liClockThetaResolventNeg :=
  continuous_liClockThetaResolvent.neg.max continuous_const

theorem liClockThetaResolventPos_sub_neg (t : ℝ) :
    liClockThetaResolventPos t - liClockThetaResolventNeg t = liClockThetaResolvent t :=
  max_zero_sub_max_neg_zero_eq_self _

theorem liClockThetaResolventPos_add_neg (t : ℝ) :
    liClockThetaResolventPos t + liClockThetaResolventNeg t = |liClockThetaResolvent t| := by
  unfold liClockThetaResolventPos liClockThetaResolventNeg
  rcases le_total 0 (liClockThetaResolvent t) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h, add_zero]
  · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h, zero_add]

/-- **Signed causal balance.**  `r₊ + r₊ ⋆ K = K + r₋ + r₋ ⋆ K` at every real clock. -/
theorem liClockThetaResolvent_signed_balance (t : ℝ) :
    liClockThetaResolventPos t + volterraConv liClockThetaResolventPos liClockThetaKernel t =
      liClockThetaKernel t + liClockThetaResolventNeg t +
        volterraConv liClockThetaResolventNeg liClockThetaKernel t := by
  have h := liClockThetaResolvent_volterra t
  have hr : liClockThetaResolvent = fun s => liClockThetaResolventPos s - liClockThetaResolventNeg s :=
    funext fun s => (liClockThetaResolventPos_sub_neg s).symm
  rw [hr] at h
  have hlin : volterraConv (fun s => liClockThetaResolventPos s - liClockThetaResolventNeg s)
      liClockThetaKernel t = volterraConv liClockThetaResolventPos liClockThetaKernel t -
        volterraConv liClockThetaResolventNeg liClockThetaKernel t := by
    rw [volterraConv_comm, volterraConv_sub_right continuous_liClockThetaKernel
      continuous_liClockThetaResolventPos continuous_liClockThetaResolventNeg,
      volterraConv_comm liClockThetaKernel, volterraConv_comm liClockThetaKernel]
  rw [hlin] at h
  linarith

private theorem volterraConv_nonneg_of_nonneg {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ volterraConv f liClockThetaKernel t := by
  unfold volterraConv
  exact intervalIntegral.integral_nonneg ht fun s hs =>
    mul_nonneg (hf _) (liClockThetaKernel_nonneg hs.1)

/-- Weighted convolution with `K` preserves integrability of nonnegative continuous inputs. -/
private theorem integrableOn_exp_mul_volterraConv_kernel {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) {p : ℝ} (hp : 0 < p)
    (hfi : IntegrableOn (fun t => Real.exp (-(p * t)) * f t) (Ioi 0)) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * volterraConv f liClockThetaKernel t) (Ioi 0) := by
  have hKi : IntegrableOn (fun t => Real.exp (-p * t) * liClockThetaKernel t) (Ioi 0) :=
    (integrableOn_liClockThetaKernel_mul_exp_neg hp).congr_fun (fun t _ => by ring_nf)
      measurableSet_Ioi
  have hfi' : IntegrableOn (fun t => Real.exp (-p * t) * f t) (Ioi 0) :=
    hfi.congr_fun (fun t _ => by ring_nf) measurableSet_Ioi
  have h := integrableOn_volterraConv_of_nonneg
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-p * t)).mul hf)
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-p * t)).mul continuous_liClockThetaKernel)
    (fun t _ => mul_nonneg (Real.exp_pos _).le (hf0 t))
    (fun t ht => mul_nonneg (Real.exp_pos _).le (liClockThetaKernel_nonneg ht)) hfi' hKi
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  show volterraConv (fun s => Real.exp (-p * s) * f s)
    (fun s => Real.exp (-p * s) * liClockThetaKernel s) t = _
  rw [← exp_mul_volterraConv]
  ring_nf

private theorem liClockThetaResolventPos_nonneg (t : ℝ) : 0 ≤ liClockThetaResolventPos t :=
  le_max_right _ _

private theorem liClockThetaResolventNeg_nonneg (t : ℝ) : 0 ≤ liClockThetaResolventNeg t :=
  le_max_right _ _

private theorem integrableOn_of_le_on {f g : ℝ → ℝ} (hf : Continuous f) (hg : IntegrableOn g (Ioi 0))
    (h : ∀ t, 0 < t → 0 ≤ f t ∧ f t ≤ g t) : IntegrableOn f (Ioi 0) := by
  refine hg.mono' hf.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (h t ht).1]
  exact (h t ht).2

/-- **Weighted signed parts are integrable together** for every `p > 0`. -/
theorem integrableOn_exp_mul_liClockThetaResolventPos_iff_neg {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaResolventPos t) (Ioi 0) ↔
      IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaResolventNeg t) (Ioi 0) := by
  have hKi : IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaKernel t) (Ioi 0) :=
    (integrableOn_liClockThetaKernel_mul_exp_neg hp).congr_fun (fun t _ => mul_comm _ _)
      measurableSet_Ioi
  constructor
  · intro h
    have hc := integrableOn_exp_mul_volterraConv_kernel continuous_liClockThetaResolventPos
      liClockThetaResolventPos_nonneg hp h
    refine integrableOn_of_le_on ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(p * t))).mul
      continuous_liClockThetaResolventNeg) (h.add hc) fun t ht => ⟨?_, ?_⟩
    · exact mul_nonneg (Real.exp_pos _).le (liClockThetaResolventNeg_nonneg t)
    · have hb := liClockThetaResolvent_signed_balance t
      have h1 := volterraConv_nonneg_of_nonneg liClockThetaResolventNeg_nonneg ht.le
      have h2 := liClockThetaKernel_nonneg ht.le
      have he := (Real.exp_pos (-(p * t))).le
      simp only [Pi.add_apply]
      nlinarith [mul_le_mul_of_nonneg_left (show liClockThetaResolventNeg t ≤
        liClockThetaResolventPos t + volterraConv liClockThetaResolventPos liClockThetaKernel t
          by linarith) he]
  · intro h
    have hc := integrableOn_exp_mul_volterraConv_kernel continuous_liClockThetaResolventNeg
      liClockThetaResolventNeg_nonneg hp h
    refine integrableOn_of_le_on ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(p * t))).mul
      continuous_liClockThetaResolventPos) ((hKi.add h).add hc) fun t ht => ⟨?_, ?_⟩
    · exact mul_nonneg (Real.exp_pos _).le (liClockThetaResolventPos_nonneg t)
    · have hb := liClockThetaResolvent_signed_balance t
      have h1 := volterraConv_nonneg_of_nonneg liClockThetaResolventPos_nonneg ht.le
      have he := (Real.exp_pos (-(p * t))).le
      simp only [Pi.add_apply]
      nlinarith [mul_le_mul_of_nonneg_left (show liClockThetaResolventPos t ≤
        liClockThetaKernel t + liClockThetaResolventNeg t +
          volterraConv liClockThetaResolventNeg liClockThetaKernel t by linarith) he]

/-- Bounded weighted masses force ordinary integrability of a nonnegative continuous function. -/
private theorem integrableOn_of_laplace_le {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    {C : ℝ} (hint : ∀ p, 0 < p → IntegrableOn (fun t => Real.exp (-(p * t)) * f t) (Ioi 0))
    (hC : ∀ p, 0 < p → ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * f t ≤ C) :
    IntegrableOn f (Ioi 0) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (l := atTop) (b := id) C 0
    (fun T => hf.integrableOn_Ioc) tendsto_id ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  simp only [id, Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
  have hbound : ∀ p, 0 < p → ∫ x in (0 : ℝ)..T, f x ≤ Real.exp (p * T) * C := by
    intro p hp
    have h1 : ∫ x in (0 : ℝ)..T, f x ≤ ∫ x in (0 : ℝ)..T, Real.exp (p * T) *
        (Real.exp (-(p * x)) * f x) := by
      refine intervalIntegral.integral_mono_on hT (hf.intervalIntegrable _ _)
        ((by fun_prop : Continuous fun x : ℝ => Real.exp (p * T) *
          (Real.exp (-(p * x)) * f x)).intervalIntegrable _ _) fun x hx => ?_
      rw [← mul_assoc, ← Real.exp_add]
      exact le_mul_of_one_le_left (hf0 x) (Real.one_le_exp (by nlinarith [hx.2]))
    have h2 : ∫ x in (0 : ℝ)..T, Real.exp (-(p * x)) * f x ≤
        ∫ x in Ioi (0 : ℝ), Real.exp (-(p * x)) * f x := by
      rw [intervalIntegral.integral_of_le hT]
      exact setIntegral_mono_set (hint p hp)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun x _ =>
          mul_nonneg (Real.exp_pos _).le (hf0 x))
        (Eventually.of_forall fun x hx => Ioc_subset_Ioi_self hx)
    rw [intervalIntegral.integral_const_mul] at h1
    calc ∫ x in (0 : ℝ)..T, f x ≤ Real.exp (p * T) * ∫ x in (0 : ℝ)..T,
        Real.exp (-(p * x)) * f x := h1
      _ ≤ Real.exp (p * T) * C :=
        mul_le_mul_of_nonneg_left (h2.trans (hC p hp)) (Real.exp_pos _).le
  have htend : Tendsto (fun p : ℝ => Real.exp (p * T) * C) (𝓝[>] 0) (𝓝 C) := by
    have : Tendsto (fun p : ℝ => Real.exp (p * T) * C) (𝓝 0) (𝓝 C) := by
      have h := ((by fun_prop : Continuous fun p : ℝ => Real.exp (p * T) * C).tendsto 0)
      simpa using h
    exact this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun p hp => hbound p hp)

private theorem integral_exp_mul_resolvent_eq_pos_sub_neg {p : ℝ}
    (hpos : IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaResolventPos t) (Ioi 0))
    (hneg : IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaResolventNeg t) (Ioi 0)) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaResolvent t =
      (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaResolventPos t) -
        ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaResolventNeg t := by
  rw [← integral_sub hpos hneg]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [← liClockThetaResolventPos_sub_neg t]; ring

private theorem integrableOn_abs_of_parts {p : ℝ}
    (hpos : IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaResolventPos t) (Ioi 0))
    (hneg : IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaResolventNeg t) (Ioi 0)) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * |liClockThetaResolvent t|) (Ioi 0) :=
  (hpos.add hneg).congr_fun (fun t _ => by
    simp only [Pi.add_apply]; rw [← mul_add, liClockThetaResolventPos_add_neg]) measurableSet_Ioi

private theorem weight_mono {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t) {p p' : ℝ}
    (hpp : p ≤ p') (h : IntegrableOn (fun t => Real.exp (-(p * t)) * f t) (Ioi 0)) :
    IntegrableOn (fun t => Real.exp (-(p' * t)) * f t) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(p' * t)) * f t ≤
        ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * f t := by
  have hle : ∀ t ∈ Ioi (0 : ℝ), Real.exp (-(p' * t)) * f t ≤ Real.exp (-(p * t)) * f t :=
    fun t ht => mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.2 (by nlinarith [show (0 : ℝ) < t from ht])) (hf0 t)
  have hi : IntegrableOn (fun t => Real.exp (-(p' * t)) * f t) (Ioi 0) :=
    integrableOn_of_le_on ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(p' * t))).mul hf) h
      fun t ht => ⟨mul_nonneg (Real.exp_pos _).le (hf0 t), hle t ht⟩
  exact ⟨hi, setIntegral_mono_on hi h measurableSet_Ioi hle⟩

/-- **Exact signed-mass classification.**  For every real `p`, `e^{-pt} r₊` is integrable on
`(0,∞)` iff `p > β`. -/
theorem integrableOn_exp_mul_liClockThetaResolventPos_iff (p : ℝ) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaResolventPos t) (Ioi 0) ↔
      liClockThetaResolventThreshold < p := by
  have hβ0 := liClockThetaResolventThreshold_nonneg
  constructor
  · intro h
    rcases lt_or_ge 0 p with hp | hp
    · exact (integrableOn_exp_mul_abs_liClockThetaResolvent_iff p).1
        (integrableOn_abs_of_parts h ((integrableOn_exp_mul_liClockThetaResolventPos_iff_neg hp).1 h))
    · exfalso
      have hpos' : ∀ p', 0 < p' → IntegrableOn
          (fun t => Real.exp (-(p' * t)) * liClockThetaResolventPos t) (Ioi 0) := fun p' hp' =>
        (weight_mono continuous_liClockThetaResolventPos liClockThetaResolventPos_nonneg
          (by linarith) h).1
      have hneg' : ∀ p', 0 < p' → IntegrableOn
          (fun t => Real.exp (-(p' * t)) * liClockThetaResolventNeg t) (Ioi 0) := fun p' hp' =>
        (integrableOn_exp_mul_liClockThetaResolventPos_iff_neg hp').1 (hpos' p' hp')
      have hthr : ∀ p', 0 < p' → liClockThetaResolventThreshold < p' := fun p' hp' =>
        (integrableOn_exp_mul_abs_liClockThetaResolvent_iff p').1
          (integrableOn_abs_of_parts (hpos' p' hp') (hneg' p' hp'))
      have hnegint : IntegrableOn liClockThetaResolventNeg (Ioi 0) := by
        refine integrableOn_of_laplace_le continuous_liClockThetaResolventNeg
          liClockThetaResolventNeg_nonneg hneg' (C := ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) *
            liClockThetaResolventPos t) fun p' hp' => ?_
        have hid := integral_exp_mul_resolvent_eq_pos_sub_neg (hpos' p' hp') (hneg' p' hp')
        have hH := (integral_exp_mul_liClockThetaResolvent_mem_Icc (hthr p' hp')).1
        have hmono := (weight_mono continuous_liClockThetaResolventPos
          liClockThetaResolventPos_nonneg (by linarith : p ≤ p') h).2
        linarith
      have hposint : IntegrableOn (fun t => Real.exp (-(0 * t)) * liClockThetaResolventPos t)
          (Ioi 0) := (weight_mono continuous_liClockThetaResolventPos
            liClockThetaResolventPos_nonneg hp h).1
      have hnegint' : IntegrableOn (fun t => Real.exp (-(0 * t)) * liClockThetaResolventNeg t)
          (Ioi 0) := hnegint.congr_fun (fun t _ => by simp) measurableSet_Ioi
      have := (integrableOn_exp_mul_abs_liClockThetaResolvent_iff 0).1
        (integrableOn_abs_of_parts hposint hnegint')
      linarith
  · intro hp
    exact integrableOn_of_le_on ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(p * t))).mul
      continuous_liClockThetaResolventPos) (integrableOn_exp_mul_abs_liClockThetaResolvent hp)
      fun t _ => ⟨mul_nonneg (Real.exp_pos _).le (liClockThetaResolventPos_nonneg t),
        mul_le_mul_of_nonneg_left (le_of_le_of_eq (le_add_of_nonneg_right
          (liClockThetaResolventNeg_nonneg t)) (liClockThetaResolventPos_add_neg t))
          (Real.exp_pos _).le⟩

/-- **Exact signed-mass classification.**  For every real `p`, `e^{-pt} r₋` is integrable on
`(0,∞)` iff `p > β`. -/
theorem integrableOn_exp_mul_liClockThetaResolventNeg_iff (p : ℝ) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaResolventNeg t) (Ioi 0) ↔
      liClockThetaResolventThreshold < p := by
  have hβ0 := liClockThetaResolventThreshold_nonneg
  constructor
  · intro h
    rcases lt_or_ge 0 p with hp | hp
    · exact (integrableOn_exp_mul_liClockThetaResolventPos_iff p).1
        ((integrableOn_exp_mul_liClockThetaResolventPos_iff_neg hp).2 h)
    · exfalso
      have hneg' : ∀ p', 0 < p' → IntegrableOn
          (fun t => Real.exp (-(p' * t)) * liClockThetaResolventNeg t) (Ioi 0) := fun p' hp' =>
        (weight_mono continuous_liClockThetaResolventNeg liClockThetaResolventNeg_nonneg
          (by linarith) h).1
      have hpos' : ∀ p', 0 < p' → IntegrableOn
          (fun t => Real.exp (-(p' * t)) * liClockThetaResolventPos t) (Ioi 0) := fun p' hp' =>
        (integrableOn_exp_mul_liClockThetaResolventPos_iff_neg hp').2 (hneg' p' hp')
      have hthr : ∀ p', 0 < p' → liClockThetaResolventThreshold < p' := fun p' hp' =>
        (integrableOn_exp_mul_abs_liClockThetaResolvent_iff p').1
          (integrableOn_abs_of_parts (hpos' p' hp') (hneg' p' hp'))
      have hposint : IntegrableOn liClockThetaResolventPos (Ioi 0) := by
        refine integrableOn_of_laplace_le continuous_liClockThetaResolventPos
          liClockThetaResolventPos_nonneg hpos' (C := 1 + ∫ t in Ioi (0 : ℝ),
            Real.exp (-(p * t)) * liClockThetaResolventNeg t) fun p' hp' => ?_
        have hid := integral_exp_mul_resolvent_eq_pos_sub_neg (hpos' p' hp') (hneg' p' hp')
        have hH := (integral_exp_mul_liClockThetaResolvent_mem_Icc (hthr p' hp')).2
        have hmono := (weight_mono continuous_liClockThetaResolventNeg
          liClockThetaResolventNeg_nonneg (by linarith : p ≤ p') h).2
        linarith
      have hnegint : IntegrableOn (fun t => Real.exp (-(0 * t)) * liClockThetaResolventNeg t)
          (Ioi 0) := (weight_mono continuous_liClockThetaResolventNeg
            liClockThetaResolventNeg_nonneg hp h).1
      have hposint' : IntegrableOn (fun t => Real.exp (-(0 * t)) * liClockThetaResolventPos t)
          (Ioi 0) := hposint.congr_fun (fun t _ => by simp) measurableSet_Ioi
      have := (integrableOn_exp_mul_abs_liClockThetaResolvent_iff 0).1
        (integrableOn_abs_of_parts hposint' hnegint)
      linarith
  · intro hp
    exact integrableOn_of_le_on ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(p * t))).mul
      continuous_liClockThetaResolventNeg) (integrableOn_exp_mul_abs_liClockThetaResolvent hp)
      fun t _ => ⟨mul_nonneg (Real.exp_pos _).le (liClockThetaResolventNeg_nonneg t),
        mul_le_mul_of_nonneg_left (le_of_le_of_eq (le_add_of_nonneg_left
          (liClockThetaResolventPos_nonneg t)) (liClockThetaResolventPos_add_neg t))
          (Real.exp_pos _).le⟩

/-- **Both ordinary signed masses are infinite.** -/
theorem not_integrableOn_liClockThetaResolventPos :
    ¬ IntegrableOn liClockThetaResolventPos (Ioi 0) := fun h => by
  have := (integrableOn_exp_mul_liClockThetaResolventPos_iff 0).1
    (h.congr_fun (fun t _ => by simp) measurableSet_Ioi)
  linarith [liClockThetaResolventThreshold_nonneg]

theorem not_integrableOn_liClockThetaResolventNeg :
    ¬ IntegrableOn liClockThetaResolventNeg (Ioi 0) := fun h => by
  have := (integrableOn_exp_mul_liClockThetaResolventNeg_iff 0).1
    (h.congr_fun (fun t _ => by simp) measurableSet_Ioi)
  linarith [liClockThetaResolventThreshold_nonneg]

private theorem integrableOn_of_eventually_zero {f : ℝ → ℝ} (hf : Continuous f) {T : ℝ}
    (hT : ∀ t, T < t → f t = 0) : IntegrableOn f (Ioi 0) := by
  have h1 : IntegrableOn f (Ioc 0 (max T 0)) := hf.integrableOn_Ioc
  have h2 : IntegrableOn f (Ioi (max T 0)) :=
    integrableOn_zero.congr_fun (fun t ht => (hT t (lt_of_le_of_lt (le_max_left _ _) ht)).symm)
      measurableSet_Ioi
  have := h1.union h2
  rwa [Ioc_union_Ioi_eq_Ioi (le_max_right _ _)] at this

/-- **Both signs occur cofinally.** -/
theorem liClockThetaResolvent_frequently_pos_and_neg (T : ℝ) :
    (∃ t, T < t ∧ 0 < liClockThetaResolvent t) ∧ ∃ t, T < t ∧ liClockThetaResolvent t < 0 := by
  constructor
  · by_contra h
    simp only [not_exists, not_and, not_lt] at h
    exact not_integrableOn_liClockThetaResolventPos (integrableOn_of_eventually_zero
      continuous_liClockThetaResolventPos fun t ht => max_eq_right (h t ht))
  · by_contra h
    simp only [not_exists, not_and, not_lt] at h
    exact not_integrableOn_liClockThetaResolventNeg (integrableOn_of_eventually_zero
      continuous_liClockThetaResolventNeg fun t ht => max_eq_right (by linarith [h t ht]))

end RHTower

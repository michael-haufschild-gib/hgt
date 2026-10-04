import GaloisForLFunctions.HTGeometry.RectangleBorelLaplaceInversion
import GaloisForLFunctions.HTGeometry.LagrangeRectangleContour
import GaloisForLFunctions.RHTower.LiClockThetaReciprocalSource
import GaloisForLFunctions.RHTower.XiDivisorDiagonalTraceClass
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockDampedResolvent

/-!
# Rectangle growth of the theta causal inverse

Let `Φ` be the normalized actual Xi generator and `G(p) = 1/(p² Φ(1/p))`.  The zeros of `Φ(1/p)`
are the points `p = -i w_q`, `w_q = α_q⁻¹`, so `|Re p| = |Im w_q|` and `|Im p| ≤ |w_q| < 1/2`.
Square summability of `|w_q|` and the strict strip bound `|Im w_q| < 1/300` give one `d < 1/300`
with `|Im w_q| ≤ d` for every zero copy.

On `|p| ≥ 2` the symbol is the Laurent series `G(p) = Σ_n a_n p^{-2n-2}` of the reciprocal germ, so
by Borel–Laplace inversion on the square `[-2,2]²`,
`2πi u^{(m)}(t) = ∮ p^m e^{tp} G(p) dp`.  The integrand is holomorphic on the frame between the
square and the thin rectangle `[-δ,δ] × [-1/2,1/2]` for every `d < δ ≤ 2`, so the contour deforms
onto the thin rectangle, where `|e^{tp}| ≤ e^{δ|t|}`.  Hence every fixed derivative of the causal
inverse `u` and of the resolvent `r = -u''` is `O(e^{δ|t|})` for one `δ < 1/300`.
-/

open Complex Set Filter Topology GaloisForLFunctions.HTGeometry
open scoped Real

noncomputable section

namespace RHTower

/-! ## The strip gap of the reciprocal frequencies -/

theorem norm_inv_xiSpectralPoint_lt_half (q : XiZeroCopy) : ‖(xiSpectralPoint q)⁻¹‖ < 1 / 2 := by
  have h := oneHundredFifty_lt_norm_xiSpectralPoint_sq q
  have h2 : 2 < ‖xiSpectralPoint q‖ := by nlinarith [norm_nonneg (xiSpectralPoint q)]
  rw [norm_inv, inv_eq_one_div, div_lt_div_iff₀ (by linarith) two_pos]
  linarith

theorem xiSpectralPoint_ne_zero' (q : XiZeroCopy) : xiSpectralPoint q ≠ 0 := by
  intro h
  have := oneHundredFifty_lt_norm_xiSpectralPoint_sq q
  rw [h, norm_zero] at this
  norm_num at this

/-- **Uniform strip gap.**  One `d < 1/300` bounds every `|Im α_q⁻¹|`. -/
theorem exists_abs_im_inv_xiSpectralPoint_le :
    ∃ d : ℝ, 0 ≤ d ∧ d < 1 / 300 ∧ ∀ q : XiZeroCopy, |((xiSpectralPoint q)⁻¹).im| ≤ d := by
  have hev : ∀ᶠ q in cofinite, ‖(xiSpectralPoint q)⁻¹‖ ^ (2 : ℕ) < (1 / 600 : ℝ) ^ 2 :=
    summable_norm_inv_xiSpectralPoint_sq.tendsto_cofinite_zero.eventually_lt_const (by norm_num)
  have hfin := Filter.eventually_cofinite.1 hev
  have hsmall : ∀ q, q ∉ hfin.toFinset → |((xiSpectralPoint q)⁻¹).im| ≤ 1 / 600 := by
    intro q hq
    have hq' : ‖(xiSpectralPoint q)⁻¹‖ ^ (2 : ℕ) < (1 / 600 : ℝ) ^ 2 := by
      by_contra h
      exact hq (hfin.mem_toFinset.2 h)
    have hw : ‖(xiSpectralPoint q)⁻¹‖ < 1 / 600 := by
      nlinarith [norm_nonneg (xiSpectralPoint q)⁻¹]
    exact (abs_im_le_norm _).trans hw.le
  by_cases hS : hfin.toFinset.Nonempty
  · obtain ⟨q₀, -, hmax⟩ := hfin.toFinset.exists_max_image
      (fun q => |((xiSpectralPoint q)⁻¹).im|) hS
    refine ⟨max (1 / 600) |((xiSpectralPoint q₀)⁻¹).im|, by positivity,
      max_lt (by norm_num) (abs_im_inv_xiSpectralPoint_lt_one_div_threeHundred q₀), fun q => ?_⟩
    by_cases hq : q ∈ hfin.toFinset
    · exact (hmax q hq).trans (le_max_right _ _)
    · exact (hsmall q hq).trans (le_max_left _ _)
  · refine ⟨1 / 600, by norm_num, by norm_num, fun q => hsmall q fun hq => hS ⟨q, hq⟩⟩

/-! ## The inverse symbol -/

theorem differentiable_liClockThetaGenerator : Differentiable ℂ liClockThetaGenerator := by
  have h : liClockThetaGenerator = fun z => XiC (-I * z) / XiC 0 :=
    funext liClockThetaGenerator_eq_XiC
  rw [h]
  exact (XiC_differentiable.comp (differentiable_id.const_mul (-I))).div_const _

/-- The Laplace symbol of the causal inverse, `G(p) = 1/(p² Φ(1/p))`. -/
def liClockThetaInverseSymbol (p : ℂ) : ℂ := (p ^ 2 * liClockThetaGenerator p⁻¹)⁻¹

theorem differentiableAt_liClockThetaInverseSymbol {p : ℂ} (hp : p ≠ 0)
    (hΦ : liClockThetaGenerator p⁻¹ ≠ 0) : DifferentiableAt ℂ liClockThetaInverseSymbol p := by
  have h1 : DifferentiableAt ℂ (fun p : ℂ => p ^ 2 * liClockThetaGenerator p⁻¹) p :=
    ((differentiable_pow 2).differentiableAt).mul
      ((differentiable_liClockThetaGenerator _).comp p (differentiableAt_inv hp))
  exact h1.inv (mul_ne_zero (pow_ne_zero 2 hp) hΦ)

/-- **Pole location.**  Outside the open box `(-δ,δ) × (-1/2,1/2)`, `d < δ`, the reciprocal
generator `Φ(1/p)` has no zero. -/
theorem liClockThetaGenerator_inv_ne_zero {d δ : ℝ}
    (hd : ∀ q : XiZeroCopy, |((xiSpectralPoint q)⁻¹).im| ≤ d) (hdδ : d < δ) {p : ℂ}
    (hp : p ∉ Ioo (-δ) δ ×ℂ Ioo (-(1 / 2)) (1 / 2)) : liClockThetaGenerator p⁻¹ ≠ 0 := by
  intro h0
  obtain ⟨q, hq⟩ := (liClockThetaGenerator_eq_zero_iff _).1 h0
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [inv_zero, mul_zero] at hq
    exact xiSpectralPoint_ne_zero' q hq
  have hw : (xiSpectralPoint q)⁻¹ = I * p := by
    rw [hq, mul_inv, inv_inv, inv_neg, Complex.inv_I, neg_neg]
  have hre : p.re = ((xiSpectralPoint q)⁻¹).im := by rw [hw]; simp
  have him : p.im = -((xiSpectralPoint q)⁻¹).re := by rw [hw]; simp
  apply hp
  have h1 := hd q
  have h2 := (abs_re_le_norm (xiSpectralPoint q)⁻¹).trans (norm_inv_xiSpectralPoint_lt_half q).le
  have h3 := norm_inv_xiSpectralPoint_lt_half q
  rw [mem_reProdIm, mem_Ioo, mem_Ioo, hre, him]
  have h2' := (abs_re_le_norm (xiSpectralPoint q)⁻¹).trans_lt h3
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    cases abs_cases ((xiSpectralPoint q)⁻¹).im <;> cases abs_cases ((xiSpectralPoint q)⁻¹).re <;>
      linarith

/-! ## The Laurent expansion at infinity -/

/-- Borel coefficients of the causal inverse: `b_{2n+1} = a_n`, `b_{2n} = 0`. -/
def liClockThetaInverseBorelCoeff (N : ℕ) : ℝ :=
  if N % 2 = 1 then liClockThetaReciprocalCoeff (N / 2) else 0

theorem liClockThetaInverseBorelCoeff_even (k : ℕ) : liClockThetaInverseBorelCoeff (2 * k) = 0 := by
  unfold liClockThetaInverseBorelCoeff
  rw [if_neg (by omega)]

theorem liClockThetaInverseBorelCoeff_odd (k : ℕ) :
    liClockThetaInverseBorelCoeff (2 * k + 1) = liClockThetaReciprocalCoeff k := by
  unfold liClockThetaInverseBorelCoeff
  rw [if_pos (by omega), show (2 * k + 1) / 2 = k by omega]

theorem geometricCoeffBound_liClockThetaInverseBorelCoeff :
    GeometricCoeffBound liClockThetaInverseBorelCoeff 1 1 := by
  intro N
  rw [one_pow, mul_one]
  unfold liClockThetaInverseBorelCoeff
  split_ifs
  · exact (abs_liClockThetaReciprocalCoeff_le _).trans (pow_le_one₀ (by norm_num) (by norm_num))
  · simp

/-- The causal inverse is the Borel series of its odd coefficients. -/
theorem liClockThetaCausalInverse_eq_borelSeries :
    liClockThetaCausalInverse = borelSeries liClockThetaInverseBorelCoeff := by
  funext t
  have hs := summable_borelTerm geometricCoeffBound_liClockThetaInverseBorelCoeff t
  have hse : Summable fun k : ℕ =>
      liClockThetaInverseBorelCoeff (2 * k) * dividedPowerFn (2 * k) t :=
    hs.comp_injective (i := fun k : ℕ => 2 * k) fun a b h => by simpa using h
  have hso : Summable fun k : ℕ =>
      liClockThetaInverseBorelCoeff (2 * k + 1) * dividedPowerFn (2 * k + 1) t :=
    hs.comp_injective (i := fun k : ℕ => 2 * k + 1) fun a b h => by simpa using h
  unfold borelSeries
  rw [← tsum_even_add_odd (f := fun n => liClockThetaInverseBorelCoeff n * dividedPowerFn n t)
    hse hso]
  simp only [liClockThetaInverseBorelCoeff_even, zero_mul, tsum_zero, zero_add,
    liClockThetaInverseBorelCoeff_odd]
  unfold liClockThetaCausalInverse oddFactorialSeries dividedPowerFn
  refine tsum_congr fun k => ?_
  ring

/-- **Laurent expansion.**  For `|p| ≥ 2`, `G(p) = Σ_N b_N p^{-N-1}`. -/
theorem liClockThetaInverseSymbol_eq_tsum {p : ℂ} (hp : 2 ≤ ‖p‖) :
    liClockThetaInverseSymbol p =
      ∑' N, (liClockThetaInverseBorelCoeff N : ℂ) * (p ^ (N + 1))⁻¹ := by
  have hp0 : p ≠ 0 := by
    rintro rfl; rw [norm_zero] at hp; norm_num at hp
  have hpinv : ‖p⁻¹‖ ≤ 1 / 2 := by
    rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ (by linarith) two_pos]; linarith
  have hz : ‖p⁻¹‖ ^ 2 < 2 := by nlinarith [norm_nonneg p⁻¹]
  have hΦA := liClockThetaGenerator_mul_reciprocalGerm hz
  have hodd : Summable fun k : ℕ =>
      (liClockThetaInverseBorelCoeff (2 * k + 1) : ℂ) * (p ^ (2 * k + 1 + 1))⁻¹ := by
    refine Summable.of_norm_bounded summable_geometric_two fun k => ?_
    rw [liClockThetaInverseBorelCoeff_odd, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_inv, norm_pow]
    have h1 : (‖p‖ ^ (2 * k + 1 + 1))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    calc |liClockThetaReciprocalCoeff k| * (‖p‖ ^ (2 * k + 1 + 1))⁻¹ ≤ (1 / 2) ^ k * 1 :=
          mul_le_mul (abs_liClockThetaReciprocalCoeff_le k) h1 (by positivity) (by positivity)
      _ = (1 / 2) ^ k := mul_one _
  have heven : Summable fun k : ℕ =>
      (liClockThetaInverseBorelCoeff (2 * k) : ℂ) * (p ^ (2 * k + 1))⁻¹ := by
    simp only [liClockThetaInverseBorelCoeff_even, Complex.ofReal_zero, zero_mul]
    exact summable_zero
  rw [← tsum_even_add_odd (f := fun N => (liClockThetaInverseBorelCoeff N : ℂ) * (p ^ (N + 1))⁻¹)
    heven hodd]
  simp only [liClockThetaInverseBorelCoeff_even, Complex.ofReal_zero, zero_mul, tsum_zero,
    zero_add, liClockThetaInverseBorelCoeff_odd]
  unfold liClockThetaInverseSymbol
  rw [mul_inv, inv_eq_of_mul_eq_one_right hΦA, liClockThetaReciprocalGerm, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [inv_pow, ← mul_assoc, mul_comm ((p ^ 2)⁻¹), mul_assoc, ← mul_inv, ← pow_add]
  ring_nf

/-! ## Contour representation and growth -/

private theorem two_le_norm_of_mem_bigSquareBorder {p : ℂ}
    (hp : p ∈ RectangleBorder (((-2 : ℝ) : ℂ) + ((-2 : ℝ) : ℂ) * I)
      (((2 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * I)) : 2 ≤ ‖p‖ := by
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff] at hp
  have hre := abs_re_le_norm p
  have him := abs_im_le_norm p
  rcases hp with ((⟨-, h⟩ | ⟨h, -⟩) | ⟨-, h⟩) | ⟨h, -⟩ <;> simp at h <;>
    first
    | (rw [h] at him; norm_num at him; linarith)
    | (rw [h] at hre; norm_num at hre; linarith)

private theorem not_mem_box_of_mem_thinBorder {δ : ℝ} {p : ℂ}
    (hp : p ∈ RectangleBorder (((-δ : ℝ) : ℂ) + ((-(1 / 2) : ℝ) : ℂ) * I)
      (((δ : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * I)) :
    p ∉ Ioo (-δ) δ ×ℂ Ioo (-(1 / 2)) (1 / 2) := by
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff] at hp
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  rcases hp with ((⟨-, h⟩ | ⟨h, -⟩) | ⟨-, h⟩) | ⟨h, -⟩ <;> simp at h <;> linarith

private theorem abs_re_le_of_mem_thinBorder {δ : ℝ} (hδ : 0 ≤ δ) {p : ℂ}
    (hp : p ∈ RectangleBorder (((-δ : ℝ) : ℂ) + ((-(1 / 2) : ℝ) : ℂ) * I)
      (((δ : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * I)) : |p.re| ≤ δ := by
  have h := (rectangleBorder_subset_rectangle _ _ hp).1
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero,
    add_zero] at h
  rw [uIcc_of_le (by linarith)] at h
  exact abs_le.2 ⟨h.1, h.2⟩

/-- **Contour representation.**  For `d < δ ≤ 2`,
`2πi u^{(m)}(t) = ∮_{∂([-δ,δ]×[-1/2,1/2])} p^m e^{tp} G(p) dp` at every real clock. -/
theorem two_pi_I_mul_iteratedDeriv_liClockThetaCausalInverse {d δ : ℝ}
    (hd : ∀ q : XiZeroCopy, |((xiSpectralPoint q)⁻¹).im| ≤ d) (hdδ : d < δ) (hδ0 : 0 < δ)
    (hδ2 : δ ≤ 2) (m : ℕ) (t : ℝ) :
    2 * π * I * ((iteratedDeriv m liClockThetaCausalInverse t : ℝ) : ℂ) =
      RectangleIntegral (fun p => p ^ m * cexp (t * p) * liClockThetaInverseSymbol p)
        (((-δ : ℝ) : ℂ) + ((-(1 / 2) : ℝ) : ℂ) * I) (((δ : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * I) := by
  have hinv := rectangleIntegral_borelLaplaceInversion
    geometricCoeffBound_liClockThetaInverseBorelCoeff zero_le_one one_lt_two
    (z := ((-2 : ℝ) : ℂ) + ((-2 : ℝ) : ℂ) * I) (w := ((2 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * I)
    (by simp) (by simp) (by simp) (by simp) (fun p hp => two_le_norm_of_mem_bigSquareBorder hp)
    m t
  have hcongr : RectangleIntegral (fun p => p ^ m * cexp (t * p) *
      ∑' N, (liClockThetaInverseBorelCoeff N : ℂ) * (p ^ (N + 1))⁻¹)
        (((-2 : ℝ) : ℂ) + ((-2 : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * I) =
      RectangleIntegral (fun p => p ^ m * cexp (t * p) * liClockThetaInverseSymbol p)
        (((-2 : ℝ) : ℂ) + ((-2 : ℝ) : ℂ) * I) (((2 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * I) := by
    refine RectangleIntegral_congr fun p hp => ?_
    rw [liClockThetaInverseSymbol_eq_tsum (two_le_norm_of_mem_bigSquareBorder hp)]
  have hframe := rectangleIntegral_eq_of_differentiableOn_frame
    (f := fun p => p ^ m * cexp (t * p) * liClockThetaInverseSymbol p)
    (x₀ := -2) (x₁ := -δ) (x₂ := δ) (x₃ := 2) (y₀ := -2) (y₁ := -(1 / 2)) (y₂ := 1 / 2) (y₃ := 2)
    (by linarith) (by linarith) hδ2 (by norm_num) (by norm_num) (by norm_num) (by
      intro p hp
      have hbox := hp.2
      have hp0 : p ≠ 0 := by
        rintro rfl
        exact hbox ⟨⟨by simp; linarith, by simp; linarith⟩, ⟨by norm_num, by norm_num⟩⟩
      exact (((differentiable_pow m).differentiableAt.mul
        ((differentiable_id.const_mul (t : ℂ)).cexp.differentiableAt)).mul
        (differentiableAt_liClockThetaInverseSymbol hp0
          (liClockThetaGenerator_inv_ne_zero hd hdδ hbox))).differentiableWithinAt)
  rw [liClockThetaCausalInverse_eq_borelSeries, ← hinv, hcongr, hframe]

/-- **Growth above any strip bound.**  If `d ≥ 0` bounds every `|Im α_q⁻¹|`, then for every
`d < δ ≤ 2` each fixed derivative of the causal inverse is `O(e^{δ|t|})` at every real clock. -/
theorem exists_abs_iteratedDeriv_liClockThetaCausalInverse_le {d δ : ℝ} (hd0 : 0 ≤ d)
    (hd : ∀ q : XiZeroCopy, |((xiSpectralPoint q)⁻¹).im| ≤ d) (hdδ : d < δ) (hδ2 : δ ≤ 2)
    (m : ℕ) : ∃ C : ℝ, ∀ t : ℝ,
      |iteratedDeriv m liClockThetaCausalInverse t| ≤ C * Real.exp (δ * |t|) := by
  have hδ0 : 0 < δ := by linarith
  set z : ℂ := ((-δ : ℝ) : ℂ) + ((-(1 / 2) : ℝ) : ℂ) * I
  set w : ℂ := ((δ : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * I
  have hcont : ContinuousOn (fun p => p ^ m * liClockThetaInverseSymbol p) (RectangleBorder z w) := by
    intro p hp
    have hbox := not_mem_box_of_mem_thinBorder hp
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact hbox ⟨⟨by simp; linarith, by simp; linarith⟩, ⟨by norm_num, by norm_num⟩⟩
    exact (((differentiable_pow m).differentiableAt.mul (differentiableAt_liClockThetaInverseSymbol
      hp0 (liClockThetaGenerator_inv_ne_zero hd hdδ hbox))).continuousAt).continuousWithinAt
  obtain ⟨K, hK⟩ := (isCompact_rectangleBorder z w).exists_bound_of_continuousOn hcont
  refine ⟨(2 * δ + 1) * K / π, fun t => ?_⟩
  have hrep := two_pi_I_mul_iteratedDeriv_liClockThetaCausalInverse hd hdδ hδ0 hδ2 m t
  have hbound := HTGeometry.norm_rectangleIntegral_le
    (f := fun p => p ^ m * cexp (t * p) * liClockThetaInverseSymbol p) (z := z) (w := w)
    (M := K * Real.exp (δ * |t|)) (fun p hp => by
      have hre := abs_re_le_of_mem_thinBorder hδ0.le hp
      have hexp : ‖cexp ((t : ℂ) * p)‖ ≤ Real.exp (δ * |t|) := by
        rw [Complex.norm_exp]
        refine Real.exp_le_exp.2 ?_
        have : ((t : ℂ) * p).re = t * p.re := by simp
        rw [this]
        calc t * p.re ≤ |t * p.re| := le_abs_self _
          _ = |t| * |p.re| := abs_mul _ _
          _ ≤ |t| * δ := mul_le_mul_of_nonneg_left hre (abs_nonneg _)
          _ = δ * |t| := mul_comm _ _
      have hK' := hK p hp
      rw [mul_right_comm, norm_mul]
      exact mul_le_mul hK' hexp (norm_nonneg _) ((norm_nonneg _).trans hK'))
  rw [← hrep] at hbound
  have hzw : |w.re - z.re| + |w.im - z.im| = 2 * δ + 1 := by
    simp only [z, w, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im, mul_zero,
      mul_one, zero_add, add_zero, sub_self]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by norm_num)]
    ring
  have hnorm : ‖2 * (π : ℂ) * I * ((iteratedDeriv m liClockThetaCausalInverse t : ℝ) : ℂ)‖ =
      2 * π * |iteratedDeriv m liClockThetaCausalInverse t| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  rw [hnorm, hzw] at hbound
  rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
  linarith

/-- **Strict sub-`1/300` growth.**  One `δ < 1/300` bounds every fixed derivative of the causal
inverse: `|u^{(m)}(t)| ≤ C_m e^{δ|t|}` at every real clock. -/
theorem exists_liClockThetaCausalInverse_iteratedDeriv_growth :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 300 ∧ ∀ m : ℕ, ∃ C : ℝ, ∀ t : ℝ,
      |iteratedDeriv m liClockThetaCausalInverse t| ≤ C * Real.exp (δ * |t|) := by
  obtain ⟨d, hd0, hd300, hd⟩ := exists_abs_im_inv_xiSpectralPoint_le
  exact ⟨(d + 1 / 300) / 2, by positivity, by linarith, fun m =>
    exists_abs_iteratedDeriv_liClockThetaCausalInverse_le hd0 hd (by linarith) (by linarith) m⟩

/-! ## The resolvent and the initial jets -/

theorem liClockThetaResolvent_eq_borelSeries :
    liClockThetaResolvent = borelSeries fun n => -liClockThetaInverseBorelCoeff (n + 2) := by
  funext t
  have h2 := iteratedDeriv_two_liClockThetaCausalInverse t
  rw [liClockThetaCausalInverse_eq_borelSeries,
    iteratedDeriv_borelSeries geometricCoeffBound_liClockThetaInverseBorelCoeff] at h2
  unfold borelSeries at h2 ⊢
  simp only [neg_mul, tsum_neg]
  linarith

theorem iteratedDeriv_liClockThetaResolvent (m : ℕ) (t : ℝ) :
    iteratedDeriv m liClockThetaResolvent t = -iteratedDeriv (m + 2) liClockThetaCausalInverse t := by
  have hb : GeometricCoeffBound (fun n => -liClockThetaInverseBorelCoeff (n + 2)) 1 1 := fun n => by
    rw [abs_neg]
    have := geometricCoeffBound_liClockThetaInverseBorelCoeff (n + 2)
    simpa using this
  rw [liClockThetaResolvent_eq_borelSeries, iteratedDeriv_borelSeries hb,
    liClockThetaCausalInverse_eq_borelSeries,
    iteratedDeriv_borelSeries geometricCoeffBound_liClockThetaInverseBorelCoeff]
  unfold borelSeries
  rw [← tsum_neg]
  refine tsum_congr fun n => ?_
  simp only [show n + m + 2 = n + (m + 2) by ring]
  ring

/-- **Resolvent growth.**  Every fixed derivative of `r` is `O(e^{δ|t|})` for one `δ < 1/300`. -/
theorem exists_liClockThetaResolvent_iteratedDeriv_growth :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 300 ∧ ∀ m : ℕ, ∃ C : ℝ, ∀ t : ℝ,
      |iteratedDeriv m liClockThetaResolvent t| ≤ C * Real.exp (δ * |t|) := by
  obtain ⟨δ, hδ0, hδ, h⟩ := exists_liClockThetaCausalInverse_iteratedDeriv_growth
  refine ⟨δ, hδ0, hδ, fun m => ?_⟩
  obtain ⟨C, hC⟩ := h (m + 2)
  exact ⟨C, fun t => by rw [iteratedDeriv_liClockThetaResolvent, abs_neg]; exact hC t⟩

theorem iteratedDeriv_liClockThetaCausalInverse_zero (m : ℕ) :
    iteratedDeriv m liClockThetaCausalInverse 0 = liClockThetaInverseBorelCoeff m := by
  rw [liClockThetaCausalInverse_eq_borelSeries,
    iteratedDeriv_borelSeries geometricCoeffBound_liClockThetaInverseBorelCoeff, borelSeries_zero,
    zero_add]

/-- **Initial jets.**  `u(0) = 0`, `u'(0) = 1`, `u''(0) = 0`, `u'''(0) = -ν_1/2`. -/
theorem liClockThetaCausalInverse_initial_jets :
    iteratedDeriv 0 liClockThetaCausalInverse 0 = 0 ∧
      iteratedDeriv 1 liClockThetaCausalInverse 0 = 1 ∧
      iteratedDeriv 2 liClockThetaCausalInverse 0 = 0 ∧
      iteratedDeriv 3 liClockThetaCausalInverse 0 = -(thetaCuspNormalizedEvenMoment 1 / 2) := by
  simp only [iteratedDeriv_liClockThetaCausalInverse_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact liClockThetaInverseBorelCoeff_even 0
  · rw [show (1 : ℕ) = 2 * 0 + 1 by rfl, liClockThetaInverseBorelCoeff_odd,
      liClockThetaReciprocalCoeff_zero]
  · rw [show (2 : ℕ) = 2 * 1 by rfl, liClockThetaInverseBorelCoeff_even]
  · rw [show (3 : ℕ) = 2 * 1 + 1 by rfl, liClockThetaInverseBorelCoeff_odd,
      liClockThetaReciprocalCoeff_one]

end RHTower

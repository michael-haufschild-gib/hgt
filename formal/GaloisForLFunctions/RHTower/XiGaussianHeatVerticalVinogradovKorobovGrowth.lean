import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalZeroFreeGrowth
import GaloisForLFunctions.RHTower.XiLogDerivVinogradovKorobovPositive

/-!
# Vinogradov–Korobov growth bound for the vertical heat trace

`norm_xiGaussianHeatTraceC_le_zeroFree` turns the de la Vallée Poussin width `1/(58 log|γ|)` into the
saving `exp(-b²/(116 a log(2|b|/a)))` for `ν(a+ib)`.  The mechanism needs only a uniform width on
the window `|γ| ≤ 2|b|/a`.

* `norm_xiGaussianHeatTraceC_le_of_window_width`: if every copy with `|Re z| ≤ X = 2|b|/a` has
  `|Im z| ≤ 1/2 - η`, then
  `‖ν(a+ib)‖ ≤ K(X² + 1/4) exp(a/4 + (1 - 2η) b²/(4a)) + (2K/a) e^{a/2}`.
* `exists_norm_xiGaussianHeatTraceC_le_vinogradovKorobov`: with the corpus Vinogradov–Korobov region
  (`abs_re_sub_half_le_vinogradovKorobov`), for all large `|b|` the width is
  `η = (log X)^{-2/3} (log log X)^{-5/3} / 10⁸`.  The saving becomes
  `exp(-b² (log X)^{-2/3} (log log X)^{-5/3} / (2·10⁸ a))`, against the trivial `exp(b²/(4a))`.

This is the strongest unconditional bound the corpus gives for the HCF single-line producer.  RH
requires `exp(o(|b|))`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- **Generic window bound.**  A uniform zero-free width `η` on the window `|Re z| ≤ X = 2|b|/a`
controls every term of the vertical heat trace. -/
theorem norm_xiGaussianHeatTermC_le_of_window_width {a b η : ℝ} (ha : 0 < a) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / 2)
    (hwin : ∀ q : XiZeroCopy, |(xiSpectralPoint q).re| ≤ 2 * |b| / a →
      |(xiSpectralPoint q).im| ≤ 1 / 2 - η)
    (q : XiZeroCopy) :
    ‖xiGaussianHeatTermC ((a : ℂ) + b * I) q‖ ≤
      (Real.exp (a / 4 + (1 - 2 * η) * (b ^ 2 / (4 * a))) * ((2 * |b| / a) ^ 2 + 1 / 4) +
        2 / a * Real.exp (a / 2)) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  set X : ℝ := 2 * |b| / a
  obtain ⟨h4, hzf⟩ := xiSpectralPoint_im_le_zeroFree q
  set x := (xiSpectralPoint q).re
  set y := (xiSpectralPoint q).im
  have hN : ‖xiSpectralPoint q‖ ^ (2 : ℕ) = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hy : |y| ≤ 1 / 2 := by
    have : 0 < 1 / 58 / Real.log |x| := by
      have : 0 < Real.log |x| := Real.log_pos (by linarith)
      positivity
    linarith
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have := sq_le_sq' (abs_le.1 hy).1 (abs_le.1 hy).2
    linarith
  have hx16 : 16 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hNpos : 0 < x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg y]
  rw [norm_xiGaussianHeatTermC, hN]
  have hre : ((a : ℂ) + b * I).re = a := by simp
  have him : ((a : ℂ) + b * I).im = b := by simp
  have hw_re : (xiSpectralPoint q ^ (2 : ℕ)).re = x ^ 2 - y ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  have hw_im : (xiSpectralPoint q ^ (2 : ℕ)).im = 2 * x * y := by
    rw [pow_two, Complex.mul_im]; ring
  rw [hre, him, hw_re, hw_im]
  set M : ℝ := a / 4 + (1 - 2 * η) * (b ^ 2 / (4 * a))
  have hbxy : b * (2 * x * y) ≤ |b| * |x| * (2 * |y|) := by
    calc b * (2 * x * y) ≤ |b * (2 * x * y)| := le_abs_self _
      _ = |b| * |x| * (2 * |y|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
  have hsplit : ∀ E : ℝ, Real.exp E ≤ Real.exp M * (X ^ 2 + 1 / 4) / (x ^ 2 + y ^ 2) ∨
      Real.exp E ≤ 2 / a * Real.exp (a / 2) / (x ^ 2 + y ^ 2) →
      Real.exp E ≤ (Real.exp M * (X ^ 2 + 1 / 4) + 2 / a * Real.exp (a / 2)) *
        (1 / (x ^ 2 + y ^ 2)) := by
    intro E h
    have h1 : 0 ≤ Real.exp M * (X ^ 2 + 1 / 4) / (x ^ 2 + y ^ 2) := by positivity
    have h2 : 0 ≤ 2 / a * Real.exp (a / 2) / (x ^ 2 + y ^ 2) := by positivity
    have heq : (Real.exp M * (X ^ 2 + 1 / 4) + 2 / a * Real.exp (a / 2)) * (1 / (x ^ 2 + y ^ 2)) =
        Real.exp M * (X ^ 2 + 1 / 4) / (x ^ 2 + y ^ 2) +
          2 / a * Real.exp (a / 2) / (x ^ 2 + y ^ 2) := by ring
    rw [heq]
    rcases h with h | h <;> linarith
  apply hsplit
  rcases le_or_gt |x| X with hxX | hxX
  · left
    set c : ℝ := 1 - 2 * η
    have hc0 : 0 ≤ c := by simp only [c]; linarith
    have hc1 : c ≤ 1 := by simp only [c]; linarith
    have h2y : 2 * |y| ≤ c := by
      have := hwin q hxX
      simp only [c]; linarith
    have hE : -(a * (x ^ 2 - y ^ 2) - b * (2 * x * y)) ≤ M := by
      have hbx : |b| * |x| * (2 * |y|) ≤ |b| * |x| * c :=
        mul_le_mul_of_nonneg_left h2y (by positivity)
      have hsq : -a * x ^ 2 + c * |b| * |x| ≤ c ^ 2 * b ^ 2 / (4 * a) := by
        have key : 0 ≤ 4 * a ^ 2 * x ^ 2 - 4 * a * c * |b| * |x| + c ^ 2 * b ^ 2 := by
          have h := sq_nonneg (2 * a * |x| - c * |b|)
          have e : (2 * a * |x| - c * |b|) ^ 2 =
              4 * a ^ 2 * |x| ^ 2 - 4 * a * c * |b| * |x| + c ^ 2 * |b| ^ 2 := by ring
          rw [e, sq_abs, sq_abs] at h
          exact h
        rw [le_div_iff₀ (by positivity)]
        nlinarith [key]
      have hc2 : c ^ 2 * b ^ 2 / (4 * a) ≤ c * (b ^ 2 / (4 * a)) := by
        have : c ^ 2 ≤ c := by nlinarith
        have hb : 0 ≤ b ^ 2 / (4 * a) := by positivity
        calc c ^ 2 * b ^ 2 / (4 * a) = c ^ 2 * (b ^ 2 / (4 * a)) := by ring
          _ ≤ c * (b ^ 2 / (4 * a)) := mul_le_mul_of_nonneg_right this hb
      simp only [M]
      nlinarith
    have hR : 1 ≤ (X ^ 2 + 1 / 4) / (x ^ 2 + y ^ 2) := by
      rw [le_div_iff₀ hNpos, one_mul]
      have : x ^ 2 ≤ X ^ 2 := by
        have := sq_le_sq' (by linarith [abs_nonneg x, le_abs_self x, neg_abs_le x]) hxX
        rwa [sq_abs] at this
      linarith
    calc Real.exp (-(a * (x ^ 2 - y ^ 2) - b * (2 * x * y)))
        ≤ Real.exp M := Real.exp_le_exp.2 hE
      _ ≤ Real.exp M * ((X ^ 2 + 1 / 4) / (x ^ 2 + y ^ 2)) :=
          le_mul_of_one_le_right (Real.exp_pos _).le hR
      _ = Real.exp M * (X ^ 2 + 1 / 4) / (x ^ 2 + y ^ 2) := by ring
  · right
    have hbx : |b| * |x| ≤ a * x ^ 2 / 2 := by
      have : 2 * |b| ≤ a * |x| := by
        have := hxX
        simp only [X] at this
        rw [div_lt_iff₀ ha] at this
        linarith
      have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
      nlinarith [abs_nonneg x]
    have hy1 : 2 * |y| ≤ 1 := by linarith
    have hE : -(a * (x ^ 2 - y ^ 2) - b * (2 * x * y)) ≤ a / 2 - a / 2 * (x ^ 2 + y ^ 2) := by
      have h1 : |b| * |x| * (2 * |y|) ≤ |b| * |x| :=
        mul_le_of_le_one_right (by positivity) hy1
      nlinarith
    have hpos : 0 < a / 2 * (x ^ 2 + y ^ 2) := by positivity
    calc Real.exp (-(a * (x ^ 2 - y ^ 2) - b * (2 * x * y)))
        ≤ Real.exp (a / 2 - a / 2 * (x ^ 2 + y ^ 2)) := Real.exp_le_exp.2 hE
      _ = Real.exp (a / 2) * Real.exp (-(a / 2 * (x ^ 2 + y ^ 2))) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (a / 2) * (1 / (a / 2 * (x ^ 2 + y ^ 2))) :=
          mul_le_mul_of_nonneg_left (exp_neg_le_inv_of_pos hpos) (Real.exp_pos _).le
      _ = 2 / a * Real.exp (a / 2) / (x ^ 2 + y ^ 2) := by field_simp

theorem norm_xiGaussianHeatTraceC_le_of_window_width {a b η : ℝ} (ha : 0 < a) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / 2)
    (hwin : ∀ q : XiZeroCopy, |(xiSpectralPoint q).re| ≤ 2 * |b| / a →
      |(xiSpectralPoint q).im| ≤ 1 / 2 - η) :
    ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤
      (Real.exp (a / 4 + (1 - 2 * η) * (b ^ 2 / (4 * a))) * ((2 * |b| / a) ^ 2 + 1 / 4) +
        2 / a * Real.exp (a / 2)) * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  have hτ : 0 < ((a : ℂ) + b * I).re := by simpa using ha
  rw [← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm (summable_norm_xiGaussianHeatTermC hτ)).trans
    (Summable.tsum_le_tsum (norm_xiGaussianHeatTermC_le_of_window_width ha hη0 hη1 hwin)
      (summable_norm_xiGaussianHeatTermC hτ) (xiSpectralPoint_inv_sq_summable.mul_left _))

/-- **Vinogradov–Korobov growth.**  For every `a > 0` there is `B₀` such that for `|b| ≥ B₀`
`‖ν(a+ib)‖ ≤ K(X² + 1/4) exp(a/4 + (1 - 2 w(X)) b²/(4a)) + (2K/a) e^{a/2}`,
with `X = 2|b|/a` and `w(X) = (log X)^{-2/3} (log log X)^{-5/3} / 10⁸`. -/
theorem exists_norm_xiGaussianHeatTraceC_le_vinogradovKorobov {a : ℝ} (ha : 0 < a) :
    ∃ B₀ : ℝ, ∀ b : ℝ, B₀ ≤ |b| →
      ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤
        (Real.exp (a / 4 + (1 - 2 * vkHadamardWidth (2 * |b| / a)) * (b ^ 2 / (4 * a))) *
            ((2 * |b| / a) ^ 2 + 1 / 4) + 2 / a * Real.exp (a / 2)) *
          ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  obtain ⟨γ₁, hγ₁e, hvk⟩ := abs_re_sub_half_le_vinogradovKorobov
  have hγ₁4 : 4 ≤ γ₁ := by
    have h1 : (4 : ℝ) ≤ Real.exp (Real.exp 1) := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
      have h3 : Real.exp 2 ≤ Real.exp (Real.exp 1) := Real.exp_le_exp.2 h2
      have h4 : (4 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (2 : ℝ)
        have h5 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith [Real.add_one_le_exp (1 : ℝ)]
      linarith
    linarith
  have hlogγ₁ : 0 < Real.log γ₁ := Real.log_pos (by linarith)
  set ε : ℝ := 1 / 58 / Real.log γ₁
  have hε : 0 < ε := by positivity
  set X₀ : ℝ := max γ₁ (Real.exp (max (Real.exp 1) ((10 ^ 8 * ε) ^ (-(3 : ℝ) / 2))))
  refine ⟨a * X₀ / 2, fun b hb => ?_⟩
  set X : ℝ := 2 * |b| / a
  have hXX₀ : X₀ ≤ X := by
    simp only [X]; rw [le_div_iff₀ ha]; linarith
  have hXγ₁ : γ₁ ≤ X := (le_max_left _ _).trans hXX₀
  have hXe : Real.exp (Real.exp 1) ≤ X := hγ₁e.trans hXγ₁
  have hwε : vkHadamardWidth X ≤ ε := vkHadamardWidth_le hε ((le_max_right _ _).trans hXX₀)
  have hw0 : 0 ≤ vkHadamardWidth X := (vkHadamardWidth_pos hXe).le
  have hw12 : vkHadamardWidth X ≤ 1 / 2 := by
    have : ε ≤ 1 / 2 := by
      simp only [ε]
      rw [div_le_iff₀ hlogγ₁]
      have : Real.log 4 ≤ Real.log γ₁ := Real.log_le_log (by norm_num) hγ₁4
      have : (1 : ℝ) / 29 ≤ Real.log 4 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]
        have : Real.exp (1 / 29) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
        have := Real.exp_one_lt_d9
        linarith
      nlinarith
    linarith
  refine norm_xiGaussianHeatTraceC_le_of_window_width ha hw0 hw12 fun q hq => ?_
  obtain ⟨h4, hzf⟩ := xiSpectralPoint_im_le_zeroFree q
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
  rcases le_or_gt γ₁ |(xiSpectralPoint q).re| with hbig | hsmall
  · -- the Vinogradov–Korobov range
    have hstrip := xi_divisor_support_re_mem_open_unit q.1
    have hxi := xi_eq_zero_of_mem_divisor_support q.1
    have hne1 : (q.1 : ℂ) ≠ 1 := fun h => by rw [h] at hstrip; simp at hstrip
    have hzeta : riemannZeta (q.1 : ℂ) = 0 := (xi_eq_zero_iff hstrip.1 hne1).1 hxi
    rw [hre] at hbig hq
    have h := hvk (q.1 : ℂ) hstrip.1 hstrip.2 hzeta hbig
    have hanti := vkHadamardWidth_anti (hγ₁e.trans hbig) hq
    rw [him, abs_neg]
    linarith
  · -- the low range: the de la Vallée Poussin width already beats `w(X)`
    have hlog : Real.log |(xiSpectralPoint q).re| ≤ Real.log γ₁ :=
      Real.log_le_log (by linarith) hsmall.le
    have hlog0 : 0 < Real.log |(xiSpectralPoint q).re| := Real.log_pos (by linarith)
    have h58 : ε ≤ 1 / 58 / Real.log |(xiSpectralPoint q).re| :=
      div_le_div_of_nonneg_left (by norm_num) hlog0 hlog
    linarith

end

end RHTower

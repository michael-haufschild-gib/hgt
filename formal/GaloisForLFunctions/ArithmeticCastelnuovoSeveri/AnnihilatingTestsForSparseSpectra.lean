import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheTowerDefectCountsTheFrobeniusEigenvalues
import GaloisForLFunctions.RHTower.WeilFullConeHerglotzRightHalfPlane
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity

/-!
# Annihilating tests for sparse spectra

A compactly supported test whose transform vanishes on a prescribed infinite set `A ⊂ ℂ` and at
no prescribed finite set `F` of non-real points exists as soon as `Σ_{a ∈ A} |a|^{-s} < ∞` for some
`s < 1`.

*Ingham bump.* The iterated convolution of the boxes `1_{[−ε_n, ε_n]}/(2ε_n)`,
`ε_n = (n+1)^{-p}` with `p > 1`, converges to a smooth function `φ` supported in
`[−Σε_n, Σε_n]` whose transform is `Φ(z) = Π_n sin(ε_n z)/(ε_n z)`. On the real line
`|Φ(x)| ≤ e^{2 − (|x|/e)^{1/p}}`; off the real line `Φ` does not vanish.

*Annihilator.* With `L_a h = h + (ia)⁻¹ h'`, the transform of `L_{a_{N−1}} ⋯ L_{a_0} φ` is
`Π_{k<N}(1 − z/a_k) Φ(z)`. Since `|Π(1 − x/a_k)| ≤ e^{|x|^s Σ|a_k|^{-s}/s}` on the real line and
`1/p > s`, these tests converge uniformly, inside the support of `φ`, to a `C²` test `g` with
`ĝ = Π_k (1 − z/a_k) · Φ`.
-/

open Complex MeasureTheory Set Filter Topology Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open Zeta23

/-! ### 1. Boxes and the complex sinc -/

/-- The complex sinc `sin w / w`, equal to `1` at `0`. -/
def sincC (w : ℂ) : ℂ := if w = 0 then 1 else Complex.sin w / w

theorem sincC_zero : sincC 0 = 1 := by simp [sincC]

/-- The normalized box `1_{[−ε, ε]} / (2ε)`. -/
def boxTest (ε : ℝ) : ℝ → ℂ := Set.indicator (Icc (-ε) ε) fun _ => ((2 * ε : ℝ)⁻¹ : ℂ)

theorem boxTest_integrable (ε : ℝ) : Integrable (boxTest ε) :=
  (integrableOn_const (isCompact_Icc.measure_lt_top).ne).integrable_indicator measurableSet_Icc

theorem boxTest_hasCompactSupport (ε : ℝ) : HasCompactSupport (boxTest ε) := by
  refine HasCompactSupport.intro isCompact_Icc fun x hx => ?_
  simp [boxTest, Set.indicator_of_notMem hx]

theorem support_boxTest_subset (ε : ℝ) : Function.support (boxTest ε) ⊆ Icc (-ε) ε :=
  Set.support_indicator_subset

/-- **The transform of a box is a sinc**: `paperFT (1_{[−ε,ε]}/(2ε)) z = sin(εz)/(εz)`. -/
theorem paperFT_boxTest {ε : ℝ} (hε : 0 < ε) (z : ℂ) : paperFT (boxTest ε) z = sincC (ε * z) := by
  have hind : paperFT (boxTest ε) z = ((2 * ε : ℝ)⁻¹ : ℂ) * ∫ u in (-ε)..ε, cexp (I * z * u) := by
    simp only [paperFT, boxTest]
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      ← integral_const_mul, ← integral_indicator measurableSet_Icc]
    congr 1
    funext u
    by_cases hu : u ∈ Icc (-ε) ε <;> simp [Set.indicator, hu]
  rw [hind]
  by_cases hz : z = 0
  · subst hz
    simp only [mul_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const, smul_eq_mul,
      mul_one, sincC_zero]
    push_cast
    field_simp
    ring
  · have hIz : I * z ≠ 0 := mul_ne_zero I_ne_zero hz
    have hεz : (ε : ℂ) * z ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hε.ne') hz
    rw [integral_exp_mul_complex hIz, sincC, if_neg hεz, Complex.sin]
    push_cast
    have hε' : (ε : ℂ) ≠ 0 := ofReal_ne_zero.mpr hε.ne'
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring_nf

/-! ### 2. Bounds for the sinc -/

theorem sincC_ofReal (t : ℝ) : sincC (t : ℂ) = ((if t = 0 then 1 else Real.sin t / t : ℝ) : ℂ) := by
  by_cases ht : t = 0
  · subst ht; simp [sincC]
  · have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht
    simp [sincC, ht, ht', Complex.ofReal_sin]

theorem norm_sincC_ofReal_le_one (t : ℝ) : ‖sincC (t : ℂ)‖ ≤ 1 := by
  rw [sincC_ofReal, Complex.norm_real, Real.norm_eq_abs]
  split_ifs with ht
  · simp
  · rw [abs_div]
    exact div_le_one_of_le₀ (Real.abs_sin_le_abs) (abs_nonneg _)

theorem norm_sincC_ofReal_le_inv (t : ℝ) (ht : t ≠ 0) : ‖sincC (t : ℂ)‖ ≤ |t|⁻¹ := by
  rw [sincC_ofReal, if_neg ht, Complex.norm_real, Real.norm_eq_abs, abs_div, div_eq_mul_inv]
  have := Real.abs_sin_le_one t
  exact mul_le_of_le_one_left (inv_nonneg.mpr (abs_nonneg _)) this

/-- Near the origin `sin w / w` is within `|w|²` of `1`. -/
theorem norm_sincC_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖sincC w - 1‖ ≤ ‖w‖ ^ 2 := by
  by_cases h0 : w = 0
  · subst h0; simp [sincC]
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr h0
  have hb := Complex.sin_bound hw
  have hsin : ‖Complex.sin w - w‖ ≤ ‖w‖ ^ 3 := by
    calc ‖Complex.sin w - w‖ = ‖(Complex.sin w - (w - w ^ 3 / 6)) - w ^ 3 / 6‖ := by ring_nf
      _ ≤ ‖Complex.sin w - (w - w ^ 3 / 6)‖ + ‖w ^ 3 / 6‖ := norm_sub_le _ _
      _ ≤ ‖w‖ ^ 4 * (5 / 96) + ‖w‖ ^ 3 / 6 := by
          gcongr
          rw [norm_div, norm_pow]; norm_num
      _ ≤ ‖w‖ ^ 3 := by
          have h4 : ‖w‖ ^ 4 ≤ ‖w‖ ^ 3 := pow_le_pow_of_le_one (norm_nonneg _) hw (by norm_num)
          nlinarith [pow_nonneg (norm_nonneg w) 3]
  rw [sincC, if_neg h0, show Complex.sin w / w - 1 = (Complex.sin w - w) / w by
    field_simp, norm_div]
  rw [div_le_iff₀ hw0]
  calc ‖Complex.sin w - w‖ ≤ ‖w‖ ^ 3 := hsin
    _ = ‖w‖ ^ 2 * ‖w‖ := by ring

/-- The sinc vanishes only on the real line. -/
theorem sincC_ne_zero_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) : sincC w ≠ 0 := by
  have h0 : w ≠ 0 := fun h => hw (by rw [h, Complex.zero_im])
  rw [sincC, if_neg h0]
  refine div_ne_zero ?_ h0
  intro hs
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
  apply hw
  rw [hk]
  simp

/-! ### 3. Iterated convolutions of boxes -/

/-- The box widths `ε_n = (n+1)^{-p}`. -/
def inghamWidth (p : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-p)

theorem inghamWidth_pos (p : ℝ) (n : ℕ) : 0 < inghamWidth p n := by
  unfold inghamWidth; positivity

/-- The partial Ingham bumps `box_0 ⋆ ⋯ ⋆ box_n`. -/
def inghamPartial (p : ℝ) : ℕ → ℝ → ℂ
  | 0 => boxTest (inghamWidth p 0)
  | n + 1 => convolution (inghamPartial p n) (boxTest (inghamWidth p (n + 1)))
      (ContinuousLinearMap.mul ℝ ℂ) volume

/-- The half-width `Σ_{k ≤ n} ε_k` of the support of the `n`-th partial bump. -/
def inghamRadius (p : ℝ) (n : ℕ) : ℝ := ∑ k ∈ range (n + 1), inghamWidth p k

theorem inghamPartial_integrable_hasCompactSupport (p : ℝ) (n : ℕ) :
    Integrable (inghamPartial p n) ∧ HasCompactSupport (inghamPartial p n) := by
  induction n with
  | zero => exact ⟨boxTest_integrable _, boxTest_hasCompactSupport _⟩
  | succ n ih =>
    exact ⟨ih.1.integrable_convolution _ (boxTest_integrable _),
      ih.2.convolution _ (boxTest_hasCompactSupport _)⟩

theorem support_inghamPartial_subset (p : ℝ) (n : ℕ) :
    Function.support (inghamPartial p n) ⊆ Icc (-inghamRadius p n) (inghamRadius p n) := by
  induction n with
  | zero =>
    simpa [inghamRadius] using support_boxTest_subset (inghamWidth p 0)
  | succ n ih =>
    refine (support_convolution_subset _).trans ?_
    refine (Set.add_subset_add ih (support_boxTest_subset _)).trans ?_
    rw [Set.Icc_add_Icc (by linarith [(inghamRadius p n).le_refl]) (by
      linarith [inghamWidth_pos p (n + 1)])]
    have : inghamRadius p (n + 1) = inghamRadius p n + inghamWidth p (n + 1) := by
      simp [inghamRadius, Finset.sum_range_succ]
    rw [this, neg_add]

/-- **The transform of a partial bump is a finite sinc product.** -/
theorem paperFT_inghamPartial (p : ℝ) (n : ℕ) (z : ℂ) :
    paperFT (inghamPartial p n) z = ∏ k ∈ range (n + 1), sincC (inghamWidth p k * z) := by
  induction n with
  | zero => simp [inghamPartial, paperFT_boxTest (inghamWidth_pos p 0)]
  | succ n ih =>
    have h := inghamPartial_integrable_hasCompactSupport p n
    rw [inghamPartial, RHTower.WeilHerglotz.paperFT_convolution h.1 (boxTest_integrable _) h.2
      (boxTest_hasCompactSupport _), ih, paperFT_boxTest (inghamWidth_pos p (n + 1)),
      Finset.prod_range_succ]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

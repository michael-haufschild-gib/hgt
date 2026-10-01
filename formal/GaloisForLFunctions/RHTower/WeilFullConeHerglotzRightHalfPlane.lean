import GaloisForLFunctions.RHTower.WeilPrimitiveSetMeanSquare
import GaloisForLFunctions.RHTower.PoissonDigammaShiftedReproduction
import GaloisForLFunctions.RHTower.WeilDeletionTestKit

/-!
# Full-cone Weil positivity makes the Weil function Herglotz on `Re s > 1`

For a real weight system `lam` put

`Φ_lam(s) = ½ψ(s/2) − ½ log π + 1/s + 1/(s−1) − Σ_{n≥2} lam(n) n^{−s}`,

the completed logarithmic derivative attached to `ζ`'s archimedean datum (for `lam = Λ` it is
`ξ'/ξ`).  **Theorem** (`re_weilFunction_nonneg`).  If `lam` is full-cone Weil-positive, then
`Re Φ_lam(s) ≥ 0` for every `s` with `Re s > 1`.

**Proof.**  Write `s = ½ + w`, `w = b + it`, `b > ½`.  The one-sided exponential
`h(u) = e^{−wu}1_{u>0}` has autocorrelation `K(x) = e^{−b|x|}e^{−itx}/(2b)` and transform
`ĥ(z) = 1/(w − iz)`.  The tests `h_j = ρ_j ⋆ (e^{−wu}1_{[0,j+1]})`, with `ρ_j` a normalised bump of
radius `1/(j+1)`, are smooth and compactly supported, so Weil positivity applies to `h_j ⋆ h̃_j`.
As `j → ∞`:
* the pole term `ĥ_j(i/2)conj ĥ_j(−i/2) + c.c.` tends to `Re(1/s + 1/(s−1))/b` (this needs
  `b > ½`);
* the prime term tends to `Σ lam(n)n^{−½}(K(log n) + K(−log n)) = Re Σ lam(n)n^{−s}/b`, dominated
  by `Σ|lam(n)|n^{−Re s}`, which converges on the Weil cone;
* the archimedean term `(1/2π)∫|ĥ_j|²γ` tends to `(1/2π)∫γ(r)/(b² + (r−t)²) dr`, dominated by
  `|ĥ_j| ≤ 2|ĥ|`; this is the Poisson integral of `Re ψ(¼ + ir/2) − log π` at height `b` and
  centre `t`, which is `Re ψ(s/2) − log π`.
The limit of the nonnegative real parts is `Re Φ_lam(s)/b`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.WeilHerglotz

/-! ## Mollifiers -/

/-- The bump of outer radius `1/(j+1)` around `0`. -/
def bumpOf (j : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1 / (2 * ((j : ℝ) + 1))
  rOut := 1 / ((j : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) h]
    linarith

/-- The normalised mollifier of radius `1/(j+1)`. -/
def mollifier (j : ℕ) (x : ℝ) : ℝ := (bumpOf j).normed volume x

/-- The mollifier as a complex function. -/
def mollC (j : ℕ) (x : ℝ) : ℂ := (mollifier j x : ℂ)

theorem mollifier_nonneg (j : ℕ) (x : ℝ) : 0 ≤ mollifier j x := (bumpOf j).nonneg_normed x

theorem integral_mollifier (j : ℕ) : ∫ x, mollifier j x = 1 := (bumpOf j).integral_normed

theorem integrable_mollifier (j : ℕ) : Integrable (mollifier j) := (bumpOf j).integrable_normed

theorem mollifier_eq_zero (j : ℕ) {x : ℝ} (hx : 1 / ((j : ℝ) + 1) ≤ |x|) : mollifier j x = 0 := by
  by_contra h
  have hmem : x ∈ Function.support (mollifier j) := h
  have hsupp := (bumpOf j).support_normed_eq (μ := volume)
  unfold mollifier at hmem
  rw [hsupp, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
  have hr : (bumpOf j).rOut = 1 / ((j : ℝ) + 1) := rfl
  rw [hr] at hmem
  linarith

theorem hasCompactSupport_mollC (j : ℕ) : HasCompactSupport (mollC j) :=
  ((bumpOf j).hasCompactSupport_normed (μ := volume)).comp_left Complex.ofReal_zero

theorem contDiff_mollC (j : ℕ) : ContDiff ℝ 2 (mollC j) :=
  Complex.ofRealCLM.contDiff.comp ((bumpOf j).contDiff_normed (μ := volume) (n := 2))

theorem integrable_mollC (j : ℕ) : Integrable (mollC j) :=
  (integrable_mollifier j).ofReal

theorem integral_mollC (j : ℕ) : ∫ x, mollC j x = 1 := by
  unfold mollC
  rw [integral_complex_ofReal, integral_mollifier]
  simp

/-! ## Truncated one-sided exponentials -/

/-- `e^{−wu}` on `[0, L]`, zero elsewhere. -/
def truncExp (w : ℂ) (L : ℝ) : ℝ → ℂ := (Icc 0 L).indicator fun u => cexp (-(w * u))

theorem integrable_truncExp (w : ℂ) (L : ℝ) : Integrable (truncExp w L) :=
  ((by fun_prop : Continuous fun u : ℝ => cexp (-(w * u))).integrableOn_Icc).integrable_indicator
    measurableSet_Icc

theorem hasCompactSupport_truncExp (w : ℂ) (L : ℝ) : HasCompactSupport (truncExp w L) :=
  HasCompactSupport.intro isCompact_Icc fun _ hu => indicator_of_notMem hu _

theorem norm_cexp_neg_mul (w : ℂ) (u : ℝ) : ‖cexp (-(w * u))‖ = Real.exp (-(w.re * u)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem norm_truncExp_le (w : ℂ) (L u : ℝ) :
    ‖truncExp w L u‖ ≤ (Ici (0 : ℝ)).indicator (fun u => Real.exp (-(w.re * u))) u := by
  unfold truncExp
  by_cases hu : u ∈ Icc 0 L
  · rw [indicator_of_mem hu, indicator_of_mem (show u ∈ Ici (0 : ℝ) from hu.1),
      norm_cexp_neg_mul]
  · rw [indicator_of_notMem hu, norm_zero]
    exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) u

/-! ## The tests -/

/-- The smooth test `ρ_j ⋆ (e^{−wu}1_{[0,j+1]})`. -/
def testFn (w : ℂ) (j : ℕ) : ℝ → ℂ :=
  convolution (mollC j) (truncExp w ((j : ℝ) + 1)) (ContinuousLinearMap.mul ℝ ℂ) volume

theorem testFn_apply (w : ℂ) (j : ℕ) (x : ℝ) :
    testFn w j x = ∫ y, mollC j y * truncExp w ((j : ℝ) + 1) (x - y) := by
  rw [testFn, convolution_def]
  simp only [ContinuousLinearMap.mul_apply']

theorem contDiff_testFn (w : ℂ) (j : ℕ) : ContDiff ℝ 2 (testFn w j) :=
  (hasCompactSupport_mollC j).contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ)
    (contDiff_mollC j) (integrable_truncExp w _).locallyIntegrable

theorem hasCompactSupport_testFn (w : ℂ) (j : ℕ) : HasCompactSupport (testFn w j) :=
  (hasCompactSupport_mollC j).convolution (ContinuousLinearMap.mul ℝ ℂ)
    (hasCompactSupport_truncExp w _)

/-! ## Transforms -/

theorem integrable_mul_cexp {f : ℝ → ℂ} (hf : Integrable f) (hfc : HasCompactSupport f) (z : ℂ) :
    Integrable fun x : ℝ => f x * cexp (I * z * x) := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  refine (hf.norm.const_mul (Real.exp (R * |z.im|))).mono'
    (hf.aestronglyMeasurable.mul (by fun_prop : Continuous fun x : ℝ =>
      cexp (I * z * x)).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  by_cases hx : x ∈ Function.support f
  · have hxR : |x| ≤ R := by
      have := hR (subset_tsupport f hx)
      rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    calc ‖f x‖ * ‖cexp (I * z * x)‖ ≤ ‖f x‖ * Real.exp (R * |z.im|) := by
          gcongr; exact WeilDeletion.norm_exp_I_mul_le hxR
      _ = Real.exp (R * |z.im|) * ‖f x‖ := by ring
  · rw [Function.notMem_support.mp hx]
    simp

/-- **Transform of a convolution.** -/
theorem paperFT_convolution {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (z : ℂ) :
    paperFT (convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume) z =
      paperFT f z * paperFT g z := by
  set F : ℝ → ℂ := fun x => f x * cexp (I * z * x) with hF
  set G : ℝ → ℂ := fun x => g x * cexp (I * z * x) with hG
  have hconv : ∀ x : ℝ, convolution F G (ContinuousLinearMap.mul ℝ ℂ) volume x =
      convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume x * cexp (I * z * x) := by
    intro x
    rw [convolution_def, convolution_def]
    simp only [ContinuousLinearMap.mul_apply', hF, hG]
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have e : cexp (I * z * t) * cexp (I * z * ((x - t : ℝ) : ℂ)) = cexp (I * z * x) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only
    linear_combination (f t * g (x - t)) * e
  unfold paperFT
  have hint : ∫ x : ℝ, convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume x * cexp (I * z * x) =
      ∫ x : ℝ, convolution F G (ContinuousLinearMap.mul ℝ ℂ) volume x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    rw [hconv]
  rw [hint, integral_convolution (ContinuousLinearMap.mul ℝ ℂ)
    (integrable_mul_cexp hf hfc z) (integrable_mul_cexp hg hgc z)]
  simp only [ContinuousLinearMap.mul_apply']

theorem paperFT_testFn (w : ℂ) (j : ℕ) (z : ℂ) :
    paperFT (testFn w j) z = paperFT (mollC j) z * paperFT (truncExp w ((j : ℝ) + 1)) z :=
  paperFT_convolution (integrable_mollC j) (integrable_truncExp w _) (hasCompactSupport_mollC j)
    (hasCompactSupport_truncExp w _) z

/-- The transform of a truncated exponential. -/
theorem paperFT_truncExp (w : ℂ) {L : ℝ} (hL : 0 ≤ L) (z : ℂ) (hz : w - I * z ≠ 0) :
    paperFT (truncExp w L) z = (1 - cexp (-((w - I * z) * L))) / (w - I * z) := by
  unfold paperFT truncExp
  have hind : ∀ u : ℝ, (Icc 0 L).indicator (fun u => cexp (-(w * u))) u * cexp (I * z * u) =
      (Icc 0 L).indicator (fun u : ℝ => cexp (-(w - I * z) * u)) u := by
    intro u
    by_cases hu : u ∈ Icc 0 L
    · rw [indicator_of_mem hu, indicator_of_mem hu, ← Complex.exp_add]
      congr 1
      ring
    · rw [indicator_of_notMem hu, indicator_of_notMem hu, zero_mul]
  rw [integral_congr_ae (Eventually.of_forall hind), integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL,
    integral_exp_mul_complex (neg_ne_zero.mpr hz)]
  have hz' : -(w - I * z) ≠ 0 := neg_ne_zero.mpr hz
  field_simp
  push_cast
  ring_nf
  rw [Complex.exp_zero]
  ring

theorem re_sub_I_mul_ofReal (w : ℂ) (r : ℝ) : (w - I * (r : ℂ)).re = w.re := by
  simp [Complex.sub_re, Complex.mul_re]

theorem norm_paperFT_truncExp_le {w : ℂ} (hw : 0 < w.re) {L : ℝ} (hL : 0 ≤ L) (r : ℝ) :
    ‖paperFT (truncExp w L) r‖ ≤ 2 / ‖w - I * (r : ℂ)‖ := by
  have hne : w - I * (r : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [re_sub_I_mul_ofReal] at this
    simp at this
    linarith
  rw [paperFT_truncExp w hL r hne, norm_div]
  refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖1 - cexp (-((w - I * (r : ℂ)) * L))‖ ≤ ‖(1 : ℂ)‖ + ‖cexp (-((w - I * (r : ℂ)) * L))‖ :=
        norm_sub_le _ _
    _ ≤ 2 := by
      rw [norm_one, Complex.norm_exp]
      have : (-((w - I * (r : ℂ)) * (L : ℂ))).re = -(w.re * L) := by
        simp [Complex.mul_re, Complex.sub_re]
      rw [this]
      have : Real.exp (-(w.re * L)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      linarith

theorem tendsto_paperFT_truncExp {w z : ℂ} (hz : 0 < (w - I * z).re) :
    Tendsto (fun j : ℕ => paperFT (truncExp w ((j : ℝ) + 1)) z) atTop (𝓝 (1 / (w - I * z))) := by
  have hne : w - I * z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have heq : ∀ j : ℕ, paperFT (truncExp w ((j : ℝ) + 1)) z =
      (1 - cexp (-((w - I * z) * (((j : ℝ) + 1 : ℝ) : ℂ)))) / (w - I * z) := fun j =>
    paperFT_truncExp w (by positivity) z hne
  simp_rw [heq]
  have hexp : Tendsto (fun j : ℕ => cexp (-((w - I * z) * (((j : ℝ) + 1 : ℝ) : ℂ)))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hn : ∀ j : ℕ, ‖cexp (-((w - I * z) * (((j : ℝ) + 1 : ℝ) : ℂ)))‖ =
        Real.exp (-((w - I * z).re * ((j : ℝ) + 1))) := by
      intro j
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
    simp_rw [hn]
    have hlin : Tendsto (fun j : ℕ => (w - I * z).re * ((j : ℝ) + 1)) atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop hz
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have := (tendsto_const_nhds (x := (1 : ℂ))).sub hexp |>.div_const (w - I * z)
  simpa using this

/-! ## The mollifier transform -/

theorem norm_mollC_mul_cexp (j : ℕ) (r x : ℝ) :
    ‖mollC j x * cexp (I * (r : ℂ) * x)‖ = mollifier j x := by
  rw [norm_mul, mollC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mollifier_nonneg j x)]
  have : I * (r : ℂ) * (x : ℂ) = ((r * x : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem norm_paperFT_mollC_le_one (j : ℕ) (r : ℝ) : ‖paperFT (mollC j) r‖ ≤ 1 := by
  unfold paperFT
  calc ‖∫ x, mollC j x * cexp (I * (r : ℂ) * x)‖ ≤ ∫ x, mollifier j x :=
        norm_integral_le_of_norm_le (integrable_mollifier j)
          (Eventually.of_forall fun x => (norm_mollC_mul_cexp j r x).le)
    _ = 1 := integral_mollifier j

theorem norm_paperFT_mollC_sub_one_le (j : ℕ) {z : ℂ} (hz : ‖z‖ ≤ (j : ℝ) + 1) :
    ‖paperFT (mollC j) z - 1‖ ≤ 2 * ‖z‖ / ((j : ℝ) + 1) := by
  have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have heq : paperFT (mollC j) z - 1 = ∫ x, mollC j x * (cexp (I * z * x) - 1) := by
    have h1 : ∫ x, mollC j x * (cexp (I * z * x) - 1) =
        (∫ x, mollC j x * cexp (I * z * x)) - ∫ x, mollC j x := by
      rw [← integral_sub (integrable_mul_cexp (integrable_mollC j) (hasCompactSupport_mollC j) z)
        (integrable_mollC j)]
      congr 1
      ext x
      ring
    rw [h1, integral_mollC]
    rfl
  rw [heq]
  refine (norm_integral_le_of_norm_le ((integrable_mollifier j).mul_const (2 * ‖z‖ / ((j : ℝ) + 1)))
    (Eventually.of_forall fun x => ?_)).trans (le_of_eq ?_)
  · rw [norm_mul, mollC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mollifier_nonneg j x)]
    by_cases hx : 1 / ((j : ℝ) + 1) ≤ |x|
    · rw [mollifier_eq_zero j hx]
      simp
    · push Not at hx
      refine mul_le_mul_of_nonneg_left ?_ (mollifier_nonneg j x)
      have hnorm : ‖I * z * (x : ℂ)‖ = ‖z‖ * |x| := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have hsmall : ‖z‖ * |x| ≤ ‖z‖ / ((j : ℝ) + 1) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left hx.le (norm_nonneg z)
      have hle1 : ‖I * z * (x : ℂ)‖ ≤ 1 := by
        rw [hnorm]
        refine hsmall.trans ?_
        rw [div_le_one hj0]
        exact hz
      calc ‖cexp (I * z * x) - 1‖ ≤ 2 * ‖I * z * (x : ℂ)‖ := Complex.norm_exp_sub_one_le hle1
        _ ≤ 2 * ‖z‖ / ((j : ℝ) + 1) := by
          rw [hnorm, mul_div_assoc]
          linarith
  · rw [integral_mul_const, integral_mollifier, one_mul]

theorem tendsto_paperFT_mollC (z : ℂ) :
    Tendsto (fun j : ℕ => paperFT (mollC j) z) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun j : ℕ => 2 * ‖z‖ * (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * ‖z‖)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop ⌈‖z‖⌉₊] with j hj
  have hz : ‖z‖ ≤ (j : ℝ) + 1 := by
    have := Nat.le_ceil ‖z‖
    have hj' : (⌈‖z‖⌉₊ : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  refine (norm_paperFT_mollC_sub_one_le j hz).trans (le_of_eq ?_)
  ring

/-! ## A uniform majorant for the tests -/

/-- `e^{b}e^{−bu}1_{u ≥ −1}`. -/
def majorant (b u : ℝ) : ℝ := (Ici (-1 : ℝ)).indicator (fun u => Real.exp b * Real.exp (-b * u)) u

theorem majorant_nonneg (b u : ℝ) : 0 ≤ majorant b u :=
  indicator_nonneg (fun _ _ => by positivity) u

theorem integrable_majorant {b : ℝ} (hb : 0 < b) : Integrable (majorant b) := by
  unfold majorant
  rw [integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
  exact (exp_neg_integrableOn_Ioi (-1) hb).const_mul (Real.exp b)

theorem majorant_le {b : ℝ} (hb : 0 ≤ b) (u : ℝ) : majorant b u ≤ Real.exp (2 * b) := by
  unfold majorant
  by_cases hu : u ∈ Ici (-1 : ℝ)
  · rw [indicator_of_mem hu, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have : -1 ≤ u := hu
    nlinarith
  · rw [indicator_of_notMem hu]
    positivity

theorem norm_testFn_le {w : ℂ} (hw : 0 ≤ w.re) (j : ℕ) (u : ℝ) :
    ‖testFn w j u‖ ≤ majorant w.re u := by
  rw [testFn_apply]
  refine (norm_integral_le_of_norm_le ((integrable_mollifier j).mul_const (majorant w.re u))
    (Eventually.of_forall fun y => ?_)).trans (le_of_eq ?_)
  · rw [norm_mul, mollC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mollifier_nonneg j y)]
    by_cases hy : 1 / ((j : ℝ) + 1) ≤ |y|
    · rw [mollifier_eq_zero j hy]
      simp
    · push Not at hy
      have hy1 : |y| < 1 := hy.trans_le (by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
      refine mul_le_mul_of_nonneg_left ((norm_truncExp_le w _ (u - y)).trans ?_)
        (mollifier_nonneg j y)
      by_cases huy : u - y ∈ Ici (0 : ℝ)
      · rw [indicator_of_mem huy]
        have hu : u ∈ Ici (-1 : ℝ) := by
          have h1 : 0 ≤ u - y := huy
          have h2 : y ≤ |y| := le_abs_self y
          show -1 ≤ u
          linarith [neg_abs_le y]
        rw [majorant, indicator_of_mem hu, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have : y ≤ 1 := (le_abs_self y).trans hy1.le
        nlinarith
      · rw [indicator_of_notMem huy]
        exact majorant_nonneg _ _
  · rw [integral_mul_const, integral_mollifier, one_mul]

/-! ## Pointwise convergence of the tests -/

/-- The one-sided exponential `e^{−wu}1_{u>0}`. -/
def oneSidedExp (w : ℂ) (u : ℝ) : ℂ := if 0 < u then cexp (-(w * u)) else 0

theorem eventually_small_large (u : ℝ) (hu : 0 < u) :
    ∀ᶠ j : ℕ in atTop, 1 / ((j : ℝ) + 1) < u ∧ u + 1 ≤ (j : ℝ) + 1 := by
  have h1 : ∀ᶠ j : ℕ in atTop, 1 / ((j : ℝ) + 1) < u :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hu)
  have h2 : ∀ᶠ j : ℕ in atTop, u + 1 ≤ (j : ℝ) + 1 := by
    filter_upwards [eventually_ge_atTop ⌈u⌉₊] with j hj
    have := Nat.le_ceil u
    have hj' : (⌈u⌉₊ : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  exact h1.and h2

theorem testFn_eq_of_pos {w : ℂ} {u : ℝ} {j : ℕ} (hsmall : 1 / ((j : ℝ) + 1) < u)
    (hlarge : u + 1 ≤ (j : ℝ) + 1) :
    testFn w j u = cexp (-(w * u)) * paperFT (mollC j) (-I * w) := by
  rw [testFn_apply, paperFT, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  by_cases hy : 1 / ((j : ℝ) + 1) ≤ |y|
  · simp [mollC, mollifier_eq_zero j hy]
  · push Not at hy
    have hy1 : |y| < 1 := hy.trans_le (by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
    have hmem : u - y ∈ Icc (0 : ℝ) ((j : ℝ) + 1) := by
      constructor
      · linarith [le_abs_self y]
      · linarith [neg_abs_le y]
    rw [truncExp, indicator_of_mem hmem]
    have e : cexp (-(w * ((u - y : ℝ) : ℂ))) = cexp (-(w * u)) * cexp (I * (-I * w) * y) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [e]
    ring

theorem testFn_eq_zero_of_neg {w : ℂ} {u : ℝ} {j : ℕ} (hsmall : 1 / ((j : ℝ) + 1) ≤ -u) :
    testFn w j u = 0 := by
  rw [testFn_apply]
  refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans (integral_zero ℝ ℂ)
  by_cases hy : 1 / ((j : ℝ) + 1) ≤ |y|
  · simp [mollC, mollifier_eq_zero j hy]
  · push Not at hy
    have hnot : u - y ∉ Icc (0 : ℝ) ((j : ℝ) + 1) := by
      intro h
      have := h.1
      linarith [neg_abs_le y]
    rw [truncExp, indicator_of_notMem hnot, mul_zero]

theorem tendsto_testFn (w : ℂ) {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun j : ℕ => testFn w j u) atTop (𝓝 (oneSidedExp w u)) := by
  rcases lt_or_gt_of_ne hu with hneg | hpos
  · have hev : ∀ᶠ j : ℕ in atTop, testFn w j u = 0 := by
      have h1 : ∀ᶠ j : ℕ in atTop, 1 / ((j : ℝ) + 1) < -u :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds (by linarith))
      filter_upwards [h1] with j hj
      exact testFn_eq_zero_of_neg hj.le
    rw [oneSidedExp, if_neg (not_lt.mpr hneg.le)]
    exact tendsto_const_nhds.congr' (hev.mono fun j hj => hj.symm)
  · have hev : ∀ᶠ j : ℕ in atTop, testFn w j u = cexp (-(w * u)) * paperFT (mollC j) (-I * w) := by
      filter_upwards [eventually_small_large u hpos] with j hj
      exact testFn_eq_of_pos hj.1 hj.2
    rw [oneSidedExp, if_pos hpos]
    have hlim := (tendsto_paperFT_mollC (-I * w)).const_mul (cexp (-(w * u)))
    rw [mul_one] at hlim
    exact hlim.congr' (hev.mono fun j hj => hj.symm)

theorem continuous_testFn (w : ℂ) (j : ℕ) : Continuous (testFn w j) :=
  (contDiff_testFn w j).continuous

/-! ## The autocorrelations -/

/-- The autocorrelation `h_j ⋆ h̃_j` of a test. -/
def autoCorr (w : ℂ) (j : ℕ) : ℝ → ℂ := EF.weilTest (testFn w j) (testFn w j)

theorem autoCorr_apply (w : ℂ) (j : ℕ) (x : ℝ) :
    autoCorr w j x = ∫ t, testFn w j t * conj (testFn w j (t - x)) := by
  rw [autoCorr, EF.weilTest, convolution_def]
  simp only [ContinuousLinearMap.mul_apply', EF.tilde, neg_sub]

/-- The autocorrelation of the one-sided exponential. -/
def oneSidedCorr (w : ℂ) (x : ℝ) : ℂ := ∫ t, oneSidedExp w t * conj (oneSidedExp w (t - x))

theorem majorant_mul_le_of_nonneg {b : ℝ} (hb : 0 ≤ b) {x : ℝ} (hx : 0 ≤ x) (t : ℝ) :
    majorant b t * majorant b (t - x) ≤ Real.exp (2 * b) * Real.exp (-(b * x)) * majorant b (t - x) := by
  by_cases ht : t - x ∈ Ici (-1 : ℝ)
  · refine mul_le_mul_of_nonneg_right ?_ (majorant_nonneg b _)
    have htt : t ∈ Ici (-1 : ℝ) := by
      have : -1 ≤ t - x := ht
      show -1 ≤ t
      linarith
    rw [majorant, indicator_of_mem htt, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have : -1 ≤ t - x := ht
    nlinarith
  · have h0 : majorant b (t - x) = 0 := indicator_of_notMem ht _
    rw [h0]
    simp

theorem majorant_mul_le_of_nonpos {b : ℝ} (hb : 0 ≤ b) {x : ℝ} (hx : x ≤ 0) (t : ℝ) :
    majorant b t * majorant b (t - x) ≤ Real.exp (2 * b) * Real.exp (-(b * |x|)) * majorant b t := by
  by_cases ht : t ∈ Ici (-1 : ℝ)
  · rw [mul_comm (majorant b t)]
    refine mul_le_mul_of_nonneg_right ?_ (majorant_nonneg b _)
    have htt : t - x ∈ Ici (-1 : ℝ) := by
      have : -1 ≤ t := ht
      show -1 ≤ t - x
      linarith
    rw [majorant, indicator_of_mem htt, ← Real.exp_add, ← Real.exp_add, abs_of_nonpos hx]
    refine Real.exp_le_exp.mpr ?_
    have : -1 ≤ t := ht
    nlinarith
  · have h0 : majorant b t = 0 := indicator_of_notMem ht _
    rw [h0]
    simp

theorem norm_autoCorr_le {w : ℂ} (hw : 0 < w.re) (j : ℕ) (x : ℝ) :
    ‖autoCorr w j x‖ ≤
      Real.exp (2 * w.re) * (∫ u, majorant w.re u) * Real.exp (-(w.re * |x|)) := by
  set b := w.re with hbdef
  have hb0 : 0 ≤ b := hw.le
  rw [autoCorr_apply]
  have hpt : ∀ t, ‖testFn w j t * conj (testFn w j (t - x))‖ ≤ majorant b t * majorant b (t - x) := by
    intro t
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (norm_testFn_le hb0 j t) (norm_testFn_le hb0 j _) (norm_nonneg _)
      (majorant_nonneg b t)
  rcases le_total 0 x with hx | hx
  · have hint : Integrable fun t => Real.exp (2 * b) * Real.exp (-(b * x)) * majorant b (t - x) :=
      ((integrable_majorant hw).comp_sub_right x).const_mul _
    refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun t =>
      (hpt t).trans (majorant_mul_le_of_nonneg hb0 hx t))).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_sub_right_eq_self (fun t => majorant b t) x,
      abs_of_nonneg hx]
    ring
  · have hint : Integrable fun t => Real.exp (2 * b) * Real.exp (-(b * |x|)) * majorant b t :=
      (integrable_majorant hw).const_mul _
    refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun t =>
      (hpt t).trans (majorant_mul_le_of_nonpos hb0 hx t))).trans (le_of_eq ?_)
    rw [integral_const_mul]
    ring

theorem ae_ne_real (a : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ a := by
  rw [ae_iff]
  simp [measure_singleton]

theorem tendsto_autoCorr {w : ℂ} (hw : 0 < w.re) (x : ℝ) :
    Tendsto (fun j : ℕ => autoCorr w j x) atTop (𝓝 (oneSidedCorr w x)) := by
  set b := w.re with hbdef
  have hb0 : 0 ≤ b := hw.le
  simp_rw [autoCorr_apply]
  refine tendsto_integral_of_dominated_convergence
    (fun t => Real.exp (2 * b) * majorant b (t - x)) (fun j => ?_)
    (((integrable_majorant hw).comp_sub_right x).const_mul _) (fun j => ?_) ?_
  · exact ((continuous_testFn w j).mul
      (Complex.continuous_conj.comp ((continuous_testFn w j).comp
        (continuous_id.sub continuous_const)))).aestronglyMeasurable
  · refine Eventually.of_forall fun t => ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul ((norm_testFn_le hb0 j t).trans (majorant_le hb0 t))
      (norm_testFn_le hb0 j _) (norm_nonneg _) (Real.exp_pos _).le
  · filter_upwards [ae_ne_real 0, ae_ne_real x] with t ht0 htx
    exact (tendsto_testFn w ht0).mul
      ((Complex.continuous_conj.tendsto _).comp (tendsto_testFn w (sub_ne_zero.mpr htx)))

/-- The autocorrelation of the one-sided exponential in closed form. -/
theorem oneSidedCorr_eq {w : ℂ} (hw : 0 < w.re) (x : ℝ) :
    oneSidedCorr w x =
      cexp (conj w * x) * cexp (-(2 * w.re) * (max 0 x : ℝ)) / (2 * w.re) := by
  have hpt : ∀ t : ℝ, oneSidedExp w t * conj (oneSidedExp w (t - x)) =
      (Ioi (max 0 x)).indicator (fun t : ℝ => cexp (conj w * x) * cexp (-(2 * w.re) * t)) t := by
    intro t
    by_cases ht : t ∈ Ioi (max 0 x)
    · rw [indicator_of_mem ht]
      have ht' : max 0 x < t := ht
      have h0 : 0 < t := lt_of_le_of_lt (le_max_left 0 x) ht'
      have hx : 0 < t - x := by linarith [le_max_right 0 x]
      rw [oneSidedExp, oneSidedExp, if_pos h0, if_pos hx, ← Complex.exp_conj, ← Complex.exp_add,
        ← Complex.exp_add]
      congr 1
      have hre : (2 * w.re : ℂ) = w + conj w := by
        rw [Complex.add_conj]
        push_cast
        ring
      rw [map_neg, map_mul, Complex.conj_ofReal]
      push_cast
      rw [hre]
      ring
    · rw [indicator_of_notMem ht]
      have ht' : t ≤ max 0 x := not_lt.mp ht
      rcases le_or_gt t 0 with h0 | h0
      · rw [oneSidedExp, if_neg (not_lt.mpr h0), zero_mul]
      · have hx : t ≤ x := by
          rcases le_total 0 x with hx | hx
          · rwa [max_eq_right hx] at ht'
          · rw [max_eq_left hx] at ht'
            linarith
        have hnx : ¬ (0 < t - x) := by linarith
        rw [show oneSidedExp w (t - x) = 0 from if_neg hnx, map_zero, mul_zero]
  have hneg : (-(2 * w.re : ℂ)).re < 0 := by
    simp
    linarith
  unfold oneSidedCorr
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_indicator measurableSet_Ioi,
    integral_const_mul, integral_exp_mul_complex_Ioi hneg]
  have h2 : (2 * w.re : ℂ) ≠ 0 := by
    norm_cast
    positivity
  field_simp

/-! ## Continuity of transforms -/

theorem continuous_paperFT_real {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous fun r : ℝ => paperFT f r := by
  unfold paperFT
  refine continuous_of_dominated (bound := fun u => ‖f u‖) (fun r => ?_) (fun r => ?_) hf.norm ?_
  · exact hf.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))
  · refine Eventually.of_forall fun u => ?_
    rw [norm_mul]
    have : I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]
  · exact Eventually.of_forall fun u => by fun_prop

/-! ## The pole part -/

theorem tendsto_paperFT_testFn {w z : ℂ} (hz : 0 < (w - I * z).re) :
    Tendsto (fun j : ℕ => paperFT (testFn w j) z) atTop (𝓝 (1 / (w - I * z))) := by
  simp_rw [paperFT_testFn]
  simpa using (tendsto_paperFT_mollC z).mul (tendsto_paperFT_truncExp hz)

theorem paperFT_autoCorr (w : ℂ) (j : ℕ) (z : ℂ) :
    paperFT (autoCorr w j) z = paperFT (testFn w j) z * conj (paperFT (testFn w j) (conj z)) :=
  EF.paperFT_weilTest (continuous_testFn w j) (continuous_testFn w j)
    (hasCompactSupport_testFn w j) (hasCompactSupport_testFn w j) z

theorem tendsto_pole {w : ℂ} (hw : 1 / 2 < w.re) :
    Tendsto (fun j : ℕ => paperFT (autoCorr w j) (I / 2) + paperFT (autoCorr w j) (-I / 2)) atTop
      (𝓝 (1 / (w + 1 / 2) * conj (1 / (w - 1 / 2)) + 1 / (w - 1 / 2) * conj (1 / (w + 1 / 2)))) := by
  have h1 : w - I * (I / 2) = w + 1 / 2 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  have h2 : w - I * (-I / 2) = w - 1 / 2 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  have hc1 : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
  have hc2 : conj (-I / 2) = I / 2 := by rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  have hre1 : 0 < (w - I * (I / 2)).re := by rw [h1]; norm_num; linarith
  have hre2 : 0 < (w - I * (-I / 2)).re := by rw [h2]; norm_num; linarith
  have ha := tendsto_paperFT_testFn hre1
  have hb := tendsto_paperFT_testFn hre2
  rw [h1] at ha
  rw [h2] at hb
  simp_rw [paperFT_autoCorr, hc1, hc2]
  exact (ha.mul ((Complex.continuous_conj.tendsto _).comp hb)).add
    (hb.mul ((Complex.continuous_conj.tendsto _).comp ha))

/-! ## The archimedean part -/

theorem gammaBracket_eq (r : ℝ) :
    EF.gammaBracket r =
      (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re - Real.log π := by
  unfold EF.gammaBracket
  congr 3
  push_cast
  ring

theorem continuous_gammaBracket : Continuous EF.gammaBracket := by
  have h := continuous_re_digamma_half (c := 1 / 4) (by norm_num)
  have h2 : Continuous fun r : ℝ =>
      (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re - Real.log π :=
    h.sub continuous_const
  exact h2.congr fun r => (gammaBracket_eq r).symm

theorem normSq_sub_I_mul (w : ℂ) (r : ℝ) :
    normSq (w - I * (r : ℂ)) = w.re ^ 2 + (r - w.im) ^ 2 := by
  rw [normSq_apply]
  simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  ring

theorem inv_normSq_sub_I_mul {w : ℂ} (hw : 0 < w.re) (r : ℝ) :
    (normSq (w - I * (r : ℂ)))⁻¹ = (Real.pi / w.re) * poissonWeight w.re (r - w.im) := by
  rw [normSq_sub_I_mul, poissonWeight]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hb : w.re ≠ 0 := hw.ne'
  have hd : w.re ^ 2 + (r - w.im) ^ 2 ≠ 0 := by positivity
  field_simp

/-- The archimedean majorant: `(4π/b)(|P_b(r−t)Re ψ(¼ + ir/2)| + log π · P_b(r−t))`. -/
def archBound (w : ℂ) (r : ℝ) : ℝ :=
  4 * (Real.pi / w.re) * (|poissonWeight w.re (r - w.im)
      * (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re|
    + Real.log π * poissonWeight w.re (r - w.im))

theorem integrable_archBound {w : ℂ} (hw : 0 < w.re) : Integrable (archBound w) :=
  (((integrable_poissonWeight_shift_mul_re_digamma_half hw (by norm_num : (0 : ℝ) < 1 / 4)
    w.im).abs.add ((integrable_poissonWeight_shift hw w.im).const_mul _)).const_mul _)

theorem norm_paperFT_testFn_le {w : ℂ} (hw : 0 < w.re) (j : ℕ) (r : ℝ) :
    ‖paperFT (testFn w j) r‖ ≤ 2 / ‖w - I * (r : ℂ)‖ := by
  rw [paperFT_testFn, norm_mul]
  calc ‖paperFT (mollC j) r‖ * ‖paperFT (truncExp w ((j : ℝ) + 1)) r‖
      ≤ 1 * (2 / ‖w - I * (r : ℂ)‖) :=
        mul_le_mul (norm_paperFT_mollC_le_one j r) (norm_paperFT_truncExp_le hw (by positivity) r)
          (norm_nonneg _) zero_le_one
    _ = 2 / ‖w - I * (r : ℂ)‖ := one_mul _

theorem norm_arch_integrand_le {w : ℂ} (hw : 0 < w.re) (j : ℕ) (r : ℝ) :
    ‖paperFT (autoCorr w j) r * (EF.gammaBracket r : ℂ)‖ ≤ archBound w r := by
  rw [paperFT_autoCorr, Complex.conj_ofReal, norm_mul, norm_mul, Complex.norm_conj,
    Complex.norm_real, Real.norm_eq_abs]
  have hpos : 0 < ‖w - I * (r : ℂ)‖ := by
    rw [norm_pos_iff]
    intro h
    have := congrArg Complex.re h
    rw [re_sub_I_mul_ofReal] at this
    simp at this
    linarith
  have h1 := norm_paperFT_testFn_le hw j r
  have hsq : ‖paperFT (testFn w j) r‖ * ‖paperFT (testFn w j) r‖ ≤ 4 * (normSq (w - I * (r : ℂ)))⁻¹ := by
    rw [← Complex.sq_norm]
    calc ‖paperFT (testFn w j) r‖ * ‖paperFT (testFn w j) r‖
        ≤ (2 / ‖w - I * (r : ℂ)‖) * (2 / ‖w - I * (r : ℂ)‖) :=
          mul_le_mul h1 h1 (norm_nonneg _) (by positivity)
      _ = 4 * (‖w - I * (r : ℂ)‖ ^ 2)⁻¹ := by field_simp; ring
  rw [inv_normSq_sub_I_mul hw] at hsq
  have hP : 0 ≤ poissonWeight w.re (r - w.im) := poissonWeight_nonneg hw _
  have hγ : |EF.gammaBracket r| ≤
      |(Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re| + Real.log π := by
    rw [gammaBracket_eq]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
  calc ‖paperFT (testFn w j) r‖ * ‖paperFT (testFn w j) r‖ * |EF.gammaBracket r|
      ≤ (4 * (Real.pi / w.re * poissonWeight w.re (r - w.im))) *
          (|(Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re| + Real.log π) :=
        mul_le_mul hsq hγ (abs_nonneg _) (by positivity)
    _ = archBound w r := by
      rw [archBound, abs_mul, abs_of_nonneg hP]
      ring

theorem tendsto_arch {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun j : ℕ => ∫ r : ℝ, paperFT (autoCorr w j) r * (EF.gammaBracket r : ℂ)) atTop
      (𝓝 (∫ r : ℝ, 1 / (w - I * r) * conj (1 / (w - I * r)) * (EF.gammaBracket r : ℂ))) := by
  refine tendsto_integral_of_dominated_convergence (archBound w) (fun j => ?_)
    (integrable_archBound hw) (fun j => Eventually.of_forall (norm_arch_integrand_le hw j)) ?_
  · refine (Continuous.mul ?_ (Complex.continuous_ofReal.comp continuous_gammaBracket)).aestronglyMeasurable
    have hc := continuous_paperFT_real ((continuous_testFn w j).integrable_of_hasCompactSupport
      (hasCompactSupport_testFn w j))
    have hc2 : Continuous fun r : ℝ => paperFT (testFn w j) r * conj (paperFT (testFn w j) r) :=
      hc.mul (Complex.continuous_conj.comp hc)
    refine hc2.congr fun r => ?_
    rw [paperFT_autoCorr, Complex.conj_ofReal]
  · refine Eventually.of_forall fun r => ?_
    have hre : 0 < (w - I * (r : ℂ)).re := by rw [re_sub_I_mul_ofReal]; exact hw
    have h := tendsto_paperFT_testFn hre
    simp_rw [paperFT_autoCorr, Complex.conj_ofReal]
    exact (h.mul ((Complex.continuous_conj.tendsto _).comp h)).mul_const _

/-- The archimedean limit is the Poisson integral of the digamma line. -/
theorem arch_limit_eq {w : ℂ} (hw : 0 < w.re) :
    (1 / (2 * π) : ℂ) * ∫ r : ℝ, 1 / (w - I * r) * conj (1 / (w - I * r)) * (EF.gammaBracket r : ℂ)
      = (((Complex.digamma (((1 / 4 + w.re / 2 : ℝ) : ℂ) + ((w.im / 2 : ℝ) : ℂ) * I)).re
          - Real.log π) / (2 * w.re) : ℝ) := by
  have hpt : ∀ r : ℝ, 1 / (w - I * r) * conj (1 / (w - I * r)) * (EF.gammaBracket r : ℂ) =
      (((Real.pi / w.re) * (poissonWeight w.re (r - w.im)
          * (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re
        - Real.log π * poissonWeight w.re (r - w.im)) : ℝ) : ℂ) := by
    intro r
    rw [Complex.mul_conj, one_div, Complex.normSq_inv, inv_normSq_sub_I_mul hw, gammaBracket_eq]
    push_cast
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_complex_ofReal]
  rw [integral_const_mul, integral_sub
    (integrable_poissonWeight_shift_mul_re_digamma_half hw (by norm_num) w.im)
    ((integrable_poissonWeight_shift hw w.im).const_mul _), integral_const_mul,
    integral_poissonWeight_shift hw w.im,
    integral_poissonWeight_shift_mul_re_digamma_half hw (by norm_num) w.im]
  have hb : w.re ≠ 0 := hw.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  push_cast
  field_simp

/-! ## The prime part -/

/-- The prime coefficient `lam(n)/√n` on `n ≥ 2`. -/
def primeCoeff (lam : ℕ → ℝ) (n : ℕ) : ℂ := ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ)

/-- The weights on `n ≥ 2`, as a complex sequence. -/
def lamC (lam : ℕ → ℝ) (n : ℕ) : ℂ := ((if 2 ≤ n then lam n else 0 : ℝ) : ℂ)

theorem sqrt_mul_exp_eq_rpow {n : ℕ} (hn : 2 ≤ n) (b : ℝ) :
    Real.sqrt n * Real.exp (b * Real.log n) = (n : ℝ) ^ (1 / 2 + b) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos, Real.rpow_def_of_pos hpos, ← Real.exp_add]
  congr 1
  ring

theorem norm_prime_le {lam : ℕ → ℝ} {w : ℂ} (hw : 0 < w.re) (j n : ℕ) :
    ‖primeCoeff lam n * (autoCorr w j (Real.log n) + autoCorr w j (-Real.log n))‖ ≤
      2 * (Real.exp (2 * w.re) * ∫ u, majorant w.re u) * (|lam n| / (n : ℝ) ^ (1 / 2 + w.re)) := by
  set C := Real.exp (2 * w.re) * ∫ u, majorant w.re u with hC
  have hC0 : 0 ≤ C := mul_nonneg (Real.exp_pos _).le (integral_nonneg (majorant_nonneg w.re))
  by_cases hn : 2 ≤ n
  · have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have h1 := norm_autoCorr_le hw j (Real.log n)
    have h2 := norm_autoCorr_le hw j (-Real.log n)
    rw [abs_neg, abs_of_pos hlog] at h2
    rw [abs_of_pos hlog] at h1
    rw [norm_mul, primeCoeff, if_pos hn, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hpos
    have hsum : ‖autoCorr w j (Real.log n) + autoCorr w j (-Real.log n)‖ ≤
        2 * C * Real.exp (-(w.re * Real.log n)) := by
      refine (norm_add_le _ _).trans ?_
      rw [← hC] at h1 h2
      linarith
    have hkey : |lam n| / Real.sqrt n * (2 * C * Real.exp (-(w.re * Real.log n))) =
        2 * C * (|lam n| / (n : ℝ) ^ (1 / 2 + w.re)) := by
      rw [← sqrt_mul_exp_eq_rpow hn w.re, Real.exp_neg]
      field_simp
    calc |lam n| / Real.sqrt n * ‖autoCorr w j (Real.log n) + autoCorr w j (-Real.log n)‖
        ≤ |lam n| / Real.sqrt n * (2 * C * Real.exp (-(w.re * Real.log n))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := hkey
  · rw [primeCoeff, if_neg hn, Complex.ofReal_zero, zero_mul, norm_zero]
    positivity

theorem tendsto_prime {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {w : ℂ} (hw : 1 / 2 < w.re) :
    Tendsto (fun j : ℕ => ∑' n : ℕ,
        primeCoeff lam n * (autoCorr w j (Real.log n) + autoCorr w j (-Real.log n))) atTop
      (𝓝 (∑' n : ℕ, primeCoeff lam n *
        (oneSidedCorr w (Real.log n) + oneSidedCorr w (-Real.log n)))) := by
  have hw0 : 0 < w.re := by linarith
  have hsum := (WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW
    (σ := 1 / 2 + w.re) (by linarith)).mul_left
      (2 * (Real.exp (2 * w.re) * ∫ u, majorant w.re u))
  refine tendsto_tsum_of_dominated_convergence hsum (fun n => ?_)
    (Eventually.of_forall fun j n => norm_prime_le hw0 j n)
  exact ((tendsto_autoCorr hw0 _).add (tendsto_autoCorr hw0 _)).const_mul _

theorem natCast_cpow_eq_cexp {n : ℕ} (hn : 2 ≤ n) (s : ℂ) :
    (n : ℂ) ^ s = cexp ((Real.log n : ℂ) * s) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (by omega : n ≠ 0)), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hpos.le]

/-- Each prime term of the limit is `Re(lam(n) n^{−s})/b`, `s = w + ½`. -/
theorem prime_limit_term {w : ℂ} (hw : 0 < w.re) (lam : ℕ → ℝ) (n : ℕ) :
    primeCoeff lam n * (oneSidedCorr w (Real.log n) + oneSidedCorr w (-Real.log n)) =
      (((LSeries.term (lamC lam) (w + 1 / 2) n).re / w.re : ℝ) : ℂ) := by
  by_cases hn : 2 ≤ n
  · have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    set L := Real.log n with hL
    have hconj : conj w = (2 * w.re : ℝ) - w := by
      have := Complex.add_conj w
      linear_combination this
    have hK1 : oneSidedCorr w L = cexp (-(w * L)) / (2 * w.re) := by
      rw [oneSidedCorr_eq hw, max_eq_right hlog.le, ← Complex.exp_add, hconj]
      congr 2
      push_cast
      ring
    have hK2 : oneSidedCorr w (-L) = cexp (-(conj w * L)) / (2 * w.re) := by
      rw [oneSidedCorr_eq hw, max_eq_left (by linarith : -L ≤ 0)]
      push_cast
      rw [mul_zero, Complex.exp_zero, mul_one]
      congr 2
      ring
    have hsqrtR : Real.sqrt n = Real.exp (L / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos, ← hL]
      ring_nf
    have hsqrt : (Real.sqrt n : ℂ) = cexp ((L : ℂ) / 2) := by
      rw [hsqrtR, Complex.ofReal_exp]
      push_cast
      ring_nf
    set T := LSeries.term (lamC lam) (w + 1 / 2) n with hT
    have hTeq : T = (lam n : ℂ) * cexp (-((w + 1 / 2) * L)) := by
      rw [hT, LSeries.term_def, if_neg (by omega), lamC, if_pos hn, natCast_cpow_eq_cexp hn,
        div_eq_mul_inv, ← Complex.exp_neg]
      congr 2
      ring
    have hA : primeCoeff lam n * cexp (-(w * L)) = T := by
      rw [hTeq, primeCoeff, if_pos hn]
      push_cast
      rw [hsqrt, div_eq_mul_inv, ← Complex.exp_neg, mul_assoc, ← Complex.exp_add]
      congr 2
      ring
    have hB : primeCoeff lam n * cexp (-(conj w * L)) = conj T := by
      rw [hTeq, primeCoeff, if_pos hn, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
      push_cast
      rw [hsqrt, div_eq_mul_inv, ← Complex.exp_neg, mul_assoc, ← Complex.exp_add]
      congr 2
      simp only [map_neg, map_mul, map_add, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
      ring
    have hb2 : (2 * w.re : ℂ) ≠ 0 := by
      norm_cast
      positivity
    rw [hK1, hK2]
    calc primeCoeff lam n * (cexp (-(w * L)) / (2 * w.re) + cexp (-(conj w * L)) / (2 * w.re))
        = (primeCoeff lam n * cexp (-(w * L)) + primeCoeff lam n * cexp (-(conj w * L)))
            / (2 * w.re) := by ring
      _ = (T + conj T) / (2 * w.re) := by rw [hA, hB]
      _ = ((T.re / w.re : ℝ) : ℂ) := by
        rw [Complex.add_conj]
        have hb : (w.re : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
        push_cast
        field_simp
  · rw [primeCoeff, if_neg hn, Complex.ofReal_zero, zero_mul]
    have : LSeries.term (lamC lam) (w + 1 / 2) n = 0 := by
      rw [LSeries.term_def, lamC, if_neg hn]
      simp
    rw [this]
    simp

theorem summable_term_lamC {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {s : ℂ} (hs : 1 < s.re) :
    Summable fun n => LSeries.term (lamC lam) s n := by
  refine Summable.of_norm_bounded (WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hs)
    fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with h0
  · positivity
  · rw [lamC, Complex.norm_real, Real.norm_eq_abs]
    split_ifs with hn
    · rfl
    · simp only [abs_zero, zero_div]
      positivity

theorem prime_limit_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {w : ℂ} (hw : 1 / 2 < w.re) :
    ∑' n : ℕ, primeCoeff lam n * (oneSidedCorr w (Real.log n) + oneSidedCorr w (-Real.log n)) =
      (((LSeries (lamC lam) (w + 1 / 2)).re / w.re : ℝ) : ℂ) := by
  have hw0 : 0 < w.re := by linarith
  have hs : 1 < (w + 1 / 2).re := by norm_num; linarith
  simp_rw [prime_limit_term hw0 lam]
  rw [← Complex.ofReal_tsum, LSeries, Complex.re_tsum (summable_term_lamC hW hs), tsum_div_const]

/-! ## The main theorem -/

/-- The Weil function `Φ_lam(s) = ½ψ(s/2) − ½ log π + 1/s + 1/(s−1) − Σ_{n≥2} lam(n) n^{−s}`. -/
def weilFunction (lam : ℕ → ℝ) (s : ℂ) : ℂ :=
  Complex.digamma (s / 2) / 2 - (Real.log π : ℂ) / 2 + 1 / s + 1 / (s - 1) - LSeries (lamC lam) s

theorem pole_limit_re {w : ℂ} (hw : 1 / 2 < w.re) :
    (1 / (w + 1 / 2) * conj (1 / (w - 1 / 2)) + 1 / (w - 1 / 2) * conj (1 / (w + 1 / 2))).re =
      ((1 / (w + 1 / 2)).re + (1 / (w - 1 / 2)).re) / w.re := by
  have hb : 0 < w.re := by linarith
  have hne1 : w + 1 / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  have hne2 : conj w - 1 / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hconj : conj w + w = (2 * w.re : ℝ) := by
    rw [add_comm, Complex.add_conj]
  have hcB : conj (1 / (w - 1 / 2)) = 1 / (conj w - 1 / 2) := by
    rw [map_div₀, map_one, map_sub, map_div₀, map_one, map_ofNat]
  set A := 1 / (w + 1 / 2) with hA
  set B := 1 / (w - 1 / 2) with hB
  have hsum : A + conj B = ((2 * w.re : ℝ) : ℂ) * (A * conj B) := by
    rw [hA, hcB, one_div_add_one_div hne1 hne2, one_div_mul_one_div, mul_one_div, ← hconj]
    congr 1
    ring
  have h2r : (2 * w.re : ℝ) ≠ 0 := by positivity
  have h2 : ((2 * w.re : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2r
  have hkey : A * conj B = (A + conj B) / ((2 * w.re : ℝ) : ℂ) := by
    rw [hsum]
    field_simp
  have hsym : B * conj A = conj (A * conj B) := by
    rw [map_mul, Complex.conj_conj, mul_comm]
  rw [hsym, Complex.add_conj, Complex.ofReal_re, hkey, Complex.div_ofReal_re, Complex.add_re,
    Complex.conj_re]
  field_simp

/-- **Weil positivity makes the Weil function Herglotz on `Re s > 1`.** -/
theorem re_weilFunction_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {s : ℂ}
    (hs : 1 < s.re) : 0 ≤ (weilFunction lam s).re := by
  set w : ℂ := s - 1 / 2 with hwdef
  have hw : 1 / 2 < w.re := by rw [hwdef]; norm_num; linarith
  have hw0 : 0 < w.re := by linarith
  have hsw : s = w + 1 / 2 := by rw [hwdef]; ring
  -- the Weil functionals of the tests
  have hpos : ∀ j : ℕ, 0 ≤ (weilFullFunctional lam (autoCorr w j)).re := fun j =>
    hW (testFn w j) (contDiff_testFn w j) (hasCompactSupport_testFn w j)
  have hfun : ∀ j : ℕ, weilFullFunctional lam (autoCorr w j) =
      (paperFT (autoCorr w j) (I / 2) + paperFT (autoCorr w j) (-I / 2))
        - (∑' n : ℕ, primeCoeff lam n * (autoCorr w j (Real.log n) + autoCorr w j (-Real.log n)))
        + (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (autoCorr w j) r * (EF.gammaBracket r : ℂ) := by
    intro j
    rfl
  have hlim := ((tendsto_pole hw).sub (tendsto_prime hW hw)).add
    ((tendsto_arch hw0).const_mul (1 / (2 * π) : ℂ))
  simp_rw [← hfun] at hlim
  have hre := ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp hlim)
    (Eventually.of_forall hpos)
  rw [prime_limit_eq hW hw, arch_limit_eq hw0] at hre
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at hre
  have hpole := pole_limit_re hw
  simp only [Complex.add_re] at hpole
  -- identify the limit with `Re Φ(s) / b`
  have hdig : (Complex.digamma (((1 / 4 + w.re / 2 : ℝ) : ℂ) + ((w.im / 2 : ℝ) : ℂ) * I)) =
      Complex.digamma (s / 2) := by
    congr 1
    rw [hsw]
    apply Complex.ext <;> simp; ring
  rw [hdig] at hre
  have hval : (weilFunction lam s).re =
      w.re * (((1 / (w + 1 / 2)).re + (1 / (w - 1 / 2)).re) / w.re
        - (LSeries (lamC lam) (w + 1 / 2)).re / w.re
        + ((Complex.digamma (s / 2)).re - Real.log π) / (2 * w.re)) := by
    have h1 : w + 1 / 2 = s := hsw.symm
    have h2 : w - 1 / 2 = s - 1 := by rw [hsw]; ring
    rw [h1, h2, weilFunction]
    simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re]
    field_simp
    ring
  rw [hval]
  refine mul_nonneg hw0.le ?_
  linarith [hpole, hre]

end RHTower.WeilHerglotz

end

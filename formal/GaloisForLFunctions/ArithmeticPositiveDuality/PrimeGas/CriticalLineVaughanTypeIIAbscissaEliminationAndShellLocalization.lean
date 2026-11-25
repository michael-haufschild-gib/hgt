import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SmoothReflectedMobiusVaughanTypeIAnnihilation

/-!
# Critical-Line Vaughan Type-II Abscissa Elimination, Zero-Residue Positive Mellin Shift, Trans-Horizon Shell Localization, and Amplified Critical-Line Excursion Forcing on `Ω_open`

In `SmoothReflectedMobiusVaughanTypeIAnnihilation`, weighting the cross-height Gaussian two-series
identity by `μ(d) d^{-(1 - s)} smoothAFECutoff(d / Y)` at `x = |Im s|^{-(1 + η)}` and
`Y = |Im s|^{3 + η}` (`η ≥ 1`) annihilates both the short Möbius head and the entire smooth Vaughan
Type-I sum without continuum pole subtraction across
`Ω_open = {s : ℂ | 3001 / 24000 ≤ Re s ∧ Re s < 1 / 2 ∧ 184 < |Im s|}`, concentrating the amplified
Spira dual vacuum `(1 - 2^{-(1 - s)}) zetaChi(s)` against `smoothOuterVaughanTypeII`.

This module establishes four unconditional structural and quantitative theorems on
`smoothOuterVaughanTypeII` across all of `Ω_open`:

1. **Exact zero-residue positive-half-plane Mellin shift and critical-line representation of
   `smoothOuterDirectPairSum` (`smoothOuterDirectPairSum_eq_mellin_shift_pos`,
   `smoothOuterDirectPairSum_eq_criticalLine_integral`):**
   Because `smoothAFEZetaShiftedPoleResidue s y - 2^{-(1 - s)} smoothAFEZetaShiftedPoleResidue s (2y) = 0`
   identically for every `y > 0`, the combined Mellin integrand agrees away from `{0, 1 - s}` with a
   function holomorphic throughout `{z : ℂ | 0 < Re z}`. Shifting from `Re z = 2` to any line
   `Re z = a > 0` (`Re s + a ≠ 1`) therefore crosses `z = 1 - s` with identically zero residue while
   remaining strictly right of `z = 0`. At `a = 1 / 2 - Re s > 0` (`0 < Re s < 1 / 2`), this
   expresses `smoothOuterDirectPairSum s x d` as an exact Gaussian integral purely along the
   critical line `linePt (Im s + v) = 1 / 2 + i (Im s + v)`.

2. **Exact critical-line abscissa elimination of `smoothOuterVaughanTypeII`
   (`criticalSmoothVaughanTypeII`, `smoothOuterVaughanTypeII_eq_criticalLine_pairing`):**
   Substituting `smoothOuterDirectPairSum_eq_criticalLine_integral` into `smoothOuterVaughanTypeII`
   and commuting `∑' d` with `∫ v : ℝ` cancels `Re s` identically inside every Dirichlet term via
   `-(1 - s) + ((1 / 2 - Re s) + i v) = -conj (linePt (Im s + v))`. Consequently, for every
   `0 < Re s < 1 / 2`, `smoothOuterVaughanTypeII U V s x Y` pairs `ζ(1 / 2 + i (Im s + v))` against
   the `Re s`-independent critical-line Vaughan Type-II series `criticalSmoothVaughanTypeII U V Y (Im s + v)`,
   isolating the entire `Re s`-dependence into the scalar factor `x^{1/2 - Re s + i v}` and the
   Gaussian kernel at `(1 / 2 - Re s) + i v`.

3. **Unconditional trans-horizon finite-shell localization on `Ω_open`
   (`smoothOuterVaughanTypeIIShell`,
   `exists_smoothOuterVaughanTypeII_shell_localization_on_remaining_strip`):**
   For every `η ≥ 1`, `0 < δ`, and `B_dec > 0`, truncating `smoothOuterVaughanTypeII` at
   `x = |Im s|^{-(1 + η)}`, `Y = |Im s|^{3 + η}` to the finite trans-horizon integer shell
   `⌊|Im s|^{1 + η - δ}⌋₊ < d ≤ ⌈|Im s|^{3 + η + δ}⌉₊` incurs error `≤ C_loc * |Im s|^{-B_dec}`
   uniformly across every point `s ∈ Ω_open` and all `U, V : ℕ`.

4. **Amplified critical-line excursion forcing and critical-line power-saving witness production
   across all of `Ω_open`
   (`norm_smoothOuterVaughanTypeII_le_criticalLine_gaussian_moment`,
   `criticalLine_vaughanTypeII_amplified_forcing_and_witness_on_remaining_strip`,
   `criticalLine_power_saving_exponent_beats_amplified_threshold`):**
   Dividing `norm_smoothOuterVaughanTypeII_le_criticalLine_gaussian_moment` by
   `x^{1/2 - Re s} = |Im s|^{-(1 + η)(1/2 - Re s)}` proves that any hypothetical zero `ζ(s) = 0` in
   `Ω_open` forces the Gaussian-localized critical-line moment of
   `‖ζ(1/2 + i t) · criticalSmoothVaughanTypeII U V Y t‖` near `t = Im s` to exceed order
   `(1 / 2 - Re s) · |Im s|^{(2 + η)(1/2 - Re s)}`, while conversely any critical-line bound below
   that explicit threshold produces an unconditional `HasStrictPrimeGasWitness` at `s`. As `η → ∞`,
   `(2 + η)(1 / 2 - σ)` strictly dominates `(3 + η)(1 / 2 - θ) + 1` whenever `σ < θ`, reducing
   pointwise witness certification on `{s ∈ Ω_open | Re s < θ}` to critical-line `Y^{1/2 - θ}`
   cancellation on `ζ(1/2 + i t) · criticalSmoothVaughanTypeII U V Y t`.
-/

noncomputable section

open Complex Filter Set MeasureTheory intervalIntegral
open scoped BigOperators ComplexConjugate Topology ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open GaloisForLFunctions.ArithmeticPositiveDuality
open _root_.RHTower

/-! ### Part 1: Zero-Residue Positive Mellin Shift and Critical-Line Integral for `smoothOuterDirectPairSum` -/

section Part1ZeroResidueCriticalLineShift

lemma norm_smoothAFECutoff_div_le' {A K : ℝ}
    (hK : ∀ {u : ℝ}, 0 < u → ‖smoothAFECutoff u‖ ≤ K * u ^ (-A))
    {u y : ℝ} (hu : 0 < u) (hy : 0 < y) :
    ‖smoothAFECutoff (u / y)‖ ≤ K * ((u ^ A)⁻¹ * y ^ A) := by
  have h := hK (div_pos hu hy)
  rwa [Real.div_rpow hu.le hy.le, Real.rpow_neg hu.le, Real.rpow_neg hy.le, div_inv_eq_mul] at h

private lemma tendsto_smoothAFEZetaMellinIntegrand_horizontal_ab'
    {X a b : ℝ} (hX : 0 < X) (hab : a < b) (w : ℂ) {ε : ℝ} (hε : |ε| = 1) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in a..b,
        smoothAFEZetaMellinIntegrand w X ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
  set M_ab : ℝ := max (|a|) (|b|) + 1
  obtain ⟨C, N, hC0, hC⟩ := exists_bound_norm_riemannZeta_strip (|w.re| + M_ab)
  set X_bd : ℝ := max (X ^ a) (X ^ b)
  set E_bd : ℝ := Real.exp (M_ab ^ (2 : ℕ))
  set K : ℝ := C * X_bd * E_bd
  refine GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
    (M := fun T => K * ((|w.im| + T) ^ N * Real.exp (-(T ^ (2 : ℕ)))))
    (hgt := fun T => ε * T) ?_
    (by simpa using (tendsto_shifted_pow_mul_exp_neg_sq |w.im| N).const_mul K)
  filter_upwards [eventually_ge_atTop (|w.im| + 2)] with T hT u hu
  rw [Set.uIoc_of_le hab.le] at hu
  have hT1 : 1 ≤ T := by linarith [abs_nonneg w.im]
  have hT_pos : 0 < T := zero_lt_one.trans_le hT1
  have habsv : |ε * T| = T := by rw [abs_mul, hε, one_mul, abs_of_pos hT_pos]
  set z : ℂ := (u : ℂ) + ((ε * T : ℝ) : ℂ) * I
  have hu_abs : |u| ≤ M_ab := by
    rw [abs_le]
    have ha_le : -M_ab ≤ a := by dsimp only [M_ab]; linarith [neg_abs_le a, le_max_left (|a|) (|b|)]
    have hb_le : b ≤ M_ab := by dsimp only [M_ab]; linarith [le_abs_self b, le_max_right (|a|) (|b|)]
    exact ⟨ha_le.trans hu.1.le, hu.2.trans hb_le⟩
  have hwz_re : |(w + z).re| ≤ |w.re| + M_ab := by
    rw [Complex.add_re, show z.re = u by simp [z]]
    linarith [abs_add_le w.re u]
  have hwz_im_ge : 1 ≤ |(w + z).im| := by
    rw [Complex.add_im, show z.im = ε * T by simp [z]]
    have htri : |ε * T| - |w.im| ≤ |w.im + ε * T| := by
      have h := abs_sub_abs_le_abs_sub (ε * T) (-w.im)
      simpa [abs_neg, sub_neg_eq_add, add_comm] using h
    linarith
  have hwz_im_le : |(w + z).im| ≤ |w.im| + T := by
    rw [Complex.add_im, show z.im = ε * T by simp [z]]
    exact (abs_add_le w.im (ε * T)).trans_eq (by rw [habsv])
  have hzeta : ‖riemannZeta (w + z)‖ ≤ C * (|w.im| + T) ^ N := by
    have hrec : ((((w + z).re : ℝ)) : ℂ) + (((w + z).im : ℝ) : ℂ) * I = w + z :=
      Complex.re_add_im _
    have hbase := hC (w + z).re (w + z).im hwz_re hwz_im_ge
    rw [hrec] at hbase
    exact hbase.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hwz_im_le N) hC0)
  have hpow : ‖(X : ℂ) ^ z‖ ≤ X_bd := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, show z.re = u by simp [z]]
    rcases le_total 1 X with h1X | h1X
    · exact (Real.rpow_le_rpow_of_exponent_le h1X hu.2).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge hX h1X hu.1.le).trans (le_max_left _ _)
  have hker : ‖smoothAFEGaussianKernel z‖ ≤ E_bd * Real.exp (-(T ^ (2 : ℕ))) := by
    rw [smoothAFEGaussianKernel, norm_div, Complex.norm_exp]
    have hz_sq : (z ^ 2).re = u ^ (2 : ℕ) - T ^ (2 : ℕ) := by
      dsimp only [z]
      simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      have hε2 : ε * ε = 1 := by have := sq_abs ε; rw [hε] at this; nlinarith
      nlinarith
    have hznorm1 : 1 ≤ ‖z‖ := by
      calc (1 : ℝ) ≤ T := hT1
        _ = |z.im| := by simp [z, habsv]
        _ ≤ ‖z‖ := Complex.abs_im_le_norm z
    have hu2 : u ^ (2 : ℕ) ≤ M_ab ^ (2 : ℕ) := by
      rw [← sq_abs u]
      exact pow_le_pow_left₀ (abs_nonneg u) hu_abs 2
    rw [hz_sq]
    exact (div_le_self (Real.exp_nonneg _) hznorm1).trans
      (by dsimp only [E_bd]; rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith))
  rw [smoothAFEZetaMellinIntegrand, norm_mul, norm_mul]
  have hX_nn : 0 ≤ X_bd := (Real.rpow_nonneg hX.le a).trans (le_max_left _ _)
  calc ‖riemannZeta (w + z)‖ * ‖(X : ℂ) ^ z‖ * ‖smoothAFEGaussianKernel z‖
      ≤ (C * (|w.im| + T) ^ N) * X_bd * (E_bd * Real.exp (-(T ^ (2 : ℕ)))) := by
        refine mul_le_mul (mul_le_mul hzeta hpow (norm_nonneg _) (by positivity))
          hker (norm_nonneg _) ?_
        exact mul_nonneg (by positivity) hX_nn
    _ = K * ((|w.im| + T) ^ N * Real.exp (-(T ^ (2 : ℕ)))) := by dsimp only [K]; ring

private lemma continuous_smoothAFEZetaMellinIntegrand_vertical
    {s : ℂ} {y c : ℝ} (hy : 0 < y) (hc0 : c ≠ 0) (hsc : s.re + c ≠ 1) :
    Continuous (fun v : ℝ => smoothAFEZetaMellinIntegrand s y ((c : ℂ) + (v : ℂ) * I)) := by
  haveI : NeZero (y : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hy.ne'⟩
  have hpath : Continuous (fun v : ℝ => (c : ℂ) + (v : ℂ) * I) := by fun_prop
  have hz : Continuous (fun v : ℝ => riemannZeta (s + ((c : ℂ) + (v : ℂ) * I))) := by
    rw [continuous_iff_continuousAt]
    intro v
    refine (differentiableAt_riemannZeta ?_).continuousAt.comp (by fun_prop)
    intro heq
    have hre := congrArg Complex.re heq
    simp at hre
    exact hsc hre
  have hypow : Continuous (fun v : ℝ => (y : ℂ) ^ ((c : ℂ) + (v : ℂ) * I)) :=
    (continuous_const_cpow (y : ℂ)).comp hpath
  have hker : Continuous (fun v : ℝ => smoothAFEGaussianKernel ((c : ℂ) + (v : ℂ) * I)) := by
    unfold smoothAFEGaussianKernel
    exact (Complex.continuous_exp.comp (hpath.pow 2)).div hpath fun v h0 => by
      have hre := congrArg Complex.re h0
      simp at hre
      exact hc0 hre
  unfold smoothAFEZetaMellinIntegrand
  exact (hz.mul hypow).mul hker

private lemma continuousOn_smoothAFEZetaMellinIntegrand_horizontal
    {s : ℂ} {y a b h : ℝ} (hy : 0 < y) (h_im_ne0 : h ≠ 0) (h_im_ne_s : s.im + h ≠ 0) :
    ContinuousOn (fun u : ℝ => smoothAFEZetaMellinIntegrand s y ((u : ℂ) + (h : ℂ) * I))
      (uIcc a b) := by
  haveI : NeZero (y : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hy.ne'⟩
  refine Continuous.continuousOn ?_
  have hpath : Continuous (fun u : ℝ => (u : ℂ) + (h : ℂ) * I) := by fun_prop
  have hz : Continuous (fun u : ℝ => riemannZeta (s + ((u : ℂ) + (h : ℂ) * I))) := by
    rw [continuous_iff_continuousAt]
    intro u
    refine (differentiableAt_riemannZeta ?_).continuousAt.comp (by fun_prop)
    intro heq
    have him := congrArg Complex.im heq
    simp at him
    exact h_im_ne_s him
  have hypow : Continuous (fun u : ℝ => (y : ℂ) ^ ((u : ℂ) + (h : ℂ) * I)) :=
    (continuous_const_cpow (y : ℂ)).comp hpath
  have hker : Continuous (fun u : ℝ => smoothAFEGaussianKernel ((u : ℂ) + (h : ℂ) * I)) := by
    unfold smoothAFEGaussianKernel
    exact (Complex.continuous_exp.comp (hpath.pow 2)).div hpath fun u h0 => by
      have him := congrArg Complex.im h0
      simp at him
      exact h_im_ne0 him
  unfold smoothAFEZetaMellinIntegrand
  exact (hz.mul hypow).mul hker

/-- **Exact zero-residue positive-half-plane Mellin shift for `smoothOuterDirectPairSum`:**
for every `s ≠ 1`, `x > 0`, `d ≥ 1`, and `0 < a < b` with `s.re + a ≠ 1` and `1 < s.re + b`,
the shifted `ζ`-pole residues at `z = 1 - s` cancel identically between `d x` and `2 d x`, while
`0 < a` keeps the contour strictly right of `z = 0`, yielding a zero-residue shift to `Re z = a`. -/
theorem smoothOuterDirectPairSum_eq_mellin_shift_pos
    {s : ℂ} (hs1 : s ≠ 1) {x : ℝ} (hx : 0 < x) {d : ℕ} (hd1 : 1 ≤ d)
    {a b : ℝ} (ha0 : 0 < a) (hab : a < b) (hsa : s.re + a ≠ 1) (hsb : 1 < s.re + b) :
    smoothOuterDirectPairSum s x d =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ v : ℝ,
          riemannZeta (s + ((a : ℂ) + (v : ℂ) * I)) *
            (1 - (2 : ℂ) ^ (-(1 - s - ((a : ℂ) + (v : ℂ) * I)))) *
            (((d : ℝ) * x : ℝ) : ℂ) ^ ((a : ℂ) + (v : ℂ) * I) *
            smoothAFEGaussianKernel ((a : ℂ) + (v : ℂ) * I) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  set y : ℝ := (d : ℝ) * x
  have hy : 0 < y := mul_pos hd_pos hx
  have h2y : 0 < 2 * y := mul_pos two_pos hy
  have h0b : 0 < b := ha0.trans hab
  -- Step 1: Express `smoothOuterDirectPairSum s x d` on `Re z = b`.
  have hs1_dir := (summable_smoothAFE_direct h0b hy hsb).congr fun n => by push_cast; rfl
  have hs2_dir := ((summable_smoothAFE_direct h0b h2y hsb).mul_left ((2 : ℂ) ^ (-(1 - s)))).congr
    fun n => by push_cast; rfl
  have hpair_b : smoothOuterDirectPairSum s x d =
      smoothAFEZetaMellinAt b s y - (2 : ℂ) ^ (-(1 - s)) * smoothAFEZetaMellinAt b s (2 * y) := by
    rw [smoothAFEZetaMellinAt_eq_tsum_smoothAFECutoff hy h0b hsb,
      smoothAFEZetaMellinAt_eq_tsum_smoothAFECutoff h2y h0b hsb]
    unfold smoothOuterDirectPairSum
    rw [← tsum_mul_left, ← hs1_dir.tsum_sub hs2_dir]
    refine tsum_congr fun n => ?_
    dsimp only [y]
    push_cast
    rw [show (2 : ℝ) * ((d : ℝ) * x) = 2 * (d : ℝ) * x by ring]
    ring
  -- Step 2: Construct `F_pair` and its `{0 < Re z}`-holomorphic replacement `G_hol`.
  set c₂s : ℂ := (2 : ℂ) ^ (-(1 - s))
  set F_pair : ℂ → ℂ := fun z =>
    smoothAFEZetaMellinIntegrand s y z - c₂s * smoothAFEZetaMellinIntegrand s (2 * y) z
  set R_pair : ℂ → ℂ := fun z =>
    smoothAFEZetaPoleRemainder s y z - c₂s * smoothAFEZetaPoleRemainder s (2 * y) z
  set G_hol : ℂ → ℂ := fun z => ((1 - c₂s) * riemannZeta s) * z⁻¹ + R_pair z
  have hR_anal : AnalyticOnNhd ℂ R_pair Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((differentiable_smoothAFEZetaPoleRemainder hy s).sub
        ((differentiable_smoothAFEZetaPoleRemainder h2y s).const_mul c₂s))
  have hG_anal : AnalyticOnNhd ℂ G_hol {z : ℂ | 0 < z.re} := by
    intro z hz
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
    exact (analyticAt_const.mul (analyticAt_id.inv hz0)).add (hR_anal z (Set.mem_univ z))
  have hres_cancel :
      smoothAFEZetaShiftedPoleResidue s y - c₂s * smoothAFEZetaShiftedPoleResidue s (2 * y) = 0 := by
    unfold smoothAFEZetaShiftedPoleResidue
    have h2y_cpow : ((2 * y : ℝ) : ℂ) ^ (1 - s) = (2 : ℂ) ^ (1 - s) * (y : ℂ) ^ (1 - s) := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg two_pos.le hy.le (1 - s)]
      norm_num
    have h2_cancel : c₂s * (2 : ℂ) ^ (1 - s) = 1 := by
      dsimp only [c₂s]
      rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), neg_add_cancel, Complex.cpow_zero]
    rw [h2y_cpow]
    calc (y : ℂ) ^ (1 - s) * Complex.exp ((1 - s) ^ (2 : ℕ)) / (1 - s) -
            c₂s * ((2 : ℂ) ^ (1 - s) * (y : ℂ) ^ (1 - s) * Complex.exp ((1 - s) ^ (2 : ℕ)) / (1 - s))
        = (1 - c₂s * (2 : ℂ) ^ (1 - s)) *
            ((y : ℂ) ^ (1 - s) * Complex.exp ((1 - s) ^ (2 : ℕ)) / (1 - s)) := by ring
      _ = 0 := by rw [h2_cancel, sub_self, zero_mul]
  have hFG_eq : ∀ z ∈ ({z : ℂ | z ≠ 0 ∧ z ≠ 1 - s} : Set ℂ), F_pair z = G_hol z := by
    rintro z ⟨hz0, hzρ⟩
    dsimp only [F_pair, G_hol, R_pair]
    rw [smoothAFEZetaMellinIntegrand_eq_two_poles_add_remainder hs1 hz0 hzρ,
      smoothAFEZetaMellinIntegrand_eq_two_poles_add_remainder hs1 hz0 hzρ]
    linear_combination (z - (1 - s))⁻¹ * hres_cancel
  -- Step 3: Show `rectIntegral F_pair ((a : ℂ) - (T : ℂ) * I) ((b : ℂ) + (T : ℂ) * I) = 0` for `T > |s.im| + 1`.
  have hrect_zero : ∀ᶠ T : ℝ in atTop,
      rectIntegral F_pair ((a : ℂ) - (T : ℂ) * I) ((b : ℂ) + (T : ℂ) * I) = 0 := by
    filter_upwards [eventually_gt_atTop (|s.im| + 1)] with T hT
    have hT_pos : 0 < T := lt_of_le_of_lt (abs_nonneg s.im) (by linarith)
    have habs_im := abs_lt.mp (by linarith : |s.im| < T)
    set z₁ : ℂ := (a : ℂ) - (T : ℂ) * I
    set z₂ : ℂ := (b : ℂ) + (T : ℂ) * I
    have hz₁_re : z₁.re = a := by simp [z₁]
    have hz₂_re : z₂.re = b := by simp [z₂]
    have hz₁_im : z₁.im = -T := by simp [z₁]
    have hz₂_im : z₂.im = T := by simp [z₂]
    have hcongr : rectIntegral F_pair z₁ z₂ = rectIntegral G_hol z₁ z₂ := by
      refine rectIntegral_congr hFG_eq ?_ ?_ ?_ ?_
      · intro u _
        rw [hz₁_im]
        refine ⟨fun h0 => ?_, fun hρ => ?_⟩
        · have him := congrArg Complex.im h0; simp at him; linarith
        · have him := congrArg Complex.im hρ; simp at him; linarith
      · intro u _
        rw [hz₂_im]
        refine ⟨fun h0 => ?_, fun hρ => ?_⟩
        · have him := congrArg Complex.im h0; simp at him; linarith
        · have him := congrArg Complex.im hρ; simp at him; linarith
      · intro v _
        rw [hz₂_re]
        refine ⟨fun h0 => ?_, fun hρ => ?_⟩
        · have hre := congrArg Complex.re h0; simp at hre; linarith
        · have hre := congrArg Complex.re hρ; simp at hre; linarith
      · intro v _
        rw [hz₁_re]
        refine ⟨fun h0 => ?_, fun hρ => ?_⟩
        · have hre := congrArg Complex.re h0; simp at hre; linarith
        · have hre := congrArg Complex.re hρ; simp at hre; exact hsa (by linarith)
    have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ {z : ℂ | 0 < z.re} := by
      intro z hz
      have hmem := (Complex.mem_reProdIm.mp hz).1
      rw [hz₁_re, hz₂_re, uIcc_of_le hab.le] at hmem
      exact ha0.trans_le hmem.1
    rw [hcongr, rectIntegral_eq_zero_of_analyticOnNhd hsub hG_anal]
  -- Step 4: Take `T → ∞` on each of the four edges of `rectIntegral F_pair`.
  have hbot : Tendsto (fun T : ℝ => ∫ u : ℝ in a..b, F_pair ((u : ℂ) + ((-T : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
    have ht1 : Tendsto (fun T : ℝ => ∫ u : ℝ in a..b,
        smoothAFEZetaMellinIntegrand s y ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
      refine (tendsto_smoothAFEZetaMellinIntegrand_horizontal_ab' hy hab s (ε := -1) (by norm_num)).congr
        fun T => intervalIntegral.integral_congr fun u _ => by congr 1; push_cast; ring
    have ht2 : Tendsto (fun T : ℝ => ∫ u : ℝ in a..b,
        smoothAFEZetaMellinIntegrand s (2 * y) ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
      refine (tendsto_smoothAFEZetaMellinIntegrand_horizontal_ab' h2y hab s (ε := -1) (by norm_num)).congr
        fun T => intervalIntegral.integral_congr fun u _ => by congr 1; push_cast; ring
    have hdiff := ht1.sub (ht2.const_mul c₂s)
    rw [mul_zero, sub_zero] at hdiff
    refine hdiff.congr' ?_
    filter_upwards [eventually_gt_atTop (|s.im| + 1)] with T hT
    have hT_pos : 0 < T := lt_of_le_of_lt (abs_nonneg s.im) (by linarith)
    have habs_im := abs_lt.mp (by linarith : |s.im| < T)
    have hi1 : IntervalIntegrable
        (fun u : ℝ => smoothAFEZetaMellinIntegrand s y ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) volume a b :=
      (continuousOn_smoothAFEZetaMellinIntegrand_horizontal (a := a) (b := b) (h := -T) hy
        (by linarith) (by linarith)).intervalIntegrable
    have hi2 : IntervalIntegrable
        (fun u : ℝ => c₂s * smoothAFEZetaMellinIntegrand s (2 * y) ((u : ℂ) + ((-T : ℝ) : ℂ) * I))
        volume a b :=
      ((continuousOn_smoothAFEZetaMellinIntegrand_horizontal (a := a) (b := b) (h := -T) h2y
        (by linarith) (by linarith)).const_mul c₂s).intervalIntegrable
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hi1 hi2]
  have htop : Tendsto (fun T : ℝ => ∫ u : ℝ in a..b, F_pair ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
    have ht1 : Tendsto (fun T : ℝ => ∫ u : ℝ in a..b,
        smoothAFEZetaMellinIntegrand s y ((u : ℂ) + (T : ℂ) * I)) atTop (𝓝 0) := by
      refine (tendsto_smoothAFEZetaMellinIntegrand_horizontal_ab' hy hab s (ε := 1) (by norm_num)).congr
        fun T => intervalIntegral.integral_congr fun u _ => by congr 1; push_cast; ring
    have ht2 : Tendsto (fun T : ℝ => ∫ u : ℝ in a..b,
        smoothAFEZetaMellinIntegrand s (2 * y) ((u : ℂ) + (T : ℂ) * I)) atTop (𝓝 0) := by
      refine (tendsto_smoothAFEZetaMellinIntegrand_horizontal_ab' h2y hab s (ε := 1) (by norm_num)).congr
        fun T => intervalIntegral.integral_congr fun u _ => by congr 1; push_cast; ring
    have hdiff := ht1.sub (ht2.const_mul c₂s)
    rw [mul_zero, sub_zero] at hdiff
    refine hdiff.congr' ?_
    filter_upwards [eventually_gt_atTop (|s.im| + 1)] with T hT
    have hT_pos : 0 < T := lt_of_le_of_lt (abs_nonneg s.im) (by linarith)
    have habs_im := abs_lt.mp (by linarith : |s.im| < T)
    have hi1 : IntervalIntegrable
        (fun u : ℝ => smoothAFEZetaMellinIntegrand s y ((u : ℂ) + (T : ℂ) * I)) volume a b :=
      (continuousOn_smoothAFEZetaMellinIntegrand_horizontal (a := a) (b := b) (h := T) hy
        (by linarith) (by linarith)).intervalIntegrable
    have hi2 : IntervalIntegrable
        (fun u : ℝ => c₂s * smoothAFEZetaMellinIntegrand s (2 * y) ((u : ℂ) + (T : ℂ) * I))
        volume a b :=
      ((continuousOn_smoothAFEZetaMellinIntegrand_horizontal (a := a) (b := b) (h := T) h2y
        (by linarith) (by linarith)).const_mul c₂s).intervalIntegrable
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hi1 hi2]
  set R_val : ℂ := (∫ v : ℝ, smoothAFEZetaMellinIntegrand s y ((b : ℂ) + (v : ℂ) * I)) -
    c₂s * ∫ v : ℝ, smoothAFEZetaMellinIntegrand s (2 * y) ((b : ℂ) + (v : ℂ) * I)
  set L_val : ℂ := (∫ v : ℝ, smoothAFEZetaMellinIntegrand s y ((a : ℂ) + (v : ℂ) * I)) -
    c₂s * ∫ v : ℝ, smoothAFEZetaMellinIntegrand s (2 * y) ((a : ℂ) + (v : ℂ) * I)
  have hright : Tendsto (fun T : ℝ => ∫ v : ℝ in (-T)..T, F_pair ((b : ℂ) + (v : ℂ) * I))
      atTop (𝓝 R_val) := by
    have hv1 := tendsto_smoothAFEZetaMellinIntegrand_vertical_general hy h0b.ne' (by linarith)
    have hv2 := tendsto_smoothAFEZetaMellinIntegrand_vertical_general h2y h0b.ne' (by linarith)
    refine (hv1.sub (hv2.const_mul c₂s)).congr fun T => ?_
    have hc1 := continuous_smoothAFEZetaMellinIntegrand_vertical hy h0b.ne' (by linarith)
    have hc2 := (continuous_smoothAFEZetaMellinIntegrand_vertical h2y h0b.ne' (by linarith)).const_mul c₂s
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
  have hleft : Tendsto (fun T : ℝ => ∫ v : ℝ in (-T)..T, F_pair ((a : ℂ) + (v : ℂ) * I))
      atTop (𝓝 L_val) := by
    have hv1 := tendsto_smoothAFEZetaMellinIntegrand_vertical_general hy ha0.ne' hsa
    have hv2 := tendsto_smoothAFEZetaMellinIntegrand_vertical_general h2y ha0.ne' hsa
    refine (hv1.sub (hv2.const_mul c₂s)).congr fun T => ?_
    have hc1 := continuous_smoothAFEZetaMellinIntegrand_vertical hy ha0.ne' hsa
    have hc2 := (continuous_smoothAFEZetaMellinIntegrand_vertical h2y ha0.ne' hsa).const_mul c₂s
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
  have hrect_tendsto :
      Tendsto (fun T : ℝ => rectIntegral F_pair ((a : ℂ) - (T : ℂ) * I) ((b : ℂ) + (T : ℂ) * I))
        atTop (𝓝 (((0 - 0) + I • R_val) - I • L_val)) := by
    refine (((hbot.sub htop).add (hright.const_smul I)).sub (hleft.const_smul I)).congr fun T => ?_
    unfold rectIntegral
    simp
  have hlim_zero := tendsto_nhds_unique hrect_tendsto
    (tendsto_const_nhds.congr' (hrect_zero.mono fun _ h => h.symm))
  have hRL_eq : R_val = L_val := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    have h : I * R_val - I * L_val = 0 := by simpa [smul_eq_mul] using hlim_zero
    linear_combination h
  -- Step 5: Combine `L_val` into a single `v`-integral on `Re z = a`.
  have hint_a1 := smoothAFEZetaMellinIntegrand_verticalIntegrable_general (s := s) hy ha0.ne' hsa
  rw [Complex.VerticalIntegrable] at hint_a1
  have hint_a2 := (smoothAFEZetaMellinIntegrand_verticalIntegrable_general (s := s) h2y ha0.ne' hsa).const_mul c₂s
  rw [hpair_b]
  unfold smoothAFEZetaMellinAt
  rw [Complex.real_smul, Complex.real_smul]
  have hb_eq_R :
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (∫ t : ℝ, smoothAFEZetaMellinIntegrand s y ((b : ℂ) + (t : ℂ) * I)) -
        c₂s *
          ((((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ∫ t : ℝ, smoothAFEZetaMellinIntegrand s (2 * y) ((b : ℂ) + (t : ℂ) * I)) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) * R_val := by
    dsimp only [R_val]; ring
  rw [hb_eq_R, hRL_eq]
  dsimp only [L_val]
  rw [← MeasureTheory.integral_const_mul c₂s, ← integral_sub hint_a1 hint_a2]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  set z : ℂ := (a : ℂ) + (v : ℂ) * I
  unfold smoothAFEZetaMellinIntegrand
  have h2y_z : ((2 * y : ℝ) : ℂ) ^ z = (2 : ℂ) ^ z * (y : ℂ) ^ z := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg two_pos.le hy.le z]
    norm_num
  have h2_comb : c₂s * (2 : ℂ) ^ z = (2 : ℂ) ^ (-(1 - s - z)) := by
    dsimp only [c₂s]
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    congr 1; ring
  dsimp only [y] at h2y_z ⊢
  rw [h2y_z]
  calc riemannZeta (s + z) * (((d : ℝ) * x : ℝ) : ℂ) ^ z * smoothAFEGaussianKernel z -
          c₂s * (riemannZeta (s + z) * ((2 : ℂ) ^ z * (((d : ℝ) * x : ℝ) : ℂ) ^ z) *
            smoothAFEGaussianKernel z)
      = riemannZeta (s + z) * (1 - c₂s * (2 : ℂ) ^ z) *
          (((d : ℝ) * x : ℝ) : ℂ) ^ z * smoothAFEGaussianKernel z := by ring
    _ = riemannZeta (s + z) * (1 - (2 : ℂ) ^ (-(1 - s - z))) *
          (((d : ℝ) * x : ℝ) : ℂ) ^ z * smoothAFEGaussianKernel z := by rw [h2_comb]

/-- **Exact zero-residue critical-line integral representation of `smoothOuterDirectPairSum`:**
for every `s ∈ ℂ` with `0 < Re s < 1 / 2`, every `x > 0`, and every `d ≥ 1`, shifting
`smoothOuterDirectPairSum s x d` to `a = 1 / 2 - Re s > 0` evaluates `ζ` purely along the
critical line `linePt (Im s + v) = 1 / 2 + i (Im s + v)` with zero residue. -/
theorem smoothOuterDirectPairSum_eq_criticalLine_integral
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) {x : ℝ} (hx : 0 < x) {d : ℕ} (hd1 : 1 ≤ d) :
    smoothOuterDirectPairSum s x d =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ v : ℝ,
          riemannZeta (linePt (s.im + v)) *
            (1 - (2 : ℂ) ^ (-conj (linePt (s.im + v)))) *
            (((d : ℝ) * x : ℝ) : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
            smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hhi; norm_num at hhi
  set a : ℝ := 1 / 2 - s.re
  have ha0 : 0 < a := by dsimp only [a]; linarith
  have hab : a < 2 := by dsimp only [a]; linarith
  have hsa : s.re + a ≠ 1 := by dsimp only [a]; norm_num
  have hsb : 1 < s.re + 2 := by linarith
  rw [smoothOuterDirectPairSum_eq_mellin_shift_pos hs1 hx hd1 ha0 hab hsa hsb]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  have hsz : s + (((a : ℝ) : ℂ) + (v : ℂ) * I) = linePt (s.im + v) := by
    unfold linePt
    dsimp only [a]
    apply Complex.ext <;> simp
  have h1sz : 1 - s - (((a : ℝ) : ℂ) + (v : ℂ) * I) = conj (linePt (s.im + v)) := by
    rw [conj_linePt, ← hsz]
    ring
  dsimp only [a] at hsz h1sz
  rw [hsz, h1sz]

end Part1ZeroResidueCriticalLineShift


/-! ### Part 2: Exact Critical-Line Abscissa Elimination of `smoothOuterVaughanTypeII` -/

section Part2CriticalLineAbscissaElimination

/-- Purely critical-line smooth Vaughan Type-II Dirichlet series at ordinate `t ∈ ℝ` (`Re = 1 / 2`),
independent of any off-line abscissa `Re s`:
`∑_{d ≥ 1} ((μ - truncAF μ U) * typeIIShort V)(d) · d^{-(1/2 - i t)} · smoothAFECutoff(d / Y)`. -/
def criticalSmoothVaughanTypeII (U V : ℕ) (Y t : ℝ) : ℂ :=
  ∑' d : ℕ,
    (((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
        _root_.RHTower.Sieve.typeIIShort V) (d + 1) : ℝ) : ℂ) *
      ((d + 1 : ℕ) : ℂ) ^ (-conj (linePt t)) *
      smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)

lemma abs_vaughanTypeIICoeff_le_four_mul_sq (U V n : ℕ) (hn : 1 ≤ n) :
    |(((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
        _root_.RHTower.Sieve.typeIIShort V) n| ≤
      4 * (n : ℝ) ^ (2 : ℕ) := by
  have ht_le1 : ∀ N k : ℕ,
      |_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) N k| ≤ 1 :=
    fun N k => _root_.RHTower.Sieve.abs_truncAF_moebius_le_one N k
  have hm_le1 : ∀ k : ℕ, |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) k| ≤ 1 := fun k => by
    have h := ht_le1 k k
    rwa [_root_.RHTower.Sieve.truncAF_apply, if_pos le_rfl] at h
  have hLong : ∀ k : ℕ,
      |((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) k| ≤ 2 :=
    fun k => by
      change |(ArithmeticFunction.moebius : ArithmeticFunction ℝ) k -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U k| ≤ 2
      linarith [abs_sub ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) k)
        (_root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U k),
        hm_le1 k, ht_le1 U k]
  have hShort : ∀ k : ℕ, 1 ≤ k → |_root_.RHTower.Sieve.typeIIShort V k| ≤ 2 * (k : ℝ) := fun k hk => by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    change |(1 : ArithmeticFunction ℝ) k -
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) k| ≤ 2 * (k : ℝ)
    have h1_le : |(1 : ArithmeticFunction ℝ) k| ≤ 1 := by
      rw [ArithmeticFunction.one_apply]; split_ifs <;> norm_num
    have h2_le : |((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) k| ≤ (k : ℝ) := by
      rw [ArithmeticFunction.coe_zeta_mul_apply]
      have hcard : (k.divisors.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.card_divisors_le_self k
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_sum fun d _ => ht_le1 V d).trans (by simpa using hcard))
    linarith [abs_sub ((1 : ArithmeticFunction ℝ) k)
      (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) k)]
  have hinj : Set.InjOn Prod.fst (n.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
    rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ (rfl : a₁ = a₂)
    have hp₁ := (Nat.mem_divisorsAntidiagonal.mp h₁).1
    have hp₂ := (Nat.mem_divisorsAntidiagonal.mp h₂).1
    have ha₁ : 0 < a₁ := by
      by_contra h0; have hz : a₁ = 0 := by omega
      rw [hz, zero_mul] at hp₁; omega
    exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left ha₁ (hp₁.trans hp₂.symm))
  have hmaps : Set.MapsTo Prod.fst (n.divisorsAntidiagonal : Set (ℕ × ℕ)) (n.divisors : Set ℕ) :=
    fun p hp => Nat.mem_divisors.mpr ⟨⟨p.2, (Nat.mem_divisorsAntidiagonal.mp hp).1.symm⟩, by omega⟩
  have hcard : (n.divisorsAntidiagonal.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Finset.card_le_card_of_injOn Prod.fst hmaps hinj).trans (Nat.card_divisors_le_self n)
  rw [ArithmeticFunction.mul_apply]
  have hpt : ∀ p ∈ n.divisorsAntidiagonal,
      |((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) p.1 *
        _root_.RHTower.Sieve.typeIIShort V p.2| ≤ 4 * (n : ℝ) := by
    intro p hp
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hp2_pos : 1 ≤ p.2 := by
      by_contra h0; have hz : p.2 = 0 := by omega
      rw [hz, mul_zero] at hprod; omega
    have hp2_le : (p.2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hn ⟨p.1, by rw [mul_comm]; exact hprod.symm⟩
    rw [abs_mul]
    calc |((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
            _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) p.1| *
          |_root_.RHTower.Sieve.typeIIShort V p.2|
        ≤ 2 * (2 * (p.2 : ℝ)) :=
          mul_le_mul (hLong p.1) (hShort p.2 hp2_pos) (abs_nonneg _) zero_le_two
      _ ≤ 4 * (n : ℝ) := by linarith
  calc |∑ p ∈ n.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
            _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) p.1 *
            _root_.RHTower.Sieve.typeIIShort V p.2|
      ≤ ∑ p ∈ n.divisorsAntidiagonal,
          |((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
            _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) p.1 *
            _root_.RHTower.Sieve.typeIIShort V p.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, 4 * (n : ℝ) := Finset.sum_le_sum hpt
    _ = (n.divisorsAntidiagonal.card : ℝ) * (4 * (n : ℝ)) := by simp
    _ ≤ (n : ℝ) * (4 * (n : ℝ)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 4 * (n : ℝ) ^ (2 : ℕ) := by ring

private lemma exists_norm_riemannZeta_linePt_le :
    ∃ (C_line : ℝ) (N : ℕ), 0 < C_line ∧
      ∀ t : ℝ, ‖riemannZeta (linePt t)‖ ≤ C_line * (1 + |t|) ^ N := by
  have hcont : Continuous (fun t : ℝ => riemannZeta (linePt t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    refine (differentiableAt_riemannZeta ?_).continuousAt.comp (by unfold linePt; fun_prop)
    intro h1
    have hre := congrArg Complex.re h1
    rw [linePt_re, Complex.one_re] at hre
    norm_num at hre
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-1 : ℝ) 1) hcont.continuousOn
  obtain ⟨C, N, hC0, hC⟩ := exists_bound_norm_riemannZeta_strip 1
  set C_line : ℝ := max 1 (max M₀ C) + 1
  have hC_pos : 0 < C_line := by dsimp only [C_line]; linarith [le_max_left (1 : ℝ) (max M₀ C)]
  refine ⟨C_line, N, hC_pos, fun t => ?_⟩
  have h1t_ge1 : (1 : ℝ) ≤ (1 + |t|) ^ N := one_le_pow₀ (by linarith [abs_nonneg t])
  rcases le_or_gt (|t|) 1 with ht1 | ht1
  · have hmem : t ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp ht1
    have hb := hM₀ t hmem
    have hM_le : M₀ ≤ C_line :=
      ((le_max_left M₀ C).trans (le_max_right 1 _)).trans (by dsimp only [C_line]; linarith)
    calc ‖riemannZeta (linePt t)‖
        ≤ M₀ := hb
      _ ≤ C_line * 1 := by linarith
      _ ≤ C_line * (1 + |t|) ^ N := mul_le_mul_of_nonneg_left h1t_ge1 hC_pos.le
  · have hb := hC (1 / 2) t (by norm_num) ht1.le
    rw [show (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = linePt t from rfl] at hb
    have hC_le : C ≤ C_line :=
      ((le_max_right M₀ C).trans (le_max_right 1 _)).trans (by dsimp only [C_line]; linarith)
    have hpow_le : |t| ^ N ≤ (1 + |t|) ^ N :=
      pow_le_pow_left₀ (abs_nonneg t) (by linarith) N
    exact hb.trans (mul_le_mul hC_le hpow_le (by positivity) hC_pos.le)

lemma continuous_criticalSmoothVaughanTypeII (U V : ℕ) {Y : ℝ} (hY : 0 < Y) :
    Continuous (criticalSmoothVaughanTypeII U V Y) := by
  obtain ⟨K₄, hK₄0, hK₄⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 4) (by norm_num)
  refine continuous_tsum
    (fun d => ?_)
    ((summable_smoothAFEZetaMajorant (p := 2) (by norm_num)).mul_left (4 * K₄ * Y ^ (4 : ℝ)))
    (fun d t => ?_)
  · haveI : NeZero ((d + 1 : ℕ) : ℂ) := ⟨by exact_mod_cast Nat.succ_ne_zero d⟩
    have hpath : Continuous (fun t : ℝ => -conj (linePt t)) := by
      have hc : Continuous (fun t : ℝ => linePt t) := by unfold linePt; fun_prop
      exact (Complex.continuous_conj.comp hc).neg
    exact (continuous_const.mul ((continuous_const_cpow ((d + 1 : ℕ) : ℂ)).comp hpath)).mul
      continuous_const
  · have hd1 : 1 ≤ d + 1 := Nat.succ_pos d
    have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hd1
    have hc_bd : ‖(((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
        _root_.RHTower.Sieve.typeIIShort V) (d + 1) : ℝ) : ℂ)‖ ≤
        4 * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_two]
      exact abs_vaughanTypeIICoeff_le_four_mul_sq U V (d + 1) hd1
    have hcpow_le1 : ‖((d + 1 : ℕ) : ℂ) ^ (-conj (linePt t))‖ ≤ 1 := by
      rw [show ((d + 1 : ℕ) : ℂ) = (((d + 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hd_pos,
        show (-conj (linePt t)).re = -(1 / 2 : ℝ) by rw [conj_linePt]; simp [linePt_re]; norm_num]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) (by norm_num)
    have hW := norm_smoothAFECutoff_div_le' hK₄ hd_pos hY
    have hrpow_cancel :
        ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ =
          1 / (d + 1 : ℝ) ^ (2 : ℝ) := by
      rw [← Real.rpow_neg hd_pos.le, ← Real.rpow_add hd_pos,
        show (2 : ℝ) + (-4 : ℝ) = -2 by norm_num, Real.rpow_neg hd_pos.le, one_div]
      push_cast; rfl
    rw [norm_mul, norm_mul]
    calc ‖(((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
            _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
            _root_.RHTower.Sieve.typeIIShort V) (d + 1) : ℝ) : ℂ)‖ *
          ‖((d + 1 : ℕ) : ℂ) ^ (-conj (linePt t))‖ *
          ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖
        ≤ (4 * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ)) * 1 *
            (K₄ * ((((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ * Y ^ (4 : ℝ))) :=
          mul_le_mul (mul_le_mul hc_bd hcpow_le1 (norm_nonneg _) (by positivity))
            hW (norm_nonneg _) (by positivity)
      _ = (4 * K₄ * Y ^ (4 : ℝ)) *
            (((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹) := by ring
      _ = (4 * K₄ * Y ^ (4 : ℝ)) * (1 / (d + 1 : ℝ) ^ (2 : ℝ)) := by rw [hrpow_cancel]

/-- **Exact critical-line abscissa elimination of `smoothOuterVaughanTypeII`:**
for all `U, V : ℕ`, `x > 0`, `Y > 0`, and `0 < Re s < 1 / 2`, substituting
`smoothOuterDirectPairSum_eq_criticalLine_integral` and commuting `∑' d` with `∫ v : ℝ` cancels
`Re s` identically inside every Dirichlet term, pairing `riemannZeta (linePt (Im s + v))` against
`criticalSmoothVaughanTypeII U V Y (Im s + v)` purely on `Re = 1 / 2`. -/
theorem smoothOuterVaughanTypeII_eq_criticalLine_pairing
    (U V : ℕ) {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y)
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) :
    smoothOuterVaughanTypeII U V s x Y =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ v : ℝ,
          (x : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
            smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
            riemannZeta (linePt (s.im + v)) *
            (1 - (2 : ℂ) ^ (-conj (linePt (s.im + v)))) *
            criticalSmoothVaughanTypeII U V Y (s.im + v) := by
  set a : ℝ := 1 / 2 - s.re
  have ha0 : 0 < a := by dsimp only [a]; linarith
  obtain ⟨K₄, hK₄0, hK₄⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 4) (by norm_num)
  obtain ⟨C_line, N_ζ, hC_line_pos, hC_line⟩ := exists_norm_riemannZeta_linePt_le
  set c_UV : ℕ → ℂ := fun d =>
    (((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
        _root_.RHTower.Sieve.typeIIShort V) (d + 1) : ℝ) : ℂ)
  set Ψ : ℝ → ℂ := fun v =>
    (x : ℂ) ^ (((a : ℝ) : ℂ) + (v : ℂ) * I) *
      smoothAFEGaussianKernel (((a : ℝ) : ℂ) + (v : ℂ) * I) *
      riemannZeta (linePt (s.im + v)) *
      (1 - (2 : ℂ) ^ (-conj (linePt (s.im + v))))
  set G_term : ℕ → ℝ → ℂ := fun d v =>
    Ψ v * (c_UV d * ((d + 1 : ℕ) : ℂ) ^ (-conj (linePt (s.im + v))) *
      smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y))
  -- Step 1: Identify each `d`-term with `(1 / (2π)) * ∫ v, G_term d v`.
  have hd_eq : ∀ d : ℕ,
      c_UV d * ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
          smoothOuterDirectPairSum s x (d + 1) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) * ∫ v : ℝ, G_term d v := by
    intro d
    have hd1 : 1 ≤ d + 1 := Nat.succ_pos d
    have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hd1
    have hd_ne0 : ((d + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
    rw [smoothOuterDirectPairSum_eq_criticalLine_integral hs0 hhi hx hd1]
    have hpull :
        c_UV d * ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
          ((((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ∫ v : ℝ,
              riemannZeta (linePt (s.im + v)) *
                (1 - (2 : ℂ) ^ (-conj (linePt (s.im + v)))) *
                ((((d + 1 : ℕ) : ℝ) * x : ℝ) : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
                smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I)) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ((c_UV d * ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)) *
            ∫ v : ℝ,
              riemannZeta (linePt (s.im + v)) *
                (1 - (2 : ℂ) ^ (-conj (linePt (s.im + v)))) *
                ((((d + 1 : ℕ) : ℝ) * x : ℝ) : ℂ) ^ (((a : ℝ) : ℂ) + (v : ℂ) * I) *
                smoothAFEGaussianKernel (((a : ℝ) : ℂ) + (v : ℂ) * I)) := by
      dsimp only [a]; ring
    rw [hpull, ← MeasureTheory.integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    set z₂ : ℂ := ((a : ℝ) : ℂ) + (v : ℂ) * I
    have hdx_cpow : ((((d + 1 : ℕ) : ℝ) * x : ℝ) : ℂ) ^ z₂ =
        ((d + 1 : ℕ) : ℂ) ^ z₂ * (x : ℂ) ^ z₂ := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hd_pos.le hx.le z₂]
      push_cast; rfl
    have hd_comb : ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * ((d + 1 : ℕ) : ℂ) ^ z₂ =
        ((d + 1 : ℕ) : ℂ) ^ (-conj (linePt (s.im + v))) := by
      rw [← Complex.cpow_add _ _ hd_ne0]
      congr 1
      rw [conj_linePt]
      unfold linePt
      dsimp only [z₂, a]
      apply Complex.ext <;> simp
    dsimp only [G_term, Ψ]
    rw [hdx_cpow]
    calc (c_UV d * ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)) *
            (riemannZeta (linePt (s.im + v)) *
              (1 - (2 : ℂ) ^ (-conj (linePt (s.im + v)))) *
              (((d + 1 : ℕ) : ℂ) ^ z₂ * (x : ℂ) ^ z₂) *
              smoothAFEGaussianKernel z₂)
        = (x : ℂ) ^ z₂ * smoothAFEGaussianKernel z₂ *
            riemannZeta (linePt (s.im + v)) *
            (1 - (2 : ℂ) ^ (-conj (linePt (s.im + v)))) *
            (c_UV d * (((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * ((d + 1 : ℕ) : ℂ) ^ z₂) *
              smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)) := by ring
      _ = (x : ℂ) ^ z₂ * smoothAFEGaussianKernel z₂ *
            riemannZeta (linePt (s.im + v)) *
            (1 - (2 : ℂ) ^ (-conj (linePt (s.im + v)))) *
            (c_UV d * ((d + 1 : ℕ) : ℂ) ^ (-conj (linePt (s.im + v))) *
              smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)) := by rw [hd_comb]
  -- Step 2: Uniform product majorant on `G_term d v` and Fubini exchange.
  set C_Ψ : ℝ := x ^ a * (Real.exp (a ^ (2 : ℕ)) / a) * C_line * (1 + |s.im|) ^ N_ζ * 2
  have hΨ_bd : ∀ v : ℝ, ‖Ψ v‖ ≤ C_Ψ * ((1 + |v|) ^ N_ζ * Real.exp (-(v ^ (2 : ℕ)))) := by
    intro v
    dsimp only [Ψ]
    set z₂ : ℂ := ((a : ℝ) : ℂ) + (v : ℂ) * I
    have hx_eq : ‖(x : ℂ) ^ z₂‖ = x ^ a := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, show z₂.re = a by simp [z₂]]
    have hker := norm_smoothAFEGaussianKernel_vertical_le ha0 v
    have hζ_v : ‖riemannZeta (linePt (s.im + v))‖ ≤
        C_line * (1 + |s.im|) ^ N_ζ * (1 + |v|) ^ N_ζ := by
      have hb := hC_line (s.im + v)
      have hv_add : (1 + |s.im + v|) ^ N_ζ ≤ (1 + |s.im|) ^ N_ζ * (1 + |v|) ^ N_ζ := by
        rw [← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ N_ζ
        have habs := abs_add_le s.im v
        nlinarith [abs_nonneg s.im, abs_nonneg v]
      exact hb.trans ((mul_le_mul_of_nonneg_left hv_add hC_line_pos.le).trans_eq (by ring))
    have h12_le : ‖1 - (2 : ℂ) ^ (-conj (linePt (s.im + v)))‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos two_pos,
        show (-conj (linePt (s.im + v))).re = -(1 / 2 : ℝ) by
          rw [conj_linePt]; simp [linePt_re]; norm_num]
      linarith [Real.rpow_le_one_of_one_le_of_nonpos one_lt_two.le (by norm_num : -(1 / 2 : ℝ) ≤ 0)]
    rw [norm_mul, norm_mul, norm_mul, hx_eq]
    calc x ^ a * ‖smoothAFEGaussianKernel z₂‖ * ‖riemannZeta (linePt (s.im + v))‖ *
            ‖1 - (2 : ℂ) ^ (-conj (linePt (s.im + v)))‖
        ≤ x ^ a * ((Real.exp (a ^ (2 : ℕ)) / a) * Real.exp (-(v ^ (2 : ℕ)))) *
            (C_line * (1 + |s.im|) ^ N_ζ * (1 + |v|) ^ N_ζ) * 2 :=
          mul_le_mul
            (mul_le_mul
              (mul_le_mul_of_nonneg_left hker (by positivity))
              hζ_v (norm_nonneg _) (by positivity))
            h12_le (norm_nonneg _) (by positivity)
      _ = C_Ψ * ((1 + |v|) ^ N_ζ * Real.exp (-(v ^ (2 : ℕ)))) := by dsimp only [C_Ψ]; ring
  have hΨ_cont : Continuous Ψ := by
    haveI : NeZero (x : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
    haveI : NeZero (2 : ℂ) := ⟨by norm_num⟩
    have hpath : Continuous (fun v : ℝ => ((a : ℝ) : ℂ) + (v : ℂ) * I) := by fun_prop
    have hlp : Continuous (fun v : ℝ => linePt (s.im + v)) := by unfold linePt; fun_prop
    have hx_c : Continuous (fun v : ℝ => (x : ℂ) ^ (((a : ℝ) : ℂ) + (v : ℂ) * I)) :=
      (continuous_const_cpow (x : ℂ)).comp hpath
    have hker_c : Continuous (fun v : ℝ => smoothAFEGaussianKernel (((a : ℝ) : ℂ) + (v : ℂ) * I)) := by
      unfold smoothAFEGaussianKernel
      exact (Complex.continuous_exp.comp (hpath.pow 2)).div hpath fun v h0 => by
        have hre := congrArg Complex.re h0; simp at hre; exact ha0.ne' hre
    have hζ_c : Continuous (fun v : ℝ => riemannZeta (linePt (s.im + v))) := by
      rw [continuous_iff_continuousAt]; intro v
      refine (differentiableAt_riemannZeta ?_).continuousAt.comp hlp.continuousAt
      intro h1; have hre := congrArg Complex.re h1; rw [linePt_re, Complex.one_re] at hre; norm_num at hre
    have h12_c : Continuous (fun v : ℝ => 1 - (2 : ℂ) ^ (-conj (linePt (s.im + v)))) :=
      continuous_const.sub ((continuous_const_cpow (2 : ℂ)).comp ((Complex.continuous_conj.comp hlp).neg))
    exact (((hx_c.mul hker_c).mul hζ_c).mul h12_c)
  have hG_pt : ∀ (d : ℕ) (v : ℝ),
      ‖G_term d v‖ ≤ (C_Ψ * (4 * K₄ * Y ^ (4 : ℝ))) *
        (1 / (d + 1 : ℝ) ^ (2 : ℝ)) * ((1 + |v|) ^ N_ζ * Real.exp (-(v ^ (2 : ℕ)))) := by
    intro d v
    have hd1 : 1 ≤ d + 1 := Nat.succ_pos d
    have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hd1
    have hc_bd : ‖c_UV d‖ ≤ 4 * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) := by
      dsimp only [c_UV]
      rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_two]
      exact abs_vaughanTypeIICoeff_le_four_mul_sq U V (d + 1) hd1
    have hcpow_le1 : ‖((d + 1 : ℕ) : ℂ) ^ (-conj (linePt (s.im + v)))‖ ≤ 1 := by
      rw [show ((d + 1 : ℕ) : ℂ) = (((d + 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hd_pos,
        show (-conj (linePt (s.im + v))).re = -(1 / 2 : ℝ) by
          rw [conj_linePt]; simp [linePt_re]; norm_num]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) (by norm_num)
    have hW := norm_smoothAFECutoff_div_le' hK₄ hd_pos hY
    have hrpow_cancel :
        ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ =
          1 / (d + 1 : ℝ) ^ (2 : ℝ) := by
      rw [← Real.rpow_neg hd_pos.le, ← Real.rpow_add hd_pos,
        show (2 : ℝ) + (-4 : ℝ) = -2 by norm_num, Real.rpow_neg hd_pos.le, one_div]
      push_cast; rfl
    have hd_tail :
        ‖c_UV d * ((d + 1 : ℕ) : ℂ) ^ (-conj (linePt (s.im + v))) *
            smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖ ≤
          (4 * K₄ * Y ^ (4 : ℝ)) * (1 / (d + 1 : ℝ) ^ (2 : ℝ)) := by
      rw [norm_mul, norm_mul]
      calc ‖c_UV d‖ * ‖((d + 1 : ℕ) : ℂ) ^ (-conj (linePt (s.im + v)))‖ *
              ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖
          ≤ (4 * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ)) * 1 *
              (K₄ * ((((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ * Y ^ (4 : ℝ))) :=
            mul_le_mul (mul_le_mul hc_bd hcpow_le1 (norm_nonneg _) (by positivity))
              hW (norm_nonneg _) (by positivity)
        _ = (4 * K₄ * Y ^ (4 : ℝ)) *
              (((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹) := by ring
        _ = (4 * K₄ * Y ^ (4 : ℝ)) * (1 / (d + 1 : ℝ) ^ (2 : ℝ)) := by rw [hrpow_cancel]
    dsimp only [G_term]
    rw [norm_mul (Ψ v)]
    calc ‖Ψ v‖ * ‖c_UV d * ((d + 1 : ℕ) : ℂ) ^ (-conj (linePt (s.im + v))) *
            smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖
        ≤ (C_Ψ * ((1 + |v|) ^ N_ζ * Real.exp (-(v ^ (2 : ℕ))))) *
            ((4 * K₄ * Y ^ (4 : ℝ)) * (1 / (d + 1 : ℝ) ^ (2 : ℝ))) :=
          mul_le_mul (hΨ_bd v) hd_tail (norm_nonneg _) (by dsimp only [C_Ψ]; positivity)
      _ = (C_Ψ * (4 * K₄ * Y ^ (4 : ℝ))) *
            (1 / (d + 1 : ℝ) ^ (2 : ℝ)) * ((1 + |v|) ^ N_ζ * Real.exp (-(v ^ (2 : ℕ)))) := by ring
  have hG_int : ∀ d : ℕ, Integrable (G_term d) := fun d => by
    haveI : NeZero ((d + 1 : ℕ) : ℂ) := ⟨by exact_mod_cast Nat.succ_ne_zero d⟩
    have hlp : Continuous (fun v : ℝ => -conj (linePt (s.im + v))) := by
      have hc : Continuous (fun v : ℝ => linePt (s.im + v)) := by unfold linePt; fun_prop
      exact (Complex.continuous_conj.comp hc).neg
    have hcont : Continuous (G_term d) :=
      hΨ_cont.mul ((continuous_const.mul ((continuous_const_cpow ((d + 1 : ℕ) : ℂ)).comp hlp)).mul
        continuous_const)
    exact Integrable.mono'
      ((integrable_shifted_pow_mul_exp_neg_sq 1 N_ζ).const_mul
        ((C_Ψ * (4 * K₄ * Y ^ (4 : ℝ))) * (1 / (d + 1 : ℝ) ^ (2 : ℝ))))
      hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall (hG_pt d))
  have hG_sum_norm : Summable (fun d : ℕ => ∫ v : ℝ, ‖G_term d v‖) := by
    set I_N : ℝ := ∫ v : ℝ, (1 + |v|) ^ N_ζ * Real.exp (-(v ^ (2 : ℕ)))
    have hg_int := integrable_shifted_pow_mul_exp_neg_sq 1 N_ζ
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun d => ?_)
      ((summable_smoothAFEZetaMajorant (p := 2) (by norm_num)).mul_left
        (C_Ψ * (4 * K₄ * Y ^ (4 : ℝ)) * I_N))
    calc ∫ v : ℝ, ‖G_term d v‖
        ≤ ∫ v : ℝ, ((C_Ψ * (4 * K₄ * Y ^ (4 : ℝ))) * (1 / (d + 1 : ℝ) ^ (2 : ℝ))) *
            ((1 + |v|) ^ N_ζ * Real.exp (-(v ^ (2 : ℕ)))) :=
          integral_mono_ae (hG_int d).norm (hg_int.const_mul _) (Filter.Eventually.of_forall (hG_pt d))
      _ = (C_Ψ * (4 * K₄ * Y ^ (4 : ℝ)) * I_N) * (1 / (d + 1 : ℝ) ^ (2 : ℝ)) := by
          rw [MeasureTheory.integral_const_mul]; dsimp only [I_N]; ring
  unfold smoothOuterVaughanTypeII
  rw [tsum_congr hd_eq, tsum_mul_left,
    MeasureTheory.integral_tsum_of_summable_integral_norm hG_int hG_sum_norm]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only [G_term, Ψ, c_UV, a]
  rw [tsum_mul_left]
  rfl

end Part2CriticalLineAbscissaElimination


/-! ### Part 3: Unconditional Trans-Horizon Shell Localization of `smoothOuterVaughanTypeII` on `Ω_open` -/

section Part3TransHorizonShellLocalization

/-- Finite trans-horizon shell truncation of `smoothOuterVaughanTypeII` on `L_lo < d ≤ L_hi`. -/
def smoothOuterVaughanTypeIIShell (U V L_lo L_hi : ℕ) (s : ℂ) (x Y : ℝ) : ℂ :=
  ∑ d ∈ Finset.Ioc L_lo L_hi,
    (((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
        _root_.RHTower.Sieve.typeIIShort V) d : ℝ) : ℂ) *
      (d : ℂ) ^ (-(1 - s)) * smoothAFECutoff ((d : ℝ) / Y) *
      smoothOuterDirectPairSum s x d

/-- **Unconditional trans-horizon finite-shell localization of `smoothOuterVaughanTypeII` across ALL
of `Ω_open`:** for every `η ≥ 1`, `0 < δ`, and `B_dec > 0`, setting
`x(s) = |Im s|^{-(1 + η)}` and `Y(s) = |Im s|^{3 + η}`, truncating `smoothOuterVaughanTypeII` to the
finite integer shell `⌊|Im s|^{1 + η - δ}⌋₊ < d ≤ ⌈|Im s|^{3 + η + δ}⌉₊` incurs error
`≤ C_loc * |Im s|^{-B_dec}` uniformly across **every** point `s ∈ Ω_open` and **all** `U, V : ℕ`. -/
theorem exists_smoothOuterVaughanTypeII_shell_localization_on_remaining_strip
    {η δ B_dec : ℝ} (hη1 : 1 ≤ η) (hδ_pos : 0 < δ) (hB_pos : 0 < B_dec) :
    ∃ C_loc : ℝ, 0 < C_loc ∧
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∀ (U V : ℕ),
          ‖smoothOuterVaughanTypeII U V s (|s.im| ^ (-(1 + η))) (|s.im| ^ (3 + η)) -
              smoothOuterVaughanTypeIIShell U V
                (Nat.floor (|s.im| ^ (1 + η - δ)))
                (Nat.ceil (|s.im| ^ (3 + η + δ)))
                s (|s.im| ^ (-(1 + η))) (|s.im| ^ (3 + η))‖ ≤
            C_loc * |s.im| ^ (-B_dec) := by
  -- Low-side exponent `A₁ ≥ 2`: `3 * (1 + η) - δ * A₁ ≤ -B_dec`.
  set A₁ : ℕ := max 2 (Nat.ceil ((3 * (1 + η) + B_dec) / δ))
  have hA₁_ge2 : (2 : ℝ) ≤ (A₁ : ℝ) := by exact_mod_cast le_max_left 2 _
  have hA₁_bd : 3 * (1 + η) + B_dec ≤ δ * (A₁ : ℝ) := by
    have hc : (3 * (1 + η) + B_dec) / δ ≤ (Nat.ceil ((3 * (1 + η) + B_dec) / δ) : ℝ) := Nat.le_ceil _
    have hm : (Nat.ceil ((3 * (1 + η) + B_dec) / δ) : ℝ) ≤ (A₁ : ℝ) := by exact_mod_cast le_max_right 2 _
    have h := (div_le_iff₀ hδ_pos).mp (hc.trans hm)
    linarith
  -- High-side extra decay `M_hi ≥ 1`: `6 * (3 + η) - δ * M_hi ≤ -B_dec`.
  set M_hi : ℕ := Nat.ceil ((6 * (3 + η) + B_dec) / δ)
  have hnum6_pos : 0 < 6 * (3 + η) + B_dec := by linarith
  have hM_hi_pos : (0 : ℝ) < (M_hi : ℝ) :=
    (div_pos hnum6_pos hδ_pos).trans_le (Nat.le_ceil _)
  have hM_hi_bd : 6 * (3 + η) + B_dec ≤ δ * (M_hi : ℝ) := by
    have hc : (6 * (3 + η) + B_dec) / δ ≤ (M_hi : ℝ) := Nat.le_ceil _
    have h := (div_le_iff₀ hδ_pos).mp hc
    linarith
  obtain ⟨M_cut, hM_cut1, hM_cut⟩ := exists_norm_smoothAFECutoff_uniform_le
  have hM_cut_pos : 0 < M_cut := zero_lt_one.trans_le hM_cut1
  have hSmaj2_nn : 0 ≤ smoothAFEZetaMajorant 2 := tsum_nonneg fun _ => by positivity
  obtain ⟨K_A₁, hKA₁0, hKA₁⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := (A₁ : ℝ)) (by linarith)
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 2) (by norm_num)
  obtain ⟨K_hi, hKhi0, hKhi⟩ :=
    exists_norm_smoothAFECutoff_le_neg_rpow (A := 6 + (M_hi : ℝ)) (by linarith [hM_hi_pos])
  set C_lo : ℝ := 4 * M_cut * ((1 + (2 : ℝ) ^ (A₁ : ℝ)) * K_A₁ * smoothAFEZetaMajorant 2) + 1
  set C_hi : ℝ := 4 * K_hi * ((1 + (2 : ℝ) ^ (2 : ℝ)) * K₂ * smoothAFEZetaMajorant 2) *
    smoothAFEZetaMajorant 2 + 1
  refine ⟨C_lo + C_hi, by dsimp only [C_lo, C_hi]; positivity, ?_⟩
  intro s hlo hhi him U V
  set τ : ℝ := |s.im|
  have hτ1 : 1 ≤ τ := by dsimp only [τ]; linarith
  have hτ_pos : 0 < τ := by dsimp only [τ]; linarith
  have hs0 : 0 < s.re := by linarith
  set x : ℝ := τ ^ (-(1 + η))
  set Y : ℝ := τ ^ (3 + η)
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hτ_pos _
  have hY_pos : 0 < Y := Real.rpow_pos_of_pos hτ_pos _
  set L_lo : ℕ := Nat.floor (τ ^ (1 + η - δ))
  set L_hi : ℕ := Nat.ceil (τ ^ (3 + η + δ))
  have hL_le : L_lo ≤ L_hi := by
    have hrp : τ ^ (1 + η - δ) ≤ τ ^ (3 + η + δ) :=
      Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith)
    have hfl : (L_lo : ℝ) ≤ τ ^ (1 + η - δ) := Nat.floor_le (Real.rpow_nonneg hτ_pos.le _)
    have hcl : τ ^ (3 + η + δ) ≤ (L_hi : ℝ) := Nat.le_ceil _
    exact_mod_cast (hfl.trans hrp).trans hcl
  set f_II : ℕ → ℂ := fun d =>
    (((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
        _root_.RHTower.Sieve.typeIIShort V) (d + 1) : ℝ) : ℂ) *
      ((d + 1 : ℕ) : ℂ) ^ (-(1 - s)) * smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y) *
      smoothOuterDirectPairSum s x (d + 1)
  -- Summability of `f_II`.
  obtain ⟨K₆, hK₆0, hK₆⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 6) (by norm_num)
  set C_p2 : ℝ := (1 + (2 : ℝ) ^ (2 : ℝ)) * K₂ * smoothAFEZetaMajorant 2 * x ^ (2 : ℝ)
  have hf_sum : Summable f_II := by
    refine Summable.of_norm_bounded
      ((summable_smoothAFEZetaMajorant (p := 2) (by norm_num)).mul_left (4 * K₆ * Y ^ (6 : ℝ) * C_p2))
      fun d => ?_
    have hd1 : 1 ≤ d + 1 := Nat.succ_pos d
    have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hd1
    have hc_bd : ‖(((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
        _root_.RHTower.Sieve.typeIIShort V) (d + 1) : ℝ) : ℂ)‖ ≤
        4 * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_two]
      exact abs_vaughanTypeIICoeff_le_four_mul_sq U V (d + 1) hd1
    have hd_cpow : ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ ≤ 1 := by
      rw [show ((d + 1 : ℕ) : ℂ) = (((d + 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hd_pos]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) (by simp; linarith)
    have hW := norm_smoothAFECutoff_div_le' hK₆ hd_pos hY_pos
    have hp := norm_smoothOuterDirectPairSum_le (le_refl 2) hK₂0 hK₂ hs0 hhi hx_pos hd1
    rw [Real.mul_rpow hd_pos.le hx_pos.le] at hp
    have hp' : ‖smoothOuterDirectPairSum s x (d + 1)‖ ≤ C_p2 * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) := by
      dsimp only [C_p2]; linarith
    have hrpow_cancel :
        ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (6 : ℝ))⁻¹ * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) =
          1 / (d + 1 : ℝ) ^ (2 : ℝ) := by
      rw [← Real.rpow_neg hd_pos.le, ← Real.rpow_add hd_pos, ← Real.rpow_add hd_pos,
        show (2 : ℝ) + (-6 : ℝ) + 2 = -2 by norm_num, Real.rpow_neg hd_pos.le, one_div]
      push_cast; rfl
    dsimp only [f_II]
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖(((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
            _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
            _root_.RHTower.Sieve.typeIIShort V) (d + 1) : ℝ) : ℂ)‖ *
          ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ * ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖ *
          ‖smoothOuterDirectPairSum s x (d + 1)‖
        ≤ (4 * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ)) * 1 *
            (K₆ * ((((d + 1 : ℕ) : ℝ) ^ (6 : ℝ))⁻¹ * Y ^ (6 : ℝ))) *
            (C_p2 * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ)) :=
          mul_le_mul
            (mul_le_mul (mul_le_mul hc_bd hd_cpow (norm_nonneg _) (by positivity))
              hW (norm_nonneg _) (by positivity))
            hp' (norm_nonneg _) (by positivity)
      _ = (4 * K₆ * Y ^ (6 : ℝ) * C_p2) *
            (((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (6 : ℝ))⁻¹ * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ)) := by
          ring
      _ = (4 * K₆ * Y ^ (6 : ℝ) * C_p2) * (1 / (d + 1 : ℝ) ^ (2 : ℝ)) := by rw [hrpow_cancel]
  -- Split `∑' d, f_II d` into `range L_lo` + `(range L_hi \ range L_lo)` + `∑' j, f_II (j + L_hi)`.
  have hsplit_hi := (hf_sum.sum_add_tsum_nat_add L_hi).symm
  have hsplit_lo :
      (∑ d ∈ Finset.range L_hi, f_II d) =
        (∑ d ∈ Finset.range L_lo, f_II d) +
          smoothOuterVaughanTypeIIShell U V L_lo L_hi s x Y := by
    have hsub : Finset.range L_lo ⊆ Finset.range L_hi := Finset.range_mono hL_le
    rw [← Finset.sum_sdiff hsub, add_comm]
    congr 1
    unfold smoothOuterVaughanTypeIIShell
    refine Finset.sum_bij (fun d _ => d + 1)
      (fun d hd => by
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hd
        exact Finset.mem_Ioc.mpr ⟨by have := Finset.mem_range.not.mp h2; omega,
          by have := Finset.mem_range.mp h1; omega⟩)
      (fun _ _ _ _ h => by omega)
      (fun q hq => ⟨q - 1, Finset.mem_sdiff.mpr
        ⟨Finset.mem_range.mpr (by have := Finset.mem_Ioc.mp hq; omega),
          Finset.mem_range.not.mpr (by have := Finset.mem_Ioc.mp hq; omega)⟩,
        by have := Finset.mem_Ioc.mp hq; omega⟩)
      (fun _ _ => rfl)
  have hdiff_eq :
      smoothOuterVaughanTypeII U V s x Y - smoothOuterVaughanTypeIIShell U V L_lo L_hi s x Y =
        (∑ d ∈ Finset.range L_lo, f_II d) + ∑' j : ℕ, f_II (j + L_hi) := by
    change (∑' d : ℕ, f_II d) - smoothOuterVaughanTypeIIShell U V L_lo L_hi s x Y = _
    rw [hsplit_hi, hsplit_lo]
    ring
  rw [hdiff_eq]
  -- 1. Bound low-side prefix `‖∑ d ∈ range L_lo, f_II d‖ ≤ C_lo * τ ^ (-B_dec)`.
  have hlo_bd : ‖∑ d ∈ Finset.range L_lo, f_II d‖ ≤ C_lo * τ ^ (-B_dec) := by
    have hL_lo_le : (L_lo : ℝ) ≤ τ ^ (1 + η) :=
      (Nat.floor_le (Real.rpow_nonneg hτ_pos.le _)).trans
        (Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith))
    have hpt_lo : ∀ d ∈ Finset.range L_lo,
        ‖f_II d‖ ≤ C_lo * (τ ^ (2 * (1 + η)) * τ ^ (-δ * (A₁ : ℝ))) := by
      intro d hd
      have hd1 : 1 ≤ d + 1 := Nat.succ_pos d
      have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hd1
      have hd_le_Llo : d + 1 ≤ L_lo := by have := Finset.mem_range.mp hd; omega
      have hd_le_lo : ((d + 1 : ℕ) : ℝ) ≤ τ ^ (1 + η - δ) :=
        (by exact_mod_cast hd_le_Llo : ((d + 1 : ℕ) : ℝ) ≤ (L_lo : ℝ)).trans
          (Nat.floor_le (Real.rpow_nonneg hτ_pos.le _))
      have hd_le_1η : ((d + 1 : ℕ) : ℝ) ≤ τ ^ (1 + η) :=
        hd_le_lo.trans (Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith))
      have hd_sq_le : ((d + 1 : ℕ) : ℝ) ^ (2 : ℕ) ≤ τ ^ (2 * (1 + η)) := by
        calc ((d + 1 : ℕ) : ℝ) ^ (2 : ℕ)
            ≤ (τ ^ (1 + η)) ^ (2 : ℕ) := pow_le_pow_left₀ hd_pos.le hd_le_1η 2
          _ = τ ^ (2 * (1 + η)) := by
              rw [← Real.rpow_natCast (τ ^ _) 2, ← Real.rpow_mul hτ_pos.le]
              congr 1; push_cast; ring
      have hdx_le : ((d + 1 : ℕ) : ℝ) * x ≤ τ ^ (-δ) := by
        calc ((d + 1 : ℕ) : ℝ) * x
            ≤ τ ^ (1 + η - δ) * τ ^ (-(1 + η)) := mul_le_mul_of_nonneg_right hd_le_lo hx_pos.le
          _ = τ ^ (-δ) := by rw [← Real.rpow_add hτ_pos]; congr 1; ring
      have hdx_A₁ : (((d + 1 : ℕ) : ℝ) * x) ^ (A₁ : ℝ) ≤ τ ^ (-δ * (A₁ : ℝ)) :=
        (Real.rpow_le_rpow (mul_pos hd_pos hx_pos).le hdx_le (by linarith)).trans_eq
          (by rw [← Real.rpow_mul hτ_pos.le])
      have hc_bd : ‖(((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
          _root_.RHTower.Sieve.typeIIShort V) (d + 1) : ℝ) : ℂ)‖ ≤
          4 * τ ^ (2 * (1 + η)) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact (abs_vaughanTypeIICoeff_le_four_mul_sq U V (d + 1) hd1).trans (by linarith)
      have hd_cpow : ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ ≤ 1 := by
        rw [show ((d + 1 : ℕ) : ℂ) = (((d + 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_cpow_eq_rpow_re_of_pos hd_pos]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) (by simp; linarith)
      have hW_le := hM_cut (div_pos hd_pos hY_pos)
      have hp_le := (norm_smoothOuterDirectPairSum_le hA₁_ge2 hKA₁0 hKA₁ hs0 hhi hx_pos hd1).trans
        (mul_le_mul_of_nonneg_left hdx_A₁ (by positivity))
      dsimp only [f_II]
      rw [norm_mul, norm_mul, norm_mul]
      calc ‖(((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
              _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
              _root_.RHTower.Sieve.typeIIShort V) (d + 1) : ℝ) : ℂ)‖ *
            ‖((d + 1 : ℕ) : ℂ) ^ (-(1 - s))‖ * ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖ *
            ‖smoothOuterDirectPairSum s x (d + 1)‖
          ≤ (4 * τ ^ (2 * (1 + η))) * 1 * M_cut *
              (((1 + (2 : ℝ) ^ (A₁ : ℝ)) * K_A₁ * smoothAFEZetaMajorant 2) * τ ^ (-δ * (A₁ : ℝ))) :=
            mul_le_mul
              (mul_le_mul (mul_le_mul hc_bd hd_cpow (norm_nonneg _) (by positivity))
                hW_le (norm_nonneg _) (by positivity))
              hp_le (norm_nonneg _) (by positivity)
        _ ≤ C_lo * (τ ^ (2 * (1 + η)) * τ ^ (-δ * (A₁ : ℝ))) := by
            have hnn : 0 ≤ τ ^ (2 * (1 + η)) * τ ^ (-δ * (A₁ : ℝ)) := by positivity
            dsimp only [C_lo]; nlinarith
    calc ‖∑ d ∈ Finset.range L_lo, f_II d‖
        ≤ ∑ _d ∈ Finset.range L_lo, C_lo * (τ ^ (2 * (1 + η)) * τ ^ (-δ * (A₁ : ℝ))) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hpt_lo)
      _ = (L_lo : ℝ) * (C_lo * (τ ^ (2 * (1 + η)) * τ ^ (-δ * (A₁ : ℝ)))) := by simp
      _ ≤ τ ^ (1 + η) * (C_lo * (τ ^ (2 * (1 + η)) * τ ^ (-δ * (A₁ : ℝ)))) :=
          mul_le_mul_of_nonneg_right hL_lo_le (by dsimp only [C_lo]; positivity)
      _ = C_lo * (τ ^ (1 + η) * τ ^ (2 * (1 + η)) * τ ^ (-δ * (A₁ : ℝ))) := by ring
      _ ≤ C_lo * τ ^ (-B_dec) := by
          rw [← Real.rpow_add hτ_pos, ← Real.rpow_add hτ_pos]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith))
            (by dsimp only [C_lo]; positivity)
  -- 2. Bound high-side tail `‖∑' j, f_II (j + L_hi)‖ ≤ C_hi * τ ^ (-B_dec)`.
  have hhi_bd : ‖∑' j : ℕ, f_II (j + L_hi)‖ ≤ C_hi * τ ^ (-B_dec) := by
    set P_hi : ℝ := 4 * K_hi * ((1 + (2 : ℝ) ^ (2 : ℝ)) * K₂ * smoothAFEZetaMajorant 2) *
      Y ^ (6 : ℝ) * τ ^ (-δ * (M_hi : ℝ))
    have hP_hi_nn : 0 ≤ P_hi := by dsimp only [P_hi]; positivity
    have hx_le1 : x ^ (2 : ℝ) ≤ 1 :=
      Real.rpow_le_one (hx_pos.le) (Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by linarith)) zero_le_two
    have hpt_hi : ∀ j : ℕ, ‖f_II (j + L_hi)‖ ≤ P_hi * (1 / (j + 1 : ℝ) ^ (2 : ℝ)) := by
      intro j
      set q : ℕ := j + L_hi + 1
      have hq1 : 1 ≤ q := by dsimp only [q]; omega
      have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
      have hq_ge_hi : τ ^ (3 + η + δ) ≤ (q : ℝ) := by
        have hcl : τ ^ (3 + η + δ) ≤ (L_hi : ℝ) := Nat.le_ceil _
        have hnat : (L_hi : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by dsimp only [q]; omega : L_hi ≤ q)
        exact hcl.trans hnat
      have hqY_ge : τ ^ δ ≤ (q : ℝ) / Y := by
        have h1 : τ ^ (3 + η + δ) / Y = τ ^ δ := by
          dsimp only [Y]; rw [← Real.rpow_sub hτ_pos]; congr 1; ring
        rw [← h1]
        exact div_le_div_of_nonneg_right hq_ge_hi hY_pos.le
      have hW_raw := hKhi (div_pos hq_pos hY_pos)
      have hW_split :
          ((q : ℝ) / Y) ^ (-(6 + (M_hi : ℝ))) ≤
            (((q : ℝ) ^ (6 : ℝ))⁻¹ * Y ^ (6 : ℝ)) * τ ^ (-δ * (M_hi : ℝ)) := by
        have hexp : ((q : ℝ) / Y) ^ (-(6 + (M_hi : ℝ))) =
            ((q : ℝ) / Y) ^ (-6 : ℝ) * ((q : ℝ) / Y) ^ (-(M_hi : ℝ)) := by
          rw [← Real.rpow_add (div_pos hq_pos hY_pos)]; congr 1; ring
        have h6 : ((q : ℝ) / Y) ^ (-6 : ℝ) = ((q : ℝ) ^ (6 : ℝ))⁻¹ * Y ^ (6 : ℝ) := by
          rw [Real.div_rpow hq_pos.le hY_pos.le, Real.rpow_neg hq_pos.le,
            Real.rpow_neg hY_pos.le, div_inv_eq_mul]
        have hM : ((q : ℝ) / Y) ^ (-(M_hi : ℝ)) ≤ τ ^ (-δ * (M_hi : ℝ)) :=
          (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hτ_pos δ) hqY_ge
            (neg_nonpos.mpr (Nat.cast_nonneg M_hi))).trans_eq
            (show (τ ^ δ) ^ (-(M_hi : ℝ)) = τ ^ (-δ * (M_hi : ℝ)) by
              rw [← Real.rpow_mul hτ_pos.le]; congr 1; ring)
        rw [hexp, h6]
        exact mul_le_mul_of_nonneg_left hM (by positivity)
      have hW_bd : ‖smoothAFECutoff ((q : ℝ) / Y)‖ ≤
          K_hi * (((q : ℝ) ^ (6 : ℝ))⁻¹ * Y ^ (6 : ℝ)) * τ ^ (-δ * (M_hi : ℝ)) :=
        (hW_raw.trans (mul_le_mul_of_nonneg_left hW_split hKhi0)).trans_eq (by ring)
      have hc_bd : ‖(((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
          _root_.RHTower.Sieve.typeIIShort V) q : ℝ) : ℂ)‖ ≤ 4 * (q : ℝ) ^ (2 : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_two]
        exact abs_vaughanTypeIICoeff_le_four_mul_sq U V q hq1
      have hq_cpow : ‖(q : ℂ) ^ (-(1 - s))‖ ≤ 1 := by
        rw [show (q : ℂ) = ((q : ℝ) : ℂ) by simp, Complex.norm_cpow_eq_rpow_re_of_pos hq_pos]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hq1) (by simp; linarith)
      have hp := norm_smoothOuterDirectPairSum_le (le_refl 2) hK₂0 hK₂ hs0 hhi hx_pos hq1
      rw [Real.mul_rpow hq_pos.le hx_pos.le] at hp
      have hp' : ‖smoothOuterDirectPairSum s x q‖ ≤
          ((1 + (2 : ℝ) ^ (2 : ℝ)) * K₂ * smoothAFEZetaMajorant 2) * (q : ℝ) ^ (2 : ℝ) := by
        have h1 : x ^ (2 : ℝ) * (q : ℝ) ^ (2 : ℝ) ≤ 1 * (q : ℝ) ^ (2 : ℝ) :=
          mul_le_mul_of_nonneg_right hx_le1 (by positivity)
        have h2 := mul_le_mul_of_nonneg_left h1
          (show 0 ≤ (1 + (2 : ℝ) ^ (2 : ℝ)) * K₂ * smoothAFEZetaMajorant 2 by positivity)
        linarith
      have hq_inv : (q : ℝ) ^ (2 : ℝ) * ((q : ℝ) ^ (6 : ℝ))⁻¹ * (q : ℝ) ^ (2 : ℝ) ≤
          1 / (j + 1 : ℝ) ^ (2 : ℝ) := by
        rw [← Real.rpow_neg hq_pos.le, ← Real.rpow_add hq_pos, ← Real.rpow_add hq_pos,
          show (2 : ℝ) + (-6 : ℝ) + 2 = -2 by norm_num]
        have hjq : (j + 1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by dsimp only [q]; omega : j + 1 ≤ q)
        exact (Real.rpow_le_rpow_of_nonpos (by positivity) hjq (by norm_num)).trans_eq
          (show (j + 1 : ℝ) ^ (-2 : ℝ) = 1 / (j + 1 : ℝ) ^ (2 : ℝ) by
            rw [Real.rpow_neg (by positivity), one_div])
      change ‖(((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
          _root_.RHTower.Sieve.typeIIShort V) q : ℝ) : ℂ) *
        (q : ℂ) ^ (-(1 - s)) * smoothAFECutoff ((q : ℝ) / Y) *
        smoothOuterDirectPairSum s x q‖ ≤ P_hi * (1 / (j + 1 : ℝ) ^ (2 : ℝ))
      rw [norm_mul, norm_mul, norm_mul]
      calc ‖(((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
              _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
              _root_.RHTower.Sieve.typeIIShort V) q : ℝ) : ℂ)‖ *
            ‖(q : ℂ) ^ (-(1 - s))‖ * ‖smoothAFECutoff ((q : ℝ) / Y)‖ *
            ‖smoothOuterDirectPairSum s x q‖
          ≤ (4 * (q : ℝ) ^ (2 : ℝ)) * 1 *
              (K_hi * (((q : ℝ) ^ (6 : ℝ))⁻¹ * Y ^ (6 : ℝ)) * τ ^ (-δ * (M_hi : ℝ))) *
              (((1 + (2 : ℝ) ^ (2 : ℝ)) * K₂ * smoothAFEZetaMajorant 2) * (q : ℝ) ^ (2 : ℝ)) :=
            mul_le_mul
              (mul_le_mul (mul_le_mul hc_bd hq_cpow (norm_nonneg _) (by positivity))
                hW_bd (norm_nonneg _) (by positivity))
              hp' (norm_nonneg _) (by positivity)
        _ = P_hi * ((q : ℝ) ^ (2 : ℝ) * ((q : ℝ) ^ (6 : ℝ))⁻¹ * (q : ℝ) ^ (2 : ℝ)) := by
            dsimp only [P_hi]; ring
        _ ≤ P_hi * (1 / (j + 1 : ℝ) ^ (2 : ℝ)) := mul_le_mul_of_nonneg_left hq_inv hP_hi_nn
    have hmaj_hi := (summable_smoothAFEZetaMajorant (p := 2) (by norm_num)).mul_left P_hi
    have hs_tail : Summable (fun j : ℕ => f_II (j + L_hi)) :=
      Summable.of_norm_bounded hmaj_hi hpt_hi
    have hY6_pow : Y ^ (6 : ℝ) * τ ^ (-δ * (M_hi : ℝ)) ≤ τ ^ (-B_dec) := by
      dsimp only [Y]
      rw [← Real.rpow_mul hτ_pos.le, ← Real.rpow_add hτ_pos]
      exact Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith)
    calc ‖∑' j : ℕ, f_II (j + L_hi)‖
        ≤ ∑' j : ℕ, ‖f_II (j + L_hi)‖ := norm_tsum_le_tsum_norm hs_tail.norm
      _ ≤ ∑' j : ℕ, P_hi * (1 / (j + 1 : ℝ) ^ (2 : ℝ)) :=
          Summable.tsum_le_tsum hpt_hi hs_tail.norm hmaj_hi
      _ = P_hi * smoothAFEZetaMajorant 2 := tsum_mul_left
      _ = (4 * K_hi * ((1 + (2 : ℝ) ^ (2 : ℝ)) * K₂ * smoothAFEZetaMajorant 2) *
            smoothAFEZetaMajorant 2) * (Y ^ (6 : ℝ) * τ ^ (-δ * (M_hi : ℝ))) := by
          dsimp only [P_hi]; ring
      _ ≤ C_hi * τ ^ (-B_dec) := by
          have h1 := mul_le_mul_of_nonneg_left hY6_pow
            (show 0 ≤ 4 * K_hi * ((1 + (2 : ℝ) ^ (2 : ℝ)) * K₂ * smoothAFEZetaMajorant 2) *
              smoothAFEZetaMajorant 2 by positivity)
          have hnn : 0 ≤ τ ^ (-B_dec) := Real.rpow_nonneg hτ_pos.le _
          dsimp only [C_hi]; nlinarith
  have htri := norm_add_le (∑ d ∈ Finset.range L_lo, f_II d) (∑' j : ℕ, f_II (j + L_hi))
  linarith

end Part3TransHorizonShellLocalization


/-! ### Part 4: Amplified Critical-Line Excursion Forcing and Power-Saving Witness Production on `Ω_open` -/

section Part4CriticalLineAmplifiedForcing

/-- **Quantitative critical-line Gaussian moment bound on `smoothOuterVaughanTypeII`:**
for all `U, V : ℕ`, `x > 0`, `Y > 0`, and `0 < Re s < 1 / 2`, `‖smoothOuterVaughanTypeII U V s x Y‖`
is bounded above by `(exp(1 / 4) / (π * (1 / 2 - Re s))) * x^{1/2 - Re s}` times the
Gaussian-localized critical-line `L¹` moment of
`‖ζ(linePt (Im s + v)) * criticalSmoothVaughanTypeII U V Y (Im s + v)‖`. -/
theorem norm_smoothOuterVaughanTypeII_le_criticalLine_gaussian_moment
    (U V : ℕ) {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y)
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) :
    ‖smoothOuterVaughanTypeII U V s x Y‖ ≤
      (Real.exp (1 / 4) / (Real.pi * (1 / 2 - s.re))) * x ^ (1 / 2 - s.re) *
        ∫ v : ℝ, Real.exp (-(v ^ (2 : ℕ))) *
          ‖riemannZeta (linePt (s.im + v)) *
            criticalSmoothVaughanTypeII U V Y (s.im + v)‖ := by
  set a : ℝ := 1 / 2 - s.re
  have ha0 : 0 < a := by dsimp only [a]; linarith
  have ha_lt_half : a < 1 / 2 := by dsimp only [a]; linarith
  obtain ⟨K₄, hK₄0, hK₄⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 4) (by norm_num)
  obtain ⟨C_line, N_ζ, hC_line_pos, hC_line⟩ := exists_norm_riemannZeta_linePt_le
  -- Continuity and polynomial-Gaussian integrability of the nonnegative majorant.
  have hV_cont : Continuous (fun v : ℝ => criticalSmoothVaughanTypeII U V Y (s.im + v)) :=
    (continuous_criticalSmoothVaughanTypeII U V hY).comp (by fun_prop)
  have hζ_cont : Continuous (fun v : ℝ => riemannZeta (linePt (s.im + v))) := by
    rw [continuous_iff_continuousAt]; intro v
    refine (differentiableAt_riemannZeta ?_).continuousAt.comp (by unfold linePt; fun_prop)
    intro h1; have hre := congrArg Complex.re h1; rw [linePt_re, Complex.one_re] at hre; norm_num at hre
  have hV_bd : ∀ t : ℝ,
      ‖criticalSmoothVaughanTypeII U V Y t‖ ≤
        (4 * K₄ * Y ^ (4 : ℝ)) * smoothAFEZetaMajorant 2 := by
    intro t
    have hpt : ∀ d : ℕ,
        ‖(((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
            _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
            _root_.RHTower.Sieve.typeIIShort V) (d + 1) : ℝ) : ℂ) *
          ((d + 1 : ℕ) : ℂ) ^ (-conj (linePt t)) *
          smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖ ≤
          (4 * K₄ * Y ^ (4 : ℝ)) * (1 / (d + 1 : ℝ) ^ (2 : ℝ)) := by
      intro d
      have hd1 : 1 ≤ d + 1 := Nat.succ_pos d
      have hd_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hd1
      have hc_bd : ‖(((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
          _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
          _root_.RHTower.Sieve.typeIIShort V) (d + 1) : ℝ) : ℂ)‖ ≤
          4 * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_two]
        exact abs_vaughanTypeIICoeff_le_four_mul_sq U V (d + 1) hd1
      have hcpow_le1 : ‖((d + 1 : ℕ) : ℂ) ^ (-conj (linePt t))‖ ≤ 1 := by
        rw [show ((d + 1 : ℕ) : ℂ) = (((d + 1 : ℕ) : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_cpow_eq_rpow_re_of_pos hd_pos,
          show (-conj (linePt t)).re = -(1 / 2 : ℝ) by rw [conj_linePt]; simp [linePt_re]; norm_num]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) (by norm_num)
      have hW := norm_smoothAFECutoff_div_le' hK₄ hd_pos hY
      have hrpow_cancel :
          ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ =
            1 / (d + 1 : ℝ) ^ (2 : ℝ) := by
        rw [← Real.rpow_neg hd_pos.le, ← Real.rpow_add hd_pos,
          show (2 : ℝ) + (-4 : ℝ) = -2 by norm_num, Real.rpow_neg hd_pos.le, one_div]
        push_cast; rfl
      rw [norm_mul, norm_mul]
      calc ‖(((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
              _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
              _root_.RHTower.Sieve.typeIIShort V) (d + 1) : ℝ) : ℂ)‖ *
            ‖((d + 1 : ℕ) : ℂ) ^ (-conj (linePt t))‖ *
            ‖smoothAFECutoff (((d + 1 : ℕ) : ℝ) / Y)‖
          ≤ (4 * ((d + 1 : ℕ) : ℝ) ^ (2 : ℝ)) * 1 *
              (K₄ * ((((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹ * Y ^ (4 : ℝ))) :=
            mul_le_mul (mul_le_mul hc_bd hcpow_le1 (norm_nonneg _) (by positivity))
              hW (norm_nonneg _) (by positivity)
        _ = (4 * K₄ * Y ^ (4 : ℝ)) *
              (((d + 1 : ℕ) : ℝ) ^ (2 : ℝ) * (((d + 1 : ℕ) : ℝ) ^ (4 : ℝ))⁻¹) := by ring
        _ = (4 * K₄ * Y ^ (4 : ℝ)) * (1 / (d + 1 : ℝ) ^ (2 : ℝ)) := by rw [hrpow_cancel]
    have hmaj := (summable_smoothAFEZetaMajorant (p := 2) (by norm_num)).mul_left (4 * K₄ * Y ^ (4 : ℝ))
    have hs_t := Summable.of_norm_bounded hmaj hpt
    unfold criticalSmoothVaughanTypeII
    exact (norm_tsum_le_tsum_norm hs_t.norm).trans
      ((Summable.tsum_le_tsum hpt hs_t.norm hmaj).trans_eq tsum_mul_left)
  have hSmaj2_nn : 0 ≤ smoothAFEZetaMajorant 2 := tsum_nonneg fun _ => by positivity
  have hmom_int : Integrable (fun v : ℝ => Real.exp (-(v ^ (2 : ℕ))) *
      ‖riemannZeta (linePt (s.im + v)) * criticalSmoothVaughanTypeII U V Y (s.im + v)‖) := by
    have hcont_m : Continuous (fun v : ℝ => Real.exp (-(v ^ (2 : ℕ))) *
        ‖riemannZeta (linePt (s.im + v)) * criticalSmoothVaughanTypeII U V Y (s.im + v)‖) :=
      (Real.continuous_exp.comp (by fun_prop)).mul ((hζ_cont.mul hV_cont).norm)
    set C_dom : ℝ := C_line * (1 + |s.im|) ^ N_ζ * ((4 * K₄ * Y ^ (4 : ℝ)) * smoothAFEZetaMajorant 2)
    refine Integrable.mono'
      ((integrable_shifted_pow_mul_exp_neg_sq 1 N_ζ).const_mul C_dom)
      hcont_m.aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have hζ_v : ‖riemannZeta (linePt (s.im + v))‖ ≤
        C_line * (1 + |s.im|) ^ N_ζ * (1 + |v|) ^ N_ζ := by
      have hb := hC_line (s.im + v)
      have hv_add : (1 + |s.im + v|) ^ N_ζ ≤ (1 + |s.im|) ^ N_ζ * (1 + |v|) ^ N_ζ := by
        rw [← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ N_ζ
        have habs := abs_add_le s.im v
        nlinarith [abs_nonneg s.im, abs_nonneg v]
      exact hb.trans ((mul_le_mul_of_nonneg_left hv_add hC_line_pos.le).trans_eq (by ring))
    rw [norm_mul]
    calc Real.exp (-(v ^ (2 : ℕ))) *
            (‖riemannZeta (linePt (s.im + v))‖ * ‖criticalSmoothVaughanTypeII U V Y (s.im + v)‖)
        ≤ Real.exp (-(v ^ (2 : ℕ))) *
            ((C_line * (1 + |s.im|) ^ N_ζ * (1 + |v|) ^ N_ζ) *
              ((4 * K₄ * Y ^ (4 : ℝ)) * smoothAFEZetaMajorant 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hζ_v (hV_bd (s.im + v)) (norm_nonneg _) (by positivity))
            (Real.exp_nonneg _)
      _ = C_dom * ((1 + |v|) ^ N_ζ * Real.exp (-(v ^ (2 : ℕ)))) := by dsimp only [C_dom]; ring
  rw [smoothOuterVaughanTypeII_eq_criticalLine_pairing U V hx hY hs0 hhi,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  set C_pref : ℝ := 2 * x ^ a * (Real.exp (1 / 4) / a)
  have hpt_pair : ∀ v : ℝ,
      ‖(x : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
          smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
          riemannZeta (linePt (s.im + v)) *
          (1 - (2 : ℂ) ^ (-conj (linePt (s.im + v)))) *
          criticalSmoothVaughanTypeII U V Y (s.im + v)‖ ≤
        C_pref * (Real.exp (-(v ^ (2 : ℕ))) *
          ‖riemannZeta (linePt (s.im + v)) * criticalSmoothVaughanTypeII U V Y (s.im + v)‖) := by
    intro v
    set z₂ : ℂ := ((a : ℝ) : ℂ) + (v : ℂ) * I
    have hx_eq : ‖(x : ℂ) ^ z₂‖ = x ^ a := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, show z₂.re = a by simp [z₂]]
    have hker : ‖smoothAFEGaussianKernel z₂‖ ≤ (Real.exp (1 / 4) / a) * Real.exp (-(v ^ (2 : ℕ))) := by
      have hk := norm_smoothAFEGaussianKernel_vertical_le ha0 v
      have hexp_a : Real.exp (a ^ (2 : ℕ)) ≤ Real.exp (1 / 4) := by
        refine Real.exp_le_exp.mpr ?_
        have hsq : a ^ (2 : ℕ) ≤ (1 / 2 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ ha0.le ha_lt_half.le 2
        linarith
      exact hk.trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hexp_a ha0.le) (Real.exp_nonneg _))
    have h12_le : ‖1 - (2 : ℂ) ^ (-conj (linePt (s.im + v)))‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos two_pos,
        show (-conj (linePt (s.im + v))).re = -(1 / 2 : ℝ) by
          rw [conj_linePt]; simp [linePt_re]; norm_num]
      linarith [Real.rpow_le_one_of_one_le_of_nonpos one_lt_two.le (by norm_num : -(1 / 2 : ℝ) ≤ 0)]
    have hrearrange :
        (x : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
            smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
            riemannZeta (linePt (s.im + v)) *
            (1 - (2 : ℂ) ^ (-conj (linePt (s.im + v)))) *
            criticalSmoothVaughanTypeII U V Y (s.im + v) =
          ((x : ℂ) ^ z₂ * smoothAFEGaussianKernel z₂ *
            (1 - (2 : ℂ) ^ (-conj (linePt (s.im + v))))) *
            (riemannZeta (linePt (s.im + v)) * criticalSmoothVaughanTypeII U V Y (s.im + v)) := by
      dsimp only [z₂, a]; ring
    rw [hrearrange, norm_mul, norm_mul ((x : ℂ) ^ z₂ * smoothAFEGaussianKernel z₂),
      norm_mul ((x : ℂ) ^ z₂), hx_eq]
    calc (x ^ a * ‖smoothAFEGaussianKernel z₂‖ *
            ‖1 - (2 : ℂ) ^ (-conj (linePt (s.im + v)))‖) *
          ‖riemannZeta (linePt (s.im + v)) * criticalSmoothVaughanTypeII U V Y (s.im + v)‖
        ≤ (x ^ a * ((Real.exp (1 / 4) / a) * Real.exp (-(v ^ (2 : ℕ)))) * 2) *
            ‖riemannZeta (linePt (s.im + v)) * criticalSmoothVaughanTypeII U V Y (s.im + v)‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul_of_nonneg_left hker (by positivity))
              h12_le (norm_nonneg _) (by positivity))
            (norm_nonneg _)
      _ = C_pref * (Real.exp (-(v ^ (2 : ℕ))) *
            ‖riemannZeta (linePt (s.im + v)) * criticalSmoothVaughanTypeII U V Y (s.im + v)‖) := by
          dsimp only [C_pref]; ring
  have hint_le := norm_integral_le_of_norm_le (hmom_int.const_mul C_pref)
    (Filter.Eventually.of_forall hpt_pair)
  rw [MeasureTheory.integral_const_mul] at hint_le
  calc (1 / (2 * Real.pi)) *
          ‖∫ v : ℝ,
            (x : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
              smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
              riemannZeta (linePt (s.im + v)) *
              (1 - (2 : ℂ) ^ (-conj (linePt (s.im + v)))) *
              criticalSmoothVaughanTypeII U V Y (s.im + v)‖
      ≤ (1 / (2 * Real.pi)) *
          (C_pref * ∫ v : ℝ, Real.exp (-(v ^ (2 : ℕ))) *
            ‖riemannZeta (linePt (s.im + v)) * criticalSmoothVaughanTypeII U V Y (s.im + v)‖) :=
        mul_le_mul_of_nonneg_left hint_le (by positivity)
    _ = (Real.exp (1 / 4) / (Real.pi * (1 / 2 - s.re))) * x ^ (1 / 2 - s.re) *
          ∫ v : ℝ, Real.exp (-(v ^ (2 : ℕ))) *
            ‖riemannZeta (linePt (s.im + v)) * criticalSmoothVaughanTypeII U V Y (s.im + v)‖ := by
        dsimp only [C_pref, a]
        field_simp [Real.pi_ne_zero, ha0.ne']

/-- **Amplified critical-line excursion forcing and pointwise `HasStrictPrimeGasWitness` production
across ALL of `Ω_open`:**
given pure Type-II cross-height duality (`exists_pure_vaughanTypeII_crossHeight_duality_on_remaining_strip`),
at **every** point `s ∈ Ω_open` (`3001 / 24000 ≤ Re s < 1 / 2`, `184 < |Im s|`) and for **all**
`1 ≤ U, V` with `U * V ≤ |Im s|^{η - 1 / 2}`:
1. If `ζ(s) = 0`, the critical-line Gaussian moment of
   `‖ζ(1/2 + i(Im s + v)) · criticalSmoothVaughanTypeII U V (|Im s|^{3 + η}) (Im s + v)‖` is forced
   strictly above `(π (1/2 - Re s) / exp(1/4)) · |Im s|^{(1 + η)(1/2 - Re s)}` times the Spira
   vacuum gap `(1/4)(|Im s| / 7)^{1/2 - Re s} - C_du |Im s|^{-1/4}` (of growth order
   `|Im s|^{(2 + η)(1/2 - Re s)}`).
2. Conversely, whenever that critical-line Gaussian moment does not exceed that threshold, `s`
   admits an unconditional `HasStrictPrimeGasWitness`. -/
theorem criticalLine_vaughanTypeII_amplified_forcing_and_witness_on_remaining_strip
    {η C_du : ℝ}
    (hduality : ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
      let x : ℝ := |s.im| ^ (-(1 + η))
      let Y : ℝ := |s.im| ^ (3 + η)
      ∀ {U V : ℕ}, 1 ≤ U → 1 ≤ V → ((U * V : ℕ) : ℝ) ≤ |s.im| ^ (η - 1 / 2) →
        ‖riemannZeta s * smoothOuterMoebiusSeries Y (1 - s) -
            ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s + smoothOuterVaughanTypeII U V s x Y)‖ ≤
          C_du * |s.im| ^ (-(1 / 4 : ℝ)))
    {s : ℂ} (hlo : 3001 / 24000 ≤ s.re) (hhi : s.re < 1 / 2) (him : 184 < |s.im|)
    {U V : ℕ} (hU1 : 1 ≤ U) (hV1 : 1 ≤ V) (hUV_bd : ((U * V : ℕ) : ℝ) ≤ |s.im| ^ (η - 1 / 2)) :
    let Y : ℝ := |s.im| ^ (3 + η)
    let gap : ℝ := (1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) - C_du * |s.im| ^ (-(1 / 4 : ℝ))
    let thresh : ℝ :=
      (Real.pi * (1 / 2 - s.re) / Real.exp (1 / 4)) *
        |s.im| ^ ((1 + η) * (1 / 2 - s.re)) * gap
    (riemannZeta s = 0 →
      thresh <
        ∫ v : ℝ, Real.exp (-(v ^ (2 : ℕ))) *
          ‖riemannZeta (linePt (s.im + v)) * criticalSmoothVaughanTypeII U V Y (s.im + v)‖) ∧
    (∀ {L_hor : ℝ}, 0 < L_hor →
      (∫ v : ℝ, Real.exp (-(v ^ (2 : ℕ))) *
        ‖riemannZeta (linePt (s.im + v)) * criticalSmoothVaughanTypeII U V Y (s.im + v)‖) ≤ thresh →
      HasStrictPrimeGasWitness s (by linarith) L_hor) := by
  dsimp only
  have hs0 : 0 < s.re := by linarith
  have hτ_pos : 0 < |s.im| := by linarith
  have ha0 : 0 < 1 / 2 - s.re := by linarith
  set x : ℝ := |s.im| ^ (-(1 + η))
  set Y : ℝ := |s.im| ^ (3 + η)
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hτ_pos _
  have hY_pos : 0 < Y := Real.rpow_pos_of_pos hτ_pos _
  obtain ⟨hforced_II, hwit_II⟩ :=
    strict_primeGas_witness_of_pure_vaughanTypeII_domination_on_remaining_strip
      hduality hlo hhi him hU1 hV1 hUV_bd
  have hmom := norm_smoothOuterVaughanTypeII_le_criticalLine_gaussian_moment U V hx_pos hY_pos hs0 hhi
  set M_int : ℝ := ∫ v : ℝ, Real.exp (-(v ^ (2 : ℕ))) *
    ‖riemannZeta (linePt (s.im + v)) * criticalSmoothVaughanTypeII U V Y (s.im + v)‖
  set K_pos : ℝ := (Real.pi * (1 / 2 - s.re) / Real.exp (1 / 4)) *
    |s.im| ^ ((1 + η) * (1 / 2 - s.re))
  have hK_pos : 0 < K_pos := by dsimp only [K_pos]; positivity
  have hKx_cancel :
      K_pos * ((Real.exp (1 / 4) / (Real.pi * (1 / 2 - s.re))) * x ^ (1 / 2 - s.re)) = 1 := by
    have hx_pow : x ^ (1 / 2 - s.re) = |s.im| ^ (-((1 + η) * (1 / 2 - s.re))) := by
      dsimp only [x]
      rw [← Real.rpow_mul hτ_pos.le]
      congr 1; ring
    have hrpow_inv :
        |s.im| ^ ((1 + η) * (1 / 2 - s.re)) * |s.im| ^ (-((1 + η) * (1 / 2 - s.re))) = 1 := by
      rw [← Real.rpow_add hτ_pos, add_neg_cancel, Real.rpow_zero]
    dsimp only [K_pos]
    rw [hx_pow]
    have hpi_a_ne : Real.pi * (1 / 2 - s.re) ≠ 0 := mul_ne_zero Real.pi_ne_zero ha0.ne'
    have hexp_ne : Real.exp (1 / 4) ≠ 0 := (Real.exp_pos _).ne'
    have hprod1 :
        (Real.pi * (1 / 2 - s.re) / Real.exp (1 / 4)) *
          (Real.exp (1 / 4) / (Real.pi * (1 / 2 - s.re))) = 1 := by
      rw [div_mul_div_comm, mul_comm (Real.exp (1 / 4)) (Real.pi * (1 / 2 - s.re))]
      exact div_self (mul_ne_zero hpi_a_ne hexp_ne)
    calc (Real.pi * (1 / 2 - s.re) / Real.exp (1 / 4)) * |s.im| ^ ((1 + η) * (1 / 2 - s.re)) *
            (Real.exp (1 / 4) / (Real.pi * (1 / 2 - s.re)) * |s.im| ^ (-((1 + η) * (1 / 2 - s.re))))
        = ((Real.pi * (1 / 2 - s.re) / Real.exp (1 / 4)) *
            (Real.exp (1 / 4) / (Real.pi * (1 / 2 - s.re)))) *
            (|s.im| ^ ((1 + η) * (1 / 2 - s.re)) * |s.im| ^ (-((1 + η) * (1 / 2 - s.re)))) := by ring
      _ = 1 * 1 := by rw [hprod1, hrpow_inv]
      _ = 1 := mul_one 1
  have hK_II_le_M : K_pos * ‖smoothOuterVaughanTypeII U V s x Y‖ ≤ M_int := by
    calc K_pos * ‖smoothOuterVaughanTypeII U V s x Y‖
        ≤ K_pos * ((Real.exp (1 / 4) / (Real.pi * (1 / 2 - s.re))) * x ^ (1 / 2 - s.re) * M_int) :=
          mul_le_mul_of_nonneg_left hmom hK_pos.le
      _ = (K_pos * ((Real.exp (1 / 4) / (Real.pi * (1 / 2 - s.re))) * x ^ (1 / 2 - s.re))) * M_int := by
          ring
      _ = M_int := by rw [hKx_cancel, one_mul]
  refine ⟨fun hζ0 => ?_, fun {L_hor} hL_hor hM_le => ?_⟩
  · exact (mul_lt_mul_of_pos_left (hforced_II hζ0) hK_pos).trans_le hK_II_le_M
  · refine hwit_II hL_hor ?_
    by_contra hgt
    push Not at hgt
    have hlt : K_pos * ((1 / 4 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) - C_du * |s.im| ^ (-(1 / 4 : ℝ))) <
        M_int := (mul_lt_mul_of_pos_left hgt hK_pos).trans_le hK_II_le_M
    linarith

/-- **Asymptotic exponent dominance of the amplified critical-line threshold over any `Y^{1/2 - θ}`
power-saving critical-line bound (`σ < θ`):**
for every target abscissa `θ ≤ 1 / 2` and every `σ < θ`, choosing
`η = max 1 ((3 * (1 / 2 - θ) - 2 * (1 / 2 - σ) + 1) / (θ - σ))` satisfies `η ≥ 1` and
`(3 + η) * (1 / 2 - θ) + 1 ≤ (2 + η) * (1 / 2 - σ)`, so `Y^{1/2 - θ} · |Im s|` (`Y = |Im s|^{3 + η}`)
is strictly dominated by the amplified critical-line threshold exponent `|Im s|^{(2 + η)(1/2 - σ)}`. -/
theorem criticalLine_power_saving_exponent_beats_amplified_threshold
    {σ θ : ℝ} (hσθ : σ < θ) :
    ∃ η : ℝ, 1 ≤ η ∧
      (3 + η) * (1 / 2 - θ) + 1 ≤ (2 + η) * (1 / 2 - σ) := by
  have hdiff : 0 < θ - σ := sub_pos.mpr hσθ
  set η : ℝ := max 1 ((3 * (1 / 2 - θ) - 2 * (1 / 2 - σ) + 1) / (θ - σ))
  refine ⟨η, le_max_left 1 _, ?_⟩
  have hge : (3 * (1 / 2 - θ) - 2 * (1 / 2 - σ) + 1) / (θ - σ) ≤ η := le_max_right 1 _
  have hmul := (div_le_iff₀ hdiff).mp hge
  nlinarith

end Part4CriticalLineAmplifiedForcing

#print axioms smoothOuterDirectPairSum_eq_mellin_shift_pos
#print axioms smoothOuterDirectPairSum_eq_criticalLine_integral
#print axioms continuous_criticalSmoothVaughanTypeII
#print axioms smoothOuterVaughanTypeII_eq_criticalLine_pairing
#print axioms exists_smoothOuterVaughanTypeII_shell_localization_on_remaining_strip
#print axioms norm_smoothOuterVaughanTypeII_le_criticalLine_gaussian_moment
#print axioms criticalLine_vaughanTypeII_amplified_forcing_and_witness_on_remaining_strip
#print axioms criticalLine_power_saving_exponent_beats_amplified_threshold

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

end

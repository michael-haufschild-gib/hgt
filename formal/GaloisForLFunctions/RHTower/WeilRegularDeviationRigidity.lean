import GaloisForLFunctions.RHTower.WeilDeviationLineRepresentation
import GaloisForLFunctions.RHTower.WeilPositivityRegularPerturbationRigidity
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection
import GaloisForLFunctions.RHTower.WeilDeviationSpectralPairing

/-!
# Regular-deviation rigidity of Weil positivity: the analytic-continuation form

Let `w : ℕ → ℝ` with `w(0) = w(1) = 0` and `Σ|w(n)|n^{−7/4} < ∞`. Suppose the Dirichlet series of
`w` continues to a function `E` holomorphic on (a neighbourhood of) the strip `½ ≤ Re s ≤ 7/4`,
with linear growth `‖E(s)‖ ≤ C(1 + |Im s|)` and `E(½ − it) = conj E(½ + it)`.

**Theorem** (`eq_zero_of_weilPositive_add`). If `Λ + w` is Weil-positive on pole-free tests, then
`w = 0`. Hence (`riemannHypothesis_of_weilPositiveFull_add`) a full-cone Weil-positive `Λ + w`
with such a `w` is `Λ`, and RH holds.

**Proof.** The critical-line representation (`tsum_deviation_mul_pair_eq`) applied to the test
`weilTest f f` gives the symbol identity
`2π Σ_n w(n)n^{−1/2}(k(log n) + k(−log n)) = ∫ |f̂(τ)|² · 2 Re E(½ − iτ) dτ`,
with a continuous symbol of linear growth. The regular-perturbation rigidity theorem
`vonMangoldt_add_eq_zero_of_symbol` then forces `w = 0`.

The partial-sum instance of that theorem (`vonMangoldt_add_oscillating_eq_zero`, partial sums
`O(n^θ)` with `θ < ½`) already covers periodic mean-zero deviations such as `1⋆p`. The present
form asks only for continuation and growth on the strip, not for partial-sum bounds.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ComplexConjugate
open Zeta23 GaloisForLFunctions.RHTower

namespace RHTower.WeilRegular

noncomputable section

/-- `w` is a **regular deviation** with continuation `E`: `w(0) = w(1) = 0`,
`Σ|w(n)|n^{−7/4} < ∞`, and `E` continues the Dirichlet series of `w` from `Re s = 7/4`
holomorphically across the strip `½ ≤ Re s ≤ 7/4`, with linear growth and real symmetry on the
critical line. -/
structure RegularDeviation (w : ℕ → ℝ) (E : ℂ → ℂ) : Prop where
  zero : w 0 = 0
  one : w 1 = 0
  summable : Summable fun n : ℕ => |w n| * (n : ℝ) ^ (-(7 / 4 : ℝ))
  series : ∀ s : ℂ, s.re = 7 / 4 → E s = ∑' n : ℕ, (w n : ℂ) * (n : ℂ) ^ (-s)
  differentiableAt : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 7 / 4 → DifferentiableAt ℂ E s
  growth : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 7 / 4 → ‖E s‖ ≤ C * (1 + |s.im|)
  conj_line : ∀ ξ : ℝ, E (1 / 2 - 2 * π * I * ξ) = conj (E (1 / 2 + 2 * π * I * ξ))

/-! ## The transform of `weilTest f f` in the frequency variable -/

section PairTransform

variable {f : ℝ → ℂ}

/-- `paperFT (weilTest f f)(−2πz)`, the transform of `f ⋆ f̃` in the frequency variable. -/
def pairTransform (f : ℝ → ℂ) (z : ℂ) : ℂ := paperFT (EF.weilTest f f) (-(2 * π * z))

theorem differentiable_pairTransform (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Differentiable ℂ (pairTransform f) :=
  (Zeta23.WeilEF.differentiable_paperFT (EF.weilTest_contDiff hf hf.continuous hfc).continuous
    (EF.weilTest_hasCompactSupport hfc hfc)).comp (by fun_prop)

theorem exists_norm_pairTransform_le (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {a : ℝ}
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ shiftHeight →
      ‖pairTransform f z‖ ≤ C * ((1 + |z.re|) ^ 3)⁻¹ := by
  set N : ℝ := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖) with hN
  have hN0 : 0 ≤ N := by
    have h1 : 0 ≤ ∫ u, ‖f u‖ := integral_nonneg fun u => norm_nonneg _
    have h2 : 0 ≤ ∫ u, ‖deriv (deriv f) u‖ := integral_nonneg fun u => norm_nonneg _
    rw [hN]; positivity
  set B : ℝ := Real.exp (5 / 4 * |a|) * N with hB
  refine ⟨B ^ 2, by positivity, fun z hz => ?_⟩
  unfold pairTransform
  rw [EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, norm_mul, Complex.norm_conj]
  have h2c := two_pi_mul_shiftHeight
  have him : |(-(2 * π * z)).im| ≤ 5 / 4 := by
    rw [show (-(2 * π * z)).im = -(2 * π * z.im) by simp, abs_neg, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    nlinarith [Real.pi_pos]
  have him' : |(conj (-(2 * π * z))).im| ≤ 5 / 4 := by
    rw [Complex.conj_im, abs_neg]; exact him
  have hre : |(-(2 * π * z)).re| = 2 * π * |z.re| := by
    rw [show (-(2 * π * z)).re = -(2 * π * z.re) by simp, abs_neg, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have hre' : |(conj (-(2 * π * z))).re| = 2 * π * |z.re| := by rw [Complex.conj_re, hre]
  have hbound : ∀ x : ℂ, |x.im| ≤ 5 / 4 → |x.re| = 2 * π * |z.re| →
      ‖paperFT f x‖ ≤ B * ((1 + 2 * π * |z.re|) ^ 2)⁻¹ := by
    intro x hxi hxr
    have h := RHTower.norm_paperFT_le_decay hf hsupp x
    rw [hxr] at h
    have ha0 : a ≤ |a| := le_abs_self a
    have he : Real.exp (|x.im| * a) ≤ Real.exp (5 / 4 * |a|) := by
      apply Real.exp_le_exp.mpr
      have := abs_nonneg x.im
      have h1 : |x.im| * a ≤ |x.im| * |a| := mul_le_mul_of_nonneg_left ha0 this
      have h2 : |x.im| * |a| ≤ 5 / 4 * |a| := mul_le_mul_of_nonneg_right hxi (abs_nonneg a)
      linarith
    calc ‖paperFT f x‖ ≤ Real.exp (|x.im| * a) * N / (1 + 2 * π * |z.re|) ^ 2 := h
      _ ≤ Real.exp (5 / 4 * |a|) * N / (1 + 2 * π * |z.re|) ^ 2 := by gcongr
      _ = B * ((1 + 2 * π * |z.re|) ^ 2)⁻¹ := by rw [hB]; ring
  have hmono : ((1 + 2 * π * |z.re|) ^ 2)⁻¹ * ((1 + 2 * π * |z.re|) ^ 2)⁻¹ ≤
      ((1 + |z.re|) ^ 3)⁻¹ := by
    rw [← mul_inv, ← pow_add]
    apply inv_anti₀ (by positivity)
    have h1 : 1 + |z.re| ≤ 1 + 2 * π * |z.re| := by
      have := Real.pi_gt_three; nlinarith [abs_nonneg z.re]
    calc (1 + |z.re|) ^ 3 ≤ (1 + |z.re|) ^ 4 :=
          pow_le_pow_right₀ (by linarith [abs_nonneg z.re]) (by norm_num)
      _ ≤ (1 + 2 * π * |z.re|) ^ (2 + 2) := pow_le_pow_left₀ (by positivity) h1 _
  calc ‖paperFT f (-(2 * π * z))‖ * ‖paperFT f (conj (-(2 * π * z)))‖
      ≤ (B * ((1 + 2 * π * |z.re|) ^ 2)⁻¹) * (B * ((1 + 2 * π * |z.re|) ^ 2)⁻¹) :=
        mul_le_mul (hbound _ him hre) (hbound _ him' hre') (norm_nonneg _) (by positivity)
    _ = B ^ 2 * (((1 + 2 * π * |z.re|) ^ 2)⁻¹ * ((1 + 2 * π * |z.re|) ^ 2)⁻¹) := by ring
    _ ≤ B ^ 2 * ((1 + |z.re|) ^ 3)⁻¹ := by gcongr

theorem pairTransform_ofReal (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (ξ : ℝ) :
    pairTransform f ξ = ((‖paperFT f (-(2 * π * (ξ : ℂ)))‖ ^ 2 : ℝ) : ℂ) := by
  unfold pairTransform
  rw [EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc]
  have hc : conj (-(2 * π * (ξ : ℂ))) = -(2 * π * (ξ : ℂ)) := by
    rw [show (2 * π * (ξ : ℂ)) = ((2 * π * ξ : ℝ) : ℂ) by push_cast; ring, map_neg,
      Complex.conj_ofReal]
  rw [hc, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **Fourier inversion for `weilTest f f`.** -/
theorem weilTest_eq_integral (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {a : ℝ}
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) (u : ℝ) :
    EF.weilTest f f u = ∫ ξ : ℝ, pairTransform f ξ * cexp (2 * π * I * ξ * u) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_pairTransform_le hf hfc hsupp
  have hkc : Continuous (EF.weilTest f f) :=
    (EF.weilTest_contDiff hf hf.continuous hfc).continuous
  have hk : Integrable (EF.weilTest f f) :=
    hkc.integrable_of_hasCompactSupport (EF.weilTest_hasCompactSupport hfc hfc)
  have hF : 𝓕 (EF.weilTest f f) = fun ξ : ℝ => pairTransform f ξ := by
    funext ξ
    rw [RHTower.WeilExcess.fourier_eq_integral, pairTransform, paperFT]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    rw [mul_comm (cexp _)]
    congr 2
    push_cast; ring
  have hFi : Integrable (𝓕 (EF.weilTest f f)) := by
    rw [hF]
    refine (integrable_inv_one_add_sq.const_mul C).mono'
      (((differentiable_pairTransform hf hfc).continuous.comp
        Complex.continuous_ofReal).aestronglyMeasurable) (Eventually.of_forall fun ξ => ?_)
    have h := hC (ξ : ℂ) (by simp [shiftHeight_pos.le])
    simp only [Complex.ofReal_re] at h
    exact h.trans (mul_le_mul_of_nonneg_left (inv_one_add_abs_pow_three_le ξ) hC0)
  have hinv := congrFun (hkc.fourierInv_fourier_eq hk hFi) u
  rw [← hinv, RHTower.WeilExcess.fourierInv_eq_integral, hF]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [mul_comm]
  congr 1; congr 1; push_cast; ring

end PairTransform

/-! ## The symbol identity -/

variable {w : ℕ → ℝ} {E : ℂ → ℂ}

theorem continuous_regularSymbol (hR : RegularDeviation w E) :
    Continuous fun τ : ℝ => 2 * (E (1 / 2 - τ * I)).re :=
  continuous_const.mul (Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun τ =>
    (hR.differentiableAt _ (by simp) (by simp; norm_num)).continuousAt.comp
      (f := fun τ : ℝ => (1 / 2 - τ * I : ℂ)) (by fun_prop)))

theorem abs_regularSymbol_le {CE : ℝ}
    (hEb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 7 / 4 → ‖E s‖ ≤ CE * (1 + |s.im|)) (τ : ℝ) :
    |2 * (E (1 / 2 - τ * I)).re| ≤ 2 * CE * (1 + |τ|) := by
  have h := hEb (1 / 2 - τ * I) (by simp) (by simp; norm_num)
  have him : |(1 / 2 - τ * I : ℂ).im| = |τ| := by simp
  rw [him] at h
  rw [abs_mul, abs_two]
  have := (Complex.abs_re_le_norm (E (1 / 2 - τ * I))).trans h
  linarith

/-- **The symbol of a regular deviation.** For every `C²` test `f` supported in `[−a, a]`,
`2π Σ_{2 ≤ n ≤ e^{2a}} w(n)n^{−1/2} Re(k(log n) + k(−log n)) = ∫ |f̂(τ)|² · 2 Re E(½ − iτ) dτ`,
with `k = weilTest f f`. -/
theorem regular_symbol_identity (hR : RegularDeviation w E) {a : ℝ}
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (2 * (E (1 / 2 - τ * I)).re) := by
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hsupp : ∀ u, f u ≠ 0 → |u| ≤ a := fun u hu =>
    abs_le.mpr (hfs (subset_tsupport f hu))
  obtain ⟨C, hC0, hC⟩ := exists_norm_pairTransform_le hf hfc hsupp
  obtain ⟨CE, hCE0, hEb⟩ := hR.growth
  have hRep := tsum_deviation_mul_pair_eq (G := pairTransform f) (g := EF.weilTest f f)
    hR.zero hR.summable hR.series hR.differentiableAt hCE0 hEb hC0
    (fun z _ => differentiable_pairTransform hf hfc z) hC
    (weilTest_eq_integral hf hfc hsupp) 0
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  have hks : tsupport (EF.weilTest f f) ⊆ Icc (-(2 * a)) (2 * a) :=
    EF.tsupport_weilTest_subset (by rw [show 2 * a / 2 = a by ring]; exact hfs)
      (by rw [show 2 * a / 2 = a by ring]; exact hfs)
  have hkzero : ∀ n : ℕ, N < n → EF.weilTest f f (Real.log n) = 0 ∧
      EF.weilTest f f (-Real.log n) = 0 := by
    intro n hn
    have hexp : Real.exp (2 * a) < n := by
      have := Nat.lt_floor_add_one (Real.exp (2 * a))
      have h' : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
      linarith
    have hlog : 2 * a < Real.log n := by
      rw [Real.lt_log_iff_exp_lt (by linarith [Real.exp_pos (2 * a)])]; exact hexp
    constructor
    · exact image_eq_zero_of_notMem_tsupport fun h => by
        have := (hks h).2; linarith
    · exact image_eq_zero_of_notMem_tsupport fun h => by
        have := (hks h).1; linarith
  have hlhs : ∑' n : ℕ, ((w n / Real.sqrt n : ℝ) : ℂ) *
      (EF.weilTest f f ((0 : ℝ) - Real.log n) + EF.weilTest f f ((0 : ℝ) + Real.log n)) =
      ∑ n ∈ Finset.Icc 2 N, ((w n / Real.sqrt n : ℝ) : ℂ) *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)) := by
    rw [tsum_eq_sum (s := Finset.Icc 2 N)]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [zero_sub, zero_add, add_comm]
    · intro n hn
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
      rcases hn with hn | hn
      · have : n = 0 ∨ n = 1 := by omega
        rcases this with rfl | rfl <;> simp [hR.zero, hR.one]
      · obtain ⟨h1, h2⟩ := hkzero n hn
        rw [zero_sub, zero_add, h1, h2]; simp
  have hrhs : ∫ ξ : ℝ, pairTransform f ξ * cexp (2 * π * I * ξ * ((0 : ℝ) : ℂ)) *
      (E (1 / 2 + 2 * π * I * ξ) + E (1 / 2 - 2 * π * I * ξ)) =
      (((1 / (2 * π)) * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (2 * (E (1 / 2 - τ * I)).re) : ℝ) : ℂ) := by
    have hpt : ∀ ξ : ℝ, pairTransform f ξ * cexp (2 * π * I * ξ * ((0 : ℝ) : ℂ)) *
        (E (1 / 2 + 2 * π * I * ξ) + E (1 / 2 - 2 * π * I * ξ)) =
        (((fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * (2 * (E (1 / 2 - τ * I)).re)) ((-(2 * π)) * ξ) :
          ℝ) : ℂ) := by
      intro ξ
      rw [pairTransform_ofReal hf hfc, hR.conj_line, Complex.add_conj]
      have harg : (1 / 2 - (((-(2 * π)) * ξ : ℝ) : ℂ) * I) = 1 / 2 + 2 * π * I * ξ := by
        push_cast; ring
      have harg' : -(2 * π * (ξ : ℂ)) = (((-(2 * π)) * ξ : ℝ) : ℂ) := by push_cast; ring
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
      rw [harg, harg']
      push_cast; ring
    simp_rw [hpt]
    have hcv := Measure.integral_comp_mul_left
      (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * (2 * (E (1 / 2 - τ * I)).re)) (-(2 * π))
    rw [integral_complex_ofReal, hcv, smul_eq_mul]
    congr 2
    rw [abs_inv, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), one_div]
  rw [hlhs, hrhs] at hRep
  have hre := congrArg Complex.re hRep
  rw [Complex.ofReal_re, Complex.re_sum] at hre
  have hterm : ∀ n ∈ Finset.Icc 2 N, (((w n / Real.sqrt n : ℝ) : ℂ) *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n))).re =
      w n / Real.sqrt n * (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re :=
    fun n _ => Complex.re_ofReal_mul _ _
  rw [Finset.sum_congr rfl hterm] at hre
  rw [hre, ← mul_assoc, mul_one_div_cancel (by positivity : (2 * π : ℝ) ≠ 0), one_mul]

/-! ## The theorem -/

/-- **Regular-deviation rigidity.** If `Λ + w` is Weil-positive on pole-free tests and `w` is a
regular deviation, then `w = 0`. -/
theorem eq_zero_of_weilPositive_add (hR : RegularDeviation w E)
    (hW : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n) (n : ℕ) :
    w n = 0 := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · exact hR.zero
    · exact hR.one
  obtain ⟨CE, hCE0, hEb⟩ := hR.growth
  exact RHTower.vonMangoldt_add_eq_zero_of_symbol (continuous_regularSymbol hR)
    (abs_regularSymbol_le hEb) (fun _ _ _ hf hfs => regular_symbol_identity hR hf hfs)
    hW hn

/-- The sequence `Λ + w`. -/
def addVonMangoldt (w : ℕ → ℝ) (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n + w n

/-- **Full-cone form.** -/
theorem eq_zero_of_weilPositiveFull_add (hR : RegularDeviation w E)
    (hW : WeilPositiveFull (addVonMangoldt w)) (n : ℕ) : w n = 0 :=
  eq_zero_of_weilPositive_add hR (RHTower.weilPositive_of_weilPositiveFull hW) n

/-- **A regular deviation of a full-cone Weil-positive completion forces RH.** -/
theorem riemannHypothesis_of_weilPositiveFull_add (hR : RegularDeviation w E)
    (hW : WeilPositiveFull (addVonMangoldt w)) : RiemannHypothesis := by
  have h : addVonMangoldt w = fun n => (ArithmeticFunction.vonMangoldt n : ℝ) :=
    funext fun n => by simp [addVonMangoldt, eq_zero_of_weilPositiveFull_add hR hW n]
  rw [h] at hW
  exact RHTower.riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr hW

end

end RHTower.WeilRegular

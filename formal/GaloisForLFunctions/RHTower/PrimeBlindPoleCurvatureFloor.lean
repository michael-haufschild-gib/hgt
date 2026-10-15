import GaloisForLFunctions.RHTower.BlindArchimedeanNodeTwoCertificate
import GaloisForLFunctions.RHTower.PrimeBlindLevelFloor

/-!
# The pole mass of a blind combination is controlled by its mass and curvature

For a nonnegative combination `c` of tests write `K_c(x) = Σ_f c_f (Re k_f(x) + Re k_f(−x))/2` for
its even real autocorrelation (`blindKernel`).  Then the pole mass is
`P(c) = ∫ K_c(x) · 2 cosh(x/2) dx` (`nodePoleMass_eq_integral`), and blindness says `K_c(log n) = 0`
for every `n ≥ 2`.

**Gap estimate.**  Between consecutive nodes `log n < log(n+1)` the kernel vanishes at both ends,
so `|K_c(x)| ≤ M (log(n+1) − log n)²` where `M` bounds `|K_c''|` (Rolle and the mean value theorem).
Since `log(n+1) − log n ≤ 1/n ≤ 2 e^{−x}` for `x ∈ [log n, log(n+1))`, the kernel obeys
`|K_c(x)| ≤ 4 M e^{−2x}` for every `x ≥ log 2` (`abs_blindKernel_le_of_log_two_le`): beyond the first
node a blind kernel decays like `e^{−2|x|}` up to its curvature, so the growing pole kernel
`2 cosh(x/2)` is harmless there.

**Pole floor.**  Consequently `P(c) ≥ −(4·mass(c) + 6·M)` (`nodePoleMass_ge_of_blind`): the pole of a
blind combination is bounded below by its mass and the curvature bound of its autocorrelation,
uniformly in the level.  Compared with the a priori level bound `|P| ≤ 4 L e^L · mass`, the
exponential in the level is gone; what remains is a frequency term.  With the one-prime symbol
certificate this gives a level-independent floor for the blind energy,
`A(c) ≥ (γ(0) − 2)·mass(c) − 6·M` (`nodeArchEnergy_ge_of_blind`).
-/

open Complex MeasureTheory Set Finsupp Zeta23
open scoped Interval

namespace RHTower.WeilOneSided

noncomputable section

/-! ## The even real autocorrelation of a combination -/

/-- The even real autocorrelation `(Re k_f(x) + Re k_f(−x))/2` of a test. -/
def symAuto (f : WeilTestFn) (x : ℝ) : ℝ :=
  (EF.weilTest f.1 f.1 x + EF.weilTest f.1 f.1 (-x)).re / 2

/-- The even real autocorrelation of a combination of tests. -/
def blindKernel (c : WeilTestFn →₀ ℝ) (x : ℝ) : ℝ := ∑ f ∈ c.support, c f * symAuto f x

theorem symAuto_neg (f : WeilTestFn) (x : ℝ) : symAuto f (-x) = symAuto f x := by
  simp [symAuto, add_comm]

theorem blindKernel_neg (c : WeilTestFn →₀ ℝ) (x : ℝ) : blindKernel c (-x) = blindKernel c x := by
  simp [blindKernel, symAuto_neg]

theorem symAuto_log (f : WeilTestFn) {n : ℕ} (hn : 2 ≤ n) :
    symAuto f (Real.log n) = Real.sqrt n * logValue f.1 n / 2 := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))).ne'
  unfold symAuto logValue
  field_simp

theorem blindKernel_log (c : WeilTestFn →₀ ℝ) (n : LogIndex) :
    blindKernel c (Real.log n) = Real.sqrt n * nodeVector c n / 2 := by
  unfold blindKernel
  rw [nodeVector_eq, linearCombination_apply, Finsupp.sum_apply, Finsupp.sum, Finset.mul_sum,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Finsupp.smul_apply, logVector_apply, smul_eq_mul]
  rw [symAuto_log f n.2]
  ring

/-- On a blind combination the even autocorrelation vanishes at every node. -/
theorem blindKernel_log_eq_zero {c : WeilTestFn →₀ ℝ} (hv : nodeVector c = 0) {n : ℕ}
    (hn : 2 ≤ n) : blindKernel c (Real.log n) = 0 := by
  have := blindKernel_log c ⟨n, hn⟩
  rw [hv] at this
  simpa using this

/-! ## Smoothness, support and size -/

theorem contDiff_symAuto (f : WeilTestFn) : ContDiff ℝ 2 (symAuto f) := by
  have hk := EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2
  exact (Complex.reCLM.contDiff.comp (hk.add (hk.comp contDiff_neg))).div_const 2

theorem contDiff_blindKernel (c : WeilTestFn →₀ ℝ) : ContDiff ℝ 2 (blindKernel c) :=
  ContDiff.sum fun f _ => contDiff_const.mul (contDiff_symAuto f)

theorem continuous_blindKernel (c : WeilTestFn →₀ ℝ) : Continuous (blindKernel c) :=
  (contDiff_blindKernel c).continuous

theorem symAuto_eq_zero_of_levelTest {L : ℝ} {f : WeilTestFn} (hf : LevelTest L f) {x : ℝ}
    (hx : 2 * L ≤ |x|) : symAuto f x = 0 := by
  unfold symAuto
  rw [weilTest_eq_zero_of_levelTest hf hx, weilTest_eq_zero_of_levelTest hf (by rwa [abs_neg])]
  simp

theorem blindKernel_eq_zero_of_level {L : ℝ} {c : WeilTestFn →₀ ℝ}
    (hc : ∀ f ∈ c.support, LevelTest L f) {x : ℝ} (hx : 2 * L ≤ |x|) : blindKernel c x = 0 := by
  unfold blindKernel
  exact Finset.sum_eq_zero fun f hf => by rw [symAuto_eq_zero_of_levelTest (hc f hf) hx, mul_zero]

/-- The autocorrelation of a test is bounded by its mass. -/
theorem norm_weilTest_self_le_testMass (f : WeilTestFn) (y : ℝ) :
    ‖EF.weilTest f.1 f.1 y‖ ≤ testMass f := by
  have hf := f.2.1.continuous
  have hfc := f.2.2
  have hs : HasCompactSupport (fun u => ‖f.1 u‖ ^ 2) := by
    simp only [pow_two]
    exact hfc.norm.mul_right
  have hi : Integrable (fun u => ‖f.1 u‖ ^ 2) := (hf.norm.pow 2).integrable_of_hasCompactSupport hs
  have hiy : Integrable (fun u => ‖f.1 (u - y)‖ ^ 2) := hi.comp_sub_right y
  have hmajor : Integrable (fun u => (‖f.1 u‖ ^ 2 + ‖f.1 (u - y)‖ ^ 2) / 2) :=
    (hi.add hiy).div_const 2
  have hpt : ∀ u : ℝ, ‖f.1 u‖ * ‖f.1 (u - y)‖ ≤ (‖f.1 u‖ ^ 2 + ‖f.1 (u - y)‖ ^ 2) / 2 :=
    fun u => by nlinarith [sq_nonneg (‖f.1 u‖ - ‖f.1 (u - y)‖)]
  have hbound := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun u => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    hmajor (Filter.Eventually.of_forall hpt)
  have hnorm : ‖EF.weilTest f.1 f.1 y‖ ≤ ∫ u, ‖f.1 u‖ * ‖f.1 (u - y)‖ := by
    simp only [EF.weilTest, convolution_def, ContinuousLinearMap.mul_apply', EF.tilde, neg_sub]
    have h := norm_integral_le_integral_norm (μ := volume)
      (fun u => f.1 u * starRingEnd ℂ (f.1 (u - y)))
    simpa only [norm_mul, Complex.norm_conj] using h
  have hsplit : ∫ u, (‖f.1 u‖ ^ 2 + ‖f.1 (u - y)‖ ^ 2) / 2 = testMass f := by
    rw [MeasureTheory.integral_div, integral_add hi hiy,
      integral_sub_right_eq_self (fun u => ‖f.1 u‖ ^ 2) y]
    unfold testMass
    ring
  linarith

theorem abs_symAuto_le (f : WeilTestFn) (x : ℝ) : |symAuto f x| ≤ testMass f := by
  unfold symAuto
  have h1 := norm_weilTest_self_le_testMass f x
  have h2 := norm_weilTest_self_le_testMass f (-x)
  have h3 := Complex.abs_re_le_norm (EF.weilTest f.1 f.1 x + EF.weilTest f.1 f.1 (-x))
  have h4 := norm_add_le (EF.weilTest f.1 f.1 x) (EF.weilTest f.1 f.1 (-x))
  rw [abs_div, abs_two]
  linarith

theorem abs_blindKernel_le {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) (x : ℝ) :
    |blindKernel c x| ≤ linearCombination ℝ testMass c := by
  change |∑ f ∈ c.support, c f * symAuto f x| ≤ ∑ f ∈ c.support, c f * testMass f
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  rw [abs_mul, abs_of_nonneg (hc f)]
  exact mul_le_mul_of_nonneg_left (abs_symAuto_le f x) (hc f)

/-! ## The pole mass as an integral against `2 cosh(x/2)` -/

theorem hasCompactSupport_symAuto (f : WeilTestFn) : HasCompactSupport (symAuto f) := by
  have hks : HasCompactSupport (EF.weilTest f.1 f.1) := EF.weilTest_hasCompactSupport f.2.2 f.2.2
  exact (hks.add (hks.comp_homeomorph (Homeomorph.neg ℝ))).comp_left
    (g := fun z : ℂ => z.re / 2) (by simp)

theorem continuous_two_cosh_half : Continuous fun x : ℝ => 2 * Real.cosh (x / 2) :=
  continuous_const.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))

theorem re_weilPoleTerm_eq_integral_symAuto (f : WeilTestFn) :
    (weilPoleTerm (EF.weilTest f.1 f.1)).re = ∫ x, symAuto f x * (2 * Real.cosh (x / 2)) := by
  set k := EF.weilTest f.1 f.1 with hk
  have hkc : Continuous k := (EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2).continuous
  have hks : HasCompactSupport k := EF.weilTest_hasCompactSupport f.2.2 f.2.2
  have e1 : ∀ u : ℝ, Complex.exp (I * (I / 2) * u) = ((Real.exp (-(u / 2)) : ℝ) : ℂ) := by
    intro u
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have e2 : ∀ u : ℝ, Complex.exp (I * (-I / 2) * u) = ((Real.exp (u / 2) : ℝ) : ℂ) := by
    intro u
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hc1 : Continuous fun u : ℝ => k u * ((Real.exp (-(u / 2)) : ℝ) : ℂ) :=
    hkc.mul (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_id.div_const 2).neg))
  have hc2 : Continuous fun u : ℝ => k u * ((Real.exp (u / 2) : ℝ) : ℂ) :=
    hkc.mul (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.div_const 2)))
  have hi1 : Integrable fun u : ℝ => k u * ((Real.exp (-(u / 2)) : ℝ) : ℂ) :=
    hc1.integrable_of_hasCompactSupport hks.mul_right
  have hi2 : Integrable fun u : ℝ => k u * ((Real.exp (u / 2) : ℝ) : ℂ) :=
    hc2.integrable_of_hasCompactSupport hks.mul_right
  have hsum : weilPoleTerm k = ∫ u, (k u * ((Real.exp (-(u / 2)) : ℝ) : ℂ) +
      k u * ((Real.exp (u / 2) : ℝ) : ℂ)) := by
    unfold weilPoleTerm paperFT
    simp only [e1, e2]
    rw [integral_add hi1 hi2]
  have hi12 : Integrable fun u : ℝ => k u * ((Real.exp (-(u / 2)) : ℝ) : ℂ) +
      k u * ((Real.exp (u / 2) : ℝ) : ℂ) := hi1.add hi2
  have hre : (weilPoleTerm k).re = ∫ u, (k u).re * (2 * Real.cosh (u / 2)) := by
    rw [hsum, ← RCLike.re_to_complex, ← integral_re hi12]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [RCLike.re_to_complex, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Real.cosh_eq]
    ring
  -- symmetrise
  set g : ℝ → ℝ := fun u => (k u).re * (2 * Real.cosh (u / 2)) with hg
  have hgc : Continuous g := (Complex.continuous_re.comp hkc).mul continuous_two_cosh_half
  have hgs : HasCompactSupport g :=
    (hks.comp_left (g := Complex.re) Complex.zero_re).mul_right
  have hgi : Integrable g := hgc.integrable_of_hasCompactSupport hgs
  have hgneg : ∀ u, g (-u) = (k (-u)).re * (2 * Real.cosh (u / 2)) := by
    intro u
    simp only [hg, neg_div, Real.cosh_neg]
  have hgi' : Integrable fun u => g (-u) := hgi.comp_neg
  have hsym : ∫ u, symAuto f u * (2 * Real.cosh (u / 2)) = ∫ u, (g u + g (-u)) / 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have e : symAuto f u = ((k u).re + (k (-u)).re) / 2 := by
      simp [symAuto, hk]
    show symAuto f u * (2 * Real.cosh (u / 2)) = (g u + g (-u)) / 2
    rw [hgneg u, e]
    simp only [hg]
    ring
  rw [hre, hsym, MeasureTheory.integral_div, integral_add hgi hgi',
    MeasureTheory.integral_neg_eq_self]
  ring

theorem nodePoleMass_eq_integral (c : WeilTestFn →₀ ℝ) :
    nodePoleMass c = ∫ x, blindKernel c x * (2 * Real.cosh (x / 2)) := by
  unfold nodePoleMass blindKernel
  rw [linearCombination_apply, Finsupp.sum]
  simp only [smul_eq_mul, re_weilPoleTerm_eq_integral_symAuto, Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum _ fun f _ => ?_]
  · refine Finset.sum_congr rfl fun f _ => ?_
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  · exact ((continuous_const.mul (contDiff_symAuto f).continuous).mul
      continuous_two_cosh_half).integrable_of_hasCompactSupport
      ((hasCompactSupport_symAuto f).mul_left.mul_right)

/-! ## The gap estimate -/

/-- A `C²` function vanishing at the ends of `[a, b]` is bounded by `M (b − a)²` there, where `M`
bounds its second derivative. -/
theorem abs_le_of_eq_zero_endpoints {K : ℝ → ℝ} (hK : ContDiff ℝ 2 K) {M : ℝ}
    (hM : ∀ x, |deriv (deriv K) x| ≤ M) {a b : ℝ} (hab : a < b) (ha : K a = 0) (hb : K b = 0)
    {x : ℝ} (hx : x ∈ Icc a b) : |K x| ≤ M * (b - a) ^ 2 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hK1 : ContDiff ℝ 1 (deriv K) := by
    have h := hK
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv] at h
    exact h.2.2
  have hKd : Differentiable ℝ K := hK.differentiable (by norm_num)
  have hK'd : Differentiable ℝ (deriv K) := hK1.differentiable (by norm_num)
  obtain ⟨ξ, hξ, hξ0⟩ := exists_hasDerivAt_eq_zero hab hK.continuous.continuousOn
    (ha.trans hb.symm) (fun y _ => (hKd y).hasDerivAt)
  have hK'bound : ∀ y ∈ Icc a b, ‖deriv K y‖ ≤ M * (b - a) := by
    intro y hy
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv K) (s := Icc a b)
      (fun z _ => hK'd z) (fun z _ => by rw [Real.norm_eq_abs]; exact hM z)
      (convex_Icc a b) (Ioo_subset_Icc_self hξ) hy
    rw [hξ0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
    have hdist : |y - ξ| ≤ b - a := by
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2, hξ.1, hξ.2]
    rw [Real.norm_eq_abs]
    exact h.trans (mul_le_mul_of_nonneg_left hdist hM0)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := K) (s := Icc a b)
    (fun z _ => hKd z) hK'bound (convex_Icc a b)
    (left_mem_Icc.mpr hab.le) hx
  rw [ha, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hxa : |x - a| ≤ b - a := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  calc |K x| ≤ M * (b - a) * |x - a| := h
    _ ≤ M * (b - a) * (b - a) :=
        mul_le_mul_of_nonneg_left hxa (mul_nonneg hM0 (by linarith))
    _ = M * (b - a) ^ 2 := by ring

/-- **Beyond the first node a blind kernel decays like `e^{−2x}` up to its curvature.** -/
theorem abs_blindKernel_le_of_log_two_le {c : WeilTestFn →₀ ℝ} (hv : nodeVector c = 0) {M : ℝ}
    (hM : ∀ x, |deriv (deriv (blindKernel c)) x| ≤ M) {x : ℝ} (hx : Real.log 2 ≤ x) :
    |blindKernel c x| ≤ 4 * M * Real.exp (-(2 * x)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set n : ℕ := ⌊Real.exp x⌋₊ with hn
  have hex : 0 < Real.exp x := Real.exp_pos x
  have h2le : (2 : ℝ) ≤ Real.exp x := by
    rw [← Real.exp_log two_pos]
    exact Real.exp_le_exp.mpr hx
  have hn2 : 2 ≤ n := by
    rw [hn]
    exact Nat.le_floor (by exact_mod_cast h2le)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hfl : (n : ℝ) ≤ Real.exp x := Nat.floor_le hex.le
  have hlt : Real.exp x < n + 1 := Nat.lt_floor_add_one _
  have hlogn : Real.log n ≤ x := by
    rw [← Real.log_exp x]
    exact Real.log_le_log hnpos hfl
  have hlogn1 : x < Real.log (n + 1) := by
    rw [← Real.log_exp x]
    exact Real.log_lt_log hex hlt
  have hab : Real.log n < Real.log (n + 1) := hlogn.trans_lt hlogn1
  have hK0 : blindKernel c (Real.log n) = 0 := blindKernel_log_eq_zero hv hn2
  have hK1 : blindKernel c (Real.log (n + 1)) = 0 := by
    have := blindKernel_log_eq_zero hv (n := n + 1) (by omega)
    push_cast at this
    exact this
  have hgap : Real.log (n + 1) - Real.log n ≤ 2 * Real.exp (-x) := by
    rw [← Real.log_div (by positivity) hnpos.ne']
    have h1 : Real.log (((n : ℝ) + 1) / n) ≤ ((n : ℝ) + 1) / n - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    have h3 : (1 : ℝ) / n ≤ 2 / (n + 1) := by
      rw [div_le_div_iff₀ hnpos (by positivity)]
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      nlinarith
    have h4 : (2 : ℝ) / (n + 1) ≤ 2 * Real.exp (-x) := by
      rw [Real.exp_neg, ← one_div, mul_one_div]
      exact div_le_div_of_nonneg_left (by norm_num) hex hlt.le
    linarith
  have hgap0 : 0 ≤ Real.log (n + 1) - Real.log n := by linarith
  have hbound := abs_le_of_eq_zero_endpoints (contDiff_blindKernel c) hM hab hK0 hK1
    ⟨hlogn, hlogn1.le⟩
  have hexp : Real.exp (-(2 * x)) = Real.exp (-x) ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  calc |blindKernel c x| ≤ M * (Real.log (n + 1) - Real.log n) ^ 2 := hbound
    _ ≤ M * (2 * Real.exp (-x)) ^ 2 := by gcongr
    _ = 4 * M * Real.exp (-(2 * x)) := by rw [hexp]; ring

/-! ## The pole floor -/

theorem two_cosh_half_le_of_abs_le_log_two {x : ℝ} (hx : |x| ≤ Real.log 2) :
    2 * Real.cosh (x / 2) ≤ 5 / 2 := by
  have h1 : Real.cosh (x / 2) ≤ Real.cosh (Real.log 2 / 2) := by
    rw [Real.cosh_le_cosh, abs_div, abs_div, abs_two, abs_of_pos (Real.log_pos one_lt_two)]
    exact div_le_div_of_nonneg_right hx (by norm_num)
  have h2 : Real.exp (Real.log 2 / 2) ≤ 3 / 2 := by
    rw [Real.exp_half, Real.exp_log two_pos]
    rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h3 : Real.exp (-(Real.log 2 / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [Real.log_pos one_lt_two])
  rw [Real.cosh_eq, Real.cosh_eq] at h1
  rw [Real.cosh_eq]
  linarith

theorem two_cosh_half_le_exp_half {x : ℝ} (hx : 0 ≤ x) :
    2 * Real.cosh (x / 2) ≤ 2 * Real.exp (x / 2) := by
  rw [Real.cosh_eq]
  have : Real.exp (-(x / 2)) ≤ Real.exp (x / 2) := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- The pointwise tail bound `|K_c(x)| 2cosh(x/2) ≤ 6 M e^{−x}` for `x ≥ log 2`. -/
theorem abs_blindKernel_mul_le_tail {c : WeilTestFn →₀ ℝ} (hv : nodeVector c = 0) {M : ℝ}
    (hM : ∀ x, |deriv (deriv (blindKernel c)) x| ≤ M) {x : ℝ} (hx : Real.log 2 ≤ x) :
    |blindKernel c x * (2 * Real.cosh (x / 2))| ≤ 6 * M * Real.exp (-x) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hx0 : 0 ≤ x := (Real.log_pos one_lt_two).le.trans hx
  have h1 := abs_blindKernel_le_of_log_two_le hv hM hx
  have h2 := two_cosh_half_le_exp_half hx0
  have hcpos : 0 ≤ 2 * Real.cosh (x / 2) := by positivity
  have hprod : |blindKernel c x * (2 * Real.cosh (x / 2))| ≤
      4 * M * Real.exp (-(2 * x)) * (2 * Real.exp (x / 2)) := by
    rw [abs_mul, abs_of_nonneg hcpos]
    exact mul_le_mul h1 h2 hcpos (by positivity)
  have hexp : Real.exp (-(2 * x)) * (2 * Real.exp (x / 2)) =
      2 * Real.exp (-x) * Real.exp (-(x / 2)) := by
    calc Real.exp (-(2 * x)) * (2 * Real.exp (x / 2))
        = 2 * (Real.exp (-(2 * x)) * Real.exp (x / 2)) := by ring
      _ = 2 * (Real.exp (-x) * Real.exp (-(x / 2))) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      _ = 2 * Real.exp (-x) * Real.exp (-(x / 2)) := by ring
  have hhalf : Real.exp (-(x / 2)) ≤ 3 / 4 := by
    have : Real.exp (-(x / 2)) ≤ Real.exp (-(Real.log 2 / 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    refine this.trans ?_
    rw [Real.exp_neg, Real.exp_half, Real.exp_log two_pos]
    rw [inv_le_comm₀ (Real.sqrt_pos.mpr two_pos) (by norm_num), inv_div]
    rw [show (4 / 3 : ℝ) = Real.sqrt ((4 / 3) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  calc |blindKernel c x * (2 * Real.cosh (x / 2))|
      ≤ 4 * M * Real.exp (-(2 * x)) * (2 * Real.exp (x / 2)) := hprod
    _ = 4 * M * (2 * Real.exp (-x) * Real.exp (-(x / 2))) := by rw [mul_assoc, hexp]
    _ ≤ 4 * M * (2 * Real.exp (-x) * (3 / 4)) := by gcongr
    _ = 6 * M * Real.exp (-x) := by ring

/-- `∫_{log 2}^{b} e^{−x} dx ≤ 1/2`. -/
theorem integral_exp_neg_log_two_le (b : ℝ) :
    ∫ x in Real.log 2..b, Real.exp (-x) ≤ 1 / 2 := by
  have : ∫ x in Real.log 2..b, Real.exp (-x) = Real.exp (-Real.log 2) - Real.exp (-b) := by
    rw [intervalIntegral.integral_comp_neg (fun x => Real.exp x), integral_exp]
  rw [this, Real.exp_neg, Real.exp_log two_pos]
  linarith [Real.exp_pos (-b)]

/-- **Pole floor.**  The pole mass of a nonnegative blind combination is at least
`−(4·mass + 6·M)`, where `M` bounds the second derivative of its even autocorrelation. -/
theorem nodePoleMass_ge_of_blind {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (hv : nodeVector c = 0) {M : ℝ} (hM : ∀ x, |deriv (deriv (blindKernel c)) x| ≤ M) :
    -(4 * linearCombination ℝ testMass c + 6 * M) ≤ nodePoleMass c := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set mass := linearCombination ℝ testMass c with hmass
  have hmass0 : 0 ≤ mass := linearCombination_testMass_nonneg hc
  rw [nodePoleMass_eq_integral]
  set g : ℝ → ℝ := fun x => blindKernel c x * (2 * Real.cosh (x / 2)) with hg
  have hgc : Continuous g := (continuous_blindKernel c).mul continuous_two_cosh_half
  have hgneg : ∀ x, g (-x) = g x := by
    intro x
    simp only [hg, blindKernel_neg, neg_div, Real.cosh_neg]
  -- a level containing every test of the combination, at least `1`
  obtain ⟨L₀, -, hLc⟩ := exists_level_combination c
  set L := max L₀ 1 with hL
  have hL1 : 1 ≤ L := le_max_right _ _
  have hLc' : ∀ f ∈ c.support, LevelTest L f := fun f hf => (hLc f hf).mono (le_max_left _ _)
  have hlog2 : Real.log 2 < 2 * L := by linarith [Real.log_two_lt_d9]
  have hgzero : ∀ x, x ∉ Ioc (-(2 * L)) (2 * L) → g x = 0 := by
    intro x hx
    simp only [hg]
    rw [blindKernel_eq_zero_of_level hLc' ?_, zero_mul]
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hint : ∫ x, g x = ∫ x in (-(2 * L))..(2 * L), g x := by
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero hgzero]
  have hII : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hgc.intervalIntegrable a b
  have hsplit : ∫ x in (-(2 * L))..(2 * L), g x =
      (∫ x in (-(2 * L))..(-Real.log 2), g x) + (∫ x in (-Real.log 2)..(Real.log 2), g x) +
        ∫ x in (Real.log 2)..(2 * L), g x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hII _ _) (hII _ _),
      intervalIntegral.integral_add_adjacent_intervals (hII _ _) (hII _ _)]
  -- the middle piece
  have hmid : -(7 / 2 * mass) ≤ ∫ x in (-Real.log 2)..(Real.log 2), g x := by
    have hb : ∀ x ∈ Ι (-Real.log 2) (Real.log 2), ‖g x‖ ≤ 5 / 2 * mass := by
      intro x hx
      have hx' : |x| ≤ Real.log 2 := by
        rw [uIoc_of_le (by linarith [Real.log_pos one_lt_two])] at hx
        rw [abs_le]
        exact ⟨hx.1.le, hx.2⟩
      rw [Real.norm_eq_abs, hg]
      simp only
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.cosh (x / 2))]
      calc |blindKernel c x| * (2 * Real.cosh (x / 2)) ≤ mass * (5 / 2) :=
            mul_le_mul (abs_blindKernel_le hc x) (two_cosh_half_le_of_abs_le_log_two hx')
              (by positivity) hmass0
        _ = 5 / 2 * mass := by ring
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs] at h
    have hlen : |Real.log 2 - -Real.log 2| ≤ 7 / 5 := by
      rw [sub_neg_eq_add, abs_of_pos (by linarith [Real.log_pos one_lt_two])]
      linarith [Real.log_two_lt_d9]
    have h2 : |∫ x in (-Real.log 2)..(Real.log 2), g x| ≤ 5 / 2 * mass * (7 / 5) :=
      h.trans (mul_le_mul_of_nonneg_left hlen (by positivity))
    have := neg_abs_le (∫ x in (-Real.log 2)..(Real.log 2), g x)
    linarith
  -- the right tail
  have htail : -(3 * M) ≤ ∫ x in (Real.log 2)..(2 * L), g x := by
    have hmono := intervalIntegral.integral_mono_on (f := fun x => -(6 * M * Real.exp (-x)))
      (g := g) hlog2.le
      ((continuous_const.mul (Real.continuous_exp.comp continuous_neg)).neg.intervalIntegrable _ _)
      (hII _ _) (fun x hx => by
        have := abs_blindKernel_mul_le_tail hv hM hx.1
        have := neg_abs_le (g x)
        simp only [hg] at *
        linarith)
    have hval : ∫ x in (Real.log 2)..(2 * L), -(6 * M * Real.exp (-x)) =
        -(6 * M * ∫ x in (Real.log 2)..(2 * L), Real.exp (-x)) := by
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
    have hexp := integral_exp_neg_log_two_le (2 * L)
    have h6 : 6 * M * ∫ x in (Real.log 2)..(2 * L), Real.exp (-x) ≤ 6 * M * (1 / 2) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    linarith
  -- the left tail equals the right tail
  have hleft : ∫ x in (-(2 * L))..(-Real.log 2), g x = ∫ x in (Real.log 2)..(2 * L), g x := by
    rw [← intervalIntegral.integral_comp_neg g]
    exact intervalIntegral.integral_congr fun x _ => (hgneg x)
  rw [hint, hsplit, hleft]
  linarith

/-- The mass of a combination in the two normalisations agrees. -/
theorem massOf_eq_linearCombination (c : WeilTestFn →₀ ℝ) :
    massOf c = linearCombination ℝ testMass c := by
  show (c.sum fun f t => t * ∫ x, ‖f.1 x‖ ^ 2) = c.sum fun f t => t • testMass f
  simp only [smul_eq_mul, testMass]

/-- **Level-independent floor of the blind energy.**  On nonnegative blind combinations,
`A(c) ≥ (γ(0) − 2)·mass(c) − 6·M`, with `M` a bound on the curvature of the even autocorrelation. -/
theorem nodeArchEnergy_ge_of_blind {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (hv : nodeVector c = 0) {M : ℝ} (hM : ∀ x, |deriv (deriv (blindKernel c)) x| ≤ M) :
    (EF.gammaBracket 0 - 2) * linearCombination ℝ testMass c - 6 * M ≤ nodeArchEnergy c := by
  have h1 := blindSymbolSlack_node_two c hc hv
  have h2 := nodePoleMass_ge_of_blind hc hv hM
  rw [massOf_eq_linearCombination, nodeArchOnly] at h1
  linarith

end

end RHTower.WeilOneSided

namespace RHTower.WeilOneSided

/-- On blind combinations whose autocorrelation curvature is at most `κ` times their mass, the blind
energy is at least `(γ(0) − 2 − 6κ)` times the mass, uniformly in the level. -/
theorem nodeArchEnergy_ge_of_blind_of_curvature_le {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (hv : nodeVector c = 0) {κ : ℝ}
    (hκ : ∀ x, |deriv (deriv (blindKernel c)) x| ≤ κ * linearCombination ℝ testMass c) :
    (EF.gammaBracket 0 - 2 - 6 * κ) * linearCombination ℝ testMass c ≤ nodeArchEnergy c := by
  have := nodeArchEnergy_ge_of_blind hc hv hκ
  linarith

/-- The energy-to-mass ratio of a blind combination with curvature at most `κ` times its mass is at
least `γ(0) − 2 − 6κ`: a blind family with energy ratio tending to `−∞` must have curvature-to-mass
ratio tending to `∞`. -/
theorem div_nodeArchEnergy_ge_of_blind_of_curvature_le {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (hv : nodeVector c = 0) {κ : ℝ} (hmass : 0 < linearCombination ℝ testMass c)
    (hκ : ∀ x, |deriv (deriv (blindKernel c)) x| ≤ κ * linearCombination ℝ testMass c) :
    EF.gammaBracket 0 - 2 - 6 * κ ≤ nodeArchEnergy c / linearCombination ℝ testMass c := by
  rw [le_div_iff₀ hmass]
  exact nodeArchEnergy_ge_of_blind_of_curvature_le hc hv hκ

end RHTower.WeilOneSided

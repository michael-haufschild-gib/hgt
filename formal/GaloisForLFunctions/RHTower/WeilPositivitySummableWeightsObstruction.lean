import GaloisForLFunctions.RHTower.WeilPositivityTwistObstruction
import GaloisForLFunctions.RHTower.DigammaIntegralRepresentation
import GaloisForLFunctions.RHTower.DigammaQuarter

/-!
# Summable prime weights are never Weil-positive

With the archimedean term of `ζ`, the finite-atom Weil symbol with weights `λ` is
`S_N(ξ) = A(ξ) - Σ_{2 ≤ n ≤ N} 2 λ(n) n^{-1/2} cos(2π ξ log n)`, with `A(τ/2π) = Re ψ(1/4 + iτ/2) - log π`.

* **x-space form of the archimedean energy** (`integral_normSq_mul_arch_eq_jump`).  By Gauss's
  integral for `ψ`, `A(τ/2π) = Re ψ(1/4) - log π + ∫_0^∞ w(t)(1 - cos(τt/2)) dt` with the positive
  jump density `w(t) = e^{-t/4}/(1 - e^{-t})`, so for a `C²` test
  `∫ |h|² A = (Re ψ(1/4) - log π) ∫ |h|² + ∫_0^∞ w(t) ∫ |h(τ)|² (1 - cos(τt/2)) dτ dt`.
* **A prime-blind test with negative archimedean energy**
  (`integral_normSq_paperFT_fejerTest_mul_arch_neg`).  The flat-top bump
  `g = σ((b + x)/d) σ((b - x)/d)` with `b = 17/50`, `d = 17/1000` has autocorrelation `R` with
  `R(0) ≥ 2(b - d)` and `R(0) - R(y) ≤ y`.  The latter follows because `(g(t) - g(t - y))⁺` is
  dominated by the increments of the monotone envelope of `g`.  Its support is inside
  `(-log 2 / 2, log 2 / 2)`, and `∫ |h|² A < 0` with explicit margin.
* **Theorem** (`summable_weights_weilAtomSymbol_not_nonneg`).  If `Σ |λ(n)| n^{-1/2} < ∞`, some
  polar-constrained `C²` test at some level has negative symbol energy.
  - On the prime-blind test every atom integrates to zero, so the full symbol `S` satisfies
    `∫ |h|² S = ∫ |h|² A < 0` and is negative somewhere.
  - Concentrated radical tests at that point then give negative energy.
  - The atom tail beyond the level is made negligible by choosing the level after the test.
  - This covers `λ = 0` and every finite truncation `Λ · 1_{n ≤ N}`: Weil positivity needs prime
    weights whose Dirichlet series diverges on the critical line.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-- The archimedean jump density `w(t) = e^{-t/4} / (1 - e^{-t})`. -/
def archJump (t : ℝ) : ℝ := Real.exp (-(t / 4)) / (1 - Real.exp (-t))

theorem archJump_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ archJump t := by
  unfold archJump
  have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  exact div_nonneg (Real.exp_pos _).le (by linarith)

/-- **Gauss's representation on the quarter line.**
`Re ψ(1/4 + iy) = ψ(1/4) + ∫_0^∞ w(t) (1 - cos(yt)) dt`. -/
theorem re_digamma_quarter_line (y : ℝ) :
    (Complex.digamma (1 / 4 + (y : ℂ) * I)).re = (Complex.digamma (1 / 4)).re +
      ∫ t in Ioi (0 : ℝ), archJump t * (1 - Real.cos (y * t)) := by
  have hs : 0 < (1 / 4 + (y : ℂ) * I).re := by simp
  have hq : 0 < (1 / 4 : ℂ).re := by norm_num
  have h1 := digamma_eq_integral_gauss hs
  have h2 := digamma_eq_integral_gauss hq
  have i1 := integrableOn_digammaGaussIntegrand hs
  have i2 := integrableOn_digammaGaussIntegrand hq
  have hsub : Complex.digamma (1 / 4 + (y : ℂ) * I) - Complex.digamma (1 / 4) =
      ∫ t in Ioi (0 : ℝ), (digammaGaussIntegrand (1 / 4 + (y : ℂ) * I) t -
        digammaGaussIntegrand (1 / 4) t) := by
    rw [h1, h2, integral_sub i1 i2]
  have hre := congrArg Complex.re hsub
  have hint := integral_re (i1.sub i2)
  simp only [RCLike.re_to_complex, Pi.sub_apply] at hint
  rw [Complex.sub_re, ← hint] at hre
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (digammaGaussIntegrand (1 / 4 + (y : ℂ) * I) t -
      digammaGaussIntegrand (1 / 4) t).re = archJump t * (1 - Real.cos (y * t)) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hden : 0 < 1 - Real.exp (-t) := by
      have := Real.exp_lt_one_iff.mpr (show -t < 0 by linarith); linarith
    unfold digammaGaussIntegrand archJump
    have hd : (1 : ℂ) - Complex.exp (-(t : ℂ)) = ((1 - Real.exp (-t) : ℝ) : ℂ) := by
      push_cast; rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
    rw [hd]
    have e1 : Complex.exp (-(1 / 4 + (y : ℂ) * I) * (t : ℂ)) =
        ((Real.exp (-(t / 4)) : ℝ) : ℂ) * Complex.exp (-((y * t : ℝ) : ℂ) * I) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : Complex.exp (-(1 / 4 : ℂ) * (t : ℂ)) = ((Real.exp (-(t / 4)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    rw [e1, e2]
    have hc : (Complex.exp (-((y * t : ℝ) : ℂ) * I)).re = Real.cos (y * t) := by
      rw [show -((y * t : ℝ) : ℂ) * I = ((-(y * t) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    simp only [Complex.sub_re, Complex.div_ofReal_re, Complex.ofReal_re, Complex.re_ofReal_mul, hc]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt] at hre
  linarith

theorem integrableOn_archJump_mul (y : ℝ) :
    IntegrableOn (fun t : ℝ => archJump t * (1 - Real.cos (y * t))) (Ioi (0 : ℝ)) := by
  have hs : 0 < (1 / 4 + (y : ℂ) * I).re := by simp
  have hq : 0 < (1 / 4 : ℂ).re := by norm_num
  have i1 := integrableOn_digammaGaussIntegrand hs
  have i2 := integrableOn_digammaGaussIntegrand hq
  refine Integrable.congr ((i1.sub i2).re) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : (0 : ℝ) < t := ht
  have hden : 0 < 1 - Real.exp (-t) := by
    have := Real.exp_lt_one_iff.mpr (show -t < 0 by linarith); linarith
  simp only [Pi.sub_apply, RCLike.re_to_complex]
  unfold digammaGaussIntegrand archJump
  have hd : (1 : ℂ) - Complex.exp (-(t : ℂ)) = ((1 - Real.exp (-t) : ℝ) : ℂ) := by
    push_cast; rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
  rw [hd]
  have e1 : Complex.exp (-(1 / 4 + (y : ℂ) * I) * (t : ℂ)) =
      ((Real.exp (-(t / 4)) : ℝ) : ℂ) * Complex.exp (-((y * t : ℝ) : ℂ) * I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : Complex.exp (-(1 / 4 : ℂ) * (t : ℂ)) = ((Real.exp (-(t / 4)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [e1, e2]
  have hc : (Complex.exp (-((y * t : ℝ) : ℂ) * I)).re = Real.cos (y * t) := by
    rw [show -((y * t : ℝ) : ℂ) * I = ((-(y * t) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  simp only [Complex.sub_re, Complex.div_ofReal_re, Complex.ofReal_re, Complex.re_ofReal_mul, hc]
  field_simp
  ring

theorem continuous_paperFT_real_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (fun r : ℝ => paperFT f r) := by
  unfold paperFT
  refine continuous_of_dominated (bound := fun u => ‖f u‖) (fun r => ?_) (fun r => ?_) hf.norm ?_
  · exact hf.1.mul (by fun_prop : Continuous fun u : ℝ =>
      Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))).aestronglyMeasurable
  · refine Eventually.of_forall fun u => ?_
    rw [norm_mul, show Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
  · exact Eventually.of_forall fun u => by fun_prop

/-- The archimedean symbol as a constant plus a positive jump integral:
`A(τ) = Re ψ(1/4) - log π + ∫_0^∞ w(t)(1 - cos(τt/2)) dt`. -/
theorem archimedeanWeilSymbol_eq_jump (τ : ℝ) :
    archimedeanWeilSymbol (τ / (2 * π)) = (Complex.digamma (1 / 4)).re - Real.log π +
      ∫ t in Ioi (0 : ℝ), archJump t * (1 - Real.cos (τ / 2 * t)) := by
  rw [archimedeanWeilSymbol_eq]
  have h := re_digamma_quarter_line (τ / 2)
  have harg : ((1 / 4 : ℝ) : ℂ) + ((π * (τ / (2 * π)) : ℝ) : ℂ) * I =
      1 / 4 + ((τ / 2 : ℝ) : ℂ) * I := by
    have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    rw [show π * (τ / (2 * π)) = τ / 2 by field_simp]; push_cast; ring
  rw [harg, h]; ring

/-- **x-space form of the archimedean energy.**  For a `C²` test supported in `[-a, a]`,
`∫ |h_f|² A = (Re ψ(1/4) - log π) ∫ |h_f|² + ∫_0^∞ w(t) ∫ |h_f(τ)|² (1 - cos(τt/2)) dτ dt`. -/
theorem integral_normSq_mul_arch_eq_jump {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) =
      ((Complex.digamma (1 / 4)).re - Real.log π) * (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2) +
        ∫ t in Ioi (0 : ℝ), archJump t *
          ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (1 - Real.cos (τ / 2 * t)) := by
  set c := (Complex.digamma (1 / 4)).re - Real.log π with hc
  set J : ℝ → ℝ := fun τ => ∫ t in Ioi (0 : ℝ), archJump t * (1 - Real.cos (τ / 2 * t)) with hJ
  have hA : ∀ τ : ℝ, archimedeanWeilSymbol (τ / (2 * π)) = c + J τ := fun τ => by
    rw [archimedeanWeilSymbol_eq_jump]
  have hF := integrable_normSq_paperFT hf hfs
  have hFA := integrable_normSq_paperFT_mul_arch hf hfs
  have hFJ : Integrable (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * J τ) := by
    refine (hFA.sub (hF.const_mul c)).congr (Eventually.of_forall fun τ => ?_)
    simp only [Pi.sub_apply, hA]; ring
  have hsplit : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) =
      c * (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2) + ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * J τ := by
    rw [← integral_const_mul, ← integral_add (hF.const_mul c) hFJ]
    congr 1; funext τ; rw [hA]; ring
  rw [hsplit]
  congr 1
  -- Tonelli
  set H : ℝ → ℝ → ℝ := fun τ t => ‖paperFT f τ‖ ^ 2 * (archJump t * (1 - Real.cos (τ / 2 * t)))
    with hH
  have hHnn : ∀ τ, ∀ t ∈ Ioi (0 : ℝ), 0 ≤ H τ t := fun τ t ht =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (archJump_nonneg ht)
      (by linarith [Real.cos_le_one (τ / 2 * t)]))
  have hmeasF : Measurable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 := by
    have : Continuous fun τ : ℝ => paperFT f τ := by
      obtain ⟨hfc, -, -, -, -⟩ := weilTest_self_data hf hfs
      exact continuous_paperFT_real_of_integrable (hf.continuous.integrable_of_hasCompactSupport hfc)
    exact (this.norm.pow 2).measurable
  have hmeasW : Measurable archJump := by unfold archJump; fun_prop
  have hHm : AEStronglyMeasurable (Function.uncurry H)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine Measurable.aestronglyMeasurable ?_
    simp only [hH]
    exact (hmeasF.comp measurable_fst).mul ((hmeasW.comp measurable_snd).mul
      (measurable_const.sub (Real.continuous_cos.measurable.comp
        ((measurable_fst.div_const 2).mul measurable_snd))))
  have hint : Integrable (Function.uncurry H) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff hHm]
    refine ⟨Eventually.of_forall fun τ => ?_, ?_⟩
    · simp only [hH, Function.uncurry_apply_pair]
      exact (integrableOn_archJump_mul (τ / 2)).const_mul _
    · refine hFJ.congr (Eventually.of_forall fun τ => ?_)
      simp only [hJ, Function.uncurry_apply_pair]
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [Real.norm_of_nonneg (hHnn τ t ht)]
  have hswap := integral_integral_swap hint
  have hleft : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * J τ = ∫ τ : ℝ, ∫ t in Ioi (0 : ℝ), H τ t := by
    congr 1; funext τ; simp only [hH, hJ]; rw [integral_const_mul]
  have hright : ∫ t in Ioi (0 : ℝ), archJump t *
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (1 - Real.cos (τ / 2 * t)) =
      ∫ t in Ioi (0 : ℝ), ∫ τ : ℝ, H τ t := by
    congr 1; funext t; simp only [hH]; rw [← integral_const_mul]; congr 1; funext τ; ring
  rw [hleft, hright, hswap]


/-! ### A flat-top bump -/

section FlatBump

variable {b d : ℝ}

/-- The flat-top bump `g(x) = σ((b + x)/d) σ((b - x)/d)`: `1` on `[-(b-d), b-d]`, `0` outside
`(-b, b)`, nondecreasing on `x ≤ 0` and nonincreasing on `x ≥ 0`. -/
def flatBump (b d x : ℝ) : ℝ :=
  Real.smoothTransition ((b + x) / d) * Real.smoothTransition ((b - x) / d)

theorem contDiff_flatBump (b d : ℝ) : ContDiff ℝ 2 (flatBump b d) := by
  unfold flatBump
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem flatBump_nonneg (x : ℝ) : 0 ≤ flatBump b d x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem flatBump_le_one (x : ℝ) : flatBump b d x ≤ 1 := by
  unfold flatBump
  calc Real.smoothTransition ((b + x) / d) * Real.smoothTransition ((b - x) / d)
      ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
        (Real.smoothTransition.nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem flatBump_eq_zero (hd : 0 < d) {x : ℝ} (hx : b ≤ |x|) : flatBump b d x = 0 := by
  unfold flatBump
  rcases le_or_gt 0 x with h0 | h0
  · rw [abs_of_nonneg h0] at hx
    rw [show Real.smoothTransition ((b - x) / d) = 0 from
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le),
      mul_zero]
  · rw [abs_of_neg h0] at hx
    rw [show Real.smoothTransition ((b + x) / d) = 0 from
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le),
      zero_mul]

theorem flatBump_eq_one (hd : 0 < d) {x : ℝ} (hx : |x| ≤ b - d) : flatBump b d x = 1 := by
  unfold flatBump
  have h := abs_le.mp hx
  rw [Real.smoothTransition.one_of_one_le ((one_le_div hd).mpr (by linarith)),
    Real.smoothTransition.one_of_one_le ((one_le_div hd).mpr (by linarith)), one_mul]

theorem flatBump_of_nonpos (hd : 0 < d) (hdb : d ≤ b) {x : ℝ} (hx : x ≤ 0) :
    flatBump b d x = Real.smoothTransition ((b + x) / d) := by
  unfold flatBump
  rw [show Real.smoothTransition ((b - x) / d) = 1 from
    Real.smoothTransition.one_of_one_le ((one_le_div hd).mpr (by linarith)), mul_one]

theorem flatBump_of_nonneg (hd : 0 < d) (hdb : d ≤ b) {x : ℝ} (hx : 0 ≤ x) :
    flatBump b d x = Real.smoothTransition ((b - x) / d) := by
  unfold flatBump
  rw [show Real.smoothTransition ((b + x) / d) = 1 from
    Real.smoothTransition.one_of_one_le ((one_le_div hd).mpr (by linarith)), one_mul]

theorem flatBump_mono (hd : 0 < d) (hdb : d ≤ b) {x y : ℝ} (hy : y ≤ 0) (hxy : x ≤ y) :
    flatBump b d x ≤ flatBump b d y := by
  rw [flatBump_of_nonpos hd hdb (hxy.trans hy), flatBump_of_nonpos hd hdb hy]
  exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hd.le)

theorem flatBump_anti (hd : 0 < d) (hdb : d ≤ b) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    flatBump b d y ≤ flatBump b d x := by
  rw [flatBump_of_nonneg hd hdb hx, flatBump_of_nonneg hd hdb (hx.trans hxy)]
  exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hd.le)

theorem flatBump_zero (hd : 0 < d) (hdb : d ≤ b) : flatBump b d 0 = 1 :=
  flatBump_eq_one hd (by rw [abs_zero]; linarith)

theorem continuous_flatBump (b d : ℝ) : Continuous (flatBump b d) :=
  (contDiff_flatBump b d).continuous

theorem hasCompactSupport_flatBump (hd : 0 < d) (hdb : d ≤ b) :
    HasCompactSupport (flatBump b d) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -b) (b := b)) fun x hx => ?_
  apply flatBump_eq_zero hd
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem integrable_flatBump (hd : 0 < d) (hdb : d ≤ b) : Integrable (flatBump b d) :=
  (continuous_flatBump b d).integrable_of_hasCompactSupport (hasCompactSupport_flatBump hd hdb)

/-- The autocorrelation `R(y) = ∫ g(t) g(t - y) dt`. -/
def flatBumpCorr (b d y : ℝ) : ℝ := ∫ t : ℝ, flatBump b d t * flatBump b d (t - y)

theorem integrable_flatBump_mul_shift (hd : 0 < d) (hdb : d ≤ b) (y : ℝ) :
    Integrable (fun t => flatBump b d t * flatBump b d (t - y)) := by
  refine ((continuous_flatBump b d).mul ((continuous_flatBump b d).comp
    (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport ?_
  exact (hasCompactSupport_flatBump hd hdb).mul_right

/-- `R(0) ≥ 2(b - d)`. -/
theorem flatBumpCorr_zero_ge (hd : 0 < d) (hdb : d ≤ b) : 2 * (b - d) ≤ flatBumpCorr b d 0 := by
  unfold flatBumpCorr
  simp only [sub_zero]
  have hint := integrable_flatBump_mul_shift hd hdb 0
  simp only [sub_zero] at hint
  calc 2 * (b - d) = ∫ t in Icc (-(b - d)) (b - d), (1 : ℝ) := by
        rw [setIntegral_const, Measure.real, Real.volume_Icc, smul_eq_mul, mul_one,
          ENNReal.toReal_ofReal (by linarith)]; ring
    _ = ∫ t in Icc (-(b - d)) (b - d), flatBump b d t * flatBump b d t := by
        refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
        rw [flatBump_eq_one hd (abs_le.mpr ⟨ht.1, ht.2⟩), mul_one]
    _ ≤ ∫ t : ℝ, flatBump b d t * flatBump b d t :=
        setIntegral_le_integral hint (Eventually.of_forall fun t =>
          mul_nonneg (flatBump_nonneg t) (flatBump_nonneg t))

theorem flatBump_sub_shift_abs_le (y t : ℝ) : |flatBump b d t - flatBump b d (t - y)| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [flatBump_nonneg (b := b) (d := d) t, flatBump_le_one (b := b) (d := d) t,
    flatBump_nonneg (b := b) (d := d) (t - y), flatBump_le_one (b := b) (d := d) (t - y)]

theorem continuous_flatBump_sub_shift (b d y : ℝ) :
    Continuous fun t => flatBump b d t - flatBump b d (t - y) :=
  (continuous_flatBump b d).sub ((continuous_flatBump b d).comp (continuous_id.sub continuous_const))

theorem hasCompactSupport_flatBump_sub_shift (hd : 0 < d) (hdb : d ≤ b) (y : ℝ) :
    HasCompactSupport fun t => flatBump b d t - flatBump b d (t - y) :=
  (hasCompactSupport_flatBump hd hdb).sub
    ((hasCompactSupport_flatBump hd hdb).comp_homeomorph (Homeomorph.subRight y))

theorem integrable_flatBump_sub_shift (hd : 0 < d) (hdb : d ≤ b) (y : ℝ) :
    Integrable fun t => flatBump b d t - flatBump b d (t - y) :=
  (continuous_flatBump_sub_shift b d y).integrable_of_hasCompactSupport
    (hasCompactSupport_flatBump_sub_shift hd hdb y)

/-- `∫ (g(t) - g(t - y))² = 2 (R(0) - R(y))`. -/
theorem integral_flatBump_sub_shift_sq (hd : 0 < d) (hdb : d ≤ b) (y : ℝ) :
    ∫ t, (flatBump b d t - flatBump b d (t - y)) ^ 2 =
      2 * (flatBumpCorr b d 0 - flatBumpCorr b d y) := by
  have i1 : Integrable fun t => flatBump b d t * flatBump b d t := by
    simpa using integrable_flatBump_mul_shift hd hdb 0
  have i2 : Integrable fun t => flatBump b d t * flatBump b d (t - y) :=
    integrable_flatBump_mul_shift hd hdb y
  have i3 : Integrable fun t => flatBump b d (t - y) * flatBump b d (t - y) := by
    have := (i1.comp_sub_right y); simpa using this
  have e3 : ∫ t, flatBump b d (t - y) * flatBump b d (t - y) = ∫ t, flatBump b d t * flatBump b d t :=
    integral_sub_right_eq_self (fun t => flatBump b d t * flatBump b d t) y
  simp only [flatBumpCorr, sub_zero]
  have hfun : (fun t => (flatBump b d t - flatBump b d (t - y)) ^ 2) = fun t =>
      (flatBump b d t * flatBump b d t - 2 * (flatBump b d t * flatBump b d (t - y))) +
        flatBump b d (t - y) * flatBump b d (t - y) := by funext t; ring
  have a1 := integral_add (μ := volume)
    (f := fun t => flatBump b d t * flatBump b d t - 2 * (flatBump b d t * flatBump b d (t - y)))
    (g := fun t => flatBump b d (t - y) * flatBump b d (t - y)) (i1.sub (i2.const_mul 2)) i3
  have a2 := integral_sub (μ := volume) (f := fun t => flatBump b d t * flatBump b d t)
    (g := fun t => 2 * (flatBump b d t * flatBump b d (t - y))) i1 (i2.const_mul 2)
  rw [hfun, a1, a2, integral_const_mul, e3]
  ring

/-- `∫ (g(t) - g(t - y))⁺ ≤ y` for `y ≥ 0`: the positive part is dominated by the increments of
the monotone envelope `1_{t ≤ 0} g(t) + 1_{t > 0}`. -/
theorem integral_flatBump_sub_shift_pos_le (hd : 0 < d) (hdb : d ≤ b) {y : ℝ} (hy : 0 ≤ y) :
    ∫ t, max (flatBump b d t - flatBump b d (t - y)) 0 ≤ y := by
  set G : ℝ → ℝ := (Iic (0 : ℝ)).indicator (flatBump b d) with hG
  have hGi : Integrable G := (integrable_flatBump hd hdb).indicator measurableSet_Iic
  have hQi : Integrable fun t => max (flatBump b d t - flatBump b d (t - y)) 0 :=
    (integrable_flatBump_sub_shift hd hdb y).pos_part
  have hIi : Integrable ((Ioc 0 y).indicator fun _ => (1 : ℝ)) :=
    (integrableOn_const (by simp) (by simp)).integrable_indicator measurableSet_Ioc
  have hQle : ∀ t, max (flatBump b d t - flatBump b d (t - y)) 0 ≤
      (G t - G (t - y)) + (Ioc 0 y).indicator (fun _ => (1 : ℝ)) t := by
    intro t
    simp only [hG]
    rcases le_or_gt t 0 with ht | ht
    · have hty : t - y ≤ 0 := by linarith
      have hmono : flatBump b d (t - y) ≤ flatBump b d t := flatBump_mono hd hdb ht (by linarith)
      rw [indicator_of_mem (show t ∈ Iic (0 : ℝ) from ht),
        indicator_of_mem (show t - y ∈ Iic (0 : ℝ) from hty),
        indicator_of_notMem (show t ∉ Ioc 0 y from fun h => by linarith [h.1]),
        max_eq_left (by linarith)]
      linarith
    · rcases le_or_gt t y with hty | hty
      · have hty' : t - y ≤ 0 := by linarith
        rw [indicator_of_notMem (show t ∉ Iic (0 : ℝ) from fun h => by simp at h; linarith),
          indicator_of_mem (show t - y ∈ Iic (0 : ℝ) from hty'),
          indicator_of_mem (show t ∈ Ioc 0 y from ⟨ht, hty⟩)]
        have := flatBump_le_one (b := b) (d := d) t
        have := flatBump_le_one (b := b) (d := d) (t - y)
        exact max_le (by linarith) (by linarith)
      · have hanti : flatBump b d t ≤ flatBump b d (t - y) :=
          flatBump_anti hd hdb (by linarith) (by linarith)
        rw [indicator_of_notMem (show t ∉ Iic (0 : ℝ) from fun h => by simp at h; linarith),
          indicator_of_notMem (show t - y ∉ Iic (0 : ℝ) from fun h => by simp at h; linarith),
          indicator_of_notMem (show t ∉ Ioc 0 y from fun h => by linarith [h.2]),
          max_eq_right (by linarith)]
        simp
  calc ∫ t, max (flatBump b d t - flatBump b d (t - y)) 0
      ≤ ∫ t, ((G t - G (t - y)) + (Ioc 0 y).indicator (fun _ => (1 : ℝ)) t) :=
        integral_mono hQi ((hGi.sub (hGi.comp_sub_right y)).add hIi) hQle
    _ = y := by
        have b1 := integral_add (μ := volume) (f := fun t => G t - G (t - y))
          (g := (Ioc 0 y).indicator fun _ => (1 : ℝ)) (hGi.sub (hGi.comp_sub_right y)) hIi
        have b2 := integral_sub (μ := volume) (f := G) (g := fun t => G (t - y)) hGi
          (hGi.comp_sub_right y)
        rw [b1, b2, integral_sub_right_eq_self G y, sub_self, zero_add,
          integral_indicator measurableSet_Ioc, setIntegral_const, Measure.real,
          Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one, sub_zero]

/-- **The autocorrelation drops at most linearly**: `R(0) - R(y) ≤ y` for `y ≥ 0`. -/
theorem flatBumpCorr_sub_le (hd : 0 < d) (hdb : d ≤ b) {y : ℝ} (hy : 0 ≤ y) :
    flatBumpCorr b d 0 - flatBumpCorr b d y ≤ y := by
  have hPi := integrable_flatBump_sub_shift hd hdb y
  have hsq := integral_flatBump_sub_shift_sq hd hdb y
  have hpt : ∀ t, (flatBump b d t - flatBump b d (t - y)) ^ 2 ≤
      |flatBump b d t - flatBump b d (t - y)| := fun t => by
    have h1 := flatBump_sub_shift_abs_le (b := b) (d := d) y t
    have h0 := abs_nonneg (flatBump b d t - flatBump b d (t - y))
    have e : (flatBump b d t - flatBump b d (t - y)) ^ 2 =
        |flatBump b d t - flatBump b d (t - y)| * |flatBump b d t - flatBump b d (t - y)| := by
      rw [← sq, sq_abs]
    rw [e]; exact mul_le_of_le_one_left h0 h1
  have hsqi : Integrable fun t => (flatBump b d t - flatBump b d (t - y)) ^ 2 := by
    refine hPi.abs.mono' ((continuous_flatBump_sub_shift b d y).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpt t
  have hle : ∫ t, (flatBump b d t - flatBump b d (t - y)) ^ 2 ≤
      ∫ t, |flatBump b d t - flatBump b d (t - y)| := integral_mono hsqi hPi.abs hpt
  have hPint : ∫ t, (flatBump b d t - flatBump b d (t - y)) = 0 := by
    rw [integral_sub (integrable_flatBump hd hdb) ((integrable_flatBump hd hdb).comp_sub_right y),
      integral_sub_right_eq_self (flatBump b d) y, sub_self]
  have habs : ∫ t, |flatBump b d t - flatBump b d (t - y)| =
      2 * ∫ t, max (flatBump b d t - flatBump b d (t - y)) 0 := by
    have hfun : (fun t => |flatBump b d t - flatBump b d (t - y)|) = fun t =>
        2 * max (flatBump b d t - flatBump b d (t - y)) 0 - (flatBump b d t - flatBump b d (t - y)) := by
      funext t
      rcases le_total 0 (flatBump b d t - flatBump b d (t - y)) with h | h
      · rw [abs_of_nonneg h, max_eq_left h]; ring
      · rw [abs_of_nonpos h, max_eq_right h]; ring
    have c1 := integral_sub (μ := volume)
      (f := fun t => 2 * max (flatBump b d t - flatBump b d (t - y)) 0)
      (g := fun t => flatBump b d t - flatBump b d (t - y))
      ((integrable_flatBump_sub_shift hd hdb y).pos_part.const_mul 2) hPi
    rw [hfun, c1, integral_const_mul, hPint, sub_zero]
  have hpos := integral_flatBump_sub_shift_pos_le hd hdb hy
  linarith


/-- The Weil test of the flat-top bump is its (real) autocorrelation. -/
theorem weilTest_flatBump (b d y : ℝ) :
    EF.weilTest (fun x => (flatBump b d x : ℂ)) (fun x => (flatBump b d x : ℂ)) y =
      (flatBumpCorr b d y : ℂ) := by
  unfold EF.weilTest flatBumpCorr
  rw [convolution_def, ← integral_complex_ofReal]
  congr 1; funext t
  simp only [ContinuousLinearMap.mul_apply', EF.tilde, Complex.conj_ofReal]
  push_cast
  ring_nf

theorem flatBumpCorr_neg (b d y : ℝ) : flatBumpCorr b d (-y) = flatBumpCorr b d y := by
  unfold flatBumpCorr
  have := integral_sub_right_eq_self (μ := volume)
    (fun t => flatBump b d t * flatBump b d (t + y)) y
  simp only [sub_add_cancel] at this
  simp only [sub_neg_eq_add]
  rw [← this]
  congr 1; funext t; ring

theorem flatBumpCorr_eq_zero (hd : 0 < d) {y : ℝ} (hy : 2 * b ≤ |y|) : flatBumpCorr b d y = 0 := by
  unfold flatBumpCorr
  have : (fun t => flatBump b d t * flatBump b d (t - y)) = fun _ => (0 : ℝ) := by
    funext t
    rcases le_or_gt b |t| with ht | ht
    · rw [flatBump_eq_zero hd ht, zero_mul]
    · have : b ≤ |t - y| := by
        have := abs_sub_abs_le_abs_sub y t
        rw [abs_sub_comm] at this; linarith
      rw [flatBump_eq_zero hd this, mul_zero]
  rw [this, integral_zero]

end FlatBump

/-! ### A prime-blind test with negative archimedean energy -/

section FejerNegativity

/-- The flat-top test with `b = 17/50`, `d = 17/1000`: its autocorrelation lives in
`(-log 2, log 2)`, so it does not see any prime power. -/
def fejerTest (x : ℝ) : ℂ := (flatBump (17 / 50) (17 / 1000) x : ℂ)

theorem contDiff_fejerTest : ContDiff ℝ 2 fejerTest :=
  Complex.ofRealCLM.contDiff.comp (contDiff_flatBump _ _)

theorem tsupport_fejerTest : tsupport fejerTest ⊆ Icc (-(17 / 50)) (17 / 50) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra h
  apply hx
  have : 17 / 50 ≤ |x| := by
    simp only [mem_Icc, not_and_or, not_le] at h
    rcases h with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  simp [fejerTest, flatBump_eq_zero (by norm_num : (0 : ℝ) < 17 / 1000) this]

theorem integral_normSq_paperFT_fejerTest_mul_cos (y : ℝ) :
    ∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2 * Real.cos (τ * y) =
      2 * π * flatBumpCorr (17 / 50) (17 / 1000) y := by
  rw [integral_normSq_paperFT_mul_cos_eq contDiff_fejerTest tsupport_fejerTest y]
  unfold fejerTest
  rw [weilTest_flatBump, weilTest_flatBump, flatBumpCorr_neg]
  simp only [Complex.add_re, Complex.ofReal_re]
  ring

theorem archJump_mul_le {t : ℝ} (ht : 0 < t) : archJump t * t ≤ 1 + t := by
  unfold archJump
  have hden : 0 < 1 - Real.exp (-t) := by
    have := Real.exp_lt_one_iff.mpr (show -t < 0 by linarith); linarith
  have h1 : Real.exp (-(t / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : (1 + t) * Real.exp (-t) ≤ 1 := by
    have := Real.add_one_le_exp t
    rw [Real.exp_neg]
    rw [mul_inv_le_iff₀ (Real.exp_pos t)]; linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith [Real.exp_pos (-(t / 4)), Real.exp_pos (-t)]

theorem archJump_le_tail {c t : ℝ} (hc : 0 < c) (ht : c ≤ t) :
    archJump t ≤ Real.exp (-(1 / 4) * t) + Real.exp (-(5 / 4) * t) / (1 - Real.exp (-c)) := by
  unfold archJump
  have hct : Real.exp (-t) ≤ Real.exp (-c) := Real.exp_le_exp.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-c) := by
    have := Real.exp_lt_one_iff.mpr (show -c < 0 by linarith); linarith
  have hden' : 0 < 1 - Real.exp (-t) := by linarith
  have e : Real.exp (-(t / 4)) / (1 - Real.exp (-t)) = Real.exp (-(1 / 4) * t) +
      Real.exp (-(5 / 4) * t) / (1 - Real.exp (-t)) := by
    have : Real.exp (-(5 / 4) * t) = Real.exp (-(1 / 4) * t) * Real.exp (-t) := by
      rw [← Real.exp_add]; ring_nf
    rw [this, show -(t / 4) = -(1 / 4) * t by ring]
    field_simp
    ring
  rw [e]
  gcongr

/-- The numeric core of the Fejér negativity. -/
theorem fejer_numeric {R0 : ℝ} (hR0 : 323 / 500 ≤ R0) :
    (-(3 * Real.log 2 + Real.eulerMascheroniConstant + π / 2) - Real.log π) * R0 +
      (2 * (17 / 50) + 4 * (17 / 50) ^ 2) +
      R0 * (4 * Real.exp (-(17 / 50)) + 4 / 5 * Real.exp (-(5 * (17 / 50))) /
        (1 - Real.exp (-(4 * (17 / 50))))) < 0 := by
  have hl2 := Real.log_two_gt_d9
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hπ := Real.pi_gt_d2
  have hlπ : 1 < Real.log π := by
    rw [Real.lt_log_iff_exp_lt Real.pi_pos]
    have := Real.exp_one_lt_d9; linarith
  have eb : Real.exp (-(17 / 50)) ≤ 1 / (1 + 17 / 50 + (17 / 50) ^ 2 / 2) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) (Real.quadratic_le_exp_of_nonneg (by norm_num))
  have e5 : Real.exp (-(5 * (17 / 50))) ≤ 1 / (1 + 5 * (17 / 50) + (5 * (17 / 50)) ^ 2 / 2) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) (Real.quadratic_le_exp_of_nonneg (by norm_num))
  have e4 : Real.exp (-(4 * (17 / 50))) ≤ 1 / (1 + 4 * (17 / 50) + (4 * (17 / 50)) ^ 2 / 2) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) (Real.quadratic_le_exp_of_nonneg (by norm_num))
  have hden : 0.69 ≤ 1 - Real.exp (-(4 * (17 / 50))) := by norm_num at e4 ⊢; linarith
  have htail : 4 / 5 * Real.exp (-(5 * (17 / 50))) / (1 - Real.exp (-(4 * (17 / 50)))) ≤ 0.28 := by
    rw [div_le_iff₀ (by linarith)]
    norm_num at e5 ⊢; nlinarith [Real.exp_pos (-(17 / 10))]
  have hI : 4 * Real.exp (-(17 / 50)) + 4 / 5 * Real.exp (-(5 * (17 / 50))) /
      (1 - Real.exp (-(4 * (17 / 50)))) ≤ 3.15 := by
    norm_num at eb ⊢; linarith
  have hR0' : 0 < R0 := by linarith
  nlinarith

/-- **A prime-blind test with negative archimedean energy.**  The flat-top test supported in
`[-17/50, 17/50]` (so its autocorrelation vanishes at every `log n`, `n ≥ 2`) has
`∫ |h|² A < 0`: the archimedean symbol alone is not positive below the first prime. -/
theorem integral_normSq_paperFT_fejerTest_mul_arch_neg :
    ∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) < 0 := by
  set b : ℝ := 17 / 50 with hb
  set d : ℝ := 17 / 1000 with hd
  have hd0 : (0 : ℝ) < d := by norm_num
  have hdb : d ≤ b := by norm_num
  set R := flatBumpCorr b d with hR
  set R0 := R 0 with hR0
  have hR0ge : 323 / 500 ≤ R0 := by
    have := flatBumpCorr_zero_ge hd0 hdb; rw [hR0, hR]; norm_num at this ⊢; linarith
  rw [integral_normSq_mul_arch_eq_jump contDiff_fejerTest tsupport_fejerTest]
  have hF := integrable_normSq_paperFT contDiff_fejerTest tsupport_fejerTest
  have hF2 : ∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2 = 2 * π * R0 := by
    have := integral_normSq_paperFT_fejerTest_mul_cos 0
    simp only [mul_zero, Real.cos_zero, mul_one] at this
    exact this
  have hJ : ∀ t : ℝ, ∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2 * (1 - Real.cos (τ / 2 * t)) =
      2 * π * (R0 - R (t / 2)) := by
    intro t
    have hc := integrable_normSq_paperFT_mul_cos contDiff_fejerTest tsupport_fejerTest (t / 2)
    have e1 : (fun τ : ℝ => ‖paperFT fejerTest τ‖ ^ 2 * (1 - Real.cos (τ / 2 * t))) =
        fun τ : ℝ => ‖paperFT fejerTest τ‖ ^ 2 - ‖paperFT fejerTest τ‖ ^ 2 * Real.cos (τ * (t / 2)) := by
      funext τ; rw [show τ / 2 * t = τ * (t / 2) by ring]; ring
    rw [e1, integral_sub hF hc, hF2, integral_normSq_paperFT_fejerTest_mul_cos]
    ring
  rw [hF2, setIntegral_congr_fun measurableSet_Ioi (fun t _ => by rw [hJ t])]
  -- the dominating function
  set c : ℝ := 4 * b with hc
  have hc0 : 0 < c := by norm_num [hc, hb]
  set T : ℝ → ℝ := fun t => Real.exp (-(1 / 4) * t) + Real.exp (-(5 / 4) * t) / (1 - Real.exp (-c))
    with hT
  set U : ℝ → ℝ := fun t => 2 * π * ((Ioc 0 c).indicator (fun t => (1 + t) / 2) t +
    (Ioi c).indicator (fun t => R0 * T t) t) with hU
  have hden : 0 < 1 - Real.exp (-c) := by
    have := Real.exp_lt_one_iff.mpr (show -c < 0 by linarith); linarith
  have hTi : IntegrableOn T (Ioi c) := by
    refine (integrableOn_exp_mul_Ioi (by norm_num : (-(1 / 4) : ℝ) < 0) c).add
      ((integrableOn_exp_mul_Ioi (by norm_num : (-(5 / 4) : ℝ) < 0) c).div_const _)
  have hUi : Integrable U := by
    refine (((((continuous_const.add continuous_id |>.div_const 2 |>.integrableOn_Icc).mono_set
      Ioc_subset_Icc_self).integrable_indicator
        measurableSet_Ioc).add ((show IntegrableOn (fun t => R0 * T t) (Ioi c) volume from hTi.const_mul R0).integrable_indicator
        measurableSet_Ioi)).const_mul
          (2 * π))
  have hV0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ archJump t * (2 * π * (R0 - R (t / 2))) := by
    intro t ht
    have : 0 ≤ R0 - R (t / 2) := by
      have := integral_flatBump_sub_shift_sq hd0 hdb (t / 2)
      have hnn : 0 ≤ ∫ s, (flatBump b d s - flatBump b d (s - t / 2)) ^ 2 :=
        integral_nonneg fun _ => sq_nonneg _
      rw [hR0, hR]; linarith
    exact mul_nonneg (archJump_nonneg ht) (by positivity)
  have hVU : ∀ t ∈ Ioi (0 : ℝ), archJump t * (2 * π * (R0 - R (t / 2))) ≤ U t := by
    intro t ht
    have ht0 : 0 < t := ht
    simp only [hU]
    rcases le_or_gt t c with htc | htc
    · rw [indicator_of_mem (show t ∈ Ioc 0 c from ⟨ht0, htc⟩),
        indicator_of_notMem (show t ∉ Ioi c from fun h => by simp at h; linarith), add_zero]
      have h1 := flatBumpCorr_sub_le hd0 hdb (show 0 ≤ t / 2 by linarith)
      have h2 := archJump_mul_le ht0
      have hw := archJump_nonneg ht0
      have hπ := Real.pi_pos
      rw [hR0, hR]
      calc archJump t * (2 * π * (flatBumpCorr b d 0 - flatBumpCorr b d (t / 2)))
          ≤ archJump t * (2 * π * (t / 2)) := by gcongr
        _ = 2 * π * ((archJump t * t) / 2) := by ring
        _ ≤ 2 * π * ((1 + t) / 2) := by gcongr
    · rw [indicator_of_notMem (show t ∉ Ioc 0 c from fun h => by linarith [h.2]),
        indicator_of_mem (show t ∈ Ioi c from htc), zero_add]
      have hz : R (t / 2) = 0 := by
        rw [hR]
        apply flatBumpCorr_eq_zero hd0
        have h68 : 68 / 50 < t := by rw [hc, hb] at htc; linarith
        rw [abs_of_pos (by linarith), hb]
        linarith
      rw [hz, sub_zero]
      have hw := archJump_le_tail hc0 htc.le
      have hπ := Real.pi_pos
      have hR0pos : 0 ≤ R0 := by linarith
      calc archJump t * (2 * π * R0) ≤ T t * (2 * π * R0) := by gcongr
        _ = 2 * π * (R0 * T t) := by ring
  have hbound : ∫ t in Ioi (0 : ℝ), archJump t * (2 * π * (R0 - R (t / 2))) ≤
      ∫ t in Ioi (0 : ℝ), U t :=
    integral_mono_of_nonneg ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hV0))
      hUi.integrableOn ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hVU))
  have hUint : ∫ t in Ioi (0 : ℝ), U t = 2 * π * ((c / 2 + c ^ 2 / 4) +
      R0 * (4 * Real.exp (-(c / 4)) + 4 / 5 * Real.exp (-(5 * (c / 4))) / (1 - Real.exp (-c)))) := by
    simp only [hU]
    rw [integral_const_mul]
    congr 1
    have hsub1 : Ioc 0 c ⊆ Ioi 0 := fun t ht => ht.1
    have hsub2 : Ioi c ⊆ Ioi 0 := fun t ht => lt_trans hc0 ht
    rw [integral_add, setIntegral_indicator measurableSet_Ioc, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr hsub1, Set.inter_eq_right.mpr hsub2]
    · rw [← intervalIntegral.integral_of_le hc0.le, intervalIntegral.integral_div,
        intervalIntegral.integral_add intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
        integral_const_mul]
      simp only [hT]
      rw [integral_add (integrableOn_exp_mul_Ioi (by norm_num : (-(1 / 4) : ℝ) < 0) c)
        ((integrableOn_exp_mul_Ioi (by norm_num : (-(5 / 4) : ℝ) < 0) c).div_const _),
        integral_div, integral_exp_mul_Ioi (by norm_num) c, integral_exp_mul_Ioi (by norm_num) c]
      simp
      ring_nf
    · exact (((continuous_const.add continuous_id |>.div_const 2 |>.integrableOn_Icc).mono_set
        Ioc_subset_Icc_self).integrable_indicator
          measurableSet_Ioc).integrableOn
    · exact ((show IntegrableOn (fun t => R0 * T t) (Ioi c) volume from hTi.const_mul R0).integrable_indicator
        measurableSet_Ioi).integrableOn
  have hnum := fejer_numeric hR0ge
  have hψ : (Complex.digamma (1 / 4)).re =
      -(3 * Real.log 2 + Real.eulerMascheroniConstant + π / 2) := by
    rw [GaloisForLFunctions.RHTower.digamma_quarter, Complex.neg_re, Complex.ofReal_re]
  rw [hψ]
  have hc4 : c / 4 = 17 / 50 := by rw [hc, hb]; ring
  have hc4' : 5 * (c / 4) = 5 * (17 / 50) := by rw [hc4]
  have hcc : c = 4 * (17 / 50) := by rw [hc, hb]
  have hπ := Real.pi_pos
  calc (-(3 * Real.log 2 + Real.eulerMascheroniConstant + π / 2) - Real.log π) * (2 * π * R0) +
        ∫ t in Ioi (0 : ℝ), archJump t * (2 * π * (R0 - R (t / 2)))
      ≤ (-(3 * Real.log 2 + Real.eulerMascheroniConstant + π / 2) - Real.log π) * (2 * π * R0) +
        ∫ t in Ioi (0 : ℝ), U t := by linarith
    _ = 2 * π * ((-(3 * Real.log 2 + Real.eulerMascheroniConstant + π / 2) - Real.log π) * R0 +
        (2 * (17 / 50) + 4 * (17 / 50) ^ 2) +
        R0 * (4 * Real.exp (-(17 / 50)) + 4 / 5 * Real.exp (-(5 * (17 / 50))) /
          (1 - Real.exp (-(4 * (17 / 50)))))) := by
        rw [hUint, hc4, hcc]; ring
    _ < 0 := mul_neg_of_pos_of_neg (by positivity) hnum

end FejerNegativity

/-! ### Summable weights: the full symbol is negative somewhere -/

section SummableWeights

/-- The `n`-th atom of the finite-atom symbol (zero for `n < 2`). -/
def weightAtom (lam : ℕ → ℝ) (n : ℕ) (ξ : ℝ) : ℝ :=
  if 2 ≤ n then lam n * (1 / Real.sqrt n) * (2 * Real.cos (2 * π * Real.log n * ξ)) else 0

/-- The symbol with all atoms, `A - Σ_{n ≥ 2} 2 λ(n) n^{-1/2} cos(2π ξ log n)`. -/
def fullAtomSymbol (lam : ℕ → ℝ) (ξ : ℝ) : ℝ := archimedeanWeilSymbol ξ - ∑' n : ℕ, weightAtom lam n ξ

variable {lam : ℕ → ℝ}

theorem abs_weightAtom_le (lam : ℕ → ℝ) (n : ℕ) (ξ : ℝ) :
    |weightAtom lam n ξ| ≤ 2 * (|lam n| / Real.sqrt n) := by
  unfold weightAtom
  split_ifs
  · rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt n),
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := Real.abs_cos_le_one (2 * π * Real.log n * ξ)
    have h0 : 0 ≤ |lam n| * (1 / Real.sqrt n) := by positivity
    calc |lam n| * (1 / Real.sqrt n) * (2 * |Real.cos (2 * π * Real.log n * ξ)|)
        ≤ |lam n| * (1 / Real.sqrt n) * (2 * 1) := by gcongr
      _ = 2 * (|lam n| / Real.sqrt n) := by ring
  · simp; positivity

theorem summable_weightAtom (hsum : Summable fun n => |lam n| / Real.sqrt n) (ξ : ℝ) :
    Summable fun n => weightAtom lam n ξ :=
  Summable.of_norm_bounded (hsum.mul_left 2) fun n => by
    rw [Real.norm_eq_abs]; exact abs_weightAtom_le lam n ξ

theorem sum_Icc_eq_sum_range_weightAtom (lam : ℕ → ℝ) (N : ℕ) (ξ : ℝ) :
    ∑ n ∈ Finset.Icc 2 N, lam n * (1 / Real.sqrt n) * (2 * Real.cos (2 * π * Real.log n * ξ)) =
      ∑ n ∈ Finset.range (N + 1), weightAtom lam n ξ := by
  unfold weightAtom
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n; simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]; omega

/-- Truncating the atoms at `N` changes the symbol by at most twice the weight tail. -/
theorem abs_weilAtomSymbol_sub_full_le (hsum : Summable fun n => |lam n| / Real.sqrt n)
    (N : ℕ) (ξ : ℝ) :
    |weilAtomSymbol lam N ξ - fullAtomSymbol lam ξ| ≤
      2 * ∑' k : ℕ, |lam (k + (N + 1))| / Real.sqrt (k + (N + 1) : ℕ) := by
  have hs := summable_weightAtom hsum ξ
  have hsplit := hs.sum_add_tsum_nat_add (N + 1)
  unfold weilAtomSymbol fullAtomSymbol
  rw [sum_Icc_eq_sum_range_weightAtom, ← hsplit]
  have e : archimedeanWeilSymbol ξ - ∑ n ∈ Finset.range (N + 1), weightAtom lam n ξ -
      (archimedeanWeilSymbol ξ - (∑ n ∈ Finset.range (N + 1), weightAtom lam n ξ +
        ∑' k : ℕ, weightAtom lam (k + (N + 1)) ξ)) = ∑' k : ℕ, weightAtom lam (k + (N + 1)) ξ := by
    ring
  rw [e]
  have htail : Summable fun k : ℕ => |lam (k + (N + 1))| / Real.sqrt (k + (N + 1) : ℕ) :=
    (summable_nat_add_iff (N + 1)).mpr hsum
  calc |∑' k : ℕ, weightAtom lam (k + (N + 1)) ξ|
      ≤ ∑' k : ℕ, |weightAtom lam (k + (N + 1)) ξ| := by
        have := ((summable_nat_add_iff (N + 1)).mpr hs).abs
        have h := norm_tsum_le_tsum_norm (f := fun k : ℕ => weightAtom lam (k + (N + 1)) ξ)
          (by simpa [Real.norm_eq_abs] using this)
        simpa [Real.norm_eq_abs] using h
    _ ≤ ∑' k : ℕ, 2 * (|lam (k + (N + 1))| / Real.sqrt (k + (N + 1) : ℕ)) :=
        Summable.tsum_le_tsum (fun k => abs_weightAtom_le lam _ ξ)
          ((summable_nat_add_iff (N + 1)).mpr hs).abs (htail.mul_left 2)
    _ = 2 * ∑' k : ℕ, |lam (k + (N + 1))| / Real.sqrt (k + (N + 1) : ℕ) := tsum_mul_left

theorem tendsto_weight_tail (lam : ℕ → ℝ) :
    Tendsto (fun N : ℕ => 2 * ∑' k : ℕ, |lam (k + (N + 1))| / Real.sqrt (k + (N + 1) : ℕ))
      atTop (𝓝 0) := by
  have h := (tendsto_sum_nat_add fun n => |lam n| / Real.sqrt n).comp (tendsto_add_atTop_nat 1)
  simpa using h.const_mul 2

theorem continuous_fullAtomSymbol (hsum : Summable fun n => |lam n| / Real.sqrt n) :
    Continuous (fullAtomSymbol lam) := by
  have hA : Continuous archimedeanWeilSymbol := by
    have : archimedeanWeilSymbol = fun ξ => archFreq (2 * π * ξ) := by
      funext ξ; unfold archFreq; congr 1; field_simp
    rw [this]; exact continuous_archFreq.comp (by fun_prop)
  refine hA.sub (continuous_tsum (fun n => ?_) (hsum.mul_left 2) fun n ξ => ?_)
  · unfold weightAtom; split_ifs <;> fun_prop
  · rw [Real.norm_eq_abs]; exact abs_weightAtom_le lam n ξ

/-- On the prime-blind Fejér test the atoms are invisible:
`∫ |h|² S_full = ∫ |h|² A`. -/
theorem integral_normSq_fejerTest_mul_full (hsum : Summable fun n => |lam n| / Real.sqrt n) :
    ∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2 * fullAtomSymbol lam (τ / (2 * π)) =
      ∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) := by
  have hF := integrable_normSq_paperFT contDiff_fejerTest tsupport_fejerTest
  have hFA := integrable_normSq_paperFT_mul_arch contDiff_fejerTest tsupport_fejerTest
  set M := ∑' n : ℕ, 2 * (|lam n| / Real.sqrt n) with hM
  have hterm : ∀ n : ℕ, Integrable fun τ : ℝ =>
      ‖paperFT fejerTest τ‖ ^ 2 * weightAtom lam n (τ / (2 * π)) := by
    intro n
    unfold weightAtom
    split_ifs
    · have hc := integrable_normSq_paperFT_mul_cos contDiff_fejerTest tsupport_fejerTest (Real.log n)
      refine (hc.const_mul (lam n * (1 / Real.sqrt n) * 2)).congr (Eventually.of_forall fun τ => ?_)
      simp only
      rw [show 2 * π * Real.log n * (τ / (2 * π)) = τ * Real.log n by field_simp]; ring
    · simp
  have hzero : ∀ n : ℕ, ∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2 * weightAtom lam n (τ / (2 * π)) = 0 := by
    intro n
    unfold weightAtom
    split_ifs with hn
    · have hlog : 2 * (17 / 50) < |Real.log n| := by
        have h2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
        have := Real.log_two_gt_d9
        rw [abs_of_nonneg (by linarith)]; linarith
      have hz := integral_normSq_paperFT_mul_cos_eq_zero contDiff_fejerTest tsupport_fejerTest hlog
      have e : (fun τ : ℝ => ‖paperFT fejerTest τ‖ ^ 2 *
          (lam n * (1 / Real.sqrt n) * (2 * Real.cos (2 * π * Real.log n * (τ / (2 * π)))))) =
          fun τ : ℝ => (lam n * (1 / Real.sqrt n) * 2) *
            (‖paperFT fejerTest τ‖ ^ 2 * Real.cos (τ * Real.log n)) := by
        funext τ
        rw [show 2 * π * Real.log n * (τ / (2 * π)) = τ * Real.log n by field_simp]; ring
      rw [e, integral_const_mul, hz, mul_zero]
    · simp
  have hnorm : Summable fun n : ℕ => ∫ τ : ℝ,
      ‖‖paperFT fejerTest τ‖ ^ 2 * weightAtom lam n (τ / (2 * π))‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) ((hsum.mul_left 2).mul_right (∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2))
    calc ∫ τ : ℝ, ‖‖paperFT fejerTest τ‖ ^ 2 * weightAtom lam n (τ / (2 * π))‖
        ≤ ∫ τ : ℝ, 2 * (|lam n| / Real.sqrt n) * ‖paperFT fejerTest τ‖ ^ 2 :=
          integral_mono (hterm n).norm (hF.const_mul _) fun τ => by
            rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs, mul_comm]
            exact mul_le_mul_of_nonneg_right (abs_weightAtom_le lam n _) (sq_nonneg _)
      _ = 2 * (|lam n| / Real.sqrt n) * ∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2 := integral_const_mul _ _
  have hswap := integral_tsum_of_summable_integral_norm hterm hnorm
  have hsum0 : ∑' n : ℕ, ∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2 * weightAtom lam n (τ / (2 * π)) = 0 := by
    simp [hzero]
  rw [hsum0] at hswap
  have hcF : Continuous fun τ : ℝ => ‖paperFT fejerTest τ‖ ^ 2 :=
    ((continuous_paperFT_real_of_integrable (contDiff_fejerTest.continuous.integrable_of_hasCompactSupport
      (IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) tsupport_fejerTest))).norm.pow 2)
  have hcT : Continuous fun τ : ℝ => ∑' n : ℕ, weightAtom lam n (τ / (2 * π)) :=
    continuous_tsum (fun n => by unfold weightAtom; split_ifs <;> fun_prop) (hsum.mul_left 2)
      fun n τ => by rw [Real.norm_eq_abs]; exact abs_weightAtom_le lam n _
  have hTi : Integrable fun τ : ℝ =>
      ∑' n : ℕ, ‖paperFT fejerTest τ‖ ^ 2 * weightAtom lam n (τ / (2 * π)) := by
    refine (hF.mul_const (∑' n : ℕ, 2 * (|lam n| / Real.sqrt n))).mono' ?_
      (Eventually.of_forall fun τ => ?_)
    · refine (hcF.mul hcT).aestronglyMeasurable.congr (Eventually.of_forall fun τ => ?_)
      simp only [Pi.mul_apply]; rw [tsum_mul_left]
    · rw [tsum_mul_left, norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rw [Real.norm_eq_abs]
      have hs := summable_weightAtom hsum (τ / (2 * π))
      calc |∑' n : ℕ, weightAtom lam n (τ / (2 * π))| ≤ ∑' n : ℕ, |weightAtom lam n (τ / (2 * π))| := by
            have h := norm_tsum_le_tsum_norm (f := fun n => weightAtom lam n (τ / (2 * π)))
              (by simpa [Real.norm_eq_abs] using hs.abs)
            simpa [Real.norm_eq_abs] using h
        _ ≤ ∑' n : ℕ, 2 * (|lam n| / Real.sqrt n) :=
            Summable.tsum_le_tsum (fun n => abs_weightAtom_le lam n _) hs.abs (hsum.mul_left 2)
  have e : (fun τ : ℝ => ‖paperFT fejerTest τ‖ ^ 2 * fullAtomSymbol lam (τ / (2 * π))) =
      fun τ : ℝ => ‖paperFT fejerTest τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) -
        ∑' n : ℕ, ‖paperFT fejerTest τ‖ ^ 2 * weightAtom lam n (τ / (2 * π)) := by
    funext τ; unfold fullAtomSymbol; rw [tsum_mul_left]; ring
  rw [e, integral_sub hFA hTi, ← hswap, sub_zero]

/-- **The full symbol of summable weights is negative somewhere.** -/
theorem exists_fullAtomSymbol_neg (hsum : Summable fun n => |lam n| / Real.sqrt n) :
    ∃ τ₁ : ℝ, fullAtomSymbol lam (τ₁ / (2 * π)) < 0 := by
  by_contra h
  push Not at h
  have hneg := integral_normSq_paperFT_fejerTest_mul_arch_neg
  rw [← integral_normSq_fejerTest_mul_full hsum] at hneg
  have : 0 ≤ ∫ τ : ℝ, ‖paperFT fejerTest τ‖ ^ 2 * fullAtomSymbol lam (τ / (2 * π)) :=
    integral_nonneg fun τ => mul_nonneg (sq_nonneg _) (h τ)
  linarith

local notation "Φ" => riemannPhiKernel

theorem abs_fullAtomSymbol_le (hsum : Summable fun n => |lam n| / Real.sqrt n) (τ₀ τ : ℝ) :
    |fullAtomSymbol lam (τ / (2 * π))| ≤
      (70 + 2 * |gammaHardyPhaseRate 0| + 2 * |τ₀| + ∑' n : ℕ, 2 * (|lam n| / Real.sqrt n) + 2) *
        (1 + |τ - τ₀|) := by
  unfold fullAtomSymbol
  have hA : archimedeanWeilSymbol (τ / (2 * π)) = archFreq τ := rfl
  rw [hA]
  have h1 := abs_archFreq_le τ
  have hs := summable_weightAtom hsum (τ / (2 * π))
  have h2 : |∑' n : ℕ, weightAtom lam n (τ / (2 * π))| ≤ ∑' n : ℕ, 2 * (|lam n| / Real.sqrt n) := by
    calc |∑' n : ℕ, weightAtom lam n (τ / (2 * π))| ≤ ∑' n : ℕ, |weightAtom lam n (τ / (2 * π))| := by
          have h := norm_tsum_le_tsum_norm (f := fun n => weightAtom lam n (τ / (2 * π)))
            (by simpa [Real.norm_eq_abs] using hs.abs)
          simpa [Real.norm_eq_abs] using h
      _ ≤ _ := Summable.tsum_le_tsum (fun n => abs_weightAtom_le lam n _) hs.abs (hsum.mul_left 2)
  have hτ : |τ| ≤ |τ₀| + |τ - τ₀| := by
    calc |τ| = |τ₀ + (τ - τ₀)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hM0 : 0 ≤ ∑' n : ℕ, 2 * (|lam n| / Real.sqrt n) :=
    tsum_nonneg fun n => by positivity
  have hg0 := abs_nonneg (gammaHardyPhaseRate 0)
  have hd0 := abs_nonneg (τ - τ₀)
  have ht0 := abs_nonneg τ₀
  calc |archFreq τ - ∑' n : ℕ, weightAtom lam n (τ / (2 * π))|
      ≤ |archFreq τ| + |∑' n : ℕ, weightAtom lam n (τ / (2 * π))| := abs_sub _ _
    _ ≤ (70 + 2 * |gammaHardyPhaseRate 0| + 2 * |τ|) + ∑' n : ℕ, 2 * (|lam n| / Real.sqrt n) :=
        add_le_add h1 h2
    _ ≤ _ := by nlinarith

/-- Truncation error of the symbol energy: `∫ |h|² S_N ≤ ∫ |h|² S_full + ε_N ∫ |h|²`. -/
theorem integral_weilAtomSymbol_le_full (hsum : Summable fun n => |lam n| / Real.sqrt n)
    {a : ℝ} {f : ℝ → ℂ} (hfd : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hint : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * fullAtomSymbol lam (τ / (2 * π))) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) ≤
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * fullAtomSymbol lam (τ / (2 * π))) +
        (2 * ∑' k : ℕ, |lam (k + (⌊Real.exp (2 * a)⌋₊ + 1))| /
          Real.sqrt (k + (⌊Real.exp (2 * a)⌋₊ + 1) : ℕ)) * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 := by
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  set ε := 2 * ∑' k : ℕ, |lam (k + (N + 1))| / Real.sqrt (k + (N + 1) : ℕ) with hε
  have hF := integrable_normSq_paperFT hfd hfs
  have hW := integrable_normSq_paperFT_mul_weilAtomSymbol_of hfd hfs lam
  have hmono : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam N (τ / (2 * π)) ≤
      ∫ τ : ℝ, (‖paperFT f τ‖ ^ 2 * fullAtomSymbol lam (τ / (2 * π)) + ε * ‖paperFT f τ‖ ^ 2) := by
    refine integral_mono hW (hint.add (hF.const_mul ε)) fun τ => ?_
    have h := (abs_le.mp (abs_weilAtomSymbol_sub_full_le hsum N (τ / (2 * π)))).2
    have h' : weilAtomSymbol lam N (τ / (2 * π)) ≤ fullAtomSymbol lam (τ / (2 * π)) + ε := by
      rw [hε]; linarith
    calc ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam N (τ / (2 * π))
        ≤ ‖paperFT f τ‖ ^ 2 * (fullAtomSymbol lam (τ / (2 * π)) + ε) :=
          mul_le_mul_of_nonneg_left h' (sq_nonneg _)
      _ = ‖paperFT f τ‖ ^ 2 * fullAtomSymbol lam (τ / (2 * π)) + ε * ‖paperFT f τ‖ ^ 2 := by ring
  rw [integral_add hint (hF.const_mul ε), integral_const_mul] at hmono
  exact hmono

/-- The concentration stage for summable weights: if the full symbol is `≤ -d₁/2` near `τ₀`
and the radical limit has size `≥ m/2` there, the spread tests violate Weil positivity. -/
theorem summable_violation_of_concentration (hsum : Summable fun n => |lam n| / Real.sqrt n)
    {τ₀ η m d₁ : ℝ} (hη0 : 0 < η) (hm0 : 0 < m) (hd₁0 : 0 < d₁)
    (hnear : ∀ τ : ℝ, |τ - τ₀| ≤ η →
      d₁ / 2 ≤ -1 * fullAtomSymbol lam (τ / (2 * π)) ∧ m / 2 ≤ ‖twistLimit 0 τ‖) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  set D : ℝ → ℝ := fun τ => fullAtomSymbol lam (τ / (2 * π)) with hDdef
  obtain ⟨Cκ, hCκ0, hCκ⟩ := exists_norm_paperFT_weilBumpC_le
  obtain ⟨C₆, hC₆0, hC₆⟩ := exists_superexp_le 6
  set E₀ := 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) with hE₀
  have hE0 : 0 ≤ E₀ := by
    have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
    have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
    rw [hE₀]; positivity
  set Aκ := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hAκ
  have hAκ0 : 0 ≤ Aκ := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  set B := (∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|)) * Aκ with hB
  have hB0 : 0 ≤ B := mul_nonneg (integral_nonneg fun _ => by positivity) hAκ0
  set Mlam := ∑' n : ℕ, 2 * (|lam n| / Real.sqrt n) with hMlam
  have hMlam0 : 0 ≤ Mlam := tsum_nonneg fun n => by positivity
  set CD := 70 + 2 * |gammaHardyPhaseRate 0| + 2 * |τ₀| + Mlam + 2 with hCD
  have hCD0 : 0 ≤ CD := by positivity
  have hcos : 0 < Real.cos (1 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
    by linarith [Real.pi_gt_three]⟩
  set c := (Real.cos (1 / 4) / 4) ^ 2 with hc
  have hc0 : 0 < c := by positivity
  set I₃ := ∫ τ : ℝ, 1 / (1 + |τ - τ₀|) ^ 3 with hI₃
  have hI₃0 : 0 ≤ I₃ := integral_nonneg fun _ => by positivity
  set L₀ := m / 4 * c with hL₀
  have hL₀0 : 0 < L₀ := by positivity
  set Ctail := |(-1 : ℝ)| * ((B ^ 3) ^ 2 * Cκ ^ 4 * CD / η ^ 4) * I₃ with hCtail
  have hCtail0 : 0 ≤ Ctail := by positivity
  set goal := d₁ / 2 * L₀ ^ 2 with hgoal
  have hgoal0 : 0 < goal := by positivity
  have t1 : Tendsto (fun S : ℝ => 3 * B ^ 2 * (E₀ * C₆ * Real.exp (1 / 4) * Aκ) / S) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have t3 : Tendsto (fun S : ℝ => Ctail / S ^ 3) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  obtain ⟨S, ⟨⟨hE2, hE4⟩, hE1⟩⟩ := ((t1.eventually (ge_mem_nhds (by linarith :
    (0 : ℝ) < m / 4))).and (t3.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < goal / 2)))).and
    (eventually_ge_atTop (max (max (Real.exp 1) (1 / η)) 1)) |>.exists
  have hSe : Real.exp 1 ≤ S := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hE1
  have hSη : 1 / η ≤ S := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hE1
  have hS1 : 1 ≤ S := le_trans (le_max_right _ _) hE1
  have hS0 : 0 < S := by linarith
  have h1S : 1 / S ≤ η := by
    rw [div_le_iff₀ hS0]; rw [div_le_iff₀ hη0] at hSη; linarith
  set R := Real.log S with hR
  have hR1 : 1 ≤ R := by rw [hR, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hSe
  have hR0 : 0 ≤ R := by linarith
  set f := twistTest 0 τ₀ R S with hf
  have hfd : ContDiff ℝ 2 f := contDiff_twistTest 0 τ₀ R S
  have hfs : tsupport f ⊆ Icc (-(3 * R + S)) (3 * R + S) := tsupport_twistTest hS0
  have hzero : ∀ z : ℂ, paperFT (weilRadicalTest R) z = 0 → paperFT f z = 0 := fun z hz => by
    rw [paperFT_twistTest_factor hS0, hz, zero_mul]
  have hp := hzero _ (paperFT_weilRadicalTest_half_I R)
  have hm' := hzero _ (paperFT_weilRadicalTest_neg_half_I R)
  have hεR : (∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) ≤
      E₀ * C₆ * Real.exp (1 / 4) / S := by
    refine (riemannPhiTail_bound_le E₀ C₆ hE₀ hC₆ hR1 (by norm_num)).trans (le_of_eq ?_)
    rw [show -(R - 1 / 4) = 1 / 4 + -R by ring, Real.exp_add, Real.exp_neg, hR,
      Real.exp_log hS0]
    field_simp
  have happrox : 3 * B ^ 2 * ((∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) * Aκ) ≤
      m / 4 := by
    refine le_trans ?_ hE2
    have : (∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) * Aκ ≤
        E₀ * C₆ * Real.exp (1 / 4) / S * Aκ := mul_le_mul_of_nonneg_right hεR hAκ0
    calc 3 * B ^ 2 * ((∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) * Aκ)
        ≤ 3 * B ^ 2 * (E₀ * C₆ * Real.exp (1 / 4) / S * Aκ) := by gcongr
      _ = 3 * B ^ 2 * (E₀ * C₆ * Real.exp (1 / 4) * Aκ) / S := by ring
  have hsed : SuperExpDecay f := ⟨hfd.continuous, fun c' =>
    (hfd.continuous.norm.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_abs_gt (a := 3 * R + S) fun u hu =>
        twistTest_eq_zero hS0 hu).norm.mul_right⟩
  have hHc : Continuous fun τ : ℝ => paperFT f τ :=
    hsed.differentiable_paperFT.continuous.comp Complex.continuous_ofReal
  have hHm : AEStronglyMeasurable (fun τ : ℝ => paperFT f τ) volume := hHc.aestronglyMeasurable
  have hF := integrable_normSq_paperFT hfd hfs
  have hDc : Continuous D := (continuous_fullAtomSymbol hsum).comp (by fun_prop)
  have hDbd : ∀ τ, |D τ| ≤ CD * (1 + |τ - τ₀|) := fun τ => abs_fullAtomSymbol_le hsum τ₀ τ
  have hint : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * D τ := by
    have hFA := integrable_normSq_paperFT_mul_arch hfd hfs
    have hcT : Continuous fun τ : ℝ => ∑' n : ℕ, weightAtom lam n (τ / (2 * π)) :=
      continuous_tsum (fun n => by unfold weightAtom; split_ifs <;> fun_prop) (hsum.mul_left 2)
        fun n τ => by rw [Real.norm_eq_abs]; exact abs_weightAtom_le lam n _
    have hT : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * ∑' n : ℕ, weightAtom lam n (τ / (2 * π)) := by
      refine (hF.mul_const Mlam).mono' ((hHc.norm.pow 2).mul hcT).aestronglyMeasurable
        (Eventually.of_forall fun τ => ?_)
      rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rw [Real.norm_eq_abs]
      have hs := summable_weightAtom hsum (τ / (2 * π))
      calc |∑' n : ℕ, weightAtom lam n (τ / (2 * π))| ≤ ∑' n : ℕ, |weightAtom lam n (τ / (2 * π))| := by
            have h := norm_tsum_le_tsum_norm (f := fun n => weightAtom lam n (τ / (2 * π)))
              (by simpa [Real.norm_eq_abs] using hs.abs)
            simpa [Real.norm_eq_abs] using h
        _ ≤ Mlam := Summable.tsum_le_tsum (fun n => abs_weightAtom_le lam n _) hs.abs (hsum.mul_left 2)
    refine (hFA.sub hT).congr (Eventually.of_forall fun τ => ?_)
    simp only [Pi.sub_apply, hDdef, fullAtomSymbol]; ring
  have hconc := concentrated_integral_lower (H := fun τ : ℝ => paperFT f τ) (D := D)
    (t := -1) (τ₀ := τ₀) (η := η) (S := S) (d₁ := d₁) (L := L₀ * S) (K₁ := B ^ 3) (Cκ := Cκ)
    (CD := CD) hS1 hη0 h1S hd₁0 (by positivity) hCD0 (by positivity) hCκ0 hHm hint
    (fun τ hτ => (hnear τ hτ).1)
    (fun τ hτ => by
      have := norm_paperFT_twistTest_real_ge (α := 0) (R := R) hS0 hτ
        (hnear τ (hτ.trans h1S)).2 happrox
      rw [hL₀]; convert this using 1; ring)
    (fun τ => norm_paperFT_twistTest_real_le hS0 hCκ τ)
    hDbd
  have hmain : d₁ / 2 * (2 / S * (L₀ * S) ^ 2) -
      |(-1 : ℝ)| * ((B ^ 3) ^ 2 * Cκ ^ 4 * CD / (S ^ 2 * η ^ 4)) * I₃ =
      2 * goal * S - Ctail / S ^ 2 := by
    rw [hgoal, hCtail]; field_simp
  rw [hmain] at hconc
  have hE4' : Ctail / S ^ 2 ≤ goal / 2 * S := by
    have := mul_le_mul_of_nonneg_right hE4 hS0.le
    calc Ctail / S ^ 2 = Ctail / S ^ 3 * S := by field_simp
      _ ≤ goal / 2 * S := this
  -- the energy of the symbol with all atoms
  have hDneg : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * D τ ≤ -(3 / 2 * goal * S) := by linarith
  -- choosing the level
  set MH := ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 with hMH
  have hMH0 : 0 ≤ MH := integral_nonneg fun _ => sq_nonneg _
  have hlev : Tendsto (fun a : ℝ => ⌊Real.exp (2 * a)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
  have htail := (tendsto_weight_tail lam).comp hlev
  have hgS : 0 < goal * S := by positivity
  have hev : ∀ᶠ a : ℝ in atTop,
      (2 * ∑' k : ℕ, |lam (k + (⌊Real.exp (2 * a)⌋₊ + 1))| /
        Real.sqrt (k + (⌊Real.exp (2 * a)⌋₊ + 1) : ℕ)) * MH ≤ goal * S := by
    have := (htail.mul_const MH)
    simp only [zero_mul] at this
    exact this.eventually (ge_mem_nhds hgS)
  obtain ⟨a, haS, ha⟩ := (hev.and (eventually_ge_atTop (3 * R + S))).exists
  have hfsa : tsupport f ⊆ Icc (-a) a := hfs.trans (Icc_subset_Icc (by linarith) ha)
  refine ⟨a, by linarith, f, hfd, hfsa, hp, hm', ?_⟩
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  set ε := 2 * ∑' k : ℕ, |lam (k + (N + 1))| / Real.sqrt (k + (N + 1) : ℕ) with hε
  have hW := integrable_normSq_paperFT_mul_weilAtomSymbol_of hfd hfsa lam
  have hmono := integral_weilAtomSymbol_le_full hsum hfd hfsa hint
  have hεMH : ε * MH ≤ goal * S := haS
  linarith

/-- **Summable prime weights are never Weil-positive.**  If `Σ_{n ≥ 2} |λ(n)| n^{-1/2} < ∞`,
then for some level `a` some polar-constrained `C²` test supported in `[-a, a]` has negative
finite-atom symbol energy with the archimedean term of `ζ`.  This covers `λ = 0` and every finite
truncation `Λ · 1_{n ≤ N}` of the von Mangoldt weights.

The full symbol `S = A - 2 Σ λ(n) n^{-1/2} cos(τ log n)` is negative somewhere, because on a test
supported in `[-17/50, 17/50]` (autocorrelation inside `(-log 2, log 2)`) the atoms are invisible
and `∫ |h|² A < 0`.  Concentrated radical tests at a negative point of `S` then violate
positivity, with the atom tail beyond the level made negligible by choosing the level last. -/
theorem summable_weights_weilAtomSymbol_not_nonneg (hsum : Summable fun n => |lam n| / Real.sqrt n) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  obtain ⟨τ₁, hτ₁⟩ := exists_fullAtomSymbol_neg hsum
  set D : ℝ → ℝ := fun τ => fullAtomSymbol lam (τ / (2 * π)) with hDdef
  have hDc : Continuous D := (continuous_fullAtomSymbol hsum).comp (by fun_prop)
  set d₁ := -1 * D τ₁ with hd₁
  have hd₁0 : 0 < d₁ := by simp only [hd₁, hDdef]; linarith
  have htD : Continuous (fun τ => -1 * D τ) := continuous_const.mul hDc
  obtain ⟨η₁, hη₁0, hη₁⟩ := Metric.continuousAt_iff.mp
    (htD.continuousAt (x := τ₁)) (d₁ / 2) (by linarith)
  have hnear₁ : ∀ τ : ℝ, |τ - τ₁| < η₁ → d₁ / 2 ≤ -1 * D τ := by
    intro τ hτ
    have := hη₁ (show dist τ τ₁ < η₁ by rwa [Real.dist_eq])
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).1
    linarith
  have hev := ((eventually_radicalLimit_shift_ne_zero 0 τ₁).and
    (nhdsWithin_le_nhds (Metric.ball_mem_nhds τ₁ (half_pos hη₁0))))
  obtain ⟨τ₀, h0, hball⟩ := hev.exists
  have hτ₀ : |τ₀ - τ₁| < η₁ / 2 := by rw [Real.dist_eq] at hball; exact hball
  have hlim0 : twistLimit 0 τ₀ ≠ 0 := by
    unfold twistLimit
    simp only [Complex.ofReal_zero, add_zero, neg_zero] at h0 ⊢
    exact mul_ne_zero (mul_ne_zero h0 h0) h0
  set m := ‖twistLimit 0 τ₀‖ with hm
  have hm0 : 0 < m := norm_pos_iff.mpr hlim0
  obtain ⟨η₂, hη₂0, hη₂⟩ := Metric.continuousAt_iff.mp
    ((continuous_twistLimit_real 0).continuousAt (x := τ₀)) (m / 2) (by linarith)
  set η := min (η₁ / 2) (η₂ / 2) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hnear : ∀ τ : ℝ, |τ - τ₀| ≤ η →
      d₁ / 2 ≤ -1 * fullAtomSymbol lam (τ / (2 * π)) ∧ m / 2 ≤ ‖twistLimit 0 τ‖ := by
    intro τ hτ
    constructor
    · refine hnear₁ τ ?_
      have : |τ - τ₁| ≤ |τ - τ₀| + |τ₀ - τ₁| := by
        calc |τ - τ₁| = |(τ - τ₀) + (τ₀ - τ₁)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      have := min_le_left (η₁ / 2) (η₂ / 2)
      linarith
    · have hd : dist τ τ₀ < η₂ := by
        rw [Real.dist_eq]; have := min_le_right (η₁ / 2) (η₂ / 2); linarith
      have := hη₂ hd
      rw [dist_eq_norm] at this
      have := norm_sub_norm_le (twistLimit 0 τ₀) (twistLimit 0 τ)
      rw [norm_sub_rev] at this
      linarith
  exact summable_violation_of_concentration hsum hη0 hm0 hd₁0 hnear

end SummableWeights

end RHTower

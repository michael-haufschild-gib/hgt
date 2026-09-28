import GaloisForLFunctions.RHTower.WeilSymbolMertensExpansion

/-!
# Weil positivity forces a nonpositive Mertens constant

Replace the von Mangoldt weights of the finite-atom Weil symbol of `ζ` by real weights `lam(n)`
whose deviation has a Mertens expansion

`∑_{2 ≤ n ≤ x} (lam(n) - Λ(n)) n^{-1/2} = A log x + B + o(1)`.

**Theorem** (`mertens_constant_nonpos_of_weilAtomSymbol_nonneg`).  If the symbol energy
`∫ |h_f(τ)|² S_lam(τ/2π) dτ` is nonnegative for every polar-constrained `C²` test at every level,
then `B ≤ 0`.  The slope `A` is unrestricted by this family of tests.

**Corollary** (`squareDeletedVonMangoldt_weilAtomSymbol_not_nonneg`).  Deleting the even prime
powers, i.e. `lam(n) = Λ(n)` off the perfect squares and `0` on them, gives
`A = -1/2`, `B = γ` (Mertens' theorem with Euler's constant), so Weil positivity fails for these
weights: some polar-constrained test has negative symbol energy.  This is a heavy perturbation
(`∑_p (log p)²/p = ∞`), outside the reach of pointwise cosine-series rigidity.

## Mechanism

The tests are `f_{R,S} = f_R ⋆ g(·/S)`, where `f_R = Φ_{≤R-1/4} ⋆ κ₂` is the truncated radical test
of `ζ` (Riemann's kernel `Φ` smoothed by a polar-free bump) and `g(x) = κ(x - 1/2) - κ(x + 1/2)` is a
mean-zero probe; the truncation level is `R = log S`.

* The zero side is super-exponentially small: `‖W(f_{R,S})‖ ≤ K S^{10} e^{-S}`
  (`exists_norm_W_mertensTest_log_le`), since every Weil summand carries the tail of `Φ` beyond
  `R - 1/4`, which is `≤ exp(-π S²/2)`, against the growth `e^{S}` of `ĝ_S` in the strip.
* The mass grows linearly: `‖f_{R,S}‖₂² ≥ cS` (`exists_integral_norm_sq_mertensTest_log_ge`), from
  `f_{R,S}(x) ≈ g(x/S) h_{f_R}(0)` and `|h_{f_R}(0)| ≥ |ξ(1/2)|/32`.
* The transform vanishes at `0` and at the poles `±i/2`.
* The Weil test `k = f ⋆ f̃` varies on the scale `S`: its even part has derivative bounded
  uniformly in `S` (`abs_deriv_weilTestEvenPart_mertensTest_le`).

The exact Mertens expansion of `WeilSymbolMertensExpansion` then bounds the symbol energy by
`2π(‖W‖ - 2B‖f‖₂² + O(E log T) + O(ηS))`, where `E` and `η` bound the Mertens remainder before
and after `T`; for `B > 0` this is `≤ -πBcS < 0` at a large scale.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

local notation "Φ" => riemannPhiKernel

/-! ### A mean-zero probe -/

/-- The probe `g(x) = κ(x - 1/2) - κ(x + 1/2)`: two unit bumps of opposite sign. -/
def mertensProbe (x : ℝ) : ℂ := weilBumpC (x - 1 / 2) - weilBumpC (x + 1 / 2)

theorem contDiff_mertensProbe : ContDiff ℝ 4 mertensProbe :=
  (contDiff_weilBumpC.comp (contDiff_id.sub contDiff_const)).sub
    (contDiff_weilBumpC.comp (contDiff_id.add contDiff_const))

theorem continuous_mertensProbe : Continuous mertensProbe := contDiff_mertensProbe.continuous

theorem mertensProbe_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : mertensProbe x = 0 := by
  have h1 : 1 / 4 ≤ |x - 1 / 2| := by
    have := abs_sub_abs_le_abs_sub x (1 / 2); rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    linarith
  have h2 : 1 / 4 ≤ |x + 1 / 2| := by
    have := abs_sub_abs_le_abs_sub x (-(1 / 2))
    rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), sub_neg_eq_add] at this
    linarith
  simp only [mertensProbe, weilBumpC_eq_zero h1, weilBumpC_eq_zero h2, sub_zero]

theorem hasCompactSupport_mertensProbe : HasCompactSupport mertensProbe :=
  hasCompactSupport_of_support_subset_abs (Λ := 1) fun u hu => by
    by_contra h; push Not at h; exact hu (mertensProbe_eq_zero h.le)

theorem norm_mertensProbe_le (x : ℝ) : ‖mertensProbe x‖ ≤ 1 := by
  simp only [mertensProbe, weilBumpC, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have h1 := weilBump.nonneg (x := x - 1 / 2)
  have h2 := weilBump.le_one (x := x - 1 / 2)
  have h3 := weilBump.nonneg (x := x + 1 / 2)
  have h4 := weilBump.le_one (x := x + 1 / 2)
  rw [abs_le]; constructor <;> linarith

theorem mertensProbe_half : mertensProbe (1 / 2) = 1 := by
  have h0 : weilBumpC 0 = 1 := by
    simp only [weilBumpC]
    rw [weilBump.one_of_mem_closedBall (by simp [weilBump]), Complex.ofReal_one]
  have h1 : weilBumpC 1 = 0 := weilBumpC_eq_zero (by norm_num)
  simp only [mertensProbe, sub_self]; norm_num [h0, h1]

theorem exists_lipschitz_mertensProbe :
    ∃ Lg : ℝ, 0 ≤ Lg ∧ ∀ x y : ℝ, ‖mertensProbe x - mertensProbe y‖ ≤ Lg * |x - y| := by
  obtain ⟨C, hC⟩ := contDiff_mertensProbe.lipschitzWith_of_hasCompactSupport
    hasCompactSupport_mertensProbe (by norm_num)
  refine ⟨C, C.2, fun x y => ?_⟩
  have := hC.dist_le_mul x y
  rwa [dist_eq_norm, Real.dist_eq] at this

theorem integral_mertensProbe_div {S : ℝ} (hS : S ≠ 0) :
    ∫ x : ℝ, mertensProbe (x / S) = 0 := by
  have hi : ∀ c : ℝ, Integrable (fun x : ℝ => weilBumpC (x / S + c)) := by
    intro c
    refine (contDiff_weilBumpC.continuous.comp (by fun_prop)).integrable_of_hasCompactSupport ?_
    refine hasCompactSupport_of_support_subset_abs (Λ := |S| * (|c| + 1)) fun u hu => ?_
    by_contra h; push Not at h
    refine hu (weilBumpC_eq_zero ?_)
    have hS0 : 0 < |S| := abs_pos.mpr hS
    have hdiv : |c| + 1 < |u / S| := by rw [abs_div, lt_div_iff₀ hS0]; linarith
    have := abs_sub_abs_le_abs_sub (u / S) (-c)
    rw [abs_neg, sub_neg_eq_add] at this
    linarith
  have hshift : ∫ x : ℝ, weilBumpC (x / S - 1 / 2) = ∫ x : ℝ, weilBumpC (x / S + 1 / 2) := by
    rw [← integral_add_right_eq_self (fun x : ℝ => weilBumpC (x / S - 1 / 2)) S]
    congr 1; funext x; congr 1; field_simp; ring
  simp only [mertensProbe]
  rw [integral_sub (by simpa [sub_eq_add_neg] using hi (-(1 / 2))) (hi (1 / 2)), hshift, sub_self]

theorem integral_mertensProbe_div_sq {S : ℝ} (hS : 0 < S) :
    ∫ x : ℝ, ‖mertensProbe (x / S)‖ ^ 2 = S * ∫ x : ℝ, ‖mertensProbe x‖ ^ 2 := by
  rw [Measure.integral_comp_div (fun y => ‖mertensProbe y‖ ^ 2) S, abs_of_pos hS, smul_eq_mul]

theorem integral_norm_mertensProbe_div {S : ℝ} (hS : 0 < S) :
    ∫ x : ℝ, ‖mertensProbe (x / S)‖ = S * ∫ x : ℝ, ‖mertensProbe x‖ := by
  rw [Measure.integral_comp_div (fun y => ‖mertensProbe y‖) S, abs_of_pos hS, smul_eq_mul]

theorem integral_norm_sq_mertensProbe_pos : 0 < ∫ x : ℝ, ‖mertensProbe x‖ ^ 2 := by
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1 / 2)
    (continuous_mertensProbe.norm.pow 2)
    (hasCompactSupport_of_support_subset_abs (Λ := 1) fun u hu => by
      by_contra h; push Not at h; exact hu (by simp [mertensProbe_eq_zero h.le]))
    (fun _ => by positivity) ?_
  rw [mertensProbe_half]; norm_num

/-! ### Uniform bounds for the truncated radical tests -/

/-- `‖f_L‖₁ ≤ ‖Φ‖₁ ‖κ₂‖₁` uniformly in the truncation level. -/
theorem integral_norm_weilRadicalTest_le (L : ℝ) :
    ∫ x : ℝ, ‖weilRadicalTest L x‖ ≤
      (∫ u : ℝ, ‖Φ u‖) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ := by
  set h₀ : ℝ → ℝ := convolution (fun u => ‖Φ u‖) (fun u => ‖weilBumpPolarFree u‖)
    (ContinuousLinearMap.mul ℝ ℝ) volume with hh₀
  have hΦi : Integrable (fun u => ‖Φ u‖) := integrable_riemannPhiKernel.norm
  have hκi : Integrable weilBumpPolarFree :=
    contDiff_weilBumpPolarFree.continuous.integrable_of_hasCompactSupport
      hasCompactSupport_weilBumpPolarFree
  have hh₀i : Integrable h₀ := hΦi.integrable_convolution _ hκi.norm
  have hh₀int : ∫ x, h₀ x = (∫ u : ℝ, ‖Φ u‖) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ := by
    rw [hh₀, integral_convolution _ hΦi hκi.norm]; rfl
  have hpt : ∀ x, ‖weilRadicalTest L x‖ ≤ h₀ x := by
    intro x
    simp only [weilRadicalTest, hh₀, convolution_def, ContinuousLinearMap.mul_apply']
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun _ => norm_nonneg _) ?_ (Eventually.of_forall fun t => ?_))
    · obtain ⟨B, hB⟩ := contDiff_weilBumpPolarFree.continuous.norm.bounded_above_of_compact_support
        hasCompactSupport_weilBumpPolarFree.norm
      refine Integrable.mono' (hΦi.mul_const B) ?_ (Eventually.of_forall fun t => ?_)
      · exact (continuous_riemannPhiKernel.norm.mul
          (contDiff_weilBumpPolarFree.continuous.norm.comp (by fun_prop))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (by simpa using hB (x - t)) (norm_nonneg _)
    · show ‖riemannPhiCore L t * weilBumpPolarFree (x - t)‖ ≤ ‖Φ t‖ * ‖weilBumpPolarFree (x - t)‖
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      unfold riemannPhiCore indicator; split_ifs <;> simp
  have hfi : Integrable (weilRadicalTest L) :=
    (contDiff_weilRadicalTest L).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_of_support_subset_abs (Λ := L) fun u hu => by
        by_contra h; push Not at h; exact hu (weilRadicalTest_eq_zero h))
  rw [← hh₀int]
  exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hh₀i
    (Eventually.of_forall hpt)

theorem integral_weilBump_ge : 1 / 4 ≤ ∫ u : ℝ, weilBump u := by
  have hint : Integrable (fun u : ℝ => weilBump u) :=
    (weilBump.contDiff (n := 0)).continuous.integrable_of_hasCompactSupport weilBump.hasCompactSupport
  have hnn : 0 ≤ᵐ[volume] (fun u : ℝ => weilBump u) := Eventually.of_forall fun u => weilBump.nonneg
  refine le_trans ?_ (setIntegral_le_integral (s := Icc (-(1 / 8)) (1 / 8)) hint hnn)
  have hlow : ∀ u ∈ Icc (-(1 / 8) : ℝ) (1 / 8), (1 : ℝ) ≤ weilBump u := by
    intro u hu
    rw [weilBump.one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      change |u| ≤ 1 / 8
      exact abs_le.mpr ⟨hu.1, hu.2⟩)]
  calc (1 / 4 : ℝ) = ∫ u in Icc (-(1 / 8) : ℝ) (1 / 8), (1 : ℝ) := by
        rw [setIntegral_const]
        simp only [Measure.real, Real.volume_Icc, smul_eq_mul]
        rw [ENNReal.toReal_ofReal (by norm_num)]; ring
    _ ≤ ∫ u in Icc (-(1 / 8) : ℝ) (1 / 8), weilBump u :=
        setIntegral_mono_on (integrableOn_const (by simp) (by simp)) hint.integrableOn
          measurableSet_Icc hlow

theorem norm_paperFT_weilBumpPolarFree_zero_ge :
    1 / 16 ≤ ‖paperFT weilBumpPolarFree 0‖ := by
  rw [paperFT_weilBumpPolarFree]
  have h0 : paperFT weilBumpC 0 = ((∫ u : ℝ, weilBump u : ℝ) : ℂ) := by
    unfold paperFT weilBumpC
    rw [← integral_complex_ofReal]; congr 1; funext u; simp
  have h := integral_weilBump_ge
  rw [h0, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have : ‖-((0 : ℂ) ^ 2 + 1 / 4)‖ = 1 / 4 := by norm_num
  rw [this]; nlinarith

theorem xi_half_ne_zero : xi (1 / 2) ≠ 0 := by
  intro h
  have h1 := (xi_eq_zero_iff (s := 1 / 2) (by norm_num) (by norm_num)).mp h
  have h2 := riemannZeta_real_strip_ne_zero (σ := 1 / 2) (by norm_num) (by norm_num)
  exact h2 (by simpa using h1)

/-- The truncated radical tests have mass bounded below at the origin, uniformly in large
truncation levels: `|h_{f_L}(0)| ≥ |ξ(1/2)|/32`. -/
theorem exists_norm_paperFT_weilRadicalTest_zero_ge :
    ∃ L₁ : ℝ, 1 ≤ L₁ ∧ ∀ L : ℝ, L₁ ≤ L →
      ‖xi (1 / 2)‖ / 32 ≤ ‖paperFT (weilRadicalTest L) 0‖ := by
  obtain ⟨C₆, hC₆0, hC₆⟩ := exists_superexp_le 6
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℝ, E₀ = 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) :=
    ⟨_, rfl⟩
  have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
  have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
  have hE0 : 0 ≤ E₀ := by rw [hE₀]; positivity
  have hξ : 0 < ‖xi (1 / 2)‖ := norm_pos_iff.mpr xi_half_ne_zero
  have hev : ∀ᶠ L in atTop, E₀ * C₆ * Real.exp (-(L - 1 / 4)) ≤ ‖xi (1 / 2)‖ / 2 := by
    have ht : Tendsto (fun L : ℝ => E₀ * C₆ * Real.exp (-(L - 1 / 4))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_atTop_add_const_right _ (-(1 / 4)) tendsto_id))
      simpa [neg_add, sub_eq_add_neg, Function.comp_def] using this.const_mul (E₀ * C₆)
    exact ht.eventually (ge_mem_nhds (by linarith))
  obtain ⟨L₁, hL₁⟩ := (hev.and (eventually_ge_atTop 1)).exists_forall_of_atTop
  refine ⟨max L₁ 1, le_max_right _ _, fun L hL => ?_⟩
  obtain ⟨hsmall, hL1⟩ := hL₁ L (le_of_max_le_left hL)
  have htail : ‖paperFT (riemannPhiTail L) 0‖ ≤ ‖xi (1 / 2)‖ / 2 := by
    refine (norm_paperFT_riemannPhiTail_le (b := 1 / 2) (by norm_num) (by simp)).trans ?_
    exact (riemannPhiTail_bound_le E₀ C₆ hE₀ hC₆ hL1 (by norm_num)).trans hsmall
  have hcore : ‖xi (1 / 2)‖ / 2 ≤ ‖paperFT (riemannPhiCore L) 0‖ := by
    rw [paperFT_riemannPhiCore_eq, mul_zero, add_zero, riemannPhiTransform_eq_xi]
    have := norm_sub_norm_le (xi (1 / 2)) (paperFT (riemannPhiTail L) 0)
    linarith
  rw [paperFT_weilRadicalTest, norm_mul]
  have hb := norm_paperFT_weilBumpPolarFree_zero_ge
  calc ‖xi (1 / 2)‖ / 32 = ‖xi (1 / 2)‖ / 2 * (1 / 16) := by ring
    _ ≤ _ := mul_le_mul hcore hb (by norm_num) (norm_nonneg _)

/-! ### The spread near-radical tests -/

theorem hasCompactSupport_norm_sq {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => ‖f x‖ ^ 2) :=
  hf.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)

theorem hasCompactSupport_weilRadicalTest (R : ℝ) : HasCompactSupport (weilRadicalTest R) :=
  hasCompactSupport_of_support_subset_abs (Λ := R) fun u hu => by
    by_contra h; push Not at h; exact hu (weilRadicalTest_eq_zero h)

theorem integrable_weilRadicalTest (R : ℝ) : Integrable (weilRadicalTest R) :=
  (contDiff_weilRadicalTest R).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_weilRadicalTest R)

theorem mertensProbe_div_eq_zero {S x : ℝ} (hS : 0 < S) (hx : S ≤ |x|) :
    mertensProbe (x / S) = 0 :=
  mertensProbe_eq_zero (by rw [abs_div, abs_of_pos hS, le_div_iff₀ hS]; linarith)

theorem hasCompactSupport_mertensProbe_div {S : ℝ} (hS : 0 < S) :
    HasCompactSupport (fun x => mertensProbe (x / S)) :=
  hasCompactSupport_of_support_subset_abs (Λ := S) fun u hu => by
    by_contra h; push Not at h; exact hu (mertensProbe_div_eq_zero hS h.le)

/-- `f_{R,S} = f_R ⋆ g(·/S)`: the truncated radical test spread over the scale `S`. -/
def mertensTest (R S : ℝ) : ℝ → ℂ :=
  convolution (weilRadicalTest R) (fun x => mertensProbe (x / S)) (ContinuousLinearMap.mul ℝ ℂ)
    volume

theorem contDiff_mertensTest (R S : ℝ) : ContDiff ℝ 2 (mertensTest R S) :=
  (hasCompactSupport_weilRadicalTest R).contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ)
    (n := 2) (contDiff_weilRadicalTest R)
    (continuous_mertensProbe.comp (continuous_id.div_const S)).locallyIntegrable

theorem mertensTest_apply (R S x : ℝ) :
    mertensTest R S x = ∫ t : ℝ, weilRadicalTest R t * mertensProbe ((x - t) / S) := by
  simp only [mertensTest, convolution_def, ContinuousLinearMap.mul_apply']

theorem mertensTest_eq_zero {R S x : ℝ} (hS : 0 < S) (hx : R + S < |x|) :
    mertensTest R S x = 0 := by
  rw [mertensTest_apply]
  have : ∀ t, weilRadicalTest R t * mertensProbe ((x - t) / S) = 0 := by
    intro t
    by_cases ht : R < |t|
    · rw [weilRadicalTest_eq_zero ht, zero_mul]
    · push Not at ht
      have h1 : S ≤ |x - t| := by have := abs_sub_abs_le_abs_sub x t; linarith
      rw [mertensProbe_div_eq_zero hS h1, mul_zero]
  simp [this]

theorem tsupport_mertensTest {R S : ℝ} (hS : 0 < S) :
    tsupport (mertensTest R S) ⊆ Icc (-(R + S)) (R + S) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have h : ¬ R + S < |x| := fun h => hx (mertensTest_eq_zero hS h)
  push Not at h
  exact ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩

theorem hasCompactSupport_mertensTest {R S : ℝ} (hS : 0 < S) :
    HasCompactSupport (mertensTest R S) :=
  hasCompactSupport_of_support_subset_abs (Λ := R + S) fun u hu => by
    by_contra h; push Not at h; exact hu (mertensTest_eq_zero hS h)

theorem paperFT_mertensTest {R S : ℝ} (hS : 0 < S) (z : ℂ) :
    paperFT (mertensTest R S) z =
      paperFT (weilRadicalTest R) z * paperFT (fun x => mertensProbe (x / S)) z := by
  apply paperFT_convolution
  · exact ((contDiff_weilRadicalTest R).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_weilRadicalTest R).mul_right
  · exact ((continuous_mertensProbe.comp (continuous_id.div_const S)).mul
      (by fun_prop)).integrable_of_hasCompactSupport (hasCompactSupport_mertensProbe_div hS).mul_right

theorem paperFT_mertensTest_half_I {R S : ℝ} (hS : 0 < S) :
    paperFT (mertensTest R S) (I / 2) = 0 := by
  rw [paperFT_mertensTest hS, paperFT_weilRadicalTest_half_I, zero_mul]

theorem paperFT_mertensTest_neg_half_I {R S : ℝ} (hS : 0 < S) :
    paperFT (mertensTest R S) (-(I / 2)) = 0 := by
  rw [paperFT_mertensTest hS, paperFT_weilRadicalTest_neg_half_I, zero_mul]

theorem paperFT_mertensTest_zero {R S : ℝ} (hS : 0 < S) : paperFT (mertensTest R S) 0 = 0 := by
  rw [paperFT_mertensTest hS]
  have : paperFT (fun x => mertensProbe (x / S)) 0 = 0 := by
    unfold paperFT
    simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
    exact integral_mertensProbe_div hS.ne'
  rw [this, mul_zero]

theorem integrable_weilRadicalTest_mul_probe (R S y : ℝ) :
    Integrable (fun t => weilRadicalTest R t * mertensProbe ((y - t) / S)) :=
  ((contDiff_weilRadicalTest R).continuous.mul (continuous_mertensProbe.comp (by fun_prop)))
    |>.integrable_of_hasCompactSupport (hasCompactSupport_weilRadicalTest R).mul_right

theorem norm_mertensTest_le (R S x : ℝ) :
    ‖mertensTest R S x‖ ≤ ∫ t : ℝ, ‖weilRadicalTest R t‖ := by
  rw [mertensTest_apply]
  refine norm_integral_le_of_norm_le (integrable_weilRadicalTest R).norm
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_mertensProbe_le _)

/-- The spread test is Lipschitz with constant `‖f_R‖₁ L_g / S`. -/
theorem norm_mertensTest_sub_le {R S Lg : ℝ} (hS : 0 < S)
    (hLg : ∀ x y : ℝ, ‖mertensProbe x - mertensProbe y‖ ≤ Lg * |x - y|) (x y : ℝ) :
    ‖mertensTest R S x - mertensTest R S y‖ ≤
      (∫ t : ℝ, ‖weilRadicalTest R t‖) * (Lg * |x - y| / S) := by
  rw [mertensTest_apply, mertensTest_apply, ← integral_sub
    (integrable_weilRadicalTest_mul_probe R S x) (integrable_weilRadicalTest_mul_probe R S y),
    ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((integrable_weilRadicalTest R).norm.mul_const _)
    (Eventually.of_forall fun t => ?_)
  rw [← mul_sub, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (hLg _ _).trans (le_of_eq ?_)
  rw [show (x - t) / S - (y - t) / S = (x - y) / S by ring, abs_div, abs_of_pos hS]
  ring

/-- The spread test is the probe times the mass of `f_R`, up to `L_g R ‖f_R‖₁ / S`. -/
theorem norm_mertensTest_sub_probe_le {R S Lg : ℝ} (hS : 0 < S) (hLg0 : 0 ≤ Lg)
    (hLg : ∀ x y : ℝ, ‖mertensProbe x - mertensProbe y‖ ≤ Lg * |x - y|) (x : ℝ) :
    ‖mertensTest R S x - mertensProbe (x / S) * paperFT (weilRadicalTest R) 0‖ ≤
      Lg * R * (∫ t : ℝ, ‖weilRadicalTest R t‖) / S := by
  have hm : paperFT (weilRadicalTest R) 0 = ∫ t : ℝ, weilRadicalTest R t := by
    unfold paperFT; simp
  have hint2 : Integrable (fun t => weilRadicalTest R t * mertensProbe (x / S)) :=
    (integrable_weilRadicalTest R).mul_const _
  rw [hm, ← integral_const_mul, mertensTest_apply, ← integral_sub
    (integrable_weilRadicalTest_mul_probe R S x) (by simpa [mul_comm] using hint2)]
  rw [show Lg * R * (∫ t : ℝ, ‖weilRadicalTest R t‖) / S =
    ∫ t : ℝ, ‖weilRadicalTest R t‖ * (Lg * R / S) by rw [integral_mul_const]; ring]
  refine norm_integral_le_of_norm_le ((integrable_weilRadicalTest R).norm.mul_const _)
    (Eventually.of_forall fun t => ?_)
  by_cases ht : R < |t|
  · rw [weilRadicalTest_eq_zero ht]; simp
  push Not at ht
  rw [show weilRadicalTest R t * mertensProbe ((x - t) / S) -
      mertensProbe (x / S) * weilRadicalTest R t =
      weilRadicalTest R t * (mertensProbe ((x - t) / S) - mertensProbe (x / S)) by ring, norm_mul]
  refine mul_le_mul_of_nonneg_left ((hLg _ _).trans ?_) (norm_nonneg _)
  rw [show (x - t) / S - x / S = -t / S by ring, abs_div, abs_neg, abs_of_pos hS]
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ht hS.le) hLg0

/-- **Mass of the spread test.**  `‖f_{R,S}‖₂² ≥ ½ |h_{f_R}(0)|² S ‖g‖₂² - 2(R+S)(L_g R ‖f_R‖₁/S)²`. -/
theorem integral_norm_sq_mertensTest_ge {R S Lg : ℝ} (hR : 0 ≤ R) (hS : 0 < S) (hLg0 : 0 ≤ Lg)
    (hLg : ∀ x y : ℝ, ‖mertensProbe x - mertensProbe y‖ ≤ Lg * |x - y|) :
    1 / 2 * ‖paperFT (weilRadicalTest R) 0‖ ^ 2 * (S * ∫ x : ℝ, ‖mertensProbe x‖ ^ 2) -
        2 * (R + S) * (Lg * R * (∫ t : ℝ, ‖weilRadicalTest R t‖) / S) ^ 2 ≤
      ∫ x : ℝ, ‖mertensTest R S x‖ ^ 2 := by
  set m := paperFT (weilRadicalTest R) 0 with hm
  set δ := Lg * R * (∫ t : ℝ, ‖weilRadicalTest R t‖) / S with hδ
  set r : ℝ → ℂ := fun x => mertensTest R S x - mertensProbe (x / S) * m with hr
  have hδ0 : 0 ≤ δ := by
    rw [hδ]; exact div_nonneg (mul_nonneg (mul_nonneg hLg0 hR)
      (integral_nonneg fun _ => norm_nonneg _)) hS.le
  have hfc := (contDiff_mertensTest R S).continuous
  have hgc : Continuous (fun x : ℝ => mertensProbe (x / S)) :=
    continuous_mertensProbe.comp (continuous_id.div_const S)
  have hrc : Continuous r := hfc.sub (hgc.mul continuous_const)
  have hrz : ∀ x, R + S < |x| → r x = 0 := by
    intro x hx
    simp only [hr, mertensTest_eq_zero hS hx,
      mertensProbe_div_eq_zero hS (by linarith : S ≤ |x|), zero_mul, sub_zero]
  have hrcs : HasCompactSupport r := hasCompactSupport_of_support_subset_abs (Λ := R + S)
    fun u hu => by by_contra h; push Not at h; exact hu (hrz u h)
  have hi_f : Integrable (fun x => ‖mertensTest R S x‖ ^ 2) :=
    (hfc.norm.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_norm_sq (hasCompactSupport_mertensTest hS))
  have hi_r : Integrable (fun x => ‖r x‖ ^ 2) :=
    (hrc.norm.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_norm_sq hrcs)
  have hi_g : Integrable (fun x => ‖mertensProbe (x / S) * m‖ ^ 2) :=
    ((hgc.mul continuous_const).norm.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_norm_sq (hasCompactSupport_mertensProbe_div hS).mul_right)
  -- pointwise: `‖g m‖² ≤ 2‖f‖² + 2‖r‖²`
  have hpt : ∀ x, 1 / 2 * ‖mertensProbe (x / S) * m‖ ^ 2 - ‖r x‖ ^ 2 ≤
      ‖mertensTest R S x‖ ^ 2 := by
    intro x
    have htri : ‖mertensProbe (x / S) * m‖ ≤ ‖mertensTest R S x‖ + ‖r x‖ := by
      have : mertensProbe (x / S) * m = mertensTest R S x - r x := by simp [hr]
      rw [this]; exact norm_sub_le _ _
    nlinarith [norm_nonneg (mertensProbe (x / S) * m), norm_nonneg (mertensTest R S x),
      norm_nonneg (r x), sq_nonneg (‖mertensTest R S x‖ - ‖r x‖)]
  have hmain : ∫ x : ℝ, ‖mertensProbe (x / S) * m‖ ^ 2 =
      ‖m‖ ^ 2 * (S * ∫ x : ℝ, ‖mertensProbe x‖ ^ 2) := by
    rw [← integral_mertensProbe_div_sq hS, ← integral_const_mul]
    congr 1; funext x; rw [norm_mul]; ring
  have hrbound : ∫ x : ℝ, ‖r x‖ ^ 2 ≤ 2 * (R + S) * δ ^ 2 := by
    have hset : ∫ x : ℝ, ‖r x‖ ^ 2 = ∫ x in Icc (-(R + S)) (R + S), ‖r x‖ ^ 2 := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
      have : R + S < |x| := by
        by_contra h; push Not at h; exact hx ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩
      rw [hrz x this]; simp
    rw [hset]
    have hle : ∀ x ∈ Icc (-(R + S)) (R + S), ‖r x‖ ^ 2 ≤ δ ^ 2 := by
      intro x _
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_mertensTest_sub_probe_le hS hLg0 hLg x) 2
    calc ∫ x in Icc (-(R + S)) (R + S), ‖r x‖ ^ 2
        ≤ ∫ x in Icc (-(R + S)) (R + S), δ ^ 2 :=
          setIntegral_mono_on hi_r.integrableOn (integrableOn_const (by simp) (by simp))
            measurableSet_Icc hle
      _ = 2 * (R + S) * δ ^ 2 := by
          rw [setIntegral_const]
          simp only [Measure.real, Real.volume_Icc, smul_eq_mul]
          rw [ENNReal.toReal_ofReal (by linarith)]; ring
  have hint := integral_mono (((hi_g.const_mul (1 / 2)).sub hi_r)) hi_f hpt
  simp only [Pi.sub_apply] at hint
  rw [integral_sub (hi_g.const_mul _) hi_r, integral_const_mul, hmain] at hint
  linarith

/-! ### Lipschitz control of the Weil test -/

theorem weilTest_apply_eq (f : ℝ → ℂ) (u : ℝ) :
    EF.weilTest f f u = ∫ t : ℝ, f t * conj (f (t - u)) := by
  unfold EF.weilTest
  rw [convolution_def]
  congr 1; funext t
  simp only [ContinuousLinearMap.mul_apply', EF.tilde, neg_sub]

/-- If `f` is continuous, compactly supported and `M`-Lipschitz, the Weil test `f ⋆ f̃` is
`‖f‖₁ M`-Lipschitz. -/
theorem norm_weilTest_sub_le {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {M : ℝ} (hM : ∀ x y : ℝ, ‖f x - f y‖ ≤ M * |x - y|) (u v : ℝ) :
    ‖EF.weilTest f f u - EF.weilTest f f v‖ ≤ (∫ t : ℝ, ‖f t‖) * (M * |u - v|) := by
  have hi : ∀ w : ℝ, Integrable (fun t => f t * conj (f (t - w))) := fun w =>
    (hf.mul (Complex.continuous_conj.comp (hf.comp (continuous_id.sub continuous_const))))
      |>.integrable_of_hasCompactSupport hfc.mul_right
  rw [weilTest_apply_eq, weilTest_apply_eq, ← integral_sub (hi u) (hi v), ← integral_mul_const]
  refine norm_integral_le_of_norm_le
    ((hf.norm.integrable_of_hasCompactSupport hfc.norm).mul_const _)
    (Eventually.of_forall fun t => ?_)
  rw [← mul_sub, norm_mul, ← map_sub, RCLike.norm_conj]
  refine mul_le_mul_of_nonneg_left ((hM _ _).trans (le_of_eq ?_)) (norm_nonneg _)
  rw [show t - u - (t - v) = -(u - v) by ring, abs_neg]

/-- A derivative bound for the even part `φ = Re(k + k(-·))` from a Lipschitz bound on `k`. -/
theorem abs_deriv_weilTestEvenPart_le {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x y : ℝ, ‖f x - f y‖ ≤ M * |x - y|) (u : ℝ) :
    |deriv (weilTestEvenPart f) u| ≤ 2 * (∫ t : ℝ, ‖f t‖) * M := by
  have hK0 : 0 ≤ 2 * (∫ t : ℝ, ‖f t‖) * M :=
    mul_nonneg (mul_nonneg (by norm_num) (integral_nonneg fun _ => norm_nonneg _)) hM0
  have hlip : LipschitzWith ⟨2 * (∫ t : ℝ, ‖f t‖) * M, hK0⟩ (weilTestEvenPart f) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq]
    change _ ≤ (2 * (∫ t : ℝ, ‖f t‖) * M) * |x - y|
    unfold weilTestEvenPart
    rw [← Complex.sub_re]
    refine (Complex.abs_re_le_norm _).trans ?_
    have h1 := norm_weilTest_sub_le hf hfc hM x y
    have h2 := norm_weilTest_sub_le hf hfc hM (-x) (-y)
    rw [show -x - -y = -(x - y) by ring, abs_neg] at h2
    calc ‖EF.weilTest f f x + EF.weilTest f f (-x) - (EF.weilTest f f y + EF.weilTest f f (-y))‖
        = ‖(EF.weilTest f f x - EF.weilTest f f y) +
            (EF.weilTest f f (-x) - EF.weilTest f f (-y))‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring
  have := norm_deriv_le_of_lipschitz (x₀ := u) hlip
  rw [Real.norm_eq_abs] at this
  exact this

/-! ### The zero side of the spread test -/

theorem norm_paperFT_mertensProbe_div_le {S : ℝ} (hS : 0 < S) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT (fun x => mertensProbe (x / S)) z‖ ≤
      Real.exp (S / 2) * (S * ∫ x : ℝ, ‖mertensProbe x‖) := by
  have hi : Integrable (fun x => mertensProbe (x / S)) :=
    (continuous_mertensProbe.comp (continuous_id.div_const S)).integrable_of_hasCompactSupport
      (hasCompactSupport_mertensProbe_div hS)
  have h := norm_paperFT_le (Λ := S) hi (fun u hu => by
    by_contra h; push Not at h; exact hu (mertensProbe_div_eq_zero hS h.le)) z
  rw [integral_norm_mertensProbe_div hS] at h
  refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
    (mul_nonneg hS.le (integral_nonneg fun _ => norm_nonneg _)))
  nlinarith [abs_nonneg z.im]

/-- **Weil energy of the spread test.**  Each Weil summand of `f_{R,S}` is the summand of `f_R`
times two values of `ĝ_S`, each bounded by `e^{S/2} S ‖g‖₁` in the critical strip; the summands of
`f_R` carry the tail of Riemann's kernel beyond `R - 1/4` and the `C²` decay `(1 + |γ|)^{-2}`. -/
theorem norm_W_mertensTest_le {K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (hK : ∀ L : ℝ, 0 ≤ L →
      4 * ((∫ u : ℝ, ‖weilRadicalTest L u‖) + ∫ u : ℝ, ‖deriv (deriv (weilRadicalTest L)) u‖)
        ≤ L * K₀)
    {R S : ℝ} (hR : 0 ≤ R) (hS : 0 < S) :
    ‖zetaZeroConfig.W (mertensTest R S) (mertensTest R S)‖ ≤
      (5 / 4) * (∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) *
      ((Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) *
        (∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|))) *
      (Real.exp (R / 2) * (R * K₀)) *
      (Real.exp (S / 2) * (S * ∫ x : ℝ, ‖mertensProbe x‖)) ^ 2 := by
  set A : ℝ := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hA
  set ε : ℝ := ∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|) with hε
  set D : ℝ := Real.exp (R / 2) * (R * K₀) with hD
  set G : ℝ := Real.exp (S / 2) * (S * ∫ x : ℝ, ‖mertensProbe x‖) with hG
  have hA0 : 0 ≤ A := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  have hε0 : 0 ≤ ε := integral_nonneg fun _ => by positivity
  have hD0 : 0 ≤ D := by positivity
  have hG0 : 0 ≤ G := mul_nonneg (Real.exp_pos _).le
    (mul_nonneg hS.le (integral_nonneg fun _ => norm_nonneg _))
  have hsum : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    have := WeilEF.zero_sum_inv_sq zetaSeam
    simpa [zetaZeroConfig] using this
  have hpt : ∀ ρ : zetaZeroConfig.carrier,
      ‖zetaZeroConfig.Wsummand (mertensTest R S) (mertensTest R S) ρ‖ ≤
        (5 / 4) * (A * ε * D * G ^ 2) *
          ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ
    have hmem := ρ.2
    have hstrip := zetaZeroConfig.strip ρ hmem
    have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := hmem
      exact ⟨h.2.1, h.2.2⟩
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact hIm
    obtain ⟨hc1, -⟩ := paperFT_riemannPhiCore_at_zero hmem R
    have hv1 : ‖paperFT (weilRadicalTest R) (gammaOf ρ)‖ ≤ ε * A := by
      rw [paperFT_weilRadicalTest, hc1, norm_mul, norm_neg]
      exact mul_le_mul (norm_paperFT_riemannPhiTail_le (by norm_num) hIm)
        (norm_paperFT_weilBumpPolarFree_le (by linarith)) (norm_nonneg _) hε0
    have hv2 : ‖paperFT (weilRadicalTest R) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤
        D * (1 / (1 + |(ρ : ℂ).im|) ^ 2) := by
      have h := norm_paperFT_le_decay (contDiff_weilRadicalTest R)
        (fun u hu => by
          by_contra h; push Not at h; exact hu (weilRadicalTest_eq_zero h))
        ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))
      have hre : ((starRingEnd ℂ) (gammaOf (ρ : ℂ))).re = (ρ : ℂ).im := by
        rw [Complex.conj_re, WeilEF.gammaOf_re]
      rw [hre] at h
      refine h.trans ?_
      have he : Real.exp (|((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| * R) ≤ Real.exp (R / 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hden : 0 < (1 + |(ρ : ℂ).im|) ^ 2 := by positivity
      rw [hD, div_eq_mul_one_div, mul_assoc]
      rw [show Real.exp (R / 2) * (R * K₀) * (1 / (1 + |(ρ : ℂ).im|) ^ 2) =
        Real.exp (R / 2) * (R * K₀ * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) by ring]
      exact mul_le_mul he (mul_le_mul_of_nonneg_right (hK R hR) (by positivity))
        (by positivity) (Real.exp_pos _).le
    have hg1 := norm_paperFT_mertensProbe_div_le hS hIm
    have hg2 := norm_paperFT_mertensProbe_div_le hS hIm'
    have hq := one_div_one_add_abs_im_sq_le hstrip
    unfold ZeroConfig.Wsummand
    rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj, paperFT_mertensTest hS,
      paperFT_mertensTest hS, norm_mul, norm_mul]
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    calc (zetaZeroConfig.mult ρ : ℝ) *
          (‖paperFT (weilRadicalTest R) (gammaOf ρ)‖ *
            ‖paperFT (fun x => mertensProbe (x / S)) (gammaOf ρ)‖) *
          (‖paperFT (weilRadicalTest R) ((starRingEnd ℂ) (gammaOf ρ))‖ *
            ‖paperFT (fun x => mertensProbe (x / S)) ((starRingEnd ℂ) (gammaOf ρ))‖)
        ≤ (zetaZeroConfig.mult ρ : ℝ) * ((ε * A) * G) *
            ((D * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) * G) := by
          gcongr
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) * ((ε * A) * G) *
            ((D * ((5 / 4) * (1 / (1 + Complex.normSq (gammaOf ρ))))) * G) := by
          gcongr
      _ = (5 / 4) * (A * ε * D * G ^ 2) *
            ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by ring
  have hsum' : Summable (fun ρ : zetaZeroConfig.carrier =>
      ‖zetaZeroConfig.Wsummand (mertensTest R S) (mertensTest R S) ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hsum.mul_left _)
  unfold ZeroConfig.W
  refine (norm_tsum_le_tsum_norm hsum').trans ?_
  refine (Summable.tsum_le_tsum hpt hsum' (hsum.mul_left _)).trans (le_of_eq ?_)
  rw [tsum_mul_left]; ring

/-! ### Uniform constants of the spread family -/

theorem integral_norm_mertensTest_le {R S : ℝ} (hR : 0 ≤ R) (hS : 0 < S) :
    ∫ x : ℝ, ‖mertensTest R S x‖ ≤ 2 * (R + S) * ∫ t : ℝ, ‖weilRadicalTest R t‖ := by
  have hset : ∫ x : ℝ, ‖mertensTest R S x‖ =
      ∫ x in Icc (-(R + S)) (R + S), ‖mertensTest R S x‖ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    have : R + S < |x| := by
      by_contra h; push Not at h; exact hx ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩
    rw [mertensTest_eq_zero hS this, norm_zero]
  rw [hset]
  have hi : IntegrableOn (fun x => ‖mertensTest R S x‖) (Icc (-(R + S)) (R + S)) :=
    (contDiff_mertensTest R S).continuous.norm.integrableOn_Icc
  calc ∫ x in Icc (-(R + S)) (R + S), ‖mertensTest R S x‖
      ≤ ∫ x in Icc (-(R + S)) (R + S), ∫ t : ℝ, ‖weilRadicalTest R t‖ :=
        setIntegral_mono_on hi (integrableOn_const (by simp) (by simp)) measurableSet_Icc
          fun x _ => norm_mertensTest_le R S x
    _ = 2 * (R + S) * ∫ t : ℝ, ‖weilRadicalTest R t‖ := by
        rw [setIntegral_const]
        simp only [Measure.real, Real.volume_Icc, smul_eq_mul]
        rw [ENNReal.toReal_ofReal (by linarith)]; ring

/-- The even part of the Weil test of `f_{R,S}` has derivative bounded by `8 C₁² L_g` for
`0 ≤ R ≤ S`, where `C₁ = ‖Φ‖₁‖κ₂‖₁`. -/
theorem abs_deriv_weilTestEvenPart_mertensTest_le {R S Lg : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S)
    (hS : 0 < S) (hLg0 : 0 ≤ Lg)
    (hLg : ∀ x y : ℝ, ‖mertensProbe x - mertensProbe y‖ ≤ Lg * |x - y|) (u : ℝ) :
    |deriv (weilTestEvenPart (mertensTest R S)) u| ≤
      8 * ((∫ v : ℝ, ‖Φ v‖) * ∫ v : ℝ, ‖weilBumpPolarFree v‖) ^ 2 * Lg := by
  set C := ∫ t : ℝ, ‖weilRadicalTest R t‖ with hC
  have hC0 : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hC1 := integral_norm_weilRadicalTest_le R
  rw [← hC] at hC1
  have hM0 : 0 ≤ C * Lg / S := div_nonneg (mul_nonneg hC0 hLg0) hS.le
  have hM : ∀ x y : ℝ, ‖mertensTest R S x - mertensTest R S y‖ ≤ C * Lg / S * |x - y| := by
    intro x y
    refine (norm_mertensTest_sub_le hS hLg x y).trans (le_of_eq ?_)
    rw [← hC]; ring
  have h := abs_deriv_weilTestEvenPart_le (contDiff_mertensTest R S).continuous
    (hasCompactSupport_mertensTest hS) hM0 hM u
  refine h.trans ?_
  have h1 := integral_norm_mertensTest_le hR hS
  rw [← hC] at h1
  calc 2 * (∫ x : ℝ, ‖mertensTest R S x‖) * (C * Lg / S)
      ≤ 2 * (2 * (R + S) * C) * (C * Lg / S) := by gcongr
    _ = 4 * ((R + S) / S) * C ^ 2 * Lg := by field_simp; ring
    _ ≤ 4 * 2 * C ^ 2 * Lg := by
        gcongr
        rw [div_le_iff₀ hS]; linarith
    _ ≤ 8 * ((∫ v : ℝ, ‖Φ v‖) * ∫ v : ℝ, ‖weilBumpPolarFree v‖) ^ 2 * Lg := by
        have : C ^ 2 ≤ ((∫ v : ℝ, ‖Φ v‖) * ∫ v : ℝ, ‖weilBumpPolarFree v‖) ^ 2 :=
          pow_le_pow_left₀ hC0 hC1 2
        nlinarith

private theorem exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have h := Real.exp_one_lt_d9
  have : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

/-- **The zero side of the spread test at `R = log S` is super-exponentially small.** -/
theorem exists_norm_W_mertensTest_log_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ S : ℝ, Real.exp 1 ≤ S →
    ‖zetaZeroConfig.W (mertensTest (Real.log S) S) (mertensTest (Real.log S) S)‖ ≤
      K * S ^ 10 * Real.exp (-S) := by
  obtain ⟨K₀, hK₀, hK⟩ := exists_weilRadicalTest_norms_le
  set SZ := ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) with hSZ
  have hSZ0 : 0 ≤ SZ := tsum_nonneg fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by have := Complex.normSq_nonneg (gammaOf (ρ : ℂ)); linarith)
  set Aκ := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hAκ
  have hAκ0 : 0 ≤ Aκ := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  set G₁ := ∫ x : ℝ, ‖mertensProbe x‖ with hG₁
  have hG₁0 : 0 ≤ G₁ := integral_nonneg fun _ => norm_nonneg _
  set E₀ := 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) with hE₀
  have hE0 : 0 ≤ E₀ := by
    have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
    have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
    rw [hE₀]; positivity
  refine ⟨5 / 4 * SZ * Aκ * E₀ * K₀ * G₁ ^ 2, by positivity, fun S hS => ?_⟩
  have hS0 : 0 < S := lt_of_lt_of_le (Real.exp_pos 1) hS
  set R := Real.log S with hR
  have hR1 : 1 ≤ R := by rw [hR, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hS
  have hR0 : 0 ≤ R := by linarith
  have hexpR : Real.exp R = S := Real.exp_log hS0
  have hRS : R ≤ S := Real.log_le_self hS0.le
  have hS2 : 2 ≤ S := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hS
  have h := norm_W_mertensTest_le hK₀ hK hR0 hS0
  rw [← hSZ, ← hAκ, ← hG₁] at h
  have hε := integral_norm_riemannPhiTail_mul_exp_le (L := R) (b := 1 / 2) hR1 (by norm_num)
  rw [← hE₀] at hε
  have he6 : Real.exp (6 * (R - 1 / 4)) ≤ S ^ 6 := by
    rw [← hexpR, ← Real.exp_nat_mul]; exact Real.exp_le_exp.mpr (by push_cast; linarith)
  have he2 : S ^ 2 / 2 ≤ Real.exp (2 * (R - 1 / 4)) := by
    have : Real.exp (2 * (R - 1 / 4)) = S ^ 2 / Real.exp (1 / 2) := by
      rw [show 2 * (R - 1 / 4) = 2 * R - 1 / 2 by ring, Real.exp_sub, ← hexpR,
        ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [this]
    exact div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) exp_half_le_two
  have hεS : ∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|) ≤
      E₀ * S ^ 6 * Real.exp (-(π * (S ^ 2 / 2))) := by
    refine hε.trans ?_
    have hexp : Real.exp (-π * Real.exp (2 * (R - 1 / 4))) ≤ Real.exp (-(π * (S ^ 2 / 2))) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    gcongr
  have hD : Real.exp (R / 2) * (R * K₀) ≤ S * (S * K₀) := by
    have : Real.exp (R / 2) ≤ S := by rw [← hexpR]; exact Real.exp_le_exp.mpr (by linarith)
    gcongr
  have hsq : (Real.exp (S / 2) * (S * G₁)) ^ 2 = Real.exp S * (S ^ 2 * G₁ ^ 2) := by
    rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hdecay : Real.exp S * Real.exp (-(π * (S ^ 2 / 2))) ≤ Real.exp (-S) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_gt_three]
  have hε0 : 0 ≤ ∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|) :=
    integral_nonneg fun _ => by positivity
  calc ‖zetaZeroConfig.W (mertensTest R S) (mertensTest R S)‖
      ≤ 5 / 4 * SZ * (Aκ * ∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) *
          (Real.exp (R / 2) * (R * K₀)) * (Real.exp (S / 2) * (S * G₁)) ^ 2 := h
    _ ≤ 5 / 4 * SZ * (Aκ * (E₀ * S ^ 6 * Real.exp (-(π * (S ^ 2 / 2))))) * (S * (S * K₀)) *
          (Real.exp S * (S ^ 2 * G₁ ^ 2)) := by
        rw [hsq]; gcongr
    _ = 5 / 4 * SZ * Aκ * E₀ * K₀ * G₁ ^ 2 * S ^ 10 *
          (Real.exp S * Real.exp (-(π * (S ^ 2 / 2)))) := by ring
    _ ≤ 5 / 4 * SZ * Aκ * E₀ * K₀ * G₁ ^ 2 * S ^ 10 * Real.exp (-S) := by gcongr

/-- Integrability of the remainder integrand of the Mertens expansion. -/
theorem integrableOn_deriv_comp_log_mul_remainder {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (c : ℕ → ℝ) (A B : ℝ) {b : ℝ} :
    IntegrableOn (fun t => deriv (fun t => φ (Real.log t)) t *
      ((∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) - A * Real.log t - B)) (Ioc 1 b) := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hφc : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hne : ∀ t ∈ Icc 1 b, t ≠ 0 := fun t ht => ne_of_gt (lt_of_lt_of_le one_pos ht.1)
  have hderivEq : EqOn (deriv (fun t => φ (Real.log t))) (fun t => deriv φ (Real.log t) * t⁻¹)
      (Icc 1 b) := fun t ht =>
    ((hφd _).hasDerivAt.comp t (Real.hasDerivAt_log (hne t ht))).deriv
  have hcont : ContinuousOn (fun t => deriv φ (Real.log t) * t⁻¹) (Icc 1 b) :=
    (hφc.comp_continuousOn (Real.continuousOn_log.mono hne)).mul (continuousOn_inv₀.mono hne)
  have hF'int : IntegrableOn (deriv (fun t => φ (Real.log t))) (Icc 1 b) :=
    (hcont.integrableOn_compact isCompact_Icc).congr_fun hderivEq.symm measurableSet_Icc
  have h1 := integrableOn_mul_sum_Icc c zero_le_one hF'int (m := 0)
  have h2 : IntegrableOn (fun t => deriv (fun t => φ (Real.log t)) t * (A * Real.log t + B))
      (Icc 1 b) := by
    refine IntegrableOn.congr_fun ?_ (fun t ht => by rw [hderivEq ht]) measurableSet_Icc
    exact (hcont.mul ((continuousOn_const.mul (Real.continuousOn_log.mono hne)).add
      continuousOn_const)).integrableOn_compact isCompact_Icc
  refine ((h1.sub h2).congr_fun (fun t _ => ?_) measurableSet_Icc).mono_set Ioc_subset_Icc_self
  simp only [Pi.sub_apply]; ring

/-! ### The Mertens-constant obstruction -/

theorem sum_weilPerturbationWeight_eq (lam : ℕ → ℝ) (m : ℕ) :
    ∑ n ∈ Finset.Icc 0 m, weilPerturbationWeight lam n =
      ∑ n ∈ Finset.Icc 2 m, (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n := by
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc (Nat.zero_le 2) le_rfl) (fun n hn0 hn => by
    rw [Finset.mem_Icc] at hn hn0
    simp only [weilPerturbationWeight]
    rw [if_neg (by omega)])]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  simp only [weilPerturbationWeight, if_pos hn.1]

/-- The mass of the spread test at `R = log S` grows linearly in `S`. -/
theorem exists_integral_norm_sq_mertensTest_log_ge : ∃ c S₀ : ℝ, 0 < c ∧ ∀ S : ℝ, S₀ ≤ S →
    c * S ≤ ∫ x : ℝ, ‖mertensTest (Real.log S) S x‖ ^ 2 := by
  obtain ⟨Lg, hLg0, hLg⟩ := exists_lipschitz_mertensProbe
  obtain ⟨L₁, hL₁1, hmass⟩ := exists_norm_paperFT_weilRadicalTest_zero_ge
  set C₁ := (∫ u : ℝ, ‖Φ u‖) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hC₁
  have hC₁0 : 0 ≤ C₁ := (integral_nonneg fun _ => norm_nonneg _).trans
    (integral_norm_weilRadicalTest_le 0)
  set G₂ := ∫ x : ℝ, ‖mertensProbe x‖ ^ 2 with hG₂
  have hG₂0 : 0 < G₂ := integral_norm_sq_mertensProbe_pos
  set c₀ := ‖xi (1 / 2)‖ / 32 with hc₀
  have hc₀0 : 0 < c₀ := by rw [hc₀]; exact div_pos (norm_pos_iff.mpr xi_half_ne_zero) (by norm_num)
  refine ⟨c₀ ^ 2 * G₂ / 4, max (Real.exp L₁) (16 * Lg ^ 2 * C₁ ^ 2 / (c₀ ^ 2 * G₂ / 4) + 1),
    by positivity, fun S hS => ?_⟩
  have hSe : Real.exp L₁ ≤ S := le_of_max_le_left hS
  have hSc : 16 * Lg ^ 2 * C₁ ^ 2 / (c₀ ^ 2 * G₂ / 4) + 1 ≤ S := le_of_max_le_right hS
  have hS0 : 0 < S := lt_of_lt_of_le (Real.exp_pos _) hSe
  set R := Real.log S with hR
  have hRL : L₁ ≤ R := by rw [hR, ← Real.log_exp L₁]; exact Real.log_le_log (Real.exp_pos _) hSe
  have hR0 : 0 ≤ R := by linarith
  have hRS : R ≤ S := Real.log_le_self hS0.le
  have hR2 : R ^ 2 ≤ 4 * S := by
    have h := Real.log_le_rpow_div (x := S) (ε := 1 / 2) hS0.le (by norm_num)
    have hsq : (S ^ (1 / 2 : ℝ)) ^ 2 = S := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hS0.le]; norm_num
    have hR2' : R ≤ 2 * S ^ (1 / 2 : ℝ) := by rw [hR]; linarith
    have := pow_le_pow_left₀ hR0 hR2' 2
    nlinarith
  have hm := hmass R hRL
  have hmass' : c₀ ^ 2 ≤ ‖paperFT (weilRadicalTest R) 0‖ ^ 2 := pow_le_pow_left₀ hc₀0.le hm 2
  have hlow := integral_norm_sq_mertensTest_ge hR0 hS0 hLg0 hLg
  have hCR := integral_norm_weilRadicalTest_le R
  rw [← hC₁] at hCR
  have hCR0 : 0 ≤ ∫ t : ℝ, ‖weilRadicalTest R t‖ := integral_nonneg fun _ => norm_nonneg _
  have herr : 2 * (R + S) * (Lg * R * (∫ t : ℝ, ‖weilRadicalTest R t‖) / S) ^ 2 ≤
      16 * Lg ^ 2 * C₁ ^ 2 := by
    have h1 : (Lg * R * (∫ t : ℝ, ‖weilRadicalTest R t‖) / S) ^ 2 ≤ (Lg * R * C₁ / S) ^ 2 := by
      gcongr
    have h2 : 2 * (R + S) * (Lg * R * C₁ / S) ^ 2 = 2 * ((R + S) / S) * (R ^ 2 / S) *
        (Lg ^ 2 * C₁ ^ 2) := by field_simp
    have h3 : (R + S) / S ≤ 2 := by rw [div_le_iff₀ hS0]; linarith
    have h4 : R ^ 2 / S ≤ 4 := by rw [div_le_iff₀ hS0]; linarith
    calc 2 * (R + S) * (Lg * R * (∫ t : ℝ, ‖weilRadicalTest R t‖) / S) ^ 2
        ≤ 2 * (R + S) * (Lg * R * C₁ / S) ^ 2 := by gcongr
      _ = 2 * ((R + S) / S) * (R ^ 2 / S) * (Lg ^ 2 * C₁ ^ 2) := h2
      _ ≤ 2 * 2 * 4 * (Lg ^ 2 * C₁ ^ 2) := by gcongr
      _ = 16 * Lg ^ 2 * C₁ ^ 2 := by ring
  have hmain : c₀ ^ 2 * G₂ / 2 * S ≤
      1 / 2 * ‖paperFT (weilRadicalTest R) 0‖ ^ 2 * (S * G₂) := by
    have : c₀ ^ 2 * G₂ / 2 * S = 1 / 2 * c₀ ^ 2 * (S * G₂) := by ring
    rw [this]; gcongr
  have hc : 16 * Lg ^ 2 * C₁ ^ 2 ≤ c₀ ^ 2 * G₂ / 4 * S := by
    have hpos : 0 < c₀ ^ 2 * G₂ / 4 := by positivity
    have := (div_le_iff₀ hpos).mp (by linarith : 16 * Lg ^ 2 * C₁ ^ 2 / (c₀ ^ 2 * G₂ / 4) ≤ S)
    linarith
  linarith

/-- A Mertens expansion `C(t) = A log t + B + o(1)` has bounded remainder on every initial range
and remainder at most `η` beyond some `T`. -/
theorem exists_mertens_remainder_bounds {c : ℕ → ℝ} {A B : ℝ}
    (hlim : Tendsto (fun t : ℝ => (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) - A * Real.log t) atTop (𝓝 B))
    {η : ℝ} (hη : 0 < η) :
    ∃ T E : ℝ, 1 ≤ T ∧
      (∀ t ∈ Icc 1 T, |(∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) - A * Real.log t - B| ≤ E) ∧
      ∀ t, T ≤ t → |(∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) - A * Real.log t - B| ≤ η := by
  have hε : Tendsto (fun t : ℝ => (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) - A * Real.log t - B) atTop
      (𝓝 0) := by
    have h := hlim.sub_const B
    rwa [sub_self] at h
  obtain ⟨T₀, hT₀⟩ := (hε.eventually (Metric.closedBall_mem_nhds 0 hη)).exists_forall_of_atTop
  refine ⟨max T₀ 1, (∑ n ∈ Finset.Icc 0 ⌊max T₀ 1⌋₊, |c n|) + |A| * Real.log (max T₀ 1) + |B|,
    le_max_right _ _, fun t ht => ?_, fun t ht => ?_⟩
  · have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht.1
    have hlogT : Real.log t ≤ Real.log (max T₀ 1) := Real.log_le_log (by linarith [ht.1]) ht.2
    have hsum : |∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n| ≤ ∑ n ∈ Finset.Icc 0 ⌊max T₀ 1⌋₊, |c n| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor ht.2)) fun _ _ _ => abs_nonneg _)
    have hA : |A * Real.log t| ≤ |A| * Real.log (max T₀ 1) := by
      rw [abs_mul, abs_of_nonneg hlog0]; exact mul_le_mul_of_nonneg_left hlogT (abs_nonneg _)
    calc |(∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) - A * Real.log t - B|
        ≤ |∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n| + |A * Real.log t| + |B| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ ≤ _ := by gcongr
  · have := hT₀ t (le_trans (le_max_left _ _) ht)
    rwa [Real.dist_eq, sub_zero] at this

/-- **Symbol energy of the spread test.**  At `R = log S` and level `a = R + S`, the symbol energy
with weights `lam` is at most `2π(‖W‖ - 2B‖f‖₂² + M₀E log T + M₀η(2a + 1))`, where `E` and `η`
bound the Mertens remainder on `[1, T]` and beyond `T`, and `M₀ = 8C₁²L_g`. -/
theorem integral_weilAtomSymbol_mertensTest_le {lam : ℕ → ℝ} {A B Lg : ℝ} (hLg0 : 0 ≤ Lg)
    (hLg : ∀ x y : ℝ, ‖mertensProbe x - mertensProbe y‖ ≤ Lg * |x - y|) {S T E η : ℝ}
    (hS : 1 ≤ S) (hT1 : 1 ≤ T) (hTS : T ≤ S)
    (hE : ∀ t ∈ Icc 1 T, |(∑ n ∈ Finset.Icc 0 ⌊t⌋₊, weilPerturbationWeight lam n) -
      A * Real.log t - B| ≤ E)
    (hη : ∀ t, T ≤ t → |(∑ n ∈ Finset.Icc 0 ⌊t⌋₊, weilPerturbationWeight lam n) -
      A * Real.log t - B| ≤ η) :
    ∫ τ : ℝ, ‖paperFT (mertensTest (Real.log S) S) τ‖ ^ 2 *
        weilAtomSymbol lam ⌊Real.exp (2 * (Real.log S + S))⌋₊ (τ / (2 * π)) ≤
      2 * π * (‖zetaZeroConfig.W (mertensTest (Real.log S) S) (mertensTest (Real.log S) S)‖ -
        2 * B * (∫ x : ℝ, ‖mertensTest (Real.log S) S x‖ ^ 2) +
        8 * ((∫ u : ℝ, ‖Φ u‖) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) ^ 2 * Lg * E * Real.log T +
        8 * ((∫ u : ℝ, ‖Φ u‖) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) ^ 2 * Lg * η *
          (2 * (Real.log S + S) + 1)) := by
  have hS0 : 0 < S := by linarith
  have hR0 : 0 ≤ Real.log S := Real.log_nonneg hS
  have hRS : Real.log S ≤ S := Real.log_le_self hS0.le
  have ha0 : 0 ≤ Real.log S + S := by linarith
  have hfd := contDiff_mertensTest (Real.log S) S
  have hfs := tsupport_mertensTest (R := Real.log S) hS0
  have hI := integral_weilAtomSymbol_eq_mertens ha0 hfd hfs (paperFT_mertensTest_half_I hS0)
    (paperFT_mertensTest_neg_half_I hS0) lam A B
  rw [paperFT_mertensTest_zero hS0, norm_zero] at hI
  have hφ : ContDiff ℝ 1 (weilTestEvenPart (mertensTest (Real.log S) S)) :=
    (contDiff_weilTestEvenPart hfd hfs).of_le (by norm_num)
  have hTb : T ≤ Real.exp (2 * (Real.log S + S) + 1) :=
    hTS.trans (le_trans (by linarith) (Real.add_one_le_exp (2 * (Real.log S + S) + 1)))
  have hJ := abs_integral_deriv_comp_log_mul_le hφ
    (abs_deriv_weilTestEvenPart_mertensTest_le hR0 hRS hS0 hLg0 hLg) hT1 hTb hE hη
    (integrableOn_deriv_comp_log_mul_remainder hφ (weilPerturbationWeight lam) A B)
  rw [Real.log_exp] at hJ
  rw [hI]
  have hWre := Complex.re_le_norm
    (zetaZeroConfig.W (mertensTest (Real.log S) S) (mertensTest (Real.log S) S))
  have hJle := (le_abs_self _).trans hJ
  have hπ : 0 < π := Real.pi_pos
  have key : (zetaZeroConfig.W (mertensTest (Real.log S) S) (mertensTest (Real.log S) S)).re -
      (A * 0 ^ 2 + 2 * B * ∫ x : ℝ, ‖mertensTest (Real.log S) S x‖ ^ 2) +
      ∫ t in Ioc 1 (Real.exp (2 * (Real.log S + S) + 1)),
        deriv (fun t => weilTestEvenPart (mertensTest (Real.log S) S) (Real.log t)) t *
          ((∑ n ∈ Finset.Icc 0 ⌊t⌋₊, weilPerturbationWeight lam n) - A * Real.log t - B) ≤
      ‖zetaZeroConfig.W (mertensTest (Real.log S) S) (mertensTest (Real.log S) S)‖ -
        2 * B * (∫ x : ℝ, ‖mertensTest (Real.log S) S x‖ ^ 2) +
        8 * ((∫ u : ℝ, ‖Φ u‖) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) ^ 2 * Lg * E * Real.log T +
        8 * ((∫ u : ℝ, ‖Φ u‖) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) ^ 2 * Lg * η *
          (2 * (Real.log S + S) + 1) := by
    have : A * (0 : ℝ) ^ 2 = 0 := by ring
    rw [this, zero_add]
    linarith
  have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * π)
  linarith

/-- **Weil positivity forces a nonpositive Mertens constant.**  Let `lam : ℕ → ℝ` be prime-side
weights whose deviation from the von Mangoldt function has a Mertens expansion
`∑_{2 ≤ n ≤ x} (lam(n) - Λ(n)) n^{-1/2} = A log x + B + o(1)`.  If the finite-atom Weil symbol with
weights `lam` has nonnegative energy on every polar-constrained `C²` test at every level, then
`B ≤ 0`.

The tests are truncated radical tests of `ζ` spread over the scale `S` by a mean-zero probe, at
truncation level `log S`.  Their zero side is `O(S^{10} e^{-S})`, their mass is at least `cS`,
their transform vanishes at `0`, and their Weil test varies on the scale `S`; the Mertens expansion
then gives symbol energy at most `-πBcS` for large `S`. -/
theorem mertens_constant_nonpos_of_weilAtomSymbol_nonneg {lam : ℕ → ℝ} {A B : ℝ}
    (hlim : Tendsto (fun x : ℝ =>
      (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n) -
        A * Real.log x) atTop (𝓝 B))
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) :
    B ≤ 0 := by
  by_contra hB
  push Not at hB
  obtain ⟨Lg, hLg0, hLg⟩ := exists_lipschitz_mertensProbe
  set M₀ := 8 * ((∫ u : ℝ, ‖Φ u‖) * ∫ u : ℝ, ‖weilBumpPolarFree u‖) ^ 2 * Lg with hM₀
  have hM₀0 : 0 ≤ M₀ := by positivity
  obtain ⟨c₁, S₁, hc₁, hmassS⟩ := exists_integral_norm_sq_mertensTest_log_ge
  obtain ⟨K, hK0, hWS⟩ := exists_norm_W_mertensTest_log_le
  have hlim' : Tendsto (fun t : ℝ => (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, weilPerturbationWeight lam n) -
      A * Real.log t) atTop (𝓝 B) :=
    hlim.congr fun t => by rw [sum_weilPerturbationWeight_eq]
  have hη0 : 0 < B * c₁ / (10 * (M₀ + 1)) := by positivity
  obtain ⟨T, E, hT1, hE, hη⟩ := exists_mertens_remainder_bounds hlim' hη0
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (hE 1 ⟨le_rfl, hT1⟩)
  have hWlim : Tendsto (fun S : ℝ => K * (S ^ 9 * Real.exp (-S))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 9).const_mul K
  obtain ⟨S, hWsmall, hSbig⟩ := ((hWlim.eventually (ge_mem_nhds (by positivity :
    (0 : ℝ) < B * c₁ / 2))).and (eventually_ge_atTop
      (max (max S₁ (Real.exp 1)) (max T (2 * M₀ * E * Real.log T / (B * c₁)))))).exists
  have hS₁ : S₁ ≤ S := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hSbig
  have hSe : Real.exp 1 ≤ S := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hSbig
  have hST : T ≤ S := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hSbig
  have hSE : 2 * M₀ * E * Real.log T / (B * c₁) ≤ S :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hSbig
  have hS0 : 0 < S := lt_of_lt_of_le (Real.exp_pos 1) hSe
  have hS1 : 1 ≤ S := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hSe
  have hRS : Real.log S ≤ S := Real.log_le_self hS0.le
  have hR0 : 0 ≤ Real.log S := Real.log_nonneg hS1
  have hbound := integral_weilAtomSymbol_mertensTest_le hLg0 hLg hS1 hT1 hST hE hη
  rw [← hM₀] at hbound
  have hpos' := hpos (Real.log S + S) (by linarith [Real.log_nonneg hS1]) _
    (contDiff_mertensTest (Real.log S) S) (tsupport_mertensTest hS0)
    (paperFT_mertensTest_half_I hS0) (paperFT_mertensTest_neg_half_I hS0)
  have hW : ‖zetaZeroConfig.W (mertensTest (Real.log S) S) (mertensTest (Real.log S) S)‖ ≤
      B * c₁ / 2 * S := by
    refine (hWS S hSe).trans ?_
    calc K * S ^ 10 * Real.exp (-S) = K * (S ^ 9 * Real.exp (-S)) * S := by ring
      _ ≤ B * c₁ / 2 * S := mul_le_mul_of_nonneg_right hWsmall hS0.le
  have hmass : B * (c₁ * S) ≤ B * ∫ x : ℝ, ‖mertensTest (Real.log S) S x‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (hmassS S hS₁) hB.le
  have h1 : M₀ * E * Real.log T ≤ B * c₁ / 2 * S := by
    have := (div_le_iff₀ (by positivity : 0 < B * c₁)).mp hSE
    linarith
  have h2 : M₀ * (B * c₁ / (10 * (M₀ + 1))) * (2 * (Real.log S + S) + 1) ≤ B * c₁ / 2 * S := by
    have hηM : M₀ * (B * c₁ / (10 * (M₀ + 1))) ≤ B * c₁ / 10 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_pos hB hc₁]
    have ha' : 2 * (Real.log S + S) + 1 ≤ 5 * S := by linarith
    calc M₀ * (B * c₁ / (10 * (M₀ + 1))) * (2 * (Real.log S + S) + 1)
        ≤ B * c₁ / 10 * (5 * S) := mul_le_mul hηM ha' (by linarith) (by positivity)
      _ = B * c₁ / 2 * S := by ring
  have hX : ‖zetaZeroConfig.W (mertensTest (Real.log S) S) (mertensTest (Real.log S) S)‖ -
        2 * B * (∫ x : ℝ, ‖mertensTest (Real.log S) S x‖ ^ 2) + M₀ * E * Real.log T +
        M₀ * (B * c₁ / (10 * (M₀ + 1))) * (2 * (Real.log S + S) + 1) < 0 := by
    have : 0 < B * c₁ * S := by positivity
    nlinarith
  have hπ : 0 < π := Real.pi_pos
  have := mul_neg_of_pos_of_neg (by positivity : (0 : ℝ) < 2 * π) hX
  linarith

/-! ### Deleting the even prime powers -/

/-- The von Mangoldt function with the even prime powers `p^{2j}` deleted: `Λ(n)` off the perfect
squares and `0` on them. -/
def squareDeletedVonMangoldt (n : ℕ) : ℝ :=
  if IsSquare n then 0 else ArithmeticFunction.vonMangoldt n

theorem floor_sqrt_eq_sqrt_floor {x : ℝ} (hx : 0 ≤ x) : ⌊Real.sqrt x⌋₊ = Nat.sqrt ⌊x⌋₊ := by
  rw [Nat.floor_eq_iff (Real.sqrt_nonneg x)]
  constructor
  · rw [Real.le_sqrt (Nat.cast_nonneg _) hx]
    have h1 : ((Nat.sqrt ⌊x⌋₊ : ℕ) : ℝ) ^ 2 ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.sqrt_le' _
    exact h1.trans (Nat.floor_le hx)
  · rw [Real.sqrt_lt' (by positivity)]
    have h2 : ⌊x⌋₊ < (Nat.sqrt ⌊x⌋₊ + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have h3 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    have h4 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ (((Nat.sqrt ⌊x⌋₊ + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h4; linarith

/-- The weight difference of the square deletion sums to minus the Mertens sum at `√N`. -/
theorem sum_squareDeletedVonMangoldt_sub_eq (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, (squareDeletedVonMangoldt n - ArithmeticFunction.vonMangoldt n) /
        Real.sqrt n =
      -∑ m ∈ Finset.Icc 0 (Nat.sqrt N), ArithmeticFunction.vonMangoldt m / m := by
  have hterm : ∀ n : ℕ, (squareDeletedVonMangoldt n - ArithmeticFunction.vonMangoldt n) /
      Real.sqrt n = -(if IsSquare n then ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0) := by
    intro n; unfold squareDeletedVonMangoldt; split_ifs <;> ring
  simp only [hterm, Finset.sum_neg_distrib, ← Finset.sum_filter]
  congr 1
  have himage : (Finset.Icc 2 N).filter (fun n => IsSquare n) =
      (Finset.Icc 2 (Nat.sqrt N)).image (fun m => m ^ 2) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h2, hN⟩, r, rfl⟩
      refine ⟨r, ⟨?_, Nat.le_sqrt.mpr hN⟩, by ring⟩
      by_contra h; push Not at h
      interval_cases r <;> omega
    · rintro ⟨m, ⟨hm2, hmN⟩, rfl⟩
      refine ⟨⟨by nlinarith, by have := Nat.le_sqrt.mp hmN; nlinarith⟩, m, by ring⟩
  rw [himage, Finset.sum_image (fun x _ y _ h => Nat.pow_left_injective two_ne_zero h)]
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc (Nat.zero_le 2) le_rfl) (fun m hm0 hm => by
    rw [Finset.mem_Icc] at hm hm0
    have : m = 0 ∨ m = 1 := by omega
    rcases this with rfl | rfl <;> simp)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero]
  push_cast
  rw [Real.sqrt_sq (Nat.cast_nonneg _)]

/-- **Mertens expansion of the square deletion**: slope `-1/2` and constant `γ`. -/
theorem tendsto_squareDeletedVonMangoldt_mertens :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, (squareDeletedVonMangoldt n - ArithmeticFunction.vonMangoldt n) /
        Real.sqrt n) - (-(1 / 2)) * Real.log x) atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h := (tendsto_real_sum_vonMangoldt_div_sub_log.comp Real.tendsto_sqrt_atTop).neg
  rw [neg_neg] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_apply, sum_squareDeletedVonMangoldt_sub_eq, floor_sqrt_eq_sqrt_floor hx,
    Real.log_sqrt hx]
  ring

/-- **Weil positivity fails when the even prime powers are deleted.**  With the weights `Λ(n)` for
non-square `n` and `0` on the perfect squares, some polar-constrained `C²` test at some level has
negative finite-atom Weil symbol energy.  The obstruction is Euler's constant: the deleted weights
`Λ(p^{2j}) p^{-j}` have Mertens expansion `-(1/2) log x + γ + o(1)`, and `γ > 0`.  For the full
von Mangoldt weights the same energy is `2π` times the zero side of `ζ`. -/
theorem squareDeletedVonMangoldt_weilAtomSymbol_not_nonneg :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol squareDeletedVonMangoldt ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  by_contra h
  push Not at h
  have := mertens_constant_nonpos_of_weilAtomSymbol_nonneg
    tendsto_squareDeletedVonMangoldt_mertens h
  linarith [Real.one_half_lt_eulerMascheroniConstant]

end RHTower

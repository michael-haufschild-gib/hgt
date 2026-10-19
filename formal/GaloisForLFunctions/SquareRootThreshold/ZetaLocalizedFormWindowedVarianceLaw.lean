import GaloisForLFunctions.SquareRootThreshold.WindowedMeanValueDiagonalLaw
import GaloisForLFunctions.SquareRootThreshold.ZetaSingleHeightPositivityAboveArchimedeanHorizon

/-!
# The windowed variance of the localized Weil forms of `ζ` below the square-root threshold

Let `f` be a `C²` profile supported in `[-a, a]`, and put `X = e^{2a}` and `N = ⌊X⌋`. The localized
form at height `2πξ` splits as `W_ζ(S_ξ f, S_ξ f) = A_f(ξ) − Π_f(ξ)`
(`zetaZeroConfig_W_heightShift_eq_sub`), where:
* `A_f(ξ) = h_k(i/2) + h_k(−i/2) + ∫ h_k μ` is the pole-plus-archimedean part, with
  `k = S_ξ f ⋆ (S_ξ f)~`;
* `Π_f(ξ) = Σ_{2 ≤ n ≤ N} Λ(n) n^{−1/2} (k_f(log n) n^{2πiξ} + k_f(−log n) n^{−2πiξ})` is the prime
  polynomial.

**Variance law** (`integral_windowed_sq_deviation_eq`). Let `η` be a window supported in
`[-r, r]` with `2rX ≤ 1`, centred at any height `ξ₀`. Then
`∫ |h_η(−2πξ)|² |W_ζ(S_{ξ+ξ₀} f, S_{ξ+ξ₀} f) − A_f(ξ + ξ₀)|² dξ = ‖η‖² V_f`, where
`V_f = Σ_{2 ≤ n ≤ N} Λ(n)²/n (|k_f(log n)|² + |k_f(−log n)|²)`. Below the square-root threshold,
the deviation of the localized form from its archimedean part has no off-diagonal.

**Most heights are positive** (`lintegral_bad_heights_le`, `lintegral_bad_heights_le_of_height`).
Suppose `A₀ > 0` is a lower bound for `Re A_f` on a set `U` of heights. Then the heights in `U` where
`Re W_ζ(S_ξ f, S_ξ f) < 0` carry window weight at most `‖η‖² V_f/A₀²`, out of a total weight
`‖η‖²`. At heights `|ξ| ≥ Ξ`, the symbol estimate gives
`A₀ = (log(1 + πΞ/4) − 10 − 2S(a))‖f‖² − B_f²/(8(1 + πΞ))`, while
`V_f ≤ 2‖f‖⁴ Σ_{n ≤ X} Λ(n)²/n`. So the proportion of heights near `T` with a negative localized form
is `O((log X/log T)²)`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.WeilRegular

/-! ### The prime polynomial of a localized Weil form -/

/-- `k_{S_ξ f}(v) = e^{2πiξv} k_f(v)`. -/
theorem weilTest_heightShift (ξ : ℝ) (f : ℝ → ℂ) (v : ℝ) :
    EF.weilTest (heightShift ξ f) (heightShift ξ f) v =
      cexp (2 * π * I * ξ * v) * EF.weilTest f f v := by
  rw [weilTest_apply, weilTest_apply, ← integral_const_mul]
  congr 1 with t
  have he : cexp (2 * π * I * ξ * t) * conj (cexp (2 * π * I * ξ * ((t - v : ℝ) : ℂ))) =
      cexp (2 * π * I * ξ * v) := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  simp only [heightShift, map_mul]
  rw [← he]
  ring

/-- Frequencies `±log n` of the prime polynomial. -/
def primeFreq (nb : ℕ × Bool) : ℝ := if nb.2 then Real.log nb.1 else -Real.log nb.1

/-- Coefficients `Λ(n) n^{−1/2} k_f(±log n)` of the prime polynomial. -/
def primeCoeff (f : ℝ → ℂ) (nb : ℕ × Bool) : ℂ :=
  ((ArithmeticFunction.vonMangoldt nb.1 / Real.sqrt nb.1 : ℝ) : ℂ) * EF.weilTest f f (primeFreq nb)

/-- The prime polynomial `Π_f(ξ)` of the localized Weil form, with primes up to `N`. -/
def primePolynomial (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) : ℂ :=
  expSum (Finset.Icc 2 N ×ˢ Finset.univ) (primeCoeff f) primeFreq ξ

/-- The pole-plus-archimedean part `A_f(ξ)` of the localized Weil form. -/
def archPart (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) (I / 2) +
    paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) (-I / 2) +
    ∫ τ : ℝ, paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ * (mu τ : ℂ)

/-- The diagonal energy `V_f` of the prime polynomial. -/
def primeVariance (f : ℝ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n) ^ 2 / n *
    (‖EF.weilTest f f (Real.log n)‖ ^ 2 + ‖EF.weilTest f f (-Real.log n)‖ ^ 2)

theorem tsum_vonMangoldt_heightShift_eq {a : ℝ} {f : ℝ → ℂ} (hfs : tsupport f ⊆ Icc (-a) a)
    (ξ : ℝ) :
    ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (EF.weilTest (heightShift ξ f) (heightShift ξ f) (Real.log n) +
        EF.weilTest (heightShift ξ f) (heightShift ξ f) (-Real.log n)) =
      primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ := by
  have hfs' : tsupport f ⊆ Icc (-(2 * a / 2)) (2 * a / 2) := by
    rwa [mul_div_cancel_left₀ _ two_ne_zero]
  have hks : tsupport (EF.weilTest f f) ⊆ Icc (-(2 * a)) (2 * a) :=
    EF.tsupport_weilTest_subset hfs' hfs'
  rw [tsum_eq_sum (s := Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊)]
  · rw [primePolynomial, expSum, Finset.sum_product]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Fintype.sum_bool]
    simp only [primeCoeff, primeFreq, ↓reduceIte, Bool.false_eq_true, weilTest_heightShift]
    push_cast
    ring
  · intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · interval_cases n <;> simp [ArithmeticFunction.vonMangoldt_apply_one]
    · have hX : Real.exp (2 * a) < n := by
        have h1 := Nat.lt_floor_add_one (Real.exp (2 * a))
        have h2 : ((⌊Real.exp (2 * a)⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
        push_cast at h2
        linarith
      have hlog : 2 * a < Real.log n := by
        rw [← Real.log_exp (2 * a)]
        exact Real.log_lt_log (Real.exp_pos _) hX
      have h1 : Real.log n ∉ Icc (-(2 * a)) (2 * a) := fun h => by linarith [h.2]
      have h2 : -Real.log n ∉ Icc (-(2 * a)) (2 * a) := fun h => by linarith [h.1]
      rw [weilTest_heightShift, weilTest_heightShift, eq_zero_of_not_mem_Icc hks h1,
        eq_zero_of_not_mem_Icc hks h2]
      simp

/-- **The localized form is the archimedean part minus the prime polynomial.** -/
theorem zetaZeroConfig_W_heightShift_eq_sub {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) :
    zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f) =
      archPart f ξ - primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ := by
  have hg : ContDiff ℝ 2 (heightShift ξ f) := heightShift_contDiff hf ξ
  have hgs : tsupport (heightShift ξ f) ⊆ Icc (-a) a :=
    (tsupport_heightShift_subset ξ f).trans hfs
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hkd := EF.weilTest_contDiff hg hg.continuous hgc
  have hkc := EF.weilTest_hasCompactSupport hgc hgc
  obtain ⟨-, heq⟩ := WeilEF.EF_lit_zetaZeroConfig
    (EF.weilTest (heightShift ξ f) (heightShift ξ f)) hkd hkc
  have hfac := EF.paperFT_weilTest hg.continuous hg.continuous hgc hgc
  have hterm : (fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℂ) *
      paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) (gammaOf ρ)) =
      fun ρ : zetaZeroConfig.carrier =>
        zetaZeroConfig.Wsummand (heightShift ξ f) (heightShift ξ f) ρ := by
    ext ρ
    simp only [ZeroConfig.Wsummand, hfac, mul_assoc]
  rw [ZeroConfig.W, ← hterm, heq, EF.literatureRHS, tsum_vonMangoldt_heightShift_eq hfs ξ,
    EF.gamma_term, archPart]
  ring

/-- The pole-plus-archimedean part is at least
`(log(1 + π|ξ|/4) − 10 − 2S(a))‖f‖² − B_f²/(8(1 + π|ξ|))`. -/
theorem re_archPart_ge {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) :
    (Real.log (1 + π * |ξ| / 4) - 10 - 2 * pairEnergy (1 / 2) a) * (∫ t, ‖f t‖ ^ 2) -
      (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) ≤
      (archPart f ξ).re := by
  have hg : ContDiff ℝ 2 (heightShift ξ f) := heightShift_contDiff hf ξ
  have hgs : tsupport (heightShift ξ f) ⊆ Icc (-a) a :=
    (tsupport_heightShift_subset ξ f).trans hfs
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hkd := EF.weilTest_contDiff hg hg.continuous hgc
  have hkc := EF.weilTest_hasCompactSupport hgc hgc
  have hval := paperFT_weilTest_heightShift_ofReal hf.continuous hfc ξ
  have hwi : Integrable fun τ : ℝ => ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ := by
    refine (EF.integrable_paperFT_mul_mu hkd hkc gammaFacts).re.congr
      (Eventually.of_forall fun τ => ?_)
    simp only [hval, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
  have h := re_pole_add_integral_symbol_heightShift_ge (E := 10) ha hf hfs ξ mu_ge_log hwi
  have hμre : (∫ τ : ℝ, paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ *
      (mu τ : ℂ)).re = ∫ τ : ℝ, ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ := by
    have hfun : (fun τ : ℝ => paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ *
        (mu τ : ℂ)) = fun τ : ℝ =>
        ((‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ : ℝ) : ℂ) := by
      funext τ
      rw [hval, Complex.ofReal_mul]
    rw [hfun, integral_complex_ofReal, Complex.ofReal_re]
  rw [archPart, Complex.add_re, hμre]
  exact h

/-! ### The variance law -/

theorem expSum_add {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) (ξ ξ₀ : ℝ) :
    expSum s c ν (ξ + ξ₀) = expSum s (fun j => c j * cexp (2 * π * I * ξ₀ * ν j)) ν ξ := by
  unfold expSum
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc (c j) (cexp (2 * π * I * ξ₀ * ν j)), ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem continuous_expSum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) :
    Continuous (expSum s c ν) := by
  unfold expSum
  fun_prop

theorem norm_expSum_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) (ξ : ℝ) :
    ‖expSum s c ν ξ‖ ≤ ∑ j ∈ s, ‖c j‖ := by
  unfold expSum
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [norm_mul, norm_cexp_two_pi_I_mul, mul_one]

/-- The prime frequencies up to `X` are `2r`-separated when `2rX ≤ 1`. -/
theorem primeFreq_separated {r X : ℝ} (hX1 : 1 ≤ X) (hX : 2 * r * X ≤ 1) :
    ∀ j ∈ Finset.Icc 2 ⌊X⌋₊ ×ˢ (Finset.univ : Finset Bool),
      ∀ k ∈ Finset.Icc 2 ⌊X⌋₊ ×ˢ (Finset.univ : Finset Bool),
        j ≠ k → 2 * r ≤ |primeFreq j - primeFreq k| := by
  have hX0 : 0 < X := by linarith
  have h2r : 2 * r ≤ 1 / X := by rw [le_div_iff₀ hX0]; exact hX
  have h1X : 1 / X ≤ 1 := by rw [div_le_one hX0]; exact hX1
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this
    linarith
  rintro ⟨n, b⟩ hj ⟨m, b'⟩ hk hne
  simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true] at hj hk
  have hnX : (n : ℝ) ≤ X := le_trans (by exact_mod_cast hj.2) (Nat.floor_le hX0.le)
  have hmX : (m : ℝ) ≤ X := le_trans (by exact_mod_cast hk.2) (Nat.floor_le hX0.le)
  have hn2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hj.1)
  have hm2 : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hk.1)
  have hsame : n ≠ m → 1 / X ≤ |Real.log n - Real.log m| := by
    intro hnm
    rcases lt_or_gt_of_ne hnm with h | h
    · have := inv_le_log_sub_log (by omega) h hmX
      rw [abs_sub_comm]
      exact this.trans (le_abs_self _)
    · have := inv_le_log_sub_log (by omega) h hnX
      exact this.trans (le_abs_self _)
  cases b <;> cases b' <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true]
  · have hnm : n ≠ m := fun h => hne (by rw [h])
    rw [show -Real.log n - -Real.log m = -(Real.log n - Real.log m) by ring, abs_neg]
    linarith [hsame hnm]
  · rw [show -Real.log n - Real.log m = -(Real.log n + Real.log m) by ring, abs_neg,
      abs_of_nonneg (by linarith)]
    linarith
  · rw [show Real.log n - -Real.log m = Real.log n + Real.log m by ring,
      abs_of_nonneg (by linarith)]
    linarith
  · have hnm : n ≠ m := fun h => hne (by rw [h])
    linarith [hsame hnm]

/-- **The windowed variance law.** For a window supported in `[-r, r]` with `2rX ≤ 1`, centred at
the height `ξ₀`, the windowed mean square of `W_ζ − A_f` is `‖η‖² V_f`. -/
theorem integral_windowed_sq_deviation_eq {a r : ℝ} (ha : 0 ≤ a) {f η : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-r) r) (hX : 2 * r * Real.exp (2 * a) ≤ 1) (ξ₀ : ℝ) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
          archPart f (ξ + ξ₀)‖ ^ 2 =
      (∫ t, ‖η t‖ ^ 2) * primeVariance f ⌊Real.exp (2 * a)⌋₊ := by
  have hX1 : 1 ≤ Real.exp (2 * a) := Real.one_le_exp (by linarith)
  have hdev : ∀ ξ : ℝ, ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
      archPart f (ξ + ξ₀)‖ = ‖primePolynomial f ⌊Real.exp (2 * a)⌋₊ (ξ + ξ₀)‖ := by
    intro ξ
    rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, sub_sub_cancel_left, norm_neg]
  simp_rw [hdev, primePolynomial, expSum_add]
  rw [integral_normSq_mul_normSq_expSum_of_separated hη hηs _ _ _
    (primeFreq_separated hX1 hX)]
  congr 1
  rw [primeVariance, Finset.sum_product]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Fintype.sum_bool]
  simp only [primeCoeff, primeFreq, ↓reduceIte, Bool.false_eq_true, norm_mul,
    norm_cexp_two_pi_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    div_pow, Real.sq_sqrt hn0]
  ring

/-! ### Most heights are positive -/

/-- **Chebyshev bound for negative localized forms.** If `A₀ > 0` bounds `Re A_f` from below on a
set `U` of heights, then the heights in `U` where `Re W_ζ < 0` carry window weight at most
`‖η‖² V_f/A₀²`. -/
theorem lintegral_bad_heights_le {a r : ℝ} (ha : 0 ≤ a) {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-r) r) (hX : 2 * r * Real.exp (2 * a) ≤ 1) (ξ₀ : ℝ) {U : Set ℝ}
    {A₀ : ℝ} (hA₀ : 0 < A₀) (hU : ∀ ξ ∈ U, A₀ ≤ (archPart f (ξ + ξ₀)).re) :
    ∫⁻ ξ, (U ∩ {ξ | (zetaZeroConfig.W (heightShift (ξ + ξ₀) f)
        (heightShift (ξ + ξ₀) f)).re < 0}).indicator
        (fun ξ => ENNReal.ofReal (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2)) ξ ≤
      ENNReal.ofReal ((∫ t, ‖η t‖ ^ 2) * primeVariance f ⌊Real.exp (2 * a)⌋₊ / A₀ ^ 2) := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  set N := ⌊Real.exp (2 * a)⌋₊ with hNdef
  set Q : ℝ → ℂ := fun ξ => primePolynomial f N (ξ + ξ₀) with hQ
  set P : ℝ → ℝ := fun ξ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 with hP
  have hPi : Integrable P := by
    refine (integrable_pairTransform hη hηc).re.congr (Eventually.of_forall fun ξ => ?_)
    simp only [pairTransform_ofReal hη hηc ξ, RCLike.re_to_complex, Complex.ofReal_re, hP]
  have hPc : Continuous P := by
    have h := Complex.continuous_re.comp ((differentiable_pairTransform hη hηc).continuous.comp
      Complex.continuous_ofReal)
    refine h.congr fun ξ => ?_
    simp only [Function.comp_apply, pairTransform_ofReal hη hηc ξ, Complex.ofReal_re, hP]
  have hQc : Continuous Q := by
    simp only [hQ, primePolynomial]
    exact (continuous_expSum _ _ _).comp (continuous_id.add continuous_const)
  set C := ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖ with hC
  have hQb : ∀ ξ, ‖Q ξ‖ ≤ C := fun ξ => norm_expSum_le _ _ _ _
  set G : ℝ → ℝ := fun ξ => P ξ * ‖Q ξ‖ ^ 2 / A₀ ^ 2 with hG
  have hG0 : ∀ ξ, 0 ≤ G ξ := fun ξ => by positivity
  have hGi : Integrable G := by
    refine (hPi.mul_const (C ^ 2 / A₀ ^ 2)).mono'
      ((hPc.mul (hQc.norm.pow 2)).div_const _).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (hG0 ξ)]
    have hP0 : 0 ≤ P ξ := sq_nonneg _
    have hQ2 : ‖Q ξ‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hQb ξ) 2
    show P ξ * ‖Q ξ‖ ^ 2 / A₀ ^ 2 ≤ P ξ * (C ^ 2 / A₀ ^ 2)
    rw [mul_div_assoc]
    gcongr
  have hGint : ∫ ξ, G ξ = (∫ t, ‖η t‖ ^ 2) * primeVariance f N / A₀ ^ 2 := by
    have hvar := integral_windowed_sq_deviation_eq ha hf hfs hη hηs hX ξ₀
    have hdev : ∀ ξ : ℝ, ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
        archPart f (ξ + ξ₀)‖ = ‖Q ξ‖ := by
      intro ξ
      rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, sub_sub_cancel_left, norm_neg]
    simp_rw [hdev] at hvar
    simp only [hG, integral_div]
    rw [hvar]
  rw [← hGint, ofReal_integral_eq_lintegral_ofReal hGi (Eventually.of_forall hG0)]
  refine lintegral_mono fun ξ => ?_
  by_cases hξ : ξ ∈ U ∩ {ξ | (zetaZeroConfig.W (heightShift (ξ + ξ₀) f)
      (heightShift (ξ + ξ₀) f)).re < 0}
  · rw [Set.indicator_of_mem hξ]
    refine ENNReal.ofReal_le_ofReal ?_
    obtain ⟨hU', hneg⟩ := hξ
    simp only [Set.mem_setOf_eq] at hneg
    have hA := hU ξ hU'
    rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, Complex.sub_re] at hneg
    have hre : A₀ < (Q ξ).re := by simp only [hQ]; linarith
    have hQn : A₀ ≤ ‖Q ξ‖ := le_trans hre.le (Complex.re_le_norm _)
    have hratio : 1 ≤ ‖Q ξ‖ ^ 2 / A₀ ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hA₀.le hQn 2
    have hP0 : 0 ≤ P ξ := sq_nonneg _
    calc ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 = P ξ * 1 := by rw [mul_one]
      _ ≤ P ξ * (‖Q ξ‖ ^ 2 / A₀ ^ 2) := mul_le_mul_of_nonneg_left hratio hP0
      _ = G ξ := by rw [hG]; ring
  · rw [Set.indicator_of_notMem hξ]
    exact bot_le

/-- **Most heights are positive, explicitly.** Let `Ξ > 0` be such that
`A₀ = (log(1 + πΞ/4) − 10 − 2S(a))‖f‖² − B_f²/(8(1 + πΞ))` is positive. Then the heights
`ξ + ξ₀` with `|ξ + ξ₀| ≥ Ξ` and `Re W_ζ(S_{ξ+ξ₀} f, S_{ξ+ξ₀} f) < 0` carry window weight at most
`‖η‖² V_f/A₀²`. -/
theorem lintegral_bad_heights_le_of_height {a r Ξ : ℝ} (ha : 0 ≤ a) {f η : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-r) r) (hX : 2 * r * Real.exp (2 * a) ≤ 1) (ξ₀ : ℝ) (hΞ : 0 ≤ Ξ)
    (hA₀ : 0 < (Real.log (1 + π * Ξ / 4) - 10 - 2 * pairEnergy (1 / 2) a) * (∫ t, ‖f t‖ ^ 2) -
      (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * Ξ))) :
    ∫⁻ ξ, ({ξ | Ξ ≤ |ξ + ξ₀|} ∩ {ξ | (zetaZeroConfig.W (heightShift (ξ + ξ₀) f)
        (heightShift (ξ + ξ₀) f)).re < 0}).indicator
        (fun ξ => ENNReal.ofReal (‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2)) ξ ≤
      ENNReal.ofReal ((∫ t, ‖η t‖ ^ 2) * primeVariance f ⌊Real.exp (2 * a)⌋₊ /
        ((Real.log (1 + π * Ξ / 4) - 10 - 2 * pairEnergy (1 / 2) a) * (∫ t, ‖f t‖ ^ 2) -
          (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * Ξ))) ^ 2) := by
  refine lintegral_bad_heights_le ha hf hfs hη hηs hX ξ₀ hA₀ fun ξ hξ => ?_
  simp only [Set.mem_setOf_eq] at hξ
  refine le_trans ?_ (re_archPart_ge ha hf hfs (ξ + ξ₀))
  have hN0 : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hlog : Real.log (1 + π * Ξ / 4) ≤ Real.log (1 + π * |ξ + ξ₀| / 4) :=
    Real.log_le_log (by positivity) (by gcongr)
  have htail : (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ + ξ₀|)) ≤
      (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * Ξ)) := by
    gcongr
  have hmul := mul_le_mul_of_nonneg_right (sub_le_sub_right (sub_le_sub_right hlog 10)
    (2 * pairEnergy (1 / 2) a)) hN0
  linarith

end GaloisForLFunctions.SquareRootThreshold

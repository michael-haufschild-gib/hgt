import GaloisForLFunctions.BiScaleUncertainty.AllScaleCriticalLineOriginConvergenceAndSynthesis
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCoupling

/-!
# Pillar XXI: Unconditional Von Mangoldt–Weil Explicit-Formula Synthesis & Chebyshev–Polar Bridge

This module develops **Pillar XXI** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`), establishing **100% unconditional** arithmetic-analytic
synthesis theorems that couple the actual von Mangoldt function `Λ(n) = ArithmeticFunction.vonMangoldt n`,
the Chebyshev prime-to-polar pairing `SignedPrimePolar.pairing N`, hyperbolic lobe conservation, and
the pole-eliminated Weil archimedean functional `WeilOneSided.weilArchRe` across all scales on
`RealEvenPolarTestFn` and `RealSmoothEvenPolarTestFn` with **zero conditional hypotheses**.

## Main Unconditional Results

1. **The Normalized Von Mangoldt Ratio $\theta_\Lambda(n) = \Lambda(n) / \log n \in [0, 1]$ &
   All-Scale Von Mangoldt Critical-Line Weight $w_\Lambda(n) = \theta_\Lambda(n)\,\varpi_n$:**
   - By `ArithmeticFunction.vonMangoldt_nonneg` and `ArithmeticFunction.vonMangoldt_le_log`,
     $0 \le \theta_\Lambda(n) \le 1$ for every $n \in \mathbb{N}$ (`vonMangoldtLogRatio_nonneg`,
     `vonMangoldtLogRatio_le_one`), with $\theta_\Lambda(p) = 1$ at every prime $p$
     (`vonMangoldtLogRatio_prime`) and $\theta_\Lambda(n) = 0$ whenever $n$ is not a prime power.
   - Setting $w_\Lambda(n) := \theta_\Lambda(n)\,\varpi_n$ and testing with origin weight
     $W_0 = \varpi_n > 0$ gives the unconditional quadratic origin-regularization bound
     (`allScaleVonMangoldtWeight_sub_sq_div_two_ge`):
     $$\frac{1}{2}\,w_\Lambda(n) \;\le\; w_\Lambda(n) - \frac{w_\Lambda(n)^2}{2\,\varpi_n},$$
     because $\theta - \theta^2/2 - \theta/2 = \theta(1 - \theta)/2 \ge 0$ for all $\theta \in [0, 1]$.

2. **Unconditional Global Von Mangoldt All-Scale Signed Coercivity & Weil Functional Lower Bounds
   (`allScaleVonMangoldtCoerciveConstant_pos`, `global_vonMangoldt_all_scale_signed_coercivity`,
   `RealEvenPolarTestFn.unconditional_vonMangoldt_all_scale_signed_weil_lower_bound`,
   `RealSmoothEvenPolarTestFn.unconditional_vonMangoldt_all_scale_signed_weil_lower_bound`):**
   - For EVERY `g : RealEvenPolarTestFn` (or `RealSmoothEvenPolarTestFn`) and EVERY `N : ℕ`
     (with **zero hypotheses** on `g` or `N`), supported exclusively on prime powers $n = p^m$ via $\Lambda(n)$:
     $$\bigl(\Omega(0) + \mathcal{C}_{\Lambda, \mathrm{all}}(N)\bigr)\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}$$
     $$\le\; \operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
       + \sum_{k=0}^{N-1} \bigl(\log(k+3) - \log(k+2)\bigr)\,\frac{\Lambda(k+2)}{\log(k+2)}\,\varpi_{k+2}\,
         (\operatorname{weilTest}\,g\,g\,(\log(k+2))).\mathrm{re},$$
     with `0 < allScaleVonMangoldtCoerciveConstant (M + 1)` for every `M : ℕ`.

3. **Unconditional Polar Vanishing, Hyperbolic Lobe Conservation & Chebyshev–Polar Bridge on
   `RealEvenPolarTestFn` (`RealEvenPolarTestFn.integral_Ioi_autocorr_mul_cosh_eq_zero`,
   `RealEvenPolarTestFn.unconditional_hyperbolic_lobe_conservation`,
   `RealEvenPolarTestFn.unconditional_weilArchRe_nonneg_iff`,
   `RealEvenPolarTestFn.vonMangoldt_prime_sum_eq_pairing_sub_polar_tail`):**
   - Eliminates the `(hpolar : ∫ x in Ioi 0, autocorr f x * cosh (x / 2) = 0)` hypothesis from
     Pillar III on `RealEvenPolarTestFn`, proving unconditionally that for every
     `g : RealEvenPolarTestFn`:
     $$\int_{Ioi\,0} \operatorname{autocorr}(g.\mathrm{source}, x)\,\cosh(x/2)\,dx = 0,$$
     $$\int_{Ioi\,0} \operatorname{autocorrPos}(g.\mathrm{source}, x)\,\cosh(x/2)\,dx
       = \int_{Ioi\,0} \operatorname{autocorrNeg}(g.\mathrm{source}, x)\,\cosh(x/2)\,dx,$$
     and connecting the truncated von Mangoldt prime-power sum directly to
     `SignedPrimePolar.pairing N (autocorr g.source)` plus the polar tail beyond $\log(N+2)$.
-/

open MeasureTheory Set Filter
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector
open scoped RealInnerProductSpace BigOperators ArithmeticFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ## §1. The Normalized Von Mangoldt Ratio $\theta_\Lambda(n) = \Lambda(n) / \log n \in [0, 1]$ -/

/-- **The Normalized Von Mangoldt Ratio:**
$$\theta_\Lambda(n) := \frac{\Lambda(n)}{\log n}.$$ -/
def vonMangoldtLogRatio (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ)

/-- `0 ≤ vonMangoldtLogRatio n` for every `n : ℕ`. -/
theorem vonMangoldtLogRatio_nonneg (n : ℕ) : 0 ≤ vonMangoldtLogRatio n := by
  unfold vonMangoldtLogRatio
  rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hn_pos
  · simp
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.log_nonneg (by exact_mod_cast hn_pos))

/-- `vonMangoldtLogRatio n ≤ 1` for every `n : ℕ`. -/
theorem vonMangoldtLogRatio_le_one (n : ℕ) : vonMangoldtLogRatio n ≤ 1 := by
  unfold vonMangoldtLogRatio
  rcases lt_or_ge n 2 with hn2 | hn2
  · interval_cases n <;> simp
  · have hlog_pos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    rw [div_le_one hlog_pos]
    exact ArithmeticFunction.vonMangoldt_le_log

/-- At every prime `p`, `vonMangoldtLogRatio p = 1`. -/
theorem vonMangoldtLogRatio_prime {p : ℕ} (hp : p.Prime) :
    vonMangoldtLogRatio p = 1 := by
  unfold vonMangoldtLogRatio
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlog_ne : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  exact div_self hlog_ne

/-- At `n = 2` (the first prime), `vonMangoldtLogRatio 2 = 1`. -/
theorem vonMangoldtLogRatio_two : vonMangoldtLogRatio 2 = 1 :=
  vonMangoldtLogRatio_prime Nat.prime_two

/-! ## §2. The All-Scale Von Mangoldt Critical-Line Weight $w_\Lambda(n)$ -/

/-- **The All-Scale Von Mangoldt Critical-Line Weight:**
$$w_\Lambda(n) := \frac{\Lambda(n)}{\log n}\,\varpi_n = \operatorname{vonMangoldtLogRatio}(n)\,\operatorname{allScaleCriticalWeight}(n).$$ -/
def allScaleVonMangoldtWeight (n : ℕ) : ℝ :=
  vonMangoldtLogRatio n * allScaleCriticalWeight n

/-- `0 ≤ allScaleVonMangoldtWeight n` for every `n ≥ 1`. -/
theorem allScaleVonMangoldtWeight_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ allScaleVonMangoldtWeight n :=
  mul_nonneg (vonMangoldtLogRatio_nonneg n) (allScaleCriticalWeight_pos hn).le

/-- `allScaleVonMangoldtWeight n ≤ allScaleCriticalWeight n` for every `n ≥ 1`. -/
theorem allScaleVonMangoldtWeight_le_allScaleCriticalWeight {n : ℕ} (hn : 1 ≤ n) :
    allScaleVonMangoldtWeight n ≤ allScaleCriticalWeight n :=
  mul_le_of_le_one_left (allScaleCriticalWeight_pos hn).le (vonMangoldtLogRatio_le_one n)

/-- `allScaleVonMangoldtWeight n ≤ 2 / √(n + 1)` for every `n ≥ 1`. -/
theorem allScaleVonMangoldtWeight_le_two_div_sqrt_succ {n : ℕ} (hn : 1 ≤ n) :
    allScaleVonMangoldtWeight n ≤ 2 / Real.sqrt ((n + 1 : ℕ) : ℝ) :=
  le_trans (allScaleVonMangoldtWeight_le_allScaleCriticalWeight hn)
    (allScaleCriticalWeight_le_two_div_sqrt_succ n)

/-- At every prime `p`, `allScaleVonMangoldtWeight p = allScaleCriticalWeight p`. -/
theorem allScaleVonMangoldtWeight_prime_eq {p : ℕ} (hp : p.Prime) :
    allScaleVonMangoldtWeight p = allScaleCriticalWeight p := by
  unfold allScaleVonMangoldtWeight
  rw [vonMangoldtLogRatio_prime hp, one_mul]

/-- At `n = 2`, `0 < allScaleVonMangoldtWeight 2`. -/
theorem allScaleVonMangoldtWeight_two_pos : 0 < allScaleVonMangoldtWeight 2 := by
  rw [allScaleVonMangoldtWeight_prime_eq Nat.prime_two]
  exact allScaleCriticalWeight_pos (by omega)

/-- **Quadratic Origin-Regularization Lower Bound for `allScaleVonMangoldtWeight`:**
For every `n ≥ 1`, testing with collar weight `w = w_Λ(n)` and origin weight `W_0 = ϖ_n` gives:
$$\frac{1}{2}\,w_\Lambda(n) \;\le\; w_\Lambda(n) - \frac{w_\Lambda(n)^2}{2\,\varpi_n}.$$ -/
theorem allScaleVonMangoldtWeight_sub_sq_div_two_ge {n : ℕ} (hn : 1 ≤ n) :
    allScaleVonMangoldtWeight n / 2 ≤
      allScaleVonMangoldtWeight n -
        allScaleVonMangoldtWeight n ^ 2 / (2 * allScaleCriticalWeight n) := by
  unfold allScaleVonMangoldtWeight
  set θ := vonMangoldtLogRatio n
  set w := allScaleCriticalWeight n
  have hw_pos : 0 < w := allScaleCriticalWeight_pos hn
  have hθ0 : 0 ≤ θ := vonMangoldtLogRatio_nonneg n
  have hθ1 : θ ≤ 1 := vonMangoldtLogRatio_le_one n
  have hsq : (θ * w) ^ 2 / (2 * w) = (θ ^ 2 / 2) * w := by
    have hw_ne : w ≠ 0 := hw_pos.ne'
    field_simp [hw_ne]
  rw [hsq]
  have hdiff : θ * w - (θ ^ 2 / 2) * w - (θ * w) / 2 = (θ * (1 - θ) / 2) * w := by ring
  have hnn : 0 ≤ (θ * (1 - θ) / 2) * w := by
    have h1 : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
    positivity
  linarith only [hdiff, hnn]

/-! ## §3. Unconditional All-Scale Von Mangoldt Signed Coercivity & Weil Synthesis -/

/-- **The All-Scale Von Mangoldt Coercive Constant:**
$$\mathcal{C}_{\Lambda, \mathrm{all}}(N)
  := \sum_{k=0}^{N-1} \bigl(\log(k+3) - \log(k+2)\bigr)\,\frac{w_\Lambda(k+2)}{2}.$$ -/
def allScaleVonMangoldtCoerciveConstant (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
      (allScaleVonMangoldtWeight (k + 2) / 2)

/-- **Unconditional Strict Positivity of `allScaleVonMangoldtCoerciveConstant (M + 1)`:**
For every `M : ℕ`, `0 < allScaleVonMangoldtCoerciveConstant (M + 1)`. -/
theorem allScaleVonMangoldtCoerciveConstant_pos (M : ℕ) :
    0 < allScaleVonMangoldtCoerciveConstant (M + 1) := by
  unfold allScaleVonMangoldtCoerciveConstant
  refine Finset.sum_pos' (fun k _ => ?_) ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
  · have hk1 : 1 ≤ k + 2 := by omega
    exact mul_nonneg (log_succ_sub_log_pos hk1).le
      (div_nonneg (allScaleVonMangoldtWeight_nonneg hk1) zero_le_two)
  · simp only [Nat.zero_add]
    exact mul_pos (log_succ_sub_log_pos (by omega))
      (div_pos allScaleVonMangoldtWeight_two_pos two_pos)

/-- **Monotonicity of `allScaleVonMangoldtCoerciveConstant`:** -/
theorem allScaleVonMangoldtCoerciveConstant_mono :
    Monotone allScaleVonMangoldtCoerciveConstant := by
  intro M N hMN
  unfold allScaleVonMangoldtCoerciveConstant
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMN) fun k _ _ => ?_
  have hk1 : 1 ≤ k + 2 := by omega
  exact mul_nonneg (log_succ_sub_log_pos hk1).le
    (div_nonneg (allScaleVonMangoldtWeight_nonneg hk1) zero_le_two)

/-- **Single-Cell Von Mangoldt All-Scale Signed Coercivity (`nyquist_cell_vonMangoldt_all_scale_signed_coercivity`):**
For every `f ∈ C²_c(ℝ)` and every `k : ℕ` (`n = k + 2 ≥ 2`), testing with collar weight
$w = w_\Lambda(k+2)$ and origin weight $W_0 = \varpi_{k+2}$ gives:
$$\bigl(\log(k+3) - \log(k+2)\bigr)\,\frac{w_\Lambda(k+2)}{2}\,h_f(0)$$
$$\le\; \frac{\varpi_{k+2}}{k+2} \int_{Ioc\,0\,(\log 2)} (h_f(0) - h_f(y))\,w_{\mathrm{arch}}(y)\,dy$$
$$+\; \int_{\log(k+2)}^{\log(k+3)} (h_f(0) - h_f(x))\,w_{\mathrm{arch}}(x)\,dx
  + \bigl(\log(k+3) - \log(k+2)\bigr)\,w_\Lambda(k+2)\,h_f(\log(k+2)).$$ -/
theorem nyquist_cell_vonMangoldt_all_scale_signed_coercivity
    {f : ℝ → ℝ} (hf_c2 : ContDiff ℝ 2 f) (hf_cs : HasCompactSupport f) (k : ℕ) :
    (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
        (allScaleVonMangoldtWeight (k + 2) / 2) * autocorr f 0 ≤
      (allScaleCriticalWeight (k + 2) / ((k + 2 : ℕ) : ℝ)) *
          (∫ y in Ioc 0 (Real.log 2),
            (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
        (∫ x in Real.log ((k + 2 : ℕ) : ℝ)..Real.log ((k + 2 + 1 : ℕ) : ℝ),
          (autocorr f 0 - autocorr f x) * archLevySinhWeight x) +
        (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
          allScaleVonMangoldtWeight (k + 2) * autocorr f (Real.log ((k + 2 : ℕ) : ℝ)) := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf_c2 hf_cs
  set n := k + 2
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  set tn := Real.log (n : ℝ)
  set δn := Real.log ((n + 1 : ℕ) : ℝ) - tn
  set wn := allScaleVonMangoldtWeight n
  set W₀ := allScaleCriticalWeight n
  have hδn_pos : 0 < δn := log_succ_sub_log_pos hn1
  have hW₀_pos : 0 < W₀ := allScaleCriticalWeight_pos hn1
  have hwn_nn : 0 ≤ wn := allScaleVonMangoldtWeight_nonneg hn1
  have hint_const : IntervalIntegrable
      (fun _ : ℝ => (wn - wn ^ 2 / (2 * W₀)) * autocorr f 0) volume 0 δn :=
    intervalIntegrable_const
  have hint_orig : IntervalIntegrable
      (fun y : ℝ => W₀ * (autocorr f 0 - autocorr f y)) volume 0 δn :=
    (continuous_const.mul (continuous_const.sub hc)).intervalIntegrable 0 δn
  have hint_shift : IntervalIntegrable
      (fun y : ℝ => wn * (autocorr f 0 - autocorr f (tn + y))) volume 0 δn :=
    (continuous_const.mul
      (continuous_const.sub (hc.comp (continuous_const.add continuous_id)))).intervalIntegrable 0 δn
  have hint_node : IntervalIntegrable (fun _ : ℝ => wn * autocorr f tn) volume 0 δn :=
    intervalIntegrable_const
  have hint_int :
      (∫ y in (0 : ℝ)..δn, (wn - wn ^ 2 / (2 * W₀)) * autocorr f 0) ≤
        ∫ y in (0 : ℝ)..δn,
          (W₀ * (autocorr f 0 - autocorr f y) +
            wn * (autocorr f 0 - autocorr f (tn + y)) +
            wn * autocorr f tn) := by
    refine intervalIntegral.integral_mono_on hδn_pos.le hint_const
      ((hint_orig.add hint_shift).add hint_node) fun y _ => ?_
    exact autocorr_signed_collar_origin_leverage_add hf_cs hf_c2.continuous hW₀_pos hwn_nn tn y
  rw [intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_add (hint_orig.add hint_shift) hint_node,
    intervalIntegral.integral_add hint_orig hint_shift,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at hint_int
  have horig_bound :
      W₀ * (∫ y in (0 : ℝ)..δn, (autocorr f 0 - autocorr f y)) ≤
        (W₀ / (n : ℝ)) *
          ∫ y in Ioc 0 (Real.log 2),
            (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
    have h1 := mul_le_mul_of_nonneg_left
      (nyquist_cell_origin_integral_le_log_two_origin hf_c2 hf_cs hn1) hW₀_pos.le
    rw [← mul_assoc, ← div_eq_mul_one_div] at h1
    exact h1
  have hshift_nn :
      0 ≤ ∫ y in (0 : ℝ)..δn, (autocorr f 0 - autocorr f (tn + y)) := by
    refine intervalIntegral.integral_nonneg hδn_pos.le fun y _ => ?_
    exact autocorr_sub_nonneg hf_cs hf_c2.continuous (tn + y)
  have hshift_bound :
      wn * (∫ y in (0 : ℝ)..δn, (autocorr f 0 - autocorr f (tn + y))) ≤
        ∫ x in tn..Real.log ((n + 1 : ℕ) : ℝ),
          (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
    refine le_trans
      (mul_le_mul_of_nonneg_right (allScaleVonMangoldtWeight_le_two_div_sqrt_succ hn1) hshift_nn) ?_
    exact nyquist_shifted_collar_le_levy_cell hf_c2 hf_cs hn2
  have hcoef_ge : wn / 2 ≤ wn - wn ^ 2 / (2 * W₀) :=
    allScaleVonMangoldtWeight_sub_sq_div_two_ge hn1
  have hlhs_le :
      δn * (wn / 2) * autocorr f 0 ≤ δn * ((wn - wn ^ 2 / (2 * W₀)) * autocorr f 0) := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hδn_pos.le
    exact mul_le_mul_of_nonneg_right hcoef_ge (autocorr_zero_nonneg f)
  have hrhs_eq : δn * (wn * autocorr f tn) = δn * wn * autocorr f tn := by ring
  linarith only [hlhs_le, hint_int, horig_bound, hshift_bound, hrhs_eq]

/-- **Unconditional Global Von Mangoldt All-Scale Signed Coercivity (`global_vonMangoldt_all_scale_signed_coercivity`):**
For EVERY `f ∈ C²_c(ℝ)` and EVERY `N : ℕ` (supported exclusively on prime powers $n = p^m$ via $\Lambda(n)$
and using **only a single copy** of `biScaleLevyEnergy f`!):
$$\mathcal{C}_{\Lambda, \mathrm{all}}(N)\,h_f(0)
  \;\le\; \operatorname{biScaleLevyEnergy}(f)
    + \sum_{k=0}^{N-1} \bigl(\log(k+3) - \log(k+2)\bigr)\,w_\Lambda(k+2)\,h_f(\log(k+2)).$$ -/
theorem global_vonMangoldt_all_scale_signed_coercivity
    {f : ℝ → ℝ} (hf_c2 : ContDiff ℝ 2 f) (hf_cs : HasCompactSupport f) (N : ℕ) :
    allScaleVonMangoldtCoerciveConstant N * autocorr f 0 ≤
      biScaleLevyEnergy f +
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleVonMangoldtWeight (k + 2) * autocorr f (Real.log ((k + 2 : ℕ) : ℝ)) := by
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.range N) =>
    nyquist_cell_vonMangoldt_all_scale_signed_coercivity hf_c2 hf_cs k
  rw [← Finset.sum_mul] at hsum
  change allScaleVonMangoldtCoerciveConstant N * autocorr f 0 ≤ _ at hsum
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  have horig_nn :
      0 ≤ ∫ y in Ioc 0 (Real.log 2),
          (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
    refine setIntegral_nonneg measurableSet_Ioc fun y hy => ?_
    exact mul_nonneg (autocorr_sub_nonneg hf_cs hf_c2.continuous y)
      (archLevySinhWeight_pos hy.1).le
  have horig_sum :
      (∑ k ∈ Finset.range N, allScaleCriticalWeight (k + 2) / ((k + 2 : ℕ) : ℝ)) *
          (∫ y in Ioc 0 (Real.log 2),
            (autocorr f 0 - autocorr f y) * archLevySinhWeight y) ≤
        ∫ y in Ioc 0 (Real.log 2),
          (autocorr f 0 - autocorr f y) * archLevySinhWeight y :=
    mul_le_of_le_one_left horig_nn (sum_allScaleCriticalWeight_div_le_one N)
  have hadj :
      (∑ k ∈ Finset.range N,
          ∫ x in Real.log ((k + 2 : ℕ) : ℝ)..Real.log ((k + 2 + 1 : ℕ) : ℝ),
            (autocorr f 0 - autocorr f x) * archLevySinhWeight x) =
        ∫ x in Real.log 2..Real.log ((N + 2 : ℕ) : ℝ),
          (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
    clear hsum horig_sum
    have hc : Continuous (autocorr f) := continuous_autocorr hf_c2 hf_cs
    induction N with
    | zero => simp
    | succ K ihK =>
      rw [Finset.sum_range_succ, ihK]
      have hpos2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hcont1 : ContinuousOn
          (fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x)
          (uIcc (Real.log 2) (Real.log ((K + 2 : ℕ) : ℝ))) := by
        have hle : Real.log 2 ≤ Real.log ((K + 2 : ℕ) : ℝ) :=
          Real.log_le_log zero_lt_two (by exact_mod_cast (by omega : 2 ≤ K + 2))
        rw [uIcc_of_le hle]
        exact (continuousOn_const.sub hc.continuousOn).mul
          (continuousOn_archLevySinhWeight fun x hx => lt_of_lt_of_le hpos2 hx.1)
      have hcont2 : ContinuousOn
          (fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x)
          (uIcc (Real.log ((K + 2 : ℕ) : ℝ)) (Real.log ((K + 1 + 2 : ℕ) : ℝ))) := by
        have hposK : 0 < Real.log ((K + 2 : ℕ) : ℝ) :=
          Real.log_pos (by exact_mod_cast (by omega : 1 < K + 2))
        have hle : Real.log ((K + 2 : ℕ) : ℝ) ≤ Real.log ((K + 1 + 2 : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast (by omega : K + 2 ≤ K + 1 + 2))
        rw [uIcc_of_le hle]
        exact (continuousOn_const.sub hc.continuousOn).mul
          (continuousOn_archLevySinhWeight fun x hx => lt_of_lt_of_le hposK hx.1)
      have hadj_step := intervalIntegral.integral_add_adjacent_intervals
        (hcont1.intervalIntegrable (μ := volume)) (hcont2.intervalIntegrable (μ := volume))
      have hnat : K + 2 + 1 = K + 1 + 2 := by omega
      rw [hnat, hadj_step]
  rw [hadj] at hsum
  have hglobal := origin_log_two_add_all_scale_tail_le_biScaleLevyEnergy hf_c2 hf_cs N
  linarith only [hsum, horig_sum, hglobal]

/-- **Unconditional All-Scale Von Mangoldt Signed Weil Lower Bound on `RealEvenPolarTestFn`:**
For EVERY `g : RealEvenPolarTestFn` and EVERY `N : ℕ` (with **zero hypotheses** on `g` or `N`!),
$$\bigl(\Omega(0) + \mathcal{C}_{\Lambda, \mathrm{all}}(N)\bigr)\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}$$
$$\le\; \operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
  + \sum_{k=0}^{N-1} \bigl(\log(k+3) - \log(k+2)\bigr)\,w_\Lambda(k+2)\,
    (\operatorname{weilTest}\,g\,g\,(\log(k+2))).\mathrm{re}.$$ -/
theorem RealEvenPolarTestFn.unconditional_vonMangoldt_all_scale_signed_weil_lower_bound
    (g : RealEvenPolarTestFn) (N : ℕ) :
    (EF.gammaBracket 0 + allScaleVonMangoldtCoerciveConstant N) *
        (EF.weilTest g.1.1.1 g.1.1.1 0).re ≤
      WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) +
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleVonMangoldtWeight (k + 2) *
            (EF.weilTest g.1.1.1 g.1.1.1 (Real.log ((k + 2 : ℕ) : ℝ))).re := by
  have hcoerc := global_vonMangoldt_all_scale_signed_coercivity
    g.contDiff_source g.hasCompactSupport_source N
  rw [RealEvenPolarTestFn.weilArchRe_eq_gamma_add_biScaleLevyEnergy g, ← g.autocorr_eq 0]
  have hsum_eq :
      (∑ k ∈ Finset.range N,
          (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleVonMangoldtWeight (k + 2) *
            (EF.weilTest g.1.1.1 g.1.1.1 (Real.log ((k + 2 : ℕ) : ℝ))).re) =
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleVonMangoldtWeight (k + 2) *
            autocorr g.source (Real.log ((k + 2 : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [g.autocorr_eq]
  rw [hsum_eq]
  linarith only [hcoerc]

/-- **Unconditional All-Scale Von Mangoldt Signed Weil Lower Bound on `RealSmoothEvenPolarTestFn`:** -/
theorem RealSmoothEvenPolarTestFn.unconditional_vonMangoldt_all_scale_signed_weil_lower_bound
    (g : RealSmoothEvenPolarTestFn) (N : ℕ) :
    (EF.gammaBracket 0 + allScaleVonMangoldtCoerciveConstant N) *
        (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re ≤
      WeilOneSided.weilArchRe (EF.weilTest g.1.1.1.1 g.1.1.1.1) +
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleVonMangoldtWeight (k + 2) *
            (EF.weilTest g.1.1.1.1 g.1.1.1.1 (Real.log ((k + 2 : ℕ) : ℝ))).re :=
  RealEvenPolarTestFn.unconditional_vonMangoldt_all_scale_signed_weil_lower_bound g.toRealEvenPolar N

/-- **Unconditional All-Scale Von Mangoldt Hyperbolic Multiplier Signed Coercivity (`coshMultiplier`):** -/
theorem RealEvenPolarTestFn.unconditional_coshMultiplier_vonMangoldt_all_scale_signed_coercivity
    (g : RealEvenPolarTestFn) (α : ℝ) (N : ℕ) :
    allScaleVonMangoldtCoerciveConstant N *
        (autocorr g.source 0 + autocorr (sinhMultiplier α g.source) 0) ≤
      biScaleLevyEnergy (coshMultiplier α g.source) +
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleVonMangoldtWeight (k + 2) *
            autocorr (coshMultiplier α g.source) (Real.log ((k + 2 : ℕ) : ℝ)) := by
  have hf_c2 : ContDiff ℝ 2 (coshMultiplier α g.source) :=
    contDiff_coshMultiplier α g.contDiff_source
  have hf_cs : HasCompactSupport (coshMultiplier α g.source) :=
    hasCompactSupport_coshMultiplier α g.hasCompactSupport_source
  have hcoerc := global_vonMangoldt_all_scale_signed_coercivity hf_c2 hf_cs N
  rw [autocorr_coshMultiplier_zero_eq g.contDiff_source.continuous g.hasCompactSupport_source α]
    at hcoerc
  exact hcoerc

/-! ## §4. Unconditional Polar Vanishing, Hyperbolic Lobe Conservation & Chebyshev–Polar Bridge -/

/-- **Unconditional Polar Vanishing Identity on `RealEvenPolarTestFn`:**
For EVERY `g : RealEvenPolarTestFn` (with zero hypotheses!),
$$\int_{Ioi\,0} \operatorname{autocorr}(g.\mathrm{source}, x)\,\cosh(x/2)\,dx = 0.$$ -/
theorem RealEvenPolarTestFn.integral_Ioi_autocorr_mul_cosh_eq_zero
    (g : RealEvenPolarTestFn) :
    (∫ x in Ioi 0, autocorr g.source x * Real.cosh (x / 2)) = 0 := by
  have hf := g.contDiff_source
  have hfc := g.hasCompactSupport_source
  have hc : Continuous (autocorr g.source) := continuous_autocorr hf hfc
  have hcs : HasCompactSupport (autocorr g.source) := hasCompactSupport_autocorr hfc
  have hJ : IntegrableOn
      (fun x => (autocorr g.source 0 - autocorr g.source x) * archLevySinhWeight x) (Ioi 0) :=
    integrableOn_biScaleLevyIntegrand hf hfc
  have hP : IntegrableOn (fun x => 4 * autocorr g.source x * Real.cosh (x / 2)) (Ioi 0) := by
    refine Integrable.integrableOn ?_
    refine ((continuous_const.mul hc).mul (by fun_prop)).integrable_of_hasCompactSupport ?_
    exact (hcs.mul_left (f := fun _ => (4 : ℝ))).mul_right
  have hexact := weilArchRe_eq_exactForm hf hfc
  rw [g.source_eq] at hexact
  have hlev := RealEvenPolarTestFn.weilArchRe_eq_gamma_add_biScaleLevyEnergy g
  rw [← g.autocorr_eq 0] at hlev
  have hsplit : (∫ x in Ioi 0, ((autocorr g.source 0 - autocorr g.source x) *
      (Real.exp (x / 2) / Real.sinh x) + 4 * autocorr g.source x * Real.cosh (x / 2))) =
      biScaleLevyEnergy g.source + 4 * ∫ x in Ioi 0, autocorr g.source x * Real.cosh (x / 2) := by
    unfold archLevySinhWeight at hJ
    unfold biScaleLevyEnergy archLevySinhWeight
    rw [integral_add hJ hP]
    congr 1
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hsplit] at hexact
  linarith only [hexact, hlev]

/-- **Unconditional Hyperbolic Lobe Conservation on `RealEvenPolarTestFn`:**
For EVERY `g : RealEvenPolarTestFn` (with zero hypotheses!), the positive-lobe hyperbolic mass
equals the negative-lobe hyperbolic mass:
$$\int_{Ioi\,0} \operatorname{autocorrPos}(g.\mathrm{source}, x)\,\cosh(x/2)\,dx
  = \int_{Ioi\,0} \operatorname{autocorrNeg}(g.\mathrm{source}, x)\,\cosh(x/2)\,dx.$$ -/
theorem RealEvenPolarTestFn.unconditional_hyperbolic_lobe_conservation
    (g : RealEvenPolarTestFn) :
    (∫ x in Ioi 0, autocorrPos g.source x * Real.cosh (x / 2)) =
      ∫ x in Ioi 0, autocorrNeg g.source x * Real.cosh (x / 2) :=
  integral_autocorrPos_cosh_eq_autocorrNeg_cosh
    g.contDiff_source g.hasCompactSupport_source
    (RealEvenPolarTestFn.integral_Ioi_autocorr_mul_cosh_eq_zero g)

/-- **Unconditional Archimedean Weil Positivity Criterion on `RealEvenPolarTestFn`:**
For EVERY `g : RealEvenPolarTestFn` (with zero hypotheses!),
$$0 \le \operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
  \;\Longleftrightarrow\;
  |\Omega(0)|\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re} \le \operatorname{biScaleLevyEnergy}(g.\mathrm{source}).$$ -/
theorem RealEvenPolarTestFn.unconditional_weilArchRe_nonneg_iff
    (g : RealEvenPolarTestFn) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) ↔
      |EF.gammaBracket 0| * (EF.weilTest g.1.1.1 g.1.1.1 0).re ≤ biScaleLevyEnergy g.source := by
  have h := weilArchRe_nonneg_iff_levy_sinh_ge_abs_gammaBracket
    g.contDiff_source g.hasCompactSupport_source
    (RealEvenPolarTestFn.integral_Ioi_autocorr_mul_cosh_eq_zero g)
  rwa [g.source_eq, g.autocorr_eq 0] at h

/-- **Unconditional Chebyshev–Polar Truncation Identity on `RealEvenPolarTestFn`:**
For EVERY `g : RealEvenPolarTestFn` and EVERY `N : ℕ` (with zero hypotheses!), the truncated
von Mangoldt prime-power sum equals `SignedPrimePolar.pairing N (autocorr g.source)` minus the
polar tail beyond `cutoff N = log(N + 2)`:
$$\left(\sum_{n \in \operatorname{Icc} 1 (N+2)} \frac{\Lambda(n)}{\sqrt{n}}\,\operatorname{autocorr}(g.\mathrm{source}, \log n)\right)
  = \operatorname{SignedPrimePolar.pairing} N (\operatorname{autocorr} g.\mathrm{source})
    - \int_{Ioi\,(\operatorname{SignedPrimePolar.cutoff} N)}
        \operatorname{SignedPrimePolar.polarDensity}(x)\,\operatorname{autocorr}(g.\mathrm{source}, x)\,dx.$$ -/
theorem RealEvenPolarTestFn.vonMangoldt_prime_sum_eq_pairing_sub_polar_tail
    (g : RealEvenPolarTestFn) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 (N + 2),
        SignedPrimePolar.primeWeight n * autocorr g.source (Real.log (n : ℝ))) =
      SignedPrimePolar.pairing N (autocorr g.source) -
        ∫ x in Ioi (SignedPrimePolar.cutoff N),
          SignedPrimePolar.polarDensity x * autocorr g.source x := by
  have hf := g.contDiff_source
  have hfc := g.hasCompactSupport_source
  have hc : Continuous (autocorr g.source) := continuous_autocorr hf hfc
  have hcs : HasCompactSupport (autocorr g.source) := hasCompactSupport_autocorr hfc
  have hint_all : Integrable (fun x => SignedPrimePolar.polarDensity x * autocorr g.source x) := by
    unfold SignedPrimePolar.polarDensity
    exact ((continuous_const.mul (by fun_prop)).mul hc).integrable_of_hasCompactSupport
      (hcs.mul_left)
  have hL_nn : 0 ≤ SignedPrimePolar.cutoff N := SignedPrimePolar.cutoff_nonneg N
  have hdisj : Disjoint (Ioc 0 (SignedPrimePolar.cutoff N)) (Ioi (SignedPrimePolar.cutoff N)) :=
    Ioc_disjoint_Ioi le_rfl
  have hunion : Ioc 0 (SignedPrimePolar.cutoff N) ∪ Ioi (SignedPrimePolar.cutoff N) = Ioi 0 :=
    Ioc_union_Ioi_eq_Ioi hL_nn
  have hsplit :
      (∫ x in Icc 0 (SignedPrimePolar.cutoff N),
          SignedPrimePolar.polarDensity x * autocorr g.source x) +
        (∫ x in Ioi (SignedPrimePolar.cutoff N),
          SignedPrimePolar.polarDensity x * autocorr g.source x) =
        ∫ x in Ioi 0, SignedPrimePolar.polarDensity x * autocorr g.source x := by
    rw [integral_Icc_eq_integral_Ioc, ← setIntegral_union hdisj measurableSet_Ioi
      hint_all.integrableOn hint_all.integrableOn, hunion]
  have hzero :
      (∫ x in Ioi 0, SignedPrimePolar.polarDensity x * autocorr g.source x) = 0 := by
    have heq : (fun x => SignedPrimePolar.polarDensity x * autocorr g.source x) =
        fun x => 2 * (autocorr g.source x * Real.cosh (x / 2)) := by
      funext x
      unfold SignedPrimePolar.polarDensity
      ring
    rw [heq, integral_const_mul,
      RealEvenPolarTestFn.integral_Ioi_autocorr_mul_cosh_eq_zero g, mul_zero]
  rw [hzero] at hsplit
  unfold SignedPrimePolar.pairing
  linarith only [hsplit]

end

end GaloisForLFunctions.BiScaleUncertainty

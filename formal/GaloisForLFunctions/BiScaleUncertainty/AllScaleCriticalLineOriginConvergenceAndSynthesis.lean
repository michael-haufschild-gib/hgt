import GaloisForLFunctions.BiScaleUncertainty.SignedWeilFunctionalCoercivityAndRHBridge

/-!
# Pillar XX: The All-Scale Critical-Line $O(n^{-3/2})$ Origin-Budget Convergence Law & Unconditional Explicit-Formula Synthesis

This module develops **Pillar XX** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`), establishing the **All-Scale Critical-Line Origin-Budget
Convergence Law** and its **completely unconditional** explicit-formula synthesis across the entire
integer logarithmic grid $\{\log n : 2 \le n < N + 2\}$ from the first prime $\log 2$ up to any
cutoff $\log(N + 2)$ simultaneously.

## The Structural Breakthrough: Why $\sigma = 1/2$ Makes All-Scale Origin Sharing Converge

In Pillar XVIII (`MultiShellOriginBudgetAndGlobalPrimeCollarSynthesis`), a single dyadic shell
$[N, 2N)$ of $N$ Nyquist cells shared the origin collar by assigning each cell $1/N$ of the origin
budget. To couple **all scales simultaneously** from $n = 2$ to $n = N + 1$ across arbitrarily many
dyadic shells while still consuming **at most one copy** of `biScaleLevyEnergy f`, we introduce the
**Canonical All-Scale Critical-Line Weight**:
$$\varpi_n := \sqrt{2}\,n\left(\frac{1}{\sqrt{n}} - \frac{1}{\sqrt{n+1}}\right) \asymp \frac{1}{\sqrt{n+1}}.$$

This single canonical weight satisfies **four simultaneous exact properties**:

1. **Critical-Line Dominance (`allScaleCriticalWeight_le_two_div_sqrt_succ` & `allScaleCriticalWeight_le_archLevySinhWeight`):**
   Using the algebraic identity $1 - 2(ab - a^2) = (b - a)^2 \ge 0$ for $a = \sqrt{n}$,
   $b = \sqrt{n+1}$ ($b^2 - a^2 = 1$), we have
   $$\varpi_n = \sqrt{2}\,\frac{ab - a^2}{b} \le \frac{\sqrt{2}}{2\sqrt{n+1}} \le \frac{2}{\sqrt{n+1}}
     \le \operatorname{archLevySinhWeight}(\log(n+1)).$$
2. **Self-Matched Origin Regularization ($w_n = W_{0, n} = \varpi_n$):**
   Choosing both the collar weight $w_n$ and the origin weight $W_{0, n}$ equal to $\varpi_n$ yields
   an exact half-weight coercive coefficient at **every** integer node $n \ge 2$:
   $$\varpi_n - \frac{\varpi_n^2}{2\varpi_n} = \frac{1}{2}\,\varpi_n > 0.$$
3. **Exact Telescoping $O(n^{-3/2})$ Origin-Budget Conservation (`sum_allScaleCriticalWeight_div_le_one`):**
   Because the $n$-th Nyquist cell's origin integral carries the factor $1/n$ from
   `nyquist_cell_origin_integral_le_levy`, its share of the fixed first-prime origin window
   $(0, \log 2]$ is
   $$\frac{\varpi_n}{n} = \sqrt{2}\left(\frac{1}{\sqrt{n}} - \frac{1}{\sqrt{n+1}}\right) \asymp n^{-3/2},$$
   whose sum over all $n \in \{2, 3, \dots, N+1\}$ telescopes **exactly** to
   $$\sum_{k=0}^{N-1} \frac{\varpi_{k+2}}{k+2} = 1 - \frac{\sqrt{2}}{\sqrt{N+2}} \le 1.$$
4. **Disjoint First-Prime Origin + All-Scale Tail Partition (`global_all_scale_signed_coercivity`):**
   For every $n \ge 1$, $\Delta_n = \log(n+1) - \log n \le \log 2$, so every cell's origin collar
   lies in $(0, \log 2]$, while the adjacent shifted collars $[\log(k+2), \log(k+3)]$ tile
   $[\log 2, \log(N+2)] \subseteq (\log 2, \infty)$ without overlap. Together, they are bounded by
   **a single copy of `biScaleLevyEnergy f`**, yielding completely unconditional all-scale signed
   Weil lower bounds on `RealEvenPolarTestFn` and `RealSmoothEvenPolarTestFn`.
-/

open MeasureTheory Set Filter
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector
open scoped RealInnerProductSpace BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ## §1. The Canonical All-Scale Critical-Line Weight $\varpi_n$ -/

/-- **The Canonical All-Scale Critical-Line Weight:**
$$\varpi_n := \sqrt{2}\,n\left(\frac{1}{\sqrt{n}} - \frac{1}{\sqrt{n+1}}\right).$$ -/
def allScaleCriticalWeight (n : ℕ) : ℝ :=
  Real.sqrt 2 * (n : ℝ) * (1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt ((n + 1 : ℕ) : ℝ))

/-- For every `n ≥ 1`, `0 < 1 / √n - 1 / √(n + 1)`. -/
theorem inv_sqrt_sub_inv_sqrt_succ_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < 1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlt : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : n < n + 1)
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hsqrt_lt : Real.sqrt (n : ℝ) < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    Real.sqrt_lt_sqrt hn_pos.le hlt
  exact sub_pos.mpr (div_lt_div_of_pos_left one_pos hsqrt_pos hsqrt_lt)

/-- **Strict Positivity of `allScaleCriticalWeight n`:**
For every `n ≥ 1`, `0 < allScaleCriticalWeight n`. -/
theorem allScaleCriticalWeight_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < allScaleCriticalWeight n := by
  unfold allScaleCriticalWeight
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  exact mul_pos (mul_pos (Real.sqrt_pos.mpr two_pos) hn_pos)
    (inv_sqrt_sub_inv_sqrt_succ_pos hn)

/-- **Algebraic Upper Bound on `allScaleCriticalWeight n`:**
For every `n : ℕ`, `allScaleCriticalWeight n ≤ 2 / √(n + 1)`. -/
theorem allScaleCriticalWeight_le_two_div_sqrt_succ (n : ℕ) :
    allScaleCriticalWeight n ≤ 2 / Real.sqrt ((n + 1 : ℕ) : ℝ) := by
  unfold allScaleCriticalWeight
  set a := Real.sqrt (n : ℝ)
  set b := Real.sqrt ((n + 1 : ℕ) : ℝ)
  have hb_pos : 0 < b := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have ha2 : a ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hb2 : b ^ 2 = ((n + 1 : ℕ) : ℝ) := Real.sq_sqrt (Nat.cast_nonneg (n + 1))
  have hba : b ^ 2 - a ^ 2 = 1 := by
    rw [ha2, hb2]
    push_cast
    ring
  rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hn_pos
  · simp
    positivity
  · have ha_pos : 0 < a := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn_pos)
    have hfrac : (n : ℝ) * (1 / a - 1 / b) = (a * b - a ^ 2) / b := by
      rw [← ha2]
      field_simp [ha_pos.ne', hb_pos.ne']
    rw [mul_assoc, hfrac]
    have hab_le : a * b - a ^ 2 ≤ 1 / 2 := by
      have hsq : 0 ≤ (b - a) ^ 2 := sq_nonneg (b - a)
      nlinarith
    have hsqrt2_le : Real.sqrt 2 ≤ 2 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hnum : Real.sqrt 2 * ((a * b - a ^ 2) / b) ≤ (2 * (1 / 2)) / b := by
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ hb_pos.le
      have hdiff_nn : 0 ≤ a * b - a ^ 2 := by
        have hab : a ≤ b := Real.sqrt_le_sqrt (by exact_mod_cast (by omega : n ≤ n + 1))
        nlinarith
      exact mul_le_mul hsqrt2_le hab_le hdiff_nn zero_le_two
    refine le_trans hnum ?_
    refine div_le_div_of_nonneg_right (by norm_num) hb_pos.le

/-- **Dominance by `archLevySinhWeight` Across the Cell `(0, log (n + 1)]`:**
For every integer `n ≥ 1` and `x ∈ (0, log(n + 1)]`,
$$\varpi_n \le \operatorname{archLevySinhWeight}(x).$$ -/
theorem allScaleCriticalWeight_le_archLevySinhWeight {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx_pos : 0 < x) (hx_le : x ≤ Real.log ((n + 1 : ℕ) : ℝ)) :
    allScaleCriticalWeight n ≤ archLevySinhWeight x :=
  le_trans (allScaleCriticalWeight_le_two_div_sqrt_succ n)
    (two_div_sqrt_succ_le_archLevySinhWeight hn hx_pos hx_le)

/-! ## §2. Exact Telescoping $O(n^{-3/2})$ Origin-Budget Conservation Across All Scales -/

/-- Dividing `allScaleCriticalWeight n` by `n` gives the exact telescoping origin share
$$\frac{\varpi_n}{n} = \sqrt{2}\left(\frac{1}{\sqrt{n}} - \frac{1}{\sqrt{n+1}}\right).$$ -/
theorem allScaleCriticalWeight_div_eq {n : ℕ} (hn : 1 ≤ n) :
    allScaleCriticalWeight n / (n : ℝ) =
      Real.sqrt 2 * (1 / Real.sqrt (n : ℝ) - 1 / Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  unfold allScaleCriticalWeight
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn0]

/-- **Exact Telescoping Origin-Budget Identity Across $[2, N + 2)$:**
For every `N : ℕ`,
$$\sum_{k=0}^{N-1} \frac{\varpi_{k+2}}{k+2} = 1 - \frac{\sqrt{2}}{\sqrt{N+2}}.$$ -/
theorem sum_allScaleCriticalWeight_div_eq (N : ℕ) :
    (∑ k ∈ Finset.range N,
        allScaleCriticalWeight (k + 2) / ((k + 2 : ℕ) : ℝ)) =
      1 - Real.sqrt 2 / Real.sqrt ((N + 2 : ℕ) : ℝ) := by
  have hcongr :
      (∑ k ∈ Finset.range N,
          allScaleCriticalWeight (k + 2) / ((k + 2 : ℕ) : ℝ)) =
        ∑ k ∈ Finset.range N,
          (Real.sqrt 2 / Real.sqrt ((k + 2 : ℕ) : ℝ) -
            Real.sqrt 2 / Real.sqrt ((k + 1 + 2 : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [allScaleCriticalWeight_div_eq (by omega)]
    have hnat : k + 2 + 1 = k + 1 + 2 := by omega
    rw [hnat]
    ring
  rw [hcongr,
    Finset.sum_range_sub' (fun k => Real.sqrt 2 / Real.sqrt ((k + 2 : ℕ) : ℝ)) N]
  have h0 : ((0 + 2 : ℕ) : ℝ) = 2 := by norm_num
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr two_pos).ne'
  rw [h0, div_self h2]

/-- **Unconditional All-Scale Origin-Budget Bound (`≤ 1`):**
For every `N : ℕ`, the total origin-collar share across all cells $n \in [2, N+2)$ is at most `1`:
$$\sum_{k=0}^{N-1} \frac{\varpi_{k+2}}{k+2} \le 1.$$ -/
theorem sum_allScaleCriticalWeight_div_le_one (N : ℕ) :
    (∑ k ∈ Finset.range N,
        allScaleCriticalWeight (k + 2) / ((k + 2 : ℕ) : ℝ)) ≤ 1 := by
  rw [sum_allScaleCriticalWeight_div_eq]
  have hpos : 0 ≤ Real.sqrt 2 / Real.sqrt ((N + 2 : ℕ) : ℝ) := by positivity
  linarith

/-! ## §3. Disjoint First-Prime Origin Window & All-Scale Tail Partition -/

/-- For every integer `n ≥ 1`, the Nyquist cell width `log(n+1) - log n` is at most `log 2`
(since `n + 1 ≤ 2 n`). -/
theorem nyquist_step_le_log_two {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ Real.log 2 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [← Real.log_div (by positivity) hn_pos.ne']
  refine Real.log_le_log (div_pos (by positivity) hn_pos) ?_
  rw [div_le_iff₀ hn_pos]
  have hle : n + 1 ≤ 2 * n := by omega
  exact_mod_cast hle

/-- **All-Scale Origin Integral Bound Relative to the First-Prime Window `(0, log 2]`:**
For every `f ∈ C²_c(ℝ)` and every integer `n ≥ 1`,
$$\int_0^{\log(n+1) - \log n} (h_f(0) - h_f(y))\,dy
  \;\le\; \frac{1}{n} \int_{Ioc\,0\,(\log 2)} (h_f(0) - h_f(y))\,w_{\mathrm{arch}}(y)\,dy.$$ -/
theorem nyquist_cell_origin_integral_le_log_two_origin
    {f : ℝ → ℝ} (hf_c2 : ContDiff ℝ 2 f) (hf_cs : HasCompactSupport f)
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ y in (0 : ℝ)..(Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)),
        (autocorr f 0 - autocorr f y)) ≤
      (1 / (n : ℝ)) *
        ∫ y in Ioc 0 (Real.log 2),
          (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
  refine le_trans (nyquist_cell_origin_integral_le_levy hf_c2 hf_cs hn) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hint := integrableOn_biScaleLevyIntegrand hf_c2 hf_cs
  refine setIntegral_mono_set (hint.mono_set Ioc_subset_Ioi_self) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact mul_nonneg (autocorr_sub_nonneg hf_cs hf_c2.continuous y)
      (archLevySinhWeight_pos hy.1).le
  · exact Eventually.of_forall fun y hy => ⟨hy.1, le_trans hy.2 (nyquist_step_le_log_two hn)⟩

/-- **Disjoint First-Prime Origin + All-Scale Tail Bound by a Single `biScaleLevyEnergy`:**
For every `f ∈ C²_c(ℝ)` and every `N : ℕ`, the first-prime origin integral on `(0, log 2]` plus
the all-scale tail integral on `[log 2, log(N + 2)]` is bounded above by a **single copy** of
`biScaleLevyEnergy f`:
$$\int_{Ioc\,0\,(\log 2)} (h_f(0) - h_f(y))\,w_{\mathrm{arch}}(y)\,dy
  + \int_{\log 2}^{\log(N+2)} (h_f(0) - h_f(x))\,w_{\mathrm{arch}}(x)\,dx
  \;\le\; \operatorname{biScaleLevyEnergy}(f).$$ -/
theorem origin_log_two_add_all_scale_tail_le_biScaleLevyEnergy
    {f : ℝ → ℝ} (hf_c2 : ContDiff ℝ 2 f) (hf_cs : HasCompactSupport f) (N : ℕ) :
    (∫ y in Ioc 0 (Real.log 2),
        (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
      (∫ x in Real.log 2..Real.log ((N + 2 : ℕ) : ℝ),
        (autocorr f 0 - autocorr f x) * archLevySinhWeight x) ≤
      biScaleLevyEnergy f := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [← origin_add_tail_levy_eq_biScaleLevyEnergy hf_c2 hf_cs hlog2_pos]
  have hle : Real.log 2 ≤ Real.log ((N + 2 : ℕ) : ℝ) := by
    refine Real.log_le_log zero_lt_two ?_
    exact_mod_cast (by omega : 2 ≤ N + 2)
  rw [intervalIntegral.integral_of_le hle]
  have hint := integrableOn_biScaleLevyIntegrand hf_c2 hf_cs
  have htail_le :
      (∫ x in Ioc (Real.log 2) (Real.log ((N + 2 : ℕ) : ℝ)),
          (autocorr f 0 - autocorr f x) * archLevySinhWeight x) ≤
        ∫ x in Ioi (Real.log 2),
          (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
    refine setIntegral_mono_set
      (hint.mono_set (fun x hx => lt_trans hlog2_pos hx)) ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (autocorr_sub_nonneg hf_cs hf_c2.continuous x)
        (archLevySinhWeight_pos (lt_trans hlog2_pos hx)).le
    · exact Eventually.of_forall fun x hx => hx.1
  linarith

/-! ## §4. Unconditional All-Scale Signed Coercivity & Explicit-Formula Synthesis -/

/-- **The All-Scale Critical-Line Coercive Constant:**
$$\mathcal{C}_{\mathrm{all}}(N)
  := \sum_{k=0}^{N-1} \bigl(\log(k+3) - \log(k+2)\bigr)\,\frac{\varpi_{k+2}}{2}.$$ -/
def allScaleCoerciveConstant (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
      (allScaleCriticalWeight (k + 2) / 2)

/-- **Unconditional Strict Positivity of `allScaleCoerciveConstant (M + 1)`:**
For every `M : ℕ`, `0 < allScaleCoerciveConstant (M + 1)`. -/
theorem allScaleCoerciveConstant_pos (M : ℕ) :
    0 < allScaleCoerciveConstant (M + 1) := by
  unfold allScaleCoerciveConstant
  refine Finset.sum_pos (fun k _ => ?_) ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hk1 : 1 ≤ k + 2 := by omega
  exact mul_pos (log_succ_sub_log_pos hk1)
    (div_pos (allScaleCriticalWeight_pos hk1) two_pos)

/-- **Monotonicity of `allScaleCoerciveConstant`:**
As the cutoff `N` grows across arbitrarily many dyadic shells, `allScaleCoerciveConstant N` is
monotonically nondecreasing. -/
theorem allScaleCoerciveConstant_mono : Monotone allScaleCoerciveConstant := by
  intro M N hMN
  unfold allScaleCoerciveConstant
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMN) fun k _ _ => ?_
  have hk1 : 1 ≤ k + 2 := by omega
  exact mul_nonneg (log_succ_sub_log_pos hk1).le
    (div_nonneg (allScaleCriticalWeight_pos hk1).le zero_le_two)

/-- **Single-Cell All-Scale Signed Coercivity (`nyquist_cell_all_scale_signed_coercivity`):**
For every `f ∈ C²_c(ℝ)` and every `k : ℕ` (representing integer node `n = k + 2 ≥ 2`), testing with
$w = W_0 = \varpi_{k+2}$ gives:
$$\bigl(\log(k+3) - \log(k+2)\bigr)\,\frac{\varpi_{k+2}}{2}\,h_f(0)$$
$$\le\; \frac{\varpi_{k+2}}{k+2} \int_{Ioc\,0\,(\log 2)} (h_f(0) - h_f(y))\,w_{\mathrm{arch}}(y)\,dy$$
$$+\; \int_{\log(k+2)}^{\log(k+3)} (h_f(0) - h_f(x))\,w_{\mathrm{arch}}(x)\,dx
  + \bigl(\log(k+3) - \log(k+2)\bigr)\,\varpi_{k+2}\,h_f(\log(k+2)).$$ -/
theorem nyquist_cell_all_scale_signed_coercivity
    {f : ℝ → ℝ} (hf_c2 : ContDiff ℝ 2 f) (hf_cs : HasCompactSupport f) (k : ℕ) :
    (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
        (allScaleCriticalWeight (k + 2) / 2) * autocorr f 0 ≤
      (allScaleCriticalWeight (k + 2) / ((k + 2 : ℕ) : ℝ)) *
          (∫ y in Ioc 0 (Real.log 2),
            (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
        (∫ x in Real.log ((k + 2 : ℕ) : ℝ)..Real.log ((k + 2 + 1 : ℕ) : ℝ),
          (autocorr f 0 - autocorr f x) * archLevySinhWeight x) +
        (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
          allScaleCriticalWeight (k + 2) * autocorr f (Real.log ((k + 2 : ℕ) : ℝ)) := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf_c2 hf_cs
  set n := k + 2
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  set tn := Real.log (n : ℝ)
  set δn := Real.log ((n + 1 : ℕ) : ℝ) - tn
  set wn := allScaleCriticalWeight n
  have hδn_pos : 0 < δn := log_succ_sub_log_pos hn1
  have hwn_pos : 0 < wn := allScaleCriticalWeight_pos hn1
  have hint_const : IntervalIntegrable
      (fun _ : ℝ => (wn - wn ^ 2 / (2 * wn)) * autocorr f 0) volume 0 δn :=
    intervalIntegrable_const
  have hint_orig : IntervalIntegrable
      (fun y : ℝ => wn * (autocorr f 0 - autocorr f y)) volume 0 δn :=
    (continuous_const.mul (continuous_const.sub hc)).intervalIntegrable 0 δn
  have hint_shift : IntervalIntegrable
      (fun y : ℝ => wn * (autocorr f 0 - autocorr f (tn + y))) volume 0 δn :=
    (continuous_const.mul
      (continuous_const.sub (hc.comp (continuous_const.add continuous_id)))).intervalIntegrable 0 δn
  have hint_node : IntervalIntegrable (fun _ : ℝ => wn * autocorr f tn) volume 0 δn :=
    intervalIntegrable_const
  have hint_int :
      (∫ y in (0 : ℝ)..δn, (wn - wn ^ 2 / (2 * wn)) * autocorr f 0) ≤
        ∫ y in (0 : ℝ)..δn,
          (wn * (autocorr f 0 - autocorr f y) +
            wn * (autocorr f 0 - autocorr f (tn + y)) +
            wn * autocorr f tn) := by
    refine intervalIntegral.integral_mono_on hδn_pos.le hint_const
      ((hint_orig.add hint_shift).add hint_node) fun y _ => ?_
    exact autocorr_signed_collar_origin_leverage_add hf_cs hf_c2.continuous hwn_pos hwn_pos.le tn y
  rw [intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_add (hint_orig.add hint_shift) hint_node,
    intervalIntegral.integral_add hint_orig hint_shift,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at hint_int
  have horig_bound :
      wn * (∫ y in (0 : ℝ)..δn, (autocorr f 0 - autocorr f y)) ≤
        (wn / (n : ℝ)) *
          ∫ y in Ioc 0 (Real.log 2),
            (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
    have h1 := mul_le_mul_of_nonneg_left
      (nyquist_cell_origin_integral_le_log_two_origin hf_c2 hf_cs hn1) hwn_pos.le
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
      (mul_le_mul_of_nonneg_right (allScaleCriticalWeight_le_two_div_sqrt_succ n) hshift_nn) ?_
    exact nyquist_shifted_collar_le_levy_cell hf_c2 hf_cs hn2
  have hcoef : wn - wn ^ 2 / (2 * wn) = wn / 2 := by
    have hne : wn ≠ 0 := hwn_pos.ne'
    field_simp [hne]
    ring
  rw [hcoef] at hint_int
  have hlhs_eq : δn * ((wn / 2) * autocorr f 0) = δn * (wn / 2) * autocorr f 0 := by ring
  have hrhs_eq : δn * (wn * autocorr f tn) = δn * wn * autocorr f tn := by ring
  linarith only [hint_int, horig_bound, hshift_bound, hlhs_eq, hrhs_eq]

/-- **Unconditional Global All-Scale Signed Coercivity (`global_all_scale_signed_coercivity`):**
For EVERY `f ∈ C²_c(ℝ)` and EVERY `N : ℕ` (covering all integer nodes $n = 2, 3, \dots, N+1$ across
all dyadic shells simultaneously with **only a single copy** of `biScaleLevyEnergy f`!):
$$\mathcal{C}_{\mathrm{all}}(N)\,h_f(0)
  \;\le\; \operatorname{biScaleLevyEnergy}(f)
    + \sum_{k=0}^{N-1} \bigl(\log(k+3) - \log(k+2)\bigr)\,\varpi_{k+2}\,h_f(\log(k+2)).$$ -/
theorem global_all_scale_signed_coercivity
    {f : ℝ → ℝ} (hf_c2 : ContDiff ℝ 2 f) (hf_cs : HasCompactSupport f) (N : ℕ) :
    allScaleCoerciveConstant N * autocorr f 0 ≤
      biScaleLevyEnergy f +
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleCriticalWeight (k + 2) * autocorr f (Real.log ((k + 2 : ℕ) : ℝ)) := by
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.range N) =>
    nyquist_cell_all_scale_signed_coercivity hf_c2 hf_cs k
  rw [← Finset.sum_mul] at hsum
  change allScaleCoerciveConstant N * autocorr f 0 ≤ _ at hsum
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

/-- **Unconditional All-Scale Signed Weil Lower Bound on `RealEvenPolarTestFn`:**
For EVERY `g : RealEvenPolarTestFn` and EVERY `N : ℕ` (with **zero hypotheses** on `g` or `N`!),
$$\bigl(\Omega(0) + \mathcal{C}_{\mathrm{all}}(N)\bigr)\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}$$
$$\le\; \operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
  + \sum_{k=0}^{N-1} \bigl(\log(k+3) - \log(k+2)\bigr)\,\varpi_{k+2}\,
    (\operatorname{weilTest}\,g\,g\,(\log(k+2))).\mathrm{re}.$$ -/
theorem RealEvenPolarTestFn.unconditional_all_scale_signed_weil_lower_bound
    (g : RealEvenPolarTestFn) (N : ℕ) :
    (EF.gammaBracket 0 + allScaleCoerciveConstant N) *
        (EF.weilTest g.1.1.1 g.1.1.1 0).re ≤
      WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) +
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleCriticalWeight (k + 2) *
            (EF.weilTest g.1.1.1 g.1.1.1 (Real.log ((k + 2 : ℕ) : ℝ))).re := by
  have hcoerc := global_all_scale_signed_coercivity
    g.contDiff_source g.hasCompactSupport_source N
  rw [RealEvenPolarTestFn.weilArchRe_eq_gamma_add_biScaleLevyEnergy g, ← g.autocorr_eq 0]
  have hsum_eq :
      (∑ k ∈ Finset.range N,
          (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleCriticalWeight (k + 2) *
            (EF.weilTest g.1.1.1 g.1.1.1 (Real.log ((k + 2 : ℕ) : ℝ))).re) =
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleCriticalWeight (k + 2) *
            autocorr g.source (Real.log ((k + 2 : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [g.autocorr_eq]
  rw [hsum_eq]
  linarith only [hcoerc]

/-- **Unconditional All-Scale Signed Weil Lower Bound on `RealSmoothEvenPolarTestFn`:**
Immediate unconditional specialization of `unconditional_all_scale_signed_weil_lower_bound` to
smooth EWU test functions `g : RealSmoothEvenPolarTestFn`. -/
theorem RealSmoothEvenPolarTestFn.unconditional_all_scale_signed_weil_lower_bound
    (g : RealSmoothEvenPolarTestFn) (N : ℕ) :
    (EF.gammaBracket 0 + allScaleCoerciveConstant N) *
        (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re ≤
      WeilOneSided.weilArchRe (EF.weilTest g.1.1.1.1 g.1.1.1.1) +
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleCriticalWeight (k + 2) *
            (EF.weilTest g.1.1.1.1 g.1.1.1.1 (Real.log ((k + 2 : ℕ) : ℝ))).re :=
  RealEvenPolarTestFn.unconditional_all_scale_signed_weil_lower_bound g.toRealEvenPolar N

/-- **Unconditional All-Scale Hyperbolic Multiplier Signed Coercivity (`coshMultiplier`):**
For EVERY `g : RealEvenPolarTestFn`, EVERY `α : ℝ`, and EVERY `N : ℕ` (with zero hypotheses!),
the `coshMultiplier α g.source` Lévy energy and all-scale signed sum simultaneously control both
`autocorr g.source 0` and `autocorr (sinhMultiplier α g.source) 0`:
$$\mathcal{C}_{\mathrm{all}}(N)\,\bigl(h_g(0) + h_{S_\alpha g}(0)\bigr)
  \;\le\; \operatorname{biScaleLevyEnergy}(C_\alpha g)
    + \sum_{k=0}^{N-1} \bigl(\log(k+3) - \log(k+2)\bigr)\,\varpi_{k+2}\,h_{C_\alpha g}(\log(k+2)).$$ -/
theorem RealEvenPolarTestFn.unconditional_coshMultiplier_all_scale_signed_coercivity
    (g : RealEvenPolarTestFn) (α : ℝ) (N : ℕ) :
    allScaleCoerciveConstant N *
        (autocorr g.source 0 + autocorr (sinhMultiplier α g.source) 0) ≤
      biScaleLevyEnergy (coshMultiplier α g.source) +
        ∑ k ∈ Finset.range N,
          (Real.log ((k + 2 + 1 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)) *
            allScaleCriticalWeight (k + 2) *
            autocorr (coshMultiplier α g.source) (Real.log ((k + 2 : ℕ) : ℝ)) := by
  have hf_c2 : ContDiff ℝ 2 (coshMultiplier α g.source) :=
    contDiff_coshMultiplier α g.contDiff_source
  have hf_cs : HasCompactSupport (coshMultiplier α g.source) :=
    hasCompactSupport_coshMultiplier α g.hasCompactSupport_source
  have hcoerc := global_all_scale_signed_coercivity hf_c2 hf_cs N
  rw [autocorr_coshMultiplier_zero_eq g.contDiff_source.continuous g.hasCompactSupport_source α]
    at hcoerc
  exact hcoerc

end

end GaloisForLFunctions.BiScaleUncertainty

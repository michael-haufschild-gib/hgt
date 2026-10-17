import GaloisForLFunctions.BiScaleUncertainty.EulerMaclaurinLevyQuadratureAndSFreeCellBounds

/-!
# Pillar XVIII: Unconditional Multi-Node Origin-Budget Allocation & Global Disjoint-Collar Synthesis

This module develops **Pillar XVIII** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`), establishing the **Unconditional Origin-Plus-Tail
Synthesis Theorem** across logarithmic Nyquist cells with zero blindness, derivative, or abstract
disjointness hypotheses.

## Mathematical Overview

At each integer node $t_n = \log n$ ($n \ge 2$) with Nyquist cell width
$\delta_n = \log(n+1) - \log n$, three structural properties of `archLevySinhWeight` meet:
1. **Strict Antitonicity on `(0, ∞)` (§1):**
   `archLevySinhWeight x = 2 / (exp(x / 2) - exp(-3 * x / 2))` is strictly decreasing on `(0, ∞)`.
   Combined with `archLevySinhWeight_log_nat_ge_two_div_sqrt`, for every $x \in [\log n, \log(n+1)]$,
   $$\frac{2}{\sqrt{n+1}} \;\le\; \operatorname{archLevySinhWeight}(\log(n+1)) \;\le\; \operatorname{archLevySinhWeight}(x).$$
2. **Exact Origin-Plus-Tail Disjointness (§2):**
   For every $N \ge 2$, the Nyquist step at $N$ satisfies
   $\delta_N = \log(N+1) - \log N \le \log 2 \le \log N$. Thus the origin absorption interval
   $(0, \delta_N]$ and the dyadic Nyquist window $(\log N, \log(2N)]$ lie in the disjoint regions
   $(0, \log N]$ and $(\log N, \infty)$ of $(0, \infty)$, so the sum of their Lévy integrals is
   bounded by **a single copy of `biScaleLevyEnergy f`**.
3. **Unconditional Critical-Line Nyquist Synthesis (§3):**
   In cell $n = N + k$ ($0 \le k < N$, $N \ge 2$), choosing the concrete critical-line collar
   weight $w_n = 2 / \sqrt{n+1}$ and the adaptive origin weight $W_{0, n} = n / N$ yields
   $$w_n - \frac{w_n^2}{2 W_{0, n}} = \frac{2}{\sqrt{n+1}} - \frac{2 N}{n(n+1)}
     \;\ge\; \frac{2}{\sqrt{n+1}} - \frac{2}{n+1} > 0,$$
   while the $N$ origin charges sum to at most $1$ copy of the origin Lévy integral on $(0, \delta_N]$
   and the $N$ shifted collars telescope across $[\log N, \log(2N)]$. This yields the completely
   unconditional **Global Dyadic Nyquist Signed Coercivity Theorem**:
   $$\left(\sum_{k=0}^{N-1} \bigl(\log(N+k+1) - \log(N+k)\bigr)\left(\frac{2}{\sqrt{N+k+1}} - \frac{2}{N+k+1}\right)\right) h_f(0)$$
   $$\le\; \operatorname{biScaleLevyEnergy}(f)
     + \sum_{k=0}^{N-1} \bigl(\log(N+k+1) - \log(N+k)\bigr)\,\frac{2}{\sqrt{N+k+1}}\,h_f(\log(N+k)).$$
-/

open MeasureTheory Set Filter
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector
open scoped RealInnerProductSpace BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ## §1. Antitonicity of `archLevySinhWeight` & Concrete Critical-Line Collar Bounds -/

/-- Exact denominator identity for `archLevySinhWeight`:
for every `x ∈ ℝ`, `(exp(x / 2) - exp(-3 * x / 2)) * exp(x / 2) = 2 * sinh x`. -/
theorem exp_half_sub_exp_neg_three_half_mul_eq_two_sinh (x : ℝ) :
    (Real.exp (x / 2) - Real.exp (-3 * x / 2)) * Real.exp (x / 2) = 2 * Real.sinh x := by
  rw [Real.sinh_eq, sub_mul, ← Real.exp_add, ← Real.exp_add]
  have h1 : x / 2 + x / 2 = x := by ring
  have h2 : -3 * x / 2 + x / 2 = -x := by ring
  rw [h1, h2]
  ring

/-- For `x > 0`, `0 < exp(x / 2) - exp(-3 * x / 2)`. -/
theorem exp_half_sub_exp_neg_three_half_pos {x : ℝ} (hx : 0 < x) :
    0 < Real.exp (x / 2) - Real.exp (-3 * x / 2) := by
  have hlt : -3 * x / 2 < x / 2 := by linarith
  exact sub_pos.mpr (Real.exp_lt_exp.mpr hlt)

/-- Exact reciprocal-difference representation of `archLevySinhWeight` on `(0, ∞)`:
for every `x > 0`, `archLevySinhWeight x = 2 / (exp(x / 2) - exp(-3 * x / 2))`. -/
theorem archLevySinhWeight_eq_two_div_of_pos {x : ℝ} (hx : 0 < x) :
    archLevySinhWeight x = 2 / (Real.exp (x / 2) - Real.exp (-3 * x / 2)) := by
  unfold archLevySinhWeight
  have hpos := exp_half_sub_exp_neg_three_half_pos hx
  have hsinh_pos : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  rw [div_eq_div_iff hsinh_pos.ne' hpos.ne']
  have hmul := exp_half_sub_exp_neg_three_half_mul_eq_two_sinh x
  linarith

/-- **Strict Antitonicity of `archLevySinhWeight` on `(0, ∞)`:**
For any `0 < x ≤ y`, `archLevySinhWeight y ≤ archLevySinhWeight x`. -/
theorem archLevySinhWeight_antitoneOn {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    archLevySinhWeight y ≤ archLevySinhWeight x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [archLevySinhWeight_eq_two_div_of_pos hx, archLevySinhWeight_eq_two_div_of_pos hy]
  refine div_le_div_of_nonneg_left zero_le_two (exp_half_sub_exp_neg_three_half_pos hx) ?_
  have h1 : Real.exp (x / 2) ≤ Real.exp (y / 2) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-3 * y / 2) ≤ Real.exp (-3 * x / 2) := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- **Concrete Critical-Line Lower Bound on the `n`-th Nyquist Cell (`n ≥ 1`):**
For every `n ≥ 1` and every `x ≤ log(n + 1)` with `0 < x`,
`2 / √(n + 1) ≤ archLevySinhWeight x`. -/
theorem two_div_sqrt_succ_le_archLevySinhWeight {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx_pos : 0 < x) (hx_le : x ≤ Real.log ((n + 1 : ℕ) : ℝ)) :
    2 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ archLevySinhWeight x := by
  have hn1 : 2 ≤ n + 1 := by omega
  exact le_trans (archLevySinhWeight_log_nat_ge_two_div_sqrt hn1)
    (archLevySinhWeight_antitoneOn hx_pos hx_le)

/-- **Shifted Collar Integral Bound by the Archimedean Lévy Integral on `[log n, log(n + 1)]`:**
For any `f ∈ C²_c(ℝ)` and `n ≥ 2`,
$$\frac{2}{\sqrt{n+1}} \int_0^{\log(n+1) - \log n} \bigl(h_f(0) - h_f(\log n + y)\bigr)\,dy
  \;\le\; \int_{\log n}^{\log(n+1)} \bigl(h_f(0) - h_f(x)\bigr)\,\operatorname{archLevySinhWeight}(x)\,dx.$$ -/
theorem nyquist_shifted_collar_le_levy_cell {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {n : ℕ} (hn : 2 ≤ n) :
    (2 / Real.sqrt ((n + 1 : ℕ) : ℝ)) *
        (∫ y in (0 : ℝ)..(Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)),
          (autocorr f 0 - autocorr f (Real.log (n : ℝ) + y))) ≤
      ∫ x in Real.log (n : ℝ)..Real.log ((n + 1 : ℕ) : ℝ),
        (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  set tn := Real.log (n : ℝ)
  set tn1 := Real.log ((n + 1 : ℕ) : ℝ)
  have hn1 : 1 ≤ n := by omega
  have htn_pos : 0 < tn := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have htn_le : tn ≤ tn1 := by
    have hpos := log_succ_sub_log_pos hn1
    linarith
  have hshift := intervalIntegral_collar_shift (fun x : ℝ => autocorr f 0 - autocorr f x) tn (tn1 - tn)
  have hadd : tn + (tn1 - tn) = tn1 := add_sub_cancel _ _
  rw [hadd] at hshift
  rw [hshift, ← intervalIntegral.integral_const_mul]
  have hint_lhs : IntervalIntegrable
      (fun x : ℝ => (2 / Real.sqrt ((n + 1 : ℕ) : ℝ)) * (autocorr f 0 - autocorr f x))
      volume tn tn1 :=
    (continuous_const.mul (continuous_const.sub hc)).intervalIntegrable tn tn1
  have hcont_w : ContinuousOn archLevySinhWeight (Icc tn tn1) :=
    continuousOn_archLevySinhWeight fun x hx => lt_of_lt_of_le htn_pos hx.1
  have hint_rhs : IntervalIntegrable
      (fun x : ℝ => (autocorr f 0 - autocorr f x) * archLevySinhWeight x) volume tn tn1 :=
    ((continuousOn_const.sub hc.continuousOn).mul hcont_w).intervalIntegrable_of_Icc htn_le
  refine intervalIntegral.integral_mono_on htn_le hint_lhs hint_rhs fun x hx => ?_
  have hx_pos : 0 < x := lt_of_lt_of_le htn_pos hx.1
  have hw := two_div_sqrt_succ_le_archLevySinhWeight hn1 hx_pos hx.2
  have hD : 0 ≤ autocorr f 0 - autocorr f x := autocorr_sub_nonneg hfc hf.continuous x
  calc
    (2 / Real.sqrt ((n + 1 : ℕ) : ℝ)) * (autocorr f 0 - autocorr f x)
        = (autocorr f 0 - autocorr f x) * (2 / Real.sqrt ((n + 1 : ℕ) : ℝ)) := mul_comm _ _
    _ ≤ (autocorr f 0 - autocorr f x) * archLevySinhWeight x :=
      mul_le_mul_of_nonneg_left hw hD

/-! ## §2. Exact Origin-Plus-Tail Disjointness on `(0, ∞)` -/

/-- **Origin-Plus-Tail Partition of `biScaleLevyEnergy`:**
For any `f ∈ C²_c(ℝ)` and any cutoff `Δ₀ > 0`, the origin Lévy integral on `Ioc 0 Δ₀` and the
tail Lévy integral on `Ioi Δ₀` sum to `biScaleLevyEnergy f`:
$$\int_{Ioc\,0\,\Delta_0} \bigl(h_f(0) - h_f(x)\bigr)\,\operatorname{archLevySinhWeight}(x)\,dx
  + \int_{Ioi\,\Delta_0} \bigl(h_f(0) - h_f(x)\bigr)\,\operatorname{archLevySinhWeight}(x)\,dx
  = \operatorname{biScaleLevyEnergy}(f).$$ -/
theorem origin_add_tail_levy_eq_biScaleLevyEnergy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {Δ₀ : ℝ} (hΔ₀ : 0 < Δ₀) :
    (∫ x in Ioc 0 Δ₀, (autocorr f 0 - autocorr f x) * archLevySinhWeight x) +
      (∫ x in Ioi Δ₀, (autocorr f 0 - autocorr f x) * archLevySinhWeight x) =
      biScaleLevyEnergy f := by
  have hint := integrableOn_biScaleLevyIntegrand hf hfc
  have hdisj : Disjoint (Ioc 0 Δ₀) (Ioi Δ₀) := Ioc_disjoint_Ioi le_rfl
  have hunion : Ioc 0 Δ₀ ∪ Ioi Δ₀ = Ioi 0 := Ioc_union_Ioi_eq_Ioi hΔ₀.le
  have hint1 : IntegrableOn (fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x)
      (Ioc 0 Δ₀) := hint.mono_set (by rw [← hunion]; exact subset_union_left)
  have hint2 : IntegrableOn (fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x)
      (Ioi Δ₀) := hint.mono_set (by rw [← hunion]; exact subset_union_right)
  unfold biScaleLevyEnergy
  rw [← hunion, setIntegral_union hdisj measurableSet_Ioi hint1 hint2]

/-- For every integer `N ≥ 2`, the Nyquist step `log(N + 1) - log N` is at most `log N`
(since `(N + 1) / N ≤ 2 ≤ N`). -/
theorem nyquist_step_le_log_self {N : ℕ} (hN : 2 ≤ N) :
    Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ) ≤ Real.log (N : ℝ) := by
  have h1 : 1 ≤ N := by omega
  have hstep := log_succ_sub_log_antitone le_rfl h1
  have hlog1 : Real.log ((1 : ℕ) : ℝ) = 0 := by simp
  have h11 : ((1 + 1 : ℕ) : ℝ) = 2 := by norm_num
  rw [hlog1, sub_zero, h11] at hstep
  have hlog2_le : Real.log 2 ≤ Real.log (N : ℝ) := by
    refine Real.log_le_log two_pos ?_
    exact_mod_cast hN
  exact le_trans hstep hlog2_le

/-- **Disjoint Origin-Plus-Dyadic-Window Bound by `biScaleLevyEnergy` (`N ≥ 2`):**
For any `f ∈ C²_c(ℝ)` and any `N ≥ 2`, because `(0, log(N+1) - log N] ⊆ (0, log N]` is disjoint
from `[log N, log(2N)] ⊆ [log N, ∞)`, the sum of the origin Lévy integral on `(0, log(N+1) - log N]`
and the dyadic-window Lévy integral on `log N..log(2N)` is bounded by **a single copy of
`biScaleLevyEnergy f`**:
$$\int_{Ioc\,0\,(\log(N+1) - \log N)} \bigl(h_f(0) - h_f(y)\bigr)\,\operatorname{archLevySinhWeight}(y)\,dy
  + \int_{\log N}^{\log(2N)} \bigl(h_f(0) - h_f(x)\bigr)\,\operatorname{archLevySinhWeight}(x)\,dx
  \;\le\; \operatorname{biScaleLevyEnergy}(f).$$ -/
theorem origin_add_dyadic_window_levy_le_biScaleLevyEnergy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {N : ℕ} (hN : 2 ≤ N) :
    (∫ y in Ioc 0 (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)),
        (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
      (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ),
        (autocorr f 0 - autocorr f x) * archLevySinhWeight x) ≤
      biScaleLevyEnergy f := by
  set Δ₀ := Real.log (N : ℝ)
  have hΔ₀_pos : 0 < Δ₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hint := integrableOn_biScaleLevyIntegrand hf hfc
  rw [← origin_add_tail_levy_eq_biScaleLevyEnergy hf hfc hΔ₀_pos]
  have hstep_le : Real.log ((N + 1 : ℕ) : ℝ) - Δ₀ ≤ Δ₀ := nyquist_step_le_log_self hN
  have horig_le :
      (∫ y in Ioc 0 (Real.log ((N + 1 : ℕ) : ℝ) - Δ₀),
          (autocorr f 0 - autocorr f y) * archLevySinhWeight y) ≤
        ∫ y in Ioc 0 Δ₀, (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
    refine setIntegral_mono_set (hint.mono_set (fun y hy => hy.1)) ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      exact mul_nonneg (autocorr_sub_nonneg hfc hf.continuous y) (archLevySinhWeight_pos hy.1).le
    · exact Eventually.of_forall fun y hy => ⟨hy.1, le_trans hy.2 hstep_le⟩
  have h2N_ge : Δ₀ ≤ Real.log ((2 * N : ℕ) : ℝ) := by
    refine Real.log_le_log (by positivity) ?_
    exact_mod_cast (by omega : N ≤ 2 * N)
  rw [intervalIntegral.integral_of_le h2N_ge]
  have htail_le :
      (∫ x in Ioc Δ₀ (Real.log ((2 * N : ℕ) : ℝ)),
          (autocorr f 0 - autocorr f x) * archLevySinhWeight x) ≤
        ∫ x in Ioi Δ₀, (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
    refine setIntegral_mono_set (hint.mono_set (fun x hx => lt_trans hΔ₀_pos hx)) ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (autocorr_sub_nonneg hfc hf.continuous x)
        (archLevySinhWeight_pos (lt_trans hΔ₀_pos hx)).le
    · exact Eventually.of_forall fun x hx => hx.1
  linarith

/-! ## §3. Unconditional Global Dyadic Nyquist Signed Coercivity -/

/-- **Single Nyquist Cell Signed Coercivity with Adaptive Origin Share (`N ≥ 2`, `0 ≤ k < N`):**
In the `k`-th Nyquist cell `[log(N+k), log(N+k+1)]` (`N ≥ 2`), testing with the concrete
critical-line weight `w_k = 2 / √(N+k+1)` and origin weight `W_{0,k} = (N + k) / N` yields:
$$\bigl(\log(N+k+1) - \log(N+k)\bigr)\left(\frac{2}{\sqrt{N+k+1}} - \frac{2}{N+k+1}\right) h_f(0)$$
$$\le\; \frac{1}{N}\int_{Ioc\,0\,(\log(N+1) - \log N)} \bigl(h_f(0) - h_f(y)\bigr)\,\operatorname{archLevySinhWeight}(y)\,dy$$
$$+\; \int_{\log(N+k)}^{\log(N+k+1)} \bigl(h_f(0) - h_f(x)\bigr)\,\operatorname{archLevySinhWeight}(x)\,dx
  + \bigl(\log(N+k+1) - \log(N+k)\bigr)\frac{2}{\sqrt{N+k+1}}\,h_f(\log(N+k)).$$ -/
theorem nyquist_cell_adaptive_signed_coercivity {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {N k : ℕ} (hN : 2 ≤ N) :
    (Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)) *
        (2 / Real.sqrt ((N + k + 1 : ℕ) : ℝ) - 2 / ((N + k + 1 : ℕ) : ℝ)) * autocorr f 0 ≤
      (1 / (N : ℝ)) *
          (∫ y in Ioc 0 (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)),
            (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
        (∫ x in Real.log ((N + k : ℕ) : ℝ)..Real.log ((N + k + 1 : ℕ) : ℝ),
          (autocorr f 0 - autocorr f x) * archLevySinhWeight x) +
        (Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)) *
          (2 / Real.sqrt ((N + k + 1 : ℕ) : ℝ)) *
          autocorr f (Real.log ((N + k : ℕ) : ℝ)) := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  set n := N + k
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hN1 : 1 ≤ N := by omega
  set tn := Real.log (n : ℝ)
  set δn := Real.log ((n + 1 : ℕ) : ℝ) - tn
  set δN := Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)
  set wn := 2 / Real.sqrt ((n + 1 : ℕ) : ℝ)
  set W₀ := (n : ℝ) / (N : ℝ)
  have hδn_pos : 0 < δn := log_succ_sub_log_pos hn1
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hW₀_pos : 0 < W₀ := div_pos hn_pos hN_pos
  have hwn_nn : 0 ≤ wn := by positivity
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
    exact autocorr_signed_collar_origin_leverage_add hfc hf.continuous hW₀_pos hwn_nn tn y
  rw [intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_add (hint_orig.add hint_shift) hint_node,
    intervalIntegral.integral_add hint_orig hint_shift,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at hint_int
  have habsorb := nyquist_cell_origin_integral_le_levy hf hfc hn1
  have hδn_le_δN : δn ≤ δN := log_succ_sub_log_antitone hN1 (by omega)
  have hint_levy :
      IntegrableOn (fun y => (autocorr f 0 - autocorr f y) * archLevySinhWeight y) (Ioc 0 δN) :=
    (integrableOn_biScaleLevyIntegrand hf hfc).mono_set (fun y hy => hy.1)
  have hmono_δ :
      (∫ y in Ioc 0 δn, (autocorr f 0 - autocorr f y) * archLevySinhWeight y) ≤
        ∫ y in Ioc 0 δN, (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
    refine setIntegral_mono_set hint_levy ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      exact mul_nonneg (autocorr_sub_nonneg hfc hf.continuous y) (archLevySinhWeight_pos hy.1).le
    · exact Eventually.of_forall fun y hy => ⟨hy.1, le_trans hy.2 hδn_le_δN⟩
  have horig_bound :
      W₀ * (∫ y in (0 : ℝ)..δn, (autocorr f 0 - autocorr f y)) ≤
        (1 / (N : ℝ)) *
          ∫ y in Ioc 0 δN, (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
    have h1 := mul_le_mul_of_nonneg_left habsorb hW₀_pos.le
    have h2 : W₀ * (1 / (n : ℝ)) = 1 / (N : ℝ) := by
      dsimp [W₀]
      field_simp [hn_pos.ne', hN_pos.ne']
    rw [← mul_assoc, h2] at h1
    have h3 := mul_le_mul_of_nonneg_left hmono_δ (by positivity : 0 ≤ 1 / (N : ℝ))
    exact le_trans h1 h3
  have hshift_bound := nyquist_shifted_collar_le_levy_cell hf hfc hn2
  have hcoef_ge :
      2 / Real.sqrt ((n + 1 : ℕ) : ℝ) - 2 / ((n + 1 : ℕ) : ℝ) ≤ wn - wn ^ 2 / (2 * W₀) := by
    have hsq : wn ^ 2 = 4 / ((n + 1 : ℕ) : ℝ) := by
      dsimp [wn]
      rw [div_pow, Real.sq_sqrt hn1_pos.le]
      norm_num
    rw [hsq]
    have hN_le_n : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : N ≤ n)
    have h1_le_W₀ : 1 ≤ W₀ := (one_le_div hN_pos).mpr hN_le_n
    have hpen_le : (4 / ((n + 1 : ℕ) : ℝ)) / (2 * W₀) ≤ 2 / ((n + 1 : ℕ) : ℝ) := by
      have h2W : 2 ≤ 2 * W₀ := by linarith
      have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ 4 / ((n + 1 : ℕ) : ℝ))
        two_pos h2W
      have hsimp : (4 / ((n + 1 : ℕ) : ℝ)) / 2 = 2 / ((n + 1 : ℕ) : ℝ) := by ring
      linarith
    dsimp [wn]
    linarith
  have hlhs_le :
      δn * (2 / Real.sqrt ((n + 1 : ℕ) : ℝ) - 2 / ((n + 1 : ℕ) : ℝ)) * autocorr f 0 ≤
        δn * ((wn - wn ^ 2 / (2 * W₀)) * autocorr f 0) := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hδn_pos.le
    exact mul_le_mul_of_nonneg_right hcoef_ge (autocorr_zero_nonneg f)
  have hrhs_eq :
      δn * (wn * autocorr f tn) = δn * wn * autocorr f tn := by ring
  linarith

/-- **Unconditional Global Dyadic Nyquist Signed Coercivity Theorem (`N ≥ 2`):**
For EVERY `f ∈ C²_c(ℝ)` and EVERY `N ≥ 2` (with zero blindness or derivative hypotheses),
$$\left(\sum_{k=0}^{N-1} \bigl(\log(N+k+1) - \log(N+k)\bigr)\left(\frac{2}{\sqrt{N+k+1}} - \frac{2}{N+k+1}\right)\right) h_f(0)$$
$$\le\; \operatorname{biScaleLevyEnergy}(f)
  + \sum_{k=0}^{N-1} \bigl(\log(N+k+1) - \log(N+k)\bigr)\,\frac{2}{\sqrt{N+k+1}}\,h_f(\log(N+k)).$$ -/
theorem global_dyadic_nyquist_signed_coercivity {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {N : ℕ} (hN : 2 ≤ N) :
    (∑ k ∈ Finset.range N,
        (Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)) *
          (2 / Real.sqrt ((N + k + 1 : ℕ) : ℝ) - 2 / ((N + k + 1 : ℕ) : ℝ))) *
      autocorr f 0 ≤
      biScaleLevyEnergy f +
        ∑ k ∈ Finset.range N,
          (Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)) *
            (2 / Real.sqrt ((N + k + 1 : ℕ) : ℝ)) *
            autocorr f (Real.log ((N + k : ℕ) : ℝ)) := by
  rw [Finset.sum_mul]
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.range N) =>
    nyquist_cell_adaptive_signed_coercivity hf hfc (k := k) hN
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hcancel :
      (N : ℝ) * ((1 / (N : ℝ)) *
        ∫ y in Ioc 0 (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)),
          (autocorr f 0 - autocorr f y) * archLevySinhWeight y) =
      ∫ y in Ioc 0 (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)),
        (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
    rw [← mul_assoc, mul_one_div_cancel hN_pos.ne', one_mul]
  rw [hcancel] at hsum
  have htel :
      (∑ k ∈ Finset.range N,
          ∫ x in Real.log ((N + k : ℕ) : ℝ)..Real.log ((N + k + 1 : ℕ) : ℝ),
            (autocorr f 0 - autocorr f x) * archLevySinhWeight x) =
        ∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ),
          (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
    have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
    induction N with
    | zero => omega
    | succ M _ =>
      -- Use adjacent interval induction over K ≤ N
      have hind : ∀ K : ℕ,
          (∑ k ∈ Finset.range K,
              ∫ x in Real.log ((M + 1 + k : ℕ) : ℝ)..Real.log ((M + 1 + k + 1 : ℕ) : ℝ),
                (autocorr f 0 - autocorr f x) * archLevySinhWeight x) =
            ∫ x in Real.log ((M + 1 : ℕ) : ℝ)..Real.log ((M + 1 + K : ℕ) : ℝ),
              (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
        intro K
        induction K with
        | zero => simp
        | succ K ihK =>
          rw [Finset.sum_range_succ, ihK]
          have hpos_start : 0 < Real.log ((M + 1 : ℕ) : ℝ) :=
            Real.log_pos (by exact_mod_cast (by omega : 1 < M + 1))
          have hcont1 : ContinuousOn
              (fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x)
              (uIcc (Real.log ((M + 1 : ℕ) : ℝ)) (Real.log ((M + 1 + K : ℕ) : ℝ))) := by
            have hle : Real.log ((M + 1 : ℕ) : ℝ) ≤ Real.log ((M + 1 + K : ℕ) : ℝ) :=
              Real.log_le_log (by positivity) (by exact_mod_cast (by omega : M + 1 ≤ M + 1 + K))
            rw [uIcc_of_le hle]
            exact (continuousOn_const.sub hc.continuousOn).mul
              (continuousOn_archLevySinhWeight fun x hx => lt_of_lt_of_le hpos_start hx.1)
          have hcont2 : ContinuousOn
              (fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x)
              (uIcc (Real.log ((M + 1 + K : ℕ) : ℝ)) (Real.log ((M + 1 + (K + 1) : ℕ) : ℝ))) := by
            have hpos_K : 0 < Real.log ((M + 1 + K : ℕ) : ℝ) :=
              Real.log_pos (by exact_mod_cast (by omega : 1 < M + 1 + K))
            have hle : Real.log ((M + 1 + K : ℕ) : ℝ) ≤ Real.log ((M + 1 + (K + 1) : ℕ) : ℝ) :=
              Real.log_le_log (by positivity)
                (by exact_mod_cast (by omega : M + 1 + K ≤ M + 1 + (K + 1)))
            rw [uIcc_of_le hle]
            exact (continuousOn_const.sub hc.continuousOn).mul
              (continuousOn_archLevySinhWeight fun x hx => lt_of_lt_of_le hpos_K hx.1)
          have hadj := intervalIntegral.integral_add_adjacent_intervals
            (hcont1.intervalIntegrable (μ := volume)) (hcont2.intervalIntegrable (μ := volume))
          have hnat : M + 1 + K + 1 = M + 1 + (K + 1) := by omega
          rw [hnat, hadj]
      rw [two_mul (M + 1)]
      exact hind (M + 1)
  rw [htel] at hsum
  have hglobal := origin_add_dyadic_window_levy_le_biScaleLevyEnergy hf hfc hN
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty

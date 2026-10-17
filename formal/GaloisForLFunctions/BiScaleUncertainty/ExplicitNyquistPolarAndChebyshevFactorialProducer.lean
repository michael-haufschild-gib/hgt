import GaloisForLFunctions.BiScaleUncertainty.ProducerConsumerDualityAndNymanBeurlingBridge
import GaloisForLFunctions.BiScaleUncertainty.ChebyshevGaugeNyquistCellQuadrature
import GaloisForLFunctions.RHTower.ChebyshevPsiLogSummatory

/-!
# Pillar XXIX: Explicit Nyquist-Cell Polar Producer & Unconditional Chebyshev Factorial-Difference Producers

Up through Pillar XXVIII, the theorems in `BiScaleUncertainty` acted primarily on the
**receiver / consumer** side:
- In Pillar XII (`ProducerConsumerDualityAndNymanBeurlingBridge.lean`), the producer weight
  `W : ℝ → ℝ` on `[log N, log(2N)]` was left as an uninstantiated variable, with its `L²`
  approximation error `∫ (cosh(x/2) - W(x))² dx` appearing as an external hypothesis.
- In Pillars XXVI–XXVIII, the Weil functional was rewritten in terms of the unknown Chebyshev cell
  defect `ψ(n) - m_n`. Meanwhile, in `RHTower.PsiDefectSqrtBound`, applying `floorSummatory` to the
  pre-subtracted defect `ψ(j) - j + 2γ` replaced the linear counterterm `j` by Dirichlet's divisor
  summatory `D(N) = ∑_{d ≤ N} ⌊N/d⌋`, contaminating the `O(log N)`-smooth Chebyshev factorial sum
  `T(N) = ∑_{d ≤ N} ψ(⌊N/d⌋) = ∑_{m ≤ N} log m` with `O(√N)` divisor noise.

This module constructs **two unconditional producers** that close both gaps without uninstantiated
weights or conditional hypotheses:

1. **Explicit Nyquist-Cell Polar Producer (§1–§2):**
   On each logarithmic Nyquist cell `[log n, log(n+1)]` (`n ≥ 1`), we construct the explicit polar
   endpoint producer
   $$\operatorname{nyquistPolarConstant}(n) := \cosh\Bigl(\frac{\log n}{2}\Bigr) = \frac{\sqrt{n} + (\sqrt{n})^{-1}}{2}$$
   and prove unconditionally:
   - the exact algebraic identity `nyquistPolarConstant_eq_sqrt_avg`,
   - the pointwise Nyquist-cell drift bound `0 ≤ cosh(x/2) - nyquistPolarConstant n ≤ 1 / (4√n)`
     on `[log n, log(n+1)]`,
   - the unconditional `L²` producer approximation bound
     $$\int_{\log n}^{\log(n+1)} \bigl(\cosh(x/2) - \operatorname{nyquistPolarConstant}(n)\bigr)^2\,dx
       \;\le\; \frac{\operatorname{cellLength}(n)}{16 n} \;\le\; \frac{1}{16 n^2},$$
   - the instantiated **Nyquist-Cell Producer–Consumer Residual Theorem**
     (`nyquist_cell_producer_consumer_residual_sq_le`), eliminating the free function `W` from
     Pillar XII, and
   - the summed **Dyadic Window Producer Error Bound**
     $$\sum_{n \in [N, 2N)} \int_{\log n}^{\log(n+1)} \bigl(\cosh(x/2) - \operatorname{nyquistPolarConstant}(n)\bigr)^2\,dx
       \;\le\; \frac{1}{16 N}.$$

2. **Unconditional Chebyshev Alternating & Bi-Null Factorial Producers (§3–§4):**
   Instead of subtracting the discrete counterterm `j` before floor summation (which introduces
   `O(√N)` Dirichlet divisor error), we apply pole-cancelling dyadic dilation stencils directly to
   the Chebyshev floor summatory
   $$T(N) := \operatorname{floorSummatory}\;\operatorname{chebyshevPsi}\;N
     = \sum_{d=1}^N \psi(\lfloor N/d \rfloor) = \sum_{m=1}^N \log m:$$
   - **Stirling Residual Sandwich (`stirlingResidual_bounds`):**
     For every `k ≥ 1`, `1 ≤ T(k) - (k log k - k) ≤ log(k + 1) + 1`.
   - **First-Order Chebyshev–Nyman–Beurling Producer (`chebyshevAlternatingProducer N := T(2N) - 2 T(N)`):**
     Cancels the `2N log N - 2N` double pole identically, isolating the exact linear main term
     `(2 log 2) N` with an **unconditional `O(log N)` error**
     $$\bigl|\operatorname{chebyshevAlternatingProducer}(N) - (2\log 2) N\bigr| \;\le\; 2\log(2N + 1) + 1.$$
   - **Second-Order Bi-Null Chebyshev Producer (`chebyshevBiNullProducer N := T(4N) - 4 T(2N) + 4 T(N)`):**
     Applies the squared dyadic annihilator `(1 - 2 · 2^{-s})²` to `T`, cancelling **both** the
     `N log N` double pole **and** the `N` simple pole identically without introducing divisor sums,
     and proving the **unconditional `O(log N)` bound** (exponentially smaller than `O(√N)`):
     $$\bigl|\operatorname{chebyshevBiNullProducer}(N)\bigr| \;\le\; 5\log(4N + 1) + 1.$$
-/

namespace GaloisForLFunctions.BiScaleUncertainty

open MeasureTheory Set Filter Finset ArithmeticFunction
open _root_.RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open scoped BigOperators

noncomputable section

/-! ## §1. Explicit Nyquist-Cell Polar Producer & Unconditional `O(1/n²)` Cell Error -/

/-- **Explicit Nyquist-Cell Polar Producer Constant:**
On the logarithmic Nyquist cell `[log n, log(n+1)]`, the polar weight `cosh(x/2)` is approximated by
its left-endpoint value `cosh((log n)/2)`. -/
def nyquistPolarConstant (n : ℕ) : ℝ :=
  Real.cosh (Real.log (n : ℝ) / 2)

/-- **Exact Radical Formula for the Nyquist Polar Constant:**
For `n ≥ 1`, `cosh((log n)/2) = (√n + (√n)⁻¹) / 2`. -/
theorem nyquistPolarConstant_eq_sqrt_avg {n : ℕ} (hn : 1 ≤ n) :
    nyquistPolarConstant n = (Real.sqrt (n : ℝ) + (Real.sqrt (n : ℝ))⁻¹) / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold nyquistPolarConstant
  rw [Real.cosh_eq]
  have hexp_pos : Real.exp (Real.log (n : ℝ) / 2) = Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0]
    ring_nf
  have hexp_neg : Real.exp (-(Real.log (n : ℝ) / 2)) = (Real.sqrt (n : ℝ))⁻¹ := by
    rw [Real.exp_neg, hexp_pos]
  rw [hexp_pos, hexp_neg]

/-- **Radical Increment Bound on a Nyquist Cell:**
For `n ≥ 1`, `√(n + 1) - √n ≤ 1 / (2 √n)`. -/
theorem sqrt_succ_sub_sqrt_le {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ) ≤ 1 / (2 * Real.sqrt (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsum_pos : 0 < Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ) := by positivity
  have hprod :
      (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) *
        (Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ)) = 1 := by
    calc (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) *
          (Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ))
        = Real.sqrt ((n : ℝ) + 1) ^ 2 - Real.sqrt (n : ℝ) ^ 2 := by ring
      _ = ((n : ℝ) + 1) - (n : ℝ) := by
          rw [Real.sq_sqrt (by positivity), Real.sq_sqrt hn0.le]
      _ = 1 := by ring
  have hge : 2 * Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ) := by
    have hle : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith
  have hsub_nonneg : 0 ≤ Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ) := by
    have hle : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    linarith
  rw [le_div_iff₀ (by positivity)]
  calc (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) * (2 * Real.sqrt (n : ℝ))
      ≤ (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) *
          (Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hge hsub_nonneg
    _ = 1 := hprod

/-- **Nyquist-Cell Polar Jump Bound:**
For `n ≥ 1`,
`0 ≤ nyquistPolarConstant (n + 1) - nyquistPolarConstant n ≤ (√(n+1) - √n)/2 ≤ 1 / (4 √n)`. -/
theorem nyquistPolarConstant_succ_sub_le {n : ℕ} (hn : 1 ≤ n) :
    nyquistPolarConstant (n + 1) - nyquistPolarConstant n ≤ 1 / (4 * Real.sqrt (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := nyquistPolarConstant_eq_sqrt_avg (by omega : 1 ≤ n + 1)
  have h2 := nyquistPolarConstant_eq_sqrt_avg hn
  push_cast at h1
  rw [h1, h2]
  have hinv_le : (Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ (Real.sqrt (n : ℝ))⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.mpr hn0) (Real.sqrt_le_sqrt (by linarith))
  have hrad := sqrt_succ_sub_sqrt_le hn
  calc ((Real.sqrt ((n : ℝ) + 1) + (Real.sqrt ((n : ℝ) + 1))⁻¹) / 2) -
        ((Real.sqrt (n : ℝ) + (Real.sqrt (n : ℝ))⁻¹) / 2)
      = (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) / 2 +
          ((Real.sqrt ((n : ℝ) + 1))⁻¹ - (Real.sqrt (n : ℝ))⁻¹) / 2 := by ring
    _ ≤ (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) / 2 + 0 := by
        linarith
    _ ≤ (1 / (2 * Real.sqrt (n : ℝ))) / 2 := by linarith
    _ = 1 / (4 * Real.sqrt (n : ℝ)) := by ring

/-- **Monotonicity of `cosh(x/2)` on `[0, ∞)`:**
If `0 ≤ a ≤ b`, then `cosh(a/2) ≤ cosh(b/2)`. -/
theorem cosh_half_le_cosh_half {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.cosh (a / 2) ≤ Real.cosh (b / 2) := by
  rw [Real.cosh_le_cosh]
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  linarith

/-- **Pointwise Nyquist-Cell Polar Producer Error Bound:**
For every `n ≥ 1` and every `x ∈ [log n, log(n+1)]`,
`0 ≤ cosh(x/2) - nyquistPolarConstant n ≤ 1 / (4 √n)`. -/
theorem nyquist_cell_cosh_sub_polarConstant_bounds {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx : x ∈ Icc (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1))) :
    0 ≤ Real.cosh (x / 2) - nyquistPolarConstant n ∧
      Real.cosh (x / 2) - nyquistPolarConstant n ≤ 1 / (4 * Real.sqrt (n : ℝ)) := by
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hlo : nyquistPolarConstant n ≤ Real.cosh (x / 2) :=
    cosh_half_le_cosh_half hlog_nonneg hx.1
  have hhi : Real.cosh (x / 2) ≤ nyquistPolarConstant (n + 1) := by
    have hcast : Real.log (((n + 1 : ℕ) : ℝ)) = Real.log ((n : ℝ) + 1) := by push_cast; rfl
    unfold nyquistPolarConstant
    rw [hcast]
    exact cosh_half_le_cosh_half (hlog_nonneg.trans hx.1) hx.2
  constructor
  · linarith
  · linarith [nyquistPolarConstant_succ_sub_le hn]

/-- **Unconditional Nyquist-Cell Polar Producer `L²` Error Bound:**
On each Nyquist cell `[log n, log(n+1)]` (`n ≥ 1`), the `L²` approximation error of the explicit
constant producer `nyquistPolarConstant n = cosh((log n)/2)` against `cosh(x/2)` satisfies
`∫_{log n}^{log(n+1)} (cosh(x/2) - nyquistPolarConstant n)² dx ≤ cellLength n / (16 n) ≤ 1 / (16 n²)`. -/
theorem nyquist_cell_polar_producer_l2_error_le {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
        (Real.cosh (x / 2) - nyquistPolarConstant n) ^ 2) ≤
      1 / (16 * (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hab : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log hn0 (by linarith)
  have hcont :
      ContinuousOn (fun x => (Real.cosh (x / 2) - nyquistPolarConstant n) ^ 2)
        (Icc (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1))) :=
    ((Real.continuous_cosh.comp (continuous_id.div_const 2)).sub continuous_const).continuousOn.pow 2
  have hint :
      IntervalIntegrable (fun x => (Real.cosh (x / 2) - nyquistPolarConstant n) ^ 2)
        volume (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1)) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    exact hcont
  have hpt : ∀ x ∈ Icc (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1)),
      (Real.cosh (x / 2) - nyquistPolarConstant n) ^ 2 ≤ 1 / (16 * (n : ℝ)) := by
    intro x hx
    obtain ⟨h0, h1⟩ := nyquist_cell_cosh_sub_polarConstant_bounds hn hx
    have hsq :
        (Real.cosh (x / 2) - nyquistPolarConstant n) ^ 2 ≤
          (1 / (4 * Real.sqrt (n : ℝ))) ^ 2 := by
      nlinarith
    have hrad_sq : (1 / (4 * Real.sqrt (n : ℝ))) ^ 2 = 1 / (16 * (n : ℝ)) := by
      calc (1 / (4 * Real.sqrt (n : ℝ))) ^ 2
          = 1 / (16 * Real.sqrt (n : ℝ) ^ 2) := by ring
        _ = 1 / (16 * (n : ℝ)) := by rw [Real.sq_sqrt hn0.le]
    linarith
  have hle_int :
      (∫ x in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
          (Real.cosh (x / 2) - nyquistPolarConstant n) ^ 2) ≤
        ∫ _ in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), (1 / (16 * (n : ℝ))) :=
    intervalIntegral.integral_mono_on hab hint intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hle_int
  have hlen : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) :=
    cellLength_le hn
  calc (∫ x in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
          (Real.cosh (x / 2) - nyquistPolarConstant n) ^ 2)
      ≤ (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) * (1 / (16 * (n : ℝ))) := hle_int
    _ ≤ (1 / (n : ℝ)) * (1 / (16 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hlen (by positivity)
    _ = 1 / (16 * (n : ℝ) ^ 2) := by ring

/-! ## §2. Instantiated Producer–Consumer Residual Bounds (Cell & Dyadic Window) -/

/-- **Instantiated Nyquist-Cell Producer–Consumer Residual Theorem:**
For any `f ∈ C²_c(ℝ)` and any Nyquist cell `[log n, log(n+1)]` (`n ≥ 1`), instantiating Pillar XII's
`correlation_producer_consumer_residual_sq_le` with the explicit producer `nyquistPolarConstant n`
yields the unconditional bound
`((∫ x in log n..log(n+1), h_f(x) cosh(x/2)) + nyquistPolarConstant n * (∫ x in log n..log(n+1), (h_f(0) - h_f(x))) - cellLength n * nyquistPolarConstant n * h_f(0))² ≤ (1 / (16 n²)) * ∫ x in log n..log(n+1), h_f(x)²`. -/
theorem nyquist_cell_producer_consumer_residual_sq_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {n : ℕ} (hn : 1 ≤ n) :
    ((∫ x in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
          autocorr f x * Real.cosh (x / 2)) +
        (∫ x in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
          (autocorr f 0 - autocorr f x) * nyquistPolarConstant n) -
        (∫ _ in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), nyquistPolarConstant n) *
          autocorr f 0) ^ 2 ≤
      (1 / (16 * (n : ℝ) ^ 2)) *
        (∫ x in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), (autocorr f x) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hab : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log hn0 (by linarith)
  have hP : ContinuousOn (fun x : ℝ => Real.cosh (x / 2))
      (Icc (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1))) :=
    (Real.continuous_cosh.comp (continuous_id.div_const 2)).continuousOn
  have hW : ContinuousOn (fun _ : ℝ => nyquistPolarConstant n)
      (Icc (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1))) :=
    continuousOn_const
  have hcs := correlation_producer_consumer_residual_sq_le hf hfc hab hP hW
  have herr := nyquist_cell_polar_producer_l2_error_le hn
  have hauto_nonneg :
      0 ≤ ∫ x in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), (autocorr f x) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _
  calc ((∫ x in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
            autocorr f x * Real.cosh (x / 2)) +
          (∫ x in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
            (autocorr f 0 - autocorr f x) * nyquistPolarConstant n) -
          (∫ _ in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), nyquistPolarConstant n) *
            autocorr f 0) ^ 2
      ≤ (∫ x in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), (autocorr f x) ^ 2) *
          (∫ x in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
            (Real.cosh (x / 2) - nyquistPolarConstant n) ^ 2) := hcs
    _ ≤ (∫ x in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), (autocorr f x) ^ 2) *
          (1 / (16 * (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left herr hauto_nonneg
    _ = (1 / (16 * (n : ℝ) ^ 2)) *
          (∫ x in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), (autocorr f x) ^ 2) :=
        mul_comm _ _

/-- **Unconditional Dyadic Window Polar Producer `L²` Error Bound (`O(1/N)`):**
Summing the Nyquist-cell polar producer `L²` errors across the `N` cells `[log n, log(n+1)]` in the
dyadic window `N ≤ n < 2N` (`N ≥ 1`) gives the unconditional `O(1/N)` bound:
`∑ n ∈ Ico N (2 * N), ∫_{log n}^{log(n+1)} (cosh(x/2) - nyquistPolarConstant n)² dx ≤ 1 / (16 N)`. -/
theorem dyadic_window_polar_producer_l2_error_sum_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico N (2 * N),
        ∫ x in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
          (Real.cosh (x / 2) - nyquistPolarConstant n) ^ 2) ≤
      1 / (16 * (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ n ∈ Finset.Ico N (2 * N),
      (∫ x in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
          (Real.cosh (x / 2) - nyquistPolarConstant n) ^ 2) ≤
        1 / (16 * (N : ℝ) ^ 2) := by
    intro n hn
    have hn_ge : N ≤ n := (Finset.mem_Ico.mp hn).1
    have hn1 : 1 ≤ n := le_trans hN hn_ge
    have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
    refine (nyquist_cell_polar_producer_l2_error_le hn1).trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  calc (∑ n ∈ Finset.Ico N (2 * N),
          ∫ x in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
            (Real.cosh (x / 2) - nyquistPolarConstant n) ^ 2)
      ≤ ∑ _ ∈ Finset.Ico N (2 * N), (1 / (16 * (N : ℝ) ^ 2)) :=
        Finset.sum_le_sum hterm
    _ = ((Finset.Ico N (2 * N)).card : ℝ) * (1 / (16 * (N : ℝ) ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (N : ℝ) * (1 / (16 * (N : ℝ) ^ 2)) := by
        rw [Nat.card_Ico, show 2 * N - N = N by omega]
    _ = 1 / (16 * (N : ℝ)) := by
        field_simp [hN0.ne']

/-! ## §3. The Stirling Residual of `floorSummatory chebyshevPsi` -/

/-- **Stirling Residual of the Chebyshev Floor Summatory:**
`stirlingResidual k := floorSummatory chebyshevPsi k - (k log k - k)`.
By `floorSummatory_chebyshevPsi`, this is `∑_{m=1}^k log m - (k log k - k)`. -/
def stirlingResidual (k : ℕ) : ℝ :=
  floorSummatory chebyshevPsi k - ((k : ℝ) * Real.log (k : ℝ) - (k : ℝ))

/-- **Exact Decomposition of `floorSummatory chebyshevPsi` into Main Term + Stirling Residual:**
`floorSummatory chebyshevPsi k = (k log k - k) + stirlingResidual k`. -/
theorem floorSummatory_chebyshevPsi_eq_main_add_stirlingResidual (k : ℕ) :
    floorSummatory chebyshevPsi k =
      ((k : ℝ) * Real.log (k : ℝ) - (k : ℝ)) + stirlingResidual k := by
  unfold stirlingResidual
  ring

/-- **Unconditional `O(log k)` Sandwich for the Stirling Residual:**
For every `k ≥ 1`,
`1 ≤ stirlingResidual k ≤ log(k + 1) + 1`. -/
theorem stirlingResidual_bounds {k : ℕ} (hk : 1 ≤ k) :
    1 ≤ stirlingResidual k ∧ stirlingResidual k ≤ Real.log ((k : ℝ) + 1) + 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold stirlingResidual
  rw [floorSummatory_chebyshevPsi]
  have hlo := stirling_le_sum_log k hk
  have hup := sum_log_le_stirling k hk
  have hstep : Real.log ((k : ℝ) + 1) ≤ Real.log (k : ℝ) + 1 / (k : ℝ) := by
    have hdiv := Real.log_le_sub_one_of_pos (x := ((k : ℝ) + 1) / (k : ℝ)) (by positivity)
    rw [Real.log_div (by positivity) hkR.ne'] at hdiv
    have heq : ((k : ℝ) + 1) / (k : ℝ) - 1 = 1 / (k : ℝ) := by
      field_simp
      ring
    linarith
  have hmulstep : (k : ℝ) * Real.log ((k : ℝ) + 1) ≤ (k : ℝ) * Real.log (k : ℝ) + 1 := by
    have := mul_le_mul_of_nonneg_left hstep hkR.le
    have hone : (k : ℝ) * (1 / (k : ℝ)) = 1 := by field_simp
    nlinarith [this, hone]
  have hexp :
      ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1) =
        (k : ℝ) * Real.log ((k : ℝ) + 1) + Real.log ((k : ℝ) + 1) := by ring
  constructor
  · linarith
  · linarith

/-! ## §4. Unconditional Chebyshev Alternating & Bi-Null Factorial Producers (`O(log N)`) -/

/-- **First-Order Chebyshev–Nyman–Beurling Alternating Producer:**
`chebyshevAlternatingProducer N := T(2N) - 2 T(N)`, where `T(N) = ∑_{d ≤ N} ψ(⌊N/d⌋)`.
In Mellin space this corresponds to applying the pole-annihilating Nyman–Beurling factor
`1 - 2 · 2^{-s}` to `(ζ(s))² (-ζ'(s)/ζ(s))`. -/
def chebyshevAlternatingProducer (N : ℕ) : ℝ :=
  floorSummatory chebyshevPsi (2 * N) - 2 * floorSummatory chebyshevPsi N

/-- **Exact Cancellation of the `2N log N - 2N` Double Pole in `chebyshevAlternatingProducer`:**
For every `N ≥ 1`,
`chebyshevAlternatingProducer N = (2 log 2) N + (stirlingResidual (2N) - 2 * stirlingResidual N)`. -/
theorem chebyshevAlternatingProducer_eq_linear_add_stirling {N : ℕ} (hN : 1 ≤ N) :
    chebyshevAlternatingProducer N =
      (2 * Real.log 2) * (N : ℝ) +
        (stirlingResidual (2 * N) - 2 * stirlingResidual N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold chebyshevAlternatingProducer
  rw [floorSummatory_chebyshevPsi_eq_main_add_stirlingResidual (2 * N),
    floorSummatory_chebyshevPsi_eq_main_add_stirlingResidual N]
  push_cast
  rw [Real.log_mul (by norm_num) hN0.ne']
  ring

/-- **Unconditional `O(log N)` Error Bound for the Chebyshev Alternating Producer:**
For every `N ≥ 1`, the alternating Chebyshev producer `T(2N) - 2 T(N)` tracks its exact polar slope
`(2 log 2) N` to within `2 log(2N + 1) + 1` (completely bypassing the `O(√N)` Dirichlet divisor
barrier!):
`|chebyshevAlternatingProducer N - (2 log 2) N| ≤ 2 * log(2N + 1) + 1`. -/
theorem abs_chebyshevAlternatingProducer_sub_linear_le {N : ℕ} (hN : 1 ≤ N) :
    |chebyshevAlternatingProducer N - (2 * Real.log 2) * (N : ℝ)| ≤
      2 * Real.log (2 * (N : ℝ) + 1) + 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hlo2, hup2⟩ := stirlingResidual_bounds (by omega : 1 ≤ 2 * N)
  obtain ⟨hlo1, hup1⟩ := stirlingResidual_bounds hN
  push_cast at hlo2 hup2
  have hlog_mono : Real.log ((N : ℝ) + 1) ≤ Real.log (2 * (N : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog_nonneg : 0 ≤ Real.log (2 * (N : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  rw [chebyshevAlternatingProducer_eq_linear_add_stirling hN]
  have hsub :
      (2 * Real.log 2) * (N : ℝ) + (stirlingResidual (2 * N) - 2 * stirlingResidual N) -
        (2 * Real.log 2) * (N : ℝ) =
      stirlingResidual (2 * N) - 2 * stirlingResidual N := by ring
  rw [hsub, abs_le]
  constructor <;> linarith

/-- **Chebyshev–von Mangoldt Floor Identity:**
`floorSummatory chebyshevPsi K = ∑ d ∈ Icc 1 K, Λ(d) * ((K / d : ℕ) : ℝ)`. -/
theorem floorSummatory_chebyshevPsi_eq_sum_vonMangoldt_mul_div (K : ℕ) :
    floorSummatory chebyshevPsi K =
      ∑ d ∈ Finset.Icc 1 K, vonMangoldt d * ((K / d : ℕ) : ℝ) := by
  have hswap := sum_Icc_mul_apply vonMangoldt
    ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) K
  rw [vonMangoldt_mul_zeta] at hswap
  have hlogs : ∑ n ∈ Finset.Icc 1 K, ArithmeticFunction.log n =
      floorSummatory chebyshevPsi K := by
    rw [floorSummatory_chebyshevPsi]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [log_apply]
  have hrhs :
      (∑ d ∈ Finset.Icc 1 K,
        vonMangoldt d * ∑ m ∈ Finset.Icc 1 (K / d),
          ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) m) =
      ∑ d ∈ Finset.Icc 1 K, vonMangoldt d * ((K / d : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    have h1 :
        (∑ m ∈ Finset.Icc 1 (K / d),
          ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) m) =
        ∑ _ ∈ Finset.Icc 1 (K / d), (1 : ℝ) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mem_Icc] at hm
      rw [natCoe_apply, zeta_apply, if_neg (by omega)]
      norm_num
    rw [h1, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  rw [← hlogs, hswap, hrhs]

/-- **Double-Numerator Floor Division Inequality:**
For any `N, d : ℕ`, `2 * (N / d) ≤ (2 * N) / d`. -/
theorem two_mul_div_le_two_mul_div (N d : ℕ) : 2 * (N / d) ≤ (2 * N) / d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [Nat.le_div_iff_mul_le hd]
    calc 2 * (N / d) * d = 2 * (N / d * d) := by ring
      _ ≤ 2 * N := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self N d)

/-- **Unconditional Dyadic Prime-Block Lower Bound for `chebyshevAlternatingProducer`:**
Because `(2N)/d - 2(N/d) ≥ 0` for all `d ≥ 1` and is `≥ 1` for `N < d ≤ 2N`, the dyadic Chebyshev
prime block `ψ(2N) - ψ(N)` is bounded above by `chebyshevAlternatingProducer N`:
`chebyshevPsi (2 * N) - chebyshevPsi N ≤ chebyshevAlternatingProducer N`. -/
theorem chebyshevPsi_two_mul_sub_le_alternatingProducer (N : ℕ) :
    chebyshevPsi (2 * N) - chebyshevPsi N ≤ chebyshevAlternatingProducer N := by
  unfold chebyshevAlternatingProducer
  rw [floorSummatory_chebyshevPsi_eq_sum_vonMangoldt_mul_div (2 * N),
    floorSummatory_chebyshevPsi_eq_sum_vonMangoldt_mul_div N]
  unfold chebyshevPsi
  have hsub_sub_floor :
      (∑ d ∈ Finset.Icc 1 N, vonMangoldt d * ((N / d : ℕ) : ℝ)) =
        ∑ d ∈ Finset.Icc 1 (2 * N),
          if d ≤ N then vonMangoldt d * ((N / d : ℕ) : ℝ) else 0 := by
    calc (∑ d ∈ Finset.Icc 1 N, vonMangoldt d * ((N / d : ℕ) : ℝ))
        = ∑ d ∈ Finset.Icc 1 N,
            if d ≤ N then vonMangoldt d * ((N / d : ℕ) : ℝ) else 0 := by
          refine Finset.sum_congr rfl fun d hd => ?_
          rw [Finset.mem_Icc] at hd
          rw [if_pos hd.2]
      _ = ∑ d ∈ Finset.Icc 1 (2 * N),
            if d ≤ N then vonMangoldt d * ((N / d : ℕ) : ℝ) else 0 := by
          refine Finset.sum_subset (Finset.Icc_subset_Icc_right (by omega : N ≤ 2 * N)) ?_
          intro d hd hnot
          rw [Finset.mem_Icc] at hd hnot
          rw [if_neg (by omega)]
  have hsub_psi :
      (∑ d ∈ Finset.Icc 1 N, vonMangoldt d) =
        ∑ d ∈ Finset.Icc 1 (2 * N), if d ≤ N then vonMangoldt d else 0 := by
    calc (∑ d ∈ Finset.Icc 1 N, vonMangoldt d)
        = ∑ d ∈ Finset.Icc 1 N, if d ≤ N then vonMangoldt d else 0 := by
          refine Finset.sum_congr rfl fun d hd => ?_
          rw [Finset.mem_Icc] at hd
          rw [if_pos hd.2]
      _ = ∑ d ∈ Finset.Icc 1 (2 * N), if d ≤ N then vonMangoldt d else 0 := by
          refine Finset.sum_subset (Finset.Icc_subset_Icc_right (by omega : N ≤ 2 * N)) ?_
          intro d hd hnot
          rw [Finset.mem_Icc] at hd hnot
          rw [if_neg (by omega)]
  rw [hsub_psi, hsub_sub_floor, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  by_cases hdN : d ≤ N
  · rw [if_pos hdN, if_pos hdN, sub_self]
    have hdiv : ((2 * (N / d) : ℕ) : ℝ) ≤ (((2 * N) / d : ℕ) : ℝ) :=
      Nat.cast_le.mpr (two_mul_div_le_two_mul_div N d)
    push_cast at hdiv
    have hvm : 0 ≤ vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
    nlinarith
  · rw [if_neg hdN, if_neg hdN, sub_zero, mul_zero, sub_zero]
    have hge1 : 1 ≤ (2 * N) / d := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
      omega
    have hge1R : (1 : ℝ) ≤ (((2 * N) / d : ℕ) : ℝ) := by exact_mod_cast hge1
    have hvm : 0 ≤ vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
    nlinarith

/-- **Unconditional Chebyshev Dyadic Prime-Block Upper Bound:**
For every `N ≥ 1`,
`chebyshevPsi (2 * N) - chebyshevPsi N ≤ (2 * log 2) * N + 2 * log(2N + 1) + 1`. -/
theorem chebyshevPsi_two_mul_sub_le_linear_add_log {N : ℕ} (hN : 1 ≤ N) :
    chebyshevPsi (2 * N) - chebyshevPsi N ≤
      (2 * Real.log 2) * (N : ℝ) + 2 * Real.log (2 * (N : ℝ) + 1) + 1 := by
  have h1 := chebyshevPsi_two_mul_sub_le_alternatingProducer N
  have h2 := (abs_le.mp (abs_chebyshevAlternatingProducer_sub_linear_le hN)).2
  linarith

/-- **Double-Numerator Floor Division Upper Step Inequality:**
For any `N, d : ℕ`, `(2 * N) / d ≤ 2 * (N / d) + 1`. -/
theorem two_mul_div_le_two_mul_div_add_one (N d : ℕ) :
    (2 * N) / d ≤ 2 * (N / d) + 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hlt : (2 * N) / d < 2 * (N / d) + 2 := by
      rw [Nat.div_lt_iff_lt_mul hd]
      have hmod := Nat.div_add_mod N d
      have hrem := Nat.mod_lt N hd
      calc 2 * N = 2 * (d * (N / d) + N % d) := by rw [hmod]
        _ < 2 * (d * (N / d) + d) := by omega
        _ = (2 * (N / d) + 2) * d := by ring
    omega

/-- **Unconditional Cumulative Prime Upper Bound for `chebyshevAlternatingProducer`:**
Because `(2N)/d - 2(N/d) ≤ 1` for every `d ≥ 1` and `Λ(d) ≥ 0`, the alternating producer
`chebyshevAlternatingProducer N` is bounded above by `chebyshevPsi (2 * N)`:
`chebyshevAlternatingProducer N ≤ chebyshevPsi (2 * N)`. -/
theorem chebyshevAlternatingProducer_le_chebyshevPsi_two_mul (N : ℕ) :
    chebyshevAlternatingProducer N ≤ chebyshevPsi (2 * N) := by
  unfold chebyshevAlternatingProducer
  rw [floorSummatory_chebyshevPsi_eq_sum_vonMangoldt_mul_div (2 * N),
    floorSummatory_chebyshevPsi_eq_sum_vonMangoldt_mul_div N]
  unfold chebyshevPsi
  have hsub_sub_floor :
      (∑ d ∈ Finset.Icc 1 N, vonMangoldt d * ((N / d : ℕ) : ℝ)) =
        ∑ d ∈ Finset.Icc 1 (2 * N),
          if d ≤ N then vonMangoldt d * ((N / d : ℕ) : ℝ) else 0 := by
    calc (∑ d ∈ Finset.Icc 1 N, vonMangoldt d * ((N / d : ℕ) : ℝ))
        = ∑ d ∈ Finset.Icc 1 N,
            if d ≤ N then vonMangoldt d * ((N / d : ℕ) : ℝ) else 0 := by
          refine Finset.sum_congr rfl fun d hd => ?_
          rw [Finset.mem_Icc] at hd
          rw [if_pos hd.2]
      _ = ∑ d ∈ Finset.Icc 1 (2 * N),
            if d ≤ N then vonMangoldt d * ((N / d : ℕ) : ℝ) else 0 := by
          refine Finset.sum_subset (Finset.Icc_subset_Icc_right (by omega : N ≤ 2 * N)) ?_
          intro d hd hnot
          rw [Finset.mem_Icc] at hd hnot
          rw [if_neg (by omega)]
  rw [hsub_sub_floor, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  by_cases hdN : d ≤ N
  · rw [if_pos hdN]
    have hdiv : (((2 * N) / d : ℕ) : ℝ) ≤ ((2 * (N / d) + 1 : ℕ) : ℝ) :=
      Nat.cast_le.mpr (two_mul_div_le_two_mul_div_add_one N d)
    push_cast at hdiv
    have hvm : 0 ≤ vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
    nlinarith
  · rw [if_neg hdN, mul_zero, sub_zero]
    have hdiv0 : N / d = 0 := Nat.div_eq_of_lt (by omega)
    have hdiv : (2 * N) / d ≤ 1 := by
      have h := two_mul_div_le_two_mul_div_add_one N d
      rw [hdiv0] at h
      omega
    have hdivR : (((2 * N) / d : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hdiv
    have hvm : 0 ≤ vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
    nlinarith

/-- **Unconditional Chebyshev Linear Lower Bound Producer:**
For every `N ≥ 1`,
`(2 * log 2) * N - (2 * log(2N + 1) + 1) ≤ chebyshevPsi (2 * N)`. -/
theorem linear_sub_log_le_chebyshevPsi_two_mul {N : ℕ} (hN : 1 ≤ N) :
    (2 * Real.log 2) * (N : ℝ) - (2 * Real.log (2 * (N : ℝ) + 1) + 1) ≤
      chebyshevPsi (2 * N) := by
  have h1 := chebyshevAlternatingProducer_le_chebyshevPsi_two_mul N
  have h2 := (abs_le.mp (abs_chebyshevAlternatingProducer_sub_linear_le hN)).1
  linarith

/-- **Second-Order Bi-Null Chebyshev Producer:**
`chebyshevBiNullProducer N := T(4N) - 4 T(2N) + 4 T(N) = chebyshevAlternatingProducer (2N) - 2 * chebyshevAlternatingProducer N`.
In Mellin space this applies the squared Nyman–Beurling / Chebyshev annihilator `(1 - 2 · 2^{-s})²`,
killing **both** the double pole `N log N` **and** the simple pole `N` at `s = 1` without
introducing Dirichlet's divisor summatory `D(N)`. -/
def chebyshevBiNullProducer (N : ℕ) : ℝ :=
  floorSummatory chebyshevPsi (4 * N) - 4 * floorSummatory chebyshevPsi (2 * N) +
    4 * floorSummatory chebyshevPsi N

/-- **Exact Second-Difference Decomposition of `chebyshevBiNullProducer`:**
`chebyshevBiNullProducer N = chebyshevAlternatingProducer (2 * N) - 2 * chebyshevAlternatingProducer N`. -/
theorem chebyshevBiNullProducer_eq_alternating_diff (N : ℕ) :
    chebyshevBiNullProducer N =
      chebyshevAlternatingProducer (2 * N) - 2 * chebyshevAlternatingProducer N := by
  unfold chebyshevBiNullProducer chebyshevAlternatingProducer
  rw [show 2 * (2 * N) = 4 * N by ring]
  ring

/-- **Exact Cancellation of Both `N log N` and `N` Main Terms in `chebyshevBiNullProducer`:**
For every `N ≥ 1`, the `N log N` and `N` main terms cancel identically, leaving purely the second
dyadic difference of `stirlingResidual`:
`chebyshevBiNullProducer N = stirlingResidual (4 * N) - 4 * stirlingResidual (2 * N) + 4 * stirlingResidual N`. -/
theorem chebyshevBiNullProducer_eq_stirling_second_diff {N : ℕ} (hN : 1 ≤ N) :
    chebyshevBiNullProducer N =
      stirlingResidual (4 * N) - 4 * stirlingResidual (2 * N) + 4 * stirlingResidual N := by
  rw [chebyshevBiNullProducer_eq_alternating_diff,
    chebyshevAlternatingProducer_eq_linear_add_stirling (by omega : 1 ≤ 2 * N),
    chebyshevAlternatingProducer_eq_linear_add_stirling hN]
  rw [show 2 * (2 * N) = 4 * N by ring]
  push_cast
  ring

/-- **Unconditional `O(log N)` Bound for the Bi-Null Chebyshev Producer (`Trap / √N-Barrier Bypass`):**
For every `N ≥ 1`,
`|chebyshevBiNullProducer N| ≤ 5 * log(4N + 1) + 1`.
Whereas `floorSummatory psiDefect N` in `PsiDefectSqrtBound.lean` only achieves `≤ 24 √N` due to
Dirichlet divisor contamination from subtracting `j` inside the floor summatory, the bi-null
Chebyshev producer cancels both `s = 1` poles via dyadic dilation and achieves an unconditional
`O(log N)` bound—exponentially smaller than `√N`! -/
theorem abs_chebyshevBiNullProducer_le {N : ℕ} (hN : 1 ≤ N) :
    |chebyshevBiNullProducer N| ≤ 5 * Real.log (4 * (N : ℝ) + 1) + 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hlo4, hup4⟩ := stirlingResidual_bounds (by omega : 1 ≤ 4 * N)
  obtain ⟨hlo2, hup2⟩ := stirlingResidual_bounds (by omega : 1 ≤ 2 * N)
  obtain ⟨hlo1, hup1⟩ := stirlingResidual_bounds hN
  push_cast at hlo4 hup4 hlo2 hup2
  have hlog14 : Real.log ((N : ℝ) + 1) ≤ Real.log (4 * (N : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog24 : Real.log (2 * (N : ℝ) + 1) ≤ Real.log (4 * (N : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog4_nonneg : 0 ≤ Real.log (4 * (N : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  rw [chebyshevBiNullProducer_eq_stirling_second_diff hN, abs_le]
  constructor <;> linarith

end

end GaloisForLFunctions.BiScaleUncertainty

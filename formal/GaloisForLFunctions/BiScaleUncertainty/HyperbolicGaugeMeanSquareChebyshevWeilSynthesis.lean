import GaloisForLFunctions.BiScaleUncertainty.AllParityWeilPoleWeightFunctionalAndChebyshevSynthesis
import GaloisForLFunctions.BiScaleUncertainty.ChebyshevGaugeNyquistCellQuadrature
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarRoughGauge
import GaloisForLFunctions.BiScaleUncertainty.AnnularGaugeEnergy

/-!
# Pillar XXVIII: Hyperbolic-Gauge Mean-Square Chebyshev & Nyquist-Cell Weil Functional Synthesis

This module synthesizes:
1. **Pillar XXVII** (`AllParityWeilPoleWeightFunctionalAndChebyshevSynthesis`), which proved the
   universal pole-to-Chebyshev absorption identity and unconditional Chebyshev–packet lower bound
   for `(weilFullFunctional Λ (weilTest f f)).re` across the entire real Weil test space
   `RealWeilTestFn` (as well as `RealEvenPolarTestFn`, `RealSmoothEvenPolarTestFn`, and
   `RealOddTestFn`);
2. **Hyperbolic-Gauge Chebyshev Energy Representation** (`HyperbolicGaugeChebyshevEnergyRepresentation`),
   which represents the signed prime–polar packet $P_{f,N}(u)$ in the critical-line hyperbolic
   gauge $f \mapsto f' - f/2 = e^{u/2}(e^{-u/2}f)'$ and bounds `packetEnergy f N` by the
   mean-square normalized Chebyshev error $\int_0^L \tilde{E}(t)^2\,dt = \int_1^{e^L} \frac{(\psi(x)-x)^2}{x^2}\,dx$;
3. **Nyquist-Cell Quadrature** (`ChebyshevGaugeNyquistCellQuadrature`), which evaluates the
   mean-square normalized Chebyshev error on each Nyquist cell $[\log n, \log(n+1))$ and proves
   the exact two-sided discrete cell-center inequality
   $$\sum_{n=1}^{N+1} \frac{(\psi(n) - m_n)^2}{n(n+1)}
     \;\le\; \int_0^{\operatorname{cutoff} N} \tilde{E}(t)^2\,dt
     \;\le\; \sum_{n=1}^{N+1} \frac{(\psi(n) - m_n)^2}{n(n+1)} + 2;$$
4. **Rough-Source Collar Gauge Control** (`SignedPrimePolarRoughGauge`), which replaces the
   derivative gauge $f' - f/2$ by the derivative-free finite-difference collar slope on an
   independent smoothing collar $[e^{a_0}, e^{a_0} + e^{b_0}]$.

Because every explicit-formula test function `f : RealWeilTestFn` has $C^2$ compactly supported
source `f.source`, it automatically satisfies `ContDiff ℝ 1 f.source` with **zero regularity
hypotheses**. Consequently, we obtain **100% unconditional** lower bounds on the full untruncated
Weil explicit-formula functional `(weilFullFunctional Λ (weilTest f f)).re` in terms of:
- the archimedean gamma term $\Omega(0)\,k_f(0)$ and the positive-definite Lévy–sinh energy
  $(1 - 2e^c)\,\operatorname{biScaleLevyEnergy}(f.\mathrm{source})$,
- the annular Chebyshev work functional $\operatorname{chebyshevWork}(f, a, b, N)$, and
- either the continuous mean-square Chebyshev gauge bound (`smoothGaugeBound`), the discrete
  Nyquist-cell centered Chebyshev sum (`discreteCellGaugeBound`), or the derivative-free rough
  collar gauge bound (`roughGaugeBound`).
-/

open MeasureTheory Set Filter
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open GaloisForLFunctions.WeilExplicit

namespace GaloisForLFunctions.BiScaleUncertainty

local notation "EF" => GaloisForLFunctions.WeilExplicit.ExplicitFormula
local notation "WMS" => RHTower.WeilMarkovSigning

noncomputable section
set_option autoImplicit false

/-! ## §1. Unconditional Cutoff-Level Nyquist-Cell Quadrature and Gauge Energy Bounds -/

/-- The discrete Nyquist-cell centered Chebyshev mean-square sum up to cutoff index `N`
(covering integers $1 \le n \le N + 1$, i.e., cells $[\log n, \log(n+1))$ up to
$\operatorname{cutoff} N = \log(N+2)$):
$$\operatorname{discreteChebyshevCellSum}(N)
  := \sum_{k=0}^{N} \frac{(\psi(k+1) - m_{k+1})^2}{(k+1)(k+2)},$$
where $m_n = n(n+1)\log((n+1)/n) \in [n, n+1]$ is the optimal Nyquist cell center. -/
def discreteChebyshevCellSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1),
    (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ChebyshevGauge.cellCenter (k + 1)) ^ 2 /
      (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))

theorem discreteChebyshevCellSum_nonneg (N : ℕ) :
    0 ≤ discreteChebyshevCellSum N := by
  unfold discreteChebyshevCellSum
  refine Finset.sum_nonneg fun k _ => ?_
  positivity

/-- For every `N : ℕ`, `SignedPrimePolar.cutoff N = Real.log ((N + 2 : ℕ) : ℝ)`. -/
theorem cutoff_eq_log_nat (N : ℕ) :
    SignedPrimePolar.cutoff N = Real.log ((N + 2 : ℕ) : ℝ) := by
  unfold SignedPrimePolar.cutoff
  congr 1
  push_cast
  ring

/-- For every `N : ℕ`, `Real.exp (SignedPrimePolar.cutoff N) = (N : ℝ) + 2`. -/
theorem exp_cutoff_eq (N : ℕ) :
    Real.exp (SignedPrimePolar.cutoff N) = (N : ℝ) + 2 := by
  unfold SignedPrimePolar.cutoff
  exact Real.exp_log (by positivity)

/-- **Unconditional Mean-Square Chebyshev Dictionary at `cutoff N`:**
For every `N : ℕ` (with **zero hypotheses**!),
$$\int_{t \in [0, \operatorname{cutoff} N]} \tilde{E}(t)^2\,dt
  = \int_{x \in [1, N+2]} \frac{(\psi(x) - x)^2}{x^2}\,dx.$$ -/
theorem integral_normalizedLogError_sq_cutoff_eq_chebyshev_mean_square (N : ℕ) :
    (∫ t in Icc 0 (SignedPrimePolar.cutoff N), ChebyshevGauge.normalizedLogError t ^ 2) =
      ∫ x in Icc 1 ((N : ℝ) + 2), (Chebyshev.psi x - x) ^ 2 / x ^ 2 := by
  rw [ChebyshevGauge.integral_normalizedLogError_sq_eq (SignedPrimePolar.cutoff N),
    exp_cutoff_eq N]

/-- **Unconditional Nyquist-Cell Decomposition at `cutoff N`:**
For every `N : ℕ` (with **zero hypotheses**!),
$$\int_{t \in [0, \operatorname{cutoff} N]} \tilde{E}(t)^2\,dt
  = \operatorname{discreteChebyshevCellSum}(N)
    + \sum_{k=0}^{N} \operatorname{cellFloor}(k+1).$$ -/
theorem integral_normalizedLogError_sq_cutoff_eq_sum_center_add_floor (N : ℕ) :
    (∫ t in Icc 0 (SignedPrimePolar.cutoff N), ChebyshevGauge.normalizedLogError t ^ 2) =
      discreteChebyshevCellSum N +
        ∑ k ∈ Finset.range (N + 1), ChebyshevGauge.cellFloor (k + 1) := by
  rw [cutoff_eq_log_nat N]
  have hM : 1 ≤ N + 2 := by omega
  have h := ChebyshevGauge.integral_normalizedLogError_sq_eq_sum_center_add_floor hM
  have hsub : N + 2 - 1 = N + 1 := by omega
  rw [hsub] at h
  exact h

/-- **Unconditional Two-Sided Discrete Nyquist-Cell Bound at `cutoff N`:**
For every `N : ℕ` (with **zero hypotheses**!),
$$\operatorname{discreteChebyshevCellSum}(N)
  \;\le\; \int_{t \in [0, \operatorname{cutoff} N]} \tilde{E}(t)^2\,dt
  \;\le\; \operatorname{discreteChebyshevCellSum}(N) + 2.$$ -/
theorem sum_center_sq_le_integral_cutoff_le (N : ℕ) :
    discreteChebyshevCellSum N ≤
        (∫ t in Icc 0 (SignedPrimePolar.cutoff N), ChebyshevGauge.normalizedLogError t ^ 2) ∧
      (∫ t in Icc 0 (SignedPrimePolar.cutoff N), ChebyshevGauge.normalizedLogError t ^ 2) ≤
        discreteChebyshevCellSum N + 2 := by
  rw [cutoff_eq_log_nat N]
  have hM : 1 ≤ N + 2 := by omega
  have h := ChebyshevGauge.sum_center_sq_le_integral_le hM
  have hsub : N + 2 - 1 = N + 1 := by omega
  rw [hsub] at h
  exact h

/-- The continuous hyperbolic-gauge mean-square Chebyshev upper bound for `packetEnergy f N`:
$$\operatorname{smoothGaugeBound}(f, N)
  := 3\bigl(10 + \tilde{E}(\operatorname{cutoff} N)^2\bigr)\,\operatorname{autocorr}(f, 0)
    + 3\left(\int_{\mathbb{R}} |f'(u) - f(u)/2|\,du\right)^2
      \int_0^{\operatorname{cutoff} N} \tilde{E}(t)^2\,dt.$$ -/
def smoothGaugeBound (f : C_c(ℝ, ℝ)) (N : ℕ) : ℝ :=
  3 * (10 + ChebyshevGauge.normalizedLogError (SignedPrimePolar.cutoff N) ^ 2) *
    autocorr f 0 +
  3 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
    ∫ t in Icc 0 (SignedPrimePolar.cutoff N), ChebyshevGauge.normalizedLogError t ^ 2

/-- The discrete Nyquist-cell centered Chebyshev upper bound for `packetEnergy f N`:
$$\operatorname{discreteCellGaugeBound}(f, N)
  := 3\bigl(10 + \tilde{E}(\operatorname{cutoff} N)^2\bigr)\,\operatorname{autocorr}(f, 0)
    + 3\left(\int_{\mathbb{R}} |f'(u) - f(u)/2|\,du\right)^2
      \bigl(\operatorname{discreteChebyshevCellSum}(N) + 2\bigr).$$ -/
def discreteCellGaugeBound (f : C_c(ℝ, ℝ)) (N : ℕ) : ℝ :=
  3 * (10 + ChebyshevGauge.normalizedLogError (SignedPrimePolar.cutoff N) ^ 2) *
    autocorr f 0 +
  3 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
    (discreteChebyshevCellSum N + 2)

theorem smoothGaugeBound_nonneg (f : C_c(ℝ, ℝ)) (N : ℕ) :
    0 ≤ smoothGaugeBound f N := by
  unfold smoothGaugeBound
  have h0 : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  have h1 : 0 ≤ ∫ t in Icc 0 (SignedPrimePolar.cutoff N),
      ChebyshevGauge.normalizedLogError t ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  positivity

theorem smoothGaugeBound_le_discreteCellGaugeBound (f : C_c(ℝ, ℝ)) (N : ℕ) :
    smoothGaugeBound f N ≤ discreteCellGaugeBound f N := by
  unfold smoothGaugeBound discreteCellGaugeBound
  have hcell := (sum_center_sq_le_integral_cutoff_le N).2
  have hmul :
      3 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
          (∫ t in Icc 0 (SignedPrimePolar.cutoff N), ChebyshevGauge.normalizedLogError t ^ 2) ≤
        3 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
          (discreteChebyshevCellSum N + 2) :=
    mul_le_mul_of_nonneg_left hcell (by positivity)
  linarith only [hmul]

theorem discreteCellGaugeBound_nonneg (f : C_c(ℝ, ℝ)) (N : ℕ) :
    0 ≤ discreteCellGaugeBound f N :=
  (smoothGaugeBound_nonneg f N).trans (smoothGaugeBound_le_discreteCellGaugeBound f N)

theorem packetEnergy_le_smoothGaugeBound (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    SignedPrimePolar.packetEnergy f N ≤ smoothGaugeBound f N :=
  ChebyshevGauge.packetEnergy_le_chebyshev_mean_square f hf N

theorem packetEnergy_le_discreteCellGaugeBound (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    SignedPrimePolar.packetEnergy f N ≤ discreteCellGaugeBound f N :=
  (packetEnergy_le_smoothGaugeBound f hf N).trans
    (smoothGaugeBound_le_discreteCellGaugeBound f N)

/-! ## §2. Unconditional Hyperbolic-Gauge & Nyquist-Cell Bounds on `RealWeilTestFn` -/

namespace RealWeilTestFn

/-- Every `f : RealWeilTestFn` has $C^1$ source **unconditionally** (from `ContDiff ℝ 2`). -/
theorem contDiff_one_source (f : RealWeilTestFn) :
    ContDiff ℝ 1 (f.toCompactlySupported : ℝ → ℝ) :=
  f.contDiff_source.of_le one_le_two

/-- **Unconditional Pointwise Hyperbolic-Gauge Identity on `RealWeilTestFn`:**
For every `f : RealWeilTestFn`, `N : ℕ`, and `u : ℝ` (with **zero hypotheses**!),
$$\operatorname{signedSource}(f.\mathrm{toCompactlySupported}, N, u)
  = \operatorname{forwardResidual}(f.\mathrm{source}, N, u)
    + \tilde{E}(\operatorname{cutoff} N)\,f.\mathrm{source}(u + \operatorname{cutoff} N)
    - \operatorname{chebyshevGaugeConvolution}(f.\mathrm{source}, N, u).$$ -/
theorem signedSource_eq_gauge (f : RealWeilTestFn) (N : ℕ) (u : ℝ) :
    SignedPrimePolar.signedSource f.toCompactlySupported N u =
      ChebyshevGauge.forwardResidual f.source N u +
        ChebyshevGauge.normalizedLogError (SignedPrimePolar.cutoff N) *
          f.source (u + SignedPrimePolar.cutoff N) -
        ChebyshevGauge.chebyshevGaugeConvolution f.source N u :=
  ChebyshevGauge.signedSource_eq_gauge f.toCompactlySupported f.contDiff_one_source N u

/-- **Unconditional Smooth Hyperbolic-Gauge Packet Energy Bound on `RealWeilTestFn`:**
For every `f : RealWeilTestFn` and `N : ℕ` (with **zero hypotheses**!),
$$\operatorname{packetEnergy}(f.\mathrm{toCompactlySupported}, N)
  \;\le\; \operatorname{smoothGaugeBound}(f.\mathrm{toCompactlySupported}, N).$$ -/
theorem packetEnergy_le_smoothGaugeBound (f : RealWeilTestFn) (N : ℕ) :
    SignedPrimePolar.packetEnergy f.toCompactlySupported N ≤
      BiScaleUncertainty.smoothGaugeBound f.toCompactlySupported N :=
  BiScaleUncertainty.packetEnergy_le_smoothGaugeBound
    f.toCompactlySupported f.contDiff_one_source N

/-- **Unconditional Discrete Nyquist-Cell Packet Energy Bound on `RealWeilTestFn`:**
For every `f : RealWeilTestFn` and `N : ℕ` (with **zero hypotheses**!),
$$\operatorname{packetEnergy}(f.\mathrm{toCompactlySupported}, N)
  \;\le\; \operatorname{discreteCellGaugeBound}(f.\mathrm{toCompactlySupported}, N).$$ -/
theorem packetEnergy_le_discreteCellGaugeBound (f : RealWeilTestFn) (N : ℕ) :
    SignedPrimePolar.packetEnergy f.toCompactlySupported N ≤
      BiScaleUncertainty.discreteCellGaugeBound f.toCompactlySupported N :=
  BiScaleUncertainty.packetEnergy_le_discreteCellGaugeBound
    f.toCompactlySupported f.contDiff_one_source N

private theorem integral_exp_neg_half_mul_sinh_nonneg (a b : ℝ) :
    0 ≤ ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y := by
  refine intervalIntegral.integral_nonneg (by linarith [Real.exp_pos b]) fun y hy => ?_
  have hy_pos : 0 < y := lt_of_lt_of_le (Real.exp_pos a) hy.1
  exact mul_nonneg (Real.exp_pos _).le (Real.sinh_pos_iff.mpr hy_pos).le

/-- **Unconditional Full Weil Functional Smooth Hyperbolic-Gauge Bound on `RealWeilTestFn`
(`RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_smoothGauge_bound`):**
For EVERY `f : RealWeilTestFn` and EVERY `a b c : ℝ` (with **zero hypotheses**!), the full
untruncated Weil functional of `Λ` is controlled by the archimedean Lévy–sinh energy, the
annular Chebyshev work, and the smooth hyperbolic-gauge mean-square Chebyshev bound
`smoothGaugeBound`:
$$\Bigl|(\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f\,f)).\mathrm{re}
  - \bigl(\operatorname{poleWeightArchRe}(0, f.1)
    - 2\,\operatorname{chebyshevWork}(f.\mathrm{toCompactlySupported}, a, b, f.\mathrm{supportScale})\bigr)\Bigr|$$
$$\le\; 2 e^c\,\operatorname{biScaleLevyEnergy}(f.\mathrm{source})
  + \frac{\operatorname{smoothGaugeBound}(f.\mathrm{toCompactlySupported}, f.\mathrm{supportScale})}{e^c e^{2b}}
    \int_{e^a}^{e^a + e^b} e^{-y/2}\sinh y\,dy.$$ -/
theorem unconditional_weilFullFunctional_vonMangoldt_smoothGauge_bound
    (f : RealWeilTestFn) (a b c : ℝ) :
    |(weilFullFunctional
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest f.1.1 f.1.1)).re -
        (poleWeightArchRe 0 f.1 -
          2 * SignedPrimePolar.chebyshevWork
            f.toCompactlySupported a b f.supportScale)| ≤
      2 * Real.exp c * biScaleLevyEnergy f.source +
        BiScaleUncertainty.smoothGaugeBound f.toCompactlySupported f.supportScale /
            (Real.exp c * Real.exp b ^ 2) *
          ∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y := by
  refine (f.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_bound a b c).trans ?_
  refine add_le_add le_rfl ?_
  refine mul_le_mul_of_nonneg_right ?_ (integral_exp_neg_half_mul_sinh_nonneg a b)
  exact div_le_div_of_nonneg_right (f.packetEnergy_le_smoothGaugeBound f.supportScale)
    (by positivity)

/-- **Unconditional Full Weil Functional Smooth Hyperbolic-Gauge Lower Bound on `RealWeilTestFn`
(`RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_smoothGauge_lower_bound`):**
For EVERY `f : RealWeilTestFn` and EVERY `a b c : ℝ` (with **zero hypotheses**!),
$$(1 - 2 e^c)\,\operatorname{biScaleLevyEnergy}(f.\mathrm{source})
  + \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
  - 2\,\operatorname{chebyshevWork}(f.\mathrm{toCompactlySupported}, a, b, f.\mathrm{supportScale})
  - \frac{\operatorname{smoothGaugeBound}(f.\mathrm{toCompactlySupported}, f.\mathrm{supportScale})}{e^c e^{2b}}
    \int_{e^a}^{e^a + e^b} e^{-y/2}\sinh y\,dy$$
$$\le\; (\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f\,f)).\mathrm{re}.$$ -/
theorem unconditional_weilFullFunctional_vonMangoldt_smoothGauge_lower_bound
    (f : RealWeilTestFn) (a b c : ℝ) :
    (1 - 2 * Real.exp c) * biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re -
        2 * SignedPrimePolar.chebyshevWork f.toCompactlySupported a b f.supportScale -
        BiScaleUncertainty.smoothGaugeBound f.toCompactlySupported f.supportScale /
            (Real.exp c * Real.exp b ^ 2) *
          (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re := by
  have habs := f.unconditional_weilFullFunctional_vonMangoldt_smoothGauge_bound a b c
  have hlow := neg_le_of_abs_le habs
  have hpole := f.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy
  linarith only [hlow, hpole]

/-- **Unconditional Full Weil Functional Discrete Nyquist-Cell Lower Bound on `RealWeilTestFn`
(`RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_discreteCellGauge_lower_bound`):**
For EVERY `f : RealWeilTestFn` and EVERY `a b c : ℝ` (with **zero hypotheses**!),
$$(1 - 2 e^c)\,\operatorname{biScaleLevyEnergy}(f.\mathrm{source})
  + \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
  - 2\,\operatorname{chebyshevWork}(f.\mathrm{toCompactlySupported}, a, b, f.\mathrm{supportScale})
  - \frac{\operatorname{discreteCellGaugeBound}(f.\mathrm{toCompactlySupported}, f.\mathrm{supportScale})}{e^c e^{2b}}
    \int_{e^a}^{e^a + e^b} e^{-y/2}\sinh y\,dy$$
$$\le\; (\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f\,f)).\mathrm{re}.$$ -/
theorem unconditional_weilFullFunctional_vonMangoldt_discreteCellGauge_lower_bound
    (f : RealWeilTestFn) (a b c : ℝ) :
    (1 - 2 * Real.exp c) * biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re -
        2 * SignedPrimePolar.chebyshevWork f.toCompactlySupported a b f.supportScale -
        BiScaleUncertainty.discreteCellGaugeBound f.toCompactlySupported f.supportScale /
            (Real.exp c * Real.exp b ^ 2) *
          (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re := by
  refine le_trans ?_ (f.unconditional_weilFullFunctional_vonMangoldt_smoothGauge_lower_bound a b c)
  have hcell :
      BiScaleUncertainty.smoothGaugeBound f.toCompactlySupported f.supportScale /
          (Real.exp c * Real.exp b ^ 2) *
        (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      BiScaleUncertainty.discreteCellGaugeBound f.toCompactlySupported f.supportScale /
          (Real.exp c * Real.exp b ^ 2) *
        (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) := by
    refine mul_le_mul_of_nonneg_right ?_ (integral_exp_neg_half_mul_sinh_nonneg a b)
    exact div_le_div_of_nonneg_right
      (smoothGaugeBound_le_discreteCellGaugeBound f.toCompactlySupported f.supportScale)
      (by positivity)
  linarith only [hcell]

/-- **Unconditional Full Weil Functional Derivative-Free Rough Collar Gauge Lower Bound on
`RealWeilTestFn` (`RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_roughGauge_lower_bound`):**
For EVERY `f : RealWeilTestFn`, smoothing collar `a₀ b₀ : ℝ`, and transport collar `a b c : ℝ`
(with **zero hypotheses**!), the full Weil functional is bounded below using only finite-difference
collar slopes (`roughGaugeBound`):
$$(1 - 2 e^c)\,\operatorname{biScaleLevyEnergy}(f.\mathrm{source})
  + \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
  - 2\,\operatorname{chebyshevWork}(f.\mathrm{toCompactlySupported}, a, b, f.\mathrm{supportScale})
  - \frac{\operatorname{roughGaugeBound}(f.\mathrm{toCompactlySupported}, a_0, b_0, f.\mathrm{supportScale})}{e^c e^{2b}}
    \int_{e^a}^{e^a + e^b} e^{-y/2}\sinh y\,dy$$
$$\le\; (\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f\,f)).\mathrm{re}.$$ -/
theorem unconditional_weilFullFunctional_vonMangoldt_roughGauge_lower_bound
    (f : RealWeilTestFn) (a₀ b₀ a b c : ℝ) :
    (1 - 2 * Real.exp c) * biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re -
        2 * SignedPrimePolar.chebyshevWork f.toCompactlySupported a b f.supportScale -
        SignedPrimePolar.roughGaugeBound f.toCompactlySupported a₀ b₀ f.supportScale /
            (Real.exp c * Real.exp b ^ 2) *
          (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re := by
  refine le_trans ?_
    (f.unconditional_weilFullFunctional_vonMangoldt_chebyshev_packet_lower_bound a b c)
  have hrough :
      SignedPrimePolar.packetEnergy f.toCompactlySupported f.supportScale /
          (Real.exp c * Real.exp b ^ 2) *
        (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      SignedPrimePolar.roughGaugeBound f.toCompactlySupported a₀ b₀ f.supportScale /
          (Real.exp c * Real.exp b ^ 2) *
        (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) := by
    refine mul_le_mul_of_nonneg_right ?_ (integral_exp_neg_half_mul_sinh_nonneg a b)
    exact div_le_div_of_nonneg_right
      (SignedPrimePolar.packetEnergy_le_roughGaugeBound
        f.toCompactlySupported a₀ b₀ f.supportScale)
      (by positivity)
  linarith only [hrough]

end RealWeilTestFn

/-! ## §3. Unconditional Lifts to `RealEvenPolarTestFn`, `RealSmoothEvenPolarTestFn`, and `RealOddTestFn` -/

namespace RealEvenPolarTestFn

/-- Every `g : RealEvenPolarTestFn` embeds into `RealWeilTestFn`. -/
def toRealWeilTestFn (g : RealEvenPolarTestFn) : RealWeilTestFn :=
  ⟨g.1.1, g.2⟩

@[simp]
theorem toRealWeilTestFn_source (g : RealEvenPolarTestFn) :
    g.toRealWeilTestFn.source = g.source := rfl

theorem contDiff_one_source (g : RealEvenPolarTestFn) :
    ContDiff ℝ 1 (g.toCompactlySupported : ℝ → ℝ) :=
  g.contDiff_source.of_le one_le_two

/-- **Unconditional Full Weil Functional Smooth Hyperbolic-Gauge Lower Bound on
`RealEvenPolarTestFn`:**
For EVERY `g : RealEvenPolarTestFn` and EVERY `a b c : ℝ` (with **zero hypotheses**!), -/
theorem unconditional_weilFullFunctional_vonMangoldt_smoothGauge_lower_bound
    (g : RealEvenPolarTestFn) (a b c : ℝ) :
    (1 - 2 * Real.exp c) * biScaleLevyEnergy g.source +
        EF.gammaBracket 0 * (EF.weilTest g.1.1.1 g.1.1.1 0).re -
        2 * SignedPrimePolar.chebyshevWork
          g.toCompactlySupported a b g.toRealWeilTestFn.supportScale -
        BiScaleUncertainty.smoothGaugeBound
            g.toCompactlySupported g.toRealWeilTestFn.supportScale /
            (Real.exp c * Real.exp b ^ 2) *
          (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest g.1.1.1 g.1.1.1)).re :=
  g.toRealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_smoothGauge_lower_bound a b c

/-- **Unconditional Full Weil Functional Discrete Nyquist-Cell Lower Bound on
`RealEvenPolarTestFn`:**
For EVERY `g : RealEvenPolarTestFn` and EVERY `a b c : ℝ` (with **zero hypotheses**!), -/
theorem unconditional_weilFullFunctional_vonMangoldt_discreteCellGauge_lower_bound
    (g : RealEvenPolarTestFn) (a b c : ℝ) :
    (1 - 2 * Real.exp c) * biScaleLevyEnergy g.source +
        EF.gammaBracket 0 * (EF.weilTest g.1.1.1 g.1.1.1 0).re -
        2 * SignedPrimePolar.chebyshevWork
          g.toCompactlySupported a b g.toRealWeilTestFn.supportScale -
        BiScaleUncertainty.discreteCellGaugeBound
            g.toCompactlySupported g.toRealWeilTestFn.supportScale /
            (Real.exp c * Real.exp b ^ 2) *
          (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest g.1.1.1 g.1.1.1)).re :=
  g.toRealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_discreteCellGauge_lower_bound
    a b c

end RealEvenPolarTestFn

namespace RealSmoothEvenPolarTestFn

/-- **Unconditional Full Weil Functional Discrete Nyquist-Cell Lower Bound on
`RealSmoothEvenPolarTestFn`:**
For EVERY `g : RealSmoothEvenPolarTestFn` and EVERY `a b c : ℝ` (with **zero hypotheses**!), -/
theorem unconditional_weilFullFunctional_vonMangoldt_discreteCellGauge_lower_bound
    (g : RealSmoothEvenPolarTestFn) (a b c : ℝ) :
    (1 - 2 * Real.exp c) * biScaleLevyEnergy g.source +
        EF.gammaBracket 0 * (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re -
        2 * SignedPrimePolar.chebyshevWork
          g.toCompactlySupported a b g.toRealEvenPolarTestFn.toRealWeilTestFn.supportScale -
        BiScaleUncertainty.discreteCellGaugeBound
            g.toCompactlySupported g.toRealEvenPolarTestFn.toRealWeilTestFn.supportScale /
            (Real.exp c * Real.exp b ^ 2) *
          (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest g.1.1.1.1 g.1.1.1.1)).re :=
  g.toRealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_discreteCellGauge_lower_bound
    a b c

end RealSmoothEvenPolarTestFn

namespace RealOddTestFn

/-- **Unconditional Full Weil Functional Smooth Hyperbolic-Gauge Lower Bound on
`RealOddTestFn`:**
For EVERY `f : RealOddTestFn` and EVERY `a b c : ℝ` (with **zero hypotheses**!), -/
theorem unconditional_weilFullFunctional_vonMangoldt_smoothGauge_lower_bound
    (f : RealOddTestFn) (a b c : ℝ) :
    (1 - 2 * Real.exp c) * biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1.1 f.1.1.1 0).re -
        2 * SignedPrimePolar.chebyshevWork
          f.toCompactlySupported a b f.toRealWeilTestFn.supportScale -
        BiScaleUncertainty.smoothGaugeBound
            f.toCompactlySupported f.toRealWeilTestFn.supportScale /
            (Real.exp c * Real.exp b ^ 2) *
          (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1.1 f.1.1.1)).re :=
  f.toRealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_smoothGauge_lower_bound a b c

/-- **Unconditional Full Weil Functional Discrete Nyquist-Cell Lower Bound on
`RealOddTestFn`:**
For EVERY `f : RealOddTestFn` and EVERY `a b c : ℝ` (with **zero hypotheses**!), -/
theorem unconditional_weilFullFunctional_vonMangoldt_discreteCellGauge_lower_bound
    (f : RealOddTestFn) (a b c : ℝ) :
    (1 - 2 * Real.exp c) * biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1.1 f.1.1.1 0).re -
        2 * SignedPrimePolar.chebyshevWork
          f.toCompactlySupported a b f.toRealWeilTestFn.supportScale -
        BiScaleUncertainty.discreteCellGaugeBound
            f.toCompactlySupported f.toRealWeilTestFn.supportScale /
            (Real.exp c * Real.exp b ^ 2) *
          (∫ y in Real.exp a..Real.exp a + Real.exp b, Real.exp (-y / 2) * Real.sinh y) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1.1 f.1.1.1)).re :=
  f.toRealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_discreteCellGauge_lower_bound
    a b c

end RealOddTestFn

end

end GaloisForLFunctions.BiScaleUncertainty

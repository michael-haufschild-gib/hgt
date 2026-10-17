import GaloisForLFunctions.BiScaleUncertainty.DivisorAverageChebyshevAndDyadicBlockVarianceProducer
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarSourceCertificate
import GaloisForLFunctions.BiScaleUncertainty.GaugeDualNormAndDivisorSampledResponse
import GaloisForLFunctions.BiScaleUncertainty.AllParityWeilPoleWeightFunctionalAndChebyshevSynthesis

/-!
# Pillar XXXVIII: Genuine Autocorrelation Weil Contrast & Divisor-Sampled Causal Response Producer

This module develops **Pillar XXXVIII** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`), establishing two unconditional producer instruments for
the CHMD (Causal Hyperbolic–Modular Duality) and Restricted-Weil proof routes:

1. **Tool 1 — Divisor-Sampled Causal Response Linear Channel & Bi-Null $(1, -4, 4)$ Stencil
   Producer (§1–§2):**
   - For the signed prime–polar causal response
     $$R_N(t) = e^{-t/2}\int_0^t e^{x/2}\,d\nu_N^{\mathrm{pol}}(x)$$
     (`SignedPrimePolar.causalResponse N t`), we define the **divisor-sampled causal response** at
     integer scale $K \ge 1$:
     $$\operatorname{divisorSampledCausalResponse}(N, K)
       := \sum_{j=1}^K \sqrt{\frac{K}{j}}\,R_N\!\left(\log\frac{K}{j}\right).$$
   - We prove that for every $1 \le K \le N + 2$, $\operatorname{divisorSampledCausalResponse}(N, K)$
     is **independent of the cutoff $N$**, equals both $\operatorname{pairing}(N, \operatorname{factorialLift} K)$
     and $\operatorname{fullPairing}(\operatorname{factorialLift} K)$, and lies unconditionally in
     the $K\log K$-free linear channel (`divisorSampledCausalResponse_bounds`):
     $$-2K \;\le\; \operatorname{divisorSampledCausalResponse}(N, K)
       \;\le\; -K + 2\log(K + 1) + 2.$$
   - Furthermore, taking the **$(1, -4, 4)$ dyadic bi-null stencil** across $(K, 2K, 4K)$ (for
     $1 \le K$ and $4K \le N + 2$) cancels the linear $-O(K)$ drift and Euler–Mascheroni harmonic
     constant identically (`divisorSampledCausalResponse_biNull_eq` and
     `abs_divisorSampledCausalResponse_biNull_le`):
     $$\operatorname{divisorSampledCausalResponse}(N, 4K)
       - 4\,\operatorname{divisorSampledCausalResponse}(N, 2K)
       + 4\,\operatorname{divisorSampledCausalResponse}(N, K)
       = 2\,\operatorname{chebyshevBiNullProducer}(K) - \operatorname{harmonicCorrection}(K),$$
     $$\left|\operatorname{divisorSampledCausalResponse}(N, 4K)
       - 4\,\operatorname{divisorSampledCausalResponse}(N, 2K)
       + 4\,\operatorname{divisorSampledCausalResponse}(N, K)\right|
       \;\le\; 10\log(4K + 1) + 3.$$
   - Combining `sq_pairing_le_laplaceEnergy_mul` with `laplaceEnergy_le_laplaceEnergyProducerBound`,
     we also obtain the prime-free gauge Sobolev dual-norm producer bound
     (`sq_pairing_le_laplaceEnergyProducerBound_mul`):
     $$\operatorname{pairing}(N, f)^2
       \;\le\; \operatorname{laplaceEnergyProducerBound}(N)
         \int_{\mathbb{R}} (\operatorname{gaugeDerivative}\,f\,t)^2\,dt.$$

2. **Tool 4 — Cutoff-Free Half-Line Weil Functional & Genuine Source Autocorrelation Contrast
   Producer (§3–§4):**
   - For every `f : RealWeilTestFn`, we prove that `fullPairing (autocorr f.source) =
     pairing N (autocorr f.source)` for all $N \ge f.\mathrm{supportScale}$, yielding the
     **cutoff-free half-line full Weil functional identity**
     (`RealWeilTestFn.re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_fullPairing`):
     $$(\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f\,f)).\mathrm{re}
       = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
         + \operatorname{biScaleLevyEnergy}(f.\mathrm{source})
         - 2\,\operatorname{fullPairing}(\operatorname{autocorr}\,f.\mathrm{source}).$$
   - For any two `f_+ f_- : RealWeilTestFn` with equal origin mass
     `autocorr f_+.source 0 = autocorr f_-.source 0`, the archimedean anomaly term $\Omega(0)h(0)$
     cancels identically (`RealWeilTestFn.re_weilFullFunctional_contrast_of_autocorr_zero_eq`).
   - On the genuine compactly supported source pair `factorialSourcePlus n` and
     `factorialSourceMinus n` (`C_c(ℝ, ℝ)`), where `autocorr (factorialSourcePlus n) 0 =
     autocorr (factorialSourceMinus n) 0 ≥ 6√(n+1)`, the half-line prime–polar contrast satisfies
     $$\frac{\operatorname{fullPairing}(\operatorname{autocorr}(\operatorname{factorialSourcePlus}\,n))
       - \operatorname{fullPairing}(\operatorname{autocorr}(\operatorname{factorialSourceMinus}\,n))}{2}
       = \operatorname{fullPairing}(\operatorname{factorialSourceProducer}\,n)$$
     (`fullPairing_autocorr_factorialSource_contrast_eq`), and the normalized prime–polar contrast
     ratio decays at rate $O(\log(n+1)/(n+1))$
     (`abs_fullPairing_factorialSourceProducer_div_autocorr_zero_le`):
     $$\frac{|\operatorname{fullPairing}(\operatorname{factorialSourceProducer}\,n)|}{\operatorname{autocorr}(\operatorname{factorialSourcePlus}\,n)\,0}
       \;\le\; \frac{10\log(4(n+1)+1) + 3 + \frac{1}{4(n+1)}}{6(n+1)}.$$
-/

open Complex MeasureTheory Set Filter Topology
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector RHTower.WeilOneSided RHTower.WeilPoleWeight
open scoped RealInnerProductSpace BigOperators CompactlySupported ArithmeticFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

open SignedPrimePolar ChebyshevGauge

/-! ## §1. Divisor-Sampled Causal Response Linear Channel & Bi-Null $(1, -4, 4)$ Stencil -/

/-- **Divisor-Sampled Causal Response at Integer Scale $K$:**
$$\operatorname{divisorSampledCausalResponse}(N, K)
  := \sum_{j=1}^K \sqrt{\frac{K}{j}}\,\operatorname{causalResponse}\,N\!\left(\log\frac{K}{j}\right).$$ -/
def divisorSampledCausalResponse (N K : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 K,
    Real.sqrt ((K : ℝ) / (j : ℝ)) * causalResponse N (Real.log ((K : ℝ) / (j : ℝ)))

/-- **Exact Evaluation of the Divisor-Sampled Causal Response:**
For every $1 \le K \le N + 2$,
$$\operatorname{divisorSampledCausalResponse}(N, K)
  = 2\,\operatorname{floorSummatory}(\psi, K) - K\log K - K H_K + K.$$ -/
theorem divisorSampledCausalResponse_eq_floorSummatory {N K : ℕ}
    (hK1 : 1 ≤ K) (hKN : K ≤ N + 2) :
    divisorSampledCausalResponse N K =
      2 * floorSummatory chebyshevPsi K - (K : ℝ) * Real.log (K : ℝ) -
        (K : ℝ) * realHarmonic K + (K : ℝ) := by
  unfold divisorSampledCausalResponse
  refine sum_sqrt_mul_causalResponse_log_ratio_eq N K hK1 ?_
  unfold cutoff
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hle : (K : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by exact_mod_cast hKN
  exact Real.log_le_log hKpos hle

/-- **Cutoff-Invariance & Identification with `fullPairing (factorialLift K)`:**
For every $1 \le K \le N + 2$,
$$\operatorname{divisorSampledCausalResponse}(N, K)
  = \operatorname{fullPairing}(\operatorname{factorialLift}\,K).$$ -/
theorem divisorSampledCausalResponse_eq_fullPairing_factorialLift {N K : ℕ}
    (hK1 : 1 ≤ K) (hKN : K ≤ N + 2) :
    divisorSampledCausalResponse N K = fullPairing (factorialLift K) := by
  rw [divisorSampledCausalResponse_eq_floorSummatory hK1 hKN, fullPairing_factorialLift_eq]

/-- **Identification with `pairing N (factorialLift K)`:**
For every $1 \le K \le N + 2$,
$$\operatorname{divisorSampledCausalResponse}(N, K)
  = \operatorname{pairing}\,N\,(\operatorname{factorialLift}\,K).$$ -/
theorem divisorSampledCausalResponse_eq_pairing_factorialLift {N K : ℕ}
    (hK1 : 1 ≤ K) (hKN : K ≤ N + 2) :
    divisorSampledCausalResponse N K = pairing N (factorialLift K) := by
  have hlog : Real.log (K : ℝ) ≤ cutoff N := by
    unfold cutoff
    exact Real.log_le_log (by exact_mod_cast hK1) (by exact_mod_cast hKN)
  rw [divisorSampledCausalResponse_eq_floorSummatory hK1 hKN,
    pairing_factorialLift_eq N K hK1 hlog]

/-- **Unconditional $K\log K$-Free Linear Channel for the Divisor-Sampled Causal Response:**
For every $1 \le K \le N + 2$,
$$-2K \;\le\; \operatorname{divisorSampledCausalResponse}(N, K)
  \;\le\; -K + 2\log(K + 1) + 2.$$ -/
theorem divisorSampledCausalResponse_bounds {N K : ℕ}
    (hK1 : 1 ≤ K) (hKN : K ≤ N + 2) :
    -2 * (K : ℝ) ≤ divisorSampledCausalResponse N K ∧
      divisorSampledCausalResponse N K ≤ -(K : ℝ) + 2 * Real.log ((K : ℝ) + 1) + 2 := by
  rw [divisorSampledCausalResponse_eq_fullPairing_factorialLift hK1 hKN]
  exact fullPairing_factorialLift_bounds hK1

/-- **Exact $(1, -4, 4)$ Bi-Null Stencil of the Divisor-Sampled Causal Response:**
For every $1 \le K$ with $4K \le N + 2$, the $(1, -4, 4)$ dyadic stencil across $(K, 2K, 4K)$
cancels both the $K\log K$ main term and the linear $-O(K)$ drift identically:
$$\operatorname{divisorSampledCausalResponse}(N, 4K)
  - 4\,\operatorname{divisorSampledCausalResponse}(N, 2K)
  + 4\,\operatorname{divisorSampledCausalResponse}(N, K)
  = 2\,\operatorname{chebyshevBiNullProducer}(K) - \operatorname{harmonicCorrection}(K).$$ -/
theorem divisorSampledCausalResponse_biNull_eq {N K : ℕ}
    (hK1 : 1 ≤ K) (hKN : 4 * K ≤ N + 2) :
    divisorSampledCausalResponse N (4 * K) -
        4 * divisorSampledCausalResponse N (2 * K) +
        4 * divisorSampledCausalResponse N K =
      2 * chebyshevBiNullProducer K - harmonicCorrection K := by
  rw [divisorSampledCausalResponse_eq_floorSummatory (by omega) hKN,
    divisorSampledCausalResponse_eq_floorSummatory (by omega) (by omega),
    divisorSampledCausalResponse_eq_floorSummatory hK1 (by omega)]
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have hlog2 : Real.log (2 * (K : ℝ)) = Real.log 2 + Real.log (K : ℝ) :=
    Real.log_mul (by norm_num) hK0
  have hlog4 : Real.log (4 * (K : ℝ)) = 2 * Real.log 2 + Real.log (K : ℝ) := by
    rw [Real.log_mul (by norm_num) hK0]
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [h4]
  unfold chebyshevBiNullProducer harmonicCorrection
  push_cast
  rw [hlog2, hlog4]
  ring

/-- **Normalized $(1, -4, 4)$ Divisor-Sampled Causal Response Equals `fullPairing (factorialBiNull K)`:**
For every $1 \le K$ with $4K \le N + 2$,
$$\frac{\operatorname{divisorSampledCausalResponse}(N, 4K)
  - 4\,\operatorname{divisorSampledCausalResponse}(N, 2K)
  + 4\,\operatorname{divisorSampledCausalResponse}(N, K)}{\sqrt{K}}
  = \operatorname{fullPairing}(\operatorname{factorialBiNull}\,K).$$ -/
theorem divisorSampledCausalResponse_biNull_div_sqrt_eq_fullPairing {N K : ℕ}
    (hK1 : 1 ≤ K) (hKN : 4 * K ≤ N + 2) :
    (divisorSampledCausalResponse N (4 * K) -
        4 * divisorSampledCausalResponse N (2 * K) +
        4 * divisorSampledCausalResponse N K) / Real.sqrt (K : ℝ) =
      fullPairing (factorialBiNull K) := by
  rw [divisorSampledCausalResponse_biNull_eq hK1 hKN, fullPairing_factorialBiNull_eq hK1]

/-- **Unconditional $O(\log K)$ Bound for the $(1, -4, 4)$ Divisor-Sampled Causal Response Stencil:**
For every $1 \le K$ with $4K \le N + 2$,
$$\left|\operatorname{divisorSampledCausalResponse}(N, 4K)
  - 4\,\operatorname{divisorSampledCausalResponse}(N, 2K)
  + 4\,\operatorname{divisorSampledCausalResponse}(N, K)\right|
  \;\le\; 10\log(4K + 1) + 3.$$ -/
theorem abs_divisorSampledCausalResponse_biNull_le {N K : ℕ}
    (hK1 : 1 ≤ K) (hKN : 4 * K ≤ N + 2) :
    |divisorSampledCausalResponse N (4 * K) -
        4 * divisorSampledCausalResponse N (2 * K) +
        4 * divisorSampledCausalResponse N K| ≤
      10 * Real.log (4 * (K : ℝ) + 1) + 3 := by
  rw [divisorSampledCausalResponse_biNull_eq hK1 hKN]
  have hb := abs_chebyshevBiNullProducer_le hK1
  obtain ⟨hc0, hc1⟩ := harmonicCorrection_bounds hK1
  calc
    |2 * chebyshevBiNullProducer K - harmonicCorrection K|
      ≤ |2 * chebyshevBiNullProducer K| + |harmonicCorrection K| := abs_sub _ _
    _ = 2 * |chebyshevBiNullProducer K| + harmonicCorrection K := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hc0]
    _ ≤ 10 * Real.log (4 * (K : ℝ) + 1) + 3 := by linarith

/-! ## §2. Prime-Free Gauge Sobolev Dual-Norm Producer Bounds -/

/-- **Prime-Free Squared Gauge Sobolev Dual-Norm Producer Bound:**
For every $N : \mathbb{N}$ and every compactly supported $C^1$ function $f : C_c(\mathbb{R}, \mathbb{R})$,
$$\operatorname{pairing}(N, f)^2
  \;\le\; \operatorname{laplaceEnergyProducerBound}(N)
    \int_{\mathbb{R}} (\operatorname{gaugeDerivative}\,f\,t)^2\,dt.$$ -/
theorem sq_pairing_le_laplaceEnergyProducerBound_mul
    (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    pairing N f ^ 2 ≤
      laplaceEnergyProducerBound N * ∫ t : ℝ, (gaugeDerivative f t) ^ 2 := by
  have h1 := sq_pairing_le_laplaceEnergy_mul f hf N
  have h2 := laplaceEnergy_le_laplaceEnergyProducerBound N
  have hint_nn : 0 ≤ ∫ t : ℝ, (gaugeDerivative f t) ^ 2 :=
    integral_nonneg fun t => sq_nonneg _
  exact h1.trans (mul_le_mul_of_nonneg_right h2 hint_nn)

/-- **Prime-Free Gauge Sobolev Dual-Norm Producer Bound:**
For every $N : \mathbb{N}$ and every compactly supported $C^1$ function $f : C_c(\mathbb{R}, \mathbb{R})$,
$$|\operatorname{pairing}(N, f)|
  \;\le\; \sqrt{\operatorname{laplaceEnergyProducerBound}(N)}
    \cdot \sqrt{\int_{\mathbb{R}} (\operatorname{gaugeDerivative}\,f\,t)^2\,dt}.$$ -/
theorem abs_pairing_le_sqrt_laplaceEnergyProducerBound_mul
    (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    |pairing N f| ≤
      Real.sqrt (laplaceEnergyProducerBound N) *
        Real.sqrt (∫ t : ℝ, (gaugeDerivative f t) ^ 2) := by
  have h1 := abs_pairing_le_sqrt_laplaceEnergy_mul f hf N
  have h2 : Real.sqrt (laplaceEnergy N) ≤ Real.sqrt (laplaceEnergyProducerBound N) :=
    Real.sqrt_le_sqrt (laplaceEnergy_le_laplaceEnergyProducerBound N)
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _))

/-! ## §3. Cutoff-Free Half-Line Full Weil Functional & Equal-Origin Contrast Law -/

namespace RealWeilTestFn

/-- **Stabilization of `pairing N (autocorr f.source)` to `fullPairing (autocorr f.source)`:**
For every `f : RealWeilTestFn` and every $N \ge f.\mathrm{supportScale}$,
$$\operatorname{fullPairing}(\operatorname{autocorr}\,f.\mathrm{source})
  = \operatorname{pairing}\,N\,(\operatorname{autocorr}\,f.\mathrm{source}).$$ -/
theorem fullPairing_autocorr_eq_pairing_of_supportScale_le
    (f : RealWeilTestFn) {N : ℕ} (hN : f.supportScale ≤ N) :
    fullPairing (autocorr f.source) = pairing N (autocorr f.source) :=
  fullPairing_eq_pairing_of_tail (autocorr f.source) N fun _ hx =>
    f.autocorr_eq_zero_of_cutoff_le hN hx

/-- **Specialization at `N = f.supportScale`:** -/
theorem fullPairing_autocorr_eq_pairing_supportScale (f : RealWeilTestFn) :
    fullPairing (autocorr f.source) = pairing f.supportScale (autocorr f.source) :=
  f.fullPairing_autocorr_eq_pairing_of_supportScale_le le_rfl

/-- **Cutoff-Free Half-Line Full Weil Functional Identity on `RealWeilTestFn`:**
For EVERY `f : RealWeilTestFn` (even, odd, or arbitrary, with **zero** parity or polar hypotheses!),
$$(\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f\,f)).\mathrm{re}
  = \Omega(0)\,(\operatorname{weilTest}\,f\,f\,0).\mathrm{re}
    + \operatorname{biScaleLevyEnergy}(f.\mathrm{source})
    - 2\,\operatorname{fullPairing}(\operatorname{autocorr}\,f.\mathrm{source}).$$ -/
theorem re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_fullPairing
    (f : RealWeilTestFn) :
    (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re =
      EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re +
        biScaleLevyEnergy f.source -
        2 * fullPairing (autocorr f.source) := by
  rw [f.fullPairing_autocorr_eq_pairing_supportScale]
  exact f.re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_pairing

/-- **Equal-Origin Full Weil Functional Contrast Law on `RealWeilTestFn`:**
For ANY two real Weil test functions `f_+ f_- : RealWeilTestFn` whose sources have equal $L^2$
norm (`autocorr f_+.source 0 = autocorr f_-.source 0`), the archimedean anomaly term
$\Omega(0)\,h(0)$ cancels identically in the difference:
$$(\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f_+\,f_+)).\mathrm{re}
  - (\operatorname{weilFullFunctional}\,\Lambda\,(\operatorname{weilTest}\,f_-\,f_-)).\mathrm{re}$$
$$= (\operatorname{biScaleLevyEnergy}(f_+.\mathrm{source})
    - \operatorname{biScaleLevyEnergy}(f_-.\mathrm{source}))
  - 2\,(\operatorname{fullPairing}(\operatorname{autocorr}\,f_+.\mathrm{source})
    - \operatorname{fullPairing}(\operatorname{autocorr}\,f_-.\mathrm{source})).$$ -/
theorem re_weilFullFunctional_contrast_of_autocorr_zero_eq
    (fPlus fMinus : RealWeilTestFn)
    (h0 : autocorr fPlus.source 0 = autocorr fMinus.source 0) :
    (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest fPlus.1.1 fPlus.1.1)).re -
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest fMinus.1.1 fMinus.1.1)).re =
      (biScaleLevyEnergy fPlus.source - biScaleLevyEnergy fMinus.source) -
        2 * (fullPairing (autocorr fPlus.source) - fullPairing (autocorr fMinus.source)) := by
  rw [fPlus.re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_fullPairing,
    fMinus.re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_fullPairing,
    ← fPlus.autocorr_eq 0, ← fMinus.autocorr_eq 0, h0]
  ring

end RealWeilTestFn

/-! ## §4. Genuine Source Autocorrelation Contrast Producer Certificate -/

/-- **Exact Half-Line Contrast Identity for `factorialSourcePlus` and `factorialSourceMinus`:**
For every $n : \mathbb{N}$,
$$\frac{\operatorname{fullPairing}(\operatorname{autocorr}(\operatorname{factorialSourcePlus}\,n))
  - \operatorname{fullPairing}(\operatorname{autocorr}(\operatorname{factorialSourceMinus}\,n))}{2}
  = \operatorname{fullPairing}(\operatorname{factorialSourceProducer}\,n).$$ -/
theorem fullPairing_autocorr_factorialSource_contrast_eq (n : ℕ) :
    (fullPairing (autocorr (factorialSourcePlus n)) -
        fullPairing (autocorr (factorialSourceMinus n))) / 2 =
      fullPairing (factorialSourceProducer n) := by
  have hsP : Summable (primeTerm (autocorr (factorialSourcePlus n))) :=
    (autocorr_fullPairing_admissible (factorialSourcePlus n)).2.1.of_abs
  have hsM : Summable (primeTerm (autocorr (factorialSourceMinus n))) :=
    (autocorr_fullPairing_admissible (factorialSourceMinus n)).2.1.of_abs
  have hiP : IntegrableOn
      (fun x => polarDensity x * autocorr (factorialSourcePlus n) x) (Ici 0) :=
    integrableOn_polar_autocorr (factorialSourcePlus n)
  have hiM : IntegrableOn
      (fun x => polarDensity x * autocorr (factorialSourceMinus n) x) (Ici 0) :=
    integrableOn_polar_autocorr (factorialSourceMinus n)
  have hpt : primeTerm (factorialSourceProducer n) =
      fun m => (primeTerm (autocorr (factorialSourcePlus n)) m -
        primeTerm (autocorr (factorialSourceMinus n)) m) / 2 := by
    funext m
    unfold primeTerm
    change (if 2 ≤ m then primeWeight m * factorialSourceContrast n (Real.log m) else 0) = _
    unfold factorialSourceContrast
    split_ifs <;> ring
  have hpol : (fun x => polarDensity x * factorialSourceProducer n x) =
      fun x => (polarDensity x * autocorr (factorialSourcePlus n) x -
        polarDensity x * autocorr (factorialSourceMinus n) x) / 2 := by
    funext x
    change polarDensity x * factorialSourceContrast n x = _
    unfold factorialSourceContrast
    ring
  unfold fullPairing
  rw [hpt, tsum_div_const, Summable.tsum_sub hsP hsM,
    hpol, integral_div, integral_sub hiP hiM]
  ring

/-- **Cutoff-Stabilized Finite-Window Contrast on `factorialSourcePlus` / `factorialSourceMinus`:**
For every $n : \mathbb{N}$ and every cutoff $N$ with
`sourceCutoff (factorialSourcePlus n) ≤ N` and `sourceCutoff (factorialSourceMinus n) ≤ N`,
$$\frac{\operatorname{pairing}\,N\,(\operatorname{autocorr}(\operatorname{factorialSourcePlus}\,n))
  - \operatorname{pairing}\,N\,(\operatorname{autocorr}(\operatorname{factorialSourceMinus}\,n))}{2}
  = \operatorname{fullPairing}(\operatorname{factorialSourceProducer}\,n).$$ -/
theorem pairing_autocorr_factorialSource_contrast_eq (n N : ℕ)
    (hP : sourceCutoff (factorialSourcePlus n) ≤ N)
    (hM : sourceCutoff (factorialSourceMinus n) ≤ N) :
    (pairing N (autocorr (factorialSourcePlus n)) -
        pairing N (autocorr (factorialSourceMinus n))) / 2 =
      fullPairing (factorialSourceProducer n) := by
  rw [← fullPairing_autocorr_eq (factorialSourcePlus n) N hP,
    ← fullPairing_autocorr_eq (factorialSourceMinus n) N hM]
  exact fullPairing_autocorr_factorialSource_contrast_eq n

/-- **Unconditional $O(\log(n+1)/(n+1))$ Decay of the Normalized Prime–Polar Contrast Ratio:**
For every $n : \mathbb{N}$, the ratio of the prime–polar contrast
`fullPairing (factorialSourceProducer n)` to the common origin energy
`autocorr (factorialSourcePlus n) 0 = autocorr (factorialSourceMinus n) 0` satisfies
$$\frac{|\operatorname{fullPairing}(\operatorname{factorialSourceProducer}\,n)|}{\operatorname{autocorr}(\operatorname{factorialSourcePlus}\,n)\,0}
  \;\le\; \frac{10\log(4(n+1)+1) + 3 + \frac{1}{4(n+1)}}{6(n+1)}.$$ -/
theorem abs_fullPairing_factorialSourceProducer_div_autocorr_zero_le (n : ℕ) :
    |fullPairing (factorialSourceProducer n)| / autocorr (factorialSourcePlus n) 0 ≤
      (10 * Real.log (4 * ((n + 1 : ℕ) : ℝ) + 1) + 3 +
          1 / (4 * ((n + 1 : ℕ) : ℝ))) /
        (6 * ((n + 1 : ℕ) : ℝ)) := by
  obtain ⟨_, _, hlo, _, _, _, hpair, _, _, _, _, _⟩ := factorialSourceProducer_certificate n
  have hn0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hsqrt_pos : 0 < Real.sqrt (n + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have hlog : 0 ≤ Real.log (4 * ((n + 1 : ℕ) : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have hinv : 0 ≤ 1 / (4 * ((n + 1 : ℕ) : ℝ)) := by positivity
  have hnum : 0 ≤ 10 * Real.log (4 * ((n + 1 : ℕ) : ℝ) + 1) + 3 +
      1 / (4 * ((n + 1 : ℕ) : ℝ)) := by linarith
  have h1 :
      |fullPairing (factorialSourceProducer n)| / autocorr (factorialSourcePlus n) 0 ≤
        ((10 * Real.log (4 * ((n + 1 : ℕ) : ℝ) + 1) + 3 +
            1 / (4 * ((n + 1 : ℕ) : ℝ))) / Real.sqrt (n + 1 : ℕ)) /
          (6 * Real.sqrt (n + 1 : ℕ)) :=
    div_le_div₀ (div_nonneg hnum hsqrt_pos.le) hpair (by positivity) hlo
  refine h1.trans (le_of_eq ?_)
  rw [div_div, mul_comm (Real.sqrt (n + 1 : ℕ)), mul_assoc,
    ← sq (Real.sqrt (n + 1 : ℕ)), Real.sq_sqrt (by positivity)]

/-- **Master Theorem (Pillar XXXVIII — Genuine Source Weil Contrast & Divisor-Sampled Causal Response Producer):**
Unconditional synthesis of:
1. The $K\log K$-free linear channel for the divisor-sampled causal response;
2. The exact $(1, -4, 4)$ bi-null cancellation of the divisor-sampled causal response down to
   $10\log(4K + 1) + 3$;
3. The cutoff-free half-line full Weil functional identity on `RealWeilTestFn`;
4. The $O(\log(n+1)/(n+1))$ normalized prime–polar contrast ratio bound on
   `factorialSourcePlus n` / `factorialSourceMinus n`. -/
theorem factorialSource_contrast_and_divisorResponse_master
    {N K : ℕ} (hK1 : 1 ≤ K) (hKN : 4 * K ≤ N + 2) (n : ℕ) (f : RealWeilTestFn) :
    (-2 * (K : ℝ) ≤ divisorSampledCausalResponse N K ∧
        divisorSampledCausalResponse N K ≤ -(K : ℝ) + 2 * Real.log ((K : ℝ) + 1) + 2) ∧
      |divisorSampledCausalResponse N (4 * K) -
          4 * divisorSampledCausalResponse N (2 * K) +
          4 * divisorSampledCausalResponse N K| ≤
        10 * Real.log (4 * (K : ℝ) + 1) + 3 ∧
      (weilFullFunctional
          (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
          (EF.weilTest f.1.1 f.1.1)).re =
        EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re +
          biScaleLevyEnergy f.source -
          2 * fullPairing (autocorr f.source) ∧
      |fullPairing (factorialSourceProducer n)| / autocorr (factorialSourcePlus n) 0 ≤
        (10 * Real.log (4 * ((n + 1 : ℕ) : ℝ) + 1) + 3 +
            1 / (4 * ((n + 1 : ℕ) : ℝ))) /
          (6 * ((n + 1 : ℕ) : ℝ)) :=
  ⟨divisorSampledCausalResponse_bounds hK1 (by omega),
    abs_divisorSampledCausalResponse_biNull_le hK1 hKN,
    f.re_weilFullFunctional_vonMangoldt_eq_gamma_add_levy_sub_two_fullPairing,
    abs_fullPairing_factorialSourceProducer_div_autocorr_zero_le n⟩

end

end GaloisForLFunctions.BiScaleUncertainty

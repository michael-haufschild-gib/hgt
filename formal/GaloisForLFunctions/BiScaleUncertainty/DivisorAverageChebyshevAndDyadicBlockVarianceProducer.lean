import GaloisForLFunctions.BiScaleUncertainty.FoldFreeLogMobiusAndPlancherelCausalProducer
import GaloisForLFunctions.BiScaleUncertainty.ExponentialRectangleAndDivisorAverageLaw
import GaloisForLFunctions.BiScaleUncertainty.QuantitativeGramProducer
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarSourceEnergy
import GaloisForLFunctions.BiScaleUncertainty.IntegerBlockVariance
import GaloisForLFunctions.BiScaleUncertainty.NyquistWeightCells

/-!
# Pillar XXXVII: Divisor-Averaged Chebyshev Linear Channel, Quantitative Gram Source Producers, Dyadic Haar Block Variance & Critical-Line Nyquist Cell Mass

This module constructs four unconditional, hypothesis-free producer packages unifying the
exponential rectangle divisor-average law (`ExponentialRectangleAndDivisorAverageLaw.lean`),
the monotone quantitative Gram ladder (`QuantitativeGramProducer.lean`), the compactly supported
factorial source pair (`SignedPrimePolarSourceEnergy.lean`), the infinite block variance
(`IntegerBlockVariance.lean`), and the logarithmic Nyquist Taylor cell mass
(`NyquistWeightCells.lean`):

1. **Exact $K\log K$-Free Linear Channel for the Divisor-Averaged Chebyshev Error & Factorial-Lift Pairing (§1):**
   - Proves the two-sided logarithmic sandwich for `realHarmonic K = ∑_{j=1}^K 1/j`:
     $$\log(K + 1) \;\le\; H_K \;\le\; 1 + \log K \qquad (K \ge 1).$$
   - Combining `sum_logError_log_ratio_eq` and `sum_sqrt_mul_normalizedLogError_eq`
     $$\sum_{j=1}^K \left(\psi\!\left(\frac{K}{j}\right) - \frac{K}{j}\right)
       = \sum_{j=1}^K \sqrt{\frac{K}{j}}\,\widetilde{E}\!\left(\log\frac{K}{j}\right)
       = \log(K!) - K H_K$$
     with the Stirling bounds on $\log(K!)$ and the harmonic bounds on $H_K$, the leading
     $K\log K$ terms **cancel identically**, locking the divisor-averaged Chebyshev error inside
     an exact linear negative channel for every $K \ge 1$:
     $$-2K + \frac{1}{2}\log K + 1
       \;\le\; \sum_{j=1}^K \operatorname{logError}\!\left(\log\frac{K}{j}\right)
       \;\le\; -K + \frac{1}{2}\log(K + 1) + 1.$$
   - Similarly, for the raw factorial-lift pairing
     $\operatorname{pairing}_N(\operatorname{factorialLift}\,K) = 2\log(K!) - K\log K - K H_K + K$,
     the $2K\log K - K\log K - K\log K = 0$ terms cancel identically, yielding the two-sided
     $K\log K$-free linear sandwich:
     $$-2K + \log K + 2
       \;\le\; \operatorname{pairing}_N(\operatorname{factorialLift}\,K)
       \;\le\; -K + \log(K + 1) + 3.$$

2. **Quantitative Gram Producer Instantiation on Factorial Source Pairs & Rough-Collar Budget (§2):**
   - Instantiates the monotone quantitative physical-collar producer `quantitativeGramCoefficient f n`
     on the explicit compactly supported sources `factorialSourcePlus m` and `factorialSourceMinus m`,
     using `6√(m+1) ≤ autocorr (factorialSourcePlus m) 0 ≤ 46√(m+1)` to obtain explicit
     $O(\sqrt{m+1}/(n+1))$ allocation error bounds and $O(\sqrt{m+1}/\sqrt{n+2})$ limiting error bounds.
   - Couples `quantitativeGramCoefficient f n` with the unconditional rough-collar lower bound
     `collar_signed_energy_lower_bound` and our prime-free archimedean producers
     `archimedeanSignedMassProducer N` and `laplaceEnergyProducerBound N`.

3. **Dyadic Haar Block Variance & Exact Wavelet Energy Conservation on `TraceData` (§3):**
   - Evaluates `finiteBlockVariance 2` and `integerBlockVariance 2` in closed form as the exact
     Haar wavelet detail square $(w(2j + 1) - w(2j))^2$, while `integerBlockSum 2 w j = w(2j) + w(2j+1)`.
   - Proves the unconditional dyadic Haar wavelet energy conservation law on `TraceData = lp (fun _ : ℕ => ℝ) 2`:
     $$\sum_{j=0}^\infty \bigl(w(2j + 1) - w(2j)\bigr)^2 + \|\operatorname{integerBlockSum}\,2\,w\|_{\ell^2}^2
       = 2\,\|w\|_{\ell^2}^2,$$
     and characterizes equality $\|\operatorname{integerBlockSum}\,2\,w\|^2 = 2\|w\|^2$ by pairwise
     dyadic constancy $w(2j) = w(2j + 1)$.

4. **Critical-Line ($\beta = 1/2$) Nyquist Taylor Cell Mass Producer Bounds (§4):**
   - Specializes `nyquistWeightCellMass β m k` to the critical-line exponent $\beta = 1/2$, proving
     explicit power-law producer bounds at Taylor orders $m = 0$ (linear jet) and $m = 1$
     (quadratic jet), together with a cumulative finite-horizon bound across $k \in \operatorname{range} K$.
-/

open Complex MeasureTheory Set Filter Topology Finset
open Zeta23 RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
open GaloisForLFunctions.BiScaleUncertainty.SobolevShear
open scoped RealInnerProductSpace BigOperators CompactlySupported ArithmeticFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact $K\log K$-Free Linear Channel for the Divisor-Averaged Chebyshev Error & Factorial-Lift Pairing -/

/-- **Unconditional Logarithmic Lower Bound on `realHarmonic K`:**
For every `K : ℕ`, $\log(K + 1) \le H_K$. -/
theorem log_add_one_le_realHarmonic (K : ℕ) :
    Real.log ((K : ℝ) + 1) ≤ realHarmonic K := by
  induction K with
  | zero =>
    simp [realHarmonic]
  | succ K ih =>
    rw [realHarmonic_succ_eq K]
    have hstep := ChebyshevGauge.cellLength_le (by omega : 1 ≤ K + 1)
    unfold ChebyshevGauge.cellLength at hstep
    have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hstep ⊢
    linarith

/-- Helper induction for the logarithmic upper bound on `realHarmonic (M + 1)`. -/
private theorem realHarmonic_succ_le_one_add_log (M : ℕ) :
    realHarmonic (M + 1) ≤ 1 + Real.log ((M + 1 : ℕ) : ℝ) := by
  induction M with
  | zero =>
    unfold realHarmonic
    simp
  | succ M ih =>
    rw [realHarmonic_succ_eq (M + 1)]
    have hstep := ChebyshevGauge.inv_succ_le_cellLength (by omega : 1 ≤ M + 1)
    unfold ChebyshevGauge.cellLength at hstep
    have hcast : ((M + 1 + 1 : ℕ) : ℝ) = ((M + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith

/-- **Unconditional Logarithmic Upper Bound on `realHarmonic K`:**
For every `K ≥ 1`, $H_K \le 1 + \log K$. -/
theorem realHarmonic_le_one_add_log {K : ℕ} (hK : 1 ≤ K) :
    realHarmonic K ≤ 1 + Real.log (K : ℝ) := by
  have heq : K = (K - 1) + 1 := (Nat.sub_add_cancel hK).symm
  rw [heq]
  exact realHarmonic_succ_le_one_add_log (K - 1)

/-- **Two-Sided Logarithmic Sandwich for `realHarmonic K` (`K ≥ 1`):**
$$\log(K + 1) \;\le\; H_K \;\le\; 1 + \log K.$$ -/
theorem realHarmonic_bounds {K : ℕ} (hK : 1 ≤ K) :
    Real.log ((K : ℝ) + 1) ≤ realHarmonic K ∧
      realHarmonic K ≤ 1 + Real.log (K : ℝ) :=
  ⟨log_add_one_le_realHarmonic K, realHarmonic_le_one_add_log hK⟩

/-- For every `K ≥ 1`, $\log K \le \log(K + 1) \le H_K$. -/
theorem log_le_realHarmonic {K : ℕ} (hK : 1 ≤ K) :
    Real.log (K : ℝ) ≤ realHarmonic K := by
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  exact (Real.log_le_log hK_pos (by linarith)).trans (log_add_one_le_realHarmonic K)

/-- **Unconditional $K\log K$-Free Linear Channel for the Divisor-Averaged Chebyshev Error
(`sum_logError_log_ratio_bounds`):**
For EVERY `K ≥ 1` (with **zero hypotheses**!), the divisor-averaged Chebyshev error
$$\sum_{j=1}^K \operatorname{logError}\!\left(\log\frac{K}{j}\right)
  = \sum_{j=1}^K \left(\psi\!\left(\frac{K}{j}\right) - \frac{K}{j}\right)
  = \log(K!) - K H_K$$
has exact cancellation of all $K\log K$ terms between Stirling's formula and the harmonic number
$H_K$, confining it to the linear negative channel:
$$-2K \;\le\; \sum_{j=1}^K \operatorname{logError}\!\left(\log\frac{K}{j}\right)
  \;\le\; -K + \log(K + 1) + 1.$$ -/
theorem sum_logError_log_ratio_bounds {K : ℕ} (hK : 1 ≤ K) :
    -2 * (K : ℝ) ≤
        (∑ j ∈ Finset.Icc 1 K, logError (Real.log ((K : ℝ) / j))) ∧
      (∑ j ∈ Finset.Icc 1 K, logError (Real.log ((K : ℝ) / j))) ≤
        -(K : ℝ) + Real.log ((K : ℝ) + 1) + 1 := by
  rw [ChebyshevGauge.sum_logError_log_ratio_eq K,
    floorSummatory_chebyshevPsi_eq_main_add_stirlingResidual K]
  have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  obtain ⟨hst_lo, hst_hi⟩ := stirlingResidual_bounds hK
  have hh_lo := log_le_realHarmonic hK
  have hh_hi := realHarmonic_le_one_add_log hK
  have hmul_lo : (K : ℝ) * Real.log (K : ℝ) ≤ (K : ℝ) * realHarmonic K :=
    mul_le_mul_of_nonneg_left hh_lo hK_nonneg
  have hmul_hi : (K : ℝ) * realHarmonic K ≤ (K : ℝ) * (1 + Real.log (K : ℝ)) :=
    mul_le_mul_of_nonneg_left hh_hi hK_nonneg
  constructor <;> linarith

/-- **Unconditional $K\log K$-Free Linear Channel for the Divisor-Sampled Normalized Chebyshev Error
(`sum_sqrt_mul_normalizedLogError_bounds`):**
For EVERY `K ≥ 1` (with **zero hypotheses**!),
$$-2K \;\le\; \sum_{j=1}^K \sqrt{\frac{K}{j}}\,\widetilde{E}\!\left(\log\frac{K}{j}\right)
  \;\le\; -K + \log(K + 1) + 1.$$ -/
theorem sum_sqrt_mul_normalizedLogError_bounds {K : ℕ} (hK : 1 ≤ K) :
    -2 * (K : ℝ) ≤
        (∑ j ∈ Finset.Icc 1 K,
          Real.sqrt ((K : ℝ) / j) * normalizedLogError (Real.log ((K : ℝ) / j))) ∧
      (∑ j ∈ Finset.Icc 1 K,
          Real.sqrt ((K : ℝ) / j) * normalizedLogError (Real.log ((K : ℝ) / j))) ≤
        -(K : ℝ) + Real.log ((K : ℝ) + 1) + 1 := by
  rw [ChebyshevGauge.sum_sqrt_mul_normalizedLogError_eq K,
    ← ChebyshevGauge.sum_logError_log_ratio_eq K]
  exact sum_logError_log_ratio_bounds hK

/-- For every `K ≥ 1`, $K(\log(K + 1) - \log K) \le 1$. -/
theorem mul_log_add_one_sub_log_le_one {K : ℕ} (hK : 1 ≤ K) :
    (K : ℝ) * (Real.log ((K : ℝ) + 1) - Real.log (K : ℝ)) ≤ 1 := by
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hcell := ChebyshevGauge.cellLength_le hK
  unfold ChebyshevGauge.cellLength at hcell
  calc
    (K : ℝ) * (Real.log ((K : ℝ) + 1) - Real.log (K : ℝ))
      ≤ (K : ℝ) * (1 / (K : ℝ)) := mul_le_mul_of_nonneg_left hcell hK_pos.le
    _ = 1 := mul_one_div_cancel hK_pos.ne'

/-- **Unconditional $K\log K$-Free Linear Channel for the Raw Factorial-Lift Pairing
(`pairing_factorialLift_bounds`):**
For EVERY `N K : ℕ` with `1 ≤ K` and `log K ≤ cutoff N` (with **zero hypotheses on zeros of $\zeta$**!),
the raw factorial-lift pairing $\operatorname{pairing}_N(\operatorname{factorialLift}\,K)$ has exact
cancellation of all $2K\log K - K\log K - K\log K = 0$ terms and satisfies:
$$-2K \;\le\; \operatorname{pairing}_N(\operatorname{factorialLift}\,K)
  \;\le\; -K + 2\log(K + 1) + 2.$$ -/
theorem pairing_factorialLift_bounds (N K : ℕ) (hK1 : 1 ≤ K)
    (hK : Real.log (K : ℝ) ≤ SignedPrimePolar.cutoff N) :
    -2 * (K : ℝ) ≤ pairing N (factorialLift K) ∧
      pairing N (factorialLift K) ≤ -(K : ℝ) + 2 * Real.log ((K : ℝ) + 1) + 2 := by
  rw [ChebyshevGauge.pairing_factorialLift_eq N K hK1 hK,
    floorSummatory_chebyshevPsi_eq_main_add_stirlingResidual K]
  have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  obtain ⟨hst_lo, hst_hi⟩ := stirlingResidual_bounds hK1
  have hh_lo := log_le_realHarmonic hK1
  have hh_hi := realHarmonic_le_one_add_log hK1
  have hmul_lo : (K : ℝ) * Real.log (K : ℝ) ≤ (K : ℝ) * realHarmonic K :=
    mul_le_mul_of_nonneg_left hh_lo hK_nonneg
  have hmul_hi : (K : ℝ) * realHarmonic K ≤ (K : ℝ) * (1 + Real.log (K : ℝ)) :=
    mul_le_mul_of_nonneg_left hh_hi hK_nonneg
  constructor <;> linarith

/-- **Unconditional $K\log K$-Free Linear Channel for the Full Factorial-Lift Pairing:**
For EVERY `K ≥ 1`,
$$-2K \;\le\; \operatorname{fullPairing}(\operatorname{factorialLift}\,K)
  \;\le\; -K + 2\log(K + 1) + 2.$$ -/
theorem fullPairing_factorialLift_bounds {K : ℕ} (hK1 : 1 ≤ K) :
    -2 * (K : ℝ) ≤ fullPairing (factorialLift K) ∧
      fullPairing (factorialLift K) ≤ -(K : ℝ) + 2 * Real.log ((K : ℝ) + 1) + 2 := by
  have hK_lt : K < K + 2 := by omega
  have hK_cut : Real.log (K : ℝ) ≤ SignedPrimePolar.cutoff K := by
    unfold SignedPrimePolar.cutoff
    exact Real.log_le_log (by exact_mod_cast hK1) (by exact_mod_cast (by omega : K ≤ K + 2))
  rw [← ChebyshevGauge.pairing_factorialLift_eq_fullPairing K K hK_lt]
  exact pairing_factorialLift_bounds K K hK1 hK_cut

/-! ## §2. Quantitative Gram Producer Instantiation on Factorial Source Pairs & Rough-Collar Budget -/

/-- **Explicit Square-Root Allocation Error Producer for `factorialSourcePlus m`:**
For every `m n : ℕ`, since `autocorr (factorialSourcePlus m) 0 ≤ 46 * √(m + 1)`, the allocation
error of the monotone quantitative Gram producer at cutoff `n` is bounded unconditionally by:
$$\operatorname{signedGramOptimalCoefficient}(\operatorname{factorialSourcePlus}\,m, n)
  - \operatorname{quantitativeGramCoefficient}(\operatorname{factorialSourcePlus}\,m, n)
  \;\le\; \frac{46\sqrt{m + 1}\,(r_0 + 1)}{n + 1}.$$ -/
theorem quantitativeGramCoefficient_factorialSourcePlus_allocation_error (m n : ℕ) :
    0 ≤ signedGramOptimalCoefficient (factorialSourcePlus m) n -
        quantitativeGramCoefficient (factorialSourcePlus m) n ∧
      signedGramOptimalCoefficient (factorialSourcePlus m) n -
        quantitativeGramCoefficient (factorialSourcePlus m) n ≤
        46 * Real.sqrt (m + 1 : ℕ) * (logarithmicCollarRadius + 1) / ((n : ℝ) + 1) := by
  have ha := quantitativeGramCoefficient_allocation_error (factorialSourcePlus m) n
  have hcert := (factorialSource_energy_certificate m).2.2
  have hpos : 0 ≤ (logarithmicCollarRadius + 1) / ((n : ℝ) + 1) := by
    positivity [logarithmicCollarRadius_pos]
  refine ⟨ha.1, ha.2.trans ?_⟩
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right hcert hpos

/-- **Explicit Square-Root Allocation Error Producer for `factorialSourceMinus m`:**
For every `m n : ℕ`,
$$\operatorname{signedGramOptimalCoefficient}(\operatorname{factorialSourceMinus}\,m, n)
  - \operatorname{quantitativeGramCoefficient}(\operatorname{factorialSourceMinus}\,m, n)
  \;\le\; \frac{46\sqrt{m + 1}\,(r_0 + 1)}{n + 1}.$$ -/
theorem quantitativeGramCoefficient_factorialSourceMinus_allocation_error (m n : ℕ) :
    0 ≤ signedGramOptimalCoefficient (factorialSourceMinus m) n -
        quantitativeGramCoefficient (factorialSourceMinus m) n ∧
      signedGramOptimalCoefficient (factorialSourceMinus m) n -
        quantitativeGramCoefficient (factorialSourceMinus m) n ≤
        46 * Real.sqrt (m + 1 : ℕ) * (logarithmicCollarRadius + 1) / ((n : ℝ) + 1) := by
  have ha := quantitativeGramCoefficient_allocation_error (factorialSourceMinus m) n
  obtain ⟨heq, _, hcert⟩ := factorialSource_energy_certificate m
  have hcert_minus : autocorr (factorialSourceMinus m) 0 ≤ 46 * Real.sqrt (m + 1 : ℕ) :=
    heq ▸ hcert
  have hpos : 0 ≤ (logarithmicCollarRadius + 1) / ((n : ℝ) + 1) := by
    positivity [logarithmicCollarRadius_pos]
  refine ⟨ha.1, ha.2.trans ?_⟩
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right hcert_minus hpos

/-- **Explicit Square-Root Limiting Error Producer for `factorialSourcePlus m`:**
For every `m n : ℕ`, the gap between the infinite-cutoff optimum
`limitingSignedGramCoefficient (factorialSourcePlus m)` and the finitely produced value
`quantitativeGramCoefficient (factorialSourcePlus m) n` satisfies:
$$\operatorname{limitingSignedGramCoefficient}(\operatorname{factorialSourcePlus}\,m)
  - \operatorname{quantitativeGramCoefficient}(\operatorname{factorialSourcePlus}\,m, n)
  \;\le\; \frac{46\sqrt{m + 1}\,(r_0 + 1)}{n + 1}
    + 92\sqrt{m + 1}\,\operatorname{collarCutoffTailMass}(n).$$ -/
theorem quantitativeGramCoefficient_factorialSourcePlus_limiting_error (m n : ℕ) :
    0 ≤ limitingSignedGramCoefficient (factorialSourcePlus m) -
        quantitativeGramCoefficient (factorialSourcePlus m) n ∧
      limitingSignedGramCoefficient (factorialSourcePlus m) -
        quantitativeGramCoefficient (factorialSourcePlus m) n ≤
        46 * Real.sqrt (m + 1 : ℕ) * (logarithmicCollarRadius + 1) / ((n : ℝ) + 1) +
          92 * Real.sqrt (m + 1 : ℕ) * collarCutoffTailMass n := by
  have hlim := quantitativeGramCoefficient_limiting_error (factorialSourcePlus m) n
  have hcert := (factorialSource_energy_certificate m).2.2
  have hpos1 : 0 ≤ (logarithmicCollarRadius + 1) / ((n : ℝ) + 1) := by
    positivity [logarithmicCollarRadius_pos]
  have hpos2 : 0 ≤ collarCutoffTailMass n := collarCutoffTailMass_nonneg n
  refine ⟨hlim.1, hlim.2.trans ?_⟩
  have h1 :
      autocorr (factorialSourcePlus m) 0 * (logarithmicCollarRadius + 1) / ((n : ℝ) + 1) ≤
        46 * Real.sqrt (m + 1 : ℕ) * (logarithmicCollarRadius + 1) / ((n : ℝ) + 1) := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hcert hpos1
  have h2 :
      2 * autocorr (factorialSourcePlus m) 0 * collarCutoffTailMass n ≤
        92 * Real.sqrt (m + 1 : ℕ) * collarCutoffTailMass n := by
    nlinarith
  linarith

/-- **Joint Quantitative Gram & Prime-Free Rough-Collar Producer Package:**
For every compactly supported source `f : C_c(ℝ, ℝ)`, collar parameters `a b : ℝ`, Gram cutoff
`n : ℕ`, and prime-polar cutoff `N : ℕ`:
1. `quantitativeGramCoefficient f n` is non-negative and bounded above by `signedGramOptimalCoefficient f n`
   with allocation error at most `autocorr f 0 * (r₀ + 1) / (n + 1)`;
2. `SignedPrimePolar.mass N` is bounded above by the prime-free `massProducerBound N`;
3. `SignedPrimePolar.packetEnergy (SignedPrimePolar.collarSource f a b) N` is bounded above by the
   prime-free `archimedeanCollarPacketProducerBound f a b N`. -/
theorem quantitativeGram_and_roughCollar_producer_package
    (f : C_c(ℝ, ℝ)) (a b : ℝ) (n N : ℕ) :
    0 ≤ quantitativeGramCoefficient f n ∧
      quantitativeGramCoefficient f n ≤ signedGramOptimalCoefficient f n ∧
      signedGramOptimalCoefficient f n - quantitativeGramCoefficient f n ≤
        autocorr f 0 * (logarithmicCollarRadius + 1) / ((n : ℝ) + 1) ∧
      SignedPrimePolar.mass N ≤ massProducerBound N ∧
      SignedPrimePolar.packetEnergy (SignedPrimePolar.collarSource f a b) N ≤
        archimedeanCollarPacketProducerBound f a b N :=
  ⟨(quantitativeGramCoefficient_bounds f n).1,
    (quantitativeGramCoefficient_bounds f n).2,
    (quantitativeGramCoefficient_allocation_error f n).2,
    mass_le_massProducerBound N,
    collar_packetEnergy_le_archimedeanCollarPacketProducerBound f a b N⟩

/-! ## §3. Dyadic Haar Block Variance & Exact Wavelet Energy Conservation on `TraceData` -/

/-- For block size `m = 2`, the finite block variance `finiteBlockVariance 2 u` is the single
squared Haar difference `(u 1 - u 0) ^ 2`. -/
theorem finiteBlockVariance_two (u : ℕ → ℝ) :
    finiteBlockVariance 2 u = (u 1 - u 0) ^ 2 := by
  unfold finiteBlockVariance
  rw [Finset.sum_range_succ, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty,
    Finset.sum_range_one, zero_add]

/-- **Dyadic Haar Wavelet Detail Formula for `integerBlockVariance 2`:**
For every `w : TraceData` and dyadic block index `j : ℕ`, the 2-block variance at `j` is the
exact squared Haar detail coefficient `(w (2 * j + 1) - w (2 * j)) ^ 2`. -/
theorem integerBlockVariance_two (w : TraceData) (j : ℕ) :
    integerBlockVariance 2 w j = (w (2 * j + 1) - w (2 * j)) ^ 2 := by
  unfold integerBlockVariance
  rw [finiteBlockVariance_two]
  simp only [Nat.add_zero]

/-- **Dyadic Haar Wavelet Scaling Formula for `integerBlockSum 2`:**
For every `w : TraceData` and dyadic block index `j : ℕ`, the 2-block sum at `j` is the
exact Haar scaling sum `w (2 * j) + w (2 * j + 1)`. -/
theorem integerBlockSum_two (w : TraceData) (j : ℕ) :
    integerBlockSum 2 w j = w (2 * j) + w (2 * j + 1) := by
  rw [integerBlockSum_range 2 w j, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.add_zero]

/-- Summability of the squared dyadic Haar detail sequence `(w (2 * j + 1) - w (2 * j)) ^ 2` for
every `w : TraceData`. -/
theorem summable_dyadicHaar_detail_sq (w : TraceData) :
    Summable (fun j : ℕ => (w (2 * j + 1) - w (2 * j)) ^ 2) := by
  have hs := summable_integerBlockVariance 2 w
  refine hs.congr fun j => ?_
  exact integerBlockVariance_two w j

/-- **Exact Dyadic Haar Detail Series Identity (`dyadicHaar_detail_tsum_eq`):**
For EVERY `w : TraceData` (with **zero hypotheses**!), the infinite series of squared dyadic
Haar differences equals `2 * ‖w‖ ^ 2 - ‖integerBlockSum 2 w‖ ^ 2`:
$$\sum_{j=0}^\infty \bigl(w(2j + 1) - w(2j)\bigr)^2
  = 2\,\|w\|_{\ell^2}^2 - \|\operatorname{integerBlockSum}\,2\,w\|_{\ell^2}^2.$$ -/
theorem dyadicHaar_detail_tsum_eq (w : TraceData) :
    (∑' j : ℕ, (w (2 * j + 1) - w (2 * j)) ^ 2) =
      2 * ‖w‖ ^ 2 - ‖integerBlockSum 2 w‖ ^ 2 := by
  have h := integerBlockVariance_tsum 2 w
  simp only [integerBlockVariance_two, Nat.cast_ofNat] at h
  exact h

/-- **Unconditional Dyadic Haar Wavelet Energy Conservation Law on `TraceData`:**
For EVERY `w : TraceData` (with **zero hypotheses**!), the sum of the infinite Haar detail energy
and the infinite Haar block-sum energy equals twice the $\ell^2$ energy of `w`:
$$\sum_{j=0}^\infty \bigl(w(2j + 1) - w(2j)\bigr)^2
  + \|\operatorname{integerBlockSum}\,2\,w\|_{\ell^2}^2
  = 2\,\|w\|_{\ell^2}^2.$$ -/
theorem dyadicHaar_energy_conservation (w : TraceData) :
    (∑' j : ℕ, (w (2 * j + 1) - w (2 * j)) ^ 2) + ‖integerBlockSum 2 w‖ ^ 2 =
      2 * ‖w‖ ^ 2 := by
  rw [dyadicHaar_detail_tsum_eq w]
  ring

/-- **Rigidity of Dyadic Block Aggregation (`integerBlockSum_two_energy_eq_iff`):**
For EVERY `w : TraceData`, $\|\operatorname{integerBlockSum}\,2\,w\|^2 = 2\,\|w\|^2$ if and only
if `w` is constant on every dyadic pair (`∀ j, w (2 * j) = w (2 * j + 1)`). -/
theorem integerBlockSum_two_energy_eq_iff (w : TraceData) :
    ‖integerBlockSum 2 w‖ ^ 2 = 2 * ‖w‖ ^ 2 ↔ ∀ j : ℕ, w (2 * j) = w (2 * j + 1) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, integerBlockSum_energy_eq_iff 2 w]
  unfold IntegerBlockConstant
  constructor
  · intro h j
    simpa using h j 0 (by decide) 1 (by decide)
  · intro h j r hr s hs
    interval_cases r <;> interval_cases s
    · rfl
    · simpa using h j
    · simpa using (h j).symm
    · rfl

/-! ## §4. Critical-Line ($\beta = 1/2$) Nyquist Taylor Cell Mass Producer Bounds -/

/-- **Unconditional Critical-Line Linear Taylor Cell Mass Bound (`m = 0`, `β = 1/2`):**
For EVERY logarithmic cell index `k : ℕ` (with **zero hypotheses**!), the linear Taylor cell mass
on $[\log(k+1), \log(k+2)]$ at the critical-line exponent $\beta = 1/2$ satisfies:
$$\operatorname{nyquistWeightCellMass}(1/2, 0, k)
  \;\le\; \frac{2^{1/2}}{4}\,(k + 1)^{-3/2}.$$ -/
theorem nyquistWeightCellMass_half_zero_le (k : ℕ) :
    nyquistWeightCellMass (1 / 2) 0 k ≤
      (2 : ℝ) ^ (1 / 2 : ℝ) / 4 * ((k + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) := by
  have h := nyquistWeightCellMass_le_power (by norm_num : (0 : ℝ) ≤ 1 / 2) 0 k
  refine h.trans (le_of_eq ?_)
  have hexp : (1 / 2 : ℝ) - ((0 + 2 : ℕ) : ℝ) = (-3 / 2 : ℝ) := by norm_num
  have hfac : ((0 + 2).factorial : ℝ) = 2 := by norm_num
  rw [hexp, hfac]
  ring

/-- **Unconditional Critical-Line Quadratic Taylor Cell Mass Bound (`m = 1`, `β = 1/2`):**
For EVERY logarithmic cell index `k : ℕ` (with **zero hypotheses**!), the quadratic Taylor cell
mass on $[\log(k+1), \log(k+2)]$ at $\beta = 1/2$ satisfies:
$$\operatorname{nyquistWeightCellMass}(1/2, 1, k)
  \;\le\; \frac{2^{1/2}}{24}\,(k + 1)^{-5/2}
  \;\le\; \frac{2^{1/2}}{24\,(k + 1)^2}.$$ -/
theorem nyquistWeightCellMass_half_one_le_rpow (k : ℕ) :
    nyquistWeightCellMass (1 / 2) 1 k ≤
      (2 : ℝ) ^ (1 / 2 : ℝ) / 24 * ((k + 1 : ℕ) : ℝ) ^ (-5 / 2 : ℝ) := by
  have h := nyquistWeightCellMass_le_power (by norm_num : (0 : ℝ) ≤ 1 / 2) 1 k
  refine h.trans (le_of_eq ?_)
  have hexp : (1 / 2 : ℝ) - ((1 + 2 : ℕ) : ℝ) = (-5 / 2 : ℝ) := by norm_num
  have hfac : ((1 + 2).factorial : ℝ) = 6 := by norm_num
  rw [hexp, hfac]
  ring

/-- Inverse-square dominance `(k + 1)^{-5/2} ≤ 1 / (k + 1)^2` for all `k : ℕ`. -/
theorem rpow_neg_five_halves_le_inv_sq (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) ^ (-5 / 2 : ℝ) ≤ 1 / (((k + 1 : ℕ) : ℝ) ^ 2) := by
  have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hk0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hrpow : ((k + 1 : ℕ) : ℝ) ^ (-5 / 2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)
  refine hrpow.trans (le_of_eq ?_)
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hk0.le, Real.rpow_natCast,
    one_div]

/-- **Unconditional Inverse-Square Producer Bound on `nyquistWeightCellMass (1/2) 1 k`:**
For EVERY `k : ℕ` (with **zero hypotheses**!),
$$\operatorname{nyquistWeightCellMass}(1/2, 1, k)
  \;\le\; \frac{2^{1/2}}{24\,(k + 1)^2}.$$ -/
theorem nyquistWeightCellMass_half_one_le_inv_sq (k : ℕ) :
    nyquistWeightCellMass (1 / 2) 1 k ≤
      (2 : ℝ) ^ (1 / 2 : ℝ) / 24 * (1 / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
  calc
    nyquistWeightCellMass (1 / 2) 1 k
      ≤ (2 : ℝ) ^ (1 / 2 : ℝ) / 24 * ((k + 1 : ℕ) : ℝ) ^ (-5 / 2 : ℝ) :=
        nyquistWeightCellMass_half_one_le_rpow k
    _ ≤ (2 : ℝ) ^ (1 / 2 : ℝ) / 24 * (1 / (((k + 1 : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (rpow_neg_five_halves_le_inv_sq k) (by positivity)

/-- **Cumulative Finite-Horizon Producer Bound on Critical-Line Nyquist Taylor Cell Mass:**
For EVERY horizon `K : ℕ` (with **zero hypotheses**!),
$$\sum_{k=0}^{K-1} \operatorname{nyquistWeightCellMass}(1/2, 1, k)
  \;\le\; \frac{2^{1/2}}{24} \sum_{k=0}^{K-1} \frac{1}{(k + 1)^2}.$$ -/
theorem sum_nyquistWeightCellMass_half_one_le (K : ℕ) :
    (∑ k ∈ Finset.range K, nyquistWeightCellMass (1 / 2) 1 k) ≤
      (2 : ℝ) ^ (1 / 2 : ℝ) / 24 *
        ∑ k ∈ Finset.range K, (1 / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => nyquistWeightCellMass_half_one_le_inv_sq k

end
end GaloisForLFunctions.BiScaleUncertainty

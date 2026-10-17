import GaloisForLFunctions.BiScaleUncertainty.CoprimeResidueAntiCorrelationAndSawtoothPhase
import GaloisForLFunctions.BiScaleUncertainty.ChebyshevHeadAndShearCellProducer
import GaloisForLFunctions.BiScaleUncertainty.BandLimitedLaplaceEnergy

/-!
# Pillar XXXIV: Common-Cutoff Sawtooth-Phase Cancellation & Band-Limited Critical-Line Spectral Producers

This module develops two major producer mechanisms connecting the Möbius-log sawtooth phase
$\Phi_{\mathrm{fract}}(N, n) = \sum_{d=1}^N (-\mu(d)\log d)\{n/d\}$ and the critical-line
band-limited spectral density $\int_{|\xi| \le \sqrt{N+2}} S_N(\xi)\,d\xi$:

1. **Common-Cutoff Harmonic-Drift Cancellation & Pure Sawtooth-Phase Representation of
   $\Lambda(n+1)$ and `dyadicChebyshevDiffSeq (2 * m)` (§1):**
   Whereas evaluating `chebyshevPsiSeq n` at a moving cutoff $N = n$ mixes cutoff increments with
   argument increments, fixing a common cutoff $N \ge n$ makes the Möbius-log harmonic drift
   $$H_{\mu\log}(N) := \sum_{d=1}^N \frac{-\mu(d)\log d}{d}$$
   a pure constant in $n$:
   $$\psi(n) = n \cdot H_{\mu\log}(n + k) - \Phi_{\mathrm{fract}}(n + k, n).$$
   Consequently:
   - Advancing $n \mapsto n + 1$ at common cutoff $N = n + k + 1$ differentiates the linear drift
     to $H_{\mu\log}(n + k + 1)$ and expresses $\Lambda(n + 1) - 1$ as the constant drift deficit
     minus the forward sawtooth phase difference:
     $$\Lambda(n + 1) - 1 = \bigl(H_{\mu\log}(n + k + 1) - 1\bigr)
       - \operatorname{addDiff}\bigl(\Phi_{\mathrm{fract}}(n + k + 1)\bigr)(n).$$
   - Forming the Wall 1 dyadic Chebyshev difference `dyadicChebyshevDiffSeq (2 * m) = 2 * ψ(m) - ψ(2m)`
     at common cutoff $N = 2m + k$ **cancels the harmonic drift $H_{\mu\log}(2m + k)$ identically**
     ($2m H_{\mu\log} - 2m H_{\mu\log} = 0$), expressing `dyadicChebyshevDiffSeq (2 * m)` purely as
     the dyadic difference of the Möbius-log sawtooth phase sum:
     $$\operatorname{dyadicChebyshevDiffSeq}(2m)
       = \Phi_{\mathrm{fract}}(2m + k, 2m) - 2\,\Phi_{\mathrm{fract}}(2m + k, m).$$

2. **Log-Factorial & Stirling Producer Bounds on the Sawtooth Phase and Its Dyadic Cancellation (§2):**
   - Individually, for every $N, n \in \mathbb{N}$, $|\Phi_{\mathrm{fract}}(N, n)|$ is bounded by
     the log-factorial $\sum_{d=1}^N \log d = \operatorname{floorSummatory}\,\operatorname{chebyshevPsi}\,N$.
   - Across the dyadic combination $\Phi_{\mathrm{fract}}(2m + k, 2m) - 2\,\Phi_{\mathrm{fract}}(2m + k, m)$,
     the $\log m$ factor cancels completely, yielding the linear bound $\le (\log 4 + 4)(2m)$, the
     two-sided Stirling producer sandwich via `chebyshevAlternatingProducer m`, and at dyadic scales
     $m = 2^K$ the pure-Stirling upper bound via `dyadicCumulativeChebyshevProducer K`.
   - Summing $\Phi_{\mathrm{fract}}(N, n)$ over $1 \le n \le N$ yields the exact identity linking
     the cumulative sawtooth phase sum to `floorSummatory chebyshevPsi N`:
     $$\sum_{n=1}^N \Phi_{\mathrm{fract}}(N, n)
       = \left(\sum_{n=1}^N n\right) H_{\mu\log}(N)
         - \operatorname{floorSummatory}\,\operatorname{chebyshevPsi}\,N.$$

3. **Band-Limited Critical-Line Spectral Density Producers & Full Weil Functional Bounds (§3):**
   Combining the critical-line band theorem (`laplaceEnergy_le_band_add_linear`) at the Nyquist
   band frequency $\xi_0 = \sqrt{N + 2}$ with our boundary-free Laplace packet and collar bounds
   controls `packetEnergy f N`, `packetEnergy (collarSource f a b) N`, and the full Weil functional
   $\operatorname{weilFullFunctional}\,\Lambda$ across all explicit-formula test spaces directly in
   terms of the critical-line band integral $\int_{-\sqrt{N+2}}^{\sqrt{N+2}} S_N(\xi)\,d\xi$ plus
   the explicit $O(\log N)$ high-frequency remainder `bandRemainderProducer N`.
-/

open Complex MeasureTheory Set Filter Topology Finset
open Zeta23 RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector RHTower.WeilOneSided RHTower.WeilPoleWeight
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open scoped RealInnerProductSpace BigOperators CompactlySupported ArithmeticFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ## §1. Common-Cutoff Harmonic-Drift Cancellation & Pure Sawtooth-Phase Producer for `dyadicChebyshevDiffSeq` -/

/-- The Möbius-log harmonic sum at cutoff `N`:
$$H_{\mu\log}(N) := \sum_{d=1}^N \frac{-\mu(d)\log d}{d}.$$ -/
def moebiusLogHarmonicSum (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, vonMangoldtDivisorWeight d / (d : ℝ)

/-- **Common-Cutoff Sawtooth Decomposition of `chebyshevPsiSeq`:**
For every `n k : ℕ` (so the common cutoff `n + k` satisfies `n ≤ n + k`),
$$\psi(n) = n \cdot H_{\mu\log}(n + k)
  - \operatorname{weightedFractSumSeq}\,\operatorname{vonMangoldtDivisorWeight}\,(n + k)\,n.$$ -/
theorem chebyshevPsiSeq_eq_common_cutoff_harmonic_sub_fractSum (n k : ℕ) :
    chebyshevPsiSeq n =
      (n : ℝ) * moebiusLogHarmonicSum (n + k) -
        weightedFractSumSeq vonMangoldtDivisorWeight (n + k) n := by
  have h := logMoebiusFloorSumSeq_eq_chebyshevPsiSeq n k
  rw [← h, ← weightedFloorSumSeq_vonMangoldt_eq_logMoebius]
  exact weightedFloorSumSeq_eq_harmonic_sub_fractSum vonMangoldtDivisorWeight (n + k) n

/-- **Common-Cutoff Sawtooth Decomposition of `chebyshevErrorSeq`:**
For every `n k : ℕ`,
$$\psi(n) - n = n\bigl(H_{\mu\log}(n + k) - 1\bigr)
  - \operatorname{weightedFractSumSeq}\,\operatorname{vonMangoldtDivisorWeight}\,(n + k)\,n.$$ -/
theorem chebyshevErrorSeq_eq_common_cutoff_harmonic_drift_sub_fractSum (n k : ℕ) :
    chebyshevErrorSeq n =
      (n : ℝ) * (moebiusLogHarmonicSum (n + k) - 1) -
        weightedFractSumSeq vonMangoldtDivisorWeight (n + k) n := by
  unfold chebyshevErrorSeq
  change chebyshevPsiSeq n - (n : ℝ) = _
  rw [chebyshevPsiSeq_eq_common_cutoff_harmonic_sub_fractSum n k]
  ring

/-- **Common-Cutoff Sawtooth Forward-Difference Representation of `Λ(n + 1)`:**
At any common cutoff `n + k + 1 ≥ n + 1`, the harmonic sum `moebiusLogHarmonicSum (n + k + 1)` is
invariant as the argument steps from `n` to `n + 1`, so:
$$\Lambda(n + 1) = H_{\mu\log}(n + k + 1)
  - \operatorname{addDiff}\bigl(\operatorname{weightedFractSumSeq}\,\operatorname{vonMangoldtDivisorWeight}\,(n + k + 1)\bigr)(n).$$ -/
theorem vonMangoldt_succ_eq_common_cutoff_harmonic_sub_addDiff_fractSum (n k : ℕ) :
    ArithmeticFunction.vonMangoldt (n + 1) =
      moebiusLogHarmonicSum (n + k + 1) -
        addDiff (weightedFractSumSeq vonMangoldtDivisorWeight (n + k + 1)) n := by
  have hstep := addDiff_chebyshevPsiSeq n
  unfold addDiff at hstep ⊢
  have h1 := chebyshevPsiSeq_eq_common_cutoff_harmonic_sub_fractSum (n + 1) k
  have h2 := chebyshevPsiSeq_eq_common_cutoff_harmonic_sub_fractSum n (k + 1)
  rw [show (n + 1) + k = n + k + 1 by omega] at h1
  rw [show n + (k + 1) = n + k + 1 by omega] at h2
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [h1, h2, hcast] at hstep
  linarith

/-- **Common-Cutoff Sawtooth Forward-Difference Representation of `Λ(n + 1) - 1`:**
For every `n k : ℕ`,
$$\Lambda(n + 1) - 1 = \bigl(H_{\mu\log}(n + k + 1) - 1\bigr)
  - \operatorname{addDiff}\bigl(\operatorname{weightedFractSumSeq}\,\operatorname{vonMangoldtDivisorWeight}\,(n + k + 1)\bigr)(n).$$ -/
theorem vonMangoldt_succ_sub_one_eq_common_cutoff_drift_sub_addDiff_fractSum (n k : ℕ) :
    ArithmeticFunction.vonMangoldt (n + 1) - 1 =
      (moebiusLogHarmonicSum (n + k + 1) - 1) -
        addDiff (weightedFractSumSeq vonMangoldtDivisorWeight (n + k + 1)) n := by
  have h := vonMangoldt_succ_eq_common_cutoff_harmonic_sub_addDiff_fractSum n k
  linarith

/-- **Exact Harmonic-Drift Cancellation in `dyadicChebyshevDiffSeq (2 * m)`:**
At any common cutoff `2 * m + k ≥ 2 * m`, the linear harmonic drift
`2 * (m * H_{μ log}(2m + k)) - (2m) * H_{μ log}(2m + k) = 0` cancels identically, expressing
`dyadicChebyshevDiffSeq (2 * m) = 2 * ψ(m) - ψ(2m)` purely as the dyadic difference of the
Möbius-log sawtooth phase sum:
$$\operatorname{dyadicChebyshevDiffSeq}(2m)
  = \Phi_{\mathrm{fract}}(2m + k, 2m) - 2\,\Phi_{\mathrm{fract}}(2m + k, m).$$ -/
theorem dyadicChebyshevDiffSeq_two_mul_eq_fractSum_diff (m k : ℕ) :
    dyadicChebyshevDiffSeq (2 * m) =
      weightedFractSumSeq vonMangoldtDivisorWeight (2 * m + k) (2 * m) -
        2 * weightedFractSumSeq vonMangoldtDivisorWeight (2 * m + k) m := by
  unfold dyadicChebyshevDiffSeq
  rw [chebyshev_psi_even_half_eq m]
  change 2 * chebyshevPsiSeq m - chebyshevPsiSeq (2 * m) = _
  have h1 := chebyshevPsiSeq_eq_common_cutoff_harmonic_sub_fractSum m (m + k)
  have h2 := chebyshevPsiSeq_eq_common_cutoff_harmonic_sub_fractSum (2 * m) k
  rw [show m + (m + k) = 2 * m + k by omega] at h1
  have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  rw [h1, h2, hcast]
  ring

/-! ## §2. Log-Factorial & Stirling Producer Bounds on the Möbius-Log Sawtooth Phase -/

/-- For every `d : ℕ`, `|vonMangoldtDivisorWeight d| ≤ log d`. -/
theorem abs_vonMangoldtDivisorWeight_le_log (d : ℕ) :
    |vonMangoldtDivisorWeight d| ≤ Real.log (d : ℝ) := by
  unfold vonMangoldtDivisorWeight
  rw [abs_mul, abs_neg, abs_of_nonneg (Real.log_natCast_nonneg d)]
  have hμ : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  nlinarith [Real.log_natCast_nonneg d]

/-- For every `d n : ℕ`, `0 ≤ fractDivSeq d n` and `fractDivSeq d n ≤ 1`. -/
theorem fractDivSeq_bounds (d n : ℕ) :
    0 ≤ fractDivSeq d n ∧ fractDivSeq d n ≤ 1 := by
  unfold fractDivSeq
  exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

/-- **Log-Factorial Upper Bound on the Möbius-Log Sawtooth Phase Sum:**
For every `N n : ℕ`, the Möbius-log sawtooth phase sum is bounded in absolute value by the
log-factorial `floorSummatory chebyshevPsi N = ∑_{d=1}^N log d`:
$$\bigl|\operatorname{weightedFractSumSeq}\,\operatorname{vonMangoldtDivisorWeight}\,N\,n\bigr|
  \;\le\; \operatorname{floorSummatory}\,\operatorname{chebyshevPsi}\,N.$$ -/
theorem abs_weightedFractSumSeq_vonMangoldt_le_floorSummatory (N n : ℕ) :
    |weightedFractSumSeq vonMangoldtDivisorWeight N n| ≤
      floorSummatory RHTower.chebyshevPsi N := by
  unfold weightedFractSumSeq
  rw [floorSummatory_chebyshevPsi]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [abs_mul]
  have hw := abs_vonMangoldtDivisorWeight_le_log d
  obtain ⟨hf0, hf1⟩ := fractDivSeq_bounds d n
  rw [abs_of_nonneg hf0]
  nlinarith [abs_nonneg (vonMangoldtDivisorWeight d)]

/-- **Stirling Producer Upper Bound on the Individual Sawtooth Phase Sum:**
For every `N ≥ 1` and `n : ℕ`,
$$\bigl|\operatorname{weightedFractSumSeq}\,\operatorname{vonMangoldtDivisorWeight}\,N\,n\bigr|
  \;\le\; N\log N - N + \log(N + 1) + 1.$$ -/
theorem abs_weightedFractSumSeq_vonMangoldt_le_stirling {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    |weightedFractSumSeq vonMangoldtDivisorWeight N n| ≤
      (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + Real.log ((N : ℝ) + 1) + 1 := by
  have h1 := abs_weightedFractSumSeq_vonMangoldt_le_floorSummatory N n
  rw [floorSummatory_chebyshevPsi_eq_main_add_stirlingResidual N] at h1
  have h2 := (stirlingResidual_bounds hN).2
  linarith

/-- **Log-Free Linear Bound on the Dyadic Sawtooth Phase Difference:**
Whereas each individual sawtooth sum $\Phi_{\mathrm{fract}}(2m+k, \cdot)$ has scale $O(m \log m)$,
the dyadic combination $\Phi_{\mathrm{fract}}(2m+k, 2m) - 2\,\Phi_{\mathrm{fract}}(2m+k, m)$
cancels the logarithmic factor completely and satisfies:
$$\bigl|\Phi_{\mathrm{fract}}(2m + k, 2m) - 2\,\Phi_{\mathrm{fract}}(2m + k, m)\bigr|
  \;\le\; (\log 4 + 4)\,(2m).$$ -/
theorem abs_dyadic_sawtooth_phase_diff_le (m k : ℕ) :
    |weightedFractSumSeq vonMangoldtDivisorWeight (2 * m + k) (2 * m) -
      2 * weightedFractSumSeq vonMangoldtDivisorWeight (2 * m + k) m| ≤
    (Real.log 4 + 4) * (2 * (m : ℝ)) := by
  rw [← dyadicChebyshevDiffSeq_two_mul_eq_fractSum_diff m k]
  unfold dyadicChebyshevDiffSeq
  have h := abs_two_mul_chebyshev_psi_half_sub_le (x := ((2 * m : ℕ) : ℝ)) (Nat.cast_nonneg _)
  have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  rw [hcast] at h ⊢
  exact h

/-- **Two-Sided Stirling Producer Sandwich for the Dyadic Sawtooth Phase Difference:**
For every `m ≥ 1` and `k : ℕ`,
$$\psi(m) - (2\log 2)m - \bigl(2\log(2m + 1) + 1\bigr)
  \;\le\; \Phi_{\mathrm{fract}}(2m + k, 2m) - 2\,\Phi_{\mathrm{fract}}(2m + k, m)
  \;\le\; 2\,\psi(m) - (2\log 2)m + \bigl(2\log(2m + 1) + 1\bigr).$$ -/
theorem dyadic_sawtooth_phase_diff_stirling_sandwich {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    RHTower.chebyshevPsi m - (2 * Real.log 2) * (m : ℝ) -
        (2 * Real.log (2 * (m : ℝ) + 1) + 1) ≤
      weightedFractSumSeq vonMangoldtDivisorWeight (2 * m + k) (2 * m) -
        2 * weightedFractSumSeq vonMangoldtDivisorWeight (2 * m + k) m ∧
    weightedFractSumSeq vonMangoldtDivisorWeight (2 * m + k) (2 * m) -
        2 * weightedFractSumSeq vonMangoldtDivisorWeight (2 * m + k) m ≤
      2 * RHTower.chebyshevPsi m - (2 * Real.log 2) * (m : ℝ) +
        (2 * Real.log (2 * (m : ℝ) + 1) + 1) := by
  rw [← dyadicChebyshevDiffSeq_two_mul_eq_fractSum_diff m k]
  exact ⟨stirling_lower_bound_dyadicChebyshevDiffSeq_two_mul hm,
    dyadicChebyshevDiffSeq_two_mul_le_stirling_upper_bound hm⟩

/-- **Exact Cumulative Identity for the Möbius-Log Sawtooth Phase Sum:**
For every `N : ℕ`, summing the Möbius-log sawtooth phase $\Phi_{\mathrm{fract}}(N, n)$ over
`1 ≤ n ≤ N` recovers the harmonic drift times $\sum_{n=1}^N n$ minus $\sum_{n=1}^N \psi(n)$:
$$\sum_{n=1}^N \Phi_{\mathrm{fract}}(N, n)
  = \left(\sum_{n=1}^N n\right) H_{\mu\log}(N)
    - \sum_{n=1}^N \psi(n).$$ -/
theorem sum_weightedFractSumSeq_eq_harmonic_mul_sum_sub_sum_chebyshevPsi (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, weightedFractSumSeq vonMangoldtDivisorWeight N n) =
      (∑ n ∈ Finset.Icc 1 N, (n : ℝ)) * moebiusLogHarmonicSum N -
        ∑ n ∈ Finset.Icc 1 N, RHTower.chebyshevPsi n := by
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨_, hnN⟩ := Finset.mem_Icc.mp hn
  have h := chebyshevPsiSeq_eq_common_cutoff_harmonic_sub_fractSum n (N - n)
  rw [Nat.add_sub_of_le hnN, chebyshevPsiSeq_eq_chebyshevPsi] at h
  linarith

/-- **Exact Hyperbolic-Grid Cumulative Identity Linking the Sawtooth Phase to `floorSummatory chebyshevPsi`:**
Summing $\Phi_{\mathrm{fract}}(N, \lfloor N / n \rfloor)$ over `1 ≤ n ≤ N` recovers the Dirichlet
divisor summatory times $H_{\mu\log}(N)$ minus `floorSummatory chebyshevPsi N`:
$$\sum_{n=1}^N \Phi_{\mathrm{fract}}(N, \lfloor N / n \rfloor)
  = \left(\sum_{n=1}^N \left\lfloor\frac{N}{n}\right\rfloor\right) H_{\mu\log}(N)
    - \operatorname{floorSummatory}\,\operatorname{chebyshevPsi}\,N.$$ -/
theorem sum_weightedFractSumSeq_div_eq_harmonic_mul_divisor_sub_floorSummatory (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, weightedFractSumSeq vonMangoldtDivisorWeight N (N / n)) =
      (∑ n ∈ Finset.Icc 1 N, ((N / n : ℕ) : ℝ)) * moebiusLogHarmonicSum N -
        floorSummatory RHTower.chebyshevPsi N := by
  unfold floorSummatory
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hdiv_le : N / n ≤ N := Nat.div_le_self N n
  have h := chebyshevPsiSeq_eq_common_cutoff_harmonic_sub_fractSum (N / n) (N - N / n)
  rw [Nat.add_sub_of_le hdiv_le, chebyshevPsiSeq_eq_chebyshevPsi] at h
  linarith

/-! ## §3. Band-Limited Critical-Line Spectral Density Producers & Full Weil Functional Bounds -/

/-- Explicit high-frequency remainder in the critical-line band theorem at $\xi_0 = \sqrt{N + 2}$:
$$\operatorname{bandRemainderProducer}(N)
  := \frac{52(\log 4 + 4)}{\pi^3}\,\operatorname{cutoff}(N)
    + \frac{32 + 8(\log 4 + 4)}{\pi^2} + \frac{4}{3\pi^4}.$$ -/
def bandRemainderProducer (N : ℕ) : ℝ :=
  52 * (Real.log 4 + 4) / Real.pi ^ 3 * cutoff N +
    (32 + 8 * (Real.log 4 + 4)) / Real.pi ^ 2 +
    4 / (3 * Real.pi ^ 4)

theorem bandRemainderProducer_nonneg (N : ℕ) : 0 ≤ bandRemainderProducer N := by
  unfold bandRemainderProducer
  have hcut : 0 ≤ cutoff N := cutoff_nonneg N
  positivity

/-- The critical-line band integral $\int_{-\xi_0}^{\xi_0} S_N(\xi)\,d\xi$ is bounded above by the
prime-free archimedean producer `laplaceEnergyProducerBound N` for every `N : ℕ` and `ξ₀ : ℝ`. -/
theorem band_spectralDensity_integral_le_laplaceEnergyProducerBound (N : ℕ) (ξ₀ : ℝ) :
    (∫ ξ in Icc (-ξ₀) ξ₀, spectralDensity N ξ) ≤ laplaceEnergyProducerBound N :=
  (band_le_laplaceEnergy N).trans (laplaceEnergy_le_laplaceEnergyProducerBound N)

/-- **Band-Split Packet Energy Producer Bound (`packetEnergy_le_band_spectralDensity_add_remainder`):**
For every `C¹` compactly supported source `f` and `N : ℕ`, the prime–polar packet energy
`packetEnergy f N` is controlled by the critical-line band integral
$\int_{|\xi| \le \sqrt{N+2}} S_N(\xi)\,d\xi$ plus the $O(\log N)$ high-frequency remainder
`bandRemainderProducer N`: -/
theorem packetEnergy_le_band_spectralDensity_add_remainder (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    SignedPrimePolar.packetEnergy f N ≤
      (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
        ((∫ ξ in Icc (-bandFrequency N) (bandFrequency N), spectralDensity N ξ) +
          bandRemainderProducer N) := by
  refine (ChebyshevGauge.packetEnergy_le_laplaceEnergy f hf N).trans ?_
  exact mul_le_mul_of_nonneg_left (laplaceEnergy_le_band_add_linear N) (sq_nonneg _)

/-- **Derivative-Free Band-Split Collar Packet Energy Producer Bound:**
For every continuous `f : C_c(ℝ, ℝ)` and `a b : ℝ`, `N : ℕ` (with **zero differentiability
hypotheses**!), the collar-smoothed packet energy is controlled by `collarGaugeBudget f a b` times
the critical-line band integral plus `bandRemainderProducer N`, with **no derivatives of `f` and
no boundary terms**: -/
theorem collar_packetEnergy_le_band_spectralDensity_add_remainder
    (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    SignedPrimePolar.packetEnergy (SignedPrimePolar.collarSource f a b) N ≤
      SignedPrimePolar.collarGaugeBudget f a b *
        ((∫ ξ in Icc (-bandFrequency N) (bandFrequency N), spectralDensity N ξ) +
          bandRemainderProducer N) :=
  (collar_packetEnergy_le_budget_mul_laplaceEnergy f a b N).trans
    (mul_le_mul_of_nonneg_left (laplaceEnergy_le_band_add_linear N)
      (SignedPrimePolar.collarGaugeBudget_nonneg f a b))

namespace RealWeilTestFn

/-- **Band-Limited Critical-Line Spectral Bound on `weilFullFunctional` (`RealWeilTestFn`):** -/
theorem weilFullFunctional_vonMangoldt_bandSpectral_bound
    (f : RealWeilTestFn) (c : ℝ) :
    |(weilFullFunctional
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest f.1.1 f.1.1)).re -
        poleWeightArchRe 0 f.1| ≤
      Real.exp c * autocorr f.source 0 +
        Real.exp (-c) *
          ((∫ t, |ChebyshevGauge.gaugeDerivative f.toCompactlySupported t|) ^ 2 *
            ((∫ ξ in Icc (-bandFrequency f.supportScale) (bandFrequency f.supportScale),
                spectralDensity f.supportScale ξ) +
              bandRemainderProducer f.supportScale)) := by
  have hid := f.re_weilFullFunctional_vonMangoldt_eq_poleWeightArchRe_zero_sub_two_pairing
  have hsub :
      (weilFullFunctional
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest f.1.1 f.1.1)).re -
        poleWeightArchRe 0 f.1 =
      -(2 * SignedPrimePolar.pairing f.supportScale (autocorr f.source)) := by
    linarith only [hid]
  rw [hsub, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  refine (BiScaleUncertainty.two_mul_abs_pairing_le_exp_add_packetEnergy
    f.toCompactlySupported f.supportScale c).trans ?_
  refine add_le_add le_rfl ?_
  exact mul_le_mul_of_nonneg_left
    (BiScaleUncertainty.packetEnergy_le_band_spectralDensity_add_remainder
      f.toCompactlySupported f.contDiff_one_source f.supportScale)
    (Real.exp_pos (-c)).le

/-- **Band-Limited Critical-Line Spectral Lower Bound on `weilFullFunctional` (`RealWeilTestFn`):** -/
theorem weilFullFunctional_vonMangoldt_bandSpectral_lower_bound
    (f : RealWeilTestFn) (c : ℝ) :
    biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re -
        Real.exp c * autocorr f.source 0 -
        Real.exp (-c) *
          ((∫ t, |ChebyshevGauge.gaugeDerivative f.toCompactlySupported t|) ^ 2 *
            ((∫ ξ in Icc (-bandFrequency f.supportScale) (bandFrequency f.supportScale),
                spectralDensity f.supportScale ξ) +
              bandRemainderProducer f.supportScale)) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re := by
  have habs := f.weilFullFunctional_vonMangoldt_bandSpectral_bound c
  have hlow := neg_le_of_abs_le habs
  have hpole := f.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy
  linarith only [hlow, hpole]

end RealWeilTestFn

/-- **Band-Limited Critical-Line Spectral Lower Bound on `RealEvenPolarTestFn`:** -/
theorem RealEvenPolarTestFn.weilFullFunctional_vonMangoldt_bandSpectral_lower_bound
    (g : RealEvenPolarTestFn) (c : ℝ) :
    biScaleLevyEnergy g.source +
        EF.gammaBracket 0 * (EF.weilTest g.1.1.1 g.1.1.1 0).re -
        Real.exp c * autocorr g.source 0 -
        Real.exp (-c) *
          ((∫ t, |ChebyshevGauge.gaugeDerivative
              (RealEvenPolarTestFn.toCompactlySupported g) t|) ^ 2 *
            ((∫ ξ in Icc (-bandFrequency (RealEvenPolarTestFn.toRealWeilTestFn g).supportScale)
                (bandFrequency (RealEvenPolarTestFn.toRealWeilTestFn g).supportScale),
                spectralDensity (RealEvenPolarTestFn.toRealWeilTestFn g).supportScale ξ) +
              bandRemainderProducer (RealEvenPolarTestFn.toRealWeilTestFn g).supportScale)) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest g.1.1.1 g.1.1.1)).re :=
  (RealEvenPolarTestFn.toRealWeilTestFn g).weilFullFunctional_vonMangoldt_bandSpectral_lower_bound c

namespace RealOddTestFn

/-- **Band-Limited Critical-Line Spectral Lower Bound on `RealOddTestFn`:** -/
theorem weilFullFunctional_vonMangoldt_bandSpectral_lower_bound
    (f : RealOddTestFn) (c : ℝ) :
    biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1.1 f.1.1.1 0).re -
        Real.exp c * autocorr f.source 0 -
        Real.exp (-c) *
          ((∫ t, |ChebyshevGauge.gaugeDerivative f.toCompactlySupported t|) ^ 2 *
            ((∫ ξ in Icc (-bandFrequency f.toRealWeilTestFn.supportScale)
                (bandFrequency f.toRealWeilTestFn.supportScale),
                spectralDensity f.toRealWeilTestFn.supportScale ξ) +
              bandRemainderProducer f.toRealWeilTestFn.supportScale)) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1.1 f.1.1.1)).re :=
  f.toRealWeilTestFn.weilFullFunctional_vonMangoldt_bandSpectral_lower_bound c

end RealOddTestFn

namespace RealHyperplaneGenerator

/-- **Band-Limited Critical-Line Spectral Lower Bound on `RealHyperplaneGenerator`:** -/
theorem weilFullFunctional_vonMangoldt_bandSpectral_lower_bound
    (x : RealHyperplaneGenerator) (c : ℝ) :
    biScaleLevyEnergy (RealHyperplaneGenerator.source x) +
        EF.gammaBracket 0 *
          (EF.weilTest (RealHyperplaneGenerator.toRealWeilTestFn x).1.1
            (RealHyperplaneGenerator.toRealWeilTestFn x).1.1 0).re -
        Real.exp c * autocorr (RealHyperplaneGenerator.source x) 0 -
        Real.exp (-c) *
          ((∫ t, |ChebyshevGauge.gaugeDerivative
              (RealHyperplaneGenerator.toRealWeilTestFn x).toCompactlySupported t|) ^ 2 *
            ((∫ ξ in Icc (-bandFrequency (RealHyperplaneGenerator.toRealWeilTestFn x).supportScale)
                (bandFrequency (RealHyperplaneGenerator.toRealWeilTestFn x).supportScale),
                spectralDensity (RealHyperplaneGenerator.toRealWeilTestFn x).supportScale ξ) +
              bandRemainderProducer (RealHyperplaneGenerator.toRealWeilTestFn x).supportScale)) ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (RealHyperplaneGenerator.toRealWeilTestFn x).1.1
          (RealHyperplaneGenerator.toRealWeilTestFn x).1.1)).re :=
  (RealHyperplaneGenerator.toRealWeilTestFn x).weilFullFunctional_vonMangoldt_bandSpectral_lower_bound c

end RealHyperplaneGenerator

end

end GaloisForLFunctions.BiScaleUncertainty

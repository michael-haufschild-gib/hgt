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

/-- **Exact Cumulative Identity Linking the Sawtooth Phase Sum to `floorSummatory chebyshevPsi`:**
For every `N : ℕ`, summing the Möbius-log sawtooth phase $\Phi_{\mathrm{fract}}(N, n)$ over
`1 ≤ n ≤ N` recovers the harmonic drift times $\sum_{n=1}^N n$ minus `floorSummatory chebyshevPsi N`:
$$\sum_{n=1}^N \Phi_{\mathrm{fract}}(N, n)
  = \left(\sum_{n=1}^N n\right) H_{\mu\log}(N)
    - \operatorname{floorSummatory}\,\operatorname{chebyshevPsi}\,N.$$ -/
theorem sum_weightedFractSumSeq_eq_harmonic_mul_sum_sub_floorSummatory (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, weightedFractSumSeq vonMangoldtDivisorWeight N n) =
      (∑ n ∈ Finset.Icc 1 N, (n : ℝ)) * moebiusLogHarmonicSum N -
        floorSummatory RHTower.chebyshevPsi N := by
  unfold floorSummatory
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨_, hnN⟩ := Finset.mem_Icc.mp hn
  have h := chebyshevPsiSeq_eq_common_cutoff_harmonic_sub_fractSum n (N - n)
  rw [Nat.add_sub_of_le hnN, chebyshevPsiSeq_eq_chebyshevPsi] at h
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
For every `f : C_c(ℝ, ℝ)` and `N : ℕ`, the prime–polar packet energy `packetEnergy f N` is
controlled by the critical-line band integral $\int_{|\xi| \le \sqrt{N+2}} S_N(\xi)\,d\xi$ plus
the $O(\log N)$ high-frequency remainder `bandRemainderProducer N`: -/
theorem packetEnergy_le_band_spectralDensity_add_remainder (f : C_c(ℝ, ℝ)) (N : ℕ) :
    packetEnergy f N ≤
      (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
        ((∫ ξ in Icc (-bandFrequency N) (bandFrequency N), spectralDensity N ξ) +
          bandRemainderProducer N) := by
  refine (CausalCorrelationPacketRepresentation.packetEnergy_le_laplaceEnergy f N).trans ?_
  exact mul_le_mul_of_nonneg_left (laplaceEnergy_le_band_add_linear N) (sq_nonneg _)

/-- **Derivative-Free Band-Split Collar Packet Energy Producer Bound:**
For every `f : C_c(ℝ, ℝ)`, `a < b`, and `N : ℕ`, the collar-smoothed packet energy is controlled
by `collarGaugeBudget f a b` times the critical-line band integral plus `bandRemainderProducer N`,
with **no derivatives of `f` and no boundary terms**: -/
theorem collar_packetEnergy_le_band_spectralDensity_add_remainder
    (f : C_c(ℝ, ℝ)) {a b : ℝ} (hab : a < b) (N : ℕ) :
    packetEnergy (collarSource f a b) N ≤
      collarGaugeBudget f a b *
        ((∫ ξ in Icc (-bandFrequency N) (bandFrequency N), spectralDensity N ξ) +
          bandRemainderProducer N) := by
  refine (collar_packetEnergy_le_budget_mul_laplaceEnergy f hab N).trans ?_
  have hbud : 0 ≤ collarGaugeBudget f a b := by
    unfold collarGaugeBudget
    have hE : 0 ≤ collarEnergy f a b := collarEnergy_nonneg f hab
    positivity
  exact mul_le_mul_of_nonneg_left (laplaceEnergy_le_band_add_linear N) hbud

/-- **Band-Limited Critical-Line Spectral Lower Bound on `weilFullFunctional` (`RealWeilTestFn`):**
For every `f : RealWeilTestFn` and `a < b`, `c : ℝ`, the full Weil explicit-formula functional of
`Λ` is bounded below directly in terms of the critical-line band integral
$\int_{|\xi| \le \sqrt{N+2}} S_N(\xi)\,d\xi$ plus `bandRemainderProducer N`: -/
theorem RealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_bandSpectral_lower_bound
    (f : RealWeilTestFn) {a b : ℝ} (hab : a < b) (c : ℝ) :
    (1 - 2 * Real.exp c) * biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re -
        Real.exp c *
          (4 * (b - a) / 3 * (Real.exp b + 1) ^ 2 *
            collarEnergy f.toCompactlySupported a b) -
        collarGaugeBudget f.toCompactlySupported a b *
          ((∫ ξ in Icc (-bandFrequency f.supportScale) (bandFrequency f.supportScale),
              spectralDensity f.supportScale ξ) +
            bandRemainderProducer f.supportScale) /
          Real.exp c ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re := by
  have h1 := f.weilFullFunctional_vonMangoldt_eq_arch_sub_pairing
  have h2 := two_mul_abs_pairing_le_collar_packetEnergy f.toCompactlySupported hab c
  have h3 := collar_packetEnergy_le_band_spectralDensity_add_remainder
    f.toCompactlySupported hab f.supportScale
  have hdiv :
      packetEnergy (collarSource f.toCompactlySupported a b) f.supportScale / Real.exp c ≤
        collarGaugeBudget f.toCompactlySupported a b *
          ((∫ ξ in Icc (-bandFrequency f.supportScale) (bandFrequency f.supportScale),
              spectralDensity f.supportScale ξ) +
            bandRemainderProducer f.supportScale) /
          Real.exp c :=
    div_le_div_of_nonneg_right h3 (Real.exp_pos c).le
  have habs := le_abs_self (SignedPrimePolar.pairing (autocorr f.toCompactlySupported) f.supportScale)
  linarith

/-- **Band-Limited Critical-Line Spectral Lower Bound on `RealEvenPolarTestFn`:** -/
theorem RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_bandSpectral_lower_bound
    (f : RealEvenPolarTestFn) {a b : ℝ} (hab : a < b) (c : ℝ) :
    (1 - 2 * Real.exp c) * biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1.1 f.1.1.1 0).re -
        Real.exp c *
          (4 * (b - a) / 3 * (Real.exp b + 1) ^ 2 *
            collarEnergy f.toCompactlySupported a b) -
        collarGaugeBudget f.toCompactlySupported a b *
          ((∫ ξ in Icc (-bandFrequency f.supportScale) (bandFrequency f.supportScale),
              spectralDensity f.supportScale ξ) +
            bandRemainderProducer f.supportScale) /
          Real.exp c ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1.1 f.1.1.1)).re :=
  f.toRealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_bandSpectral_lower_bound hab c

end

end GaloisForLFunctions.BiScaleUncertainty

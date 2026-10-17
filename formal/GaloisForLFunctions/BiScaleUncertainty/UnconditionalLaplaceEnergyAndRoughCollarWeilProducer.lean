import GaloisForLFunctions.BiScaleUncertainty.UnconditionalChebyshevCellAndArchimedeanWeilProducer
import GaloisForLFunctions.BiScaleUncertainty.CausalExponentialResponseAndLaplaceEnergy
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarOptimalCollar

/-!
# Pillar XXXI: All-Scale Dyadic Chebyshev Producers, Unconditional Laplace Energy & Derivative-Free Correlation Collar Weil Producers

This module develops **Pillar XXXI** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**,
advancing the field's **unconditional producer** machinery along four axes:

1. **All-Scale Telescoping Dyadic Chebyshev Factorial Producer (§1):**
   - Summing the Stirling-controlled alternating Chebyshev factorial producer
     `chebyshevAlternatingProducer (2^k) = T(2^{k+1}) - 2 T(2^k)` across dyadic scales
     `k ∈ range K`, we define the **Dyadic Cumulative Chebyshev Producer**
     $$\operatorname{dyadicCumulativeChebyshevProducer}(K)
       := \sum_{k=0}^{K-1} \operatorname{chebyshevAlternatingProducer}(2^k).$$
   - Because `chebyshevPsi (2 * N) - chebyshevPsi N ≤ chebyshevAlternatingProducer N` and
     `chebyshevPsi 1 = 0`, the dyadic differences telescope identically to `chebyshevPsi (2^K)`,
     yielding the **unconditional Stirling-only dyadic Chebyshev upper bound**:
     $$\operatorname{chebyshevPsi}(2^K)
       \;\le\; \operatorname{dyadicCumulativeChebyshevProducer}(K)
       \;\le\; (2\log 2)(2^K - 1) + K\bigl(2\log(2^K + 1) + 1\bigr).$$

2. **Unconditional Prime-Free Laplace Gram Energy Producer & Laplace Packet Control (§2):**
   - Combining `CausalExponentialResponseAndLaplaceEnergy` with Pillar XXX's Nyquist-cell
     Chebyshev bounds (`integral_normalizedLogError_sq_cutoff_le` and
     `normalizedLogError_cutoff_sq_le`), we construct the explicit prime-free archimedean
     producer bound `laplaceEnergyProducerBound N` on the Laplace Gram energy
     `laplaceEnergy N = ∬ e^{-|s-t|/2} dν_N(s) dν_N(t)`.
   - Conversely, we prove that `laplaceEnergy N` controls both the bulk Chebyshev integral
     `∫_0^{cutoff N} normalizedLogError(t)² dt` and the boundary square
     `normalizedLogError (cutoff N) ^ 2`, yielding a direct bound on `packetEnergy f N` purely in
     terms of `laplaceEnergy N`.

3. **Unconditional Prime-Free Producer Bound on `SignedPrimePolar.mass N` (§3):**
   - Up through `SignedPrimePolarOptimalCollar`, every rough-source and collar bound retained the
     unbounded arithmetic sum `SignedPrimePolar.mass N = ∑_{n=1}^{N+2} Λ(n)/√n + ∫_0^L 2cosh(x/2) dx`.
   - We define the explicit prime-free producer bound
     $$\operatorname{massProducerBound}(N) := (\log 4 + 4)(N + 2) + 4\sinh\Bigl(\frac{\operatorname{cutoff}(N)}{2}\Bigr)$$
     and prove `SignedPrimePolar.mass N ≤ massProducerBound N` unconditionally.

4. **Derivative-Free, Correlation-Only Archimedean Collar & Trial Weil Producers (§4–§5):**
   - Substituting `chebyshevProducerSlope`, `integral_normalizedLogError_sq_cutoff_le`, and
     `massProducerBound` into `collarPacketBound`, `correlationGaugeBound`, and `collarTrialBound`,
     we construct `archimedeanCollarPacketProducerBound`,
     `archimedeanCorrelationGaugeProducerBound`, and `archimedeanCollarTrialProducerBound`.
   - These bound `packetEnergy f N`, `|pairing N (autocorr f)|`, and the full untruncated Weil
     explicit-formula functional `(weilFullFunctional Λ (weilTest f f)).re` with **zero
     arithmetic functions** and **zero derivatives of `f`** on the bound side—depending only on the
     autocorrelation `autocorr f` and the support radius `multiplierSourceRadius f`.
-/

open Complex MeasureTheory Set Filter Topology Finsupp
open Zeta23
open _root_.RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector RHTower.WeilOneSided RHTower.WeilPoleWeight
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open scoped RealInnerProductSpace BigOperators CompactlySupported ArithmeticFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ## §1. All-Scale Telescoping Dyadic Chebyshev Factorial Producer -/

/-- `chebyshevPsi 1 = 0`, since `Λ(1) = 0`. -/
theorem chebyshevPsi_one_eq_zero : chebyshevPsi 1 = 0 := by
  unfold chebyshevPsi
  simp

/-- **Exact Dyadic Telescoping of `chebyshevPsi`:**
For every `K : ℕ`,
`∑ k ∈ Finset.range K, (chebyshevPsi (2 * 2^k) - chebyshevPsi (2^k)) = chebyshevPsi (2^K)`. -/
theorem sum_dyadic_chebyshevPsi_diff_eq (K : ℕ) :
    (∑ k ∈ Finset.range K, (chebyshevPsi (2 * 2 ^ k) - chebyshevPsi (2 ^ k))) =
      chebyshevPsi (2 ^ K) := by
  have hpow : ∀ k : ℕ, 2 * 2 ^ k = 2 ^ (k + 1) := fun k => by ring
  simp_rw [hpow]
  rw [Finset.sum_range_sub (fun k => chebyshevPsi (2 ^ k)) K, pow_zero,
    chebyshevPsi_one_eq_zero, sub_zero]

/-- **Dyadic Cumulative Chebyshev–Nyman–Beurling Producer:**
Sums `chebyshevAlternatingProducer (2^k) = T(2^{k+1}) - 2 T(2^k)` across all dyadic scales
`0 ≤ k < K`. -/
def dyadicCumulativeChebyshevProducer (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, chebyshevAlternatingProducer (2 ^ k)

/-- **Unconditional Dominance of `chebyshevPsi (2^K)` by `dyadicCumulativeChebyshevProducer K`:**
For every `K : ℕ`,
`chebyshevPsi (2^K) ≤ dyadicCumulativeChebyshevProducer K`. -/
theorem chebyshevPsi_two_pow_le_dyadicCumulativeChebyshevProducer (K : ℕ) :
    chebyshevPsi (2 ^ K) ≤ dyadicCumulativeChebyshevProducer K := by
  rw [← sum_dyadic_chebyshevPsi_diff_eq K]
  unfold dyadicCumulativeChebyshevProducer
  exact Finset.sum_le_sum fun k _ => chebyshevPsi_two_mul_sub_le_alternatingProducer (2 ^ k)

/-- Geometric sum of real powers of `2`: `∑ k ∈ range K, ((2^k : ℕ) : ℝ) = 2^K - 1`. -/
theorem sum_range_two_pow_nat_cast (K : ℕ) :
    (∑ k ∈ Finset.range K, ((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ K - 1 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- **Unconditional Stirling-Only Upper Bound on `dyadicCumulativeChebyshevProducer K`:**
For every `K : ℕ`,
`dyadicCumulativeChebyshevProducer K ≤ (2 * log 2) * (2^K - 1) + K * (2 * log(2^K + 1) + 1)`. -/
theorem dyadicCumulativeChebyshevProducer_le (K : ℕ) :
    dyadicCumulativeChebyshevProducer K ≤
      (2 * Real.log 2) * ((2 : ℝ) ^ K - 1) +
        (K : ℝ) * (2 * Real.log ((2 : ℝ) ^ K + 1) + 1) := by
  unfold dyadicCumulativeChebyshevProducer
  have hterm : ∀ k ∈ Finset.range K,
      chebyshevAlternatingProducer (2 ^ k) ≤
        (2 * Real.log 2) * ((2 ^ k : ℕ) : ℝ) +
          (2 * Real.log ((2 : ℝ) ^ K + 1) + 1) := by
    intro k hk
    have hkK : k + 1 ≤ K := Finset.mem_range.mp hk
    have hpow_pos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have habs := abs_chebyshevAlternatingProducer_sub_linear_le hpow_pos
    have hup : chebyshevAlternatingProducer (2 ^ k) - (2 * Real.log 2) * ((2 ^ k : ℕ) : ℝ) ≤
        2 * Real.log (2 * ((2 ^ k : ℕ) : ℝ) + 1) + 1 := (abs_le.mp habs).2
    have hpow_le : 2 * ((2 ^ k : ℕ) : ℝ) ≤ (2 : ℝ) ^ K := by
      have hnat : 2 * 2 ^ k ≤ 2 ^ K := by
        calc 2 * 2 ^ k = 2 ^ (k + 1) := by ring
          _ ≤ 2 ^ K := Nat.pow_le_pow_right (by omega) hkK
      exact_mod_cast hnat
    have hlog_le : Real.log (2 * ((2 ^ k : ℕ) : ℝ) + 1) ≤ Real.log ((2 : ℝ) ^ K + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  calc (∑ k ∈ Finset.range K, chebyshevAlternatingProducer (2 ^ k))
      ≤ ∑ k ∈ Finset.range K,
          ((2 * Real.log 2) * ((2 ^ k : ℕ) : ℝ) +
            (2 * Real.log ((2 : ℝ) ^ K + 1) + 1)) :=
        Finset.sum_le_sum hterm
    _ = (2 * Real.log 2) * (∑ k ∈ Finset.range K, ((2 ^ k : ℕ) : ℝ)) +
          ∑ _ ∈ Finset.range K, (2 * Real.log ((2 : ℝ) ^ K + 1) + 1) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = (2 * Real.log 2) * ((2 : ℝ) ^ K - 1) +
          (K : ℝ) * (2 * Real.log ((2 : ℝ) ^ K + 1) + 1) := by
        rw [sum_range_two_pow_nat_cast, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Elementary Stirling-Driven All-Scale Dyadic Chebyshev Upper Bound:**
For every `K : ℕ`,
`chebyshevPsi (2^K) ≤ (2 * log 2) * (2^K - 1) + K * (2 * log(2^K + 1) + 1)`. -/
theorem chebyshevPsi_two_pow_le_linear_add_log (K : ℕ) :
    chebyshevPsi (2 ^ K) ≤
      (2 * Real.log 2) * ((2 : ℝ) ^ K - 1) +
        (K : ℝ) * (2 * Real.log ((2 : ℝ) ^ K + 1) + 1) :=
  (chebyshevPsi_two_pow_le_dyadicCumulativeChebyshevProducer K).trans
    (dyadicCumulativeChebyshevProducer_le K)

/-! ## §2. Unconditional Prime-Free Laplace Gram Energy Producer & Laplace Packet Control -/

/-- **Explicit Prime-Free Archimedean Producer Bound on `laplaceEnergy N`:**
`laplaceEnergyProducerBound N := 2 * chebyshevProducerSlope ^ 2 * (2 * N + 3) + 6 + 2 * ((1 - cutoff N) * exp(-cutoff N / 2)) ^ 2`. -/
def laplaceEnergyProducerBound (N : ℕ) : ℝ :=
  2 * chebyshevProducerSlope ^ 2 * (2 * (N : ℝ) + 3) + 6 +
    2 * ((1 - SignedPrimePolar.cutoff N) * Real.exp (-SignedPrimePolar.cutoff N / 2)) ^ 2

theorem laplaceEnergyProducerBound_nonneg (N : ℕ) :
    0 ≤ laplaceEnergyProducerBound N := by
  unfold laplaceEnergyProducerBound
  positivity

/-- **Unconditional Prime-Free Upper Bound on `laplaceEnergy N`:**
For every `N : ℕ`, the Laplace Gram energy
`laplaceEnergy N = ∬ e^{-|s-t|/2} dν_N(s) dν_N(t)` is bounded by the prime-free archimedean
producer `laplaceEnergyProducerBound N`. -/
theorem laplaceEnergy_le_laplaceEnergyProducerBound (N : ℕ) :
    ChebyshevGauge.laplaceEnergy N ≤ laplaceEnergyProducerBound N := by
  have h1 := ChebyshevGauge.laplaceEnergy_le_chebyshev_mean_square N
  have hint := integral_normalizedLogError_sq_cutoff_le N
  have hcut := normalizedLogError_cutoff_sq_le N
  set E := ChebyshevGauge.normalizedLogError (SignedPrimePolar.cutoff N)
  set T := (1 - SignedPrimePolar.cutoff N) * Real.exp (-SignedPrimePolar.cutoff N / 2)
  have hET : (E + T) ^ 2 ≤ 2 * E ^ 2 + 2 * T ^ 2 := by
    nlinarith [sq_nonneg (E - T)]
  unfold laplaceEnergyProducerBound
  linarith

/-- **Boundary `normalizedLogError (cutoff N) ^ 2` Controlled by `laplaceEnergy N`:**
For every `N : ℕ`,
`normalizedLogError (cutoff N) ^ 2 ≤ 2 * laplaceEnergy N + 2 * ((1 - cutoff N) * exp(-cutoff N / 2)) ^ 2`. -/
theorem normalizedLogError_cutoff_sq_le_laplaceEnergy (N : ℕ) :
    ChebyshevGauge.normalizedLogError (SignedPrimePolar.cutoff N) ^ 2 ≤
      2 * ChebyshevGauge.laplaceEnergy N +
        2 * ((1 - SignedPrimePolar.cutoff N) * Real.exp (-SignedPrimePolar.cutoff N / 2)) ^ 2 := by
  set L := SignedPrimePolar.cutoff N
  set E := ChebyshevGauge.normalizedLogError L
  set T := (1 - L) * Real.exp (-L / 2)
  have hwin_nonneg :
      0 ≤ ∫ t in Icc 0 L,
        (ChebyshevGauge.normalizedLogError t + (1 - t) * Real.exp (-t / 2)) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have htail_le : (E + T) ^ 2 ≤ ChebyshevGauge.laplaceEnergy N := by
    have hlap := ChebyshevGauge.laplaceEnergy_eq_window_add_tail N
    linarith
  have hE : E ^ 2 ≤ 2 * (E + T) ^ 2 + 2 * T ^ 2 := by
    nlinarith [sq_nonneg (E + 2 * T)]
  linarith

/-- **Packet Energy Controlled Directly by `laplaceEnergy N`:**
For every `C¹` compactly supported source `f` and `N : ℕ`, `packetEnergy f N` is controlled by
the single positive-definite Laplace Gram scalar `laplaceEnergy N`. -/
theorem packetEnergy_le_laplaceEnergy_gauge (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    SignedPrimePolar.packetEnergy f N ≤
      3 * (10 + 2 * ChebyshevGauge.laplaceEnergy N +
            2 * ((1 - SignedPrimePolar.cutoff N) *
              Real.exp (-SignedPrimePolar.cutoff N / 2)) ^ 2) * autocorr f 0 +
        3 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
          (2 * ChebyshevGauge.laplaceEnergy N + 2) := by
  have hp := ChebyshevGauge.packetEnergy_le_chebyshev_mean_square f hf N
  have hcut := normalizedLogError_cutoff_sq_le_laplaceEnergy N
  have hint := ChebyshevGauge.chebyshev_mean_square_le_laplaceEnergy N
  have h0 : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  have h1 :
      3 * (10 + ChebyshevGauge.normalizedLogError (SignedPrimePolar.cutoff N) ^ 2) *
          autocorr f 0 ≤
        3 * (10 + 2 * ChebyshevGauge.laplaceEnergy N +
              2 * ((1 - SignedPrimePolar.cutoff N) *
                Real.exp (-SignedPrimePolar.cutoff N / 2)) ^ 2) * autocorr f 0 := by
    nlinarith
  have h2 :
      3 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
          (∫ t in Icc 0 (SignedPrimePolar.cutoff N),
            ChebyshevGauge.normalizedLogError t ^ 2) ≤
        3 * (∫ u, |ChebyshevGauge.gaugeDerivative f u|) ^ 2 *
          (2 * ChebyshevGauge.laplaceEnergy N + 2) :=
    mul_le_mul_of_nonneg_left hint (by positivity)
  linarith

/-! ## §3. Unconditional Prime-Free Producer Bound on `SignedPrimePolar.mass N` -/

/-- Each critical-line prime weight `Λ(n) / √n` is at most `Λ(n)`. -/
theorem primeWeight_le_vonMangoldt (n : ℕ) :
    SignedPrimePolar.primeWeight n ≤ ArithmeticFunction.vonMangoldt n := by
  unfold SignedPrimePolar.primeWeight
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [Real.one_le_sqrt]
      exact_mod_cast hn
    exact div_le_self ArithmeticFunction.vonMangoldt_nonneg h1

/-- The atomic part of `SignedPrimePolar.mass N` is at most `Chebyshev.psi (N + 2)`. -/
theorem sum_primeWeight_le_chebyshev_psi (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 (N + 2), SignedPrimePolar.primeWeight n) ≤
      Chebyshev.psi ((N : ℝ) + 2) := by
  have hsum :
      (∑ n ∈ Finset.Icc 1 (N + 2), SignedPrimePolar.primeWeight n) ≤
        ∑ n ∈ Finset.Icc 1 (N + 2), ArithmeticFunction.vonMangoldt n :=
    Finset.sum_le_sum fun n _ => primeWeight_le_vonMangoldt n
  have hstep :
      SignedPrimePolar.step N (SignedPrimePolar.cutoff N) =
        ∑ n ∈ Finset.Icc 1 (N + 2), ArithmeticFunction.vonMangoldt n := by
    unfold SignedPrimePolar.step
    refine Finset.sum_congr rfl fun n hn => ?_
    exact if_pos (SignedPrimePolar.node_bounds N n hn).2
  have hpsi :
      SignedPrimePolar.step N (SignedPrimePolar.cutoff N) =
        Chebyshev.psi ((N : ℝ) + 2) := by
    rw [SignedPrimePolar.step_eq N le_rfl, exp_cutoff_eq N]
  linarith

/-- Exact evaluation of the polar density integral on `[0, cutoff N]`:
`∫_{x ∈ [0, cutoff N]} polarDensity x dx = 4 * sinh(cutoff N / 2)`. -/
theorem integral_polarDensity_cutoff_eq (N : ℕ) :
    (∫ x in Icc 0 (SignedPrimePolar.cutoff N), SignedPrimePolar.polarDensity x) =
      4 * Real.sinh (SignedPrimePolar.cutoff N / 2) := by
  unfold SignedPrimePolar.polarDensity
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (SignedPrimePolar.cutoff_nonneg N)]
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) (SignedPrimePolar.cutoff N),
      HasDerivAt (fun t : ℝ => 4 * Real.sinh (t / 2)) (2 * Real.cosh (x / 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => t / 2) ((1 : ℝ) / 2) x :=
      (hasDerivAt_id x).div_const 2
    exact (h1.sinh.const_mul 4).congr_deriv (by ring)
  have hint : IntervalIntegrable (fun t : ℝ => 2 * Real.cosh (t / 2)) volume
      0 (SignedPrimePolar.cutoff N) :=
    (continuous_const.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).intervalIntegrable
      0 (SignedPrimePolar.cutoff N)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [Real.sinh_zero]

/-- **Explicit Prime-Free Archimedean Producer Bound on `SignedPrimePolar.mass N`:**
`massProducerBound N := (log 4 + 4) * (N + 2) + 4 * sinh(cutoff N / 2)`. -/
def massProducerBound (N : ℕ) : ℝ :=
  (Real.log 4 + 4) * ((N : ℝ) + 2) + 4 * Real.sinh (SignedPrimePolar.cutoff N / 2)

theorem massProducerBound_nonneg (N : ℕ) : 0 ≤ massProducerBound N := by
  unfold massProducerBound
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hsinh : 0 ≤ Real.sinh (SignedPrimePolar.cutoff N / 2) :=
    Real.sinh_nonneg_iff.mpr (by linarith [SignedPrimePolar.cutoff_nonneg N])
  positivity

/-- **Unconditional Prime-Free Upper Bound on `SignedPrimePolar.mass N`:**
For every `N : ℕ`, `SignedPrimePolar.mass N ≤ massProducerBound N`. -/
theorem mass_le_massProducerBound (N : ℕ) :
    SignedPrimePolar.mass N ≤ massProducerBound N := by
  unfold SignedPrimePolar.mass massProducerBound
  have h1 := sum_primeWeight_le_chebyshev_psi N
  have h2 : Chebyshev.psi ((N : ℝ) + 2) ≤ (Real.log 4 + 4) * ((N : ℝ) + 2) :=
    Chebyshev.psi_le_const_mul_self (by positivity)
  have h3 := integral_polarDensity_cutoff_eq N
  linarith

theorem mass_sq_le_massProducerBound_sq (N : ℕ) :
    SignedPrimePolar.mass N ^ 2 ≤ massProducerBound N ^ 2 :=
  pow_le_pow_left₀ (SignedPrimePolar.mass_nonneg N) (mass_le_massProducerBound N) 2

/-! ## §4. Derivative-Free Correlation-Only Archimedean Collar & Trial Packet Producers -/

/-- **Prime-Free, Derivative-Free Archimedean Collar Packet Producer Bound:**
Replaces `normalizedLogError` in `collarPacketBound` with `chebyshevProducerSlope`. -/
def archimedeanCollarPacketProducerBound (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) : ℝ :=
  3 * (10 + chebyshevProducerSlope ^ 2 * ((N : ℝ) + 2)) *
      SignedPrimePolar.collarEnergy f a b +
    3 * SignedPrimePolar.collarGaugeBudget f a b *
      (chebyshevProducerSlope ^ 2 * ((N : ℝ) + 1) + 2)

theorem collarPacketBound_le_archimedeanCollarPacketProducerBound
    (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    SignedPrimePolar.collarPacketBound f a b N ≤
      archimedeanCollarPacketProducerBound f a b N := by
  unfold SignedPrimePolar.collarPacketBound archimedeanCollarPacketProducerBound
  have hce : 0 ≤ SignedPrimePolar.collarEnergy f a b :=
    SignedPrimePolar.collarEnergy_nonneg f a b
  have hgb : 0 ≤ SignedPrimePolar.collarGaugeBudget f a b :=
    SignedPrimePolar.collarGaugeBudget_nonneg f a b
  have hcut := normalizedLogError_cutoff_sq_le N
  have hint := integral_normalizedLogError_sq_cutoff_le N
  have h1 :
      3 * (10 + ChebyshevGauge.normalizedLogError (SignedPrimePolar.cutoff N) ^ 2) *
          SignedPrimePolar.collarEnergy f a b ≤
        3 * (10 + chebyshevProducerSlope ^ 2 * ((N : ℝ) + 2)) *
          SignedPrimePolar.collarEnergy f a b := by
    nlinarith
  have h2 :
      3 * SignedPrimePolar.collarGaugeBudget f a b *
          (∫ x in Icc 0 (SignedPrimePolar.cutoff N),
            ChebyshevGauge.normalizedLogError x ^ 2) ≤
        3 * SignedPrimePolar.collarGaugeBudget f a b *
          (chebyshevProducerSlope ^ 2 * ((N : ℝ) + 1) + 2) :=
    mul_le_mul_of_nonneg_left hint (by positivity)
  linarith

theorem collar_packetEnergy_le_archimedeanCollarPacketProducerBound
    (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    SignedPrimePolar.packetEnergy (SignedPrimePolar.collarSource f a b) N ≤
      archimedeanCollarPacketProducerBound f a b N :=
  (SignedPrimePolar.collar_packetEnergy_le_correlation f a b N).trans
    (collarPacketBound_le_archimedeanCollarPacketProducerBound f a b N)

/-- **Prime-Free, Derivative-Free Archimedean Correlation Gauge Producer Bound:**
Bounds `packetEnergy f N` for **every** `f : C_c(ℝ, ℝ)` (with **zero differentiability hypotheses**
and **zero arithmetic functions** on the bound side!) purely in terms of `autocorr f` and
`multiplierSourceRadius f`. -/
def archimedeanCorrelationGaugeProducerBound (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) : ℝ :=
  6 * (10 + chebyshevProducerSlope ^ 2 * ((N : ℝ) + 2)) *
      SignedPrimePolar.collarEnergy f a b +
    6 * SignedPrimePolar.collarGaugeBudget f a b *
      (chebyshevProducerSlope ^ 2 * ((N : ℝ) + 1) + 2) +
    2 * massProducerBound N ^ 2 * SignedPrimePolar.collarChordEnergy f a b

theorem correlationGaugeBound_le_archimedeanCorrelationGaugeProducerBound
    (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    SignedPrimePolar.correlationGaugeBound f a b N ≤
      archimedeanCorrelationGaugeProducerBound f a b N := by
  unfold SignedPrimePolar.correlationGaugeBound archimedeanCorrelationGaugeProducerBound
  have hce : 0 ≤ SignedPrimePolar.collarEnergy f a b :=
    SignedPrimePolar.collarEnergy_nonneg f a b
  have hgb : 0 ≤ SignedPrimePolar.collarGaugeBudget f a b :=
    SignedPrimePolar.collarGaugeBudget_nonneg f a b
  have hchord : 0 ≤ SignedPrimePolar.collarChordEnergy f a b :=
    SignedPrimePolar.collarChordEnergy_nonneg f a b
  have hcut := normalizedLogError_cutoff_sq_le N
  have hint := integral_normalizedLogError_sq_cutoff_le N
  have hmass := mass_sq_le_massProducerBound_sq N
  have h1 :
      6 * (10 + ChebyshevGauge.normalizedLogError (SignedPrimePolar.cutoff N) ^ 2) *
          SignedPrimePolar.collarEnergy f a b ≤
        6 * (10 + chebyshevProducerSlope ^ 2 * ((N : ℝ) + 2)) *
          SignedPrimePolar.collarEnergy f a b := by
    nlinarith
  have h2 :
      6 * SignedPrimePolar.collarGaugeBudget f a b *
          (∫ t in Icc 0 (SignedPrimePolar.cutoff N),
            ChebyshevGauge.normalizedLogError t ^ 2) ≤
        6 * SignedPrimePolar.collarGaugeBudget f a b *
          (chebyshevProducerSlope ^ 2 * ((N : ℝ) + 1) + 2) :=
    mul_le_mul_of_nonneg_left hint (by positivity)
  have h3 :
      2 * SignedPrimePolar.mass N ^ 2 * SignedPrimePolar.collarChordEnergy f a b ≤
        2 * massProducerBound N ^ 2 * SignedPrimePolar.collarChordEnergy f a b := by
    nlinarith
  linarith

/-- **Unconditional Derivative-Free Prime-Free Producer Bound on `packetEnergy f N`:**
Holds for **every** compactly supported continuous `f : C_c(ℝ, ℝ)` without any `ContDiff`
hypothesis! -/
theorem packetEnergy_le_archimedeanCorrelationGaugeProducerBound
    (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    SignedPrimePolar.packetEnergy f N ≤
      archimedeanCorrelationGaugeProducerBound f a b N :=
  (SignedPrimePolar.packetEnergy_le_correlationGaugeBound f a b N).trans
    (correlationGaugeBound_le_archimedeanCorrelationGaugeProducerBound f a b N)

/-- **Prime-Free, Derivative-Free Archimedean Signed Scalar Collar Trial Producer Bound:**
Retains the full signed scalar parameter `t : ℝ` and splitting parameter `c : ℝ` while eliminating
all prime and Chebyshev expressions from `collarTrialBound`. -/
def archimedeanCollarTrialProducerBound (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (1 + Real.exp c) * t ^ 2 * archimedeanCollarPacketProducerBound f a b N +
    (1 + 1 / Real.exp c) * massProducerBound N ^ 2 *
      (autocorr f 0 - 2 * t * correlationAverage f a b 0 +
        t ^ 2 * SignedPrimePolar.collarEnergy f a b)

theorem collarTrialBound_le_archimedeanCollarTrialProducerBound
    (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) (t : ℝ) :
    SignedPrimePolar.collarTrialBound f a b c N t ≤
      archimedeanCollarTrialProducerBound f a b c N t := by
  unfold SignedPrimePolar.collarTrialBound archimedeanCollarTrialProducerBound
  have hcp := collarPacketBound_le_archimedeanCollarPacketProducerBound f a b N
  have hmass := mass_sq_le_massProducerBound_sq N
  have hrem_nonneg :
      0 ≤ autocorr f 0 - 2 * t * correlationAverage f a b 0 +
            t ^ 2 * SignedPrimePolar.collarEnergy f a b := by
    rw [← SignedPrimePolar.autocorr_sub_smul_collar_zero f a b t]
    exact autocorr_zero_nonneg _
  have h1 :
      (1 + Real.exp c) * t ^ 2 * SignedPrimePolar.collarPacketBound f a b N ≤
        (1 + Real.exp c) * t ^ 2 * archimedeanCollarPacketProducerBound f a b N :=
    mul_le_mul_of_nonneg_left hcp (by positivity)
  have h2 :
      (1 + 1 / Real.exp c) * SignedPrimePolar.mass N ^ 2 *
          (autocorr f 0 - 2 * t * correlationAverage f a b 0 +
            t ^ 2 * SignedPrimePolar.collarEnergy f a b) ≤
        (1 + 1 / Real.exp c) * massProducerBound N ^ 2 *
          (autocorr f 0 - 2 * t * correlationAverage f a b 0 +
            t ^ 2 * SignedPrimePolar.collarEnergy f a b) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass (by positivity)) hrem_nonneg
  linarith

/-- **Unconditional Derivative-Free Prime-Free Trial Producer Bound on `packetEnergy f N`:**
For every `f : C_c(ℝ, ℝ)`, `a b c t : ℝ`, and `N : ℕ`,
`packetEnergy f N ≤ archimedeanCollarTrialProducerBound f a b c N t`. -/
theorem packetEnergy_le_archimedeanCollarTrialProducerBound
    (f : C_c(ℝ, ℝ)) (a b c t : ℝ) (N : ℕ) :
    SignedPrimePolar.packetEnergy f N ≤
      archimedeanCollarTrialProducerBound f a b c N t :=
  (SignedPrimePolar.packetEnergy_le_collarTrialBound f a b c t N).trans
    (collarTrialBound_le_archimedeanCollarTrialProducerBound f a b c N t)

/-- **Unconditional Derivative-Free Prime-Free Pairing Bound via `archimedeanCorrelationGaugeProducerBound`:**
For every `f : C_c(ℝ, ℝ)`, `a b c : ℝ`, and `N : ℕ` (with **zero differentiability hypotheses**!),
`2 * |pairing N (autocorr f)| ≤ e^c * autocorr f 0 + e^{-c} * archimedeanCorrelationGaugeProducerBound f a b N`. -/
theorem two_mul_abs_pairing_le_archimedeanCorrelationGaugeProducerBound
    (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) :
    2 * |SignedPrimePolar.pairing N (autocorr f)| ≤
      Real.exp c * autocorr f 0 +
        Real.exp (-c) * archimedeanCorrelationGaugeProducerBound f a b N := by
  refine (two_mul_abs_pairing_le_exp_add_packetEnergy f N c).trans ?_
  refine add_le_add le_rfl ?_
  exact mul_le_mul_of_nonneg_left
    (packetEnergy_le_archimedeanCorrelationGaugeProducerBound f a b N)
    (Real.exp_pos (-c)).le

/-! ## §5. Derivative-Free Correlation-Only Full Weil Functional Bounds Across All Test Spaces -/

namespace RealWeilTestFn

/-- **Unconditional Derivative-Free Correlation-Collar Full Weil Functional Bound on `RealWeilTestFn`:**
For EVERY `f : RealWeilTestFn` and EVERY `a b c : ℝ` (with **zero hypotheses**, **zero
`chebyshevWork`**, **zero arithmetic functions**, and **zero derivatives of `f`** on the bound
side!): -/
theorem unconditional_weilFullFunctional_vonMangoldt_correlationCollarProducer_bound
    (f : RealWeilTestFn) (a b c : ℝ) :
    |(weilFullFunctional
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest f.1.1 f.1.1)).re -
        poleWeightArchRe 0 f.1| ≤
      Real.exp c * autocorr f.source 0 +
        Real.exp (-c) *
          BiScaleUncertainty.archimedeanCorrelationGaugeProducerBound
            f.toCompactlySupported a b f.supportScale := by
  have hid := f.re_weilFullFunctional_vonMangoldt_eq_poleWeightArchRe_zero_sub_two_pairing
  have hsub :
      (weilFullFunctional
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest f.1.1 f.1.1)).re -
        poleWeightArchRe 0 f.1 =
      -(2 * SignedPrimePolar.pairing f.supportScale (autocorr f.source)) := by
    linarith only [hid]
  rw [hsub, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact BiScaleUncertainty.two_mul_abs_pairing_le_archimedeanCorrelationGaugeProducerBound
    f.toCompactlySupported a b c f.supportScale

/-- **Unconditional Derivative-Free Correlation-Collar Full Weil Functional Lower Bound on `RealWeilTestFn`:**
For EVERY `f : RealWeilTestFn` and EVERY `a b c : ℝ` (with **zero hypotheses**!), the full
untruncated Weil explicit-formula functional of `Λ` is bounded below by a 100% prime-free,
derivative-free correlation functional of `f`: -/
theorem unconditional_weilFullFunctional_vonMangoldt_correlationCollarProducer_lower_bound
    (f : RealWeilTestFn) (a b c : ℝ) :
    biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1 f.1.1 0).re -
        Real.exp c * autocorr f.source 0 -
        Real.exp (-c) *
          BiScaleUncertainty.archimedeanCorrelationGaugeProducerBound
            f.toCompactlySupported a b f.supportScale ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1 f.1.1)).re := by
  have habs := f.unconditional_weilFullFunctional_vonMangoldt_correlationCollarProducer_bound a b c
  have hlow := neg_le_of_abs_le habs
  have hpole := f.poleWeightArchRe_zero_eq_gamma_add_biScaleLevyEnergy
  linarith only [hlow, hpole]

end RealWeilTestFn

/-- **Unconditional Derivative-Free Correlation-Collar Full Weil Functional Lower Bound on `RealEvenPolarTestFn`:** -/
theorem RealEvenPolarTestFn.unconditional_weilFullFunctional_vonMangoldt_correlationCollarProducer_lower_bound
    (g : RealEvenPolarTestFn) (a b c : ℝ) :
    biScaleLevyEnergy g.source +
        EF.gammaBracket 0 * (EF.weilTest g.1.1.1 g.1.1.1 0).re -
        Real.exp c * autocorr g.source 0 -
        Real.exp (-c) *
          BiScaleUncertainty.archimedeanCorrelationGaugeProducerBound
            (RealEvenPolarTestFn.toCompactlySupported g) a b
            (RealEvenPolarTestFn.toRealWeilTestFn g).supportScale ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest g.1.1.1 g.1.1.1)).re :=
  (RealEvenPolarTestFn.toRealWeilTestFn g).unconditional_weilFullFunctional_vonMangoldt_correlationCollarProducer_lower_bound
    a b c

namespace RealOddTestFn

/-- **Unconditional Derivative-Free Correlation-Collar Full Weil Functional Lower Bound on `RealOddTestFn`:** -/
theorem unconditional_weilFullFunctional_vonMangoldt_correlationCollarProducer_lower_bound
    (f : RealOddTestFn) (a b c : ℝ) :
    biScaleLevyEnergy f.source +
        EF.gammaBracket 0 * (EF.weilTest f.1.1.1 f.1.1.1 0).re -
        Real.exp c * autocorr f.source 0 -
        Real.exp (-c) *
          BiScaleUncertainty.archimedeanCorrelationGaugeProducerBound
            f.toCompactlySupported a b f.toRealWeilTestFn.supportScale ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1.1.1 f.1.1.1)).re :=
  f.toRealWeilTestFn.unconditional_weilFullFunctional_vonMangoldt_correlationCollarProducer_lower_bound
    a b c

end RealOddTestFn

namespace RealHyperplaneGenerator

/-- **Unconditional Derivative-Free Correlation-Collar Full Weil Functional Lower Bound on `RealHyperplaneGenerator`:** -/
theorem unconditional_weilFullFunctional_vonMangoldt_correlationCollarProducer_lower_bound
    (x : RealHyperplaneGenerator) (a b c : ℝ) :
    biScaleLevyEnergy (RealHyperplaneGenerator.source x) +
        EF.gammaBracket 0 *
          (EF.weilTest (RealHyperplaneGenerator.toRealWeilTestFn x).1.1
            (RealHyperplaneGenerator.toRealWeilTestFn x).1.1 0).re -
        Real.exp c * autocorr (RealHyperplaneGenerator.source x) 0 -
        Real.exp (-c) *
          BiScaleUncertainty.archimedeanCorrelationGaugeProducerBound
            (RealHyperplaneGenerator.toRealWeilTestFn x).toCompactlySupported a b
            (RealHyperplaneGenerator.toRealWeilTestFn x).supportScale ≤
      (weilFullFunctional
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (RealHyperplaneGenerator.toRealWeilTestFn x).1.1
          (RealHyperplaneGenerator.toRealWeilTestFn x).1.1)).re :=
  (RealHyperplaneGenerator.toRealWeilTestFn x).unconditional_weilFullFunctional_vonMangoldt_correlationCollarProducer_lower_bound
    a b c

end RealHyperplaneGenerator

end

end GaloisForLFunctions.BiScaleUncertainty

import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.MoebiusEscapedPairingBoundaryLaw
import GaloisForLFunctions.BezoutValuationIncidence.ReceiverBoundedInTheVinogradovKorobovBand
import GaloisForLFunctions.BezoutValuationIncidence.ShortWindowPrimeSavingIsTheQuasiRiemannHypothesis
import GaloisForLFunctions.BezoutValuationIncidence.LittlewoodAdmitsTheReceiverAboveHalfTheZeroAbscissa
import GaloisForLFunctions.BezoutValuationIncidence.TheCentredPrimeBandFromAZeroFreeStrip
import GaloisForLFunctions.RHTower.AdmissionBelowHalfDampingAboveTheZeroWidth
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheDyadicAmplificationOfTheHeckeDefect
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.CriticalDiscsAndTheTerminalLens
import GaloisForLFunctions.HTGeometry.LogarithmicResidueQuantization
import GaloisForLFunctions.RHTower.CrossRouteReceiverBridges
import GaloisForLFunctions.RHTower.XiLogDerivNonholonomic

/-!
# Unconditional Escaped Möbius Decay, Vinogradov–Korobov Rate, and the Cross-Route Bridge to `RH`

`MoebiusEscapedPairingBoundaryLaw` established that on `HorizonSpace N`, the growing-endpoint
power-saving law `GrowingEndpointEscapedMoebiusLaw θ` (`0 < θ ≤ 1 / 2`) for
`escapedPairing N a b (moebiusSource N) (flatSource N) = ∑_{(N - b)/a < j ≤ N} μ(j) / j` is
unconditionally equivalent to `zetaZeroAbscissa ≤ 1 - θ`, and across all `θ ∈ (0, 1 / 2)` is
equivalent to `RiemannHypothesis`.

This module establishes the **unconditional quantitative decay laws** on the escaped Möbius
boundary and completes the **cross-route unification** linking the escaped biarithmetic boundary,
the coupled damped Möbius receiver, the centred prime band, short-window prime/Möbius dispersion,
`RenormalizedBiarithmeticGeometry`'s dyadic Hecke-defect RG amplification and Carathéodory
half-plane, and the coalescent pair-correlation threshold `θ(λ) = (λ - 1) / (2λ)`:

1. **Unconditional Uniform Growing-Endpoint Vanishing vs. Flat Trans-Horizon Persistence
   (`escapedPairing_moebiusSource_uniform_tendsto_zero`, `escapedPairing_flatSource_dyadic_ge_half`):**
   While `escapedPairing N 2 0 (flatSource N) (flatSource N) ≥ 1 / 2` for every `N ≥ 1`, the
   escaped Möbius pairing vanishes **uniformly across all horizons `N`, multipliers `a : ℕ+`, and
   shifts `b ≤ N`** as the escaped endpoint `(N - b) / a → ∞`, with zero loss in the octave ratio
   `N / ((N - b) / a)`.

2. **Unconditional Quantitative Vinogradov–Korobov Escaped Möbius Bound
   (`exists_abs_escapedPairing_moebiusSource_le_vk_rate`,
   `exists_abs_moebiusHarmonicTail_le_vk_rate`):**
   Splitting the Vinogradov–Korobov Mertens exponent `-(κ σ(j) / 24)` into a monotone endpoint
   factor `-(κ σ(M) / 48)` (`M = (N - b) / a`) and a summable `(1/24) √(log j)` harmonic tail proves
   that there exist explicit `C > 0` and `M₀ ≥ 1` such that for **all** `N, a, b` with `b ≤ N` and
   `M₀ ≤ (N - b) / a`,
   `|escapedPairing N a b (moebiusSource N) (flatSource N)|
     ≤ C · exp(-vkKappa · vkScale ((N - b) / a) / 48)`.
   Specializing to `a = 1, b = N - M` and sending `N → ∞` yields the same unconditional
   Vinogradov–Korobov bound for the infinite harmonic tail `|∑_{n ≤ M} μ(n) / n|`.

3. **Pointwise Four-Way Escaped/Receiver/Abscissa Equivalence and Seven-Way Quasi-RH Unification
   (`escapedMoebius_receiver_abscissa_tfae`, `quasiRH_crossRoute_seven_way_tfae`,
   `riemannHypothesis_iff_forall_coalescent_escapedMoebiusLaw`):**
   Combining `receiverDampingRate_eq_zetaZeroAbscissa_sub_half` with
   `growingEndpointEscapedMoebiusLaw_tfae` equates `GrowingEndpointEscapedMoebiusLaw θ`,
   `DyadicEscapedMoebiusLaw θ`, `receiverDampingRate ≤ 1 / 2 - θ`, and
   `zetaZeroAbscissa ≤ 1 - θ` pointwise at every `θ ∈ (0, 1 / 2]`, unifies all seven Quasi-RH
   criteria across the corpus, and parameterizes the full path to `RiemannHypothesis` along the
   coalescent resonance family `θ(λ) = (λ - 1) / (2λ) → 1 / 2⁻` (`λ → ∞`), with First-Blood
   landmark `θ(4 / 3) = 1 / 8` (`zetaZeroAbscissa ≤ 7 / 8`, `receiverDampingRate ≤ 3 / 8`).

4. **Lossless RG Hecke-Defect Transfer and Seven-Way `RBG` Pointwise Unification
   (`heckeDefect_le_depthKernel_of_dyadic_exp_rate`, `escapedMoebius_rbg_seven_way_tfae`):**
   For every single `CompactTest` `f`, asymptotic dyadic growth `O_ε(exp((2φ + ε) 2^k L))` transfers
   losslessly via `RBG.heckeDefect_dyadic_ge` to the exact finite-scale strip cap
   `heckeDefect f L ≤ depthKernel L φ * mass f`; for every `θ ∈ (0, 1 / 2]`, this closes a 7-way
   pointwise equivalence uniting `GrowingEndpointEscapedMoebiusLaw θ` with the exact `heckeDefect`
   strip cap, the dyadic RG growth rate `O_ε(exp((1 - 2θ + ε) 2^k))`, and the Carathéodory
   half-plane positivity `∀ s, 1 - θ < s.re → 0 ≤ (logDeriv xi s).re`.
-/

open Finset Filter Topology RHTower RHTower.Sieve
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.SelectivePositivityAndThresholdLaws
open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

set_option autoImplicit false

/-! ## §1. Unconditional Uniform Escaped Möbius Vanishing vs. Flat Trans-Horizon Persistence -/

/-- Exact harmonic-sum evaluation of `escapedPairing N a b (flatSource N) (flatSource N)`. -/
theorem escapedPairing_flatSource_self (N : ℕ) (a : ℕ+) (b : ℕ) :
    escapedPairing N a b (flatSource N) (flatSource N) =
      ∑ j ∈ Ioc ((N - b) / a) N, (1 : ℝ) / j := by
  rw [flatSource, escapedPairing_cellSource]
  refine sum_congr rfl fun j hj => ?_
  have hj0 : j ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hj).1)
  exact inv_sqrt_mul_inv_sqrt hj0

/-- **Unconditional Flat Trans-Horizon Persistence (`a = 2, b = 0`):**
For every `N ≥ 1`, `1 / 2 ≤ escapedPairing N 2 0 (flatSource N) (flatSource N)`. -/
theorem escapedPairing_flatSource_dyadic_ge_half {N : ℕ} (hN : 1 ≤ N) :
    (1 / 2 : ℝ) ≤ escapedPairing N 2 0 (flatSource N) (flatSource N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [escapedPairing_flatSource_self]
  simp only [Nat.sub_zero, PNat.val_ofNat]
  calc (1 / 2 : ℝ)
      ≤ ((N - N / 2 : ℕ) : ℝ) / (N : ℝ) := by
        rw [div_le_div_iff₀ (by norm_num) hN0]
        have hhalf : N ≤ 2 * (N - N / 2) := by omega
        have hcast : (N : ℝ) ≤ 2 * ((N - N / 2 : ℕ) : ℝ) := by exact_mod_cast hhalf
        linarith
    _ = ∑ _j ∈ Ioc (N / 2) N, (1 : ℝ) / (N : ℝ) := by
        rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one_div]
    _ ≤ ∑ j ∈ Ioc (N / 2) N, (1 : ℝ) / (j : ℝ) := by
        refine sum_le_sum fun j hj => ?_
        have hj_pos : (0 : ℝ) < j := by
          exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hj).1)
        exact one_div_le_one_div_of_le hj_pos (by exact_mod_cast (mem_Ioc.mp hj).2)

/-- Exact difference identity expressing `escapedPairing N a b (moebiusSource N) (flatSource N)` via
`moebiusHarmonicTail` at `(N - b) / a` and `N`. -/
theorem escapedPairing_moebiusSource_eq_moebiusHarmonicTail_sub
    (N : ℕ) (a : ℕ+) (b : ℕ) :
    escapedPairing N a b (moebiusSource N) (flatSource N) =
      moebiusHarmonicTail ((N - b) / a) - moebiusHarmonicTail N := by
  have hMN : (N - b) / a ≤ N := (Nat.div_le_self _ _).trans (Nat.sub_le N b)
  rw [escapedPairing_moebiusSource, sum_Ioc_moebius_div _ _ hMN]
  unfold moebiusHarmonicTail
  ring

/-- **Unconditional Uniform Growing-Endpoint Vanishing of `escapedPairing` on `moebiusSource`:**
For every `ε > 0`, there exists `M₀ : ℕ` such that for **every** horizon `N : ℕ`, multiplier
`a : ℕ+`, and shift `b ≤ N` with `M₀ ≤ (N - b) / a`,
`|escapedPairing N a b (moebiusSource N) (flatSource N)| ≤ ε`. -/
theorem escapedPairing_moebiusSource_uniform_tendsto_zero :
    ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ (N : ℕ) (a : ℕ+) (b : ℕ),
      b ≤ N → M₀ ≤ (N - b) / a →
        |escapedPairing N a b (moebiusSource N) (flatSource N)| ≤ ε := by
  intro ε hε
  have htend : Tendsto moebiusHarmonicTail atTop (𝓝 0) := by
    unfold moebiusHarmonicTail
    simpa using RHTower.tendsto_sum_range_succ_moebius_div.neg
  obtain ⟨M₀, hM₀⟩ := Metric.tendsto_atTop.mp htend (ε / 2) (half_pos hε)
  refine ⟨M₀, fun N a b _ hM => ?_⟩
  have hMN : (N - b) / a ≤ N := (Nat.div_le_self _ _).trans (Nat.sub_le N b)
  have h1 : |moebiusHarmonicTail ((N - b) / a)| ≤ ε / 2 := by
    have hd := hM₀ ((N - b) / a) hM
    rw [Real.dist_eq, sub_zero] at hd
    exact hd.le
  have h2 : |moebiusHarmonicTail N| ≤ ε / 2 := by
    have hd := hM₀ N (le_trans hM hMN)
    rw [Real.dist_eq, sub_zero] at hd
    exact hd.le
  rw [escapedPairing_moebiusSource_eq_moebiusHarmonicTail_sub N a b]
  calc |moebiusHarmonicTail ((N - b) / a) - moebiusHarmonicTail N|
      ≤ |moebiusHarmonicTail ((N - b) / a)| + |moebiusHarmonicTail N| := abs_sub _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := add_halves ε

/-! ## §2. Unconditional Quantitative Vinogradov–Korobov Escaped Möbius Bound -/

/-- **Unconditional Quantitative Vinogradov–Korobov Escaped Möbius Bound:**
There exist `C > 0` and `M₀ : ℕ` (`1 ≤ M₀`) such that for **every** horizon `N : ℕ`, multiplier
`a : ℕ+`, and shift `b ≤ N` with `M₀ ≤ (N - b) / a`,
`|escapedPairing N a b (moebiusSource N) (flatSource N)|
  ≤ C · exp(-vkKappa · vkScale (((N - b) / a : ℕ)) / 48)`,
uniformly across arbitrarily large octave ratios `N / ((N - b) / a)`. -/
theorem exists_abs_escapedPairing_moebiusSource_le_vk_rate :
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∀ (N : ℕ) (a : ℕ+) (b : ℕ),
      b ≤ N → M₀ ≤ (N - b) / a →
        |escapedPairing N a b (moebiusSource N) (flatSource N)| ≤
          C * Real.exp (-(vkKappa * vkScale (((N - b) / a : ℕ) : ℝ) / 48)) := by
  obtain ⟨B, hB, hev_mert⟩ := exists_abs_sum_moebius_le_vk_rate
  have hev := tendsto_natCast_atTop_atTop.eventually
    ((hev_mert.and (eventually_vk_conditions one_pos 0)).and
      (eventually_ge_atTop (Real.exp (Real.exp (25 / 9)))))
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp hev
  set M₀ : ℕ := max M₁ 1
  have hsum := GaloisForLFunctions.HTGeometry.summable_exp_neg_sqrt_log_div
    (show (0 : ℝ) < 1 / 24 by norm_num)
  set S : ℝ := ∑' m : ℕ, Real.exp (-(1 / 24 * Real.sqrt (Real.log m))) / (m : ℝ)
  have hS0 : 0 ≤ S := tsum_nonneg fun m =>
    div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg m)
  set C : ℝ := 1 + B * (2 + S)
  have hC0 : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC0, M₀, le_max_right _ _, fun N a b hbN hM₀ => ?_⟩
  set M : ℕ := (N - b) / a
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM₀
  have hMM₁ : M₁ ≤ M := le_trans (le_max_left _ _) hM₀
  have hMN : M ≤ N := (Nat.div_le_self _ _).trans (Nat.sub_le N b)
  rw [escapedPairing_moebiusSource, sum_Ioc_moebius_div_eq_mertens_abel hMN]
  split_ifs with heq
  · rw [abs_zero]
    positivity
  · have hN1 : 1 ≤ N := le_trans hM1 hMN
    have hM0_pos : (0 : ℝ) < M := by exact_mod_cast hM1
    have hN0_pos : (0 : ℝ) < N := by exact_mod_cast hN1
    obtain ⟨⟨_, _⟩, hM_exp⟩ := hM₁ M hMM₁
    have hpoint : ∀ j : ℕ, M ≤ j →
        |∑ k ∈ Icc 1 j, moebiusReal k| ≤
          B * (j : ℝ) * Real.exp (-(vkKappa * vkScale (j : ℝ) / 24)) ∧
        2 * Real.sqrt (Real.log (j : ℝ)) ≤ vkKappa * vkScale (j : ℝ) ∧
        vkScale (M : ℝ) ≤ vkScale (j : ℝ) := by
      intro j hj
      obtain ⟨⟨hj_mert, hj_vk⟩, _⟩ := hM₁ j (le_trans hMM₁ hj)
      rw [Nat.floor_natCast, sum_range_moebius_eq_sum_Icc_moebiusReal] at hj_mert
      obtain ⟨-, -, -, -, hsq, -⟩ := hj_vk
      rw [log_vkHeight] at hsq
      exact ⟨hj_mert, hsq, vkScale_le_vkScale hM_exp (by exact_mod_cast hj)⟩
    have hκ : 0 < vkKappa := vkKappa_pos
    have hbN_bound : |(∑ k ∈ Icc 1 N, moebiusReal k) / (N : ℝ)| ≤
        B * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) := by
      obtain ⟨hNm, hNsq, hNmono⟩ := hpoint N hMN
      have hgN_nonneg : 0 ≤ vkKappa * vkScale (N : ℝ) :=
        le_trans (by positivity) hNsq
      have hMN_scale : vkKappa * vkScale (M : ℝ) ≤ vkKappa * vkScale (N : ℝ) :=
        mul_le_mul_of_nonneg_left hNmono hκ.le
      have hexp_le : Real.exp (-(vkKappa * vkScale (N : ℝ) / 24)) ≤
          Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) :=
        Real.exp_le_exp.mpr (by linarith)
      rw [abs_div, abs_of_pos hN0_pos]
      calc |∑ k ∈ Icc 1 N, moebiusReal k| / (N : ℝ)
          ≤ (B * (N : ℝ) * Real.exp (-(vkKappa * vkScale (N : ℝ) / 24))) / (N : ℝ) :=
            div_le_div_of_nonneg_right hNm hN0_pos.le
        _ = B * Real.exp (-(vkKappa * vkScale (N : ℝ) / 24)) := by
            field_simp [hN0_pos.ne']
        _ ≤ B * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) :=
            mul_le_mul_of_nonneg_left hexp_le hB
    have hbM_bound : |(∑ k ∈ Icc 1 M, moebiusReal k) / ((M : ℝ) + 1)| ≤
        B * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) := by
      obtain ⟨hMm, hMsq, _⟩ := hpoint M le_rfl
      have hgM_nonneg : 0 ≤ vkKappa * vkScale (M : ℝ) :=
        le_trans (by positivity) hMsq
      have hexp_le : Real.exp (-(vkKappa * vkScale (M : ℝ) / 24)) ≤
          Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) :=
        Real.exp_le_exp.mpr (by linarith)
      have hMp : 0 < (M : ℝ) + 1 := by positivity
      rw [abs_div, abs_of_pos hMp]
      calc |∑ k ∈ Icc 1 M, moebiusReal k| / ((M : ℝ) + 1)
          ≤ |∑ k ∈ Icc 1 M, moebiusReal k| / (M : ℝ) :=
            div_le_div_of_nonneg_left (abs_nonneg _) hM0_pos (by linarith)
        _ ≤ (B * (M : ℝ) * Real.exp (-(vkKappa * vkScale (M : ℝ) / 24))) / (M : ℝ) :=
            div_le_div_of_nonneg_right hMm hM0_pos.le
        _ = B * Real.exp (-(vkKappa * vkScale (M : ℝ) / 24)) := by
            field_simp [hM0_pos.ne']
        _ ≤ B * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) :=
            mul_le_mul_of_nonneg_left hexp_le hB
    have hint_bound : |∑ j ∈ Ico (M + 1) N,
          (∑ k ∈ Icc 1 j, moebiusReal k) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))| ≤
        B * S * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) := by
      have hterm : ∀ j ∈ Ico (M + 1) N,
          |(∑ k ∈ Icc 1 j, moebiusReal k) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))| ≤
            B * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) *
              (Real.exp (-(1 / 24 * Real.sqrt (Real.log (j : ℝ)))) / (j : ℝ)) := by
        intro j hj
        have hjM : M ≤ j := le_trans (Nat.le_succ M) (mem_Ico.mp hj).1
        have hj1 : 1 ≤ j := le_trans hM1 hjM
        have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
        have hjp : 0 < (j : ℝ) + 1 := by positivity
        obtain ⟨hjm, hjsq, hjmono⟩ := hpoint j hjM
        have hdiff_nn : 0 ≤ 1 / (j : ℝ) - 1 / ((j : ℝ) + 1) :=
          sub_nonneg.mpr (one_div_le_one_div_of_le hj0 (by linarith))
        have hdiff_le : 1 / (j : ℝ) - 1 / ((j : ℝ) + 1) ≤ 1 / (j : ℝ) ^ 2 := by
          have hfrac : 1 / (j : ℝ) - 1 / ((j : ℝ) + 1) = 1 / ((j : ℝ) * ((j : ℝ) + 1)) := by
            field_simp; ring
          rw [hfrac, sq]
          exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
        have hexp_split : Real.exp (-(vkKappa * vkScale (j : ℝ) / 24)) ≤
            Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) *
              Real.exp (-(1 / 24 * Real.sqrt (Real.log (j : ℝ)))) := by
          rw [← Real.exp_add]
          have h1 : vkKappa * vkScale (M : ℝ) ≤ vkKappa * vkScale (j : ℝ) :=
            mul_le_mul_of_nonneg_left hjmono hκ.le
          exact Real.exp_le_exp.mpr (by linarith)
        rw [abs_mul, abs_of_nonneg hdiff_nn]
        calc |∑ k ∈ Icc 1 j, moebiusReal k| * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))
            ≤ (B * (j : ℝ) * Real.exp (-(vkKappa * vkScale (j : ℝ) / 24))) * (1 / (j : ℝ) ^ 2) :=
              mul_le_mul hjm hdiff_le hdiff_nn (by positivity)
          _ = B * (Real.exp (-(vkKappa * vkScale (j : ℝ) / 24)) / (j : ℝ)) := by
              field_simp [hj0.ne']
          _ ≤ B * ((Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) *
                Real.exp (-(1 / 24 * Real.sqrt (Real.log (j : ℝ))))) / (j : ℝ)) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hexp_split hj0.le) hB
          _ = B * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) *
                (Real.exp (-(1 / 24 * Real.sqrt (Real.log (j : ℝ)))) / (j : ℝ)) := by ring
      calc |∑ j ∈ Ico (M + 1) N,
              (∑ k ∈ Icc 1 j, moebiusReal k) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))|
          ≤ ∑ j ∈ Ico (M + 1) N,
              |(∑ k ∈ Icc 1 j, moebiusReal k) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))| :=
            abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ Ico (M + 1) N, B * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) *
              (Real.exp (-(1 / 24 * Real.sqrt (Real.log (j : ℝ)))) / (j : ℝ)) :=
            sum_le_sum hterm
          _ = B * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) *
              ∑ j ∈ Ico (M + 1) N,
                Real.exp (-(1 / 24 * Real.sqrt (Real.log (j : ℝ)))) / (j : ℝ) := by
            rw [← mul_sum]
          _ ≤ B * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) * S :=
            mul_le_mul_of_nonneg_left
              (hsum.sum_le_tsum _ fun m _ =>
                div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg m))
              (by positivity)
          _ = B * S * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) := by ring
    calc |(∑ k ∈ Icc 1 N, moebiusReal k) / (N : ℝ) -
            (∑ k ∈ Icc 1 M, moebiusReal k) / ((M : ℝ) + 1) +
            ∑ j ∈ Ico (M + 1) N,
              (∑ k ∈ Icc 1 j, moebiusReal k) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))|
        ≤ |(∑ k ∈ Icc 1 N, moebiusReal k) / (N : ℝ)| +
            |(∑ k ∈ Icc 1 M, moebiusReal k) / ((M : ℝ) + 1)| +
            |∑ j ∈ Ico (M + 1) N,
              (∑ k ∈ Icc 1 j, moebiusReal k) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))| :=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ B * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) +
            B * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) +
            B * S * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) :=
          add_le_add (add_le_add hbN_bound hbM_bound) hint_bound
      _ ≤ C * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) := by
          dsimp [C]
          have hexp_pos : 0 < Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) := Real.exp_pos _
          nlinarith

/-- **Unconditional Vinogradov–Korobov Bound on `moebiusHarmonicTail` (`-∑_{n ≤ M} μ(n) / n`):**
Obtained directly from `exists_abs_escapedPairing_moebiusSource_le_vk_rate` by specializing to
`a = 1, b = N - M` and letting `N → ∞`. -/
theorem exists_abs_moebiusHarmonicTail_le_vk_rate :
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      |moebiusHarmonicTail M| ≤ C * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) := by
  obtain ⟨C, hC, M₀, hM₀1, hbd⟩ := exists_abs_escapedPairing_moebiusSource_le_vk_rate
  refine ⟨C, hC, M₀, hM₀1, fun M hM => ?_⟩
  have htend : Tendsto
      (fun N : ℕ => |moebiusHarmonicTail M - moebiusHarmonicTail N|)
      atTop (𝓝 |moebiusHarmonicTail M|) := by
    have h0 : Tendsto moebiusHarmonicTail atTop (𝓝 0) := by
      unfold moebiusHarmonicTail
      simpa using RHTower.tendsto_sum_range_succ_moebius_div.neg
    simpa [sub_zero] using (tendsto_const_nhds.sub h0).abs
  refine le_of_tendsto htend (eventually_ge_atTop M |>.mono fun N hMN => ?_)
  have hbN : N - M ≤ N := Nat.sub_le N M
  have hdiv : (N - (N - M)) / (1 : ℕ+) = M := by
    simp only [PNat.val_ofNat, Nat.div_one]
    omega
  have hesc := hbd N 1 (N - M) hbN (by rwa [hdiv])
  rw [escapedPairing_moebiusSource_eq_moebiusHarmonicTail_sub N 1 (N - M), hdiv] at hesc
  exact hesc

/-! ## §3. Pointwise Escaped/Receiver/Abscissa Equivalence, Seven-Way Quasi-RH, and `θ(λ) → 1 / 2⁻` -/

/-- **Pointwise Four-Way Escaped-Boundary / Receiver-Damping / Zero-Abscissa Equivalence:**
For every `θ ∈ (0, 1 / 2]`, the following four laws are unconditionally equivalent:
1. `GrowingEndpointEscapedMoebiusLaw θ` (uniform `O_ε(((N - b)/a)^{-θ+ε})` across all `a, b`);
2. `DyadicEscapedMoebiusLaw θ` (single-multiplier `a = 2, b = 0` power saving `O_ε(N^{-θ+ε})`);
3. `receiverDampingRate ≤ 1 / 2 - θ` (coupled damped Möbius receiver rate);
4. `zetaZeroAbscissa ≤ 1 - θ` (zero-free half-plane `Re ρ ≤ 1 - θ`). -/
theorem escapedMoebius_receiver_abscissa_tfae {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ ≤ 1 / 2) :
    List.TFAE [GrowingEndpointEscapedMoebiusLaw θ,
      DyadicEscapedMoebiusLaw θ,
      receiverDampingRate ≤ 1 / 2 - θ,
      zetaZeroAbscissa ≤ 1 - θ] := by
  have hbase := growingEndpointEscapedMoebiusLaw_tfae hθ0 hθ2
  tfae_have 1 ↔ 2 := hbase.out 0 1
  tfae_have 2 ↔ 4 := hbase.out 1 2
  tfae_have 3 ↔ 4 := by
    rw [receiverDampingRate_eq_zetaZeroAbscissa_sub_half]
    constructor <;> intro h <;> linarith
  tfae_finish

/-- **Seven-Way Cross-Route Unification of the Quasi-Riemann Hypothesis (`Θ < 1`):**
Unites the first power-saving rung across five programmes (`SPTL`, `ACG`, `BVI`, `ACT`, `RHTower`):
1. `∃ θ ∈ (0, 1/2], GrowingEndpointEscapedMoebiusLaw θ`;
2. `∃ θ ∈ (0, 1/2], DyadicEscapedMoebiusLaw θ`;
3. `CentredPrimeBandPowerSaving` (balanced prime statistic power saving near the diagonal);
4. `PrimePowerWindowSaving` (short-window prime mean-square power saving);
5. `MoebiusPowerWindowSaving` (short-window Möbius mean-square power saving);
6. `receiverDampingRate < 1 / 2` (coupled damped Möbius receiver below half damping);
7. `zetaZeroAbscissa < 1` (zero-free strip). -/
theorem quasiRH_crossRoute_seven_way_tfae :
    List.TFAE [∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧ GrowingEndpointEscapedMoebiusLaw θ,
      ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧ DyadicEscapedMoebiusLaw θ,
      CentredPrimeBandPowerSaving,
      PrimePowerWindowSaving,
      MoebiusPowerWindowSaving,
      receiverDampingRate < 1 / 2,
      zetaZeroAbscissa < 1] := by
  tfae_have 1 → 2 := by
    rintro ⟨θ, hθ0, hθ2, hgrow⟩
    exact ⟨θ, hθ0, hθ2, ((growingEndpointEscapedMoebiusLaw_tfae hθ0 hθ2).out 0 1).mp hgrow⟩
  tfae_have 2 → 7 := by
    rintro ⟨θ, hθ0, hθ2, hdyad⟩
    have habs := ((growingEndpointEscapedMoebiusLaw_tfae hθ0 hθ2).out 1 2).mp hdyad
    linarith
  tfae_have 7 → 1 := by
    intro hlt
    set θ : ℝ := min (1 / 2) ((1 - zetaZeroAbscissa) / 2)
    have hθ0 : 0 < θ := lt_min (by norm_num) (by linarith)
    have hθ2 : θ ≤ 1 / 2 := min_le_left _ _
    have habs : zetaZeroAbscissa ≤ 1 - θ := by
      have : θ ≤ (1 - zetaZeroAbscissa) / 2 := min_le_right _ _
      linarith
    exact ⟨θ, hθ0, hθ2, ((growingEndpointEscapedMoebiusLaw_tfae hθ0 hθ2).out 2 0).mp habs⟩
  tfae_have 3 ↔ 7 := centredPrimeBandPowerSaving_iff
  tfae_have 4 ↔ 7 := primePowerWindowSaving_iff
  tfae_have 5 ↔ 7 := moebiusPowerWindowSaving_iff
  tfae_have 6 ↔ 7 := receiverDampingRate_lt_half_iff
  tfae_finish

/-- **Coalescent Resonance Threshold Exponent `θ(λ) = (λ - 1) / (2λ)` (`λ > 1`):**
Maps each trans-threshold pair-correlation aperture `λ > 1` (`κ = λ`) to the exact zero-free strip
exponent `θ(λ) ∈ (0, 1 / 2)` at which off-critical zero contributions `x^{β₀}` stay strictly below
the square-root coalescent barrier (`(1 - θ(λ)) λ ≤ (1 + λ) / 2`, i.e., `β₀ ≤ (1 + 1/λ) / 2`). -/
def coalescentResonanceExponent (lam : ℝ) : ℝ :=
  (lam - 1) / (2 * lam)

/-- Landmark evaluations and monotonicity of `coalescentResonanceExponent`:
- `θ(4 / 3) = 1 / 8` (First-Blood pair-correlation threshold `β₀ ≤ 7 / 8`);
- `θ(5 / 4) = 1 / 10` (`β₀ ≤ 9 / 10`);
- `0 < θ(λ) < 1 / 2` for every `λ > 1`, with `θ(λ) → 1 / 2` as `λ → ∞`. -/
theorem coalescentResonanceExponent_properties :
    coalescentResonanceExponent (4 / 3) = 1 / 8 ∧
    coalescentResonanceExponent (5 / 4) = 1 / 10 ∧
    (∀ lam : ℝ, 1 < lam →
      0 < coalescentResonanceExponent lam ∧ coalescentResonanceExponent lam < 1 / 2) ∧
    Tendsto coalescentResonanceExponent atTop (𝓝 (1 / 2)) := by
  refine ⟨by unfold coalescentResonanceExponent; norm_num,
    by unfold coalescentResonanceExponent; norm_num,
    fun lam hlam => ?_, ?_⟩
  · unfold coalescentResonanceExponent
    constructor
    · exact div_pos (by linarith) (by linarith)
    · rw [div_lt_iff₀ (by linarith : 0 < 2 * lam)]
      linarith
  · have hlim : Tendsto (fun lam : ℝ => (1 / 2 : ℝ) - (1 / 2 : ℝ) * lam⁻¹) atTop (𝓝 (1 / 2)) := by
      simpa using tendsto_const_nhds.sub (tendsto_inv_atTop_zero.const_mul (1 / 2 : ℝ))
    refine hlim.congr' (eventually_gt_atTop (0 : ℝ) |>.mono fun lam hlam => ?_)
    unfold coalescentResonanceExponent
    field_simp [hlam.ne']

/-- **First-Blood Landmark Equivalence (`λ = 4 / 3`, `θ = 1 / 8`):**
At the pair-correlation aperture `λ = 4 / 3`, `GrowingEndpointEscapedMoebiusLaw (1 / 8)` is
unconditionally equivalent to `receiverDampingRate ≤ 3 / 8` and to `zetaZeroAbscissa ≤ 7 / 8`. -/
theorem firstBlood_fourThirds_escapedMoebius_iff :
    (GrowingEndpointEscapedMoebiusLaw (coalescentResonanceExponent (4 / 3)) ↔
      receiverDampingRate ≤ 3 / 8) ∧
    (GrowingEndpointEscapedMoebiusLaw (coalescentResonanceExponent (4 / 3)) ↔
      zetaZeroAbscissa ≤ 7 / 8) := by
  rw [coalescentResonanceExponent_properties.1]
  have ht := escapedMoebius_receiver_abscissa_tfae (θ := 1 / 8) (by norm_num) (by norm_num)
  have h1 : GrowingEndpointEscapedMoebiusLaw (1 / 8) ↔ receiverDampingRate ≤ 1 / 2 - 1 / 8 :=
    ht.out 0 2
  have h2 : GrowingEndpointEscapedMoebiusLaw (1 / 8) ↔ zetaZeroAbscissa ≤ 1 - 1 / 8 :=
    ht.out 0 3
  norm_num at h1 h2
  exact ⟨h1, h2⟩

/-- **Full-Target Master Equivalence (`θ(λ) → 1 / 2⁻ ⟺ RH`):**
`RiemannHypothesis` holds if and only if `GrowingEndpointEscapedMoebiusLaw (coalescentResonanceExponent lam)`
holds for every `lam > 1` (equivalently, `receiverDampingRate = 0`). -/
theorem riemannHypothesis_iff_forall_coalescent_escapedMoebiusLaw :
    (RiemannHypothesis ↔
      ∀ lam : ℝ, 1 < lam → GrowingEndpointEscapedMoebiusLaw (coalescentResonanceExponent lam)) ∧
    (RiemannHypothesis ↔ receiverDampingRate = 0) := by
  refine ⟨?_, riemannHypothesis_iff_receiverDampingRate_eq_zero⟩
  rw [riemannHypothesis_iff_forall_lt_half_growingEndpointEscapedMoebiusLaw]
  constructor
  · intro hall lam hlam
    obtain ⟨h0, hhalf⟩ := coalescentResonanceExponent_properties.2.2.1 lam hlam
    exact hall _ h0 hhalf
  · intro hcoal θ hθ0 hθ2
    set lam : ℝ := 1 / (1 - 2 * θ)
    have hden : 0 < 1 - 2 * θ := by linarith
    have hlam1 : 1 < lam := by
      dsimp [lam]
      rw [one_lt_div hden]
      linarith
    have heq : coalescentResonanceExponent lam = θ := by
      dsimp [coalescentResonanceExponent, lam]
      field_simp [hden.ne']
      ring
    exact heq ▸ hcoal lam hlam1

/-! ## §4. Lossless RG Hecke-Defect Transfer and Seven-Way `RBG` Pointwise Unification -/

section RBGBridge

open Zeta23
open GaloisForLFunctions.ConjugateDiagonalGeometry
open GaloisForLFunctions.RenormalizedBiarithmeticGeometry

/-- **Lossless Asymptotic-to-Exact RG Transfer for `heckeDefect`:**
For any single `CompactTest` `f`, nonnegative depth `φ ≥ 0`, and nonnegative scale `L ≥ 0`, if the
dyadic Hecke defects satisfy `heckeDefect f (2^k L) = O_ε(exp((2φ + ε) 2^k L))` for every `ε > 0`,
then iterated nonlinear amplification (`RBG.heckeDefect_dyadic_ge`) forces the exact finite-scale
strip cap `heckeDefect f L ≤ depthKernel L φ * mass f` with unit leading constant and zero `ε`-loss.
At `φ = 0`, this recovers `RBG.heckeDefect_eq_zero_of_dyadic_subexp`. -/
theorem heckeDefect_le_depthKernel_of_dyadic_exp_rate
    (f : CompactTest) {φ L : ℝ} (hφ : 0 ≤ φ) (hL : 0 ≤ L)
    (hrate : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ k : ℕ,
      heckeDefect f (2 ^ k * L) ≤ C * Real.exp ((2 * φ + ε) * (2 ^ k * L))) :
    heckeDefect f L ≤ depthKernel L φ * mass f := by
  by_contra hlt
  rw [not_le] at hlt
  have hdk_nn : 0 ≤ depthKernel L φ * mass f := mul_nonneg (depthKernel_nonneg L φ) (mass_nonneg f)
  have hE_pos : 0 < heckeDefect f L := lt_of_le_of_lt hdk_nn hlt
  have hL_pos : 0 < L := by
    rcases hL.lt_or_eq with hpos | rfl
    · exact hpos
    · have h0 := heckeDefect_le_mass_cosh f 0
      rw [Real.cosh_zero, show (2 : ℝ) * 1 - 2 = 0 by norm_num, mul_zero] at h0
      linarith
  have hD : 0 < mass f := mass_pos_of_heckeDefect_pos hE_pos
  set ψ₀ : ℝ := 2 * φ * L
  have hψ₀_nn : 0 ≤ ψ₀ := by positivity
  have hlt_cosh : mass f * (2 * Real.cosh ψ₀ - 2) < heckeDefect f L := by
    have heq : depthKernel L φ * mass f = mass f * (2 * Real.cosh ψ₀ - 2) := by
      unfold depthKernel ψ₀; ring
    linarith
  have hc : Tendsto (fun ψ : ℝ => mass f * (2 * Real.cosh ψ - 2)) (𝓝[>] ψ₀)
      (𝓝 (mass f * (2 * Real.cosh ψ₀ - 2))) :=
    ((continuous_const.mul ((continuous_const.mul Real.continuous_cosh).sub
      continuous_const)).tendsto ψ₀).mono_left nhdsWithin_le_nhds
  obtain ⟨ψ, hψ_lt, hψ_gt⟩ := ((hc.eventually (gt_mem_nhds hlt_cosh)).and self_mem_nhdsWithin).exists
  have hψ_gt' : ψ₀ < ψ := hψ_gt
  set δ : ℝ := ψ - ψ₀
  have hδ : 0 < δ := by dsimp [δ]; linarith
  set ε : ℝ := δ / (2 * L)
  have hε : 0 < ε := div_pos hδ (by positivity)
  obtain ⟨C, hC⟩ := hrate ε hε
  set M : ℝ := (|C| + 2 * mass f) / mass f + 1
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * M / δ)
  have hk2 : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self.le
  have hyM : M < Real.exp (δ / 2 * 2 ^ k) := by
    have h1 : M < δ / 2 * 2 ^ k := by
      rw [div_lt_iff₀ hδ] at hk
      nlinarith
    linarith [Real.add_one_le_exp (δ / 2 * 2 ^ k)]
  set E₀ : ℝ := Real.exp ((ψ₀ + δ / 2) * 2 ^ k)
  have hE₀_pos : 0 < E₀ := Real.exp_pos _
  have hE₀_ge1 : 1 ≤ E₀ := Real.one_le_exp (by positivity)
  have hexp_arg : (2 * φ + ε) * (2 ^ k * L) = (ψ₀ + δ / 2) * 2 ^ k := by
    dsimp [ψ₀, ε, δ]
    field_simp [hL_pos.ne']
  have hup : heckeDefect f (2 ^ k * L) ≤ |C| * E₀ := by
    have hk_up := hC k
    rw [hexp_arg] at hk_up
    exact hk_up.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hE₀_pos.le)
  have hlow := heckeDefect_dyadic_ge f L ψ hψ_lt.le k
  have hcosh : E₀ * Real.exp (δ / 2 * 2 ^ k) ≤ 2 * Real.cosh (2 ^ k * ψ) := by
    have hsplit : 2 ^ k * ψ = (ψ₀ + δ / 2) * 2 ^ k + δ / 2 * 2 ^ k := by dsimp [δ]; ring
    have heq : E₀ * Real.exp (δ / 2 * 2 ^ k) = Real.exp (2 ^ k * ψ) := by
      dsimp [E₀]; rw [← Real.exp_add, hsplit]
    rw [heq, Real.cosh_eq]
    linarith [Real.exp_pos (-(2 ^ k * ψ))]
  have hcomb : mass f * (E₀ * Real.exp (δ / 2 * 2 ^ k) - 2) ≤ |C| * E₀ :=
    (mul_le_mul_of_nonneg_left (by linarith) hD.le).trans (hlow.trans hup)
  have hM_mul : (|C| + 2 * mass f + mass f) * E₀ < mass f * E₀ * Real.exp (δ / 2 * 2 ^ k) := by
    have hM' : |C| + 2 * mass f + mass f < mass f * Real.exp (δ / 2 * 2 ^ k) := by
      calc |C| + 2 * mass f + mass f
          = (|C| + 2 * mass f) / mass f * mass f + mass f := by rw [div_mul_cancel₀ _ hD.ne']
        _ = M * mass f := by dsimp [M]; ring
        _ < Real.exp (δ / 2 * 2 ^ k) * mass f := mul_lt_mul_of_pos_right hyM hD
        _ = mass f * Real.exp (δ / 2 * 2 ^ k) := mul_comm _ _
    nlinarith
  nlinarith [abs_nonneg C]

/-- Under `zetaZeroAbscissa ≤ 1 - θ` (`0 < θ ≤ 1 / 2`), every nontrivial zero `ρ` satisfies
`|zetaDepth ρ| ≤ 1 / 2 - θ`. -/
theorem abs_zetaDepth_le_of_zetaZeroAbscissa_le {θ : ℝ} (_hθ0 : 0 < θ) (_hθ2 : θ ≤ 1 / 2)
    (habs : zetaZeroAbscissa ≤ 1 - θ) (ρ : zetaZeroConfig.carrier) :
    |zetaDepth ρ| ≤ 1 / 2 - θ := by
  have hρ : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hre_hi : (ρ : ℂ).re ≤ 1 - θ := (RHTower.re_le_zetaZeroAbscissa hρ.1).trans habs
  have hrefl : riemannZeta (1 - (ρ : ℂ)) = 0 :=
    RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hρ.1 hρ.2.1 hρ.2.2
  have hre_lo : 1 - (ρ : ℂ).re ≤ 1 - θ := by
    have h := (RHTower.re_le_zetaZeroAbscissa hrefl).trans habs
    simpa using h
  rw [zetaDepth, abs_le]
  constructor <;> linarith

/-- **Zero-Abscissa Strip Cap on `heckeDefect`:**
If `zetaZeroAbscissa ≤ 1 - θ` (`0 < θ ≤ 1 / 2`), then for every `f : CompactTest` and `L : ℝ`,
`heckeDefect f L ≤ depthKernel L (1 / 2 - θ) * mass f`. -/
theorem heckeDefect_le_of_zetaZeroAbscissa_le {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ ≤ 1 / 2)
    (habs : zetaZeroAbscissa ≤ 1 - θ) (f : CompactTest) (L : ℝ) :
    heckeDefect f L ≤ depthKernel L (1 / 2 - θ) * mass f := by
  change heckeDefect f L ≤ depthKernel L (1 / 2 - θ) * ∑' ρ, zetaWeight f ρ
  rw [← tsum_mul_left]
  refine (summable_heckeDefect f L).tsum_le_tsum (fun ρ => ?_)
    ((summable_zetaWeight f).mul_left (depthKernel L (1 / 2 - θ)))
  change zetaWeight f ρ * depthKernel L (zetaDepth ρ) ≤
    depthKernel L (1 / 2 - θ) * zetaWeight f ρ
  rw [mul_comm (depthKernel L (1 / 2 - θ))]
  have hbd : |zetaDepth ρ| ≤ |1 / 2 - θ| := by
    rw [abs_of_nonneg (by linarith)]
    exact abs_zetaDepth_le_of_zetaZeroAbscissa_le hθ0 hθ2 habs ρ
  exact mul_le_mul_of_nonneg_left (depthKernel_mono_depth L hbd) (zetaWeight_nonneg f ρ)

/-- An exact finite-scale strip cap `heckeDefect f L ≤ depthKernel L (1 / 2 - θ) * mass f` implies
the dyadic exponential rate `O_ε(exp((1 - 2θ + ε) 2^k))`. -/
theorem dyadic_heckeDefect_rate_of_heckeDefect_le {θ : ℝ} (_hθ0 : 0 < θ) (hθ2 : θ ≤ 1 / 2)
    (hcap : ∀ (f : CompactTest) (L : ℝ), heckeDefect f L ≤ depthKernel L (1 / 2 - θ) * mass f)
    (f : CompactTest) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ k : ℕ, heckeDefect f (2 ^ k) ≤ C * Real.exp ((1 - 2 * θ + ε) * 2 ^ k) := by
  refine ⟨2 * mass f, fun k => ?_⟩
  have h1 := hcap f (2 ^ k)
  set x : ℝ := 2 * (1 / 2 - θ) * (2 ^ k : ℝ)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hdk : depthKernel (2 ^ k) (1 / 2 - θ) ≤ 2 * Real.exp x := by
    unfold depthKernel
    change 2 * Real.cosh x - 2 ≤ 2 * Real.exp x
    rw [Real.cosh_eq]
    have hneg : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hpos : 0 < Real.exp x := Real.exp_pos x
    linarith
  have hexp_le : Real.exp x ≤ Real.exp ((1 - 2 * θ + ε) * 2 ^ k) := by
    apply Real.exp_le_exp.mpr
    dsimp [x]
    have hk0 : (0 : ℝ) < 2 ^ k := by positivity
    nlinarith
  calc heckeDefect f (2 ^ k)
      ≤ depthKernel (2 ^ k) (1 / 2 - θ) * mass f := h1
    _ ≤ (2 * Real.exp x) * mass f := mul_le_mul_of_nonneg_right hdk (mass_nonneg f)
    _ ≤ (2 * Real.exp ((1 - 2 * θ + ε) * 2 ^ k)) * mass f :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_le (by norm_num)) (mass_nonneg f)
    _ = (2 * mass f) * Real.exp ((1 - 2 * θ + ε) * 2 ^ k) := by ring

/-- **Converse Zero-Abscissa Extraction from `heckeDefect`:**
If `heckeDefect f L ≤ depthKernel L (1 / 2 - θ) * mass f` holds across compact `C²` tests and scales
`L`, then `zetaZeroAbscissa ≤ 1 - θ`. -/
theorem zetaZeroAbscissa_le_of_heckeDefect_le {θ : ℝ} (_hθ0 : 0 < θ) (hθ2 : θ ≤ 1 / 2)
    (hcap : ∀ (f : CompactTest) (L : ℝ), heckeDefect f L ≤ depthKernel L (1 / 2 - θ) * mass f) :
    zetaZeroAbscissa ≤ 1 - θ := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨s, hs0, hs1, hsre⟩ := RHTower.exists_zetaZero_mem_openStrip_lt_re hlt
  have hs_pos : 0 < s.re := by linarith
  have hmem : s ∈ zetaZeroConfig.carrier := ⟨hs0, hs_pos, hs1⟩
  obtain ⟨⟨⟨g, hgreal⟩, _⟩, hg0, -⟩ :=
    GaloisForLFunctions.ArithmeticCorrespondencePositivity.exists_mem_realTestsAt_mellinAt_ne_zero
      one_pos s s
  let f : CompactTest := ⟨fun u => (g u : ℂ),
    Complex.ofRealCLM.contDiff.comp hgreal.1, hgreal.2.comp_left Complex.ofReal_zero⟩
  let ρ₀ : zetaZeroConfig.carrier := ⟨s, hmem⟩
  have htr : GaloisForLFunctions.ArithmeticPolarization.tr f.1 s ≠ 0 := by
    rw [GaloisForLFunctions.ArithmeticPolarization.tr_cx_eq_mellinAt]
    exact hg0
  have hm1 : (1 : ℝ) ≤ zetaZeroConfig.mult s := by
    exact_mod_cast zetaZeroConfig.one_le_mult s hmem
  have hw_pos : 0 < zetaWeight f ρ₀ :=
    mul_pos (by linarith) (Complex.normSq_pos.mpr htr)
  set b : ℝ := s.re - 1 / 2
  have hb_gt : 1 / 2 - θ < b := by dsimp [b]; linarith
  have hb_pos : 0 < b := by linarith
  have htail_ge : zetaWeight f ρ₀ ≤ depthTail f b := by
    have hterm : (if |b| ≤ |zetaDepth ρ₀| then zetaWeight f ρ₀ else 0) = zetaWeight f ρ₀ :=
      if_pos (le_of_eq (rfl : |b| = |zetaDepth ρ₀|))
    rw [depthTail, ← hterm]
    exact (summable_depthTail f b).le_tsum ρ₀ fun ρ _ => by
      split_ifs
      · exact zetaWeight_nonneg f ρ
      · exact le_rfl
  set δ : ℝ := 2 * b - (1 - 2 * θ)
  have hδ : 0 < δ := by dsimp [δ]; linarith
  set M : ℝ := (2 * mass f + 2 * zetaWeight f ρ₀) / zetaWeight f ρ₀ + 1
  obtain ⟨k, hk⟩ := exists_nat_gt (M / δ + 1)
  set L : ℝ := (k : ℝ)
  have hL_pos : 0 < L := by
    have : 0 ≤ M / δ := div_nonneg (by dsimp [M]; positivity) hδ.le
    dsimp [L]; linarith
  have hexpM : M < Real.exp (δ * L) := by
    have h1 : M < δ * L := by
      have hk' : M / δ < L := by dsimp [L]; linarith
      rwa [div_lt_iff₀ hδ] at hk'
    linarith [Real.add_one_le_exp (δ * L)]
  have hlow1 : depthKernel L b * zetaWeight f ρ₀ ≤ heckeDefect f L :=
    (mul_le_mul_of_nonneg_left htail_ge (depthKernel_nonneg L b)).trans
      (depthKernel_mul_tail_le f L b)
  have hdk_lo : Real.exp (2 * b * L) - 2 ≤ depthKernel L b := by
    unfold depthKernel
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-(2 * b * L))]
  have hdk_hi : depthKernel L (1 / 2 - θ) ≤ 2 * Real.exp ((1 - 2 * θ) * L) := by
    unfold depthKernel
    rw [show 2 * (1 / 2 - θ) * L = (1 - 2 * θ) * L by ring, Real.cosh_eq]
    have hneg : Real.exp (-((1 - 2 * θ) * L)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith [Real.exp_pos ((1 - 2 * θ) * L)]
  set E₀ : ℝ := Real.exp ((1 - 2 * θ) * L)
  have hE₀_ge1 : 1 ≤ E₀ := Real.one_le_exp (by nlinarith)
  have hprod : Real.exp (2 * b * L) = E₀ * Real.exp (δ * L) := by
    dsimp [E₀, δ]
    rw [← Real.exp_add]
    congr 1; ring
  have hineq : (E₀ * Real.exp (δ * L) - 2) * zetaWeight f ρ₀ ≤ 2 * E₀ * mass f := by
    calc (E₀ * Real.exp (δ * L) - 2) * zetaWeight f ρ₀
        = (Real.exp (2 * b * L) - 2) * zetaWeight f ρ₀ := by rw [hprod]
      _ ≤ depthKernel L b * zetaWeight f ρ₀ := mul_le_mul_of_nonneg_right hdk_lo hw_pos.le
      _ ≤ heckeDefect f L := hlow1
      _ ≤ depthKernel L (1 / 2 - θ) * mass f := hcap f L
      _ ≤ (2 * E₀) * mass f := mul_le_mul_of_nonneg_right hdk_hi (mass_nonneg f)
      _ = 2 * E₀ * mass f := by ring
  have hM_mul : 2 * mass f + 2 * zetaWeight f ρ₀ + zetaWeight f ρ₀ <
      zetaWeight f ρ₀ * Real.exp (δ * L) := by
    calc 2 * mass f + 2 * zetaWeight f ρ₀ + zetaWeight f ρ₀
        = (2 * mass f + 2 * zetaWeight f ρ₀) / zetaWeight f ρ₀ * zetaWeight f ρ₀ +
            zetaWeight f ρ₀ := by rw [div_mul_cancel₀ _ hw_pos.ne']
      _ = M * zetaWeight f ρ₀ := by dsimp [M]; ring
      _ < Real.exp (δ * L) * zetaWeight f ρ₀ := mul_lt_mul_of_pos_right hexpM hw_pos
      _ = zetaWeight f ρ₀ * Real.exp (δ * L) := mul_comm _ _
  nlinarith [mass_nonneg f]

/-- **Forward `RBG` Carathéodory Half-Plane Law:**
Under `zetaZeroAbscissa ≤ 1 - θ` (`0 < θ ≤ 1 / 2`), every `s : ℂ` in the open half-plane
`1 - θ < s.re` lies strictly right of `1 / 2`, avoids all zeros of `xi`, and lies outside every
`RBG` critical disc `InCriticalDisc q s`, hence satisfies `0 ≤ (logDeriv xi s).re`. -/
theorem re_logDeriv_xi_nonneg_of_zetaZeroAbscissa_le {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ ≤ 1 / 2)
    (habs : zetaZeroAbscissa ≤ 1 - θ) {s : ℂ} (hs : 1 - θ < s.re) :
    0 ≤ (logDeriv RHTower.xi s).re := by
  have hs_half : 1 / 2 < s.re := by linarith
  have hxi : RHTower.xi s ≠ 0 := by
    intro hz
    have hmem := RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_of_xi_eq_zero hz
    have hle := (RHTower.re_le_zetaZeroAbscissa hmem.1).trans habs
    linarith
  refine re_logDeriv_xi_nonneg_of_outside_discs hs_half hxi fun q hdisc => ?_
  unfold InCriticalDisc at hdisc
  have hq_mem := RHTower.CrossRouteReceiverBridges.xiZeroCopy_mem_zetaZeroConfig_carrier q
  have hq_abs : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 - θ :=
    abs_zetaDepth_le_of_zetaZeroAbscissa_le hθ0 hθ2 habs ⟨(q.1 : ℂ), hq_mem⟩
  have hq_sq : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (1 / 2 - θ) ^ 2 := by
    rw [← sq_abs ((q.1 : ℂ).re - 1 / 2)]
    exact pow_le_pow_left₀ (abs_nonneg _) hq_abs 2
  have hs_gt : 1 / 2 - θ < s.re - 1 / 2 := by linarith
  have hs_sq : (1 / 2 - θ) ^ 2 < (s.re - 1 / 2) ^ 2 :=
    pow_lt_pow_left₀ hs_gt (by linarith) (by norm_num)
  nlinarith [sq_nonneg (s.im - (q.1 : ℂ).im)]

/-- **Converse `RBG` Carathéodory Half-Plane Law via Residue Quantization:**
If `0 ≤ (logDeriv xi s).re` throughout the open half-plane `1 - θ < s.re` (`0 < θ ≤ 1 / 2`), then
`zetaZeroAbscissa ≤ 1 - θ`: any zero `ρ` of `xi` with `1 - θ < ρ.re` has positive integer
meromorphic order `m ≥ 1`, so approaching `ρ` from the left along `s = ρ - r` (`r → 0⁺`) forces
`(s - ρ) * logDeriv xi s → m` and hence `(logDeriv xi (ρ - r)).re < 0` inside `1 - θ < Re s`. -/
theorem zetaZeroAbscissa_le_of_re_logDeriv_xi_nonneg {θ : ℝ} (_hθ0 : 0 < θ) (hθ2 : θ ≤ 1 / 2)
    (hcar : ∀ s : ℂ, 1 - θ < s.re → 0 ≤ (logDeriv RHTower.xi s).re) :
    zetaZeroAbscissa ≤ 1 - θ := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨ρ, hρ0, hρ1, hρre⟩ := RHTower.exists_zetaZero_mem_openStrip_lt_re hlt
  have hρ_pos : 0 < ρ.re := by linarith
  have hxi0 : RHTower.xi ρ = 0 :=
    (RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp
      ⟨hρ0, hρ_pos, hρ1⟩).1
  have hana : AnalyticAt ℂ RHTower.xi ρ := RHTower.xi_analyticOnNhd_univ ρ (Set.mem_univ ρ)
  set m : ℕ := (analyticOrderAt RHTower.xi ρ).toNat
  have hm_ne : m ≠ 0 := RHTower.xi_order_toNat_ne_zero hxi0
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm_ne
  have ha_ord : analyticOrderAt RHTower.xi ρ = (m : ℕ∞) :=
    (ENat.coe_toNat (RHTower.xi_orderAt_ne_top ρ)).symm
  have hm_ord : meromorphicOrderAt RHTower.xi ρ = ((m : ℤ) : WithTop ℤ) := by
    rw [hana.meromorphicOrderAt_eq, ha_ord]
    rfl
  have hres := GaloisForLFunctions.HTGeometry.logDeriv_residue_of_meromorphicOrder
    hana.meromorphicAt hm_ord
  have hray : Tendsto (fun r : ℝ => ρ - (r : ℂ)) (𝓝[>] 0) (𝓝[≠] ρ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous (fun r : ℝ => ρ - (r : ℂ)) :=
        continuous_const.sub Complex.continuous_ofReal
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : (r : ℝ) ≠ 0 := (Set.mem_Ioi.mp hr).ne'
      intro heq
      exact hr0 (Complex.ofReal_eq_zero.mp (sub_eq_self.mp (Set.mem_singleton_iff.mp heq)))
  have hlim_re : Tendsto (fun r : ℝ => (((ρ - (r : ℂ)) - ρ) * logDeriv RHTower.xi (ρ - (r : ℂ))).re)
      (𝓝[>] 0) (𝓝 (m : ℝ)) := by
    have hcomp := (Complex.continuous_re.tendsto ((m : ℤ) : ℂ)).comp (hres.comp hray)
    rw [Complex.intCast_re, Int.cast_natCast] at hcomp
    exact hcomp
  have hev_pos := hlim_re.eventually (Ioi_mem_nhds hm_pos)
  have hev_small : ∀ᶠ r : ℝ in 𝓝[>] 0, r < ρ.re - (1 - θ) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds (by linarith : (0 : ℝ) < ρ.re - (1 - θ)))
  obtain ⟨r, ⟨hr_res, hr_small⟩, hr_gt0⟩ :=
    ((hev_pos.and hev_small).and self_mem_nhdsWithin).exists
  have hr0 : 0 < r := hr_gt0
  have hs_re : 1 - θ < (ρ - (r : ℂ)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hnonneg := hcar (ρ - (r : ℂ)) hs_re
  have hval : (((ρ - (r : ℂ)) - ρ) * logDeriv RHTower.xi (ρ - (r : ℂ))).re =
      -r * (logDeriv RHTower.xi (ρ - (r : ℂ))).re := by
    have hsub : (ρ - (r : ℂ)) - ρ = -(r : ℂ) := by ring
    rw [hsub, neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, neg_mul]
  have hr_res' : 0 < -r * (logDeriv RHTower.xi (ρ - (r : ℂ))).re := hval ▸ Set.mem_Ioi.mp hr_res
  nlinarith

/-- **Seven-Way Cross-Programme Pointwise Unification (`SPTL` / `ACG` / `BVI` / `RHTower` / `CDG` / `RBG`):**
For every `θ ∈ (0, 1 / 2]`, the following seven statements are unconditionally equivalent:
1. `GrowingEndpointEscapedMoebiusLaw θ` (`SPTL` uniform biarithmetic escaped Möbius power saving);
2. `DyadicEscapedMoebiusLaw θ` (`ACG` / `BVI` dyadic escaped Möbius power saving);
3. `receiverDampingRate ≤ 1 / 2 - θ` (`THIM` / `SPTL` coupled damped Möbius receiver rate);
4. `zetaZeroAbscissa ≤ 1 - θ` (`RHTower` zero-free half-plane);
5. `∀ f L, heckeDefect f L ≤ depthKernel L (1 / 2 - θ) * mass f` (`CDG` / `RBG` exact strip cap);
6. `∀ f ε > 0, ∃ C, ∀ k, heckeDefect f (2^k) ≤ C exp((1 - 2θ + ε) 2^k)` (`RBG` dyadic RG rate);
7. `∀ s, 1 - θ < s.re → 0 ≤ (logDeriv xi s).re` (`RBG` Carathéodory half-plane positivity). -/
theorem escapedMoebius_rbg_seven_way_tfae {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ ≤ 1 / 2) :
    List.TFAE [GrowingEndpointEscapedMoebiusLaw θ,
      DyadicEscapedMoebiusLaw θ,
      receiverDampingRate ≤ 1 / 2 - θ,
      zetaZeroAbscissa ≤ 1 - θ,
      ∀ (f : CompactTest) (L : ℝ), heckeDefect f L ≤ depthKernel L (1 / 2 - θ) * mass f,
      ∀ (f : CompactTest) (ε : ℝ), 0 < ε → ∃ C : ℝ, ∀ k : ℕ,
        heckeDefect f (2 ^ k) ≤ C * Real.exp ((1 - 2 * θ + ε) * 2 ^ k),
      ∀ s : ℂ, 1 - θ < s.re → 0 ≤ (logDeriv RHTower.xi s).re] := by
  have h4 := escapedMoebius_receiver_abscissa_tfae hθ0 hθ2
  tfae_have 1 ↔ 2 := h4.out 0 1
  tfae_have 2 ↔ 4 := h4.out 1 3
  tfae_have 3 ↔ 4 := h4.out 2 3
  tfae_have 4 → 5 := fun habs f L => heckeDefect_le_of_zetaZeroAbscissa_le hθ0 hθ2 habs f L
  tfae_have 5 → 6 := fun hcap f ε hε => dyadic_heckeDefect_rate_of_heckeDefect_le hθ0 hθ2 hcap f ε hε
  tfae_have 6 → 4 := by
    intro hdyad
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨s, hs0, hs1, hsre⟩ := RHTower.exists_zetaZero_mem_openStrip_lt_re hlt
    have hs_pos : 0 < s.re := by linarith
    have hmem : s ∈ zetaZeroConfig.carrier := ⟨hs0, hs_pos, hs1⟩
    obtain ⟨⟨⟨g, hgreal⟩, _⟩, hg0, -⟩ :=
      GaloisForLFunctions.ArithmeticCorrespondencePositivity.exists_mem_realTestsAt_mellinAt_ne_zero
        one_pos s s
    let f : CompactTest := ⟨fun u => (g u : ℂ),
      Complex.ofRealCLM.contDiff.comp hgreal.1, hgreal.2.comp_left Complex.ofReal_zero⟩
    let ρ₀ : zetaZeroConfig.carrier := ⟨s, hmem⟩
    have htr : GaloisForLFunctions.ArithmeticPolarization.tr f.1 s ≠ 0 := by
      rw [GaloisForLFunctions.ArithmeticPolarization.tr_cx_eq_mellinAt]
      exact hg0
    have hm1 : (1 : ℝ) ≤ zetaZeroConfig.mult s := by
      exact_mod_cast zetaZeroConfig.one_le_mult s hmem
    have hw_pos : 0 < zetaWeight f ρ₀ := mul_pos (by linarith) (Complex.normSq_pos.mpr htr)
    set b : ℝ := s.re - 1 / 2
    have hb_gt : 1 / 2 - θ < b := by dsimp [b]; linarith
    set ε : ℝ := b - (1 / 2 - θ)
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨C, hC⟩ := hdyad f ε hε
    have htail_ge : zetaWeight f ρ₀ ≤ depthTail f b := by
      have hterm : (if |b| ≤ |zetaDepth ρ₀| then zetaWeight f ρ₀ else 0) = zetaWeight f ρ₀ :=
        if_pos (le_of_eq (rfl : |b| = |zetaDepth ρ₀|))
      rw [depthTail, ← hterm]
      exact (summable_depthTail f b).le_tsum ρ₀ fun ρ _ => by
        split_ifs
        · exact zetaWeight_nonneg f ρ
        · exact le_rfl
    set M : ℝ := (|C| + 2 * zetaWeight f ρ₀) / zetaWeight f ρ₀ + 1
    obtain ⟨k, hk⟩ := exists_nat_gt (M / ε)
    have hk2 : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self.le
    have hexpM : M < Real.exp (ε * 2 ^ k) := by
      have h1 : M < ε * 2 ^ k := by
        rw [div_lt_iff₀ hε] at hk
        nlinarith
      linarith [Real.add_one_le_exp (ε * 2 ^ k)]
    have hlow : (Real.exp (2 * b * 2 ^ k) - 2) * zetaWeight f ρ₀ ≤ heckeDefect f (2 ^ k) := by
      have hdk : Real.exp (2 * b * 2 ^ k) - 2 ≤ depthKernel (2 ^ k) b := by
        unfold depthKernel; rw [Real.cosh_eq]; linarith [Real.exp_pos (-(2 * b * 2 ^ k))]
      exact (mul_le_mul_of_nonneg_right hdk hw_pos.le).trans
        ((mul_le_mul_of_nonneg_left htail_ge (depthKernel_nonneg _ _)).trans
          (depthKernel_mul_tail_le f (2 ^ k) b))
    set E₀ : ℝ := Real.exp ((1 - 2 * θ + ε) * 2 ^ k)
    have hE₀_pos : 0 < E₀ := Real.exp_pos _
    have hE₀_ge1 : 1 ≤ E₀ := Real.one_le_exp (by dsimp [ε]; nlinarith [show (0 : ℝ) < 2 ^ k by positivity])
    have hup : heckeDefect f (2 ^ k) ≤ |C| * E₀ :=
      (hC k).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hE₀_pos.le)
    have hprod : Real.exp (2 * b * 2 ^ k) = E₀ * Real.exp (ε * 2 ^ k) := by
      dsimp [E₀, ε]; rw [← Real.exp_add]; congr 1; ring
    have hcomb : (E₀ * Real.exp (ε * 2 ^ k) - 2) * zetaWeight f ρ₀ ≤ |C| * E₀ := by
      rw [← hprod]; exact hlow.trans hup
    have hM_mul : |C| + 2 * zetaWeight f ρ₀ + zetaWeight f ρ₀ <
        zetaWeight f ρ₀ * Real.exp (ε * 2 ^ k) := by
      calc |C| + 2 * zetaWeight f ρ₀ + zetaWeight f ρ₀
          = (|C| + 2 * zetaWeight f ρ₀) / zetaWeight f ρ₀ * zetaWeight f ρ₀ +
              zetaWeight f ρ₀ := by rw [div_mul_cancel₀ _ hw_pos.ne']
        _ = M * zetaWeight f ρ₀ := by dsimp [M]; ring
        _ < Real.exp (ε * 2 ^ k) * zetaWeight f ρ₀ := mul_lt_mul_of_pos_right hexpM hw_pos
        _ = zetaWeight f ρ₀ * Real.exp (ε * 2 ^ k) := mul_comm _ _
    nlinarith [abs_nonneg C]
  tfae_have 4 → 7 := fun habs s hs => re_logDeriv_xi_nonneg_of_zetaZeroAbscissa_le hθ0 hθ2 habs hs
  tfae_have 7 → 4 := fun hcar => zetaZeroAbscissa_le_of_re_logDeriv_xi_nonneg hθ0 hθ2 hcar
  tfae_finish

end RBGBridge

end GaloisForLFunctions.BezoutValuationIncidence

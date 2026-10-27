import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.MoebiusEscapedPairingBoundaryLaw
import GaloisForLFunctions.BezoutValuationIncidence.ReceiverBoundedInTheVinogradovKorobovBand
import GaloisForLFunctions.BezoutValuationIncidence.ShortWindowPrimeSavingIsTheQuasiRiemannHypothesis
import GaloisForLFunctions.BezoutValuationIncidence.LittlewoodAdmitsTheReceiverAboveHalfTheZeroAbscissa
import GaloisForLFunctions.BezoutValuationIncidence.TheCentredPrimeBandFromAZeroFreeStrip
import GaloisForLFunctions.RHTower.AdmissionBelowHalfDampingAboveTheZeroWidth

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
and the coalescent pair-correlation threshold `θ(λ) = (λ - 1) / (2λ)`:

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
   factor `-(κ σ(M) / 48)` (`M = (N - b) / a`) and a summable `(1/2) √(log j)` harmonic tail proves
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
-/

open Finset Filter Topology Set RHTower RHTower.Sieve
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
    {N : ℕ} (a : ℕ+) {b : ℕ} (hbN : b ≤ N) :
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
  refine ⟨M₀, fun N a b hbN hM => ?_⟩
  have hMN : (N - b) / a ≤ N := (Nat.div_le_self _ _).trans (Nat.sub_le N b)
  have h1 : |moebiusHarmonicTail ((N - b) / a)| ≤ ε / 2 := by
    have hd := hM₀ ((N - b) / a) hM
    rw [Real.dist_eq, sub_zero] at hd
    exact hd.le
  have h2 : |moebiusHarmonicTail N| ≤ ε / 2 := by
    have hd := hM₀ N (le_trans hM hMN)
    rw [Real.dist_eq, sub_zero] at hd
    exact hd.le
  rw [escapedPairing_moebiusSource_eq_moebiusHarmonicTail_sub a hbN]
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
    (show (0 : ℝ) < 1 / 2 by norm_num)
  set S : ℝ := ∑' m : ℕ, Real.exp (-(1 / 2 * Real.sqrt (Real.log m))) / (m : ℝ)
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
        Real.sqrt (Real.log (j : ℝ)) ≤ vkKappa * vkScale (j : ℝ) / 24 ∧
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
      have hgN_nonneg : 0 ≤ vkKappa * vkScale (N : ℝ) / 24 :=
        le_trans (Real.sqrt_nonneg _) hNsq
      have hexp_le : Real.exp (-(vkKappa * vkScale (N : ℝ) / 24)) ≤
          Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) :=
        Real.exp_le_exp.mpr (by nlinarith)
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
      have hgM_nonneg : 0 ≤ vkKappa * vkScale (M : ℝ) / 24 :=
        le_trans (Real.sqrt_nonneg _) hMsq
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
              (Real.exp (-(1 / 2 * Real.sqrt (Real.log (j : ℝ)))) / (j : ℝ)) := by
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
              Real.exp (-(1 / 2 * Real.sqrt (Real.log (j : ℝ)))) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by nlinarith)
        rw [abs_mul, abs_of_nonneg hdiff_nn]
        calc |∑ k ∈ Icc 1 j, moebiusReal k| * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))
            ≤ (B * (j : ℝ) * Real.exp (-(vkKappa * vkScale (j : ℝ) / 24))) * (1 / (j : ℝ) ^ 2) :=
              mul_le_mul hjm hdiff_le hdiff_nn (by positivity)
          _ = B * (Real.exp (-(vkKappa * vkScale (j : ℝ) / 24)) / (j : ℝ)) := by
              field_simp [hj0.ne']
          _ ≤ B * ((Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) *
                Real.exp (-(1 / 2 * Real.sqrt (Real.log (j : ℝ))))) / (j : ℝ)) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hexp_split hj0.le) hB
          _ = B * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) *
                (Real.exp (-(1 / 2 * Real.sqrt (Real.log (j : ℝ)))) / (j : ℝ)) := by ring
      calc |∑ j ∈ Ico (M + 1) N,
              (∑ k ∈ Icc 1 j, moebiusReal k) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))|
          ≤ ∑ j ∈ Ico (M + 1) N,
              |(∑ k ∈ Icc 1 j, moebiusReal k) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Ico (M + 1) N, B * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) *
              (Real.exp (-(1 / 2 * Real.sqrt (Real.log (j : ℝ)))) / (j : ℝ)) :=
            sum_le_sum hterm
        _ = B * Real.exp (-(vkKappa * vkScale (M : ℝ) / 48)) *
              ∑ j ∈ Ico (M + 1) N,
                Real.exp (-(1 / 2 * Real.sqrt (Real.log (j : ℝ)))) / (j : ℝ) := by
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
  have hesc := hbd N 1 (N - M) hbN (hdiv ▸ hM)
  rw [escapedPairing_moebiusSource_eq_moebiusHarmonicTail_sub 1 hbN, hdiv] at hesc
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
    ring

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

end GaloisForLFunctions.BezoutValuationIncidence

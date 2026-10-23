import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheTwoThirdsConstantIsPairCorrelation
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.BreakingTheCoalescenceBlindSpotAndThreeQuarters
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SpectralSlackConservationAndTheHyperbolicDisplacementThreshold
import GaloisForLFunctions.RHTower.PairCorrelationMixtureWindow
import GaloisForLFunctions.RHTower.ZetaDyadicWindowMomentTwoThirds
import GaloisForLFunctions.RHTower.ZetaOffLineMomentMontgomeryTaylor
import GaloisForLFunctions.RHTower.ThetaTailSimpleCriticalThreshold

/-!
# What a Gram Functional Certifies Without Effectivity: Complete Classification and Corpus-Wide Applications

In Weil's proof over `𝔽_q`, Riemann–Roch supplies an effective auxiliary cycle on `C × C`, forcing
the Castelnuovo–Severi form `W(f, f)` to be positive semidefinite (`scalingSurface_hodgeIndex_iff`).
By the Pontryagin law (`pontryagin_law_curve`), the number of negative squares of `W` is the number
`p` of off-line zero pairs `{ρ, 1 − ρ̄}` (`Re ρ ≠ 1/2`), so effectivity forces `p = 0`.

When Riemann–Roch effectivity is absent (`BezoutEffectivityAndTheBeurlingObstruction`), a Gram
functional observes only the total zero count `N` and the Hermitian evaluation Gram matrix
`Â = P + Q` on a finite window of probe cycles, where `P ⪰ 0` is the critical-line sum of rank at
most `s₁ + s₂` and trace at most `N_on`, and `Q = Q^*` is the off-line pair sum with at most one
positive square per pair (`n₊(Q) ≤ p`).

This module establishes the **complete, unconditional classification** of what a Gram functional
certifies without effectivity across all multiplicity weights `c > 0`, window profiles `v`, and
bandwidths `λ`, and applies the resulting theorems to advance the zero-census, horizontal off-line
moment, and double-exponential uniqueness thresholds in `RHTower`:

1. **Strengthened `c = 2` and `c = 3` Multiplicity-Excess and Off-Line Exclusion Laws
   (`mult_two_with_excess`, `double_triple_offLine_exclusion_law`, `mult_three_with_excess`,
   `exclusion_of_normalized_gram`):**
   For any `ZeroBlockData` configuration `D` with pair representatives `Pr`, let `a₂` be the number
   of double critical-line zeros (`m_z = 2`), `a₃` the number of critical-line zeros of multiplicity
   `m_z ≥ 3`, and `multExcess := N − (s₁ + 2s₂ + 2p) ≥ a₃` the higher-multiplicity excess.
   * At `c = 2`, the rank–trace inequality strengthens to
     `4 tr Â − ‖Â‖_F² − 2N + 2 multExcess ≤ s₁`,
     yielding the exact exclusion law
     `2 a₂ + 5 a₃ + 2 p ≤ 2(s₂ + p) + 3 multExcess ≤ 3N − (4 tr Â − ‖Â‖_F²)`.
     For a normalized Gram matrix (`tr Â ≥ N`, `‖Â‖_F² ≤ κN`), this simultaneously certifies:
     - `s₁ ≥ (2 − κ)N + 2 multExcess ≥ (2 − κ)N + 2 a₃` simple critical-line zeros,
     - `s₂ + p ≤ ((κ − 1)/2)N` (both multiple critical zeros and off-line pairs bounded by
       `((κ − 1)/2)N`),
     - `a₃ ≤ ((κ − 1)/5)N` (critical zeros of multiplicity `≥ 3` penalized at weight `5`, giving
       `a₃ ≤ N/15` at `κ = 4/3`).
   * At `c = 3`, the rank–trace inequality strengthens to
     `6 tr Â − ‖Â‖_F² − 3N + 2 a₃ + p + 3(N − (a₁ + 2a₂ + 3a₃ + 2p)) ≤ 2 N_d`,
     certifying `N_d ≥ ((3 − κ)/2)N + a₃ + p/2` total distinct zeros and the critical-line vs.
     off-line trade-off `2(s₁ + s₂) + 3p ≥ (3 − κ)N + 2a₃`.

2. **Universal Sharpness and Coalescence Indistinguishability Classification
   (`universal_gram_certification_classification`):**
   Because `doubleZeroBlockData s₁ d₂` (`(s₁, s₂, p) = (s₁, d₂, 0)`) and
   `coalescedPairBlockData s₁ d₂` (`(s₁, s₂, p) = (s₁, 0, d₂)`) produce the **exact same** Gram
   matrix `extremalDiag s₁ d₂` and total count `N = s₁ + 2d₂`, every functional of `(Â, N)` has:
   * exact maximum lower bound `(2 − κ)N` on `s₁`, on `s₁ + s₂`, and on `N_on` (uniquely achieved
     by `c = 2`);
   * exact maximum lower bound `((3 − κ)/2)N` on `N_d = s₁ + s₂ + 2p` (achieved by `c = 3`);
   * exact minimum upper bound `((κ − 1)/2)N` on `s₂` and on `p` (achieved by `c = 2`).

3. **Below Pair Correlation (`λ ≤ 1`): Flat-Top Cap `2/3` vs. Variational Profile `HD(1) = 0.6725…`
   (`two_thirds_lt_HD_one`, `HD_one_lt_three_quarters`, `five_sixths_lt_GD_one`,
   `montgomeryTaylor_simpleCritical_dyadic`, `montgomeryTaylor_distinct_dyadic`,
   `offLine_and_multiple_exclusion_dyadic`):**
   * The `2/3` cap at `λ = 1` (`kfun 1 = 4/3`) is the cap for a **flat-top** prime window, not for
     an arbitrary window profile supported below `λ = 1`. Optimizing the scale-free functional
     `cFun λ v` at `v*(s) = cos(√2 λ s)` lowers `κ` from `4/3 = 1.3333…` to
     `1 / cStar 1 ≤ 3319/2500 = 1.3276`, strictly beating `2/3` (`2/3 < 1681/2500 ≤ HD 1`) and
     `5/6` (`5/6 < 4181/5000 ≤ GD 1`) unconditionally on every dyadic window `(T, 2T]` and on
     `(0, T]`.
   * Yet even at the variational optimum `v*_1`, `HD 1 < 3/4` (`HD_one_lt_three_quarters`). Thus no
     window profile supported below `λ = 1` can reach `3/4` without either zero-side spectral slack
     (Route I) or trans-threshold pair correlation `λ > 1` (Route II).

4. **The Two Routes to `3/4` (`κ = 5/4`), Dual Sub-Threshold Ceiling, and Two-Window Mixture
   Optimization (`subthreshold_spectralSlack_dual_ceiling`, `mixQ_at_two_one_third`,
   `mixQ_ge_three_quarters_iff_le_fourteen_fifths`, `mixQ_beats_two_thirds_of_lt`):**
   * **Route I (Zero-Side Spectral Slack):** For `λ ∈ (0, 1)`, the slack-augmented functional is
     bounded above by `min(N₀*(T, 2T), (λ + ε) N(T, 2T))`, refuting `3/4` on `(0, 3/4)` and fixing
     the exact missing slack `(3/4 − H(λ))N(T, 2T)` on `[3/4, 1]` (`1/12` at `λ = 1`).
   * **Route II (Prime-Side Surplus & Two-Window Mixture):** While a single flat-top window beyond
     `λ = 1` under `F(α) ≤ B` reaches `3/4` iff `B ≤ 2`, mixing the bandwidth-`4/3` window with the
     unconditional bandwidth-`1` window (`RHTower.mixQ B ε`) reaches `1513/1944 > 3/4` at `B = 2`
     (`ε = 1/3`), reaches `3/4` iff `B ≤ 117/41 ≈ 2.8537` at `ε = 7/16` (in particular for all
     `B ≤ 14/5 = 2.8`), and strictly beats `2/3` for all `B < 181/18`.

5. **Corpus-Wide Downstream Upgrades in `RHTower`
   (`eventually_dyadicWindowTail_le_selberg_upper_of_proportion`,
   `eventually_dyadicWindowTail_le_sixtySix_thousandths`,
   `eventually_dyadicWindowTail_le_fiftySeven_thousandths_of_primeSurplusFourThirds`,
   `ae_eq_zero_of_doubleExp_simpleCritical_of_proportion`,
   `ae_eq_zero_of_doubleExp_simpleCritical_montgomeryTaylor`,
   `ae_eq_zero_of_doubleExp_simpleCritical_ge_three`):**
   * **Dyadic Window Off-Line Moment (`ZetaDyadicWindowMomentTwoThirds` upgrade):** Proves the
     general proportion transfer `4π windowTail 0 (T+1) (2T−1) ≤ (log c_R − (1 + p)R + η)T` for any
     dyadic simple-critical density `p ∈ (0, 1]`. Unconditionally via `HD 1 ≥ 1681/2500`, this
     improves the dyadic window horizontal off-line moment from `(67/1000)T` down to `(66/1000)T`;
     under `PrimeSurplusFourThirds` (`p = 3/4`), it improves the coefficient to `(7/4)R` and the
     dyadic moment to `(57/1000)T`, and the cumulative moment to `(57/1000)V`.
   * **Real-Divisor-Only Double-Exponential Uniqueness (`ThetaTailSimpleCriticalThreshold` upgrade):**
     Proves that a cumulative simple-critical density `p ∈ (0, 1]` forces `u = 0` a.e. for every
     even `|u(x)| ≤ C exp(−a e^{b|x|})` vanishing at the simple critical zeros whenever `b > 2/p`.
     Unconditionally via `HD 1 ≥ 1681/2500`, this lowers the uniqueness threshold from `b > 3` down
     to `b > 2 / HD 1` (and `b > 5000/1681 = 2.9744… < 3`), resolving the previously open boundary
     case `b = 3` (`b ≥ 3`) unconditionally; under `PrimeSurplusFourThirds`, the threshold drops to
     `b > 8/3`.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology Matrix Finset
open scoped BigOperators ComplexOrder

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open Zeta23 Zeta23.ZeroSide Zeta23.ZeroSide.RankTraceMult _root_.RHTower

/-! ## 1. Strengthened `c = 2` and `c = 3` Multiplicity-Excess and Exclusion Laws -/

section ZeroBlockDataLaws

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- The higher-multiplicity excess `N − (s₁ + 2s₂ + 2p) = ∑_{z ∈ S₂} (m_z − 2) + 2 ∑_{ρ ∈ R} (m_ρ − 1)`
of a zero-block configuration, measuring how much the total multiplicity exceeds the minimal
configuration of simple critical zeros, double critical zeros, and simple off-line pairs. -/
def multExcess (D : ZeroBlockData ι d) (Pr : D.PairReps) : ℕ :=
  D.Ncount - (D.s₁ + 2 * D.s₂ + 2 * Pr.p)

/-- Exact additive decomposition of `Ncount` into `s₁ + 2s₂ + 2p` and `multExcess`. -/
theorem Ncount_eq_s1_add_two_s2_add_two_p_add_multExcess
    (D : ZeroBlockData ι d) (Pr : D.PairReps) :
    (D.Ncount : ℝ) = (D.s₁ : ℝ) + 2 * (D.s₂ : ℝ) + 2 * (Pr.p : ℝ) + (multExcess D Pr : ℝ) := by
  have hle := D.s₁_add_two_s₂_add_two_p_le_Ncount Pr
  have hnat : D.Ncount = (D.s₁ + 2 * D.s₂ + 2 * Pr.p) + multExcess D Pr :=
    (Nat.add_sub_of_le hle).symm
  exact_mod_cast hnat

/-- Every critical-line zero of multiplicity `m_z ≥ 3` contributes at least `1` to `multExcess`:
`#{z ∈ onLine : m_z ≥ 3} ≤ multExcess D Pr`. -/
theorem card_ge_three_le_multExcess (D : ZeroBlockData ι d) (Pr : D.PairReps) :
    (D.onLine.filter (fun z => 3 ≤ D.m z)).card ≤ multExcess D Pr := by
  have hs1 := D.card_onLine_m_eq_one
  have hs2 := D.card_two_add_card_ge_three
  have hNon := D.Non_ge_weighted
  have hN := D.Non_add_two_p_le_Ncount Pr
  have hreal : ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) +
      ((D.s₁ : ℝ) + 2 * (D.s₂ : ℝ) + 2 * (Pr.p : ℝ)) ≤ (D.Ncount : ℝ) := by
    have hs1' : ((D.onLine.filter (fun z => D.m z = 1)).card : ℝ) = D.s₁ := by exact_mod_cast hs1
    have hs2' : ((D.onLine.filter (fun z => D.m z = 2)).card : ℝ) +
        ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) = D.s₂ := by exact_mod_cast hs2
    have hN' : (D.Non : ℝ) + 2 * (Pr.p : ℝ) ≤ D.Ncount := by exact_mod_cast hN
    linarith
  have hnat : (D.onLine.filter (fun z => 3 ≤ D.m z)).card +
      (D.s₁ + 2 * D.s₂ + 2 * Pr.p) ≤ D.Ncount := by exact_mod_cast hreal
  unfold multExcess
  omega

/-- The raw `c = 2` multiplicity-aware rank–trace inequality before subtracting `2N`:
`4 tr(blockP c + blockQ c) − ‖blockP c + blockQ c‖_F² ≤ 3 s₁ + 4 s₂ + 4 p`. -/
theorem four_rtrace_sub_frobSq_le (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {c : ℝ} (hc : 0 < c) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) ≤ c) :
    4 * RHLinalg.rtrace (D.blockP c + D.blockQ c) - RHLinalg.frobSq (D.blockP c + D.blockQ c) ≤
      3 * (D.s₁ : ℝ) + 4 * (D.s₂ : ℝ) + 4 * (Pr.p : ℝ) := by
  classical
  have hR := rank_trace_mult_k_le (𝕜 := ℂ) (fun z => D.mhat_nonneg z) (D.vhat c)
    (D.xsq_vhat_le hc hPois) (D.blockQ_isHermitian c) (D.posIndex_blockQ_le Pr hc)
    (c := 2) (by norm_num)
  rw [← D.blockP_eq_Pmat hc] at hR
  have hk : ∑ z : D.onLine, kc 2 (D.mhat z) = 3 * (D.s₁ : ℝ) + 4 * (D.s₂ : ℝ) := by
    have := sum_kc_two_nat (fun z : D.onLine => D.m z) (fun z => D.one_le_m z)
    simp only [ZeroBlockData.mhat] at this ⊢
    rw [this, D.card_sub_filter (fun n => n = 1), D.card_sub_filter (fun n => 2 ≤ n),
      D.card_onLine_m_eq_one]
    have h2 : (D.onLine.filter (fun z => 2 ≤ D.m z)).card = D.s₂ := by
      unfold ZeroBlockData.s₂ ZeroBlockData.S₂ ZeroBlockData.onLine
      rw [Finset.filter_filter]
    rw [h2]
  rw [hk] at hR
  norm_num at hR
  linarith

/-- **Strengthened `c = 2` Rank–Trace Inequality with Multiplicity Excess (`mult_two_with_excess`).**
Subtracting `2N` from `4 tr Â − ‖Â‖_F² ≤ 3 s₁ + 4 s₂ + 4 p` retains the exact penalty
`2 multExcess = 2(N − (s₁ + 2s₂ + 2p))`:
`4 tr Â − ‖Â‖_F² − 2N + 2 multExcess ≤ s₁`. -/
theorem mult_two_with_excess (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {c : ℝ} (hc : 0 < c) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) ≤ c) :
    4 * RHLinalg.rtrace (D.blockP c + D.blockQ c) - RHLinalg.frobSq (D.blockP c + D.blockQ c) -
      2 * (D.Ncount : ℝ) + 2 * (multExcess D Pr : ℝ) ≤ (D.s₁ : ℝ) := by
  have hR := four_rtrace_sub_frobSq_le D Pr hc hPois
  have hN := Ncount_eq_s1_add_two_s2_add_two_p_add_multExcess D Pr
  linarith

/-- **Triple-Zero Penalty in the `c = 2` Rank–Trace Bound.**
Every critical-line zero of multiplicity `m_z ≥ 3` tightens the `c = 2` simple-zero bound by `2`:
`4 tr Â − ‖Â‖_F² − 2N + 2 #{z ∈ onLine : m_z ≥ 3} ≤ s₁`. -/
theorem mult_two_with_triple_penalty (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {c : ℝ} (hc : 0 < c) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) ≤ c) :
    4 * RHLinalg.rtrace (D.blockP c + D.blockQ c) - RHLinalg.frobSq (D.blockP c + D.blockQ c) -
      2 * (D.Ncount : ℝ) + 2 * ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) ≤ (D.s₁ : ℝ) := by
  have h1 := mult_two_with_excess D Pr hc hPois
  have h2 : ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) ≤ (multExcess D Pr : ℝ) := by
    exact_mod_cast card_ge_three_le_multExcess D Pr
  linarith

/-- **Multiple-Critical and Off-Line Exclusion Law (`c = 2`).**
Eliminating `s₁` between `4 tr Â − ‖Â‖_F² ≤ 3 s₁ + 4 s₂ + 4 p` and
`N = s₁ + 2 s₂ + 2 p + multExcess` yields the exact exclusion inequality
`2(s₂ + p) + 3 multExcess ≤ 3N − (4 tr Â − ‖Â‖_F²)`. -/
theorem multiplicity_and_offLine_exclusion_law (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {c : ℝ} (hc : 0 < c) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) ≤ c) :
    2 * ((D.s₂ : ℝ) + (Pr.p : ℝ)) + 3 * (multExcess D Pr : ℝ) ≤
      3 * (D.Ncount : ℝ) -
        (4 * RHLinalg.rtrace (D.blockP c + D.blockQ c) -
          RHLinalg.frobSq (D.blockP c + D.blockQ c)) := by
  have hR := four_rtrace_sub_frobSq_le D Pr hc hPois
  have hN := Ncount_eq_s1_add_two_s2_add_two_p_add_multExcess D Pr
  linarith

/-- **Weighted Double, Triple-or-Higher, and Off-Line Exclusion Law (`2 a₂ + 5 a₃ + 2 p`).**
Each double critical-line zero (`m_z = 2`) and each off-line pair costs `2`, while each
critical-line zero of multiplicity `m_z ≥ 3` costs `5`, against `3N − (4 tr Â − ‖Â‖_F²)`. -/
theorem double_triple_offLine_exclusion_law (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {c : ℝ} (hc : 0 < c) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) ≤ c) :
    2 * ((D.onLine.filter (fun z => D.m z = 2)).card : ℝ) +
      5 * ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) +
      2 * (Pr.p : ℝ) ≤
      3 * (D.Ncount : ℝ) -
        (4 * RHLinalg.rtrace (D.blockP c + D.blockQ c) -
          RHLinalg.frobSq (D.blockP c + D.blockQ c)) := by
  have hexcl := multiplicity_and_offLine_exclusion_law D Pr hc hPois
  have hs2 : ((D.onLine.filter (fun z => D.m z = 2)).card : ℝ) +
      ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) = D.s₂ := by
    exact_mod_cast D.card_two_add_card_ge_three
  have ha3 : ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) ≤ (multExcess D Pr : ℝ) := by
    exact_mod_cast card_ge_three_le_multExcess D Pr
  linarith

/-- The raw `c = 3` multiplicity-aware rank–trace inequality before subtracting `3N`:
`6 tr(blockP c + blockQ c) − ‖blockP c + blockQ c‖_F² ≤ 5 a₁ + 8 a₂ + 9 a₃ + 9 p`. -/
theorem six_rtrace_sub_frobSq_le (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {c : ℝ} (hc : 0 < c) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) ≤ c) :
    6 * RHLinalg.rtrace (D.blockP c + D.blockQ c) - RHLinalg.frobSq (D.blockP c + D.blockQ c) ≤
      5 * (D.s₁ : ℝ) +
        8 * ((D.onLine.filter (fun z => D.m z = 2)).card : ℝ) +
        9 * ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) +
        9 * (Pr.p : ℝ) := by
  classical
  have hR := rank_trace_mult_k_le (𝕜 := ℂ) (fun z => D.mhat_nonneg z) (D.vhat c)
    (D.xsq_vhat_le hc hPois) (D.blockQ_isHermitian c) (D.posIndex_blockQ_le Pr hc)
    (c := 3) (by norm_num)
  rw [← D.blockP_eq_Pmat hc] at hR
  have hk : ∑ z : D.onLine, kc 3 (D.mhat z) =
      5 * (D.s₁ : ℝ) +
        8 * ((D.onLine.filter (fun z => D.m z = 2)).card : ℝ) +
        9 * ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) := by
    have := sum_kc_three_nat (fun z : D.onLine => D.m z) (fun z => D.one_le_m z)
    simp only [ZeroBlockData.mhat] at this ⊢
    rw [this, D.card_sub_filter (fun n => n = 1), D.card_sub_filter (fun n => n = 2),
      D.card_sub_filter (fun n => 3 ≤ n), D.card_onLine_m_eq_one]
  rw [hk] at hR
  norm_num at hR
  linarith

/-- **Strengthened `c = 3` Distinct-Zero Rank–Trace Law (`mult_three_with_excess`).**
The `c = 3` rank–trace inequality retains the positive penalties `2 a₃ + p`:
`6 tr Â − ‖Â‖_F² − 3N + 2 a₃ + p ≤ 2 N_d`, where `N_d = Fintype.card ι = s₁ + s₂ + 2p` is the
number of distinct zeros, and `6 tr Â − ‖Â‖_F² − 3N + 2 a₃ ≤ 2(s₁ + s₂) + 3p`. -/
theorem mult_three_with_excess (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {c : ℝ} (hc : 0 < c) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) ≤ c) :
    6 * RHLinalg.rtrace (D.blockP c + D.blockQ c) - RHLinalg.frobSq (D.blockP c + D.blockQ c) -
        3 * (D.Ncount : ℝ) + 2 * ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) +
        (Pr.p : ℝ) ≤ 2 * (Fintype.card ι : ℝ) ∧
      6 * RHLinalg.rtrace (D.blockP c + D.blockQ c) - RHLinalg.frobSq (D.blockP c + D.blockQ c) -
        3 * (D.Ncount : ℝ) + 2 * ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) ≤
        2 * ((D.s₁ : ℝ) + (D.s₂ : ℝ)) + 3 * (Pr.p : ℝ) := by
  have hR := six_rtrace_sub_frobSq_le D Pr hc hPois
  have hs1 := D.card_onLine_m_eq_one
  have hs2 : ((D.onLine.filter (fun z => D.m z = 2)).card : ℝ) +
      ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) = D.s₂ := by
    exact_mod_cast D.card_two_add_card_ge_three
  have hNon := D.Non_ge_weighted
  have hs1' : ((D.onLine.filter (fun z => D.m z = 1)).card : ℝ) = D.s₁ := by exact_mod_cast hs1
  have hN : (D.Non : ℝ) + 2 * (Pr.p : ℝ) ≤ D.Ncount := by
    exact_mod_cast D.Non_add_two_p_le_Ncount Pr
  have hcard : (Fintype.card ι : ℝ) = (D.s₁ : ℝ) + (D.s₂ : ℝ) + 2 * (Pr.p : ℝ) := by
    exact_mod_cast D.card_eq Pr
  constructor <;> linarith

/-- **Complete Census Certified by a Normalized Gram Matrix (`tr Â ≥ N`, `‖Â‖_F² ≤ κN`).**
Whenever `rtrace (blockP c + blockQ c) ≥ Ncount` and `frobSq (blockP c + blockQ c) ≤ κ * Ncount`,
the `c = 2` and `c = 3` Gram functionals simultaneously certify:
1. `(2 − κ)N + 2 multExcess ≤ s₁` (simple critical-line zeros),
2. `((3 − κ)/2)N + a₃ + p/2 ≤ N_d` (distinct zeros),
3. `2 a₂ + 5 a₃ + 2 p ≤ (κ − 1)N` (weighted double/triple-or-higher/off-line exclusion),
4. `s₂ + p ≤ ((κ − 1)/2)N` (combined multiple-critical and off-line pair ceiling),
5. `a₃ ≤ ((κ − 1)/5)N` (triple-or-higher critical-line zero ceiling). -/
theorem exclusion_of_normalized_gram (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {c κ : ℝ} (hc : 0 < c) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) ≤ c)
    (htr : (D.Ncount : ℝ) ≤ RHLinalg.rtrace (D.blockP c + D.blockQ c))
    (hfr : RHLinalg.frobSq (D.blockP c + D.blockQ c) ≤ κ * (D.Ncount : ℝ)) :
    (2 - κ) * (D.Ncount : ℝ) + 2 * (multExcess D Pr : ℝ) ≤ (D.s₁ : ℝ) ∧
      (3 - κ) / 2 * (D.Ncount : ℝ) + ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) +
        (Pr.p : ℝ) / 2 ≤ (Fintype.card ι : ℝ) ∧
      2 * ((D.onLine.filter (fun z => D.m z = 2)).card : ℝ) +
        5 * ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) + 2 * (Pr.p : ℝ) ≤
        (κ - 1) * (D.Ncount : ℝ) ∧
      (D.s₂ : ℝ) + (Pr.p : ℝ) ≤ (κ - 1) / 2 * (D.Ncount : ℝ) ∧
      ((D.onLine.filter (fun z => 3 ≤ D.m z)).card : ℝ) ≤ (κ - 1) / 5 * (D.Ncount : ℝ) := by
  have hm2 := mult_two_with_excess D Pr hc hPois
  have hm3 := (mult_three_with_excess D Pr hc hPois).1
  have hexcl := multiplicity_and_offLine_exclusion_law D Pr hc hPois
  have h252 := double_triple_offLine_exclusion_law D Pr hc hPois
  have hex0 : (0 : ℝ) ≤ (multExcess D Pr : ℝ) := Nat.cast_nonneg _
  have ha2_0 : (0 : ℝ) ≤ ((D.onLine.filter (fun z => D.m z = 2)).card : ℝ) := Nat.cast_nonneg _
  have hp_0 : (0 : ℝ) ≤ (Pr.p : ℝ) := Nat.cast_nonneg _
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

end ZeroBlockDataLaws

/-! ## 2. Complete Classification of Universal Matrix Functionals -/

/-- Multiple critical zero count of `doubleZeroBlockData s₁ d₂` is `d₂`. -/
theorem s₂_doubleZeroBlockData (s₁ d₂ : ℕ) :
    (doubleZeroBlockData s₁ d₂).s₂ = d₂ := by
  have hcard := (doubleZeroBlockData s₁ d₂).card_onLine
  have hon : (doubleZeroBlockData s₁ d₂).onLine = Finset.univ := by
    ext z; simp [ZeroBlockData.onLine, doubleZeroBlockData]
  rw [hon, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
    s₁_doubleZeroBlockData] at hcard
  omega

/-- Every evaluation vector of `doubleZeroBlockData s₁ d₂` has unit `ℓ²` norm. -/
theorem norm_sq_v_doubleZeroBlockData (s₁ d₂ : ℕ) (z : Fin s₁ ⊕ Fin d₂) :
    ∑ k : Fin s₁ ⊕ Fin d₂, ‖(doubleZeroBlockData s₁ d₂).v z k‖ ^ (2 : ℕ) = 1 := by
  have hterm : ∀ k : Fin s₁ ⊕ Fin d₂, ‖unitVec z k‖ ^ (2 : ℕ) = if k = z then 1 else 0 := by
    intro k; simp only [unitVec]; split_ifs <;> simp
  simp only [doubleZeroBlockData]
  simp_rw [hterm]
  simp

/-- **Complete Classification of Universal Matrix Functionals (`universal_gram_certification_classification`).**
Because `doubleZeroBlockData s₁ d₂` and `coalescedPairBlockData s₁ d₂` share the exact same
matrix `extremalDiag s₁ d₂` and total count `N = s₁ + 2d₂`, on `extremalDiag s₁ d₂`:
1. Any universal lower bound `Φ_on` on `N_on` (or `s₁`, or `s₁ + s₂`) cannot exceed the `c = 2`
   rank–trace value `4 tr Â − ‖Â‖_F² − 2N = s₁`;
2. Any universal lower bound `Ψ_dist` on `Fintype.card ι` (`N_d`, distinct zeros) cannot exceed the
   `c = 3` rank–trace value `(6 tr Â − ‖Â‖_F² − 3N) / 2 = s₁ + d₂`;
3. Any universal upper bound `Ω_mult` on `s₂` (multiple critical zeros) is at least the `c = 2`
   exclusion ceiling `(3N − (4 tr Â − ‖Â‖_F²)) / 2 = d₂`;
4. Any universal upper bound `Ω_off` on `p` (off-line pairs) is at least the `c = 2` exclusion
   ceiling `(3N − (4 tr Â − ‖Â‖_F²)) / 2 = d₂`. -/
theorem universal_gram_certification_classification (s₁ d₂ : ℕ)
    (Φ_on Ψ_dist Ω_mult Ω_off : Matrix (Fin s₁ ⊕ Fin d₂) (Fin s₁ ⊕ Fin d₂) ℂ → ℕ → ℝ)
    (hΦ : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : ZeroBlockData ι (Fin s₁ ⊕ Fin d₂)),
      (∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) ≤ 1) →
      Φ_on D.blockA D.Ncount ≤ (D.Non : ℝ))
    (hΨ : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : ZeroBlockData ι (Fin s₁ ⊕ Fin d₂)),
      (∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) ≤ 1) →
      Ψ_dist D.blockA D.Ncount ≤ (Fintype.card ι : ℝ))
    (hΩ_mult : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : ZeroBlockData ι (Fin s₁ ⊕ Fin d₂)),
      (∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) ≤ 1) →
      (D.s₂ : ℝ) ≤ Ω_mult D.blockA D.Ncount)
    (hΩ_off : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : ZeroBlockData ι (Fin s₁ ⊕ Fin d₂))
      (Pr : D.PairReps),
      (∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ (2 : ℕ) ≤ 1) →
      (Pr.p : ℝ) ≤ Ω_off D.blockA D.Ncount) :
    Φ_on (extremalDiag s₁ d₂) (s₁ + 2 * d₂) ≤
        4 * RHLinalg.rtrace (extremalDiag s₁ d₂) - RHLinalg.frobSq (extremalDiag s₁ d₂) -
          2 * ((s₁ : ℝ) + 2 * (d₂ : ℝ)) ∧
      Ψ_dist (extremalDiag s₁ d₂) (s₁ + 2 * d₂) ≤
        (6 * RHLinalg.rtrace (extremalDiag s₁ d₂) - RHLinalg.frobSq (extremalDiag s₁ d₂) -
          3 * ((s₁ : ℝ) + 2 * (d₂ : ℝ))) / 2 ∧
      (3 * ((s₁ : ℝ) + 2 * (d₂ : ℝ)) -
          (4 * RHLinalg.rtrace (extremalDiag s₁ d₂) - RHLinalg.frobSq (extremalDiag s₁ d₂))) / 2 ≤
        Ω_mult (extremalDiag s₁ d₂) (s₁ + 2 * d₂) ∧
      (3 * ((s₁ : ℝ) + 2 * (d₂ : ℝ)) -
          (4 * RHLinalg.rtrace (extremalDiag s₁ d₂) - RHLinalg.frobSq (extremalDiag s₁ d₂))) / 2 ≤
        Ω_off (extremalDiag s₁ d₂) (s₁ + 2 * d₂) := by
  refine ⟨universal_matrix_functional_barrier s₁ d₂ Φ_on hΦ, ?_, ?_, ?_⟩
  · have h := hΨ (Fin s₁ ⊕ Fin d₂) (doubleZeroBlockData s₁ d₂)
      (fun z _ => (norm_sq_v_doubleZeroBlockData s₁ d₂ z).le)
    rw [blockA_doubleZeroBlockData, (Ncount_doubleZeroBlockData s₁ d₂).1,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Nat.cast_add,
      ← rankTrace_three_extremalDiag_exact s₁ d₂] at h
    exact h
  · have h := hΩ_mult (Fin s₁ ⊕ Fin d₂) (doubleZeroBlockData s₁ d₂)
      (fun z _ => (norm_sq_v_doubleZeroBlockData s₁ d₂ z).le)
    rw [blockA_doubleZeroBlockData, (Ncount_doubleZeroBlockData s₁ d₂).1,
      s₂_doubleZeroBlockData] at h
    rw [rtrace_extremalDiag, frobSq_extremalDiag]
    linarith
  · have h := hΩ_off (Fin s₁ ⊕ (Fin d₂ ⊕ Fin d₂)) (coalescedPairBlockData s₁ d₂)
      (coalescedPairReps s₁ d₂) (fun z _ => (norm_sq_v_coalescedPairBlockData s₁ d₂ z).le)
    rw [blockA_coalescedPairBlockData, (counts_coalescedPairBlockData s₁ d₂).1,
      (counts_coalescedPairBlockData s₁ d₂).2.2.2.2] at h
    rw [rtrace_extremalDiag, frobSq_extremalDiag]
    linarith

/-! ## 3. Below Pair Correlation (`λ ≤ 1`): Flat-Top Cap `2/3` vs. Variational Profile `HD(1)` -/

/-- **Variational Window Profile Strictly Beats the Flat-Top `2/3` Cap at `λ = 1`.**
Optimizing the window profile `v*(s) = cos(√2 s)` on `[−1/2, 1/2]` gives
`HD(1) = 2 − 1/cStar(1) ≥ 1681/2500 > 2/3` (saving at least `43/7500` past `2/3`), and lowers the
normalized second moment from `kfun 1 = 4/3` to `1 / cStar 1 ≤ 3319/2500 < 4/3`. -/
theorem two_thirds_lt_HD_one :
    (2 / 3 : ℝ) < Zeta23.ThmD.HD 1 ∧
      43 / 7500 ≤ Zeta23.ThmD.HD 1 - 2 / 3 ∧
      1 / Zeta23.ThmD.cStar 1 ≤ 3319 / 2500 ∧
      1 / Zeta23.ThmD.cStar 1 < Zeta23.kfun 1 := by
  have hHD := RHTower.HD_one_ge
  have hdef : Zeta23.ThmD.HD 1 = 2 - 1 / Zeta23.ThmD.cStar 1 := rfl
  have hk1 : Zeta23.kfun 1 = 4 / 3 := by unfold Zeta23.kfun; norm_num
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Variational Window Profile Strictly Beats the Flat-Top `5/6` Distinct-Zero Cap at `λ = 1`.**
For `c = 3` (distinct zeros), `GD(1) = (HD(1) + 1)/2 ≥ 4181/5000 = 0.8362 > 5/6 = Gfun 1`. -/
theorem five_sixths_lt_GD_one :
    (5 / 6 : ℝ) < Zeta23.ThmD.GD 1 ∧
      (4181 / 5000 : ℝ) ≤ Zeta23.ThmD.GD 1 ∧
      Zeta23.Gfun 1 = 5 / 6 := by
  have hHD := RHTower.HD_one_ge
  have hGD := Zeta23.ThmD.GD_eq 1
  have hG1 : Zeta23.Gfun 1 = 5 / 6 := by unfold Zeta23.Gfun Zeta23.kfun; norm_num
  refine ⟨by linarith, by linarith, hG1⟩

/-- **Even the Variational Optimum at `λ = 1` is Strictly Bounded Below `3/4` (`HD(1) < 3/4`).**
At `s = (√2)⁻¹`, `cos s ≥ 1 − s²/2 = 3/4` while `sin s = 2 sin(s/2) cos(s/2) < s`, so
`s cos s / sin s > 3/4` and `HD(1) = 3/2 − s cos s / sin s < 3/4`. Thus no window profile
supported below `λ = 1` can reach `3/4` without zero-side spectral slack or trans-threshold
pair correlation `λ > 1`. -/
theorem HD_one_lt_three_quarters : Zeta23.ThmD.HD 1 < 3 / 4 := by
  rw [Zeta23.ThmD.HD_one]
  set s : ℝ := (Real.sqrt 2)⁻¹ with hs
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < s := inv_pos.mpr hsqrt0
  have hs2 : s ^ 2 = 1 / 2 := by rw [hs, inv_pow, hsq, one_div]
  have hs1 : s < 1 := by nlinarith
  have hcos : 3 / 4 ≤ Real.cos s := by
    have h := Real.one_sub_sq_div_two_le_cos (x := s)
    linarith
  have hsin_pos : 0 < Real.sin s :=
    Real.sin_pos_of_pos_of_lt_pi hs0 (by linarith [Real.pi_gt_three])
  have hsin_lt : Real.sin s < s := by
    have hsh0 : 0 < s / 2 := by linarith
    have hsh_sin_pos : 0 < Real.sin (s / 2) :=
      Real.sin_pos_of_pos_of_lt_pi hsh0 (by linarith [Real.pi_gt_three])
    have hsh_sin_le : Real.sin (s / 2) ≤ s / 2 := Real.sin_le hsh0.le
    have hsh_cos_lt : Real.cos (s / 2) < 1 := by
      have hsc := Real.sin_sq_add_cos_sq (s / 2)
      have hsin2 : 0 < Real.sin (s / 2) ^ 2 := sq_pos_of_pos hsh_sin_pos
      have hcos_le : Real.cos (s / 2) ≤ 1 := Real.cos_le_one (s / 2)
      nlinarith
    have h2 : Real.sin s = 2 * Real.sin (s / 2) * Real.cos (s / 2) := by
      conv_lhs => rw [show s = 2 * (s / 2) by ring, Real.sin_two_mul]
    rw [h2]
    have hcos_pos : 0 < Real.cos (s / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
    nlinarith
  have hquot : 3 / 4 < s * (Real.cos s / Real.sin s) := by
    rw [← mul_div_assoc, lt_div_iff₀ hsin_pos]
    nlinarith
  linarith

/-- `Zeta23.Ndist T₁ T₂` equals the cardinality of the native completed-`xi` window
`stripFinsetPos T₂ \ stripFinsetPos T₁` for `0 ≤ T₁`. -/
theorem zeta23_Ndist_window_eq {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) :
    Zeta23.Ndist T₁ T₂ = (RHTower.stripFinsetPos T₂ \ RHTower.stripFinsetPos T₁).card := by
  classical
  unfold Zeta23.Ndist
  rw [Set.ncard_eq_toFinset_card _ (Zeta23.zerosIn_finite T₁ T₂)]
  exact congrArg Finset.card (RHTower.zeta23_zerosIn_toFinset_eq_window hT₁)

/-- **Unconditional `5/6` Distinct Zeros on Dyadic Windows and Cumulatively (`c = 3`, Flat-Top).**
In the completed-`xi` census, at least `(5/6 − ε)` of the zeros in `(T, 2T]` and in `(0, T]` are
distinct. -/
theorem five_sixths_distinct_dyadic_and_cumulative :
    (∀ ε > 0, ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T ≥ T₀,
      (5 / 6 - ε) * ∑ z ∈ RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T,
          ((analyticOrderAt RHTower.xi z).toNat : ℝ) ≤
        ((RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T).card : ℝ)) ∧
    (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (5 / 6 - ε) * (RHTower.xiPosZeroCount T : ℝ) ≤ (RHTower.xiPosDistinctZeroCount T : ℝ)) := by
  constructor
  · intro ε hε
    obtain ⟨T₀, hT₀⟩ := Zeta23.thmC₀_mult ε hε
    refine ⟨max T₀ 0, le_max_right _ _, fun T hT => ?_⟩
    have hT0 : 0 ≤ T := (le_max_right _ _).trans hT
    have h := hT₀ T ((le_max_left _ _).trans hT)
    rwa [RHTower.zeta23_Ncount_window_eq hT0, zeta23_Ndist_window_eq hT0] at h
  · intro ε hε
    obtain ⟨T₀, hT₀⟩ := Zeta23.thmC₀_mult_cumulative ε hε
    refine ⟨T₀, fun T hT => ?_⟩
    simpa only [RHTower.zeta23_Ncount_zero_eq_xiPosZeroCount,
      RHTower.zeta23_Ndist_zero_eq_xiPosDistinctZeroCount] using hT₀ T hT

/-- **Unconditional Montgomery–Taylor `HD(1) = 0.6725…` Simple-Critical Density on Dyadic Windows.**
In the completed-`xi` census, at least `(HD(1) − ε)` of the zeros in every dyadic window `(T, 2T]`
are simple and on the critical line (`HD(1) ≥ 1681/2500 > 2/3`). -/
theorem montgomeryTaylor_simpleCritical_dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T ≥ T₀,
      (Zeta23.ThmD.HD 1 - ε) * ∑ z ∈ RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T,
          ((analyticOrderAt RHTower.xi z).toNat : ℝ) ≤
        (((RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T).filter
            (fun z => z.re = 1 / 2 ∧ (analyticOrderAt RHTower.xi z).toNat = 1)).card : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := Zeta23.ThmD.thmD₀_simple_mult ε hε
  refine ⟨max T₀ 0, le_max_right _ _, fun T hT => ?_⟩
  have hT0 : 0 ≤ T := (le_max_right _ _).trans hT
  have h := hT₀ T ((le_max_left _ _).trans hT)
  rwa [RHTower.zeta23_Ncount_window_eq hT0, RHTower.zeta23_N0simple_window_eq hT0] at h

/-- **Unconditional Montgomery–Taylor `GD(1) = 0.83625…` Distinct-Zero Density on Dyadic Windows.**
In the completed-`xi` census, at least `(GD(1) − ε)` of the zeros in every dyadic window `(T, 2T]`
are distinct (`GD(1) ≥ 4181/5000 > 5/6`). -/
theorem montgomeryTaylor_distinct_dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T ≥ T₀,
      (Zeta23.ThmD.GD 1 - ε) * ∑ z ∈ RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T,
          ((analyticOrderAt RHTower.xi z).toNat : ℝ) ≤
        ((RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T).card : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := Zeta23.ThmD.thmD₀_dist_mult ε hε
  refine ⟨max T₀ 0, le_max_right _ _, fun T hT => ?_⟩
  have hT0 : 0 ≤ T := (le_max_right _ _).trans hT
  have h := hT₀ T ((le_max_left _ _).trans hT)
  rwa [RHTower.zeta23_Ncount_window_eq hT0, zeta23_Ndist_window_eq hT0] at h

/-- **Unconditional Dyadic Off-Line Exclusion Ceiling for `ξ` (`≤ (1 − HD(1))/2 ≤ 819/5000 < 1/6`).**
By reflection (`two_mul_sum_right_add_simple_le`) and `montgomeryTaylor_simpleCritical_dyadic`, the
total multiplicity of zeros of `ξ` strictly to the right of the critical line in `(T, 2T]` is
unconditionally at most `((1 − HD(1))/2 + ε) N(T, 2T) ≤ (819/5000 + ε) N(T, 2T) < (1/6 + ε) N(T, 2T)`. -/
theorem offLine_right_multiplicity_dyadic_le :
    ∀ ε > 0, ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T ≥ T₀,
      ∑ z ∈ RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T,
          ((analyticOrderAt RHTower.xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0) ≤
        ((1 - Zeta23.ThmD.HD 1) / 2 + ε) *
          ∑ z ∈ RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T,
            ((analyticOrderAt RHTower.xi z).toNat : ℝ) ∧
      ∑ z ∈ RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T,
          ((analyticOrderAt RHTower.xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0) ≤
        (819 / 5000 + ε) *
          ∑ z ∈ RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T,
            ((analyticOrderAt RHTower.xi z).toNat : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀0, hT₀⟩ := montgomeryTaylor_simpleCritical_dyadic (2 * ε) (by linarith)
  have hHD := RHTower.HD_one_ge
  refine ⟨T₀, hT₀0, fun T hT => ?_⟩
  have hrefl := RHTower.two_mul_sum_right_add_simple_le (T₁ := T) (T₂ := 2 * T)
  have hsimple := hT₀ T hT
  have hN0 : 0 ≤ ∑ z ∈ RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T,
      ((analyticOrderAt RHTower.xi z).toNat : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have h1 : ∑ z ∈ RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T,
      ((analyticOrderAt RHTower.xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0) ≤
      ((1 - Zeta23.ThmD.HD 1) / 2 + ε) *
        ∑ z ∈ RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T,
          ((analyticOrderAt RHTower.xi z).toNat : ℝ) := by linarith
  refine ⟨h1, h1.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith) hN0

/-! ## 4. The Two Routes to `3/4`: Dual Sub-Threshold Slack Ceiling and Two-Window Mixture -/

/-- **Dual Ceiling on the Sub-Threshold Spectral-Slack Functional (`λ ∈ (0, 1)`).**
For every sub-threshold bandwidth `λ ∈ (0, 1)` and `ε > 0`, the slack-augmented Gram certificate
`(H(λ) − ε) N(T, 2T) + zeroSideSlack(λ, T)` is simultaneously bounded above by `N₀*(T, 2T)` AND by
the normalized grid dimension `(λ + ε) N(T, 2T)`. Consequently, at bandwidth `λ ∈ (0, 1)`, no
amount of zero-side spectral slack can ever certify a critical-line proportion larger than `λ`. -/
theorem subthreshold_spectralSlack_dual_ceiling {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.Hfun lam - ε) * (Zeta23.Ncount T (2 * T) : ℝ) +
        RHTower.zeroSideSlack Zeta23.zetaZeroConfig (Zeta23.paramsOf Zeta23.stdProfile lam) T ≤
        min (Zeta23.N0star T (2 * T) : ℝ) ((lam + ε) * (Zeta23.Ncount T (2 * T) : ℝ)) := by
  obtain ⟨T₁, hT₁⟩ := RHTower.thmA_lam_spectralSlack h0 h1 ε hε
  obtain ⟨T₂, hT₂⟩ := zeroSideSlack_eventually_le_lam_sub_Hfun h0 h1 hε
  refine ⟨max T₁ T₂, fun T hT => le_min (hT₁ T ((le_max_left _ _).trans hT)) ?_⟩
  obtain ⟨hd1, hd2, -⟩ := hT₂ T ((le_max_right _ _).trans hT)
  have hN0 : 0 ≤ (Zeta23.Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **Two-Window Mixture Exact Value at `B = 2` (`1513/1944 > 3/4`).**
At the Montgomery pair-correlation bound `B = 2`, the single uniform window of length `4/3`
certifies `certOpt 2 = 3/4 = 0.75`, whereas mixing it with the unconditional length-`1` window at
weight `ε = 1/3` (`RHTower.mixQ 2 (1/3) = 2375/1944`) certifies `2 − mixQ 2 (1/3) = 1513/1944 ≈ 0.7783`,
gaining an additional `55/1944` beyond `3/4`. -/
theorem mixQ_at_two_one_third :
    2 - RHTower.mixQ 2 (1 / 3) = 1513 / 1944 ∧
      RHTower.certOpt 2 = 3 / 4 ∧
      2 - RHTower.mixQ 2 (1 / 3) - RHTower.certOpt 2 = 55 / 1944 := by
  unfold RHTower.mixQ RHTower.certOpt
  norm_num

/-- **Exact Linear Form of the Two-Window Mixture at `ε = 7/16` and `B ≤ 117/41` Threshold for `3/4`.**
At mixture weight `ε = 7/16`, `2 − mixQ B (7/16) = 3/4 + 3 * (117 − 41 * B) / 4096`. Thus the
two-window mixture at `ε = 7/16` certifies at least `3/4` if and only if `B ≤ 117/41 ≈ 2.8537`
(in particular for all `B ≤ 14/5 = 2.8`, relaxing the single-window requirement `B ≤ 2`). -/
theorem mixQ_ge_three_quarters_iff_le_oneHundredSeventeen_div_fortyOne (B : ℝ) :
    2 - RHTower.mixQ B (7 / 16) = 3 / 4 + 3 * (117 - 41 * B) / 4096 ∧
      (3 / 4 ≤ 2 - RHTower.mixQ B (7 / 16) ↔ B ≤ 117 / 41) ∧
      (B ≤ 14 / 5 → 3 / 4 ≤ 2 - RHTower.mixQ B (7 / 16)) := by
  have hid : 2 - RHTower.mixQ B (7 / 16) = 3 / 4 + 3 * (117 - 41 * B) / 4096 := by
    unfold RHTower.mixQ; ring
  refine ⟨hid, ?_, RHTower.mixture_three_quarters⟩
  rw [hid]
  constructor <;> intro h <;> linarith

/-- **Two-Window Mixture Strictly Beats `2/3` Whenever `B < 181/18`.**
Expanding `mixQ B (1 − δ)` around `ε = 1` (`δ = 0`) gives
`2 − mixQ B (1 − δ) = 2/3 + δ((181 − 18B)/432 − δ(182 + 18B)/864)`. For every `B < 181/18`,
there exists `ε ∈ (0, 1)` such that `2/3 < 2 − mixQ B ε`. -/
theorem mixQ_beats_two_thirds_of_lt {B : ℝ} (hB : B < 181 / 18) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ 2 / 3 < 2 - RHTower.mixQ B ε := by
  have hexp : ∀ δ : ℝ, 2 - RHTower.mixQ B (1 - δ) =
      2 / 3 + δ * ((181 - 18 * B) / 432 - δ * (182 + 18 * B) / 864) := by
    intro δ; unfold RHTower.mixQ; ring
  set num : ℝ := 181 - 18 * B
  have hnum : 0 < num := by dsimp [num]; linarith
  set den : ℝ := 182 + 18 * |B|
  have hden : 0 < den := by dsimp [den]; positivity
  set δ : ℝ := min (1 / 2) (num / den)
  have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hnum hden)
  have hδ12 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ_le : δ ≤ num / den := min_le_right _ _
  refine ⟨1 - δ, by linarith, by linarith, ?_⟩
  have h1 : δ * den ≤ num := (le_div_iff₀ hden).mp hδ_le
  have h2 : 2 - RHTower.mixQ B (1 - δ) ≥
      2 / 3 + δ * (num / 432 - δ * den / 864) := by
    rw [hexp δ]
    have habs : B ≤ |B| := le_abs_self B
    have hδsq : 0 ≤ δ ^ 2 := sq_nonneg δ
    dsimp [num, den]
    nlinarith
  have h3 : 0 < num / 432 - δ * den / 864 := by linarith
  have h4 : 0 < δ * (num / 432 - δ * den / 864) := mul_pos hδ0 h3
  linarith

/-! ## 5. Downstream Applications to `RHTower`: Dyadic Off-Line Moment and Uniqueness Threshold -/

/-- **General Proportion Transfer for the Dyadic Window Off-Line Moment.**
If at least `(p₀ − ε) N(T, 2T)` zeros of `ξ` in `(T, 2T]` are simple and on the critical line for
every `ε > 0` (`0 < p₀ ≤ 1`), then for every `R > 0` and `η > 0`, eventually
`4π Σ_{T+1 < Im ρ ≤ 2T−1} m_ρ (Re ρ − 1/2)⁺ ≤ (log c_R − (1 + p₀) R + η) T`. -/
theorem eventually_dyadicWindowTail_le_selberg_upper_of_proportion {p₀ R η : ℝ}
    (hp₀0 : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hR : 0 < R) (hη : 0 < η)
    (hprop : ∀ ε > 0, ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T ≥ T₀,
      (p₀ - ε) * ∑ z ∈ RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T,
          ((analyticOrderAt RHTower.xi z).toNat : ℝ) ≤
        (((RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T).filter
            (fun z => z.re = 1 / 2 ∧ (analyticOrderAt RHTower.xi z).toNat = 1)).card : ℝ)) :
    ∀ᶠ T in atTop,
      4 * Real.pi * RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤
        (Real.log (ZetaGateProductAFE.selbergBlockConstUpper R) - (1 + p₀) * R + η) * T := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ZetaGateProductAFE.selbergBlockConstUpper R := ⟨_, rfl⟩
  rw [← hcdef]
  have hc1 : 1 ≤ c := hcdef ▸ ZetaGateProductAFE.one_le_selbergBlockConstUpper hR
  have hc0 : 0 < c := by linarith
  have hlogc : 2 * R ≤ Real.log c := hcdef ▸ RHTower.two_mul_le_log_selbergBlockConstUpper hR
  obtain ⟨η', hη'⟩ : ∃ η' : ℝ, η' = η / 2 := ⟨_, rfl⟩
  have hη'0 : 0 < η' := by rw [hη']; positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (η / (4 * R)) p₀ := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; exact lt_min (by positivity) hp₀0
  have hεp : ε ≤ p₀ := by rw [hεdef]; exact min_le_right _ _
  have hεR : ε * R ≤ η / 4 := by
    have h1 : ε ≤ η / (4 * R) := by rw [hεdef]; exact min_le_left _ _
    calc ε * R ≤ η / (4 * R) * R := mul_le_mul_of_nonneg_right h1 hR.le
      _ = η / 4 := by field_simp
  obtain ⟨TZ, hTZ0, hZ⟩ := hprop ε hε0
  obtain ⟨Cc, hCc, Tc, hTc, hceil⟩ := RHTower.exists_xiZeroCount_window_le
  obtain ⟨C, K, hC, hK, hwide⟩ := RHTower.exists_zetaWideMoment_le_of_mollified_meanSquare
  obtain ⟨CR, hCR, TR, hTR, hrvm⟩ := RHTower.exists_xiPosZeroCount_window_bounds
  have hεc : 0 < c * (η' / 8) := mul_pos hc0 (div_pos hη'0 (by norm_num))
  obtain ⟨U₀, hU₀⟩ := Filter.eventually_atTop.mp
    (ZetaGateProductAFE.eventually_window_meanSquare_selberg_upper hR hεc)
  rw [← hcdef] at hU₀
  have hbb1 : 1 ≤ RHTower.routeKRVMBase := by
    rw [RHTower.routeKRVMBase]
    have h1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    nlinarith
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ,
      L₀ = 8 * R + 16 * R * (Real.log 2 + Real.log RHTower.routeKRVMBase) / η' := ⟨_, rfl⟩
  have hp1_nn : 0 ≤ 16 * R * (Real.log 2 + Real.log RHTower.routeKRVMBase) / η' := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have : 0 ≤ Real.log RHTower.routeKRVMBase := Real.log_nonneg hbb1
    exact div_nonneg (by positivity) hη'0.le
  have hL₀a : 8 * R ≤ L₀ := by linarith
  have hL₀b : 16 * R * (Real.log 2 + Real.log RHTower.routeKRVMBase) / η' ≤ L₀ := by linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 12 * Real.pi * R * CR + 2 * C + 14 * K * Real.log 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 4 * Real.pi * R * (8 * (1 / (2 * Real.pi) + 2 * Cc)) := ⟨_, rfl⟩
  have hη64 : 0 < η' / 64 := div_pos hη'0 (by norm_num)
  filter_upwards [eventually_ge_atTop (max (max U₀ (TR + 1)) (max ((2 : ℝ) ^ 50) (Real.exp L₀))),
    eventually_ge_atTop (max (TZ + 1) (Tc + 1)),
    RHTower.eventually_const_mul_rpow_neg_le 8 ((1 : ℝ) / 100) (by norm_num)
      (show 0 < η' / 8 from div_pos hη'0 (by norm_num)),
    RHTower.eventually_const_mul_rpow_neg_mul_log_pow_le A ((24 : ℝ) / 25) (by norm_num) 0 hη64,
    RHTower.eventually_const_mul_rpow_neg_mul_log_pow_le (8 * K) ((24 : ℝ) / 25) (by norm_num) 1 hη64,
    RHTower.eventually_const_mul_rpow_neg_mul_log_pow_le B ((24 : ℝ) / 25) (by norm_num) 0 hη64]
    with T hTbig hTbig2 hratio hadd1 hadd2 hadd3
  have hTU₀ : U₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hTbig
  have hTTR : TR + 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTbig
  have hT50 : (2 : ℝ) ^ 50 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hTbig
  have hTL : Real.exp L₀ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hTbig
  have hTZ : TZ ≤ T := by linarith [le_max_left (TZ + 1) (Tc + 1)]
  have hTc' : Tc ≤ T := by linarith [le_max_right (TZ + 1) (Tc + 1)]
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT50
  have hT2 : 2 ≤ T := le_trans (by norm_num) hT50
  have hlogTL : L₀ ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos L₀) hTL
    rwa [Real.log_exp] at this
  have hT2425 : (4 : ℝ) ≤ T ^ ((24 : ℝ) / 25) :=
    RHTower.four_le_rpow_twentyfour_div_twentyfive (le_trans (by norm_num) hT50)
  have hH1 : T ^ ((24 : ℝ) / 25) ≤ T := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ T)
      (show (24 : ℝ) / 25 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have hH4 : 4 ≤ T := le_trans hT2425 hH1
  have hpos2425 : 0 < T ^ ((24 : ℝ) / 25) := Real.rpow_pos_of_pos hT0 _
  have hA' : A ≤ η' / 64 * T ^ ((24 : ℝ) / 25) := by
    have h := hadd1
    rw [pow_zero, mul_one, Real.rpow_neg hT0.le, ← div_eq_mul_inv, div_le_iff₀ hpos2425] at h
    exact h
  have hK' : 8 * K * Real.log T ≤ η' / 64 * T ^ ((24 : ℝ) / 25) := by
    have h := hadd2
    rw [pow_one, Real.rpow_neg hT0.le, ← mul_assoc, mul_comm (8 * K), mul_assoc,
      ← div_eq_inv_mul, div_le_iff₀ hpos2425] at h
    linarith only [h]
  have hB' : B ≤ η' / 64 * T ^ ((24 : ℝ) / 25) := by
    have h := hadd3
    rw [pow_zero, mul_one, Real.rpow_neg hT0.le, ← div_eq_mul_inv, div_le_iff₀ hpos2425] at h
    exact h
  have hms := hU₀ (T + T) (by linarith)
  obtain ⟨T₁, T₂, hT₁lo, hT₁hi, hT₂lo, hT₂hi, hlit₀⟩ :=
    RHTower.exists_window_littlewood_upper hR hwide hT50 hH4 le_rfl (le_trans hL₀a hlogTL) hms
  obtain ⟨hNlo, -⟩ := hrvm T₁ T₂ (by linarith) (by linarith)
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = p₀ - ε := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by rw [hpdef]; linarith only [hεp]
  have hp1 : p ≤ 1 := by rw [hpdef]; linarith only [hε0, hp₀1]
  have hT₁₂ : T₁ ≤ T₂ := by linarith
  have hsub :
      RHTower.stripFinsetPos T₂ \ RHTower.stripFinsetPos T₁ ⊆
        RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T := by
    intro z hz
    rw [Finset.mem_sdiff] at hz ⊢
    exact ⟨RHTower.stripFinsetPos_mono (by linarith) hz.1,
      fun h => hz.2 (RHTower.stripFinsetPos_mono hT₁lo.le h)⟩
  have hRmono : ∑ z ∈ RHTower.stripFinsetPos T₂ \ RHTower.stripFinsetPos T₁,
        ((analyticOrderAt RHTower.xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0)
      ≤ ∑ z ∈ RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T,
        ((analyticOrderAt RHTower.xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ =>
      mul_nonneg (Nat.cast_nonneg _) (by split_ifs <;> norm_num)
  have hrefl := RHTower.two_mul_sum_right_add_simple_le (T₁ := T) (T₂ := 2 * T)
  have hZT := hZ T hTZ
  have hNdy := RHTower.window_mult_sum_eq (T₁ := T) (T₂ := 2 * T) (by linarith)
  rw [hNdy] at hrefl hZT
  have hcast : ∀ t : ℝ, 0 ≤ t →
      ((RHTower.xiPosZeroCount t : ℕ) : ℝ) = ((RHTower.xiZeroCount t : ℤ) : ℝ) := by
    intro t ht
    have := RHTower.xiPosZeroCount_eq_xiZeroCount ht
    exact_mod_cast this
  have hE₁ : (RHTower.xiPosZeroCount T₁ : ℝ) - RHTower.xiPosZeroCount T
      ≤ 1 / (2 * Real.pi) * Real.log (T + 1) + 2 * Cc * Real.log (T + 1) := by
    have h := hceil T hTc' 1 (by norm_num)
    rw [← hcast (T + 1) (by linarith), ← hcast T hT0.le] at h
    have hmono : (RHTower.xiPosZeroCount T₁ : ℝ) ≤ RHTower.xiPosZeroCount (T + 1) := by
      exact_mod_cast Finset.sum_le_sum_of_subset (RHTower.stripFinsetPos_mono hT₁hi.le)
    linarith
  have hE₂ : (RHTower.xiPosZeroCount (2 * T) : ℝ) - RHTower.xiPosZeroCount T₂
      ≤ 1 / (2 * Real.pi) * Real.log (2 * T) + 2 * Cc * Real.log (2 * T) := by
    have h := hceil (2 * T - 1) (by linarith) 1 (by norm_num)
    rw [show 2 * T - 1 + 1 = 2 * T by ring, ← hcast (2 * T) (by linarith),
      ← hcast (2 * T - 1) (by linarith)] at h
    have hmono : (RHTower.xiPosZeroCount (2 * T - 1) : ℝ) ≤ RHTower.xiPosZeroCount T₂ := by
      exact_mod_cast Finset.sum_le_sum_of_subset (RHTower.stripFinsetPos_mono (by linarith))
    linarith
  have hlog1 : Real.log (T + 1) ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
  have hlog2T : Real.log (2 * T) ≤ 2 * Real.log T := by
    have h2T : 2 * T ≤ T ^ 2 := by
      have := mul_le_mul_of_nonneg_left hT2 hT0.le
      nlinarith only [this]
    have := Real.log_le_log (by linarith) h2T
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  obtain ⟨Ec, hEc⟩ : ∃ Ec : ℝ, Ec = (1 / (2 * Real.pi) + 2 * Cc) * (2 * Real.log (2 * T)) :=
    ⟨_, rfl⟩
  have hright : ∑ z ∈ RHTower.stripFinsetPos T₂ \ RHTower.stripFinsetPos T₁,
        ((analyticOrderAt RHTower.xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0)
      ≤ (1 - p) / 2 * ((RHTower.xiPosZeroCount T₂ : ℝ) - RHTower.xiPosZeroCount T₁) + Ec := by
    have hNw : (RHTower.xiPosZeroCount (2 * T) : ℝ) - RHTower.xiPosZeroCount T
        ≤ ((RHTower.xiPosZeroCount T₂ : ℝ) - RHTower.xiPosZeroCount T₁) + Ec := by
      rw [hEc]
      have hc4 : 0 ≤ 1 / (2 * Real.pi) + 2 * Cc := by positivity
      have h1 := mul_le_mul_of_nonneg_left hlog1 hc4
      linarith
    have hq : 0 ≤ (1 - p) / 2 := by linarith only [hp1]
    have hq1 : (1 - p) / 2 ≤ 1 := by linarith only [hp0]
    have hRdy : ∑ z ∈ RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T,
          ((analyticOrderAt RHTower.xi z).toNat : ℝ) * (if 1 / 2 < z.re then 1 else 0)
        ≤ (1 - p) / 2 * ((RHTower.xiPosZeroCount (2 * T) : ℝ) - RHTower.xiPosZeroCount T) := by
      rw [hpdef]; linarith only [hrefl, hZT]
    have h3 := mul_le_mul_of_nonneg_left hNw hq
    have hEc0 : 0 ≤ Ec := by
      rw [hEc]
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T by linarith only [hT2])
      positivity
    have h4 : (1 - p) / 2 * Ec ≤ Ec := by
      have := mul_le_mul_of_nonneg_right hq1 hEc0
      linarith only [this]
    linarith
  have hX : 4 * Real.pi * (R / Real.log T₂ * Ec) ≤ η' / 64 * T ^ ((24 : ℝ) / 25) := by
    have hlogT₂ : Real.log T ≤ Real.log T₂ :=
      Real.log_le_log hT0 (by linarith only [hT₁lo, hT₁₂])
    have hlogTpos : 0 < Real.log T := Real.log_pos (by linarith only [hT2])
    have h1 : R / Real.log T₂ * Ec ≤ R * (8 * (1 / (2 * Real.pi) + 2 * Cc)) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith only [hlogT₂, hlogTpos])]
      rw [hEc]
      have hc4 : 0 ≤ 1 / (2 * Real.pi) + 2 * Cc := by positivity
      have hl : 2 * Real.log (2 * T) ≤ 8 * Real.log T₂ := by
        linarith only [hlog2T, hlogT₂, hlogTpos]
      have h5 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl hc4) hR.le
      calc R * ((1 / (2 * Real.pi) + 2 * Cc) * (2 * Real.log (2 * T)))
          ≤ R * ((1 / (2 * Real.pi) + 2 * Cc) * (8 * Real.log T₂)) := h5
        _ = R * (8 * (1 / (2 * Real.pi) + 2 * Cc)) * Real.log T₂ := by ring
    calc 4 * Real.pi * (R / Real.log T₂ * Ec) ≤ 4 * Real.pi * (R * (8 * (1 / (2 * Real.pi) +
          2 * Cc))) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = B := by rw [hB]; ring
      _ ≤ η' / 64 * T ^ ((24 : ℝ) / 25) := hB'
  have hN2 := ZetaGateProductAFE.two_le_mollUpper (show (2 : ℝ) ^ 50 ≤ T + T by linarith)
  have h := RHTower.window_moment_of_littlewood_dyadic hp0 hp1 hR hη'0 hc0 hlogc hK hCR hC hbb1
    hL₀a hL₀b hA hT0 hlogTL hratio hA' hK' hX hT2425 hH1 le_rfl hT₁lo hT₁hi hT₂lo hT₂hi
    (by omega) (ZetaGateProductAFE.mollUpper_le (by linarith only [hT0])) hlit₀ hNlo hright
  rw [show T + T - 1 = 2 * T - 1 by ring] at h
  refine h.trans ?_
  have : Real.log c - (1 + p) * R + η' ≤ Real.log c - (1 + p₀) * R + η := by
    rw [hpdef, hη']
    have e : (1 + (p₀ - ε)) * R = (1 + p₀) * R - ε * R := by ring
    linarith only [e, hεR, hη]
  exact mul_le_mul_of_nonneg_right this hT0.le

/-- **Unconditional Montgomery–Taylor Upgrade of the Dyadic Window Off-Line Moment (`66/1000`).**
Using `montgomeryTaylor_simpleCritical_dyadic` (`HD(1) ≥ 1681/2500`), for every `R, η > 0`:
1. `4π windowTail 0 (T+1) (2T−1) ≤ (log c_R − (1 + HD(1)) R + η) T` eventually,
2. `windowTail 0 (T+1) (2T−1) ≤ (66/1000) T` eventually (`R = 3/2`), strictly improving
   `eventually_dyadicWindowTail_le_sixtySeven_thousandths` (`67/1000 * T`). -/
theorem eventually_dyadicWindowTail_le_sixtySix_thousandths :
    (∀ {R η : ℝ}, 0 < R → 0 < η → ∀ᶠ T in atTop,
      4 * Real.pi * RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤
        (Real.log (ZetaGateProductAFE.selbergBlockConstUpper R) -
          (1 + Zeta23.ThmD.HD 1) * R + η) * T) ∧
    (∀ᶠ T in atTop, RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤ 66 / 1000 * T) := by
  have hHD_pos : 0 < Zeta23.ThmD.HD 1 := lt_of_lt_of_le (by norm_num) RHTower.HD_one_ge
  have hHD_le1 : Zeta23.ThmD.HD 1 ≤ 1 := le_trans HD_one_lt_three_quarters.le (by norm_num)
  have hgen : ∀ {R η : ℝ}, 0 < R → 0 < η → ∀ᶠ T in atTop,
      4 * Real.pi * RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤
        (Real.log (ZetaGateProductAFE.selbergBlockConstUpper R) -
          (1 + Zeta23.ThmD.HD 1) * R + η) * T :=
    fun hR hη => eventually_dyadicWindowTail_le_selberg_upper_of_proportion hHD_pos hHD_le1 hR hη
      montgomeryTaylor_simpleCritical_dyadic
  refine ⟨hgen, ?_⟩
  filter_upwards [hgen (R := 3 / 2) (η := 1 / 1000) (by norm_num) (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with T hT hT0
  have hc := RHTower.log_selbergBlockConstUpper_three_halves_le_montgomeryTaylor
  have hHD := RHTower.HD_one_ge
  have hπ : 0 < 4 * Real.pi := by positivity
  have hcoef : Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 2)) -
      (1 + Zeta23.ThmD.HD 1) * (3 / 2) + 1 / 1000 ≤ 4 * Real.pi * (66 / 1000) := by linarith
  have h1 : 4 * Real.pi * RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤
      4 * Real.pi * (66 / 1000 * T) := by
    calc 4 * Real.pi * RHTower.windowTail 0 (T + 1) (2 * T - 1)
        ≤ (Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 2)) -
            (1 + Zeta23.ThmD.HD 1) * (3 / 2) + 1 / 1000) * T := hT
      _ ≤ (4 * Real.pi * (66 / 1000)) * T := mul_le_mul_of_nonneg_right hcoef hT0
      _ = 4 * Real.pi * (66 / 1000 * T) := by ring
  exact le_of_mul_le_mul_left h1 hπ

/-- `log c_{3/2} − (7/4)(3/2) + 1/1000 ≤ 4π · 57/1000`. -/
theorem log_selbergBlockConstUpper_three_halves_le_three_quarters :
    Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 2)) - (7 / 4) * (3 / 2)
      + 1 / 1000 ≤ 4 * Real.pi * (57 / 1000) := by
  set y : ℝ := Real.exp (-(63 / 50 : ℝ)) with hy
  have hden := RHTower.exp_neg_threeHundredThirtyFive_le_one_sub_exp_neg_sixtyThree_fiftieths
  rw [← hy] at hden
  have h1y : 0 < 1 - y := lt_of_lt_of_le (Real.exp_pos _) hden
  have hc : ZetaGateProductAFE.selbergBlockConstUpper (3 / 2) = Real.exp 3 / (1 - y) := by
    unfold ZetaGateProductAFE.selbergBlockConstUpper
    rw [hy]
    norm_num
  rw [hc, Real.log_div (Real.exp_pos _).ne' h1y.ne', Real.log_exp]
  have hlog : -(335 / 1000) ≤ Real.log (1 - y) := by
    have := Real.log_le_log (Real.exp_pos _) hden
    rwa [Real.log_exp] at this
  have hπ := Real.pi_gt_d4
  norm_num at hπ ⊢
  linarith

/-- **Three-Quarters Upgrade of the Dyadic and Cumulative Off-Line Moment (`57/1000` under `PrimeSurplusFourThirds`).**
Under `PrimeSurplusFourThirds`, the simple-critical proportion `p = 3/4` upgrades the off-line
moment slope from `(5/3)R` to `(7/4)R`, reducing both the dyadic window off-line moment and the
cumulative off-line moment at `R = 3/2` from `(66/1000)` down to `(57/1000)`. -/
theorem offLineMoment_fiftySeven_thousandths_of_primeSurplusFourThirds
    (h : RHTower.PrimeSurplusFourThirds) :
    (∀ {R η : ℝ}, 0 < R → 0 < η → ∀ᶠ T in atTop,
      4 * Real.pi * RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤
        (Real.log (ZetaGateProductAFE.selbergBlockConstUpper R) - 7 / 4 * R + η) * T) ∧
    (∀ᶠ T in atTop, RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤ 57 / 1000 * T) ∧
    (∀ᶠ V in atTop, RHTower.offLineMoment V ≤ 57 / 1000 * V) := by
  have hFrob : RHTower.FrobeniusFourThirds :=
    RHTower.frobeniusFourThirds_of_surplus (RHTower.surplusFourThirds_of_primeSurplus h)
  have hprop_dyadic : ∀ ε > 0, ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T ≥ T₀,
      (3 / 4 - ε) * ∑ z ∈ RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T,
          ((analyticOrderAt RHTower.xi z).toNat : ℝ) ≤
        (((RHTower.stripFinsetPos (2 * T) \ RHTower.stripFinsetPos T).filter
            (fun z => z.re = 1 / 2 ∧ (analyticOrderAt RHTower.xi z).toNat = 1)).card : ℝ) := by
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := RHTower.zeta_three_quarters_simple_of_frobenius hFrob ε hε
    refine ⟨max T₀ 0, le_max_right _ _, fun T hT => ?_⟩
    have hT0 : 0 ≤ T := (le_max_right _ _).trans hT
    have h1 := hT₀ T ((le_max_left _ _).trans hT)
    rwa [RHTower.zeta23_Ncount_window_eq hT0, RHTower.zeta23_N0simple_window_eq hT0] at h1
  have hgen : ∀ {R η : ℝ}, 0 < R → 0 < η → ∀ᶠ T in atTop,
      4 * Real.pi * RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤
        (Real.log (ZetaGateProductAFE.selbergBlockConstUpper R) - 7 / 4 * R + η) * T := by
    intro R η hR hη
    have := eventually_dyadicWindowTail_le_selberg_upper_of_proportion
      (p₀ := 3 / 4) (by norm_num) (by norm_num) hR hη hprop_dyadic
    simpa [show (1 + 3 / 4 : ℝ) = 7 / 4 by norm_num] using this
  refine ⟨hgen, ?_, ?_⟩
  · filter_upwards [hgen (R := 3 / 2) (η := 1 / 1000) (by norm_num) (by norm_num),
      eventually_ge_atTop (0 : ℝ)] with T hT hT0
    have hc := log_selbergBlockConstUpper_three_halves_le_three_quarters
    have hπ : 0 < 4 * Real.pi := by positivity
    have h1 : 4 * Real.pi * RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤
        4 * Real.pi * (57 / 1000 * T) := by
      calc 4 * Real.pi * RHTower.windowTail 0 (T + 1) (2 * T - 1)
          ≤ (Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 2)) -
              (7 / 4) * (3 / 2) + 1 / 1000) * T := hT
        _ ≤ (4 * Real.pi * (57 / 1000)) * T := mul_le_mul_of_nonneg_right hc hT0
        _ = 4 * Real.pi * (57 / 1000 * T) := by ring
    exact le_of_mul_le_mul_left h1 hπ
  · have hprop_cum : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
        (3 / 4 - ε) * (RHTower.xiPosZeroCount T : ℝ) ≤ (RHTower.xiSimpleCriticalZeroCount T : ℝ) := by
      intro ε hε
      obtain ⟨T₀, hT₀⟩ := RHTower.zeta_three_quarters_simple_of_prime_surplus h ε hε
      refine ⟨T₀, fun T hT => ?_⟩
      simpa only [RHTower.zeta23_Ncount_zero_eq_xiPosZeroCount,
        RHTower.zeta23_N0simple_zero_eq_xiSimpleCriticalZeroCount] using hT₀ T hT
    have hcum := RHTower.eventually_offLineMoment_le_of_zetaGateFrom_proportion (α := (49 : ℝ) / 50)
      (R := 3 / 2) (η := 1 / 1000) (p := 3 / 4) (by norm_num) (by norm_num) (by norm_num)
      (ZetaGateProductAFE.one_le_selbergBlockConstUpper (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num) hprop_cum (ZetaGateProductAFE.zetaMollifiedMeanSquareGateFrom_selberg_upper
        (by norm_num))
    filter_upwards [hcum, eventually_ge_atTop (0 : ℝ)] with V hV hV0
    have hc := log_selbergBlockConstUpper_three_halves_le_three_quarters
    have hπ : 0 < 4 * Real.pi := by positivity
    have h1 : 4 * Real.pi * RHTower.offLineMoment V ≤ 4 * Real.pi * (57 / 1000 * V) := by
      calc 4 * Real.pi * RHTower.offLineMoment V
          ≤ (Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 2)) -
              (1 + 3 / 4) * (3 / 2) + 1 / 1000) * V := hV
        _ = (Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 2)) -
              (7 / 4) * (3 / 2) + 1 / 1000) * V := by ring
        _ ≤ (4 * Real.pi * (57 / 1000)) * V := mul_le_mul_of_nonneg_right hc hV0
        _ = 4 * Real.pi * (57 / 1000 * V) := by ring
    exact le_of_mul_le_mul_left h1 hπ

/-- **General Proportion Transfer for the Real-Divisor-Only Double-Exponential Capacity Threshold (`b > 2/p`).**
If at least `(p − ε) N(T)` zeros of `ξ` in `(0, T]` are simple and on the critical line (`0 < p ≤ 1`),
and an even measurable `u` obeys `|u(x)| ≤ C exp(−a e^{b|x|})` with `b > 2 / p` and its transform
vanishes at every simple critical zero of `ξ`, then `u = 0` almost everywhere. -/
theorem ae_eq_zero_of_doubleExp_simpleCritical_of_proportion
    {u : ℝ → ℂ} {a b C p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hprop : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (p - ε) * (RHTower.xiPosZeroCount T : ℝ) ≤ (RHTower.xiSimpleCriticalZeroCount T : ℝ))
    (hu : AEStronglyMeasurable u) (heven : ∀ x, u (-x) = u x) (ha : 0 < a) (hb : 2 / p < b)
    (hC : ∀ x, ‖u x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|)))
    (hvan : ∀ γ : ℝ, 0 < γ → RHTower.xi (1 / 2 + γ * I) = 0 →
      (analyticOrderAt RHTower.xi (1 / 2 + γ * I)).toNat = 1 →
      RHTower.sourceTransform u γ = 0) :
    u =ᵐ[volume] 0 := by
  have hb0 : 0 < b := lt_trans (div_pos (by norm_num) hp0) hb
  have hms := RHTower.measurableMomentSource_of_doubleExp hu ha hb0 hC
  have hHd := hms.differentiable_sourceTransform
  have hint_u : Integrable u := (hms.moment 0).mono' hu (Eventually.of_forall fun x => by simp)
  by_cases hH : ∀ z, RHTower.sourceTransform u z = 0
  · exact RHTower.ae_eq_zero_of_sourceTransform_eq_zero hint_u hH
  exfalso
  push Not at hH
  obtain ⟨c, hc⟩ := hH
  have hπ := Real.pi_pos
  have hbp : 2 < b * p := (div_lt_iff₀ hp0).mp hb
  set δ := p / Real.pi - 2 / (Real.pi * b) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef, sub_pos, div_lt_div_iff₀ (by positivity) hπ]
    nlinarith
  set η := min (min (1 / 10) (p / 2)) (δ / 4) with hηdef
  have hη0 : 0 < η := lt_min (lt_min (by norm_num) (by positivity)) (by linarith)
  have hη10 : η ≤ 1 / 10 := (min_le_left _ _).trans (min_le_left _ _)
  have hηp : η ≤ p / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hηδ : η ≤ δ / 4 := min_le_right _ _
  obtain ⟨T₁, hT₁⟩ := hprop η hη0
  obtain ⟨T₂, hT₂4, hN⟩ := RHTower.exists_xiZeroCount_close η hη0
  set κ := 2 * ((p - η) * (1 / (2 * Real.pi) - η)) with hκdef
  have hπ3 : 3 < Real.pi := Real.pi_gt_three
  have hκ : 2 / (Real.pi * b) < κ := by
    have h1 : κ = p / Real.pi - 2 * p * η - η / Real.pi + 2 * η ^ 2 := by
      rw [hκdef]; field_simp; ring
    have h2 : η / Real.pi ≤ η / 3 := div_le_div_of_nonneg_left hη0.le (by norm_num) hπ3.le
    have h3 : 2 * p * η ≤ 2 * η := by nlinarith
    nlinarith
  refine RHTower.false_of_capacity hu ha hb0 hC hc (κ := κ) (K := ‖c‖)
    (T₀ := max (max T₁ T₂) 1) (norm_nonneg _) hκ (le_max_right _ _) fun T hT => ?_
  have hT1 : T₁ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hT2 : T₂ ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hTone : 1 ≤ T := (le_max_right _ _).trans hT
  have hsimple := hT₁ T hT1
  have hNT := (abs_le.mp (hN T hT2)).1
  rw [← RHTower.xiPosZeroCount_eq_xiZeroCount (by linarith)] at hNT
  push_cast at hNT
  have hcount := RHTower.two_mul_xiSimpleCriticalZeroCount_le_finsum_divisor hHd ⟨c, hc⟩
    (RHTower.sourceTransform_neg_of_even heven) hvan c (T := T) (r := T + ‖c‖) le_rfl
  have hpos1 : 0 ≤ p - η := by linarith
  have hpos2 : 0 ≤ 1 / (2 * Real.pi) - η := by
    have : 1 / 10 < 1 / (2 * Real.pi) := by
      rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith [Real.pi_lt_d2]
    linarith
  have hlow : (1 / (2 * Real.pi) - η) * (T * Real.log T) ≤ (RHTower.xiPosZeroCount T : ℝ) := by
    linarith
  calc κ * (T * Real.log T) = 2 * ((p - η) * ((1 / (2 * Real.pi) - η) * (T * Real.log T))) := by
        rw [hκdef]; ring
    _ ≤ 2 * ((p - η) * (RHTower.xiPosZeroCount T : ℝ)) := by gcongr
    _ ≤ 2 * (RHTower.xiSimpleCriticalZeroCount T : ℝ) := by linarith
    _ ≤ _ := hcount

/-- **Unconditional Montgomery–Taylor Upgrade of the Real-Divisor-Only Capacity Threshold (`b > 2 / HD(1)`).**
Because `HD(1) ≥ 1681/2500 > 2/3`, the real-divisor-only uniqueness theorem of
`ThetaTailSimpleCriticalThreshold` holds **unconditionally** for all `b > 2 / HD(1)` (in particular
for all `b > 5000 / 1681 = 2.9744…`, including the previously open boundary `b = 3`). -/
theorem ae_eq_zero_of_doubleExp_simpleCritical_montgomeryTaylor
    {u : ℝ → ℂ} {a b C : ℝ} (hu : AEStronglyMeasurable u) (heven : ∀ x, u (-x) = u x)
    (ha : 0 < a) (hb : 2 / Zeta23.ThmD.HD 1 < b)
    (hC : ∀ x, ‖u x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|)))
    (hvan : ∀ γ : ℝ, 0 < γ → RHTower.xi (1 / 2 + γ * I) = 0 →
      (analyticOrderAt RHTower.xi (1 / 2 + γ * I)).toNat = 1 →
      RHTower.sourceTransform u γ = 0) :
    u =ᵐ[volume] 0 := by
  have hHD_pos : 0 < Zeta23.ThmD.HD 1 := lt_of_lt_of_le (by norm_num) RHTower.HD_one_ge
  have hHD_le1 : Zeta23.ThmD.HD 1 ≤ 1 := le_trans HD_one_lt_three_quarters.le (by norm_num)
  exact ae_eq_zero_of_doubleExp_simpleCritical_of_proportion hHD_pos hHD_le1
    RHTower.lamzouri_montgomeryTaylor_simpleCritical_epsilon hu heven ha hb hC hvan

/-- **Unconditional Resolution of the Boundary `b = 3` (`b ≥ 3` and `b > 5000/1681`) in
`ThetaTailSimpleCriticalThreshold`.**
Since `2 / HD(1) ≤ 5000 / 1681 < 3`, any even measurable `u` obeying
`|u(x)| ≤ C exp(−a e^{b|x|})` with `b ≥ 3` (or `b > 5000/1681`) whose transform vanishes at every
simple critical zero of `ξ` vanishes almost everywhere (and identically if `u` is continuous). -/
theorem ae_eq_zero_of_doubleExp_simpleCritical_ge_three
    {u : ℝ → ℂ} {a b C : ℝ} (hu : AEStronglyMeasurable u) (heven : ∀ x, u (-x) = u x)
    (ha : 0 < a) (hb : 5000 / 1681 < b)
    (hC : ∀ x, ‖u x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|)))
    (hvan : ∀ γ : ℝ, 0 < γ → RHTower.xi (1 / 2 + γ * I) = 0 →
      (analyticOrderAt RHTower.xi (1 / 2 + γ * I)).toNat = 1 →
      RHTower.sourceTransform u γ = 0) :
    u =ᵐ[volume] 0 := by
  have hHD := RHTower.HD_one_ge
  have hHD_pos : 0 < Zeta23.ThmD.HD 1 := lt_of_lt_of_le (by norm_num) hHD
  have hdiv : 2 / Zeta23.ThmD.HD 1 ≤ 5000 / 1681 := by
    rw [div_le_iff₀ hHD_pos]
    linarith
  exact ae_eq_zero_of_doubleExp_simpleCritical_montgomeryTaylor hu heven ha
    (lt_of_le_of_lt hdiv hb) hC hvan

/-- Pointwise form at `b = 3` (and all `b ≥ 3`) for continuous `u`, unconditionally. -/
theorem eq_zero_of_doubleExp_simpleCritical_ge_three_of_continuous
    {u : ℝ → ℂ} {a b C : ℝ} (hu : Continuous u) (heven : ∀ x, u (-x) = u x)
    (ha : 0 < a) (hb : 3 ≤ b)
    (hC : ∀ x, ‖u x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|)))
    (hvan : ∀ γ : ℝ, 0 < γ → RHTower.xi (1 / 2 + γ * I) = 0 →
      (analyticOrderAt RHTower.xi (1 / 2 + γ * I)).toNat = 1 →
      RHTower.sourceTransform u γ = 0) :
    u = 0 :=
  (hu.ae_eq_iff_eq volume continuous_const).mp
    (ae_eq_zero_of_doubleExp_simpleCritical_ge_three hu.aestronglyMeasurable heven ha
      (by linarith) hC hvan)

/-- **Three-Quarters Upgrade of the Real-Divisor-Only Capacity Threshold (`b > 8/3` under `PrimeSurplusFourThirds`).** -/
theorem ae_eq_zero_of_doubleExp_simpleCritical_of_primeSurplusFourThirds
    (h : RHTower.PrimeSurplusFourThirds)
    {u : ℝ → ℂ} {a b C : ℝ} (hu : AEStronglyMeasurable u) (heven : ∀ x, u (-x) = u x)
    (ha : 0 < a) (hb : 8 / 3 < b)
    (hC : ∀ x, ‖u x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|)))
    (hvan : ∀ γ : ℝ, 0 < γ → RHTower.xi (1 / 2 + γ * I) = 0 →
      (analyticOrderAt RHTower.xi (1 / 2 + γ * I)).toNat = 1 →
      RHTower.sourceTransform u γ = 0) :
    u =ᵐ[volume] 0 := by
  have hprop : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 4 - ε) * (RHTower.xiPosZeroCount T : ℝ) ≤ (RHTower.xiSimpleCriticalZeroCount T : ℝ) := by
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := RHTower.zeta_three_quarters_simple_of_prime_surplus h ε hε
    refine ⟨T₀, fun T hT => ?_⟩
    simpa only [RHTower.zeta23_Ncount_zero_eq_xiPosZeroCount,
      RHTower.zeta23_N0simple_zero_eq_xiSimpleCriticalZeroCount] using hT₀ T hT
  exact ae_eq_zero_of_doubleExp_simpleCritical_of_proportion (p := 3 / 4) (by norm_num)
    (by norm_num) hprop hu heven ha (by linarith) hC hvan

/-! ## 6. Master Theorem Answering Question 4 -/

/-- **Definite Answer to Question 4: What a Gram Functional Certifies Without Effectivity.**
1. **Universal Matrix-Functional Classification (`c = 2` and `c = 3`):**
   On `extremalDiag s₁ d₂` (`N = s₁ + 2d₂`, `tr = N`, `‖·‖_F² = κN`), `doubleZeroBlockData s₁ d₂`
   and `coalescedPairBlockData s₁ d₂` have the identical Gram matrix, so `c = 2` uniquely achieves
   the maximum lower bound `(2 − κ)N = s₁` on `s₁`, `s₁ + s₂`, and `N_on`, and the minimum upper
   bound `((κ − 1)/2)N = d₂` on `s₂` and `p`, while `c = 3` achieves the maximum lower bound
   `((3 − κ)/2)N = s₁ + d₂` on distinct zeros `N_d`.
2. **Below Pair Correlation (`λ ≤ 1`):**
   A flat-top window is capped at `2 − kfun 1 = 2/3` (`c = 2`) and `Gfun 1 = 5/6` (`c = 3`),
   whereas the Montgomery–Taylor optimal window profile `v*(s) = cos(√2 s)` strictly beats both
   unconditionally (`2/3 < 1681/2500 ≤ HD 1 < 3/4` and `5/6 < 4181/5000 ≤ GD 1`), upgrading the
   dyadic off-line moment to `(66/1000)T` and resolving the `b = 3` real-divisor uniqueness
   threshold (`b > 5000/1681 < 3`).
3. **Reaching `3/4` (`κ = 5/4`):**
   Since `HD 1 < 3/4`, reaching `3/4` requires either:
   * **Route I (Zero-Side Spectral Slack):** `λ ∈ [3/4, 1]` with `zeroSideSlack(λ, T) ≥ (3/4 − H(λ))N(T, 2T)`
     (refuted on `(0, 3/4)` by the grid ceiling `d(T) ≤ (λ + ε)N(T, 2T)`), or
   * **Route II (Prime-Side Surplus / Trans-Threshold Pair Correlation):** `PrimeSurplusFourThirds`
     at `λ = 4/3` (`43/36 + 1/18 = 5/4`), or pair correlation `F ≤ B` with `B ≤ 2` for a single
     flat-top window (`certOpt B ≥ 3/4 ↔ B ≤ 2`) and `B ≤ 117/41` (in particular `B ≤ 14/5`) for
     the two-window mixture (`2 − mixQ B (7/16) ≥ 3/4 ↔ B ≤ 117/41`), which upgrades the dyadic and
     cumulative off-line moments to `(57/1000)` and the uniqueness threshold to `b > 8/3`. -/
theorem what_a_gram_functional_certifies_without_effectivity :
    ((2 / 3 : ℝ) < Zeta23.ThmD.HD 1 ∧
      (1681 / 2500 : ℝ) ≤ Zeta23.ThmD.HD 1 ∧
      Zeta23.ThmD.HD 1 < 3 / 4 ∧
      (5 / 6 : ℝ) < Zeta23.ThmD.GD 1 ∧
      (4181 / 5000 : ℝ) ≤ Zeta23.ThmD.GD 1) ∧
    (∀ B : ℝ, (3 / 4 ≤ 2 - RHTower.mixQ B (7 / 16) ↔ B ≤ 117 / 41)) ∧
    (2 - RHTower.mixQ 2 (1 / 3) = 1513 / 1944) ∧
    (∀ᶠ T in atTop, RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤ 66 / 1000 * T) ∧
    (RHTower.PrimeSurplusFourThirds →
      (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0simple 0 T) ∧
      (∀ᶠ T in atTop, RHTower.windowTail 0 (T + 1) (2 * T - 1) ≤ 57 / 1000 * T) ∧
      (∀ᶠ V in atTop, RHTower.offLineMoment V ≤ 57 / 1000 * V)) := by
  refine ⟨⟨two_thirds_lt_HD_one.1, RHTower.HD_one_ge, HD_one_lt_three_quarters,
      five_sixths_lt_GD_one.1, five_sixths_lt_GD_one.2.1⟩,
    fun B => (mixQ_ge_three_quarters_iff_le_oneHundredSeventeen_div_fortyOne B).2.1,
    mixQ_at_two_one_third.1,
    eventually_dyadicWindowTail_le_sixtySix_thousandths.2,
    fun h => ⟨RHTower.zeta_three_quarters_simple_of_prime_surplus h,
      (offLineMoment_fiftySeven_thousandths_of_primeSurplusFourThirds h).2.1,
      (offLineMoment_fiftySeven_thousandths_of_primeSurplusFourThirds h).2.2⟩⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end

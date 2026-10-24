import GaloisForLFunctions.BezoutValuationIncidence.SuperlinearObservabilityHorizonAtArbitraryPhase
import GaloisForLFunctions.BezoutValuationIncidence.SelbergSupportExactRecurrenceComplexity
import GaloisForLFunctions.BezoutValuationIncidence.UniformLagWindowCovarianceAtQuadraticOrder
import GaloisForLFunctions.BezoutValuationIncidence.StableRelationSpectrumFromPolynomialWindows
import GaloisForLFunctions.BezoutValuationIncidence.RelationSpectrumDeterminesTheRowUpToTheCompanion
import GaloisForLFunctions.BezoutValuationIncidence.MomentSignVisibilityAndZeroProductRelations
import GaloisForLFunctions.BezoutValuationIncidence.TheMoebiusEnergyTransfersAtEverySuperlinearHorizon
import GaloisForLFunctions.BezoutValuationIncidence.SharedBirthPronicCellCovariance
import GaloisForLFunctions.BezoutValuationIncidence.PronicPositivityOfTheVasyuninPrimeKernel
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SmallHorizonDefectSignAndMontgomeryVaughanWindowLaws

/-!
# Observation Constants, Quantitative Recovery Laws, and Strict Positivity of the Energy-Centered Pronic Gram

This module establishes the quantitative observation constants, stability laws, cofinal Möbius error
rates, and strict positive-definiteness theorems of the Bézout valuation incidence programme:

1. **Exact Arbitrary-Phase Observability Horizon and LCM-Reduced Alternating-Grid Lower Bound (§1):**
   - We define `arbitraryPhaseObservabilityHorizon N` as the infimal window length `L ∈ ℕ` such that
     for every phase `A` and row `c`, vanishing of `sieveSeq N c` on `[A, A + L)` forces `c(d) = 0`
     for all `d ∈ [1, N]`.
   - It is attained for every `N ∈ ℕ` and satisfies
     `arbitraryPhaseObservabilityHorizon N ≤ cyclotomicIncidenceOrder N ≤ N(N + 1)/2`
     (`arbitraryPhaseObservabilityHorizon_spec`).
   - Replacing the factorial `M = (2^{m+1})!` in the alternating-grid witness by the least common
     multiple `lcmGridModulus (m + 1) = lcm_{1 ≤ q < 2^{m+1}} q` shows that for every `m, N ∈ ℕ`
     with `(m + 2) · lcm(1, …, 2^{m+1} - 1) · (1 + 2^{m+1}) ≤ N`, some nonzero row has vanishing
     response on `m N` consecutive integers (`exists_zero_response_window_lcm`), so
     `m N < arbitraryPhaseObservabilityHorizon N` (`mul_lt_arbitraryPhaseObservabilityHorizon_of_lcm_le`)
     and `arbitraryPhaseObservabilityHorizon N / N → ∞` as `N → ∞`
     (`tendsto_arbitraryPhaseObservabilityHorizon_div_atTop`).

2. **Optimal Window Sandwich Constant in `[Φ(N) - 2, N(N - 1)]` and Montgomery–Vaughan Sharpening of
   Window-to-Spectrum Recovery (§2):**
   - The optimal window sandwich constant `optimalWindowSandwichConstant N` is attained and satisfies
     `N²/8 + N - (N/2) H_N - 2 ≤ Φ(N) - 2 ≤ optimalWindowSandwichConstant N ≤ N(N - 1)`
     (`optimalWindowSandwichConstant_quadratic_brackets`).
   - Using the Montgomery–Vaughan lag-covariance bound `abs_window_lag_covariance_sub_le_mv`, every
     normalized window covariance is within `N(N - 1) V(c) / K` of the complete-period covariance
     (`abs_windowLagCovariance_sub_le_mv`), halving the `(2N² - 1)` constant of
     `UniformLagWindowCovarianceAtQuadraticOrder` and recovering every Selberg energy `Y(q)²`
     (`2 ≤ q ≤ N`) from a single window at unknown phase within
     `H_N² N(N - 1) V(c) / K ≤ (1 + log N)² N(N - 1) V(c) / K`
     (`abs_lagSpectrumReadout_window_sub_le_mv`).

3. **Quantitative Stability for Rows Approximately Equal in Degrees 5 and 6 (§3):**
   - For every odd mode `q ∈ [1, N]`, the zero-product 5-tuple `![ζ, ζ, ζ^{q-2}, ζ, ζ⁻¹]` isolates
     `Y_c(q)⁵` directly in the degree-5 relation spectrum (`exists_zeroProductTuple_five_odd_pow`),
     and the exact algebraic identity
     `16(x⁵ - y⁵) - (x - y)⁵ = 5(x - y)(x + y)²((x + y)² + 2(x - y)²)` gives the unconditional
     signed fifth-root stability bound
     `|Y_c(q) - Y_e(q)|⁵ ≤ 16 √(∑_{ζ ∈ Z_{N,5}} (A_c(ζ) - A_e(ζ))²)`
     (`abs_selbergMultiplesCoord_sub_pow_five_le_of_odd`,
     `abs_selbergMultiplesCoord_sub_pow_five_le_of_windows_five`) with no anchor hypothesis.
   - When both rows carry a unit top-order coordinate and have degree-5 and degree-6 translated
     moments within `δ³` (`0 ≤ δ ≤ 1`), either `e` is within `2δ` in every Selberg coordinate and
     within `2 Φ(N) δ` in every response value of `c`, or of `companion N c`
     (`exists_self_or_companion_coord_and_response_error`), making the exact degree-5/6
     classification `sameRelationSpectrum_five_six_iff` quantitative.

4. **Explicit Quantitative Error Rates in the Cofinal Möbius Laws (§4):**
   - Splitting the harmonic-fibre expansion of `γ_t = cofinalBandSlope t` at any cutoff `J ≥ 1` with
     `2(J + 1) ≤ t` yields the explicit three-term quantitative rate
     `|γ_t - κ| ≤ C (J + 1)² / t + C (1 + log t) / (1 + log (J + 1))⁴ + C / (1 + log (J + 1))²`
     (`exists_abs_cofinalBandSlope_sub_cofinalMobiusSlope_le`).

5. **Shared-Birth Pronic Cell Covariance Bounds and Strict Positive Definiteness of `G^{ec}` and the
   Vasyunin Prime Kernel (§5):**
   - Every shared-birth unit-gap cell covariance satisfies
     `0 ≤ sharedBirthUnitGapCovariance g l offset ≤ 2 / (l + offset)`
     (`sharedBirthUnitGapCovariance_le_inv`).
   - For every cutoff `N ∈ ℕ` and row `c : ℕ → ℝ`, `sieveEnergyCenteredPronicGramForm N c = 0` holds
     if and only if `Y_{N,c}(q) = 0` for all `q ∈ [2, N]` (`sieveEnergyCenteredPronicGramForm_eq_zero_iff`).
     Consequently, for **every** finite set `S` of moduli `≥ 2` (and in particular every finite set
     of primes) and every weight `x : ℕ → ℝ`, the energy-centered pronic Gram `G^{ec}` and the
     Vasyunin prime kernel `K(p, q)` are **strictly positive definite**:
     `0 < ∑_{p,q ∈ S} x(p) x(q) G^{ec}(p, q) ↔ ∃ p ∈ S, x(p) ≠ 0`
     (`sum_sum_mul_pmRamanujanEnergyCenteredGram_pos_iff`,
     `sum_sum_mul_vasyuninPrimeKernel_pos_iff`), and the rank-1 von Mangoldt lower bound
     `(∑_{e=2}^N Λ(e) Y(e))² ≤ sievePronicDiscrepancyGramForm N c` is a **strict inequality** for
     every row of positive variance (`vonMangoldt_sum_sq_lt_sievePronicDiscrepancyGramForm_iff`).
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.TransHorizonIncidenceMechanics
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Arbitrary-Phase Observability Horizon and LCM-Reduced Alternating-Grid Lower Bound -/

/-- A window length `L ∈ ℕ` is an **arbitrary-phase observability horizon** at level `N` if for
every phase `A ∈ ℕ` and every row `c : ℕ → ℝ`, vanishing of the response `sieveSeq N c` on the `L`
consecutive integers `[A, A + L)` forces `c(d) = 0` for all `d ∈ [1, N]`. -/
def IsArbitraryPhaseObservabilityHorizon (N L : ℕ) : Prop :=
  ∀ (A : ℕ) (c : ℕ → ℝ),
    (∀ k ∈ Finset.Ico A (A + L), sieveSeq N c k = 0) → ∀ d ∈ Finset.Icc 1 N, c d = 0

/-- The **exact arbitrary-phase observability horizon** at level `N`: the least window length `L`
that observes every level-`N` row at every phase. -/
def arbitraryPhaseObservabilityHorizon (N : ℕ) : ℕ :=
  sInf {L : ℕ | IsArbitraryPhaseObservabilityHorizon N L}

/-- The cyclotomic incidence order `Φ(N) = ∑_{q ≤ N} φ(q)` is an arbitrary-phase observability
horizon at every level `N`. -/
theorem isArbitraryPhaseObservabilityHorizon_cyclotomic (N : ℕ) :
    IsArbitraryPhaseObservabilityHorizon N (cyclotomicIncidenceOrder N) :=
  fun A c hwin => (sieveSeq_window_eq_zero_iff N A c).mp hwin

/-- Monotonicity of arbitrary-phase observability horizons in the window length. -/
theorem isArbitraryPhaseObservabilityHorizon_mono {N L L' : ℕ} (hLL' : L ≤ L')
    (hL : IsArbitraryPhaseObservabilityHorizon N L) :
    IsArbitraryPhaseObservabilityHorizon N L' :=
  fun A c hwin => hL A c fun k hk =>
    hwin k (Finset.Ico_subset_Ico le_rfl (Nat.add_le_add_left hLL' A) hk)

/-- **Attainment and Cyclotomic Upper Bound (`arbitraryPhaseObservabilityHorizon_spec`):**
For every `N ∈ ℕ`, `arbitraryPhaseObservabilityHorizon N` is itself an arbitrary-phase
observability horizon, is a lower bound for all such horizons, and satisfies
`arbitraryPhaseObservabilityHorizon N ≤ Φ(N)` and `2 · arbitraryPhaseObservabilityHorizon N ≤ N(N+1)`. -/
theorem arbitraryPhaseObservabilityHorizon_spec (N : ℕ) :
    IsArbitraryPhaseObservabilityHorizon N (arbitraryPhaseObservabilityHorizon N) ∧
      (∀ L : ℕ, IsArbitraryPhaseObservabilityHorizon N L →
        arbitraryPhaseObservabilityHorizon N ≤ L) ∧
      arbitraryPhaseObservabilityHorizon N ≤ cyclotomicIncidenceOrder N ∧
      2 * arbitraryPhaseObservabilityHorizon N ≤ N * (N + 1) := by
  let S : Set ℕ := {L : ℕ | IsArbitraryPhaseObservabilityHorizon N L}
  have hne : S.Nonempty := ⟨cyclotomicIncidenceOrder N,
    isArbitraryPhaseObservabilityHorizon_cyclotomic N⟩
  have hmem : sInf S ∈ S := Nat.sInf_mem hne
  have hle : ∀ L : ℕ, IsArbitraryPhaseObservabilityHorizon N L →
      arbitraryPhaseObservabilityHorizon N ≤ L :=
    fun L hL => Nat.sInf_le hL
  have hcyc : arbitraryPhaseObservabilityHorizon N ≤ cyclotomicIncidenceOrder N :=
    hle _ (isArbitraryPhaseObservabilityHorizon_cyclotomic N)
  refine ⟨hmem, hle, hcyc, ?_⟩
  exact (Nat.mul_le_mul_left 2 hcyc).trans (two_mul_cyclotomicIncidenceOrder_le N)

/-- The LCM grid modulus `M_m = lcm_{1 ≤ q < 2^m} q`, which absorbs every positive difference
between binary slopes `< 2^m` without the factorial blowup `(2^m)!`. -/
def lcmGridModulus (m : ℕ) : ℕ :=
  (Finset.Ico 1 (2 ^ m)).lcm id

theorem lcmGridModulus_pos (m : ℕ) : 0 < lcmGridModulus m := by
  unfold lcmGridModulus
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [Finset.lcm_eq_zero_iff] at h
  obtain ⟨q, hq, hq0⟩ := h
  have := (Finset.mem_Ico.mp hq).1
  simp only [id_eq] at hq0
  omega

theorem dvd_lcmGridModulus {m q : ℕ} (hq0 : 0 < q) (hq : q < 2 ^ m) :
    q ∣ lcmGridModulus m :=
  Finset.dvd_lcm (Finset.mem_Ico.mpr ⟨hq0, hq⟩)

/-- **LCM-Reduced Alternating-Grid Witness (`exists_zero_response_window_lcm`):**
For every `m, N ∈ ℕ` with `(m + 2) · lcm(1, …, 2^{m+1} - 1) · (1 + 2^{m+1}) ≤ N`, there exist a
phase `A` and a nonzero level-`N` row `c` whose response vanishes on `[A, A + m N)`. -/
theorem exists_zero_response_window_lcm (m N : ℕ)
    (hN : (m + 2) * (lcmGridModulus (m + 1) * (1 + 2 ^ (m + 1))) ≤ N) :
    ∃ (A : ℕ) (c : ℕ → ℝ), (∃ d ∈ Finset.Icc 1 N, c d ≠ 0) ∧
      ∀ k ∈ Finset.Ico A (A + m * N), sieveSeq N c k = 0 := by
  set M := lcmGridModulus (m + 1)
  set K := M * 2 ^ (m + 1) with hK
  have hM0 : 0 < M := lcmGridModulus_pos (m + 1)
  have hN1 : 1 ≤ N := by
    have : 1 ≤ (m + 2) * (M * (1 + 2 ^ (m + 1))) := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero hM0.ne' (by positivity)))
    omega
  set D := 1 + (N - 1) / M * M with hDdef
  have hDN : D ≤ N := by have := Nat.div_mul_le_self (N - 1) M; omega
  have hND : N < D + M := by have := Nat.lt_div_mul_add (a := N - 1) hM0; omega
  have hcop : Nat.Coprime D M := by
    rw [hDdef, mul_comm, Nat.coprime_add_mul_left_left]
    exact Nat.coprime_one_left M
  have hNK : (m + 2) * (M + K) ≤ N := by
    have : M * (1 + 2 ^ (m + 1)) = M + K := by rw [hK]; ring
    rw [← this]; exact hN
  have hlarge : (m + 1 + 1) * K < D := by nlinarith
  have hdata : GridData (m + 1) D M :=
    { dvd := fun q hq hq' => dvd_lcmGridModulus hq hq'
      pos := hM0
      coprime := hcop
      large := hlarge }
  obtain ⟨A, hA⟩ := hdata.exists_phase
  refine ⟨A, gridRow (m + 1) D M, ⟨D, Finset.mem_Icc.mpr ⟨by omega, hDN⟩, by
    rw [gridRow_top hdata]; exact one_ne_zero⟩, fun k hk => ?_⟩
  apply gridRow_response_eq_zero hdata hDN hA
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
  refine Finset.mem_Ico.mpr ⟨hk1, lt_of_lt_of_le hk2 (Nat.add_le_add_left ?_ A)⟩
  have hKD : K ≤ D := (Nat.le_mul_of_pos_left K (by omega : 0 < m + 1 + 1)).trans hlarge.le
  obtain ⟨E, hE⟩ : ∃ E, D = E + K := ⟨D - K, by omega⟩
  rw [← hK, hE, Nat.add_sub_cancel]
  have h1 : N + 1 ≤ E + M + K := by omega
  have h2 := Nat.mul_le_mul_left (m + 1) h1
  nlinarith

/-- **Superlinear Lower Bound on `arbitraryPhaseObservabilityHorizon`
(`mul_lt_arbitraryPhaseObservabilityHorizon_of_lcm_le`):**
Whenever `(m + 2) · lcm(1, …, 2^{m+1} - 1) · (1 + 2^{m+1}) ≤ N`, the exact arbitrary-phase
observability horizon strictly exceeds `m N`. -/
theorem mul_lt_arbitraryPhaseObservabilityHorizon_of_lcm_le (m N : ℕ)
    (hN : (m + 2) * (lcmGridModulus (m + 1) * (1 + 2 ^ (m + 1))) ≤ N) :
    m * N < arbitraryPhaseObservabilityHorizon N := by
  by_contra hle
  push Not at hle
  have hobs := isArbitraryPhaseObservabilityHorizon_mono hle
    (arbitraryPhaseObservabilityHorizon_spec N).1
  obtain ⟨A, c, ⟨d, hd, hcd⟩, hz⟩ := exists_zero_response_window_lcm m N hN
  exact hcd (hobs A c hz d hd)

/-- **Asymptotic Superlinearity of the Exact Arbitrary-Phase Observability Horizon
(`tendsto_arbitraryPhaseObservabilityHorizon_div_atTop`):**
As `N → ∞`, `arbitraryPhaseObservabilityHorizon N / N → ∞`. -/
theorem tendsto_arbitraryPhaseObservabilityHorizon_div_atTop :
    Tendsto (fun N : ℕ => (arbitraryPhaseObservabilityHorizon N : ℝ) / N) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro B
  obtain ⟨m, hm⟩ := exists_nat_gt (max B 0)
  have hm0 : 0 < m := by
    have : (0 : ℝ) < m := lt_of_le_of_lt (le_max_right B 0) hm
    exact_mod_cast this
  set N₀ := (m + 2) * (lcmGridModulus (m + 1) * (1 + 2 ^ (m + 1)))
  have hN₀_pos : 0 < N₀ :=
    Nat.mul_pos (by omega) (Nat.mul_pos (lcmGridModulus_pos (m + 1)) (by positivity))
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hN₀_pos hN)
  have hlt := mul_lt_arbitraryPhaseObservabilityHorizon_of_lcm_le m N hN
  have hltR : (m : ℝ) * N ≤ arbitraryPhaseObservabilityHorizon N := by exact_mod_cast hlt.le
  have hdiv : (m : ℝ) ≤ (arbitraryPhaseObservabilityHorizon N : ℝ) / N :=
    (le_div_iff₀ hN_pos).mpr hltR
  linarith [le_max_left B 0]

/-! ## §2. Optimal Window Sandwich Constant in `[Φ(N) - 2, N(N - 1)]` and Montgomery–Vaughan Sharpening of Window-to-Spectrum Recovery -/

/-- **Two-Sided Quadratic Sandwich for `optimalWindowSandwichConstant`
(`optimalWindowSandwichConstant_quadratic_brackets`):**
For every `N ≥ 2`, `optimalWindowSandwichConstant N` is an admissible window sandwich constant and
satisfies
`N²/8 + N - (N/2) H_N - 2 ≤ Φ(N) - 2 ≤ optimalWindowSandwichConstant N ≤ N(N - 1)`. -/
theorem optimalWindowSandwichConstant_quadratic_brackets {N : ℕ} (hN : 2 ≤ N) :
    IsWindowSandwichConstant N (optimalWindowSandwichConstant N) ∧
      (N : ℝ) ^ 2 / 8 + N - (N : ℝ) / 2 * (harmonic N : ℝ) - 2 ≤
        (cyclotomicIncidenceOrder N : ℝ) - 2 ∧
      (cyclotomicIncidenceOrder N : ℝ) - 2 ≤ optimalWindowSandwichConstant N ∧
      optimalWindowSandwichConstant N ≤ (N : ℝ) * ((N : ℝ) - 1) := by
  obtain ⟨hatt, hlo, hhi⟩ := optimalWindowSandwichConstant_bounds hN
  refine ⟨hatt, ?_, hlo, hhi⟩
  linarith [cyclotomicIncidenceOrder_ge N]

/-- **Montgomery–Vaughan Normalized Window Lag Covariance Bound (`abs_windowLagCovariance_sub_le_mv`):**
For every `N ≥ 2`, row `c`, phase `A`, lag `g`, and window length `K > 0`, the normalized window
lag covariance deviates from the period covariance by at most `N(N - 1) V(c) / K`, halving the
`(2N² - 1)` constant of `abs_windowLagCovariance_sub_le_two_mul_sq`. -/
theorem abs_windowLagCovariance_sub_le_mv {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) (A g : ℕ)
    {K : ℕ} (hK : 0 < K) :
    |windowLagCovariance N c A K g - TwoLagSieve.periodCovariance N c g| ≤
      ((N : ℝ) * ((N : ℝ) - 1)) * sieveVariance N c / K := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have h := abs_window_lag_covariance_sub_le_mv hN c A K g
  rw [windowLagCovariance, le_div_iff₀ hKR]
  calc |(∑ k ∈ Finset.Icc (A + 1) (A + K), (sieveSeq N c k - finiteHarmonicSum N c) *
          (sieveSeq N c (k + g) - finiteHarmonicSum N c)) / K -
          TwoLagSieve.periodCovariance N c g| * K
      = |∑ k ∈ Finset.Icc (A + 1) (A + K), (sieveSeq N c k - finiteHarmonicSum N c) *
          (sieveSeq N c (k + g) - finiteHarmonicSum N c) -
          K * TwoLagSieve.periodCovariance N c g| := by
        rw [← abs_of_pos hKR, ← abs_mul, abs_of_pos hKR, sub_mul, div_mul_cancel₀ _ hKR.ne',
          mul_comm]
    _ ≤ _ := h

/-- **Montgomery–Vaughan Sharpened Lag-Spectrum Readout from One Window
(`abs_lagSpectrumReadout_window_sub_le_mv`):**
At every phase `A` and length `K > 0`, the lag-spectrum readout of the window covariances recovers
every Selberg energy `Y(q)²` (`2 ≤ q ≤ N`) within
`H_N² N(N - 1) V(c) / K ≤ (1 + log N)² N(N - 1) V(c) / K`. -/
theorem abs_lagSpectrumReadout_window_sub_le_mv {N q : ℕ} (hN : 2 ≤ N)
    (hq : q ∈ Finset.Icc 2 N) (c : ℕ → ℝ) (A : ℕ) {K : ℕ} (hK : 0 < K) :
    |lagSpectrumReadout N q (windowLagCovariance N c A K) - selbergMultiplesCoord N c q ^ 2| ≤
      (harmonic N : ℝ) ^ 2 * (((N : ℝ) * ((N : ℝ) - 1)) * sieveVariance N c / K) ∧
    |lagSpectrumReadout N q (windowLagCovariance N c A K) - selbergMultiplesCoord N c q ^ 2| ≤
      (1 + Real.log N) ^ 2 * (((N : ℝ) * ((N : ℝ) - 1)) * sieveVariance N c / K) := by
  have h1 : |lagSpectrumReadout N q (windowLagCovariance N c A K) -
      selbergMultiplesCoord N c q ^ 2| ≤
      (harmonic N : ℝ) ^ 2 * (((N : ℝ) * ((N : ℝ) - 1)) * sieveVariance N c / K) :=
    abs_lagSpectrumReadout_sub_le hq c _ fun g _ =>
      abs_windowLagCovariance_sub_le_mv hN c A g hK
  refine ⟨h1, h1.trans ?_⟩
  have hN_nn : 0 ≤ (N : ℝ) * ((N : ℝ) - 1) := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hV_nn : 0 ≤ sieveVariance N c :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hH_nn : 0 ≤ (harmonic N : ℝ) := by
    rw [Sieve.harmonic_eq_sum_Icc]; exact Finset.sum_nonneg fun _ _ => by positivity
  have hH_le : (harmonic N : ℝ) ^ 2 ≤ (1 + Real.log N) ^ 2 :=
    pow_le_pow_left₀ hH_nn (harmonic_le_one_add_log N) 2
  exact mul_le_mul_of_nonneg_right hH_le (div_nonneg (mul_nonneg hN_nn hV_nn) (Nat.cast_nonneg K))

/-! ## §3. Quantitative Stability for Rows Approximately Equal in Degrees 5 and 6 -/

/-- Every individual relation coefficient difference `|A_c(ζ) - A_e(ζ)|` at a zero-product tuple
`ζ ∈ zeroProductTuples N m` is bounded by the `ℓ²` distance of the relation spectra. -/
theorem abs_relationCoeff_sub_le_sqrt_relation_energy {N m : ℕ} (c e : ℕ → ℝ)
    {ζ : Fin m → ℂ} (hζ : ζ ∈ zeroProductTuples N m) :
    |relationCoeff N c ζ - relationCoeff N e ζ| ≤
      Real.sqrt (∑ ξ ∈ zeroProductTuples N m, (relationCoeff N c ξ - relationCoeff N e ξ) ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt
    (Finset.single_le_sum (fun ξ _ => sq_nonneg (relationCoeff N c ξ - relationCoeff N e ξ)) hζ)

/-- **Exact Fifth-Power Stability Inequality (`abs_sub_pow_five_le_sixteen_mul_abs_pow_five_sub`):**
For all `x, y ∈ ℝ`, `|x - y|⁵ ≤ 16 |x⁵ - y⁵|`, proved via the exact algebraic identity
`16(x⁵ - y⁵) - (x - y)⁵ = 5(x - y)(x + y)²((x + y)² + 2(x - y)²)`. -/
theorem abs_sub_pow_five_le_sixteen_mul_abs_pow_five_sub (x y : ℝ) :
    |x - y| ^ 5 ≤ 16 * |x ^ 5 - y ^ 5| := by
  have hstep : ∀ u v : ℝ, v ≤ u → (u - v) ^ 5 ≤ 16 * (u ^ 5 - v ^ 5) := by
    intro u v hvu
    have hid : 16 * (u ^ 5 - v ^ 5) - (u - v) ^ 5 =
        5 * (u - v) * (u + v) ^ 2 * ((u + v) ^ 2 + 2 * (u - v) ^ 2) := by ring
    have h1 : 0 ≤ u - v := sub_nonneg.mpr hvu
    have h2 : 0 ≤ (u + v) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ (u + v) ^ 2 + 2 * (u - v) ^ 2 := by positivity
    have hprod : 0 ≤ 5 * (u - v) * (u + v) ^ 2 * ((u + v) ^ 2 + 2 * (u - v) ^ 2) := by positivity
    linarith
  rcases le_total y x with hyx | hxy
  · have h1 := hstep x y hyx
    have h2 : 0 ≤ x ^ 5 - y ^ 5 := by
      have : (0 : ℝ) ≤ (x - y) ^ 5 := pow_nonneg (sub_nonneg.mpr hyx) 5
      linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hyx), abs_of_nonneg h2]
    exact h1
  · have h1 := hstep y x hxy
    have h2 : 0 ≤ y ^ 5 - x ^ 5 := by
      have : (0 : ℝ) ≤ (y - x) ^ 5 := pow_nonneg (sub_nonneg.mpr hxy) 5
      linarith
    rw [abs_sub_comm x y, abs_sub_comm (x ^ 5) (y ^ 5),
      abs_of_nonneg (sub_nonneg.mpr hxy), abs_of_nonneg h2]
    exact h1

/-- **Isolation of `Y(q)⁵` in the Degree-5 Relation Spectrum at Every Odd Mode `q ∈ [1, N]`
(`exists_zeroProductTuple_five_odd_pow`):**
For every odd `q ∈ [1, N]`, there exists a zero-product 5-tuple `τ ∈ zeroProductTuples N 5` all of
whose components have order `q`, so that `relationCoeff N c τ = Y_c(q)⁵` for every row `c`. -/
theorem exists_zeroProductTuple_five_odd_pow {N q : ℕ} (hq : q ∈ Finset.Icc 1 N) (hodd : Odd q) :
    ∃ τ ∈ zeroProductTuples N 5, ∀ c : ℕ → ℝ,
      relationCoeff N c τ = selbergMultiplesCoord N c q ^ 5 := by
  obtain ⟨hq1, hqN⟩ := Finset.mem_Icc.mp hq
  rcases eq_or_lt_of_le hq1 with rfl | hq2
  · -- Case `q = 1`: `τ = (1, 1, 1, 1, 1)`
    let τ : Fin 5 → ℂ := fun _ => 1
    have h1_mem : (1 : ℂ) ∈ responseRoots N := by
      have h1I : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hqN⟩
      exact primitiveRoot_mem_responseRoots h1I IsPrimitiveRoot.one
    have hτ_mem : τ ∈ zeroProductTuples N 5 := by
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun _ => h1_mem, ?_⟩
      simp [τ]
    refine ⟨τ, hτ_mem, fun c => ?_⟩
    unfold relationCoeff
    simp [τ, orderOf_one]
  · -- Case `q ≥ 3` odd: `τ = ![ζ, ζ, ζ^{q-2}, ζ, ζ⁻¹]`
    have hq3 : 3 ≤ q := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hq0 : 0 < q := by omega
    have hζ := Complex.isPrimitiveRoot_exp q hq0.ne'
    set ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑q)
    have hcop : Nat.Coprime (q - 2) q := by
      have hodd2 : Odd (q - 2) := by
        obtain ⟨t, ht⟩ := hodd
        exact ⟨t - 1, by omega⟩
      have h := Nat.coprime_two_right.mpr hodd2
      have hq_eq : q = 2 + (q - 2) := by omega
      rw [Nat.Coprime]
      nth_rewrite 2 [hq_eq]
      rw [Nat.gcd_add_self_right]
      exact h
    have hξ := hζ.pow_of_coprime (q - 2) hcop
    have hζ_mem : ζ ∈ responseRoots N := primitiveRoot_mem_responseRoots hq hζ
    have hξ_mem : ζ ^ (q - 2) ∈ responseRoots N := primitiveRoot_mem_responseRoots hq hξ
    have hinv_mem : ζ⁻¹ ∈ responseRoots N := inv_mem_responseRoots hζ_mem
    let τ : Fin 5 → ℂ := fun i =>
      if i.val = 2 then ζ ^ (q - 2) else if i.val = 4 then ζ⁻¹ else ζ
    have hζ_ne : ζ ≠ 0 := hζ.ne_zero hq0.ne'
    have hprod3 : ζ * (ζ * ζ ^ (q - 2)) = 1 := by
      calc ζ * (ζ * ζ ^ (q - 2)) = ζ ^ 2 * ζ ^ (q - 2) := by ring
        _ = ζ ^ (2 + (q - 2)) := (pow_add ζ 2 (q - 2)).symm
        _ = ζ ^ q := by rw [show 2 + (q - 2) = q by omega]
        _ = 1 := hζ.pow_eq_one
    have hτ_mem : τ ∈ zeroProductTuples N 5 := by
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩
      · dsimp only [τ]
        split_ifs
        · exact hξ_mem
        · exact hinv_mem
        · exact hζ_mem
      · rw [Fin.prod_univ_five]
        dsimp only [τ]
        norm_num
        calc ζ * ζ * ζ ^ (q - 2) * ζ * ζ⁻¹
            = (ζ * (ζ * ζ ^ (q - 2))) * (ζ * ζ⁻¹) := by ring
          _ = 1 * 1 := by rw [hprod3, mul_inv_cancel₀ hζ_ne]
          _ = 1 := mul_one 1
    have hord : ∀ i : Fin 5, orderOf (τ i) = q := by
      intro i
      dsimp only [τ]
      split_ifs
      · exact hξ.eq_orderOf.symm
      · rw [orderOf_inv_of_mem_responseRoots hζ_mem, hζ.eq_orderOf]
      · exact hζ.eq_orderOf.symm
    refine ⟨τ, hτ_mem, fun c => ?_⟩
    unfold relationCoeff
    simp [hord]

/-- **Unconditional Signed Coordinate Stability at Odd Modes from the Degree-5 Relation Spectrum
(`abs_selbergMultiplesCoord_sub_pow_five_le_of_odd`):**
For every odd mode `q ∈ [1, N]` and any two rows `c, e : ℕ → ℝ` (with no anchor hypothesis),
`|Y_c(q) - Y_e(q)|⁵ ≤ 16 √(∑_{ζ ∈ Z_{N,5}} (A_c(ζ) - A_e(ζ))²)`. -/
theorem abs_selbergMultiplesCoord_sub_pow_five_le_of_odd {N q : ℕ}
    (hq : q ∈ Finset.Icc 1 N) (hodd : Odd q) (c e : ℕ → ℝ) :
    |selbergMultiplesCoord N c q ^ 5 - selbergMultiplesCoord N e q ^ 5| ≤
      Real.sqrt (∑ ζ ∈ zeroProductTuples N 5, (relationCoeff N c ζ - relationCoeff N e ζ) ^ 2) ∧
    |selbergMultiplesCoord N c q - selbergMultiplesCoord N e q| ^ 5 ≤
      16 * Real.sqrt (∑ ζ ∈ zeroProductTuples N 5,
        (relationCoeff N c ζ - relationCoeff N e ζ) ^ 2) := by
  obtain ⟨τ, hτ, hcoeff⟩ := exists_zeroProductTuple_five_odd_pow hq hodd
  have h1 := abs_relationCoeff_sub_le_sqrt_relation_energy c e hτ
  rw [hcoeff c, hcoeff e] at h1
  refine ⟨h1, (abs_sub_pow_five_le_sixteen_mul_abs_pow_five_sub _ _).trans ?_⟩
  exact mul_le_mul_of_nonneg_left h1 (by norm_num)

/-- **Unconditional Signed Odd-Mode Recovery from Degree-5 Polynomial Windows at Arbitrary Phase
(`abs_selbergMultiplesCoord_sub_pow_five_le_of_windows_five`):**
If the degree-5 window averages of `c` and `e` on windows of length `K > 0` at arbitrary
shift-dependent phases `φ v, ψ v` agree within `η`, then every odd mode `q ∈ [1, N]` satisfies
`|Y_c(q) - Y_e(q)|⁵ ≤ 16 (η + windowTransferError N 5 K c + windowTransferError N 5 K e)`. -/
theorem abs_selbergMultiplesCoord_sub_pow_five_le_of_windows_five {N q : ℕ}
    (hq : q ∈ Finset.Icc 1 N) (hodd : Odd q) {K : ℕ} (hK : 0 < K) (c e : ℕ → ℝ)
    (φ ψ : (Fin 5 → ℕ) → ℕ) {η : ℝ}
    (hobs : ∀ v ∈ Fintype.piFinset (fun _ : Fin 5 => Finset.range N.factorial),
      |windowMoment N c v (φ v) K - windowMoment N e v (ψ v) K| ≤ η) :
    |selbergMultiplesCoord N c q - selbergMultiplesCoord N e q| ^ 5 ≤
      16 * (η + (windowTransferError N 5 K c + windowTransferError N 5 K e)) := by
  have hrel := sqrt_relation_energy_le_of_windows N 5 hK c e φ ψ hobs
  have hodd_bd := (abs_selbergMultiplesCoord_sub_pow_five_le_of_odd hq hodd c e).2
  exact hodd_bd.trans (mul_le_mul_of_nonneg_left hrel (by norm_num))

/-- **Quantitative Companion-Involution Stability for Rows Approximately Equal in Degrees 5 and 6
(`exists_self_or_companion_coord_and_response_error`):**
If `c` and `e` carry a unit top-order coordinate `|Y(q_top)| ≥ 1` and have degree-5 and degree-6
translated moments within `δ³` (`0 ≤ δ ≤ 1`), then either `e` is within `2δ` in every Selberg
coordinate and `2 Φ(N) δ` in every response value of `c`, or of `companion N c`. -/
theorem exists_self_or_companion_coord_and_response_error (N : ℕ) (hN : 2 ≤ N)
    (c e : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hc : 1 ≤ |selbergMultiplesCoord N c (SieveMoments.TopAnchor.topOrder N)|)
    (he : 1 ≤ |selbergMultiplesCoord N e (SieveMoments.TopAnchor.topOrder N)|)
    (h5 : ∀ v : Fin 5 → ℕ,
      |SieveMoments.translatedMoment N c v - SieveMoments.translatedMoment N e v| ≤ δ ^ 3)
    (h6 : ∀ v : Fin 6 → ℕ,
      |SieveMoments.translatedMoment N c v - SieveMoments.translatedMoment N e v| ≤ δ ^ 3) :
    ((∀ q ∈ Finset.Icc 1 N,
        |selbergMultiplesCoord N e q - selbergMultiplesCoord N c q| ≤ 2 * δ) ∧
      (∀ n : ℕ, |sieveSeq N e n - sieveSeq N c n| ≤
        2 * (cyclotomicIncidenceOrder N : ℝ) * δ)) ∨
    ((∀ q ∈ Finset.Icc 1 N,
        |selbergMultiplesCoord N e q -
          selbergMultiplesCoord N (SieveMoments.ValuationPhase.companion N c) q| ≤ 2 * δ) ∧
      (∀ n : ℕ, |sieveSeq N e n - sieveSeq N (SieveMoments.ValuationPhase.companion N c) n| ≤
        2 * (cyclotomicIncidenceOrder N : ℝ) * δ)) := by
  have hp := SieveMoments.TopAnchor.topOrder_mem N hN
  have ha := SieveMoments.coordinate_sixth_error N c e (δ ^ 3) h6
    (SieveMoments.TopAnchor.topOrder N) hp
  have hδ3 : δ ^ 3 ≤ 2 * δ := by
    have h₁ := mul_nonneg hδ (sub_nonneg.mpr hδ1)
    have h₂ := mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hδ1)
    nlinarith only [h₁, h₂, hδ]
  have hΦ : (∑ q ∈ Finset.Icc 1 N, (q.totient : ℝ)) = cyclotomicIncidenceOrder N := by
    unfold cyclotomicIncidenceOrder; push_cast; rfl
  have hlow (q : ℕ) (hq : q ∈ Finset.Icc 1 N) (hne : q ≠ SieveMoments.TopAnchor.topOrder N) :
      |selbergMultiplesCoord N e q - selbergMultiplesCoord N c q| ≤ 2 * δ := by
    have hdepth : q.factorization 2 < (SieveMoments.TopAnchor.topOrder N).factorization 2 := by
      rw [SieveMoments.TopAnchor.topOrder_depth]
      exact SieveMoments.TopAnchor.depth_lt_top hq hne
    have hh := SieveMoments.TopAnchor.lower_error
      (selbergMultiplesCoord N c q) (selbergMultiplesCoord N e q)
      (selbergMultiplesCoord N c (SieveMoments.TopAnchor.topOrder N))
      (selbergMultiplesCoord N e (SieveMoments.TopAnchor.topOrder N))
      δ hc he hδ hδ1 ha (SieveMoments.coordinate_sixth_error N c e (δ ^ 3) h6 q hq)
      (SieveMoments.TopAnchor.lower_product_error N c e (δ ^ 3) h5 hq hp hdepth)
    simpa only [abs_sub_comm] using hh
  rcases SieveMoments.TopAnchor.upper_error
      (selbergMultiplesCoord N c (SieveMoments.TopAnchor.topOrder N))
      (selbergMultiplesCoord N e (SieveMoments.TopAnchor.topOrder N)) (δ ^ 3) hc ha with hs | hs
  · left
    have hcoord (q : ℕ) (hq : q ∈ Finset.Icc 1 N) :
        |selbergMultiplesCoord N e q - selbergMultiplesCoord N c q| ≤ 2 * δ := by
      by_cases hqtop : q = SieveMoments.TopAnchor.topOrder N
      · subst q; exact hs.trans hδ3
      · exact hlow q hq hqtop
    refine ⟨hcoord, fun n => ?_⟩
    have hh := SieveMoments.sieveSeq_error_le_totient_sum N e c (2 * δ) hcoord n
    rw [hΦ] at hh
    linarith
  · right
    have hc0 : selbergMultiplesCoord N c (SieveMoments.TopAnchor.topOrder N) ≠ 0 := by
      intro hz; rw [hz, abs_zero] at hc; linarith
    have hcoord (q : ℕ) (hq : q ∈ Finset.Icc 1 N) :
        |selbergMultiplesCoord N e q -
          selbergMultiplesCoord N (SieveMoments.ValuationPhase.companion N c) q| ≤ 2 * δ := by
      rw [SieveMoments.TopAnchor.coordinate_companion_top N hN c hc0 q hq]
      by_cases hqtop : q = SieveMoments.TopAnchor.topOrder N
      · rw [if_pos hqtop, hqtop, sub_neg_eq_add]; exact hs.trans hδ3
      · rw [if_neg hqtop]; exact hlow q hq hqtop
    refine ⟨hcoord, fun n => ?_⟩
    have hh := SieveMoments.sieveSeq_error_le_totient_sum N e
      (SieveMoments.ValuationPhase.companion N c) (2 * δ) hcoord n
    rw [hΦ] at hh
    linarith

/-! ## §4. Explicit Quantitative Error Rates in the Cofinal Möbius Laws -/

/-- For every cutoff `J ∈ ℕ`, the tail of `∑_{j > J} f(j) log(1 + 1/j)` for a sequence satisfying
`|f(j)| ≤ C / (1 + log j)⁴` is bounded by `2 C / (1 + log (J + 1))²`. -/
theorem abs_tsum_tail_mul_log_one_add_inv_le {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ X : ℕ, 1 ≤ X → |f X| ≤ C / (1 + Real.log X) ^ 4) (J : ℕ) :
    Summable (fun j : ℕ => f j * Real.log (1 + 1 / (j : ℝ))) ∧
      |(∑' j : ℕ, f j * Real.log (1 + 1 / (j : ℝ))) -
        ∑ j ∈ Finset.Icc 1 J, f j * Real.log (1 + 1 / (j : ℝ))| ≤
        2 * C / (1 + Real.log ((J : ℝ) + 1)) ^ 2 := by
  have hC0 : 0 ≤ C := by
    have h1 := hf 1 le_rfl
    rw [Nat.cast_one, Real.log_one, add_zero, one_pow, div_one] at h1
    exact (abs_nonneg _).trans h1
  have hlog_le : ∀ j : ℕ, 1 ≤ j → Real.log (1 + 1 / (j : ℝ)) ≤ (j : ℝ)⁻¹ := by
    intro j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (j : ℝ) by positivity)
    simpa [one_div] using this
  have hlog_nn : ∀ j : ℕ, 0 ≤ Real.log (1 + 1 / (j : ℝ)) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · exact Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  have hterm_le : ∀ j : ℕ, |f j * Real.log (1 + 1 / (j : ℝ))| ≤
      C * ((j : ℝ) * (1 + Real.log j) ^ 2)⁻¹ := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
      have hl : 0 ≤ Real.log j := Real.log_nonneg hjR
      have h4 : (1 + Real.log j) ^ 2 ≤ (1 + Real.log j) ^ 4 := by
        have : 1 ≤ (1 + Real.log j) ^ 2 := by nlinarith
        nlinarith
      rw [abs_mul, abs_of_nonneg (hlog_nn j)]
      calc |f j| * Real.log (1 + 1 / (j : ℝ))
          ≤ (C / (1 + Real.log j) ^ 4) * (j : ℝ)⁻¹ :=
            mul_le_mul (hf j hj) (hlog_le j hj) (hlog_nn j) (by positivity)
        _ ≤ (C / (1 + Real.log j) ^ 2) * (j : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hC0 (by positivity) h4)
              (by positivity)
        _ = C * ((j : ℝ) * (1 + Real.log j) ^ 2)⁻¹ := by field_simp
  have hsum : Summable (fun j : ℕ => f j * Real.log (1 + 1 / (j : ℝ))) :=
    Summable.of_norm_bounded (summable_inv_mul_one_add_log_sq.mul_left C) fun j => by
      rw [Real.norm_eq_abs]; exact hterm_le j
  refine ⟨hsum, ?_⟩
  have hrange : ∑ j ∈ Finset.range (J + 1), f j * Real.log (1 + 1 / (j : ℝ)) =
      ∑ j ∈ Finset.Icc 1 J, f j * Real.log (1 + 1 / (j : ℝ)) := by
    have hset : Finset.range (J + 1) = insert 0 (Finset.Icc 1 J) := by
      ext j; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert (by simp)]
    simp
  rw [← hrange, ← hsum.sum_add_tsum_nat_add (J + 1), add_sub_cancel_left]
  have hlJ : 0 ≤ Real.log ((J : ℝ) + 1) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ J := Nat.cast_nonneg J; linarith)
  have hLJ : 0 < (1 + Real.log ((J : ℝ) + 1)) ^ 2 := by positivity
  have htail_pt : ∀ i : ℕ,
      |f (i + (J + 1)) * Real.log (1 + 1 / ((i + (J + 1) : ℕ) : ℝ))| ≤
        (C / (1 + Real.log ((J : ℝ) + 1)) ^ 2) *
          (((i + (J + 1) : ℕ) : ℝ) * (1 + Real.log ((i + (J + 1) : ℕ) : ℝ)) ^ 2)⁻¹ := by
    intro i
    set j := i + (J + 1)
    have hj1 : 1 ≤ j := by omega
    have hjJ : (J : ℝ) + 1 ≤ j := by
      have : J + 1 ≤ j := by omega
      exact_mod_cast this
    have hlog_mono : Real.log ((J : ℝ) + 1) ≤ Real.log j :=
      Real.log_le_log (by positivity) hjJ
    have hsq_mono : (1 + Real.log ((J : ℝ) + 1)) ^ 2 ≤ (1 + Real.log j) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    rw [abs_mul, abs_of_nonneg (hlog_nn j)]
    calc |f j| * Real.log (1 + 1 / (j : ℝ))
        ≤ (C / (1 + Real.log j) ^ 4) * (j : ℝ)⁻¹ :=
          mul_le_mul (hf j hj1) (hlog_le j hj1) (hlog_nn j) (by positivity)
      _ = (C / (1 + Real.log j) ^ 2) * (((j : ℝ) * (1 + Real.log j) ^ 2)⁻¹) := by field_simp
      _ ≤ (C / (1 + Real.log ((J : ℝ) + 1)) ^ 2) * (((j : ℝ) * (1 + Real.log j) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hC0 hLJ hsq_mono) (by positivity)
  have hmaj_sum : Summable (fun i : ℕ =>
      (C / (1 + Real.log ((J : ℝ) + 1)) ^ 2) *
        (((i + (J + 1) : ℕ) : ℝ) * (1 + Real.log ((i + (J + 1) : ℕ) : ℝ)) ^ 2)⁻¹) :=
    ((summable_nat_add_iff (J + 1)).mpr summable_inv_mul_one_add_log_sq).mul_left _
  have htsum_inv_le : (∑' j : ℕ, ((j : ℝ) * (1 + Real.log j) ^ 2)⁻¹) ≤ 2 := by
    refine summable_inv_mul_one_add_log_sq.tsum_le_of_sum_range_le fun N => ?_
    have key : ∀ M : ℕ, ∑ j ∈ Finset.range (M + 2), ((j : ℝ) * (1 + Real.log j) ^ 2)⁻¹ ≤
        2 - (1 + Real.log ((M + 1 : ℕ) : ℝ))⁻¹ := by
      intro M
      induction M with
      | zero => norm_num [Finset.sum_range_succ]
      | succ M ih =>
        rw [Finset.sum_range_succ]
        have ht := term_le_telescope (j := M + 2) (by omega)
        rw [show M + 2 - 1 = M + 1 by omega] at ht
        push_cast at ht ih ⊢
        rw [show ((M : ℝ) + 1 + 1) = (M : ℝ) + 2 by ring]
        linarith
    rcases N with _ | _ | N
    · simp
    · norm_num
    · have h := key N
      have hpos : 0 ≤ (1 + Real.log ((N + 1 : ℕ) : ℝ))⁻¹ := by
        have : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
        have := Real.log_nonneg this
        positivity
      linarith
  have htail_tsum_le :
      (∑' i : ℕ, (((i + (J + 1) : ℕ) : ℝ) * (1 + Real.log ((i + (J + 1) : ℕ) : ℝ)) ^ 2)⁻¹) ≤ 2 := by
    have h1 := summable_inv_mul_one_add_log_sq.sum_add_tsum_nat_add (J + 1)
    have h2 : 0 ≤ ∑ j ∈ Finset.range (J + 1), ((j : ℝ) * (1 + Real.log j) ^ 2)⁻¹ :=
      Finset.sum_nonneg fun j _ => by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp
        · have := Real.log_nonneg (show (1 : ℝ) ≤ j by exact_mod_cast hj); positivity
    linarith
  have hnorm := norm_tsum_le_tsum_norm (hsum.comp_injective (add_left_injective (J + 1))).norm
  rw [Real.norm_eq_abs] at hnorm
  calc |∑' i : ℕ, f (i + (J + 1)) * Real.log (1 + 1 / ((i + (J + 1) : ℕ) : ℝ))|
      ≤ ∑' i : ℕ, ‖f (i + (J + 1)) * Real.log (1 + 1 / ((i + (J + 1) : ℕ) : ℝ))‖ := hnorm
    _ ≤ ∑' i : ℕ, (C / (1 + Real.log ((J : ℝ) + 1)) ^ 2) *
          (((i + (J + 1) : ℕ) : ℝ) * (1 + Real.log ((i + (J + 1) : ℕ) : ℝ)) ^ 2)⁻¹ :=
        ((hsum.comp_injective (add_left_injective (J + 1))).norm).tsum_le_tsum
          (fun i => by rw [Real.norm_eq_abs]; exact htail_pt i) hmaj_sum
    _ = (C / (1 + Real.log ((J : ℝ) + 1)) ^ 2) *
          ∑' i : ℕ, (((i + (J + 1) : ℕ) : ℝ) * (1 + Real.log ((i + (J + 1) : ℕ) : ℝ)) ^ 2)⁻¹ :=
        tsum_mul_left
    _ ≤ (C / (1 + Real.log ((J : ℝ) + 1)) ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left htail_tsum_le (by positivity)
    _ = 2 * C / (1 + Real.log ((J : ℝ) + 1)) ^ 2 := by ring

/-- **Explicit Quantitative Convergence Rate for the Cofinal Möbius Band Slope
(`exists_abs_cofinalBandSlope_sub_cofinalMobiusSlope_le`):**
There exists `C ≥ 0` such that for every `t ≥ 2` and every fibre cutoff `J ≥ 1` with
`2(J + 1) ≤ t`,
`|γ_t - κ| ≤ C (J + 1)² / t + C (1 + log t) / (1 + log (J + 1))⁴ + C / (1 + log (J + 1))²`. -/
theorem exists_abs_cofinalBandSlope_sub_cofinalMobiusSlope_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t J : ℕ), 1 ≤ J → 2 * (J + 1) ≤ t →
      |cofinalBandSlope t - cofinalMobiusSlope| ≤
        C * ((J : ℝ) + 1) ^ 2 / t +
          C * (1 + Real.log t) / (1 + Real.log ((J : ℝ) + 1)) ^ 4 +
          C / (1 + Real.log ((J : ℝ) + 1)) ^ 2 := by
  obtain ⟨C₀, hC₀⟩ := exists_abs_coprimePairMoebiusSigmaSum_le
  have hC₀_nn : 0 ≤ C₀ := by
    have h1 := hC₀ 1 le_rfl
    rw [Nat.cast_one, Real.log_one, add_zero, one_pow, div_one] at h1
    exact (abs_nonneg _).trans h1
  set ρ := RHTower.Sieve.squarefreeDensity
  have hρ_nn : 0 ≤ ρ := by
    dsimp only [ρ]; rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
  refine ⟨4 * ρ * C₀, by positivity, fun t J hJ1 hJt => ?_⟩
  have ht1 : 1 ≤ t := by omega
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht1
  have hJt_le : J ≤ t := by omega
  have hlJ : 0 ≤ Real.log ((J : ℝ) + 1) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ J := Nat.cast_nonneg J; linarith)
  have hlt : 0 ≤ Real.log t := Real.log_nonneg (by exact_mod_cast ht1)
  have hdecomp :
      cofinalBandSlope t - cofinalMobiusSlope =
        ρ * ((∑ j ∈ Finset.Icc 1 J, coprimePairMoebiusSigmaSum j *
              (harmonicFibre t j - Real.log (1 + 1 / (j : ℝ)))) +
            (∑ j ∈ (Finset.Icc 1 t).filter (fun j => ¬ j ≤ J),
              coprimePairMoebiusSigmaSum j * harmonicFibre t j) -
            ((∑' j : ℕ, coprimePairMoebiusSigmaSum j * Real.log (1 + 1 / (j : ℝ))) -
              ∑ j ∈ Finset.Icc 1 J, coprimePairMoebiusSigmaSum j *
                Real.log (1 + 1 / (j : ℝ)))) := by
    rw [cofinalBandSlope_eq, sum_div_eq_sum_harmonicFibre, cofinalMobiusSlope, ← mul_sub]
    congr 1
    have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 t) (fun j => j ≤ J)
      (fun j => coprimePairMoebiusSigmaSum j * harmonicFibre t j)).symm
    have hhead : (Finset.Icc 1 t).filter (fun j => j ≤ J) = Finset.Icc 1 J := by
      ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [hhead] at hsplit
    have hdiff : ∑ j ∈ Finset.Icc 1 J, coprimePairMoebiusSigmaSum j *
        (harmonicFibre t j - Real.log (1 + 1 / (j : ℝ))) =
        (∑ j ∈ Finset.Icc 1 J, coprimePairMoebiusSigmaSum j * harmonicFibre t j) -
          ∑ j ∈ Finset.Icc 1 J, coprimePairMoebiusSigmaSum j * Real.log (1 + 1 / (j : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith
  -- 1. Head bound: `j ≤ J`
  have hhead_bd :
      |∑ j ∈ Finset.Icc 1 J, coprimePairMoebiusSigmaSum j *
          (harmonicFibre t j - Real.log (1 + 1 / (j : ℝ)))| ≤
        4 * C₀ * ((J : ℝ) + 1) ^ 2 / t := by
    have hpt : ∀ j ∈ Finset.Icc 1 J,
        |coprimePairMoebiusSigmaSum j * (harmonicFibre t j - Real.log (1 + 1 / (j : ℝ)))| ≤
          4 * C₀ * ((J : ℝ) + 1) / t := by
      intro j hj
      obtain ⟨hj1, hjJ⟩ := Finset.mem_Icc.mp hj
      have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      have hlj : 0 ≤ Real.log j := Real.log_nonneg hjR
      have h14 : 1 ≤ (1 + Real.log j) ^ 4 := one_le_pow₀ (by linarith)
      have hSj : |coprimePairMoebiusSigmaSum j| ≤ C₀ :=
        (hC₀ j hj1).trans (div_le_self hC₀_nn h14)
      have hfib := abs_harmonicFibre_sub_log_le hj1 (by omega : 2 * (j + 1) ≤ t)
      have hjJ_R : (j : ℝ) + 1 ≤ (J : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hjJ 1
      rw [abs_mul]
      calc |coprimePairMoebiusSigmaSum j| * |harmonicFibre t j - Real.log (1 + 1 / (j : ℝ))|
          ≤ C₀ * (4 * ((j : ℝ) + 1) / t) :=
            mul_le_mul hSj hfib (abs_nonneg _) hC₀_nn
        _ ≤ C₀ * (4 * ((J : ℝ) + 1) / t) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) ht0.le) hC₀_nn
        _ = 4 * C₀ * ((J : ℝ) + 1) / t := by ring
    calc |∑ j ∈ Finset.Icc 1 J, coprimePairMoebiusSigmaSum j *
            (harmonicFibre t j - Real.log (1 + 1 / (j : ℝ)))|
        ≤ ∑ j ∈ Finset.Icc 1 J, 4 * C₀ * ((J : ℝ) + 1) / t :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hpt)
      _ = (J : ℝ) * (4 * C₀ * ((J : ℝ) + 1) / t) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      _ ≤ ((J : ℝ) + 1) * (4 * C₀ * ((J : ℝ) + 1) / t) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 4 * C₀ * ((J : ℝ) + 1) ^ 2 / t := by ring
  -- 2. Finite tail bound: `J < j ≤ t`
  have hftail_bd :
      |∑ j ∈ (Finset.Icc 1 t).filter (fun j => ¬ j ≤ J),
          coprimePairMoebiusSigmaSum j * harmonicFibre t j| ≤
        C₀ * (1 + Real.log t) / (1 + Real.log ((J : ℝ) + 1)) ^ 4 := by
    have hpt : ∀ j ∈ (Finset.Icc 1 t).filter (fun j => ¬ j ≤ J),
        |coprimePairMoebiusSigmaSum j * harmonicFibre t j| ≤
          (C₀ / (1 + Real.log ((J : ℝ) + 1)) ^ 4) * harmonicFibre t j := by
      intro j hj
      obtain ⟨hjI, hjJ⟩ := Finset.mem_filter.mp hj
      have hj1 := (Finset.mem_Icc.mp hjI).1
      have hj_ge : (J : ℝ) + 1 ≤ j := by
        have : J + 1 ≤ j := by omega
        exact_mod_cast this
      have hlog_le : Real.log ((J : ℝ) + 1) ≤ Real.log j :=
        Real.log_le_log (by positivity) hj_ge
      have hpow_le : (1 + Real.log ((J : ℝ) + 1)) ^ 4 ≤ (1 + Real.log j) ^ 4 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 4
      rw [abs_mul, abs_of_nonneg (harmonicFibre_nonneg t j)]
      exact mul_le_mul_of_nonneg_right
        ((hC₀ j hj1).trans (div_le_div_of_nonneg_left hC₀_nn (by positivity) hpow_le))
        (harmonicFibre_nonneg t j)
    calc |∑ j ∈ (Finset.Icc 1 t).filter (fun j => ¬ j ≤ J),
            coprimePairMoebiusSigmaSum j * harmonicFibre t j|
        ≤ ∑ j ∈ (Finset.Icc 1 t).filter (fun j => ¬ j ≤ J),
            (C₀ / (1 + Real.log ((J : ℝ) + 1)) ^ 4) * harmonicFibre t j :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hpt)
      _ ≤ ∑ j ∈ Finset.Icc 1 t,
            (C₀ / (1 + Real.log ((J : ℝ) + 1)) ^ 4) * harmonicFibre t j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ =>
            mul_nonneg (by positivity) (harmonicFibre_nonneg t j)
      _ = (C₀ / (1 + Real.log ((J : ℝ) + 1)) ^ 4) * harmonic t := by
          rw [← Finset.mul_sum, sum_harmonicFibre]
      _ ≤ (C₀ / (1 + Real.log ((J : ℝ) + 1)) ^ 4) * (1 + Real.log t) :=
          mul_le_mul_of_nonneg_left (harmonic_le_one_add_log t) (by positivity)
      _ = C₀ * (1 + Real.log t) / (1 + Real.log ((J : ℝ) + 1)) ^ 4 := by ring
  -- 3. Infinite tail bound: `j > J`
  have hitail_bd := (abs_tsum_tail_mul_log_one_add_inv_le hC₀ J).2
  rw [hdecomp, abs_mul, abs_of_nonneg hρ_nn]
  have htri :
      |(∑ j ∈ Finset.Icc 1 J, coprimePairMoebiusSigmaSum j *
            (harmonicFibre t j - Real.log (1 + 1 / (j : ℝ)))) +
          (∑ j ∈ (Finset.Icc 1 t).filter (fun j => ¬ j ≤ J),
            coprimePairMoebiusSigmaSum j * harmonicFibre t j) -
          ((∑' j : ℕ, coprimePairMoebiusSigmaSum j * Real.log (1 + 1 / (j : ℝ))) -
            ∑ j ∈ Finset.Icc 1 J, coprimePairMoebiusSigmaSum j *
              Real.log (1 + 1 / (j : ℝ)))| ≤
        4 * C₀ * ((J : ℝ) + 1) ^ 2 / t +
          C₀ * (1 + Real.log t) / (1 + Real.log ((J : ℝ) + 1)) ^ 4 +
          2 * C₀ / (1 + Real.log ((J : ℝ) + 1)) ^ 2 := by
    calc _ ≤ |(∑ j ∈ Finset.Icc 1 J, coprimePairMoebiusSigmaSum j *
                (harmonicFibre t j - Real.log (1 + 1 / (j : ℝ)))) +
              (∑ j ∈ (Finset.Icc 1 t).filter (fun j => ¬ j ≤ J),
                coprimePairMoebiusSigmaSum j * harmonicFibre t j)| +
            |(∑' j : ℕ, coprimePairMoebiusSigmaSum j * Real.log (1 + 1 / (j : ℝ))) -
              ∑ j ∈ Finset.Icc 1 J, coprimePairMoebiusSigmaSum j *
                Real.log (1 + 1 / (j : ℝ))| := abs_sub _ _
      _ ≤ |∑ j ∈ Finset.Icc 1 J, coprimePairMoebiusSigmaSum j *
              (harmonicFibre t j - Real.log (1 + 1 / (j : ℝ)))| +
          |∑ j ∈ (Finset.Icc 1 t).filter (fun j => ¬ j ≤ J),
              coprimePairMoebiusSigmaSum j * harmonicFibre t j| +
          |(∑' j : ℕ, coprimePairMoebiusSigmaSum j * Real.log (1 + 1 / (j : ℝ))) -
              ∑ j ∈ Finset.Icc 1 J, coprimePairMoebiusSigmaSum j *
                Real.log (1 + 1 / (j : ℝ))| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by linarith
  have hmul := mul_le_mul_of_nonneg_left htri hρ_nn
  have hdiff_nn :
      0 ≤ (4 * ρ * C₀ * ((J : ℝ) + 1) ^ 2 / t +
            4 * ρ * C₀ * (1 + Real.log t) / (1 + Real.log ((J : ℝ) + 1)) ^ 4 +
            4 * ρ * C₀ / (1 + Real.log ((J : ℝ) + 1)) ^ 2) -
          ρ * (4 * C₀ * ((J : ℝ) + 1) ^ 2 / t +
            C₀ * (1 + Real.log t) / (1 + Real.log ((J : ℝ) + 1)) ^ 4 +
            2 * C₀ / (1 + Real.log ((J : ℝ) + 1)) ^ 2) := by
    have hring :
        (4 * ρ * C₀ * ((J : ℝ) + 1) ^ 2 / t +
            4 * ρ * C₀ * (1 + Real.log t) / (1 + Real.log ((J : ℝ) + 1)) ^ 4 +
            4 * ρ * C₀ / (1 + Real.log ((J : ℝ) + 1)) ^ 2) -
          ρ * (4 * C₀ * ((J : ℝ) + 1) ^ 2 / t +
            C₀ * (1 + Real.log t) / (1 + Real.log ((J : ℝ) + 1)) ^ 4 +
            2 * C₀ / (1 + Real.log ((J : ℝ) + 1)) ^ 2) =
        3 * ρ * (C₀ * (1 + Real.log t) / (1 + Real.log ((J : ℝ) + 1)) ^ 4) +
          2 * ρ * (C₀ / (1 + Real.log ((J : ℝ) + 1)) ^ 2) := by ring
    rw [hring]
    positivity
  linarith [hmul, hdiff_nn]

/-! ## §5. Shared-Birth Pronic Cell Covariance Bounds and Strict Positive Definiteness of `G^{ec}` and the Vasyunin Prime Kernel -/

/-- **Universal Upper Bound on Shared-Birth Unit-Gap Cell Covariance
(`sharedBirthUnitGapCovariance_le_inv`):**
For all `g, l : ℕ+` and `offset : ℕ`,
`0 ≤ sharedBirthUnitGapCovariance g l offset ≤ 2 / (l + offset)`. -/
theorem sharedBirthUnitGapCovariance_le_inv (g l : ℕ+) (offset : ℕ) :
    0 ≤ sharedBirthUnitGapCovariance g l offset ∧
      sharedBirthUnitGapCovariance g l offset ≤ 2 / (((l : ℕ) + offset : ℕ) : ℝ) := by
  refine ⟨sharedBirthUnitGapCovariance_nonneg g l offset, ?_⟩
  let k := (l : ℕ) + offset
  let p := (g : ℕ) * (l : ℕ)
  let j := k * p / (p + 1)
  let s := (j + 1) * (p + 1)
  have hk_pos : 0 < k := by dsimp only [k]; positivity
  have hp_pos : 0 < p := by dsimp only [p]; positivity
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk_pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp_pos
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hhas : k * p < s := by
    simpa only [s, j, Nat.mul_comm] using Nat.lt_mul_div_succ (k * p) (by positivity : 0 < p + 1)
  have hhasR : (k : ℝ) * p < s := by
    have : ((k * p : ℕ) : ℝ) < (s : ℝ) := by exact_mod_cast hhas
    simpa only [Nat.cast_mul] using this
  have hjk : (k : ℝ) ≤ 2 * ((j : ℝ) + 1) := by
    have hlt2 : k * p < (2 * (j + 1)) * p := by
      calc k * p < s := hhas
        _ = (j + 1) * (p + 1) := rfl
        _ ≤ (j + 1) * (2 * p) := Nat.mul_le_mul_left (j + 1) (by omega)
        _ = (2 * (j + 1)) * p := by ring
    have hk_lt : k < 2 * (j + 1) := Nat.lt_of_mul_lt_mul_right hlt2
    have hk_le : k ≤ 2 * (j + 1) := hk_lt.le
    exact_mod_cast hk_le
  have heq := sharedBirthUnitGapCovariance_eq g l offset
  change sharedBirthUnitGapCovariance g l offset =
    if s < (k + 1) * p then
      if k * p + (l : ℕ) ≤ s then
        (((k : ℝ) + 1) * p - s) / (((j : ℝ) + 1) * p)
      else
        ((s : ℝ) - (k : ℝ) * p) * ((g : ℝ) - 1) / (((j : ℝ) + 1) * p)
    else 0 at heq
  rw [heq]
  split_ifs with hs ht
  · rw [div_le_div_iff₀ (by positivity) hkR]
    have hnum_le : ((k : ℝ) + 1) * p - s ≤ p := by linarith
    have h1 : (((k : ℝ) + 1) * p - s) * k ≤ p * k :=
      mul_le_mul_of_nonneg_right hnum_le hkR.le
    have h2 : (p : ℝ) * k ≤ 2 * (((j : ℝ) + 1) * p) := by
      calc (p : ℝ) * k ≤ p * (2 * ((j : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hjk hpR.le
        _ = 2 * (((j : ℝ) + 1) * p) := by ring
    exact h1.trans h2
  · push Not at ht
    have htR : (s : ℝ) < (k : ℝ) * p + l := by exact_mod_cast ht
    have hsub_le : (s : ℝ) - (k : ℝ) * p ≤ l := by linarith
    have hnum_le : ((s : ℝ) - (k : ℝ) * p) * ((g : ℝ) - 1) ≤ p := by
      have hg1 : (0 : ℝ) ≤ (g : ℝ) - 1 := by
        have : (1 : ℝ) ≤ g := by exact_mod_cast g.pos
        linarith
      have hlg : (l : ℝ) * ((g : ℝ) - 1) = (p : ℝ) - l := by
        dsimp only [p]; push_cast; ring
      have hl_nn : (0 : ℝ) ≤ l := Nat.cast_nonneg _
      calc ((s : ℝ) - (k : ℝ) * p) * ((g : ℝ) - 1)
          ≤ l * ((g : ℝ) - 1) := mul_le_mul_of_nonneg_right hsub_le hg1
        _ = (p : ℝ) - l := hlg
        _ ≤ p := by linarith
    rw [div_le_div_iff₀ (by positivity) hkR]
    have h1 : ((s : ℝ) - (k : ℝ) * p) * ((g : ℝ) - 1) * k ≤ p * k :=
      mul_le_mul_of_nonneg_right hnum_le hkR.le
    have h2 : (p : ℝ) * k ≤ 2 * (((j : ℝ) + 1) * p) := by
      calc (p : ℝ) * k ≤ p * (2 * ((j : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hjk hpR.le
        _ = 2 * (((j : ℝ) + 1) * p) := by ring
    exact h1.trans h2
  · positivity

/-- At `M = N!`, every modulus `d ∈ [1, N]` divides `N!`, so the prefix discrepancy vanishes
identically for every level `N` and every row `c`. -/
theorem sievePrefixDiscrepancy_factorial_eq_zero (N : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy N N.factorial c = 0 := by
  rw [sievePrefixDiscrepancy_eq_neg_sievedFractSum, sievedFractSum, neg_eq_zero]
  refine Finset.sum_eq_zero fun d hd => ?_
  obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hd1 hdN
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hfr : fractDivSeq d N.factorial = 0 := by
    unfold fractDivSeq
    rw [hk, Nat.cast_mul, mul_div_cancel_left₀ _ hd0]
    exact_mod_cast Int.fract_intCast (k : ℤ)
  rw [hfr, mul_zero]

/-- **Kernel of `sieveEnergyCenteredPronicGramForm` (`sieveEnergyCenteredPronicGramForm_eq_zero_iff`):**
For every cutoff `N ∈ ℕ` and row `c : ℕ → ℝ`, the energy-centered pronic Gram form vanishes if and
only if every Selberg coordinate `Y_{N,c}(q)` for `q ∈ [2, N]` vanishes (equivalently
`sieveVariance N c = 0`). -/
theorem sieveEnergyCenteredPronicGramForm_eq_zero_iff (N : ℕ) (c : ℕ → ℝ) :
    (sieveEnergyCenteredPronicGramForm N c = 0 ↔
      ∀ q ∈ Finset.Icc 2 N, selbergMultiplesCoord N c q = 0) ∧
    (sieveEnergyCenteredPronicGramForm N c = 0 ↔ sieveVariance N c = 0) := by
  have hiff1 : sieveEnergyCenteredPronicGramForm N c = 0 ↔
      ∀ q ∈ Finset.Icc 2 N, selbergMultiplesCoord N c q = 0 := by
    constructor
    · intro h0
      have hhas := hasSum_sieveEnergyCenteredPrefixDiscrepancy_sq_div_pronicSeq N c
      rw [h0] at hhas
      have hterm0 : ∀ M : ℕ,
          (sieveEnergyCenteredPrefixDiscrepancy N M c) ^ 2 / (pronicSeq M : ℝ) = 0 :=
        fun M => congr_fun ((hasSum_zero_iff_of_nonneg
          (fun k => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))).mp hhas) M
      have hdisc0 : ∀ M : ℕ, 1 ≤ M → sieveEnergyCenteredPrefixDiscrepancy N M c = 0 := by
        intro M hM
        have hpr : (0 : ℝ) < pronicSeq M := by
          rw [cast_pronicSeq_eq]
          have : (0 : ℝ) < M := by exact_mod_cast hM
          positivity
        have hsq := (div_eq_zero_iff.mp (hterm0 M)).resolve_right hpr.ne'
        exact sq_eq_zero_iff.mp hsq
      -- Evaluate at `M = N! ≥ 1` to see that the von Mangoldt functional vanishes
      have hfac_pos : 1 ≤ N.factorial := Nat.factorial_pos N
      have hfac := hdisc0 N.factorial hfac_pos
      rw [sieveEnergyCenteredPrefixDiscrepancy_eq_add_vonMangoldt,
        sievePrefixDiscrepancy_factorial_eq_zero, zero_add] at hfac
      -- Therefore `sievePrefixDiscrepancy N M c = 0` for all `M ≥ 1`
      have hpref0 : ∀ M ∈ Finset.Ico 1 (1 + cyclotomicIncidenceOrder N),
          sievePrefixDiscrepancy N M c = 0 := by
        intro M hM
        have hM1 : 1 ≤ M := (Finset.mem_Ico.mp hM).1
        have h := hdisc0 M hM1
        rw [sieveEnergyCenteredPrefixDiscrepancy_eq_add_vonMangoldt, hfac, add_zero] at h
        exact h
      have hvar0 : sieveVariance N c = 0 :=
        (sievePrefixDiscrepancy_window_eq_zero_iff N 1 c).mp hpref0
      unfold sieveVariance at hvar0
      intro q hq
      have hq_term := (Finset.sum_eq_zero_iff_of_nonneg
        (fun e _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))).mp hvar0 q hq
      have htot_pos : (0 : ℝ) < q.totient := by
        have hq2 := (Finset.mem_Icc.mp hq).1
        exact_mod_cast Nat.totient_pos.mpr (by omega)
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hq_term).resolve_left htot_pos.ne')
    · intro hzero
      unfold sieveEnergyCenteredPronicGramForm
      refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q _ => ?_
      rw [hzero p hp, zero_mul, zero_mul]
  refine ⟨hiff1, hiff1.trans ?_⟩
  unfold sieveVariance
  constructor
  · intro hzero
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [hzero q hq, sq, mul_zero, mul_zero]
  · intro hvar0 q hq
    have hq_term := (Finset.sum_eq_zero_iff_of_nonneg
      (fun e _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))).mp hvar0 q hq
    have htot_pos : (0 : ℝ) < q.totient := by
      have hq2 := (Finset.mem_Icc.mp hq).1
      exact_mod_cast Nat.totient_pos.mpr (by omega)
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hq_term).resolve_left htot_pos.ne')

/-- **Strict Positivity of `sieveEnergyCenteredPronicGramForm` (`sieveEnergyCenteredPronicGramForm_pos_iff`):**
For every cutoff `N ∈ ℕ` and row `c : ℕ → ℝ`, `0 < sieveEnergyCenteredPronicGramForm N c` if and
only if `Y_{N,c}(q) ≠ 0` for some `q ∈ [2, N]`. -/
theorem sieveEnergyCenteredPronicGramForm_pos_iff (N : ℕ) (c : ℕ → ℝ) :
    0 < sieveEnergyCenteredPronicGramForm N c ↔
      ∃ q ∈ Finset.Icc 2 N, selbergMultiplesCoord N c q ≠ 0 := by
  have hnn := sieveEnergyCenteredPronicGramForm_nonneg N c
  have h0 := (sieveEnergyCenteredPronicGramForm_eq_zero_iff N c).1
  constructor
  · intro hpos
    by_contra hall
    push Not at hall
    exact hpos.ne' (h0.mpr hall)
  · intro hex
    refine lt_of_le_of_ne hnn (Ne.symm fun heq => ?_)
    obtain ⟨q, hq, hne⟩ := hex
    exact hne (h0.mp heq q hq)

/-- **Strict Inequality in the Von Mangoldt Pronic Gram Lower Bound
(`vonMangoldt_sum_sq_lt_sievePronicDiscrepancyGramForm_iff`):**
For every cutoff `N ∈ ℕ` and row `c : ℕ → ℝ`, the Cauchy–Schwarz von Mangoldt lower bound
`(∑_{e=2}^N Λ(e) Y_{N,c}(e))² ≤ sievePronicDiscrepancyGramForm N c` is a **strict inequality** if
and only if `Y_{N,c}(q) ≠ 0` for some `q ∈ [2, N]`. -/
theorem vonMangoldt_sum_sq_lt_sievePronicDiscrepancyGramForm_iff (N : ℕ) (c : ℕ → ℝ) :
    (∑ e ∈ Finset.Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e) ^ 2 <
        sievePronicDiscrepancyGramForm N c ↔
      ∃ q ∈ Finset.Icc 2 N, selbergMultiplesCoord N c q ≠ 0 := by
  rw [sievePronicDiscrepancyGramForm_eq_vonMangoldt_sq_add_energyCentered,
    lt_add_iff_pos_right]
  exact sieveEnergyCenteredPronicGramForm_pos_iff N c

/-- **Strict Positive Definiteness of `pmRamanujanEnergyCenteredGram` on Every Finite Set of
Moduli `≥ 2` (`sum_sum_mul_pmRamanujanEnergyCenteredGram_pos_iff`):**
For every finite set `S ⊂ ℕ` with `∀ p ∈ S, 2 ≤ p` and every weight `x : ℕ → ℝ`:
1. `∑_{p, q ∈ S} x(p) x(q) G^{ec}(p, q) = 0 ↔ ∀ p ∈ S, x(p) = 0`, and
2. `0 < ∑_{p, q ∈ S} x(p) x(q) G^{ec}(p, q) ↔ ∃ p ∈ S, x(p) ≠ 0`. -/
theorem sum_sum_mul_pmRamanujanEnergyCenteredGram_pos_iff (S : Finset ℕ)
    (hS : ∀ p ∈ S, 2 ≤ p) (x : ℕ → ℝ) :
    (∑ p ∈ S, ∑ q ∈ S, x p * x q * pmRamanujanEnergyCenteredGram p q = 0 ↔
      ∀ p ∈ S, x p = 0) ∧
    (0 < ∑ p ∈ S, ∑ q ∈ S, x p * x q * pmRamanujanEnergyCenteredGram p q ↔
      ∃ p ∈ S, x p ≠ 0) := by
  classical
  set N := S.sup id
  have hSN : S ⊆ Finset.Icc 2 N := fun p hp =>
    Finset.mem_Icc.mpr ⟨hS p hp, Finset.le_sup (f := id) hp⟩
  let y : ℕ → ℝ := fun q => if q ∈ S then x q else 0
  let c : ℕ → ℝ := RHTower.pmRamanujanResidueCoeff y N
  have hcoord : ∀ q ∈ Finset.Icc 2 N, selbergMultiplesCoord N c q = y q := fun q hq => by
    obtain ⟨hq2, hqN⟩ := Finset.mem_Icc.mp hq
    exact RHTower.pmRamanujanResidueCoeff_multiples y (by omega) hqN
  have hform :
      sieveEnergyCenteredPronicGramForm N c =
        ∑ p ∈ S, ∑ q ∈ S, x p * x q * pmRamanujanEnergyCenteredGram p q := by
    unfold sieveEnergyCenteredPronicGramForm
    have h1 : ∀ p ∈ Finset.Icc 2 N,
        ∑ q ∈ Finset.Icc 2 N,
          selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
            pmRamanujanEnergyCenteredGram p q =
        if p ∈ S then
          ∑ q ∈ S, x p * x q * pmRamanujanEnergyCenteredGram p q
        else 0 := by
      intro p hp
      rw [hcoord p hp]
      by_cases hpS : p ∈ S
      · rw [if_pos hpS]
        dsimp only [y]
        rw [if_pos hpS]
        calc ∑ q ∈ Finset.Icc 2 N,
              x p * selbergMultiplesCoord N c q * pmRamanujanEnergyCenteredGram p q
            = ∑ q ∈ S, x p * selbergMultiplesCoord N c q *
                pmRamanujanEnergyCenteredGram p q := by
              symm
              refine Finset.sum_subset hSN fun q hq hqS => ?_
              rw [hcoord q hq]
              dsimp only [y]
              rw [if_neg hqS, mul_zero, zero_mul]
          _ = ∑ q ∈ S, x p * x q * pmRamanujanEnergyCenteredGram p q :=
              Finset.sum_congr rfl fun q hq => by
                rw [hcoord q (hSN hq)]
                dsimp only [y]
                rw [if_pos hq]
      · rw [if_neg hpS]
        dsimp only [y]
        rw [if_neg hpS]
        exact Finset.sum_eq_zero fun q _ => by ring
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
    have hfilt : (Finset.Icc 2 N).filter (fun p => p ∈ S) = S :=
      Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr hSN)
    rw [hfilt]
  have hzero_iff :
      (∀ q ∈ Finset.Icc 2 N, selbergMultiplesCoord N c q = 0) ↔ ∀ p ∈ S, x p = 0 := by
    constructor
    · intro hall p hp
      have h := hall p (hSN hp)
      rw [hcoord p (hSN hp)] at h
      dsimp only [y] at h
      rwa [if_pos hp] at h
    · intro hall q hq
      rw [hcoord q hq]
      dsimp only [y]
      by_cases hqS : q ∈ S
      · rw [if_pos hqS, hall q hqS]
      · rw [if_neg hqS]
  have heq0 :
      ∑ p ∈ S, ∑ q ∈ S, x p * x q * pmRamanujanEnergyCenteredGram p q = 0 ↔
        ∀ p ∈ S, x p = 0 := by
    rw [← hform]
    exact (sieveEnergyCenteredPronicGramForm_eq_zero_iff N c).1.trans hzero_iff
  refine ⟨heq0, ?_⟩
  have hnn := sum_sum_mul_pmRamanujanEnergyCenteredGram_nonneg S
    (fun p hp => lt_of_lt_of_le one_lt_two (hS p hp)) x
  constructor
  · intro hpos
    by_contra hall
    push Not at hall
    exact hpos.ne' (heq0.mpr hall)
  · intro hex
    refine lt_of_le_of_ne hnn (Ne.symm fun h0 => ?_)
    obtain ⟨p, hp, hne⟩ := hex
    exact hne (heq0.mp h0 p hp)

/-- **Strict Positive Definiteness of the Vasyunin Prime Kernel (`sum_sum_mul_vasyuninPrimeKernel_pos_iff`):**
For every finite set of primes `S` and every weight `x : ℕ → ℝ`, the Vasyunin prime kernel form
`∑_{p, q ∈ S} x(p) x(q) K(p, q)` vanishes if and only if `x(p) = 0` for all `p ∈ S`, and is
strictly positive if and only if `x(p) ≠ 0` for some `p ∈ S`. -/
theorem sum_sum_mul_vasyuninPrimeKernel_pos_iff (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (x : ℕ → ℝ) :
    (∑ p ∈ S, ∑ q ∈ S, x p * x q * vasyuninPrimeKernel p q = 0 ↔
      ∀ p ∈ S, x p = 0) ∧
    (0 < ∑ p ∈ S, ∑ q ∈ S, x p * x q * vasyuninPrimeKernel p q ↔
      ∃ p ∈ S, x p ≠ 0) := by
  have heq :
      ∑ p ∈ S, ∑ q ∈ S, x p * x q * vasyuninPrimeKernel p q =
        ∑ p ∈ S, ∑ q ∈ S, x p * x q * pmRamanujanEnergyCenteredGram p q :=
    Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => by
      rw [pmRamanujanEnergyCenteredGram_prime_eq_vasyuninPrimeKernel (hS p hp) (hS q hq)]
  rw [heq]
  exact sum_sum_mul_pmRamanujanEnergyCenteredGram_pos_iff S (fun p hp => (hS p hp).two_le) x

end

end GaloisForLFunctions.BezoutValuationIncidence

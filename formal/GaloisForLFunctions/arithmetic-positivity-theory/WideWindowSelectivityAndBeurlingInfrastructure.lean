import GaloisForLFunctions.«arithmetic-positivity-theory».CompactCriticalPolynomialWindowAndTemperednessBridge
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeKernelNegativeDefinite
import GaloisForLFunctions.RHTower.WeilShiftPairLandau
import GaloisForLFunctions.RHTower.BeurlingRHSensitivityThreshold
import GaloisForLFunctions.BiScaleUncertainty.PrimePowerNodeDeletionPrice

/-!
# Wide-Window Selectivity Against `ζ(s - a)ζ(s + a)`, Critical Harmonic Charge Reversal, and Beurling Infrastructure Invariance

This module resolves Open Problem §7.7 of `arithmetic-positivity-theory/README.md` by establishing
three complementary results that locate where arithmetic selectivity enters:

1. **Wide-Window Prime-Driven Failure of Weil Positivity for the Shifted Pair `ζ(s - a)ζ(s + a)`
   (`autoLaplaceReal_pos`, `sum_windowValue_le_windowSum`,
   `integral_Ioi_windowValue_mul_exp_of_large`,
   `exists_wide_windowSum_shiftedPairVonMangoldt_gt_shiftMajorant`,
   `exists_wide_shiftPair_shiftedPairVonMangoldt_neg`,
   `exists_wide_shiftPair_narrowG_shiftedPairVonMangoldt_neg`):**
   For every real shift `a ≠ 0`, every nonnegative bump `g ∈ C_c²([-1/4, 1/4])` with `∫ g ≠ 0`,
   and every horizon `L₀ ≥ 0`, there exists a wide window shift `L > max L₀ (log 2)` (at which only
   prime powers in `[e^{L - 1/2}, e^{L + 1/2}]` enter the window sum) such that:
   - the shifted-pair prime window `windowSum hg hgc hsupp (shiftedPairVonMangoldt a) L` strictly
     exceeds the polar-plus-archimedean budget `shiftMajorant g (2 * poleConst g + 2 * archConst g) L`,
     and
   - the full Weil functional of `shiftedPairVonMangoldt a` is strictly negative on the wide shift
     pair `g + g(· - L)`:
     `(weilFullFunctional (shiftedPairVonMangoldt a) (EF.weilTest (shiftPair g 1 L) (shiftPair g 1 L))).re < 0`.
   The proof integrates finite partial sums of `windowValue g L n * exp(-σ L)` at `σ = 1/2 + |a| > 1/2`
   against `integral_shiftMajorant_mul_exp` and contradicts the divergence of `∑ Λ(n)/n`
   (`RHTower.deningerVonMangoldt_not_summable`).

2. **Dilation-Ring Majorant Divergence, Shifted-Pair Harmonic Charge `A_a(m)`, and Sign Reversal of
   the Critical Prime Channel (`shiftedPairWindowRingMajorant`,
   `not_summable_shiftedPairWindowRingMajorant_of_half_le`,
   `shiftedPairWindowRingMajorant_prefix_ge`, `shiftedPairHarmonicCharge`,
   `shiftedPairHarmonicCharge_sign`, `shiftedPairCumulativeCharge`,
   `shiftedPairCumulativeCharge_three_pos_of_two_le`,
   `shiftedPairCumulativeCharge_pos_of_one_le`,
   `not_summable_shiftedPairHarmonicCharge_div_cube_of_two_le`,
   `not_summable_shiftedPairSingletonPrimeSeries_of_three_le`):**
   - For `|a| ≥ 1/2`, the dilation-ring window majorant
     `r ↦ (Λ_a(r)/r) min(1, √(L/r))` diverges on every scale window `L ≥ 1`, and for every `a` and
     `L ≥ 2` its finite prefix `2 ≤ r ≤ L` dominates `∑_{2 ≤ r ≤ L} Λ(r) r^{|a| - 1}`.
   - The critical harmonic divisor charge
     `A_a(m) = χ(m) ∑_{d ∣ m} d Λ_a(d) χ(m/d)` has `A_a(2) = -2 log 2 (2^a + 2^{-a}) < 0` as its
     unique negative harmonic, vanishes at `m = 0, 1` and multiples of `4`, and is strictly positive
     at all `m > 2` with `4 ∤ m`, with `A_a(p) = p log p (p^a + p^{-a})` at every odd prime `p`.
   - Whereas for `ζ` (`a = 0`) the cubic cumulative charge is strictly negative at `N = 2, 3, 4`
     (`factorialCriticalPrimeCumulativeCharge_sign`), for `|a| ≥ 2` the odd prime `m = 3` already
     flips the cumulative charge positive at `N = 3, 4`, and for `|a| ≥ 1` it is strictly positive
     for all `N ≥ 5`. For `|a| ≥ 2` the cubic charge series `∑_m A_a(m)/m³` diverges, and for
     `|a| ≥ 3` the singleton prime series `∑_m A_a(m) J_m / m⁴` diverges.

3. **Tempered Prime-Weight Infrastructure Invariance, Beurling Off-Line Zero Indistinguishability on
   the Critical Family, and Quantifier Separation (`TemperedPrimeWeight`,
   `re_weilFullFunctional_criticalTruncatedTest_eq`,
   `abs_weightedTruncatedPrimeEnergy_le_of_window`,
   `exists_temperedWeight_polynomial_window_weilFullFunctional_pos`,
   `temperedPrimeWeight_liouvilleTwist`, `temperedPrimeWeight_deletedFour`,
   `temperedPrimeWeight_primesOnly`, `beurling_offLine_zero_system_vs_critical_infrastructure`,
   `exists_fixedV_polynomial_window_pos_for_any_weight`):**
   - For **any** arithmetic weight `w : ℕ → ℝ` satisfying `|w(r)| ≤ C Λ(r)` (`TemperedPrimeWeight w C`),
     the prime energy of `criticalTruncatedSource V S b` satisfies
     `|weightedTruncatedPrimeEnergy w V S b| ≤ C C_TW (3 + log L) ∑_{n ∈ S} b_n²` uniformly in `V > 0`,
     and `(weilFullFunctional w (EF.weilTest g^V g^V)).re > 0` holds uniformly for all `M ≥ M₀`,
     all polynomial windows `L ≤ M^δ`, and all truncations `V ≥ criticalTruncationThreshold`.
   - In particular, the Liouville-twisted weight `λ(r)Λ(r)`, the node-`4`-deleted weight
     `Λ · 1_{r ≠ 4}`, the primes-only weight `Λ · 1_{r prime}`, and bounded-ratio Beurling
     perturbations satisfy the exact same uniform-in-`V` polynomial-window positivity on the
     critical family as `Λ`, while `BeurlingSensitivity.rh_sensitivity_threshold` produces positive
     generalized-prime densities of arbitrarily small reciprocal mass with off-line zeros at `β + iγ`
     (`1/2 < β < 1`), and `BiScaleUncertainty` node-criticality tests refute missing prime powers
     unconditionally (`zeroPoleBlindSymbolValue_neg_of_missing_primePow`).
   - Finally, at any **fixed** truncation `V ≥ criticalTruncationThreshold`, because `g^V` has
     compact support `[-log(2V), 0]` and only finitely many `r ≤ ⌊2V⌋` enter, choosing `M ≥ M₀(w, V)`
     after `V` makes `(weilFullFunctional w (EF.weilTest g^V g^V)).re > 0` for **every** weight
     `w : ℕ → ℝ` (including `shiftedPairVonMangoldt a`); what separates tempered weights from
     `shiftedPairVonMangoldt a` on the critical family is **uniformity in `V`**.
-/

open Complex MeasureTheory Set Filter Topology Finsupp
open scoped Real BigOperators CompactlySupported ENNReal
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilOneSided
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.SquareRootThreshold

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ## Section 1: Wide-Window Prime-Driven Failure of Weil Positivity for `ζ(s - a)ζ(s + a)` -/

/-- For a nonnegative `C²` bump `g` supported in `[-1/4, 1/4]` with `∫ g ≠ 0`, every real exponential
moment `∫ g(u) e^{c u} du` is strictly positive. -/
theorem integral_bump_mul_exp_pos {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (hg0 : ∀ u, 0 ≤ g u) (hint : ∫ u, g u ≠ 0) (c : ℝ) :
    0 < ∫ u, g u * Real.exp (c * u) := by
  have hg_int : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hge_int : Integrable fun u => g u * Real.exp (c * u) :=
    (hg.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have hg_pos : 0 < ∫ u, g u :=
    lt_of_le_of_ne (integral_nonneg hg0) (Ne.symm hint)
  have hdom : ∀ u : ℝ, g u * Real.exp (-|c| / 4) ≤ g u * Real.exp (c * u) := by
    intro u
    by_cases hu : 1 / 4 < |u|
    · rw [hsupp u hu, zero_mul, zero_mul]
    · rw [not_lt] at hu
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hg0 u)
      have h1 : -(|c| * |u|) ≤ c * u := by
        rw [← abs_mul]
        exact neg_abs_le (c * u)
      have h2 : |c| * |u| ≤ |c| * (1 / 4) :=
        mul_le_mul_of_nonneg_left hu (abs_nonneg c)
      linarith
  have hle := integral_mono (hg_int.mul_const (Real.exp (-|c| / 4))) hge_int hdom
  rw [integral_mul_const] at hle
  exact lt_of_lt_of_le (mul_pos hg_pos (Real.exp_pos _)) hle

/-- **Strict positivity of the real autocorrelation Laplace transform.** For any nonnegative bump
`g ∈ C_c²([-1/4, 1/4])` with `∫ g ≠ 0` and any real `σ`, `0 < autoLaplaceReal g σ`. -/
theorem autoLaplaceReal_pos {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (hg0 : ∀ u, 0 ≤ g u) (hint : ∫ u, g u ≠ 0) (σ : ℝ) :
    0 < autoLaplaceReal g σ := by
  rw [autoLaplaceReal_eq hg hsupp σ]
  exact mul_pos (integral_bump_mul_exp_pos hg hgc hsupp hg0 hint (-σ))
    (integral_bump_mul_exp_pos hg hgc hsupp hg0 hint σ)

/-- Every finite partial sum of nonnegative weighted window values is bounded above by `windowSum`. -/
theorem sum_windowValue_le_windowSum {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) (hg0 : ∀ u, 0 ≤ g u) {lam : ℕ → ℝ}
    (hlam : ∀ n, 0 ≤ lam n) (F : Finset ℕ) (hF : ∀ n ∈ F, 2 ≤ n) (L : ℝ) :
    ∑ n ∈ F, lam n * windowValue g L n ≤ windowSum hg hgc hsupp lam L := by
  classical
  set W := windowVector hg hgc hsupp L with hW
  have hWv : ∀ j : LogIndex, W j = windowValue g L j := fun j => by
    simp [hW, windowVector, Finsupp.ofSupportFinite_coe]
  unfold windowSum
  rw [← hW, linearCombination_apply, Finsupp.sum]
  set S : Finset ℕ := W.support.map ⟨Subtype.val, Subtype.val_injective⟩
  have hS : (∑ j ∈ W.support, W j • lam j) = ∑ n ∈ S, lam n * windowValue g L n := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.Embedding.coeFn_mk, hWv, smul_eq_mul, mul_comm]
  rw [hS]
  have hsub : ∑ n ∈ F, lam n * windowValue g L n =
      ∑ n ∈ F ∩ S, lam n * windowValue g L n := by
    refine (Finset.sum_subset Finset.inter_subset_left fun n hnF hnFS => ?_).symm
    have hn2 : 2 ≤ n := hF n hnF
    have hnS : n ∉ S := fun h => hnFS (Finset.mem_inter.mpr ⟨hnF, h⟩)
    have hW0 : W ⟨n, hn2⟩ = 0 := by
      by_contra hne
      exact hnS (Finset.mem_map.mpr ⟨⟨n, hn2⟩, Finsupp.mem_support_iff.mpr hne, rfl⟩)
    rw [hWv] at hW0
    rw [hW0, mul_zero]
  rw [hsub]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    fun n _ _ => mul_nonneg (hlam n) (windowValue_nonneg hg0 L n)

/-- For `L₀ ≥ 0` and `n ≥ 2` with `L₀ + 1/2 < log n`, `windowValue g L n` vanishes on `(0, L₀]`,
so its Laplace integral over `Ioi L₀` equals its full Laplace integral over `Ioi 0`. -/
theorem integral_Ioi_windowValue_mul_exp_of_large {g : ℝ → ℝ}
    (hsupp : ∀ u, 1 / 4 < |u| → g u = 0) {L₀ : ℝ} (hL₀ : 0 ≤ L₀)
    {n : ℕ} (hn2 : 2 ≤ n) (hlog : L₀ + 1 / 2 < Real.log n) (σ : ℝ) :
    ∫ L in Ioi L₀, windowValue g L n * Real.exp (-σ * L) =
      (n : ℝ) ^ (-(1 / 2 + σ)) * autoLaplaceReal g σ := by
  rw [← integral_windowValue_mul_exp hsupp hn2 σ]
  have hsub : Ioi L₀ ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hL₀
  refine (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet hsub
    (Eventually.of_forall fun L hL => ?_)).symm
  have hL0 : 0 < L := hL.1
  have hLL₀ : L ≤ L₀ := not_lt.mp hL.2
  have h1 : 1 / 2 < |Real.log n - L| := by
    rw [abs_of_pos (by linarith)]
    linarith
  have h2 : 1 / 2 < |Real.log n + L| := by
    rw [abs_of_pos (by linarith)]
    linarith
  unfold windowValue
  rw [autoCorr_eq_zero hsupp h1, autoCorr_eq_zero hsupp h2, add_zero, zero_div, zero_mul]

/-- **Wide-window divergence of the shifted-pair prime sum over the shift majorant.**
For every shift `a ≠ 0`, every nonnegative bump `g ∈ C_c²([-1/4, 1/4])` with `∫ g ≠ 0`, every
constant `C ≥ 0`, and every horizon `L₀ ≥ 0`, there exists a wide window shift `L > L₀` at which
`windowSum hg hgc hsupp (shiftedPairVonMangoldt a) L` strictly exceeds `shiftMajorant g C L`. -/
theorem exists_wide_windowSum_shiftedPairVonMangoldt_gt_shiftMajorant {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hsupp : ∀ u, 1 / 4 < |u| → g u = 0)
    (hg0 : ∀ u, 0 ≤ g u) (hint : ∫ u, g u ≠ 0) {a : ℝ} (ha : a ≠ 0) (C : ℝ) {L₀ : ℝ}
    (hL₀ : 0 ≤ L₀) :
    ∃ L : ℝ, L₀ < L ∧ shiftMajorant g C L < windowSum hg hgc hsupp (shiftedPairVonMangoldt a) L := by
  by_contra hcon
  push Not at hcon
  set σ : ℝ := 1 / 2 + |a|
  have ha_pos : 0 < |a| := abs_pos.mpr ha
  have hσ : 1 / 2 < σ := by unfold σ; linarith
  have hR : 0 < autoLaplaceReal g σ := autoLaplaceReal_pos hg hgc hsupp hg0 hint σ
  obtain ⟨hMint0, hMval0⟩ := integral_shiftMajorant_mul_exp (g := g) (max C 0) hσ
  have hMint : IntegrableOn (fun L => shiftMajorant g (max C 0) L * Real.exp (-σ * L)) (Ioi L₀) :=
    hMint0.mono_set (Ioi_subset_Ioi hL₀)
  set B : ℝ := ∫ L in Ioi L₀, shiftMajorant g (max C 0) L * Real.exp (-σ * L)
  set N₀ : ℕ := max 2 (⌈Real.exp (L₀ + 1)⌉₊ + 1)
  have hN₀2 : 2 ≤ N₀ := le_max_left _ _
  have hlogN₀ : ∀ n ≥ N₀, L₀ + 1 / 2 < Real.log n := by
    intro n hn
    have hn_gt : Real.exp (L₀ + 1) < (n : ℝ) := by
      have h1 : ⌈Real.exp (L₀ + 1)⌉₊ + 1 ≤ n := (le_max_right _ _).trans hn
      have h2 : Real.exp (L₀ + 1) ≤ (⌈Real.exp (L₀ + 1)⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : (⌈Real.exp (L₀ + 1)⌉₊ : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : ⌈Real.exp (L₀ + 1)⌉₊ < n)
      linarith
    have hn_pos : (0 : ℝ) < n := (Real.exp_pos _).trans hn_gt
    have := (Real.lt_log_iff_exp_lt hn_pos).mpr hn_gt
    linarith
  have hpartial : ∀ N : ℕ,
      ∑ n ∈ Finset.Icc N₀ N, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ≤
        B / autoLaplaceReal g σ := by
    intro N
    let F : ℕ → ℝ → ℝ := fun n L =>
      shiftedPairVonMangoldt a n * windowValue g L n * Real.exp (-σ * L)
    have hF_int : ∀ n ∈ Finset.Icc N₀ N, IntegrableOn (F n) (Ioi L₀) := fun n _ =>
      ((continuous_const.mul (continuous_windowValue hg hgc n)).mul (by fun_prop))
        |>.integrable_of_hasCompactSupport
          ((hasCompactSupport_windowValue hsupp n).mono (Function.support_subset_iff'.mpr fun L hL => by
            simp only [Function.mem_support, not_not] at hL
            dsimp [F]
            simp [hL])) |>.integrableOn
    have hsum_le : ∀ L ∈ Ioi L₀,
        ∑ n ∈ Finset.Icc N₀ N, F n L ≤ shiftMajorant g (max C 0) L * Real.exp (-σ * L) := by
      intro L hL
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have h1 := sum_windowValue_le_windowSum hg hgc hsupp hg0 (shiftedPairVonMangoldt_nonneg a)
        (Finset.Icc N₀ N) (fun n hn => hN₀2.trans (Finset.mem_Icc.mp hn).1) L
      have h2 := hcon L hL
      have h3 : shiftMajorant g C L ≤ shiftMajorant g (max C 0) L := by
        unfold shiftMajorant
        linarith [le_max_left C 0]
      exact h1.trans (h2.trans h3)
    have hint_le : ∫ L in Ioi L₀, (∑ n ∈ Finset.Icc N₀ N, F n L) ≤ B :=
      setIntegral_mono_on (integrable_finsetSum _ hF_int) hMint measurableSet_Ioi hsum_le
    rw [integral_finsetSum _ hF_int] at hint_le
    have hterm : ∀ n ∈ Finset.Icc N₀ N,
        autoLaplaceReal g σ * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)) ≤
          ∫ L in Ioi L₀, F n L := by
      intro n hn
      have hnN₀ : N₀ ≤ n := (Finset.mem_Icc.mp hn).1
      have hn2 : 2 ≤ n := hN₀2.trans hnN₀
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hI : ∫ L in Ioi L₀, F n L =
          shiftedPairVonMangoldt a n * ((n : ℝ) ^ (-(1 / 2 + σ)) * autoLaplaceReal g σ) := by
        dsimp [F]
        simp_rw [mul_assoc]
        rw [integral_const_mul,
          integral_Ioi_windowValue_mul_exp_of_large hsupp hL₀ hn2 (hlogN₀ n hnN₀) σ]
      rw [hI]
      have hpow : (n : ℝ) ^ (-(1 / 2 + σ)) = ((n : ℝ) * (n : ℝ) ^ |a|)⁻¹ := by
        have h1 : -(1 / 2 + σ) = -(1 + |a|) := by unfold σ; ring
        rw [h1, Real.rpow_neg hn_pos.le, Real.rpow_add hn_pos, Real.rpow_one]
      rw [hpow]
      have hdom := vonMangoldt_mul_rpow_abs_le_shiftedPairVonMangoldt a (by omega : 1 ≤ n)
      have hdiv : (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ≤
          shiftedPairVonMangoldt a n * ((n : ℝ) * (n : ℝ) ^ |a|)⁻¹ := by
        rw [← div_eq_mul_inv]
        calc (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)
            = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ |a| /
                ((n : ℝ) * (n : ℝ) ^ |a|) := by
              rw [mul_div_mul_right _ _ (Real.rpow_pos_of_pos hn_pos |a|).ne']
          _ ≤ shiftedPairVonMangoldt a n / ((n : ℝ) * (n : ℝ) ^ |a|) :=
              div_le_div_of_nonneg_right hdom (by positivity)
      calc autoLaplaceReal g σ * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ))
          ≤ autoLaplaceReal g σ * (shiftedPairVonMangoldt a n * ((n : ℝ) * (n : ℝ) ^ |a|)⁻¹) :=
            mul_le_mul_of_nonneg_left hdiv hR.le
        _ = shiftedPairVonMangoldt a n * (((n : ℝ) * (n : ℝ) ^ |a|)⁻¹ * autoLaplaceReal g σ) := by ring
    have hsum_low : autoLaplaceReal g σ *
        ∑ n ∈ Finset.Icc N₀ N, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ≤ B := by
      rw [Finset.mul_sum]
      exact (Finset.sum_le_sum hterm).trans hint_le
    rwa [le_div_iff₀ hR, mul_comm]
  apply RHTower.deningerVonMangoldt_not_summable
  refine summable_of_sum_range_le
    (c := ∑ n ∈ Finset.range N₀, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) +
      B / autoLaplaceReal g σ)
    (fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)) fun N => ?_
  rcases le_or_gt N N₀ with hN | hN
  · have hsub : ∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ≤
        ∑ n ∈ Finset.range N₀, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN)
        fun n _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
    have hB0 : 0 ≤ B / autoLaplaceReal g σ := by
      have := hpartial N₀
      have h0 : 0 ≤ ∑ n ∈ Finset.Icc N₀ N₀, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) :=
        Finset.sum_nonneg fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
      linarith
    linarith
  · have hsplit : Finset.range N = Finset.range N₀ ∪ Finset.Icc N₀ (N - 1) := by
      ext m
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
      omega
    have hdisj : Disjoint (Finset.range N₀) (Finset.Icc N₀ (N - 1)) := by
      rw [Finset.disjoint_left]
      intro m hm1 hm2
      simp only [Finset.mem_range, Finset.mem_Icc] at hm1 hm2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    linarith [hpartial (N - 1)]

/-- **Wide-Window Prime-Driven Failure of Weil Positivity for `ζ(s - a)ζ(s + a)`.**
For every real shift `a ≠ 0`, every nonnegative bump `g ∈ C_c²([-1/4, 1/4])` with `∫ g ≠ 0`, and
every horizon `L₀ ≥ 0`, there exists a wide window shift `L > max L₀ (log 2)` such that:
1. the shifted-pair prime window `windowSum hg hgc hsupp (shiftedPairVonMangoldt a) L` strictly
   exceeds the polar-plus-archimedean budget `shiftMajorant g (2 * poleConst g + 2 * archConst g) L`, and
2. the full Weil functional of `shiftedPairVonMangoldt a` is strictly negative on the wide shift
   pair `shiftPair g 1 L = g + g(· - L)`:
   `(weilFullFunctional (shiftedPairVonMangoldt a) (EF.weilTest (shiftPair g 1 L) (shiftPair g 1 L))).re < 0`. -/
theorem exists_wide_shiftPair_shiftedPairVonMangoldt_neg {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hsupp : ∀ u, 1 / 4 < |u| → g u = 0)
    (hg0 : ∀ u, 0 ≤ g u) (hint : ∫ u, g u ≠ 0) {a : ℝ} (ha : a ≠ 0) {L₀ : ℝ} (hL₀ : 0 ≤ L₀) :
    ∃ L : ℝ, max L₀ (Real.log 2) < L ∧
      shiftMajorant g (2 * poleConst g + 2 * archConst g) L <
        windowSum hg hgc hsupp (shiftedPairVonMangoldt a) L ∧
      (weilFullFunctional (shiftedPairVonMangoldt a)
        (EF.weilTest (shiftPair g 1 L) (shiftPair g 1 L))).re < 0 := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨L, hL, hgt⟩ := exists_wide_windowSum_shiftedPairVonMangoldt_gt_shiftMajorant
    hg hgc hsupp hg0 hint ha (2 * poleConst g + 2 * archConst g) (le_max_of_le_left hL₀)
  refine ⟨L, hL, hgt, ?_⟩
  by_contra hnonneg
  rw [not_lt] at hnonneg
  have hle := windowSum_le_of_shiftPair hg hgc hsupp hnonneg
  unfold shiftMajorant at hgt
  linarith

/-- Concrete wide-window failure of Weil positivity for `shiftedPairVonMangoldt a` on the canonical
bump `narrowG 0`. -/
theorem exists_wide_shiftPair_narrowG_shiftedPairVonMangoldt_neg {a : ℝ} (ha : a ≠ 0)
    {L₀ : ℝ} (hL₀ : 0 ≤ L₀) :
    ∃ L : ℝ, max L₀ (Real.log 2) < L ∧
      shiftMajorant (narrowG 0) (2 * poleConst (narrowG 0) + 2 * archConst (narrowG 0)) L <
        windowSum (contDiff_narrowG 0) (hasCompactSupport_narrowG 0) (narrowG_supp 0)
          (shiftedPairVonMangoldt a) L ∧
      (weilFullFunctional (shiftedPairVonMangoldt a)
        (EF.weilTest (shiftPair (narrowG 0) 1 L) (shiftPair (narrowG 0) 1 L))).re < 0 :=
  exists_wide_shiftPair_shiftedPairVonMangoldt_neg
    (contDiff_narrowG 0) (hasCompactSupport_narrowG 0) (narrowG_supp 0)
    (fun _ => (narrowBump 0).nonneg) (narrowBump 0).integral_pos.ne' ha hL₀

/-! ## Section 2: Dilation-Ring Majorant Divergence, Shifted-Pair Harmonic Charge `A_a(m)`, and Sign Reversal of the Critical Prime Channel -/

/-- The scale-window dilation-ring majorant `(Λ_a(r) / r) min(1, √(L / r))` of the shifted pair. -/
def shiftedPairWindowRingMajorant (a : ℝ) (L : ℕ) (r : ℕ) : ℝ :=
  if 2 ≤ r then shiftedPairVonMangoldt a r / (r : ℝ) * min 1 (Real.sqrt (L / r)) else 0

theorem shiftedPairWindowRingMajorant_nonneg (a : ℝ) (L r : ℕ) :
    0 ≤ shiftedPairWindowRingMajorant a L r := by
  unfold shiftedPairWindowRingMajorant
  split_ifs with hr
  · exact mul_nonneg (div_nonneg (shiftedPairVonMangoldt_nonneg a r) (Nat.cast_nonneg r))
      (le_min zero_le_one (Real.sqrt_nonneg _))
  · exact le_rfl

/-- **Dilation-ring window majorant divergence for `|a| ≥ 1/2`.** Whenever `1/2 ≤ |a|`, the
window-ring majorant `r ↦ (Λ_a(r)/r) min(1, √(L/r))` diverges on **every** window `L ≥ 1` because
even the far-ring `r^{-1/2}` decay cannot compensate for `r^{|a|} ≥ r^{1/2}`. -/
theorem not_summable_shiftedPairWindowRingMajorant_of_half_le {a : ℝ} (ha : 1 / 2 ≤ |a|)
    {L : ℕ} (hL : 1 ≤ L) :
    ¬ Summable (shiftedPairWindowRingMajorant a L) := by
  intro hsum
  apply RHTower.deningerVonMangoldt_not_summable
  refine Summable.of_nonneg_of_le
    (fun r => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg r))
    (fun r => ?_) hsum
  unfold shiftedPairWindowRingMajorant
  split_ifs with hr
  · have hr1 : 1 ≤ r := by omega
    have hr_pos : (0 : ℝ) < r := by exact_mod_cast hr1
    have hr_ge1 : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have hL_ge1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hmin : (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ min 1 (Real.sqrt (L / r)) := by
      rw [Real.rpow_neg hr_pos.le, ← Real.sqrt_eq_rpow, le_min_iff]
      refine ⟨?_, ?_⟩
      · exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hr_ge1)
      · rw [Real.sqrt_div (Nat.cast_nonneg L), inv_eq_one_div]
        exact div_le_div_of_nonneg_right (Real.one_le_sqrt.mpr hL_ge1) (Real.sqrt_nonneg r)
    have hdom := vonMangoldt_mul_rpow_abs_le_shiftedPairVonMangoldt a hr1
    have hpow : 1 ≤ (r : ℝ) ^ |a| * (r : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hr_pos]
      exact Real.one_le_rpow hr_ge1 (by linarith)
    calc (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ)
        ≤ (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
            ((r : ℝ) ^ |a| * (r : ℝ) ^ (-(1 / 2 : ℝ))) :=
          le_mul_of_one_le_right
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hr_pos.le) hpow
      _ = ((ArithmeticFunction.vonMangoldt r : ℝ) * (r : ℝ) ^ |a|) / (r : ℝ) *
            (r : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
      _ ≤ shiftedPairVonMangoldt a r / (r : ℝ) * min 1 (Real.sqrt (L / r)) :=
          mul_le_mul (div_le_div_of_nonneg_right hdom hr_pos.le) hmin
            (Real.rpow_nonneg hr_pos.le _)
            (div_nonneg (shiftedPairVonMangoldt_nonneg a r) hr_pos.le)
  · have hr01 : r = 0 ∨ r = 1 := by omega
    rcases hr01 with rfl | rfl <;> simp [ArithmeticFunction.vonMangoldt_apply_one]

/-- **Prefix growth of the shifted-pair window-ring majorant.** On the near-ring prefix `2 ≤ r ≤ L`,
the window factor `min(1, √(L/r))` equals `1`, so the partial sum of `shiftedPairWindowRingMajorant`
dominates `∑_{2 ≤ r ≤ L} Λ(r) r^{|a| - 1}`. -/
theorem shiftedPairWindowRingMajorant_prefix_ge (a : ℝ) (L : ℕ) :
    ∑ r ∈ Finset.Icc 2 L, (ArithmeticFunction.vonMangoldt r : ℝ) * (r : ℝ) ^ (|a| - 1) ≤
      ∑ r ∈ Finset.Icc 2 L, shiftedPairWindowRingMajorant a L r := by
  refine Finset.sum_le_sum fun r hr => ?_
  rcases Finset.mem_Icc.mp hr with ⟨hr2, hrL⟩
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hmin : min 1 (Real.sqrt (L / r)) = 1 := by
    refine min_eq_left ?_
    rw [Real.one_le_sqrt, one_le_div hr_pos]
    exact_mod_cast hrL
  unfold shiftedPairWindowRingMajorant
  rw [if_pos hr2, hmin, mul_one]
  have hdom := vonMangoldt_mul_rpow_abs_le_shiftedPairVonMangoldt a (by omega : 1 ≤ r)
  rw [sub_eq_add_neg, Real.rpow_add hr_pos, Real.rpow_neg_one, ← mul_assoc, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right hdom hr_pos.le

/-- The critical harmonic divisor charge `A_a(m) = χ(m) ∑_{d ∣ m} d Λ_a(d) χ(m/d)` of the shifted
pair `ζ(s - a)ζ(s + a)`. -/
def shiftedPairHarmonicCharge (a : ℝ) (m : ℕ) : ℝ :=
  dyadicHarmonicChi m * ∑ r ∈ m.divisors,
    (r : ℝ) * shiftedPairVonMangoldt a r * dyadicHarmonicChi (m / r)

theorem shiftedPairHarmonicCharge_neg (a : ℝ) (m : ℕ) :
    shiftedPairHarmonicCharge (-a) m = shiftedPairHarmonicCharge a m := by
  unfold shiftedPairHarmonicCharge shiftedPairVonMangoldt
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [neg_neg, add_comm ((r : ℝ) ^ (-a))]

/-- At `a = 0`, `shiftedPairHarmonicCharge 0 m = 2 * factorialCriticalPrimeHarmonicCharge m`. -/
theorem shiftedPairHarmonicCharge_zero (m : ℕ) :
    shiftedPairHarmonicCharge 0 m = 2 * factorialCriticalPrimeHarmonicCharge m := by
  unfold shiftedPairHarmonicCharge factorialCriticalPrimeHarmonicCharge shiftedPairVonMangoldt
  simp only [neg_zero, Real.rpow_zero]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- Harmonic `2` is negative for every shift `a`, with exact charge `-2 log 2 (2^a + 2^{-a})`. -/
theorem shiftedPairHarmonicCharge_two (a : ℝ) :
    shiftedPairHarmonicCharge a 2 = -2 * Real.log 2 * ((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) := by
  have hdiv : (2 : ℕ).divisors = {1, 2} := by decide
  norm_num [shiftedPairHarmonicCharge, shiftedPairVonMangoldt, hdiv, dyadicHarmonicChi,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  ring

/-- Every odd prime `p` contributes `p log p (p^a + p^{-a})` to `shiftedPairHarmonicCharge a p`. -/
theorem shiftedPairHarmonicCharge_odd_prime (a : ℝ) {p : ℕ} (hp : p.Prime) (hodd : p % 2 = 1) :
    shiftedPairHarmonicCharge a p = (p : ℝ) * Real.log p * ((p : ℝ) ^ a + (p : ℝ) ^ (-a)) := by
  have h1p : 1 ≠ p := Ne.symm hp.ne_one
  have hpp : p / p = 1 := Nat.div_self hp.pos
  simp [shiftedPairHarmonicCharge, shiftedPairVonMangoldt, hp.divisors, h1p, hpp,
    dyadicHarmonicChi, hodd, ArithmeticFunction.vonMangoldt_apply_prime hp]
  ring

private theorem shifted_chi_divisor (m r : ℕ) (hr : r ∈ m.divisors) (hm : m % 4 ≠ 0) :
    dyadicHarmonicChi m * dyadicHarmonicChi (m / r) = dyadicHarmonicChi r := by
  let q := m / r
  have hmul : r * q = m := Nat.mul_div_cancel' (Nat.mem_divisors.mp hr).1
  have hχ : dyadicHarmonicChi m = dyadicHarmonicChi (r * q) := congrArg _ hmul.symm
  have hmod : (r * q) % 4 ≠ 0 := by simpa only [hmul] using hm
  change dyadicHarmonicChi m * dyadicHarmonicChi q = dyadicHarmonicChi r
  rw [hχ]
  have hr2 : r % 2 = (r % 4) % 2 := by omega
  have hq2 : q % 2 = (q % 4) % 2 := by omega
  have hr4 := Nat.mod_lt r (by norm_num : 0 < 4)
  have hq4 := Nat.mod_lt q (by norm_num : 0 < 4)
  interval_cases hR : r % 4 <;> interval_cases hQ : q % 4 <;>
    norm_num [Nat.mul_mod, hR, hQ] at hmod <;>
    norm_num [dyadicHarmonicChi, Nat.mul_mod, hr2, hq2, hR, hQ]

private theorem shifted_even_vonMangoldt_zero (a : ℝ) (r : ℕ) (hr : r ≠ 2)
    (hodd : ¬ r % 2 = 1) (hfour : r % 4 ≠ 0) :
    shiftedPairVonMangoldt a r = 0 := by
  unfold shiftedPairVonMangoldt
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr, zero_mul]
  intro hpow
  have hr2 : 2 < r := by have h := hpow.two_le; omega
  have h4 : ¬ 4 ∣ r := fun h => hfour (Nat.mod_eq_zero_of_dvd h)
  obtain ⟨p, hp, hpd, hpodd⟩ :=
    (Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hr2).resolve_left h4
  obtain ⟨q, _, hq⟩ := isPrimePow_iff_unique_prime_dvd.mp hpow
  have h2dvd : 2 ∣ r := Nat.dvd_of_mod_eq_zero (by omega)
  have hpq := hq p ⟨hp, hpd⟩
  have h2q := hq 2 ⟨Nat.prime_two, h2dvd⟩
  have hp3 := hp.odd_iff.mp hpodd
  omega

/-- **Complete sign classification of the shifted-pair harmonic divisor charge `A_a(m)`.**
For every real shift `a` and every `m : ℕ`:
- `A_a(m) < 0 ↔ m = 2`,
- `A_a(m) = 0 ↔ m = 1 ∨ m % 4 = 0`,
- `0 < A_a(m) ↔ 2 < m ∧ m % 4 ≠ 0`. -/
theorem shiftedPairHarmonicCharge_sign (a : ℝ) (m : ℕ) :
    (shiftedPairHarmonicCharge a m < 0 ↔ m = 2) ∧
    (shiftedPairHarmonicCharge a m = 0 ↔ m = 1 ∨ m % 4 = 0) ∧
    (0 < shiftedPairHarmonicCharge a m ↔ 2 < m ∧ m % 4 ≠ 0) := by
  have htwo_neg : shiftedPairHarmonicCharge a 2 < 0 := by
    rw [shiftedPairHarmonicCharge_two]
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hp : 0 < (2 : ℝ) ^ a + (2 : ℝ) ^ (-a) := by positivity
    nlinarith
  have hfour_zero (hm : m % 4 = 0) : shiftedPairHarmonicCharge a m = 0 := by
    have hodd : ¬ m % 2 = 1 := by omega
    simp [shiftedPairHarmonicCharge, dyadicHarmonicChi, hodd, hm]
  have hone_zero : shiftedPairHarmonicCharge a 1 = 0 := by
    simp [shiftedPairHarmonicCharge, shiftedPairVonMangoldt]
  have hpos (hm : 2 < m) (hfour : m % 4 ≠ 0) : 0 < shiftedPairHarmonicCharge a m := by
    have hsum : shiftedPairHarmonicCharge a m =
        ∑ r ∈ m.divisors, (r : ℝ) * shiftedPairVonMangoldt a r * dyadicHarmonicChi r := by
      unfold shiftedPairHarmonicCharge
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      calc dyadicHarmonicChi m * ((r : ℝ) * shiftedPairVonMangoldt a r * dyadicHarmonicChi (m / r))
          = (r : ℝ) * shiftedPairVonMangoldt a r * (dyadicHarmonicChi m * dyadicHarmonicChi (m / r)) := by ring
        _ = (r : ℝ) * shiftedPairVonMangoldt a r * dyadicHarmonicChi r := by
            rw [shifted_chi_divisor m r hr hfour]
    rw [hsum]
    have hnn : ∀ r : ℕ, r ≠ 2 → 0 ≤ (r : ℝ) * shiftedPairVonMangoldt a r * dyadicHarmonicChi r := by
      intro r hr2
      by_cases hodd : r % 2 = 1
      · simp only [dyadicHarmonicChi, if_pos hodd, mul_one]
        exact mul_nonneg (Nat.cast_nonneg r) (shiftedPairVonMangoldt_nonneg a r)
      · by_cases hf4 : r % 4 = 0
        · have ht2 : ¬ r % 4 = 2 := by omega
          simp [dyadicHarmonicChi, hodd, ht2]
        · rw [shifted_even_vonMangoldt_zero a r hr2 hodd hf4]
          ring_nf
          exact le_rfl
    have h4 : ¬ 4 ∣ m := fun h => hfour (Nat.mod_eq_zero_of_dvd h)
    obtain ⟨p, hp, hpd, hpodd⟩ :=
      (Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hm).resolve_left h4
    have hp3 := hp.odd_iff.mp hpodd
    have hp2 : p ≠ 2 := by omega
    have hpmod : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
    have hpmem : p ∈ m.divisors := Nat.mem_divisors.mpr ⟨hpd, by omega⟩
    have hpterm : (p : ℝ) * shiftedPairVonMangoldt a p * dyadicHarmonicChi p =
        (p : ℝ) * Real.log p * ((p : ℝ) ^ a + (p : ℝ) ^ (-a)) := by
      simp [shiftedPairVonMangoldt, ArithmeticFunction.vonMangoldt_apply_prime hp,
        dyadicHarmonicChi, hpmod]
      ring
    by_cases h2d : 2 ∈ m.divisors
    · have hpne2 : p ≠ 2 := hp2
      have hpair : ({2, p} : Finset ℕ) ⊆ m.divisors := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact h2d
        · rw [Finset.mem_singleton.mp hx]; exact hpmem
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg hpair fun r _ hrnot =>
        hnn r (fun hr2 => hrnot (by simp [hr2]))
      rw [Finset.sum_pair hpne2.symm] at hsub
      have h2term : ((2 : ℕ) : ℝ) * shiftedPairVonMangoldt a 2 * dyadicHarmonicChi 2 =
          -2 * Real.log 2 * ((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) := by
        norm_num [shiftedPairVonMangoldt, dyadicHarmonicChi,
          ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
        ring
      rw [h2term, hpterm] at hsub
      have hlog : Real.log 2 < Real.log p :=
        Real.log_lt_log (by norm_num) (by exact_mod_cast (show 2 < p by omega))
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hp_ge3 : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      have hcosh : (2 : ℝ) ^ a + (2 : ℝ) ^ (-a) ≤ (p : ℝ) ^ a + (p : ℝ) ^ (-a) := by
        have h2p : (2 : ℝ) ≤ p := by linarith
        have hsymm : ∀ x : ℝ, x ^ a + x ^ (-a) = x ^ |a| + x ^ (-|a|) := fun x => by
          rcases le_or_gt 0 a with ha0 | ha0
          · rw [abs_of_nonneg ha0]
          · rw [abs_of_neg ha0, neg_neg, add_comm]
        rw [hsymm 2, hsymm p]
        have hd1 : (2 : ℝ) ^ |a| ≤ (p : ℝ) ^ |a| :=
          Real.rpow_le_rpow (by norm_num) h2p (abs_nonneg a)
        have hprod1 : (2 : ℝ) ^ |a| * (2 : ℝ) ^ (-|a|) = 1 := by
          rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
        have hprod2 : (p : ℝ) ^ |a| * (p : ℝ) ^ (-|a|) = 1 := by
          rw [← Real.rpow_add (by linarith), add_neg_cancel, Real.rpow_zero]
        have hle1 : (2 : ℝ) ^ (-|a|) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (abs_nonneg a))
        have hle2 : (p : ℝ) ^ (-|a|) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (neg_nonpos.mpr (abs_nonneg a))
        have hdiff : 0 ≤ ((p : ℝ) ^ |a| - (2 : ℝ) ^ |a|) *
            (1 - (2 : ℝ) ^ (-|a|) * (p : ℝ) ^ (-|a|)) := by
          refine mul_nonneg (by linarith) ?_
          nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-|a|),
            Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ p) (-|a|)]
        have hid : ((p : ℝ) ^ |a| + (p : ℝ) ^ (-|a|)) - ((2 : ℝ) ^ |a| + (2 : ℝ) ^ (-|a|)) =
            ((p : ℝ) ^ |a| - (2 : ℝ) ^ |a|) * (1 - (2 : ℝ) ^ (-|a|) * (p : ℝ) ^ (-|a|)) := by
          linear_combination (2 : ℝ) ^ (-|a|) * hprod2 - (p : ℝ) ^ (-|a|) * hprod1
        linarith
      have h2pos : 0 < (2 : ℝ) ^ a + (2 : ℝ) ^ (-a) := by positivity
      have hstrict : -2 * Real.log 2 * ((2 : ℝ) ^ a + (2 : ℝ) ^ (-a)) +
          (p : ℝ) * Real.log p * ((p : ℝ) ^ a + (p : ℝ) ^ (-a)) > 0 := by
        have h1 : 3 * Real.log 2 < (p : ℝ) * Real.log p :=
          calc 3 * Real.log 2 ≤ (p : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hp_ge3 hlog2.le
            _ < (p : ℝ) * Real.log p := mul_lt_mul_of_pos_left hlog (by linarith)
        nlinarith
      linarith
    · have hsub := Finset.single_le_sum (fun r hr => hnn r (fun hr2 => h2d (hr2 ▸ hr))) hpmem
      rw [hpterm] at hsub
      have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hcosh : 0 < (p : ℝ) ^ a + (p : ℝ) ^ (-a) := by positivity
      exact lt_of_lt_of_le (by positivity) hsub
  rcases eq_or_ne m 0 with rfl | hm0
  · rw [hfour_zero (by norm_num)]; norm_num
  rcases eq_or_ne m 1 with rfl | hm1
  · rw [hone_zero]; norm_num
  rcases eq_or_ne m 2 with rfl | hm2
  · refine ⟨⟨fun _ => rfl, fun _ => htwo_neg⟩, ⟨fun h => by linarith, by omega⟩,
      ⟨fun h => by linarith, by omega⟩⟩
  by_cases hf : m % 4 = 0
  · rw [hfour_zero hf]
    exact ⟨⟨by norm_num, fun h => False.elim (hm2 h)⟩,
      ⟨fun _ => Or.inr hf, fun _ => rfl⟩, ⟨by norm_num, fun h => False.elim (h.2 hf)⟩⟩
  · have hm_gt2 : 2 < m := by omega
    have hp := hpos hm_gt2 hf
    exact ⟨⟨fun h => by linarith, fun h => False.elim (hm2 h)⟩,
      ⟨fun h => by linarith, fun h => False.elim (h.elim hm1 hf)⟩,
      ⟨fun _ => ⟨hm_gt2, hf⟩, fun _ => hp⟩⟩

theorem shiftedPairHarmonicCharge_nonneg_of_ne_two (a : ℝ) {m : ℕ} (hm : m ≠ 2) :
    0 ≤ shiftedPairHarmonicCharge a m :=
  le_of_not_gt fun h => hm ((shiftedPairHarmonicCharge_sign a m).1.mp h)

/-- The cubic cumulative divisor charge `∑_{m=1}^N A_a(m) / m³` of the shifted pair. -/
def shiftedPairCumulativeCharge (a : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, shiftedPairHarmonicCharge a m / (m : ℝ) ^ 3

theorem shiftedPairCumulativeCharge_mono (a : ℝ) {M N : ℕ} (hM : 2 ≤ M) (hMN : M ≤ N) :
    shiftedPairCumulativeCharge a M ≤ shiftedPairCumulativeCharge a N := by
  unfold shiftedPairCumulativeCharge
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro m hm
    rcases Finset.mem_Icc.mp hm with ⟨hm1, hmM⟩
    exact Finset.mem_Icc.mpr ⟨hm1, hmM.trans hMN⟩
  · intro m hm hmnot
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmne : m ≠ 2 := by
      intro rfl
      exact hmnot (Finset.mem_Icc.mpr ⟨by norm_num, hM⟩)
    exact div_nonneg (shiftedPairHarmonicCharge_nonneg_of_ne_two a hmne) (by positivity)

/-- **Sign reversal of the cubic cumulative charge at `N = 3, 4` for `|a| ≥ 2`.**
Whereas for `ζ` (`a = 0`) the cumulative charge is strictly negative at `N = 2, 3, 4`
(`factorialCriticalPrimeCumulativeCharge_sign`), for `|a| ≥ 2` the odd prime `m = 3` already flips
`shiftedPairCumulativeCharge a N` strictly positive for all `N ≥ 3`. -/
theorem shiftedPairCumulativeCharge_three_pos_of_two_le {a : ℝ} (ha : 2 ≤ |a|) {N : ℕ}
    (hN : 3 ≤ N) :
    0 < shiftedPairCumulativeCharge a N := by
  refine lt_of_lt_of_le ?_ (shiftedPairCumulativeCharge_mono a (by norm_num : 2 ≤ 3) hN)
  have hsymm : shiftedPairCumulativeCharge a 3 = shiftedPairCumulativeCharge |a| 3 := by
    rcases le_or_gt 0 a with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h]
      unfold shiftedPairCumulativeCharge
      exact Finset.sum_congr rfl fun m _ => by rw [shiftedPairHarmonicCharge_neg]
  rw [hsymm]
  have hI3 : Finset.Icc (1 : ℕ) 3 = {1, 2, 3} := by decide
  have h1 : shiftedPairHarmonicCharge |a| 1 = 0 :=
    (shiftedPairHarmonicCharge_sign |a| 1).2.1.mpr (Or.inl rfl)
  have h2 := shiftedPairHarmonicCharge_two |a|
  have h3 : shiftedPairHarmonicCharge |a| 3 =
      3 * Real.log 3 * ((3 : ℝ) ^ |a| + (3 : ℝ) ^ (-|a|)) :=
    shiftedPairHarmonicCharge_odd_prime |a| Nat.prime_three (by norm_num)
  unfold shiftedPairCumulativeCharge
  rw [hI3]
  norm_num [h1, h2, h3]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h23 : 3 * Real.log 2 < 2 * Real.log 3 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2 ^ 3) (by norm_num : (2 : ℝ) ^ 3 < 3 ^ 2)
    simp only [Real.log_pow, Nat.cast_ofNat] at h
    exact h
  have hpow2 : (2 : ℝ) ^ (-|a|) ≤ (1 / 4) * (2 : ℝ) ^ |a| := by
    have hle1 : (2 : ℝ) ^ (-|a|) ≤ (2 : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hge2 : (2 : ℝ) ^ (2 : ℝ) ≤ (2 : ℝ) ^ |a| :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
    norm_num at hle1 hge2
    linarith
  have hpow3 : (9 / 4 : ℝ) * (2 : ℝ) ^ |a| ≤ (3 : ℝ) ^ |a| := by
    have hq : (3 / 2 : ℝ) ^ (2 : ℝ) ≤ (3 / 2 : ℝ) ^ |a| :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
    have hmul : (3 / 2 : ℝ) ^ |a| * (2 : ℝ) ^ |a| = (3 : ℝ) ^ |a| := by
      rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
    have h2pos : 0 < (2 : ℝ) ^ |a| := Real.rpow_pos_of_pos (by norm_num) |a|
    have hq' : (9 / 4 : ℝ) ≤ (3 / 2 : ℝ) ^ |a| := by norm_num at hq; exact hq
    nlinarith [mul_le_mul_of_nonneg_right hq' h2pos.le]
  have h3_neg : 0 < (3 : ℝ) ^ (-|a|) := Real.rpow_pos_of_pos (by norm_num) (-|a|)
  have h2_pos : 0 < (2 : ℝ) ^ |a| := Real.rpow_pos_of_pos (by norm_num) |a|
  have hratio : (9 / 5 : ℝ) * ((2 : ℝ) ^ |a| + (2 : ℝ) ^ (-|a|)) <
      (3 : ℝ) ^ |a| + (3 : ℝ) ^ (-|a|) := by linarith
  have hlog3_pos : 0 < (3 : ℝ) ^ |a| + (3 : ℝ) ^ (-|a|) := by positivity
  nlinarith

/-- For every `|a| ≥ 1` and every `N ≥ 5`, `shiftedPairCumulativeCharge a N > 0`. -/
theorem shiftedPairCumulativeCharge_pos_of_one_le {a : ℝ} (ha : 1 ≤ |a|) {N : ℕ}
    (hN : 5 ≤ N) :
    0 < shiftedPairCumulativeCharge a N := by
  refine lt_of_lt_of_le ?_ (shiftedPairCumulativeCharge_mono a (by norm_num : 2 ≤ 5) hN)
  have hsymm : shiftedPairCumulativeCharge a 5 = shiftedPairCumulativeCharge |a| 5 := by
    rcases le_or_gt 0 a with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h]
      unfold shiftedPairCumulativeCharge
      exact Finset.sum_congr rfl fun m _ => by rw [shiftedPairHarmonicCharge_neg]
  rw [hsymm]
  have hI5 : Finset.Icc (1 : ℕ) 5 = {1, 2, 3, 4, 5} := by decide
  have h1 : shiftedPairHarmonicCharge |a| 1 = 0 :=
    (shiftedPairHarmonicCharge_sign |a| 1).2.1.mpr (Or.inl rfl)
  have h2 := shiftedPairHarmonicCharge_two |a|
  have h3 : shiftedPairHarmonicCharge |a| 3 =
      3 * Real.log 3 * ((3 : ℝ) ^ |a| + (3 : ℝ) ^ (-|a|)) :=
    shiftedPairHarmonicCharge_odd_prime |a| Nat.prime_three (by norm_num)
  have h4 : shiftedPairHarmonicCharge |a| 4 = 0 :=
    (shiftedPairHarmonicCharge_sign |a| 4).2.1.mpr (Or.inr (by norm_num))
  have h5 : shiftedPairHarmonicCharge |a| 5 =
      5 * Real.log 5 * ((5 : ℝ) ^ |a| + (5 : ℝ) ^ (-|a|)) :=
    shiftedPairHarmonicCharge_odd_prime |a| Nat.prime_five (by norm_num)
  unfold shiftedPairCumulativeCharge
  rw [hI5]
  norm_num [h1, h2, h3, h4, h5]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h23 : 3 * Real.log 2 < 2 * Real.log 3 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2 ^ 3) (by norm_num : (2 : ℝ) ^ 3 < 3 ^ 2)
    simp only [Real.log_pow, Nat.cast_ofNat] at h; exact h
  have h25 : 9 * Real.log 2 < 4 * Real.log 5 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2 ^ 9) (by norm_num : (2 : ℝ) ^ 9 < 5 ^ 4)
    simp only [Real.log_pow, Nat.cast_ofNat] at h; exact h
  have hpow2 : (2 : ℝ) ^ (-|a|) ≤ (1 / 4) * (2 : ℝ) ^ |a| := by
    have hle1 : (2 : ℝ) ^ (-|a|) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hge2 : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ |a| :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
    norm_num at hle1 hge2
    linarith
  have h2_pos : 0 < (2 : ℝ) ^ |a| := Real.rpow_pos_of_pos (by norm_num) |a|
  have hpow3 : (3 / 2 : ℝ) * (2 : ℝ) ^ |a| ≤ (3 : ℝ) ^ |a| := by
    have hq : (3 / 2 : ℝ) ^ (1 : ℝ) ≤ (3 / 2 : ℝ) ^ |a| :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
    have hmul : (3 / 2 : ℝ) ^ |a| * (2 : ℝ) ^ |a| = (3 : ℝ) ^ |a| := by
      rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
    rw [Real.rpow_one] at hq
    nlinarith [mul_le_mul_of_nonneg_right hq h2_pos.le]
  have hpow5 : (5 / 2 : ℝ) * (2 : ℝ) ^ |a| ≤ (5 : ℝ) ^ |a| := by
    have hq : (5 / 2 : ℝ) ^ (1 : ℝ) ≤ (5 / 2 : ℝ) ^ |a| :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
    have hmul : (5 / 2 : ℝ) ^ |a| * (2 : ℝ) ^ |a| = (5 : ℝ) ^ |a| := by
      rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
    rw [Real.rpow_one] at hq
    nlinarith [mul_le_mul_of_nonneg_right hq h2_pos.le]
  have h3_neg : 0 < (3 : ℝ) ^ (-|a|) := Real.rpow_pos_of_pos (by norm_num) (-|a|)
  have h5_neg : 0 < (5 : ℝ) ^ (-|a|) := Real.rpow_pos_of_pos (by norm_num) (-|a|)
  have hratio3 : (6 / 5 : ℝ) * ((2 : ℝ) ^ |a| + (2 : ℝ) ^ (-|a|)) <
      (3 : ℝ) ^ |a| + (3 : ℝ) ^ (-|a|) := by linarith
  have hratio5 : 2 * ((2 : ℝ) ^ |a| + (2 : ℝ) ^ (-|a|)) <
      (5 : ℝ) ^ |a| + (5 : ℝ) ^ (-|a|) := by linarith
  have hc3 : 0 < (3 : ℝ) ^ |a| + (3 : ℝ) ^ (-|a|) := by positivity
  have hc5 : 0 < (5 : ℝ) ^ |a| + (5 : ℝ) ^ (-|a|) := by positivity
  nlinarith

/-- **Divergence of the cubic harmonic charge series `∑_m A_a(m) / m³` for `|a| ≥ 2`.**
Whereas `∑_m |A_0(m)| / m³` converges (`summable_abs_factorialCriticalPrimeHarmonicCharge_div_cube`),
for `|a| ≥ 2` every odd prime `p ≥ 3` satisfies `A_a(p) / p³ ≥ log 3 > 0`, so the series fails
summability. -/
theorem not_summable_shiftedPairHarmonicCharge_div_cube_of_two_le {a : ℝ} (ha : 2 ≤ |a|) :
    ¬ Summable (fun m : ℕ => shiftedPairHarmonicCharge a m / (m : ℝ) ^ 3) := by
  intro hsum
  have htend := hsum.tendsto_atTop_zero
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htend.eventually (eventually_lt_nhds hlog3))
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max N 3)
  have hp3 : 3 ≤ p := (le_max_right N 3).trans hpN
  have hp2 : p ≠ 2 := by omega
  have hpmod : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have hval := shiftedPairHarmonicCharge_odd_prime a hp hpmod
  have hp_ge3 : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hp_pos : (0 : ℝ) < p := by linarith
  have hpow : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ a + (p : ℝ) ^ (-a) := by
    have h1 : (p : ℝ) ^ (2 : ℝ) ≤ (p : ℝ) ^ |a| :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) ha
    rw [Real.rpow_two] at h1
    rcases le_or_gt 0 a with h | h
    · rw [abs_of_nonneg h] at h1
      have : 0 ≤ (p : ℝ) ^ (-a) := Real.rpow_nonneg hp_pos.le _
      linarith
    · rw [abs_of_neg h] at h1
      have : 0 ≤ (p : ℝ) ^ a := Real.rpow_nonneg hp_pos.le _
      linarith
  have hge : Real.log 3 ≤ shiftedPairHarmonicCharge a p / (p : ℝ) ^ 3 := by
    rw [hval]
    have hlogp : Real.log 3 ≤ Real.log p := Real.log_le_log (by norm_num) hp_ge3
    have hlogp0 : 0 ≤ Real.log p := hlog3.le.trans hlogp
    calc Real.log 3 ≤ Real.log p := hlogp
      _ = (p : ℝ) * Real.log p * (p : ℝ) ^ 2 / (p : ℝ) ^ 3 := by field_simp
      _ ≤ (p : ℝ) * Real.log p * ((p : ℝ) ^ a + (p : ℝ) ^ (-a)) / (p : ℝ) ^ 3 := by gcongr
  have hlt := hN p ((le_max_left N 3).trans hpN)
  linarith

/-- **Divergence of the singleton critical prime series `∑_m A_a(m) J_m / m⁴` for `|a| ≥ 3`.**
Whereas for `ζ` (`a = 0`) the series `∑_m A(m) J_m / m⁴` converges absolutely to a strictly negative
limit `≤ -(log 2)/390` (`factorialCriticalPrimeHarmonicSum_negative_bound`), for `|a| ≥ 3` every odd
prime `p ≥ 8` satisfies `A_a(p) J_p / p⁴ ≥ (log 3) / 2 > 0`, so the series fails summability. -/
theorem not_summable_shiftedPairSingletonPrimeSeries_of_three_le {a : ℝ} (ha : 3 ≤ |a|) :
    ¬ Summable (fun m : ℕ =>
      shiftedPairHarmonicCharge a m * factorialCriticalHarmonicDefect m / (m : ℝ) ^ 4) := by
  intro hsum
  have htend := hsum.tendsto_atTop_zero
  have hlog3 : 0 < Real.log 3 / 2 := by have := Real.log_pos (by norm_num : (1 : ℝ) < 3); positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htend.eventually (eventually_lt_nhds hlog3))
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max N 8)
  have hp8 : 8 ≤ p := (le_max_right N 8).trans hpN
  have hp2 : p ≠ 2 := by omega
  have hpmod : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have hval := shiftedPairHarmonicCharge_odd_prime a hp hpmod
  have hp_ge8 : (8 : ℝ) ≤ p := by exact_mod_cast hp8
  have hp_pos : (0 : ℝ) < p := by linarith
  have hJ : 1 / 2 ≤ factorialCriticalHarmonicDefect p := by
    have htb := factorialCriticalHarmonicDefect_tail_bound (p - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ p)] at htb
    have herr : 12 / (Real.pi * (p : ℝ)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have hpi := Real.pi_gt_three
      nlinarith
    have := (abs_le.mp htb).1
    linarith
  have hpow : (p : ℝ) ^ 3 ≤ (p : ℝ) ^ a + (p : ℝ) ^ (-a) := by
    have h1 : (p : ℝ) ^ (3 : ℝ) ≤ (p : ℝ) ^ |a| :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) ha
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
    rcases le_or_gt 0 a with h | h
    · rw [abs_of_nonneg h] at h1
      have : 0 ≤ (p : ℝ) ^ (-a) := Real.rpow_nonneg hp_pos.le _
      linarith
    · rw [abs_of_neg h] at h1
      have : 0 ≤ (p : ℝ) ^ a := Real.rpow_nonneg hp_pos.le _
      linarith
  have hge : Real.log 3 / 2 ≤
      shiftedPairHarmonicCharge a p * factorialCriticalHarmonicDefect p / (p : ℝ) ^ 4 := by
    rw [hval]
    have hlogp : Real.log 3 ≤ Real.log p := Real.log_le_log (by norm_num) (by linarith)
    have hlogp0 : 0 ≤ Real.log p := (Real.log_pos (by norm_num)).le.trans hlogp
    calc Real.log 3 / 2 ≤ Real.log p * (1 / 2) := by linarith
      _ = (p : ℝ) * Real.log p * (p : ℝ) ^ 3 * (1 / 2) / (p : ℝ) ^ 4 := by field_simp
      _ ≤ (p : ℝ) * Real.log p * ((p : ℝ) ^ a + (p : ℝ) ^ (-a)) *
            factorialCriticalHarmonicDefect p / (p : ℝ) ^ 4 := by
          gcongr
  have hlt := hN p ((le_max_left N 8).trans hpN)
  linarith

/-! ## Section 3: Tempered Prime-Weight Infrastructure Invariance, Beurling Off-Line Zero Indistinguishability on the Critical Family, and Quantifier Separation -/

/-- An arithmetic weight `w : ℕ → ℝ` is `C`-tempered if `|w(r)| ≤ C Λ(r)` for all `r ≥ 2`.
This condition requires neither multiplicativity, nor prime-power support, nor nonnegativity. -/
def TemperedPrimeWeight (w : ℕ → ℝ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ r : ℕ, 2 ≤ r → |w r| ≤ C * (ArithmeticFunction.vonMangoldt r : ℝ)

/-- The prime atom of `criticalTruncatedSource V S b` against an arbitrary arithmetic weight `w`. -/
def weightedTruncatedPrimeAtom (w : ℕ → ℝ) (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) : ℝ :=
  (if 2 ≤ r then w r / Real.sqrt (r : ℝ) else 0) *
    ∫ x : ℝ, criticalTruncatedSource V S b x * criticalTruncatedSource V S b (x - Real.log r)

/-- The prime energy of `criticalTruncatedSource V S b` against an arbitrary arithmetic weight `w`. -/
def weightedTruncatedPrimeEnergy (w : ℕ → ℝ) (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑' r : ℕ, weightedTruncatedPrimeAtom w V S b r

@[simp]
theorem weightedTruncatedPrimeAtom_vonMangoldt (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) :
    weightedTruncatedPrimeAtom (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) V S b r =
      criticalTruncatedPrimeAtom V S b r := rfl

@[simp]
theorem weightedTruncatedPrimeEnergy_vonMangoldt (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) :
    weightedTruncatedPrimeEnergy (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) V S b =
      criticalTruncatedPrimeEnergy V S b := rfl

/-- Because `criticalTruncatedSource V S b` vanishes outside `[-log(2V), 0]`, every prime atom
`weightedTruncatedPrimeAtom w V S b r` vanishes for `r > ⌊2V⌋` (`2 * V < r`), for **every**
weight `w : ℕ → ℝ`. -/
theorem weightedTruncatedPrimeAtom_eq_zero_of_gt {w : ℕ → ℝ} {V : ℝ} (hV : 0 < V)
    (S : Finset ℕ) (b : ℕ → ℝ) {r : ℕ} (hr : 2 * V < (r : ℝ)) :
    weightedTruncatedPrimeAtom w V S b r = 0 := by
  unfold weightedTruncatedPrimeAtom
  have hzero : (fun x : ℝ =>
      criticalTruncatedSource V S b x * criticalTruncatedSource V S b (x - Real.log r)) =
      fun _ => 0 := by
    funext x
    by_cases hx : x ∈ Icc (-Real.log (2 * V)) 0
    · have hnot : x - Real.log r ∉ Icc (-Real.log (2 * V)) 0 := by
        intro hmem
        have hlog : Real.log (2 * V) < Real.log r :=
          Real.log_lt_log (by positivity) hr
        linarith [hx.2, hmem.1]
      rw [criticalTruncatedSource_eq_zero hV S b hnot, mul_zero]
    · rw [criticalTruncatedSource_eq_zero hV S b hx, zero_mul]
  rw [hzero, integral_zero, mul_zero]

theorem summable_weightedTruncatedPrimeAtom (w : ℕ → ℝ) {V : ℝ} (hV : 0 < V)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    Summable (weightedTruncatedPrimeAtom w V S b) := by
  refine summable_of_ne_finset_zero (s := Finset.range (⌊2 * V⌋₊ + 1)) fun r hr => ?_
  rw [Finset.mem_range, not_lt] at hr
  have hgt : 2 * V < (r : ℝ) :=
    lt_of_lt_of_le (Nat.lt_floor_add_one (2 * V)) (by exact_mod_cast hr)
  exact weightedTruncatedPrimeAtom_eq_zero_of_gt hV S b hgt

/-- **Exact Weil Functional Identity for General Arithmetic Weights on Compact Critical Sources.**
For every arithmetic weight `w : ℕ → ℝ`, every truncation `V > 0`, and every pattern `(S, b)`,
the real part of `weilFullFunctional w` on `criticalTruncatedTest hV S b` equals the `ζ` energy
`compactFullWeilEnergy` with `criticalTruncatedPrimeEnergy` replaced by `weightedTruncatedPrimeEnergy w`. -/
theorem re_weilFullFunctional_criticalTruncatedTest_eq (w : ℕ → ℝ) {V : ℝ} (hV : 0 < V)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    (weilFullFunctional w
      (EF.weilTest (fun x => (criticalTruncatedTest hV S b x : ℂ))
        (fun x => (criticalTruncatedTest hV S b x : ℂ)))).re =
      compactFullWeilEnergy (criticalTruncatedTest hV S b) +
        2 * criticalTruncatedPrimeEnergy V S b -
        2 * weightedTruncatedPrimeEnergy w V S b := by
  set f := criticalTruncatedTest hV S b
  set g := criticalTruncatedSource V S b
  set k := EF.weilTest (fun x => (f x : ℂ)) (fun x => (f x : ℂ))
  have hΛ : compactFullWeilEnergy f =
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) k).re := rfl
  have hk_apply : ∀ y : ℝ, k y = (sourceAutocorrelation g y : ℂ) := by
    intro y
    change EF.weilTest (liftC g) (liftC g) y = _
    rw [weilTest_liftC]
    rfl
  have hk_symm : ∀ y : ℝ, sourceAutocorrelation g (-y) = sourceAutocorrelation g y := by
    intro y
    change autoCorr g (-y) = autoCorr g y
    exact autoCorr_neg g y
  have hterm : ∀ u : ℕ → ℝ, ∀ r : ℕ,
      (((if 2 ≤ r then u r / Real.sqrt r else 0 : ℝ) : ℂ) *
        (k (Real.log r) + k (-Real.log r))).re =
      2 * weightedTruncatedPrimeAtom u V S b r := by
    intro u r
    rw [hk_apply, hk_apply, hk_symm, ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re]
    unfold weightedTruncatedPrimeAtom sourceAutocorrelation
    split_ifs <;> ring
  have hsum_re : ∀ u : ℕ → ℝ,
      (∑' r : ℕ, ((if 2 ≤ r then u r / Real.sqrt r else 0 : ℝ) : ℂ) *
        (k (Real.log r) + k (-Real.log r))).re =
      2 * weightedTruncatedPrimeEnergy u V S b := by
    intro u
    have hs : Summable fun r : ℕ =>
        ((if 2 ≤ r then u r / Real.sqrt r else 0 : ℝ) : ℂ) *
          (k (Real.log r) + k (-Real.log r)) := by
      refine summable_of_ne_finset_zero (s := Finset.range (⌊2 * V⌋₊ + 1)) fun r hr => ?_
      rw [Finset.mem_range, not_lt] at hr
      have hgt : 2 * V < (r : ℝ) :=
        lt_of_lt_of_le (Nat.lt_floor_add_one (2 * V)) (by exact_mod_cast hr)
      have hzero : (fun x : ℝ =>
          criticalTruncatedSource V S b x * criticalTruncatedSource V S b (x - Real.log r)) =
          fun _ => 0 := by
        funext x
        by_cases hx : x ∈ Icc (-Real.log (2 * V)) 0
        · have hnot : x - Real.log r ∉ Icc (-Real.log (2 * V)) 0 := by
            intro hmem
            have hlog : Real.log (2 * V) < Real.log r :=
              Real.log_lt_log (by positivity) hgt
            linarith [hx.2, hmem.1]
          rw [criticalTruncatedSource_eq_zero hV S b hnot, mul_zero]
        · rw [criticalTruncatedSource_eq_zero hV S b hx, zero_mul]
      rw [hk_apply, hk_apply, hk_symm]
      change _ * ((sourceAutocorrelation g (Real.log r) : ℂ) +
        (sourceAutocorrelation g (Real.log r) : ℂ)) = 0
      unfold sourceAutocorrelation
      rw [hzero, integral_zero, Complex.ofReal_zero, add_zero, mul_zero]
    rw [Complex.re_tsum hs]
    simp_rw [hterm u]
    rw [tsum_mul_left]
    rfl
  rw [hΛ]
  unfold weilFullFunctional
  simp only [Complex.add_re, Complex.sub_re]
  rw [hsum_re w, hsum_re (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)),
    weightedTruncatedPrimeEnergy_vonMangoldt]
  ring

/-- Pointwise bound on `weightedTruncatedPrimeAtom w` for any `C`-tempered weight `w`. -/
theorem abs_weightedTruncatedPrimeAtom_le_of_tempered {w : ℕ → ℝ} {C : ℝ}
    (hw : TemperedPrimeWeight w C) (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) :
    |weightedTruncatedPrimeAtom w V S b r| ≤ C * |criticalTruncatedPrimeAtom V S b r| := by
  unfold weightedTruncatedPrimeAtom criticalTruncatedPrimeAtom
  split_ifs with hr
  · rw [abs_mul, abs_mul, abs_div, abs_div, ← mul_assoc,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hw.2 r hr) (abs_nonneg _)
  · simp

/-- **Uniform-in-`V` logarithmic prime-window bound for arbitrary `C`-tempered weights.**
For every `w` satisfying `TemperedPrimeWeight w C`, every truncation `V > 0`, and every scale window
`ScaleWindow S M L` (`M, L ≥ 1`),
`|weightedTruncatedPrimeEnergy w V S b| ≤ C * criticalTruncatedWindowPrimeSlope * (3 + log L) ∑ b_n²`
uniformly in `V`. -/
theorem abs_weightedTruncatedPrimeEnergy_le_of_window {w : ℕ → ℝ} {C : ℝ}
    (hw : TemperedPrimeWeight w C) {V : ℝ} (hV : 0 < V) {S : Finset ℕ} {M L : ℕ}
    (hM : 1 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L) (b : ℕ → ℝ) :
    |weightedTruncatedPrimeEnergy w V S b| ≤
      C * criticalTruncatedWindowPrimeSlope * (3 + Real.log L) * ∑ n ∈ S, b n ^ 2 := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
  set ε := 1 / (2 + Real.log L)
  have hε0 : 0 < ε := by positivity
  have hε : ε ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  set K := 4 / Real.pi ^ 4 * criticalTruncatedWindowConstant * E
  have hK : 0 ≤ K := by have := criticalTruncatedWindowConstant_nonneg; positivity
  have hs : (1 : ℝ) < 1 + ε := by linarith
  have hsum := RHTower.summable_vonMangoldt_div_rpow_mertensVonMangoldtEulerConstant hs
  have hbd (r : ℕ) : |weightedTruncatedPrimeAtom w V S b r| ≤
      C * K * (L : ℝ) ^ ε * ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ (1 + ε)) := by
    refine (abs_weightedTruncatedPrimeAtom_le_of_tempered hw V S b r).trans ?_
    have hatom := abs_criticalTruncatedPrimeAtom_le_of_window hV hM hL hS b r
    have hC := hw.1
    refine (mul_le_mul_of_nonneg_left hatom hC).trans ?_
    split_ifs with hr
    · have hr0 : (0 : ℝ) < r := by positivity
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := r)
      have hmin : min 1 (Real.sqrt (L / r)) ≤ (L / r) ^ ε := by
        rcases le_or_gt (r : ℝ) L with h | h
        · exact (min_le_left _ _).trans (Real.one_le_rpow (by rw [le_div_iff₀ hr0]; linarith) hε0.le)
        · refine (min_le_right _ _).trans ?_
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_ge (by positivity) (by rw [div_le_one hr0]; linarith) hε
      have hpow : (r : ℝ) ^ (1 + ε) = r * r ^ ε := by rw [Real.rpow_add hr0, Real.rpow_one]
      rw [hpow, Real.div_rpow hL0.le hr0.le] at *
      have hK0 := criticalTruncatedWindowConstant_nonneg
      calc C * ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
            (4 / Real.pi ^ 4 * (criticalTruncatedWindowConstant * min 1 (Real.sqrt (L / r)))) * E)
          ≤ C * ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) *
            (4 / Real.pi ^ 4 * (criticalTruncatedWindowConstant * ((L : ℝ) ^ ε / (r : ℝ) ^ ε))) * E) := by
            gcongr
        _ = C * K * (L : ℝ) ^ ε * ((ArithmeticFunction.vonMangoldt r : ℝ) / (r * r ^ ε)) := by
            unfold K; field_simp
    · rw [mul_zero]
      have := ArithmeticFunction.vonMangoldt_nonneg (n := r)
      have hrp : 0 ≤ (r : ℝ) ^ (1 + ε) := Real.rpow_nonneg (Nat.cast_nonneg r) _
      positivity
  have hmaj : Summable fun r : ℕ =>
      C * K * (L : ℝ) ^ ε * ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ (1 + ε)) :=
    hsum.mul_left _
  have habs : Summable fun r => ‖weightedTruncatedPrimeAtom w V S b r‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun r => by rw [Real.norm_eq_abs]; exact hbd r) hmaj
  unfold weightedTruncatedPrimeEnergy
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm habs).trans ((habs.tsum_le_tsum (fun r => by
    rw [Real.norm_eq_abs]; exact hbd r) hmaj).trans ?_)
  rw [tsum_mul_left]
  have hsix := RHTower.tsum_vonMangoldt_div_rpow_le_six hs
  have hLε : (L : ℝ) ^ ε ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hL0]
    refine Real.exp_le_exp.mpr ?_
    unfold ε
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  have hfrac : 6 * (1 + ε) / (1 + ε - 1) = 6 * (3 + Real.log L) := by
    unfold ε; field_simp; ring
  rw [hfrac] at hsix
  have hC := hw.1
  calc C * K * (L : ℝ) ^ ε * ∑' r : ℕ, (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ (1 + ε)
      ≤ C * K * Real.exp 1 * (6 * (3 + Real.log L)) := by gcongr
    _ = C * criticalTruncatedWindowPrimeSlope * (3 + Real.log L) * E := by
        unfold K criticalTruncatedWindowPrimeSlope; ring

/-- **Uniform-in-`V` Polynomial Scale-Window Positivity for Arbitrary `C`-Tempered Prime Weights.**
For every constant `C ≥ 0`, there exist a polynomial window exponent `δ > 0` and a scale threshold
`M₀ : ℕ` (both independent of `V`) such that for **every** arithmetic weight `w : ℕ → ℝ` satisfying
`TemperedPrimeWeight w C`, every `M ≥ M₀`, every window `[M, LM]` with `L ≤ M^δ`, every truncation
`V ≥ criticalTruncationThreshold` (support `[-log(2V), 0]` of arbitrarily large length), every
`ScaleWindow S M L`, and every nonzero `b`,
`0 < (s_T / 4) log M ∑_{n ∈ S} b_n² ≤ (weilFullFunctional w (EF.weilTest g^V g^V)).re`. -/
theorem exists_temperedWeight_polynomial_window_weilFullFunctional_pos (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M₀ : ℕ, ∀ w : ℕ → ℝ, TemperedPrimeWeight w C →
      ∀ M ≥ M₀, ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ (M : ℝ) ^ δ →
        ∀ V : ℝ, ∀ hVpos : 0 < V, criticalTruncationThreshold ≤ V →
          ∀ S : Finset ℕ, ScaleWindow S M L → ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
            0 < criticalTruncatedArchLogSlope / 4 * Real.log M * ∑ n ∈ S, b n ^ 2 ∧
            criticalTruncatedArchLogSlope / 4 * Real.log M * ∑ n ∈ S, b n ^ 2 ≤
              (weilFullFunctional w
                (EF.weilTest (fun x => (criticalTruncatedTest hVpos S b x : ℂ))
                  (fun x => (criticalTruncatedTest hVpos S b x : ℂ)))).re := by
  set s := criticalTruncatedArchLogSlope
  have hs : 0 < s := criticalTruncatedArchLogSlope_pos
  set W := C * criticalTruncatedWindowPrimeSlope
  have hW : 0 ≤ W := mul_nonneg hC criticalTruncatedWindowPrimeSlope_nonneg
  set δ := s / (4 * (W + 1))
  have hδ : 0 < δ := by positivity
  set K := s * criticalTruncatedArchLogOffset + criticalTruncatedWindowBaseConstant + 6 * W
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((hlog.eventually_gt_atTop (4 * K / s)).and
    (eventually_ge_atTop 2))
  refine ⟨δ, hδ, M₀, fun w hw M hM L hL hLM V hVpos hV S hS b hb => ?_⟩
  obtain ⟨hlogM, hM2⟩ := hM₀ M hM
  obtain ⟨j, hj, hbj⟩ := hb
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 < E :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogL : Real.log L ≤ δ * Real.log M := by
    have := Real.log_le_log hL0 hLM
    rwa [Real.log_rpow hMpos] at this
  have hlogM_pos : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hgap : s / 4 * Real.log M ≤
      s * (Real.log M - criticalTruncatedArchLogOffset) - criticalTruncatedWindowBaseConstant -
        2 * W * (3 + Real.log L) := by
    have h1 : 2 * W * Real.log L ≤ s / 2 * Real.log M := by
      calc 2 * W * Real.log L ≤ 2 * W * (δ * Real.log M) := by gcongr
        _ = s / 2 * Real.log M * (W / (W + 1)) := by unfold δ; field_simp; ring
        _ ≤ s / 2 * Real.log M * 1 := by
            gcongr
            rw [div_le_one (by linarith)]; linarith
        _ = s / 2 * Real.log M := by ring
    have h2 : K < s / 4 * Real.log M := by
      have := (div_lt_iff₀ hs).mp hlogM
      linarith
    unfold K at h2
    linarith
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  have hlev_ch : (s * (Real.log M - criticalTruncatedArchLogOffset) -
      criticalTruncatedWindowBaseConstant) * E ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos S b) +
        2 * criticalTruncatedPrimeEnergy V S b := by
    set X := s * (Real.log M - criticalTruncatedArchLogOffset) * E
    have hlev : (X : EReal) ≤ (sourceLevyEnergy (criticalTruncatedSource V S b) : EReal) := by
      have h1 := ofReal_le_criticalTruncatedLevyEnergy S b hM2 (fun n hn => (hS n hn).1) hV
      have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
      rw [EReal.coe_ennreal_ofReal] at h2
      exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
    set ac := sourceAutocorrelation (criticalTruncatedSource V S b) 0
    have hac0 : 0 ≤ ac := integral_nonneg fun y => by simp only [sub_zero]; exact mul_self_nonneg _
    have hac := sourceAutocorrelation_criticalTruncatedSource_zero_le V S b
    have hΩ : -(|EF.gammaBracket 0| * (criticalCollarMassUpper * E)) ≤ EF.gammaBracket 0 * ac := by
      have h1 : -(|EF.gammaBracket 0| * ac) ≤ EF.gammaBracket 0 * ac := by
        have := neg_abs_le (EF.gammaBracket 0 * ac)
        rwa [abs_mul, abs_of_nonneg hac0] at this
      have h2 : |EF.gammaBracket 0| * ac ≤ |EF.gammaBracket 0| * (criticalCollarMassUpper * E) :=
        mul_le_mul_of_nonneg_left hac (abs_nonneg _)
      linarith
    set T := ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
    have hT2 := sq_sum_abs_div_succ_le S b hM2 fun n hn => (hS n hn).1
    have hM0 : (2 : ℝ) ≤ M := by exact_mod_cast hM2
    have hTE : T ^ 2 ≤ E := hT2.trans (by
      have : 2 / (M : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM0
      nlinarith)
    have ha0 : 0 ≤ criticalTruncatedReadoutConstant := by
      unfold criticalTruncatedReadoutConstant
      have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarWeight v| := integral_nonneg fun _ => abs_nonneg _
      have := smoothTransitionSlope_nonneg
      have : 0 ≤ criticalCollarMass := integral_nonneg fun _ => abs_nonneg _
      positivity
    have hc0 : 0 ≤ criticalTruncatedEndpointConstant := by
      unfold criticalTruncatedEndpointConstant
      have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v| :=
        integral_nonneg fun _ => abs_nonneg _
      have := smoothTransitionSlope_nonneg
      positivity
    have hpol : |criticalTruncatedPolarReadout V S b * criticalTruncatedPolarEndpoint V S b| ≤
        144 * criticalTruncatedReadoutConstant * criticalTruncatedEndpointConstant * E := by
      rw [abs_mul]
      have h1 := abs_criticalTruncatedPolarReadout_le hVpos S b
      have h2 := abs_criticalTruncatedPolarEndpoint_le hV1 S b
      have h12 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      calc _ ≤ criticalTruncatedReadoutConstant * (12 * T) *
            (criticalTruncatedEndpointConstant * (12 * T)) := h12
        _ = 144 * criticalTruncatedReadoutConstant * criticalTruncatedEndpointConstant * T ^ 2 := by ring
        _ ≤ 144 * criticalTruncatedReadoutConstant * criticalTruncatedEndpointConstant * E :=
            mul_le_mul_of_nonneg_left hTE (by positivity)
    have hpol' := (abs_le.mp hpol).1
    have hbase : -(criticalTruncatedWindowBaseConstant * E) ≤
        EF.gammaBracket 0 * ac +
          2 * (criticalTruncatedPolarReadout V S b * criticalTruncatedPolarEndpoint V S b) := by
      unfold criticalTruncatedWindowBaseConstant
      nlinarith
    have hcomp := compactFullWeilEnergy_criticalTruncatedTest hVpos S b
    unfold criticalTruncatedCompleteEnergy at hcomp
    have hsum_er :
        ((X + (EF.gammaBracket 0 * ac +
          2 * (criticalTruncatedPolarReadout V S b * criticalTruncatedPolarEndpoint V S b) -
          2 * criticalTruncatedPrimeEnergy V S b) : ℝ) : EReal) ≤
          (compactFullWeilEnergy (criticalTruncatedTest hVpos S b) : EReal) := by
      rw [hcomp, EReal.coe_add]
      exact add_le_add hlev le_rfl
    have hreal := EReal.coe_le_coe_iff.mp hsum_er
    linarith
  have hPw := abs_weightedTruncatedPrimeEnergy_le_of_window hw hVpos (by omega) hL hS b
  have hPw' := (abs_le.mp hPw).2
  rw [re_weilFullFunctional_criticalTruncatedTest_eq w hVpos S b]
  refine ⟨by positivity, ?_⟩
  have h1 := mul_le_mul_of_nonneg_right hgap hE.le
  dsimp only [W] at h1
  linarith

/-- The Liouville-twisted von Mangoldt weight `w_λ(r) = (-1)^{Ω(r)} Λ(r)`. -/
def liouvilleTwistVonMangoldt (r : ℕ) : ℝ :=
  (-1 : ℝ) ^ ArithmeticFunction.cardFactors r * (ArithmeticFunction.vonMangoldt r : ℝ)

/-- The Liouville-twisted von Mangoldt weight `w_λ(r) = (-1)^{Ω(r)} Λ(r)` is `1`-tempered. -/
theorem temperedPrimeWeight_liouvilleTwist :
    TemperedPrimeWeight liouvilleTwistVonMangoldt 1 := by
  refine ⟨zero_le_one, fun r _ => ?_⟩
  unfold liouvilleTwistVonMangoldt
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, one_mul,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- The node-`4`-deleted von Mangoldt weight `Λ · 1_{r ≠ 4}` is `1`-tempered. -/
theorem temperedPrimeWeight_deletedFour :
    TemperedPrimeWeight
      (fun r => if r = 4 then 0 else (ArithmeticFunction.vonMangoldt r : ℝ)) 1 := by
  refine ⟨zero_le_one, fun r _ => ?_⟩
  dsimp only
  rw [one_mul]
  split_ifs
  · rw [abs_zero]; exact ArithmeticFunction.vonMangoldt_nonneg
  · rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- The primes-only von Mangoldt weight `Λ · 1_{r prime}` is `1`-tempered. -/
theorem temperedPrimeWeight_primesOnly :
    TemperedPrimeWeight
      (fun r => if r.Prime then (ArithmeticFunction.vonMangoldt r : ℝ) else 0) 1 := by
  refine ⟨zero_le_one, fun r _ => ?_⟩
  dsimp only
  rw [one_mul]
  split_ifs
  · rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  · rw [abs_zero]; exact ArithmeticFunction.vonMangoldt_nonneg

/-- **Beurling and Node-Deletion Selectivity Synthesis.**
1. *Invariance on the critical family*: The Liouville-twisted weight `(-1)^{Ω(r)} Λ(r)`, the
   node-`4`-deleted weight `Λ · 1_{r ≠ 4}`, and the primes-only weight `Λ · 1_{r prime}` all
   satisfy the exact same uniform-in-`V` polynomial scale-window Weil positivity on
   `criticalTruncatedTest hVpos S b` as `Λ` itself.
2. *Beurling off-line zero instability at arbitrarily small reciprocal mass*: For every
   `β ∈ (1/2, 1)` and `ε > 0`, `BeurlingSensitivity.rh_sensitivity_threshold` produces a positive
   generalized-prime density `adjoinedDensity β γ` with reciprocal mass `< ε` whose enlarged zeta
   `perturbedZeta β γ` vanishes at the off-line point `β + iγ`.
3. *Unconditional refutation by node-criticality tests*: Deleting `4` (with exact deletion price
   `-(log 2 / 2)`) or restricting to primes `{p | p.Prime}` (which misses `4 = 2²`) refutes
   `ZeroPoleBlindPositiveOn` unconditionally. -/
theorem beurling_offLine_zero_system_vs_critical_infrastructure {β : ℝ} (hβ1 : 1 / 2 < β)
    (hβ2 : β < 1) {ε : ℝ} (hε : 0 < ε) :
    (∃ δ : ℝ, 0 < δ ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ (M : ℝ) ^ δ →
      ∀ V : ℝ, ∀ hVpos : 0 < V, criticalTruncationThreshold ≤ V →
        ∀ S : Finset ℕ, ScaleWindow S M L → ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
          0 < (weilFullFunctional
                liouvilleTwistVonMangoldt
                (EF.weilTest (fun x => (criticalTruncatedTest hVpos S b x : ℂ))
                  (fun x => (criticalTruncatedTest hVpos S b x : ℂ)))).re ∧
          0 < (weilFullFunctional
                (fun r => if r = 4 then 0 else (ArithmeticFunction.vonMangoldt r : ℝ))
                (EF.weilTest (fun x => (criticalTruncatedTest hVpos S b x : ℂ))
                  (fun x => (criticalTruncatedTest hVpos S b x : ℂ)))).re ∧
          0 < (weilFullFunctional
                (fun r => if r.Prime then (ArithmeticFunction.vonMangoldt r : ℝ) else 0)
                (EF.weilTest (fun x => (criticalTruncatedTest hVpos S b x : ℂ))
                  (fun x => (criticalTruncatedTest hVpos S b x : ℂ)))).re) ∧
    (∃ γ : ℝ, 0 < γ ∧
      (∀ t : ℝ, 0 < t → 0 ≤ RHTower.BeurlingSensitivity.adjoinedDensity β γ t) ∧
      (∫ t in Ioi (0 : ℝ), Real.exp (-(1 * t)) *
        RHTower.BeurlingSensitivity.adjoinedDensity β γ t) < ε ∧
      RHTower.BeurlingSensitivity.perturbedZeta β γ ((β : ℂ) + (γ : ℂ) * I) = 0 ∧
      1 / 2 < ((β : ℂ) + (γ : ℂ) * I).re) ∧
    (¬ BiScaleUncertainty.ZeroPoleBlindPositiveOn (Set.univ \ {4}) ∧
      ¬ BiScaleUncertainty.ZeroPoleBlindPositiveOn {p : ℕ | p.Prime} ∧
      IsLeast (BiScaleUncertainty.deletionDeviations 4) (-(Real.log 2 / 2))) := by
  obtain ⟨δ, hδ, M₀, hwin⟩ := exists_temperedWeight_polynomial_window_weilFullFunctional_pos 1 zero_le_one
  obtain ⟨γ, hγ, hnn, -, -, hrec, -, hzero, hre⟩ :=
    RHTower.BeurlingSensitivity.rh_sensitivity_threshold hβ1 hβ2 hε
  refine ⟨⟨δ, hδ, M₀, fun M hM L hL hLM V hVpos hV S hS b hb => ?_⟩,
    ⟨γ, hγ, hnn, hrec, hzero, hre⟩,
    ⟨BiScaleUncertainty.not_zeroPoleBlindPositiveOn_diff_four Set.univ,
      BiScaleUncertainty.not_zeroPoleBlindPositiveOn_primes,
      BiScaleUncertainty.isLeast_deletionDeviations_four⟩⟩
  have h1 := hwin _ temperedPrimeWeight_liouvilleTwist M hM L hL hLM V hVpos hV S hS b hb
  have h2 := hwin _ temperedPrimeWeight_deletedFour M hM L hL hLM V hVpos hV S hS b hb
  have h3 := hwin _ temperedPrimeWeight_primesOnly M hM L hL hLM V hVpos hV S hS b hb
  exact ⟨lt_of_lt_of_le h1.1 h1.2, lt_of_lt_of_le h2.1 h2.2, lt_of_lt_of_le h3.1 h3.2⟩

/-- At any **fixed** truncation `V > 0`, every prime weight `w : ℕ → ℝ` is `C`-tempered on the
support of `weightedTruncatedPrimeAtom w V S b` because all atoms with `r > ⌊2V⌋` vanish. -/
theorem abs_weightedTruncatedPrimeEnergy_le_at_fixed_V (w : ℕ → ℝ) {V : ℝ} (hV : 0 < V)
    {S : Finset ℕ} {M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L) (b : ℕ → ℝ) :
    |weightedTruncatedPrimeEnergy w V S b| ≤
      (∑ r ∈ Finset.range (⌊2 * V⌋₊ + 1), |w r|) *
        (4 / Real.pi ^ 4 * criticalTruncatedWindowConstant) * ∑ n ∈ S, b n ^ 2 := by
  unfold weightedTruncatedPrimeEnergy
  rw [tsum_eq_sum (s := Finset.range (⌊2 * V⌋₊ + 1))]
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun r _ => ?_
    unfold weightedTruncatedPrimeAtom
    split_ifs with hr2
    · have hr0 : (0 : ℝ) < r := by positivity
      have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
      have hl : 0 ≤ (r : ℝ) / V := by positivity
      have hw : (∫ v in Ioi 1, criticalCollarWeight v * criticalUpperCutoff (r * v / V) *
          (realPhaseCombination S b v * realPhaseCombination S b (r * v))) =
          ∫ v in Ioi 1, criticalTruncatedWeight ((r : ℝ) / V) v *
            (realPhaseCombination S b v * realPhaseCombination S b (r * v)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
        simp only [criticalTruncatedWeight]
        rw [show (r : ℝ) / V * v = r * v / V by ring]
      have hK0 := criticalTruncatedWindowConstant_nonneg
      have hE0 : 0 ≤ ∑ n ∈ S, b n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hmin1 : min 1 (Real.sqrt (L / r)) ≤ 1 := min_le_left _ _
      have hcorr : |∫ v in Ioi 1, criticalTruncatedWeight ((r : ℝ) / V) v *
          (realPhaseCombination S b v * realPhaseCombination S b (r * v))| ≤
          4 / Real.pi ^ 4 * (criticalTruncatedWindowConstant * 1) * ∑ n ∈ S, b n ^ 2 :=
        (abs_criticalTruncatedWindowCorrelation_le hl hM hL hS b (r := r) (by omega)).trans
          (by gcongr)
      have hint_eq := integral_criticalTruncatedSource_mul_dilate hV S b hr2
      rw [hint_eq, hw, abs_mul, abs_mul, abs_div, abs_of_pos hsr,
        abs_of_pos (by positivity : 0 < 1 / Real.sqrt r)]
      have hrr : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0.le
      have hdiv_le : |w r| / (r : ℝ) ≤ |w r| :=
        div_le_self (abs_nonneg _) (by exact_mod_cast (by omega : 1 ≤ r))
      calc |w r| / Real.sqrt r * (1 / Real.sqrt r * |_|)
          ≤ |w r| / Real.sqrt r * (1 / Real.sqrt r *
              (4 / Real.pi ^ 4 * (criticalTruncatedWindowConstant * 1) * ∑ n ∈ S, b n ^ 2)) := by
            gcongr
        _ = (|w r| / (Real.sqrt r * Real.sqrt r)) *
              (4 / Real.pi ^ 4 * criticalTruncatedWindowConstant) * ∑ n ∈ S, b n ^ 2 := by ring
        _ = (|w r| / (r : ℝ)) *
              (4 / Real.pi ^ 4 * criticalTruncatedWindowConstant) * ∑ n ∈ S, b n ^ 2 := by rw [hrr]
        _ ≤ |w r| * (4 / Real.pi ^ 4 * criticalTruncatedWindowConstant) * ∑ n ∈ S, b n ^ 2 := by
            gcongr
    · have hK0 := criticalTruncatedWindowConstant_nonneg
      have hE0 : 0 ≤ ∑ n ∈ S, b n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      rw [zero_mul, abs_zero]
      positivity
  · intro r hr
    rw [Finset.mem_range, not_lt] at hr
    have hgt : 2 * V < (r : ℝ) :=
      lt_of_lt_of_le (Nat.lt_floor_add_one (2 * V)) (by exact_mod_cast hr)
    exact weightedTruncatedPrimeAtom_eq_zero_of_gt hV S b hgt

/-- **Quantifier Separation (`∀ V, ∃ M₀` vs. `∃ M₀, ∀ V`) on the Critical Family.**
At any **fixed** truncation `V ≥ criticalTruncationThreshold` and **any** arithmetic weight
`w : ℕ → ℝ` whatsoever (including the non-tempered shifted pair `shiftedPairVonMangoldt a` for any
`a ≠ 0`), because only primes `r ≤ ⌊2V⌋` enter `criticalTruncatedSource V S b`, there exists a
scale threshold `M₀(w, V)` such that for all `M ≥ M₀(w, V)` and all windows `[M, LM]` (`L ≥ 1`),
`0 < (s_T / 2) log M ∑_{n ∈ S} b_n² ≤ (weilFullFunctional w (EF.weilTest g^V g^V)).re`.
Thus what separates tempered weights from `shiftedPairVonMangoldt a` on the critical family is
**uniformity in `V`** (`∃ M₀, ∀ M ≥ M₀, ∀ V ≥ V₀`). -/
theorem exists_fixedV_polynomial_window_pos_for_any_weight (w : ℕ → ℝ) {V : ℝ}
    (hVpos : 0 < V) (hV : criticalTruncationThreshold ≤ V) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ L : ℕ, 1 ≤ L →
      ∀ S : Finset ℕ, ScaleWindow S M L → ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
        0 < criticalTruncatedArchLogSlope / 2 * Real.log M * ∑ n ∈ S, b n ^ 2 ∧
        criticalTruncatedArchLogSlope / 2 * Real.log M * ∑ n ∈ S, b n ^ 2 ≤
          (weilFullFunctional w
            (EF.weilTest (fun x => (criticalTruncatedTest hVpos S b x : ℂ))
              (fun x => (criticalTruncatedTest hVpos S b x : ℂ)))).re := by
  set s := criticalTruncatedArchLogSlope
  have hs : 0 < s := criticalTruncatedArchLogSlope_pos
  set Wv := (∑ r ∈ Finset.range (⌊2 * V⌋₊ + 1), |w r|) *
    (4 / Real.pi ^ 4 * criticalTruncatedWindowConstant)
  set K := s * criticalTruncatedArchLogOffset + criticalTruncatedWindowBaseConstant + 2 * Wv
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((hlog.eventually_gt_atTop (2 * K / s)).and
    (eventually_ge_atTop 2))
  refine ⟨M₀, fun M hM L hL S hS b hb => ?_⟩
  obtain ⟨hlogM, hM2⟩ := hM₀ M hM
  obtain ⟨j, hj, hbj⟩ := hb
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 < E :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj)
  have hlogM_pos : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  have hlev_ch : (s * (Real.log M - criticalTruncatedArchLogOffset) -
      criticalTruncatedWindowBaseConstant) * E ≤
      compactFullWeilEnergy (criticalTruncatedTest hVpos S b) +
        2 * criticalTruncatedPrimeEnergy V S b := by
    set X := s * (Real.log M - criticalTruncatedArchLogOffset) * E
    have hlev : (X : EReal) ≤ (sourceLevyEnergy (criticalTruncatedSource V S b) : EReal) := by
      have h1 := ofReal_le_criticalTruncatedLevyEnergy S b hM2 (fun n hn => (hS n hn).1) hV
      have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
      rw [EReal.coe_ennreal_ofReal] at h2
      exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
    set ac := sourceAutocorrelation (criticalTruncatedSource V S b) 0
    have hac0 : 0 ≤ ac := integral_nonneg fun y => by simp only [sub_zero]; exact mul_self_nonneg _
    have hac := sourceAutocorrelation_criticalTruncatedSource_zero_le V S b
    have hΩ : -(|EF.gammaBracket 0| * (criticalCollarMassUpper * E)) ≤ EF.gammaBracket 0 * ac := by
      have h1 : -(|EF.gammaBracket 0| * ac) ≤ EF.gammaBracket 0 * ac := by
        have := neg_abs_le (EF.gammaBracket 0 * ac)
        rwa [abs_mul, abs_of_nonneg hac0] at this
      have h2 : |EF.gammaBracket 0| * ac ≤ |EF.gammaBracket 0| * (criticalCollarMassUpper * E) :=
        mul_le_mul_of_nonneg_left hac (abs_nonneg _)
      linarith
    set T := ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
    have hT2 := sq_sum_abs_div_succ_le S b hM2 fun n hn => (hS n hn).1
    have hM0 : (2 : ℝ) ≤ M := by exact_mod_cast hM2
    have hTE : T ^ 2 ≤ E := hT2.trans (by
      have : 2 / (M : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM0
      nlinarith)
    have ha0 : 0 ≤ criticalTruncatedReadoutConstant := by
      unfold criticalTruncatedReadoutConstant
      have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarWeight v| := integral_nonneg fun _ => abs_nonneg _
      have := smoothTransitionSlope_nonneg
      have : 0 ≤ criticalCollarMass := integral_nonneg fun _ => abs_nonneg _
      positivity
    have hc0 : 0 ≤ criticalTruncatedEndpointConstant := by
      unfold criticalTruncatedEndpointConstant
      have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v| :=
        integral_nonneg fun _ => abs_nonneg _
      have := smoothTransitionSlope_nonneg
      positivity
    have hpol : |criticalTruncatedPolarReadout V S b * criticalTruncatedPolarEndpoint V S b| ≤
        144 * criticalTruncatedReadoutConstant * criticalTruncatedEndpointConstant * E := by
      rw [abs_mul]
      have h1 := abs_criticalTruncatedPolarReadout_le hVpos S b
      have h2 := abs_criticalTruncatedPolarEndpoint_le hV1 S b
      have h12 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      calc _ ≤ criticalTruncatedReadoutConstant * (12 * T) *
            (criticalTruncatedEndpointConstant * (12 * T)) := h12
        _ = 144 * criticalTruncatedReadoutConstant * criticalTruncatedEndpointConstant * T ^ 2 := by ring
        _ ≤ 144 * criticalTruncatedReadoutConstant * criticalTruncatedEndpointConstant * E :=
            mul_le_mul_of_nonneg_left hTE (by positivity)
    have hpol' := (abs_le.mp hpol).1
    have hcomp := compactFullWeilEnergy_criticalTruncatedTest hVpos S b
    unfold criticalTruncatedCompleteEnergy at hcomp
    have hsum_er :
        ((X + (EF.gammaBracket 0 * ac +
          2 * (criticalTruncatedPolarReadout V S b * criticalTruncatedPolarEndpoint V S b) -
          2 * criticalTruncatedPrimeEnergy V S b) : ℝ) : EReal) ≤
          (compactFullWeilEnergy (criticalTruncatedTest hVpos S b) : EReal) := by
      rw [hcomp, EReal.coe_add]
      exact add_le_add hlev le_rfl
    have hreal := EReal.coe_le_coe_iff.mp hsum_er
    unfold criticalTruncatedWindowBaseConstant
    linarith
  have hPw := abs_weightedTruncatedPrimeEnergy_le_at_fixed_V w hVpos (by omega) hL hS b
  have hPw' := (abs_le.mp hPw).2
  have hgap : s / 2 * Real.log M ≤
      s * (Real.log M - criticalTruncatedArchLogOffset) - criticalTruncatedWindowBaseConstant -
        2 * Wv := by
    have := (div_lt_iff₀ hs).mp hlogM
    unfold K at this
    linarith
  rw [re_weilFullFunctional_criticalTruncatedTest_eq w hVpos S b]
  refine ⟨by positivity, ?_⟩
  have h1 := mul_le_mul_of_nonneg_right hgap hE.le
  dsimp only [Wv] at h1
  linarith

end GaloisForLFunctions.ArithmeticPositivityTheory

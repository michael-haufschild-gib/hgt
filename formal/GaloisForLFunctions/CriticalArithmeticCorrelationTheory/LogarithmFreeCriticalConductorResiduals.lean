import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTopCollarHasADyadicSeventhPowerReserve
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BilinearConductorResidualsAndOneEighthPackets
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandOverlapAndNonRatioBounds
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.RamanujanAutocorrelationWeights

/-!
# Logarithm-Free Critical-Curve Conductor Residuals

On the critical overlap curve `c ≍ (log N)^{1/8}`, low conductors `1 ≤ m ≤ ⌊c⌋₊` have completed
energy `E_m(c) ≍ (m / c)^7`, so any `log c` or `(log N)^{1/k}` factor in either the low-conductor
bilinear residuals `⟪r_m, v_l⟫` or the top-collar Schur pairing against the far complement would
diverge against `(m / c)^7`. This module eliminates both factors through three exact mechanisms:

1. **Dual seventh-power top-collar norm (`topCollarDualSeventhMass`):** Paired against the
   dyadic seventh-power top-collar reserve `∑_{n > M} (N / n)^7 w_n^2`, Cauchy–Schwarz puts the
   dual weight `(n / N)^7 ≤ 1` on `r_m`. On the upward prime channel, `(n / N)^7 / n ≤ 1 / N`
   turns the deterministic linear shell bound `O(m c / √n)` directly into `O(m c^2 / log N)`
   with no Siegel–Walfisz input.
2. **Near-Gamma, downward-prime, and near-center cancellation:** At `m = 1`, the `log c` pole
   contributions of `normalizedFullNearGammaDownwardVector` and `nearCenterVector` cancel via
   `exactPoleCoefficient_eq` and the harmonic collar identity `archimedeanCenterKernel_div_sqrt_mul`;
   at `m ≥ 2`, zero-mean Ramanujan periodicity removes `log c` by summation by parts.
3. **Adjoint downward-divisor reduction of the upward bilinear pairing:** By exact transpose
   `⟪upwardPrimeVector φ c N v_m, v_l⟫ = ⟪v_m, downwardPrimeVector φ c N v_l⟫`, the prime sum
   collapses via `∑_{d | j} Λ(d) c_l(j / d) = c_l(j) log j - ramanujanLogDivisorJet l j` to an
   integer correlation sum whose `m = l` mean equals `shellCorrection φ c m` and whose `m ≠ l`
   mean vanishes by `sum_range_ramanujanLagCoefficient_shift_mul`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped BigOperators RealInnerProductSpace Matrix Classical

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open ArithmeticElectrostatics
  BezoutValuationIncidence
  CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell
  RenormalizedIntersectionTheory
  SignedArithmeticHodgeTheory
  SpacingScaleHarmonicAnalysis
  SuccessorShellArithmetic

/-! ## Section 1: Dual Seventh-Power Top-Collar Mass and Elementary Majorants -/

/-- Dual top-collar quadratic mass with weight `(n / N)^7 ≤ 1`, Cauchy–Schwarz dual to
`topCollarSeventhMass M N`. -/
def topCollarDualSeventhMass (M N : ℕ) (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) : ℝ :=
  ∑ n ∈ Ioc M N, ((n : ℝ) / N) ^ 7 * primeHorizonExtension u n ^ 2

theorem topCollarDualSeventhMass_nonneg (M N : ℕ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    0 ≤ topCollarDualSeventhMass M N u :=
  sum_nonneg fun _ _ => mul_nonneg (by positivity) (sq_nonneg _)

/-- Because `(n / N)^7 ≤ 1` on `Ioc M N`, the dual seventh-power collar mass never exceeds the
full Euclidean squared norm `‖u‖^2`. -/
theorem topCollarDualSeventhMass_le_norm_sq (M N : ℕ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    topCollarDualSeventhMass M N u ≤ ‖u‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · simp [topCollarDualSeventhMass]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hsub : Ioc M N ⊆ Icc 1 N := fun n hn => by
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hn
    exact mem_Icc.mpr ⟨by omega, h2⟩
  calc
    topCollarDualSeventhMass M N u
        ≤ ∑ n ∈ Ioc M N, primeHorizonExtension u n ^ 2 := by
          refine sum_le_sum fun n hn => ?_
          have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Ioc.mp hn).2
          have h1 : ((n : ℝ) / N) ^ 7 ≤ 1 :=
            pow_le_one₀ (by positivity) ((div_le_one hNR).mpr hnN)
          exact (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)).trans_eq (one_mul _)
    _ ≤ ∑ n ∈ Icc 1 N, primeHorizonExtension u n ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    _ = ‖u‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq, ← sum_coe_sort (Icc 1 N)]
          refine sum_congr rfl fun n _ => ?_
          rw [Real.norm_eq_abs, sq_abs, primeHorizonExtension_coe]

/-- Weighted prefix-collar Cauchy–Schwarz inequality pairing `topCollarDualSeventhMass` against
`topCollarSeventhMass`. -/
theorem inner_sq_le_prefix_add_topCollarSeventh {M N : ℕ} (hMN : M ≤ N)
    (u w : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪u, w⟫ ^ 2 ≤
      2 * (∑ n ∈ Icc 1 M, primeHorizonExtension u n ^ 2) *
          (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
        2 * topCollarDualSeventhMass M N u *
          topCollarSeventhMass M N (primeHorizonExtension w) := by
  have hsplit : Icc 1 N = Icc 1 M ∪ Ioc M N := by
    ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 M) (Ioc M N) :=
    disjoint_left.mpr fun n h1 h2 => by
      have := (mem_Icc.mp h1).2; have := (mem_Ioc.mp h2).1; omega
  have hinner : ⟪u, w⟫ =
      (∑ n ∈ Icc 1 M, primeHorizonExtension u n * primeHorizonExtension w n) +
        ∑ n ∈ Ioc M N, primeHorizonExtension u n * primeHorizonExtension w n := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ i : PrimeHorizonIndex N, w i * u i) = _
    have hsum : (∑ i : PrimeHorizonIndex N, w i * u i) =
        ∑ n ∈ Icc 1 N, primeHorizonExtension u n * primeHorizonExtension w n := by
      rw [← sum_coe_sort (Icc 1 N)]
      refine sum_congr rfl fun i _ => ?_
      rw [primeHorizonExtension_coe, primeHorizonExtension_coe, mul_comm]
    rw [hsum, hsplit, sum_union hdisj]
  set A := ∑ n ∈ Icc 1 M, primeHorizonExtension u n * primeHorizonExtension w n
  set B := ∑ n ∈ Ioc M N, primeHorizonExtension u n * primeHorizonExtension w n
  have h2ab : (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
    nlinarith [sq_nonneg (A - B)]
  have hA : A ^ 2 ≤ (∑ n ∈ Icc 1 M, primeHorizonExtension u n ^ 2) *
      (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 M)
      (fun n => primeHorizonExtension u n) (fun n => primeHorizonExtension w n)
  have hB : B ^ 2 ≤ topCollarDualSeventhMass M N u *
      topCollarSeventhMass M N (primeHorizonExtension w) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN0
    · simp [B, topCollarDualSeventhMass, topCollarSeventhMass]
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
    let f : ℕ → ℝ := fun n =>
      ((n : ℝ) / N) ^ 3 * (Real.sqrt n / Real.sqrt N) * primeHorizonExtension u n
    let g : ℕ → ℝ := fun n =>
      ((N : ℝ) / n) ^ 3 * (Real.sqrt N / Real.sqrt n) * primeHorizonExtension w n
    have hfg : B = ∑ n ∈ Ioc M N, f n * g n := by
      refine sum_congr rfl fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_le M).trans_lt (mem_Ioc.mp hn).1
      have hsn : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
      have hsN : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hNR).ne'
      dsimp only [f, g]
      field_simp [hn0.ne', hNR.ne', hsn, hsN]
    have hf2 : (∑ n ∈ Ioc M N, f n ^ 2) = topCollarDualSeventhMass M N u := by
      unfold topCollarDualSeventhMass
      refine sum_congr rfl fun n _ => ?_
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      dsimp only [f]
      rw [mul_pow, mul_pow, div_pow (Real.sqrt _), Real.sq_sqrt hn0, Real.sq_sqrt hNR.le]
      ring
    have hg2 : (∑ n ∈ Ioc M N, g n ^ 2) = topCollarSeventhMass M N (primeHorizonExtension w) := by
      unfold topCollarSeventhMass
      refine sum_congr rfl fun n _ => ?_
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      dsimp only [g]
      rw [mul_pow, mul_pow, div_pow (Real.sqrt _), Real.sq_sqrt hn0, Real.sq_sqrt hNR.le]
      ring
    rw [hfg, ← hf2, ← hg2]
    exact Finset.sum_mul_sq_le_sq_mul_sq (Ioc M N) f g
  rw [hinner]
  linarith

theorem topCollarDualSeventhMass_smul (M N : ℕ) (a : ℝ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    topCollarDualSeventhMass M N (a • u) = a ^ 2 * topCollarDualSeventhMass M N u := by
  unfold topCollarDualSeventhMass
  rw [mul_sum]
  refine sum_congr rfl fun n hn => ?_
  have hnIcc : n ∈ Icc 1 N := mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
  let idx : PrimeHorizonIndex N := ⟨n, hnIcc⟩
  have h1 : primeHorizonExtension (a • u) n = a * primeHorizonExtension u n := by
    change primeHorizonExtension (a • u) idx.1 = a * primeHorizonExtension u idx.1
    rw [primeHorizonExtension_coe, primeHorizonExtension_coe]
    rfl
  rw [h1]
  ring

theorem topCollarDualSeventhMass_neg (M N : ℕ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    topCollarDualSeventhMass M N (-u) = topCollarDualSeventhMass M N u := by
  rw [show (-u) = (-1 : ℝ) • u by simp, topCollarDualSeventhMass_smul]
  ring

theorem topCollarDualSeventhMass_add_le (M N : ℕ)
    (u v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    topCollarDualSeventhMass M N (u + v) ≤
      2 * topCollarDualSeventhMass M N u + 2 * topCollarDualSeventhMass M N v := by
  unfold topCollarDualSeventhMass
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun n hn => ?_
  have hnIcc : n ∈ Icc 1 N := mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
  let idx : PrimeHorizonIndex N := ⟨n, hnIcc⟩
  have hext : primeHorizonExtension (u + v) n =
      primeHorizonExtension u n + primeHorizonExtension v n := by
    change primeHorizonExtension (u + v) idx.1 =
      primeHorizonExtension u idx.1 + primeHorizonExtension v idx.1
    rw [primeHorizonExtension_coe, primeHorizonExtension_coe, primeHorizonExtension_coe]
    rfl
  rw [hext]
  have hw0 : 0 ≤ ((n : ℝ) / N) ^ 7 := by positivity
  have h2 : (primeHorizonExtension u n + primeHorizonExtension v n) ^ 2 ≤
      2 * primeHorizonExtension u n ^ 2 + 2 * primeHorizonExtension v n ^ 2 := by
    nlinarith [sq_nonneg (primeHorizonExtension u n - primeHorizonExtension v n)]
  have hm := mul_le_mul_of_nonneg_left h2 hw0
  linarith

/-- Seven-channel Cauchy–Schwarz inequality for `topCollarDualSeventhMass`. -/
theorem topCollarDualSeventhMass_seven_le (M N : ℕ)
    (u₁ u₂ u₃ u₄ u₅ u₆ u₇ : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    topCollarDualSeventhMass M N (u₁ + u₂ + u₃ + u₄ + u₅ + u₆ + u₇) ≤
      16 * (topCollarDualSeventhMass M N u₁ + topCollarDualSeventhMass M N u₂ +
        topCollarDualSeventhMass M N u₃ + topCollarDualSeventhMass M N u₄ +
        topCollarDualSeventhMass M N u₅ + topCollarDualSeventhMass M N u₆ +
        topCollarDualSeventhMass M N u₇) := by
  have h1 := topCollarDualSeventhMass_add_le M N ((u₁ + u₂) + (u₃ + u₄)) ((u₅ + u₆) + u₇)
  have h2 := topCollarDualSeventhMass_add_le M N (u₁ + u₂) (u₃ + u₄)
  have h3 := topCollarDualSeventhMass_add_le M N u₁ u₂
  have h4 := topCollarDualSeventhMass_add_le M N u₃ u₄
  have h5 := topCollarDualSeventhMass_add_le M N (u₅ + u₆) u₇
  have h6 := topCollarDualSeventhMass_add_le M N u₅ u₆
  have h01 := topCollarDualSeventhMass_nonneg M N u₁
  have h02 := topCollarDualSeventhMass_nonneg M N u₂
  have h03 := topCollarDualSeventhMass_nonneg M N u₃
  have h04 := topCollarDualSeventhMass_nonneg M N u₄
  have h05 := topCollarDualSeventhMass_nonneg M N u₅
  have h06 := topCollarDualSeventhMass_nonneg M N u₆
  have h07 := topCollarDualSeventhMass_nonneg M N u₇
  have heq : u₁ + u₂ + u₃ + u₄ + u₅ + u₆ + u₇ =
      ((u₁ + u₂) + (u₃ + u₄)) + ((u₅ + u₆) + u₇) := by abel
  rw [heq]
  linarith only [h1, h2, h3, h4, h5, h6, h01, h02, h03, h04, h05, h06, h07]

/-! ### Elementary Logarithm-to-Root Majorants and Telescoping Tails -/

/-- `2 + Real.log x ≤ 2 * Real.sqrt x` for `x > 0`. -/
theorem two_add_log_le_two_sqrt {x : ℝ} (hx : 0 < x) :
    2 + Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hlog : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  linarith [Real.log_le_sub_one_of_pos hs]

/-- Fourth-root logarithm majorant: `2 + Real.log x ≤ 4 * Real.sqrt (Real.sqrt x)` for `x > 0`. -/
theorem two_add_log_le_four_fourthRoot {x : ℝ} (hx : 0 < x) :
    2 + Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
  have hs1 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hs2 : 0 < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.mpr hs1
  have hlog1 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  have hlog2 : Real.log (Real.sqrt (Real.sqrt x)) = Real.log (Real.sqrt x) / 2 :=
    Real.log_sqrt hs1.le
  linarith [Real.log_le_sub_one_of_pos hs2]

theorem one_add_log_le_two_sqrt_pos {x : ℝ} (hx : 0 < x) :
    1 + Real.log x ≤ 2 * Real.sqrt x := by
  linarith [two_add_log_le_two_sqrt hx]

theorem one_add_log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) :
    (1 + Real.log x) ^ 2 ≤ 4 * x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have h1 := one_add_log_le_two_sqrt_pos hx0
  have h0 : 0 ≤ 1 + Real.log x := by linarith [Real.log_nonneg hx]
  calc
    (1 + Real.log x) ^ 2 ≤ (2 * Real.sqrt x) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 4 * x := by rw [mul_pow, Real.sq_sqrt hx0.le]; ring

theorem one_add_log_cube_le_eight_sq {c : ℝ} (hc : 1 ≤ c) :
    (1 + Real.log c) ^ 3 ≤ 8 * c ^ 2 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have h0 : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc]
  have h_tight : 1 + Real.log c ≤ 2 * Real.sqrt c := one_add_log_le_two_sqrt_pos hc0
  have hc_sq : c ≤ c ^ 2 := by nlinarith
  calc
    (1 + Real.log c) ^ 3 ≤ (2 * Real.sqrt c) ^ 3 := pow_le_pow_left₀ h0 h_tight 3
    _ = 8 * c * Real.sqrt c := by
      have : (Real.sqrt c) ^ 3 = c * Real.sqrt c := by
        rw [pow_succ, Real.sq_sqrt hc0.le]
      rw [mul_pow, this]; ring
    _ ≤ 8 * c * c := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact Real.sqrt_le_iff.mpr ⟨hc0.le, hc_sq⟩
    _ = 8 * c ^ 2 := by ring

/-- Telescoping tail bound `∑_{n ∈ Ioc M N} 1 / n^2 ≤ 1 / M` for `M ≥ 1`. -/
theorem sum_Ioc_inv_sq_le {M N : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Ioc M N, 1 / (n : ℝ) ^ 2) ≤ 1 / (M : ℝ) := by
  by_cases hMN : M < N
  · have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    have hbij : (∑ n ∈ Ioc M N, 1 / (n : ℝ) ^ 2) =
        ∑ k ∈ range (N - M), 1 / ((M + 1 + k : ℕ) : ℝ) ^ 2 := by
      refine sum_bij (fun n _ => n - (M + 1)) ?_ ?_ ?_ ?_
      · intro n hn; simp only [mem_Ioc] at hn; simp only [mem_range]; omega
      · intro a ha b hb h; simp only [mem_Ioc] at ha hb; omega
      · intro k hk; simp only [mem_range] at hk
        exact ⟨M + 1 + k, mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro n hn; simp only [mem_Ioc] at hn
        rw [show M + 1 + (n - (M + 1)) = n by omega]
    rw [hbij]
    have hstep : ∀ k : ℕ,
        1 / ((M + 1 + k : ℕ) : ℝ) ^ 2 ≤
          1 / ((M + k : ℕ) : ℝ) - 1 / ((M + (k + 1) : ℕ) : ℝ) := by
      intro k
      have hk1 : (0 : ℝ) < (M + k : ℕ) := by exact_mod_cast (show 0 < M + k by omega)
      have hk2 : (0 : ℝ) < (M + (k + 1) : ℕ) := by exact_mod_cast (show 0 < M + (k + 1) by omega)
      have heq1 : ((M + 1 + k : ℕ) : ℝ) = (M : ℝ) + k + 1 := by push_cast; ring
      have heq2 : ((M + k : ℕ) : ℝ) = (M : ℝ) + k := by push_cast; ring
      have heq3 : ((M + (k + 1) : ℕ) : ℝ) = (M : ℝ) + k + 1 := by push_cast; ring
      rw [heq1, heq2, heq3]
      have hdiff : 1 / ((M : ℝ) + k) - 1 / ((M : ℝ) + k + 1) =
          1 / (((M : ℝ) + k) * ((M : ℝ) + k + 1)) := by
        field_simp [hk1.ne', hk2.ne']; ring
      rw [hdiff]
      refine one_div_le_one_div_of_le (mul_pos (by positivity) (by positivity)) ?_
      nlinarith
    have htel : ∀ K : ℕ,
        (∑ k ∈ range K, (1 / ((M + k : ℕ) : ℝ) - 1 / ((M + (k + 1) : ℕ) : ℝ))) =
          1 / (M : ℝ) - 1 / ((M + K : ℕ) : ℝ) := by
      intro K
      induction K with
      | zero => simp
      | succ K ih => rw [Finset.sum_range_succ, ih]; ring
    calc
      (∑ k ∈ range (N - M), 1 / ((M + 1 + k : ℕ) : ℝ) ^ 2)
          ≤ ∑ k ∈ range (N - M), (1 / ((M + k : ℕ) : ℝ) - 1 / ((M + (k + 1) : ℕ) : ℝ)) :=
            sum_le_sum fun k _ => hstep k
      _ = 1 / (M : ℝ) - 1 / ((M + (N - M) : ℕ) : ℝ) := htel (N - M)
      _ ≤ 1 / (M : ℝ) := sub_le_self _ (by positivity)
  · rw [Ioc_eq_empty hMN, sum_empty]
    positivity

theorem sum_Icc_inv_sq_from_le {d N : ℕ} (hd : 1 ≤ d) :
    (∑ k ∈ Icc d N, 1 / (k : ℝ) ^ 2) ≤ 2 / (d : ℝ) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := zero_lt_one.trans_le hd1
  by_cases hdN : d ≤ N
  · have hsplit : Icc d N = insert d (Ioc d N) := by
      ext k; simp only [mem_Icc, mem_insert, mem_Ioc]; omega
    have hmem : d ∉ Ioc d N := by simp only [mem_Ioc]; omega
    rw [hsplit, sum_insert hmem]
    have hfirst : 1 / (d : ℝ) ^ 2 ≤ 1 / (d : ℝ) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hd0) hd0]; nlinarith only [hd1]
    have htail : (∑ k ∈ Ioc d N, 1 / (k : ℝ) ^ 2) ≤ 1 / (d : ℝ) := sum_Ioc_inv_sq_le (N := N) hd
    exact (add_le_add hfirst htail).trans_eq (by ring)
  · rw [Icc_eq_empty hdN, sum_empty]; positivity

/-- Telescoping tail bound `∑_{n ∈ Ioc M N} 1 / n^3 ≤ 1 / M^2` for `M ≥ 1`. -/
theorem sum_Ioc_inv_cube_le {M N : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Ioc M N, 1 / (n : ℝ) ^ 3) ≤ 1 / (M : ℝ) ^ 2 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    (∑ n ∈ Ioc M N, 1 / (n : ℝ) ^ 3)
        ≤ ∑ n ∈ Ioc M N, (1 / (M : ℝ)) * (1 / (n : ℝ) ^ 2) := by
          refine sum_le_sum fun n hn => ?_
          have hnM : (M : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1.le
          rw [show 1 / (n : ℝ) ^ 3 = (1 / (n : ℝ)) * (1 / (n : ℝ) ^ 2) by ring]
          exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hM0 hnM) (by positivity)
    _ = (1 / (M : ℝ)) * ∑ n ∈ Ioc M N, 1 / (n : ℝ) ^ 2 := (mul_sum _ _ _).symm
    _ ≤ (1 / (M : ℝ)) * (1 / (M : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le hM) (by positivity)
    _ = 1 / (M : ℝ) ^ 2 := by ring

theorem sum_Icc_one_div_sqrt_le_two_sqrt_nat (N : ℕ) :
    (∑ n ∈ Icc 1 N, 1 / Real.sqrt (n : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ k ih =>
    have hsplit : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
      ext n; simp only [mem_Icc, mem_insert]; omega
    have hnot : k + 1 ∉ Icc 1 k := by simp only [mem_Icc]; omega
    rw [hsplit, sum_insert hnot]
    have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hstep : 1 / Real.sqrt ((k + 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 * Real.sqrt (k : ℝ) := by
      have hpos : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) + Real.sqrt (k : ℝ) := by positivity
      have hdiff : (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) *
          (Real.sqrt ((k + 1 : ℕ) : ℝ) + Real.sqrt (k : ℝ)) = 1 := by
        rw [mul_comm, ← sq_sub_sq, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
        push_cast; ring
      have hle : Real.sqrt ((k + 1 : ℕ) : ℝ) + Real.sqrt (k : ℝ) ≤
          2 * Real.sqrt ((k + 1 : ℕ) : ℝ) := by
        have := Real.sqrt_le_sqrt (show (k : ℝ) ≤ (k + 1 : ℕ) by exact_mod_cast Nat.le_succ k)
        linarith
      rw [div_le_iff₀ (Real.sqrt_pos.mpr hk1)]
      nlinarith
    linarith

private theorem abs_mode_le_sqrt_conductor {m : ℕ} (hm : 0 < m) (n : ℕ) :
    |normalizedRamanujanMode m n| ≤ Real.sqrt m := by
  have ht : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  rw [normalizedRamanujanMode,
    TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hm,
    abs_div, abs_of_pos (Real.sqrt_pos.mpr ht)]
  calc
    |ramanujanLagCoefficient m n| / Real.sqrt m.totient
        ≤ (m.totient : ℝ) / Real.sqrt m.totient :=
          div_le_div_of_nonneg_right
            (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m n)
            (Real.sqrt_nonneg _)
    _ = Real.sqrt m.totient := by
          rw [div_eq_iff (Real.sqrt_pos.mpr ht).ne', Real.mul_self_sqrt ht.le]
    _ ≤ Real.sqrt m := Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le m)

private theorem norm_normalizedRamanujanHorizonVector_le_two_sqrt {l N : ℕ}
    (hl : 0 < l) (hlog : 1 ≤ Real.log (N : ℝ)) :
    ‖normalizedRamanujanHorizonVector l N‖ ≤ 2 * Real.sqrt l := by
  have hL : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hraw : ‖ramanujanHorizonVector l N‖ ^ 2 ≤ (l : ℝ) * (1 + Real.log N) := by
    rw [ramanujanHorizonVector_norm_sq]
    calc
      _ ≤ ∑ n ∈ Icc 1 N, (l : ℝ) * (1 / (n : ℝ)) := by
        refine sum_le_sum fun n _ => ?_
        rw [ramanujanPoleProfile, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        have hs := pow_le_pow_left₀ (abs_nonneg _) (abs_mode_le_sqrt_conductor hl n) 2
        rw [sq_abs, Real.sq_sqrt (Nat.cast_nonneg l)] at hs
        simpa only [div_eq_mul_inv, one_mul] using
          div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)
      _ = (l : ℝ) * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log N) (Nat.cast_nonneg l)
  have hsq : ‖normalizedRamanujanHorizonVector l N‖ ^ 2 ≤ 4 * (l : ℝ) := by
    calc
      ‖normalizedRamanujanHorizonVector l N‖ ^ 2
          = ‖ramanujanHorizonVector l N‖ ^ 2 / Real.log N := by
            rw [normalizedRamanujanHorizonVector, norm_smul, mul_pow, Real.norm_eq_abs,
              sq_abs, inv_pow, Real.sq_sqrt hL.le]
            ring
      _ ≤ (l : ℝ) * (1 + Real.log N) / Real.log N := div_le_div_of_nonneg_right hraw hL.le
      _ ≤ 4 * (l : ℝ) := by
            rw [div_le_iff₀ hL]
            nlinarith
  have h2l : (0 : ℝ) ≤ 2 * Real.sqrt l := by positivity
  exact (Real.le_sqrt_of_sq_le hsq).trans_eq (by
    rw [show (4 : ℝ) * l = (2 * Real.sqrt l) ^ 2 by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg l)]; ring,
      Real.sqrt_sq h2l])

private theorem abs_inner_of_coord_div_sqrt_log {l N : ℕ} (hl : 0 < l)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) (row : ℕ → ℝ)
    (hcoord : ∀ n : PrimeHorizonIndex N, u n = row n.1 / Real.sqrt (Real.log N)) :
    |⟪u, normalizedRamanujanHorizonVector l N⟫| ≤
      (Real.sqrt l / Real.log N) * ∑ n ∈ Icc 1 N, |row n| / Real.sqrt n := by
  by_cases hL : Real.log (N : ℝ) ≤ 0
  · have hN1 : N ≤ 1 := by
      by_contra h; push Not at h
      have : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast h)
      linarith
    have hu0 : u = 0 := by
      ext i
      rcases Nat.eq_zero_or_pos N with rfl | hN0
      · exact absurd (mem_Icc.mp i.2).1 (by have := (mem_Icc.mp i.2).2; omega)
      · have hN_eq : N = 1 := by omega
        subst hN_eq
        have hi := hcoord i
        simp only [Nat.cast_one, Real.log_one, Real.sqrt_zero, div_zero] at hi
        exact hi
    rw [hu0, inner_zero_left, abs_zero]
    rcases Nat.eq_zero_or_pos N with rfl | hN0
    · simp
    · have hN_eq : N = 1 := by omega
      subst hN_eq; simp
  push Not at hL
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change |∑ i : PrimeHorizonIndex N, normalizedRamanujanHorizonVector l N i * u i| ≤ _
  have hrew : (∑ i : PrimeHorizonIndex N, normalizedRamanujanHorizonVector l N i * u i) =
      (1 / Real.log N) * ∑ n ∈ Icc 1 N,
        normalizedRamanujanMode l n * (row n / Real.sqrt n) := by
    rw [← sum_coe_sort (Icc 1 N), mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [hcoord i]
    change ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode l i.1 / Real.sqrt i.1)) *
      (row i.1 / Real.sqrt (Real.log N)) = _
    have hsL : Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.log (N : ℝ)) = Real.log N :=
      Real.mul_self_sqrt hL.le
    field_simp [(Real.sqrt_pos.mpr hL).ne',
      (Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp i.2).1 : (0 : ℝ) < i.1)).ne']
    rw [sq, hsL]; ring
  rw [hrew, abs_mul, abs_of_pos (one_div_pos.mpr hL)]
  calc
    (1 / Real.log (N : ℝ)) * |∑ n ∈ Icc 1 N, normalizedRamanujanMode l n * (row n / Real.sqrt n)|
        ≤ (1 / Real.log N) * ∑ n ∈ Icc 1 N, |normalizedRamanujanMode l n * (row n / Real.sqrt n)| :=
          mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (1 / Real.log N) * ∑ n ∈ Icc 1 N, Real.sqrt l * (|row n| / Real.sqrt n) := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun n _ => ?_) (by positivity)
          rw [abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact mul_le_mul_of_nonneg_right (abs_mode_le_sqrt_conductor hl n) (by positivity)
    _ = (Real.sqrt l / Real.log N) * ∑ n ∈ Icc 1 N, |row n| / Real.sqrt n := by
          rw [← mul_sum]; ring

/-- Exact bilinear adjointness between `upwardPrimeVector` and `downwardPrimeVector` on all
horizon vectors `x, y`. -/
theorem upwardPrimeVector_inner_eq_downward {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪upwardPrimeVector φ c N x, y⟫ = ⟪x, downwardPrimeVector φ c N y⟫ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  obtain ⟨_, hgsupp, _⟩ := atomDilate_facts hφ hsupp hw
  let g := atomDilate φ (c / N)
  let G0 := ∫ u, g u ^ 2
  let K := lagRange (Real.log N + c / N + 1)
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n : PrimeHorizonIndex N, y n * (upwardPrimeRow g N (primeHorizonExtension x) n / G0)) =
    ∑ j : PrimeHorizonIndex N, (downwardPrimeRow g N (primeHorizonExtension y) j / G0) * x j
  have hlhs :
      (∑ n : PrimeHorizonIndex N, y n * (upwardPrimeRow g N (primeHorizonExtension x) n / G0)) =
        (∑ n ∈ Icc 1 N,
          primeHorizonExtension y n * upwardPrimeRow g N (primeHorizonExtension x) n) / G0 := by
    rw [← sum_coe_sort (Icc 1 N), sum_div]
    refine sum_congr rfl fun n _ => ?_
    rw [primeHorizonExtension_coe, mul_div_assoc]
  have hrhs :
      (∑ j : PrimeHorizonIndex N, (downwardPrimeRow g N (primeHorizonExtension y) j / G0) * x j) =
        (∑ j ∈ Icc 1 N,
          primeHorizonExtension x j * downwardPrimeRow g N (primeHorizonExtension y) j) / G0 := by
    rw [← sum_coe_sort (Icc 1 N), sum_div]
    refine sum_congr rfl fun j _ => ?_
    rw [primeHorizonExtension_coe, div_mul_eq_mul_div, mul_comm]
  rw [hlhs, hrhs]
  congr 1
  have hup : ∀ n ∈ Icc 1 N,
      primeHorizonExtension y n * upwardPrimeRow g N (primeHorizonExtension x) n =
        ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
          ∑ j ∈ Icc 1 N, primeHorizonExtension y n * primeHorizonExtension x j *
            (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n))) := by
    intro n hn
    rw [upwardPrimeRow_eq_sum hgsupp hw.le hn (primeHorizonExtension x), mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, mul_comm (primeHorizonExtension y n), mul_assoc, mul_sum]
    congr 1
    exact sum_congr rfl fun j _ => by dsimp only [g]; ring
  have hdown : ∀ j ∈ Icc 1 N,
      primeHorizonExtension x j * downwardPrimeRow g N (primeHorizonExtension y) j =
        ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
          ∑ n ∈ Icc 1 N, primeHorizonExtension y n * primeHorizonExtension x j *
            (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n))) := by
    intro j hj
    rw [downwardPrimeRow_eq_sum hgsupp hw.le hj (primeHorizonExtension y), mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, mul_comm (primeHorizonExtension x j), mul_assoc, mul_sum]
    congr 1
    exact sum_congr rfl fun n _ => by dsimp only [g]; ring
  rw [sum_congr rfl hup, sum_congr rfl hdown, sum_comm,
    sum_comm (s := Icc 1 N) (t := range K)]
  refine sum_congr rfl fun k _ => ?_
  simp_rw [← mul_sum]
  congr 1
  exact sum_comm

/-! ## Section 2: Channels 1–5 Logarithm-Free Bilinear and Dual-Collar Bounds -/

/-- Channel 1 bilinear bound (`O(√(m l) (1 + log m) / log N)`), independent of `c`. -/
theorem exists_primeResidual_bilinear_log_free :
    ∃ C : ℝ, 0 < C ∧ ∀ m l N : ℕ, 0 < m → 0 < l →
      |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
          (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector l N⟫| ≤
        C * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N := by
  obtain ⟨c_M, hc_M, A_M, hA_M, hMertens⟩ :=
    GaloisForLFunctions.RHTower.exists_global_mertensDeviation_exp_sqrt_log_bound
  let C_env : ℝ := A_M * (2 + 48 / c_M ^ 4) + 4
  have hC_env : 0 < C_env := by dsimp only [C_env]; positivity
  let C_tot : ℝ := 8 * C_env * (1 + 2 * Real.pi ^ 2)
  refine ⟨C_tot, by dsimp only [C_tot]; positivity, ?_⟩
  intro m l N hm hl
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · have hu0 : Matrix.toEuclideanLin (fullPrimeMatrix 0) (normalizedRamanujanHorizonVector m 0) -
        (Real.log (0 : ℕ) - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m 0 = 0 := by
      ext ⟨n, hn⟩; simp at hn
    rw [hu0, inner_zero_left, abs_zero, Nat.cast_zero, Real.log_zero, div_zero]
  have hcoord : ∀ n : PrimeHorizonIndex N,
      (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N) n =
        SignedArithmeticHodgeTheory.ramanujanPrimeResidual m N n / Real.sqrt (Real.log N) := by
    intro n
    change (Matrix.toEuclideanLin (fullPrimeMatrix N)
        ((Real.sqrt (Real.log N))⁻¹ • ramanujanHorizonVector m N)) n -
      (Real.log N - ramanujanAdjunctionEnergy m) *
        ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m n) = _
    rw [map_smul]
    change (Real.sqrt (Real.log N))⁻¹ *
        (Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) n) -
      (Real.log N - ramanujanAdjunctionEnergy m) *
        ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m n) = _
    rw [fullPrimeMatrix_apply_ramanujanHorizonVector,
      SignedArithmeticHodgeTheory.ramanujanPrimeResidual]
    ring
  have hpair := abs_inner_of_coord_div_sqrt_log hl _
    (fun n => SignedArithmeticHodgeTheory.ramanujanPrimeResidual m N n) hcoord
  have henv : ∀ y : ℕ, 0 < y →
      SignedArithmeticHodgeTheory.primeMertensRemainderProfile y ≤
        C_env / (1 + Real.log y) ^ 2 := by
    intro y hy
    have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
    have hLy : 0 ≤ Real.log (y : ℝ) := Real.log_natCast_nonneg y
    have hden : 0 < (1 + Real.log (y : ℝ)) ^ 2 := by positivity
    have hexp_wt : Real.exp (-c_M * Real.sqrt (Real.log y)) * (1 + Real.log y) ^ 2 ≤
        2 + 48 / c_M ^ 4 := by
      have hx : 0 ≤ c_M * Real.sqrt (Real.log y) := mul_nonneg hc_M.le (Real.sqrt_nonneg _)
      have h4 := Real.pow_div_factorial_le_exp (c_M * Real.sqrt (Real.log y)) hx 4
      have hsq4 : (c_M * Real.sqrt (Real.log y)) ^ 4 = c_M ^ 4 * (Real.log y) ^ 2 := by
        have h2 : (Real.sqrt (Real.log y)) ^ 2 = Real.log y := Real.sq_sqrt hLy
        calc
          (c_M * Real.sqrt (Real.log y)) ^ 4 = c_M ^ 4 * ((Real.sqrt (Real.log y)) ^ 2) ^ 2 := by ring
          _ = c_M ^ 4 * (Real.log y) ^ 2 := by rw [h2]
      have hfac4 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
      rw [hsq4, hfac4] at h4
      have hexp1 : Real.exp (c_M * Real.sqrt (Real.log y)) *
          Real.exp (-c_M * Real.sqrt (Real.log y)) = 1 := by
        rw [← Real.exp_add]; simp only [neg_mul, add_neg_cancel, Real.exp_zero]
      have hmul := mul_le_mul_of_nonneg_right h4
        (Real.exp_pos (-c_M * Real.sqrt (Real.log y))).le
      rw [hexp1] at hmul
      have hL2 : (Real.log y) ^ 2 * Real.exp (-c_M * Real.sqrt (Real.log y)) ≤ 24 / c_M ^ 4 := by
        rw [le_div_iff₀ (pow_pos hc_M 4)]; nlinarith only [hmul]
      have he_le1 : Real.exp (-c_M * Real.sqrt (Real.log y)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith only [hx])
      have h2sq : (1 + Real.log y) ^ 2 ≤ 2 + 2 * (Real.log y) ^ 2 := by
        nlinarith only [sq_nonneg (1 - Real.log y)]
      have hprod := mul_le_mul_of_nonneg_left h2sq
        (Real.exp_pos (-c_M * Real.sqrt (Real.log y))).le
      calc
        Real.exp (-c_M * Real.sqrt (Real.log y)) * (1 + Real.log y) ^ 2
            ≤ Real.exp (-c_M * Real.sqrt (Real.log y)) * (2 + 2 * (Real.log y) ^ 2) := hprod
        _ = 2 * Real.exp (-c_M * Real.sqrt (Real.log y)) +
              2 * ((Real.log y) ^ 2 * Real.exp (-c_M * Real.sqrt (Real.log y))) := by ring
        _ ≤ 2 * 1 + 2 * (24 / c_M ^ 4) := add_le_add
              (mul_le_mul_of_nonneg_left he_le1 zero_le_two)
              (mul_le_mul_of_nonneg_left hL2 zero_le_two)
        _ = 2 + 48 / c_M ^ 4 := by ring
    have hinv_wt : 1 / (y : ℝ) * (1 + Real.log y) ^ 2 ≤ 4 := by
      have hsq := one_add_log_sq_le_four_mul (by exact_mod_cast hy : (1 : ℝ) ≤ y)
      calc
        1 / (y : ℝ) * (1 + Real.log y) ^ 2 ≤ 1 / (y : ℝ) * (4 * (y : ℝ)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = 4 := by field_simp [hy0.ne']
    have hM := hMertens y hy
    change |mertensSum y - Real.log y + Real.eulerMascheroniConstant| ≤
      A_M * Real.exp (-c_M * Real.sqrt (Real.log y)) at hM
    rw [le_div_iff₀ hden, SignedArithmeticHodgeTheory.primeMertensRemainderProfile, add_mul]
    have h1 := mul_le_mul_of_nonneg_right hM hden.le
    have h2 := mul_le_mul_of_nonneg_left hexp_wt hA_M
    dsimp only [C_env]
    nlinarith only [h1, h2, hinv_wt]
  have hker_cmp : ∀ n ∈ Icc 1 N,
      1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2 ≤
        2 * (1 + Real.log ((N / n : ℕ) : ℝ)) ^ 2 := by
    intro n hn
    have hn0 : 0 < n := (mem_Icc.mp hn).1
    have hnN : n ≤ N := (mem_Icc.mp hn).2
    have hy : 0 < N / n := Nat.div_pos hnN hn0
    have hyn : (1 : ℝ) ≤ ((N / n : ℕ) : ℝ) := by exact_mod_cast hy
    have hinv : 1 / ((N / n : ℕ) : ℝ) ≤ 1 := div_le_self zero_le_one hyn
    have hr := roundoff_le hn0 hnN
    have hlog : 0 ≤ Real.log ((N / n : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hquot : Real.log ((n : ℝ) / N) = Real.log n - Real.log N :=
      Real.log_div (by exact_mod_cast hn0.ne') (by exact_mod_cast hN0.ne')
    have hnonpos : Real.log ((n : ℝ) / N) ≤ 0 := by rw [hquot]; linarith only [hr.1, hlog]
    have habs : |Real.log ((n : ℝ) / N)| ≤ 1 + Real.log ((N / n : ℕ) : ℝ) := by
      rw [abs_of_nonpos hnonpos, hquot]; linarith only [hr.2, hinv]
    have hα0 : 0 ≤ 1 / (2 * Real.pi) := by positivity
    have hα1 : 1 / (2 * Real.pi) ≤ 1 := one_div_two_pi_mem_Ioo.2.le
    have hα : |1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)| ≤
        1 + Real.log ((N / n : ℕ) : ℝ) := by
      rw [abs_mul, abs_of_nonneg hα0]
      exact (mul_le_mul_of_nonneg_right hα1 (abs_nonneg _)).trans (by simpa using habs)
    have hsq := mul_le_mul hα hα (abs_nonneg _) (by positivity)
    rw [← sq, sq_abs, ← sq] at hsq
    nlinarith only [hsq, hlog]
  have hwiener : (∑ n ∈ Icc 1 N, 1 / (n : ℝ) *
      (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) ≤ 1 + 2 * Real.pi ^ 2 := by
    have hcheby : chebyWith 1 (fun _ : ℕ => (1 : ℂ)) := by intro n; simp [cumsum]
    have hN0R : (0 : ℝ) < N := by exact_mod_cast hN0
    have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN0
    have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) *
        (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) := by
      simpa only [norm_one, one_div] using limiting_fourier_lim1_aux ⟨1, hcheby⟩ hN0R 1 zero_le_one
    have hfull : (∑' n : ℕ, 1 / (n : ℝ) *
        (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) ≤ 1 + 2 * Real.pi ^ 2 := by
      simpa only [norm_one, one_mul] using bound_sum_log' hcheby hN1R
    exact (Summable.sum_le_tsum (Icc 1 N) (fun _ _ => by positivity) hsum).trans hfull
  have hcost : SignedArithmeticHodgeTheory.ramanujanResidualConductorCost m ≤
      4 * Real.sqrt m * (1 + Real.log m) := by
    rw [SignedArithmeticHodgeTheory.ramanujanResidualConductorCost]
    have htot : Real.sqrt (m.totient : ℝ) ≤ Real.sqrt m :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le m)
    have h14 : 1 + 4 * Real.log (m : ℝ) ≤ 4 * (1 + Real.log m) := by
      linarith [Real.log_natCast_nonneg m]
    exact (mul_le_mul htot h14 (by positivity) (Real.sqrt_nonneg m)).trans_eq (by ring)
  have hrow_sum : (∑ n ∈ Icc 1 N,
      |SignedArithmeticHodgeTheory.ramanujanPrimeResidual m N n| / Real.sqrt n) ≤
      8 * C_env * (1 + 2 * Real.pi ^ 2) * Real.sqrt m * (1 + Real.log m) := by
    have hpt : ∀ n ∈ Icc 1 N,
        |SignedArithmeticHodgeTheory.ramanujanPrimeResidual m N n| / Real.sqrt n ≤
          8 * C_env * Real.sqrt m * (1 + Real.log m) *
            (1 / (n : ℝ) * (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) := by
      intro n hn
      have hn0 : 0 < n := (mem_Icc.mp hn).1
      have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0
      have hy : 0 < N / n := Nat.div_pos (mem_Icc.mp hn).2 hn0
      have hb := SignedArithmeticHodgeTheory.abs_ramanujanPrimeResidual_le hm hn
      have hdiv : |SignedArithmeticHodgeTheory.ramanujanPrimeResidual m N n| / Real.sqrt n ≤
          SignedArithmeticHodgeTheory.ramanujanResidualConductorCost m *
            SignedArithmeticHodgeTheory.primeMertensRemainderProfile (N / n) / (n : ℝ) := by
        calc
          _ ≤ (SignedArithmeticHodgeTheory.ramanujanResidualConductorCost m *
                SignedArithmeticHodgeTheory.primeMertensRemainderProfile (N / n) / Real.sqrt n) /
                Real.sqrt n := div_le_div_of_nonneg_right hb (Real.sqrt_nonneg n)
          _ = SignedArithmeticHodgeTheory.ramanujanResidualConductorCost m *
                SignedArithmeticHodgeTheory.primeMertensRemainderProfile (N / n) /
                (Real.sqrt n * Real.sqrt n) := div_div _ _ _
          _ = _ := by rw [Real.mul_self_sqrt hn0R.le]
      have hkpos : 0 < 1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2 := by positivity
      have hlog_pos : 0 < (1 + Real.log ((N / n : ℕ) : ℝ)) ^ 2 := by
        have := Real.log_natCast_nonneg (N / n); positivity
      have hinv_cmp : 1 / (1 + Real.log ((N / n : ℕ) : ℝ)) ^ 2 ≤
          2 * (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ hlog_pos hkpos, one_mul]
        linarith only [hker_cmp n hn]
      have hprof_le : SignedArithmeticHodgeTheory.primeMertensRemainderProfile (N / n) ≤
          2 * C_env * (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹ := by
        calc
          _ ≤ C_env / (1 + Real.log ((N / n : ℕ) : ℝ)) ^ 2 := henv (N / n) hy
          _ = C_env * (1 / (1 + Real.log ((N / n : ℕ) : ℝ)) ^ 2) := div_eq_mul_one_div _ _
          _ ≤ C_env * (2 * (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left hinv_cmp hC_env.le
          _ = _ := by ring
      have hc0_cost : 0 ≤ SignedArithmeticHodgeTheory.ramanujanResidualConductorCost m := by
        rw [SignedArithmeticHodgeTheory.ramanujanResidualConductorCost]
        have := Real.log_natCast_nonneg m; positivity
      have hp0_prof : 0 ≤ SignedArithmeticHodgeTheory.primeMertensRemainderProfile (N / n) := by
        unfold SignedArithmeticHodgeTheory.primeMertensRemainderProfile; positivity
      have hp := mul_le_mul hcost hprof_le hp0_prof (by positivity)
      exact hdiv.trans ((div_le_div_of_nonneg_right hp hn0R.le).trans_eq (by ring))
    calc
      _ ≤ ∑ n ∈ Icc 1 N, 8 * C_env * Real.sqrt m * (1 + Real.log m) *
            (1 / (n : ℝ) * (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) :=
          sum_le_sum hpt
      _ = 8 * C_env * Real.sqrt m * (1 + Real.log m) *
            ∑ n ∈ Icc 1 N, 1 / (n : ℝ) *
              (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹ :=
          (mul_sum _ _ _).symm
      _ ≤ 8 * C_env * Real.sqrt m * (1 + Real.log m) * (1 + 2 * Real.pi ^ 2) :=
          mul_le_mul_of_nonneg_left hwiener (by have := Real.log_natCast_nonneg m; positivity)
      _ = _ := by ring
  by_cases hL0 : 0 < Real.log (N : ℝ)
  · refine (hpair.trans (mul_le_mul_of_nonneg_left hrow_sum (by positivity))).trans_eq ?_
    rw [Real.sqrt_mul (Nat.cast_nonneg m)]
    dsimp only [C_tot]; ring
  · have hN1 : N = 1 := by
      by_contra h
      have h2 : 2 ≤ N := by omega
      exact hL0 (Real.log_pos (by exact_mod_cast h2))
    subst hN1
    have hu0 : Matrix.toEuclideanLin (fullPrimeMatrix 1) (normalizedRamanujanHorizonVector m 1) -
        (Real.log (1 : ℝ) - ramanujanAdjunctionEnergy m) •
          normalizedRamanujanHorizonVector m 1 = 0 := by
      ext i; simpa [Real.log_one] using hcoord i
    rw [Nat.cast_one, hu0, inner_zero_left, abs_zero, Real.log_one, div_zero]

/-- Pointwise row envelope of `separatedCrossErrorMatrix` on `normalizedRamanujanHorizonVector m N`,
giving both the `L^2` and bilinear Channel 4 bounds with zero `log c` factors. -/
theorem exists_separatedCrossError_bounds {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ c : ℝ, 1 ≤ c →
      ∀ N : ℕ, 1 ≤ N → c ^ 2 ≤ (N : ℝ) →
        ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
          (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
          C * (m : ℝ) * c ^ 2 / Real.log N ∧
        ∀ l : ℕ, 0 < l →
          |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
              (normalizedRamanujanHorizonVector m N),
            normalizedRamanujanHorizonVector l N⟫| ≤
            C * Real.sqrt ((m : ℝ) * l) * c / Real.log N := by
  let K₀ := 152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)
  have hK₀0 : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  refine ⟨2080 * K₀ ^ 2 + 40 * K₀ + 1, by positivity, ?_⟩
  intro m hm c hc N hN hc2N
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let E_ker : ℕ → ℕ → ℝ := fun n j =>
    if 2 * (c / N) < |Real.log j - Real.log n| then
      atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0
  let row_x : ℕ → ℝ := fun n =>
    ∑ j ∈ Icc 1 N, E_ker n j * (normalizedRamanujanMode m j / Real.sqrt j)
  have hcoord : ∀ n : PrimeHorizonIndex N,
      (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N)) n =
        row_x n / Real.sqrt (Real.log N) := by
    intro n
    rw [normalizedRamanujanHorizonVector, map_smul]
    change (Real.sqrt (Real.log N))⁻¹ *
      ((Matrix.toEuclideanLin (horizonKernelMatrix E_ker N)
        (horizonProfileVector (ramanujanPoleProfile m) N)) n) = _
    rw [horizonKernelMatrix_apply_profile, div_eq_inv_mul]
    rfl
  have hrow_abs : ∀ n ∈ Icc 1 N,
      |row_x n| ≤
        32 * K₀ * Real.sqrt m * c * Real.sqrt n / N + 4 * K₀ * Real.sqrt m * c ^ 2 / N := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    let d : ℕ := max 1 ⌈c * (n : ℝ) / N⌉₊
    have hd1 : 1 ≤ d := le_max_left _ _
    have hcd : c * (n : ℝ) / N ≤ (d : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈c * (n : ℝ) / N⌉₊))
    have hinv_d : 1 / (d : ℝ) ≤ (N : ℝ) / (c * n) := by
      have hpos : 0 < c * (n : ℝ) / N := div_pos (mul_pos hc0 hn0) hN0
      exact (one_div_le_one_div_of_le hpos hcd).trans_eq (one_div_div _ _)
    let S_mod := (Icc 1 N).filter (fun j : ℕ => 2 * (c / N) < |Real.log (j : ℝ) - Real.log n| ∧
      (n ≤ 2 * j ∧ j ≤ 2 * n))
    have hterm_pt : ∀ j ∈ Icc 1 N,
        |E_ker n j * (normalizedRamanujanMode m j / Real.sqrt j)| ≤
          K₀ * (c / N) ^ 2 * Real.sqrt m *
            ((if j ∈ S_mod then 8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 else 0) + 4) := by
      intro j hj
      have hj1 := (mem_Icc.mp hj).1
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj0
      have hsj1 : 1 ≤ Real.sqrt (j : ℝ) := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by exact_mod_cast hj1 : (1 : ℝ) ≤ j)
      by_cases hgap : 2 * (c / N) < |Real.log j - Real.log n|
      · have hne : n ≠ j := by
          intro heq; subst heq; simp only [sub_self, abs_zero] at hgap
          linarith only [hgap, div_pos hc0 hN0]
        have hd_pos : 0 < |(n : ℝ) - j| :=
          abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
        have hd2 : 0 < |(n : ℝ) - j| ^ 2 := sq_pos_of_pos hd_pos
        have hm0 : 0 ≤ max (n : ℝ) j := hn0.le.trans (le_max_left _ _)
        have hentry := abs_separatedCrossError_le hφ hsupp hM hc0 hN hn hj
        change |E_ker n j| ≤ K₀ * (c / N) ^ 2 * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 at hentry
        have ha : |normalizedRamanujanMode m j / Real.sqrt j| ≤ Real.sqrt m / Real.sqrt j := by
          rw [abs_div, abs_of_pos hsj]
          exact div_le_div_of_nonneg_right (abs_mode_le_sqrt_conductor hm j) hsj.le
        have hprod := mul_le_mul hentry ha (abs_nonneg _) (by positivity)
        rw [← abs_mul] at hprod
        have hrew : K₀ * (c / N) ^ 2 * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 *
            (Real.sqrt m / Real.sqrt j) =
            K₀ * (c / N) ^ 2 * Real.sqrt m *
              ((max (n : ℝ) j) ^ 2 / (Real.sqrt j * |(n : ℝ) - j| ^ 2)) := by ring
        rw [hrew] at hprod
        refine hprod.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        by_cases hnear : n ≤ 2 * j ∧ j ≤ 2 * n
        · rw [if_pos (mem_filter.mpr ⟨hj, hgap, hnear⟩)]
          have hnjR : (n : ℝ) ≤ 2 * j := by exact_mod_cast hnear.1
          have hjnR : (j : ℝ) ≤ 2 * n := by exact_mod_cast hnear.2
          have hs_cmp : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (j : ℝ) := by
            by_contra h
            have hlt : 2 * Real.sqrt (j : ℝ) < Real.sqrt (n : ℝ) := lt_of_not_ge h
            have hp := mul_pos (sub_pos.mpr hlt) (by positivity :
              0 < Real.sqrt (n : ℝ) + 2 * Real.sqrt (j : ℝ))
            nlinarith only [hp, Real.sq_sqrt hn0.le, Real.sq_sqrt hj0.le, hnjR, hj0]
          have hm_le : max (n : ℝ) j ≤ 2 * n := max_le (by linarith only [hn0]) hjnR
          have hm2 : (max (n : ℝ) j) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
            have hsq := mul_self_le_mul_self hm0 hm_le
            nlinarith only [hsq]
          have hnum : (max (n : ℝ) j) ^ 2 ≤ 8 * (n : ℝ) * Real.sqrt n * Real.sqrt j := by
            calc
              _ ≤ 4 * (n : ℝ) ^ 2 := hm2
              _ = (4 * (n : ℝ) * Real.sqrt n) * Real.sqrt n := by
                rw [mul_assoc (4 * (n : ℝ)), ← pow_two, Real.sq_sqrt hn0.le]; ring
              _ ≤ (4 * (n : ℝ) * Real.sqrt n) * (2 * Real.sqrt j) :=
                mul_le_mul_of_nonneg_left hs_cmp (by positivity)
              _ = _ := by ring
          have ht : (max (n : ℝ) j) ^ 2 / (Real.sqrt j * |(n : ℝ) - j| ^ 2) ≤
              8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 := by
            rw [div_le_div_iff₀ (mul_pos hsj hd2) hd2]
            nlinarith only [mul_nonneg (sub_nonneg.mpr hnum) hd2.le]
          linarith only [ht]
        · rw [if_neg (fun h => hnear (mem_filter.mp h).2.2), zero_add]
          have hm_far : max (n : ℝ) j ≤ 2 * |(n : ℝ) - j| := by
            rcases not_and_or.mp hnear with h | h
            · have hnR' : 2 * (j : ℝ) < n := by exact_mod_cast (lt_of_not_ge h)
              rw [max_eq_left (by linarith only [hnR', hj0]),
                abs_of_pos (by linarith only [hnR', hj0])]
              linarith only [hnR']
            · have hjR' : 2 * (n : ℝ) < j := by exact_mod_cast (lt_of_not_ge h)
              rw [max_eq_right (by linarith only [hjR', hn0]),
                abs_of_neg (by linarith only [hjR', hn0])]
              linarith only [hjR']
          have hm2 : (max (n : ℝ) j) ^ 2 ≤ 4 * |(n : ℝ) - j| ^ 2 := by
            have hsq := mul_self_le_mul_self hm0 hm_far
            nlinarith only [hsq]
          rw [div_le_iff₀ (mul_pos hsj hd2)]
          nlinarith only [hm2, mul_nonneg (sub_nonneg.mpr hsj1) hd2.le]
      · have hz : E_ker n j = 0 := by dsimp only [E_ker]; rw [if_neg hgap]
        rw [hz, zero_mul, abs_zero]
        have hif0 : 0 ≤ (if j ∈ S_mod then 8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 else 0) + 4 := by
          split_ifs <;> positivity
        exact mul_nonneg (by positivity) hif0
    have hgap_mod : ∀ j ∈ S_mod, c * (n : ℝ) / N < |(n : ℝ) - j| := by
      intro j hjS
      obtain ⟨hj, hgap, hnj2, _⟩ := mem_filter.mp hjS
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
      have hnjR : (n : ℝ) ≤ 2 * j := by exact_mod_cast hnj2
      have hne : j ≠ n := by
        intro heq; subst heq; simp only [sub_self, abs_zero] at hgap
        linarith only [hgap, div_pos hc0 hN0]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hjlt : (j : ℝ) < n := by exact_mod_cast hlt
        have hlog_ub := Real.log_le_sub_one_of_pos (div_pos hn0 hj0)
        rw [Real.log_div hn0.ne' hj0.ne', show (n : ℝ) / j - 1 = ((n : ℝ) - j) / j by
          field_simp [hj0.ne']] at hlog_ub
        have hlog_eq : |Real.log j - Real.log n| = Real.log n - Real.log j := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hj0 hjlt.le))]
        have hfrac : ((n : ℝ) - j) / j ≤ 2 * ((n : ℝ) - j) / n := by
          rw [div_le_div_iff₀ hj0 hn0]
          nlinarith only [hnjR, sub_pos.mpr hjlt]
        have habs_eq : |(n : ℝ) - j| = (n : ℝ) - j := abs_of_pos (sub_pos.mpr hjlt)
        have hlt2 : 2 * c / N < 2 * |(n : ℝ) - j| / n := by
          rw [habs_eq, show 2 * c / (N : ℝ) = 2 * (c / N) by ring]
          linarith only [hgap, hlog_eq, hlog_ub, hfrac]
        have hmul := (div_lt_div_iff₀ hN0 hn0).mp hlt2
        exact (div_lt_iff₀ hN0).mpr (by linarith only [hmul])
      · have hngt : (n : ℝ) < j := by exact_mod_cast hgt
        have hlog_ub := Real.log_le_sub_one_of_pos (div_pos hj0 hn0)
        rw [Real.log_div hj0.ne' hn0.ne', show (j : ℝ) / n - 1 = ((j : ℝ) - n) / n by
          field_simp [hn0.ne']] at hlog_ub
        have hlog_eq : |Real.log j - Real.log n| = Real.log j - Real.log n :=
          abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hn0 hngt.le))
        have habs_eq : |(n : ℝ) - j| = (j : ℝ) - n := by
          rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hngt)]
        have hpos_diff : 0 < ((j : ℝ) - n) / n := div_pos (sub_pos.mpr hngt) hn0
        have h2diff : ((j : ℝ) - n) / n ≤ 2 * ((j : ℝ) - n) / n := by
          rw [mul_div_assoc]; linarith only [hpos_diff]
        have hlt2 : 2 * c / N < 2 * |(n : ℝ) - j| / n := by
          rw [habs_eq, show 2 * c / (N : ℝ) = 2 * (c / N) by ring]
          linarith only [hgap, hlog_eq, hlog_ub, h2diff]
        have hmul := (div_lt_div_iff₀ hN0 hn0).mp hlt2
        exact (div_lt_iff₀ hN0).mpr (by linarith only [hmul])
    have hsum_mod : (∑ j ∈ S_mod, 1 / |(n : ℝ) - j| ^ 2) ≤ 4 * (N : ℝ) / (c * n) := by
      let L_set := S_mod.filter (fun j => j < n)
      let R_set := S_mod.filter (fun j => n < j)
      have hsplit_LR : (∑ j ∈ S_mod, 1 / |(n : ℝ) - j| ^ 2) =
          (∑ j ∈ L_set, 1 / |(n : ℝ) - j| ^ 2) + ∑ j ∈ R_set, 1 / |(n : ℝ) - j| ^ 2 := by
        simp only [L_set, R_set, sum_filter, ← sum_add_distrib]
        refine sum_congr rfl fun j _ => ?_
        rcases lt_trichotomy j n with h | rfl | h
        · rw [if_pos h, if_neg (not_lt_of_ge h.le), add_zero]
        · simp
        · rw [if_neg (not_lt_of_ge h.le), if_pos h, zero_add]
      have hL_bound : (∑ j ∈ L_set, 1 / |(n : ℝ) - j| ^ 2) ≤ 2 / (d : ℝ) := by
        have hinj : ∀ i ∈ L_set, ∀ j ∈ L_set, n - i = n - j → i = j := by
          intro i hi j hj hij
          have := (mem_filter.mp hi).2; have := (mem_filter.mp hj).2
          change n - i = n - j at hij; omega
        have hmap : (∑ j ∈ L_set, 1 / |(n : ℝ) - j| ^ 2) =
            ∑ k ∈ L_set.image (fun j => n - j), 1 / (k : ℝ) ^ 2 := by
          rw [sum_image hinj]
          refine sum_congr rfl fun j hj => ?_
          have hlt := (mem_filter.mp hj).2
          rw [Nat.cast_sub hlt.le, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le))]
        have hsub_d : L_set.image (fun j => n - j) ⊆ Icc d N := by
          intro k hk
          obtain ⟨j, hjL, rfl⟩ := mem_image.mp hk
          obtain ⟨hjS, hlt⟩ := mem_filter.mp hjL
          have hgj := hgap_mod j hjS
          rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
            ← Nat.cast_sub hlt.le] at hgj
          exact mem_Icc.mpr ⟨max_le (by omega) (Nat.ceil_le.mpr hgj.le), (Nat.sub_le n j).trans hnN⟩
        rw [hmap]
        exact (sum_le_sum_of_subset_of_nonneg hsub_d (fun _ _ _ => by positivity)).trans
          (sum_Icc_inv_sq_from_le hd1)
      have hR_bound : (∑ j ∈ R_set, 1 / |(n : ℝ) - j| ^ 2) ≤ 2 / (d : ℝ) := by
        have hinj : ∀ i ∈ R_set, ∀ j ∈ R_set, i - n = j - n → i = j := by
          intro i hi j hj hij
          have := (mem_filter.mp hi).2; have := (mem_filter.mp hj).2
          change i - n = j - n at hij; omega
        have hmap : (∑ j ∈ R_set, 1 / |(n : ℝ) - j| ^ 2) =
            ∑ k ∈ R_set.image (fun j => j - n), 1 / (k : ℝ) ^ 2 := by
          rw [sum_image hinj]
          refine sum_congr rfl fun j hj => ?_
          have hlt := (mem_filter.mp hj).2
          rw [abs_sub_comm, Nat.cast_sub hlt.le,
            abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le))]
        have hsub_d : R_set.image (fun j => j - n) ⊆ Icc d N := by
          intro k hk
          obtain ⟨j, hjR, rfl⟩ := mem_image.mp hk
          obtain ⟨hjS, hlt⟩ := mem_filter.mp hjR
          have hjN_le := (mem_Icc.mp (mem_filter.mp hjS).1).2
          have hgj := hgap_mod j hjS
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
            ← Nat.cast_sub hlt.le] at hgj
          exact mem_Icc.mpr ⟨max_le (by omega) (Nat.ceil_le.mpr hgj.le), (Nat.sub_le j n).trans hjN_le⟩
        rw [hmap]
        exact (sum_le_sum_of_subset_of_nonneg hsub_d (fun _ _ _ => by positivity)).trans
          (sum_Icc_inv_sq_from_le hd1)
      rw [hsplit_LR]
      calc
        _ ≤ 2 / (d : ℝ) + 2 / (d : ℝ) := add_le_add hL_bound hR_bound
        _ = 4 * (1 / (d : ℝ)) := by ring
        _ ≤ 4 * ((N : ℝ) / (c * n)) := mul_le_mul_of_nonneg_left hinv_d (by norm_num)
        _ = 4 * (N : ℝ) / (c * n) := by ring
    calc
      |row_x n| ≤ ∑ j ∈ Icc 1 N, |E_ker n j * (normalizedRamanujanMode m j / Real.sqrt j)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Icc 1 N, K₀ * (c / N) ^ 2 * Real.sqrt m *
            ((if j ∈ S_mod then 8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 else 0) + 4) :=
          sum_le_sum hterm_pt
      _ = K₀ * (c / N) ^ 2 * Real.sqrt m *
            (8 * (n : ℝ) * Real.sqrt n * (∑ j ∈ S_mod, 1 / |(n : ℝ) - j| ^ 2) + 4 * N) := by
          rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel,
            ← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr (filter_subset _ _)]
          congr 2
          · rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
          · ring
      _ ≤ K₀ * (c / N) ^ 2 * Real.sqrt m *
            (8 * (n : ℝ) * Real.sqrt n * (4 * (N : ℝ) / (c * n)) + 4 * N) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) (by positivity)
          exact mul_le_mul_of_nonneg_left hsum_mod (by positivity)
      _ = 32 * K₀ * Real.sqrt m * c * Real.sqrt n / N + 4 * K₀ * Real.sqrt m * c ^ 2 / N := by
          field_simp [hN0.ne', hc0.ne', hn0.ne']; ring
  constructor
  · -- L^2 bound
    by_cases hL0 : 0 < Real.log (N : ℝ)
    · rw [EuclideanSpace.norm_sq_eq]
      have hsq_sum : (∑ i : PrimeHorizonIndex N, ‖(Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
          (normalizedRamanujanHorizonVector m N)) i‖ ^ 2) ≤
          (1 / Real.log N) * ∑ n ∈ Icc 1 N,
            (2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 * (n : ℝ) / (N : ℝ) ^ 2 +
              32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / (N : ℝ) ^ 2) := by
        change (∑ i : Icc 1 N, _) ≤ _
        rw [← sum_coe_sort (Icc 1 N), mul_sum]
        refine sum_le_sum fun idx _ => ?_
        let n : ℕ := idx.1
        have hn : n ∈ Icc 1 N := idx.2
        have h1 := hrow_abs n hn
        have hsq := pow_le_pow_left₀ (abs_nonneg _) h1 2
        have h2ab : (32 * K₀ * Real.sqrt m * c * Real.sqrt n / N +
            4 * K₀ * Real.sqrt m * c ^ 2 / N) ^ 2 ≤
            2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 * (n : ℝ) / (N : ℝ) ^ 2 +
              32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / (N : ℝ) ^ 2 := by
          set A := 32 * K₀ * Real.sqrt m * c * Real.sqrt n / N
          set B := 4 * K₀ * Real.sqrt m * c ^ 2 / N
          have h2 : (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by nlinarith [sq_nonneg (A - B)]
          have hA2 : A ^ 2 = 1024 * K₀ ^ 2 * (m : ℝ) * c ^ 2 * (n : ℝ) / (N : ℝ) ^ 2 := by
            dsimp only [A]
            rw [div_pow, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m),
              Real.sq_sqrt (Nat.cast_nonneg n)]
            ring
          have hB2 : B ^ 2 = 16 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / (N : ℝ) ^ 2 := by
            dsimp only [B]
            rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
            ring
          exact h2.trans_eq (by rw [hA2, hB2]; ring)
        change ‖(Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
          (normalizedRamanujanHorizonVector m N)) idx‖ ^ 2 ≤ _
        rw [Real.norm_eq_abs, sq_abs, hcoord idx, div_pow, Real.sq_sqrt hL0.le, ← sq_abs]
        calc
          |row_x n| ^ 2 / Real.log N
              ≤ (2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 * (n : ℝ) / (N : ℝ) ^ 2 +
                  32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / (N : ℝ) ^ 2) / Real.log N :=
                div_le_div_of_nonneg_right (hsq.trans h2ab) hL0.le
          _ = _ := by ring
      have hsum_n : (∑ n ∈ Icc 1 N, (n : ℝ)) ≤ (N : ℝ) ^ 2 := by
        calc
          (∑ n ∈ Icc 1 N, (n : ℝ)) ≤ ∑ _n ∈ Icc 1 N, (N : ℝ) :=
            sum_le_sum fun n hn => by exact_mod_cast (mem_Icc.mp hn).2
          _ = (N : ℝ) ^ 2 := by rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]; ring
      have hsum_tot : (∑ n ∈ Icc 1 N,
          (2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 * (n : ℝ) / (N : ℝ) ^ 2 +
            32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / (N : ℝ) ^ 2)) ≤
          2080 * K₀ ^ 2 * (m : ℝ) * c ^ 2 := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
        have h1 : (∑ n ∈ Icc 1 N, 2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 * (n : ℝ) / (N : ℝ) ^ 2) =
            (2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 / (N : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, (n : ℝ) := by
          rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
        rw [h1]
        have h2 : (2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 / (N : ℝ) ^ 2) * (∑ n ∈ Icc 1 N, (n : ℝ)) ≤
            2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 := by
          calc
            _ ≤ (2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 / (N : ℝ) ^ 2) * (N : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_left hsum_n (by positivity)
            _ = 2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 := div_mul_cancel₀ _ (pow_pos hN0 2).ne'
        have h3 : (N : ℝ) * (32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / (N : ℝ) ^ 2) ≤
            32 * K₀ ^ 2 * (m : ℝ) * c ^ 2 := by
          have hc4 : c ^ 4 ≤ c ^ 2 * (N : ℝ) := by
            have h := mul_le_mul_of_nonneg_left hc2N (sq_nonneg c)
            rwa [show c ^ 2 * c ^ 2 = c ^ 4 by ring] at h
          rw [mul_div_assoc', div_le_iff₀ (pow_pos hN0 2)]
          calc
            (N : ℝ) * (32 * K₀ ^ 2 * (m : ℝ) * c ^ 4)
                = (32 * K₀ ^ 2 * (m : ℝ) * (N : ℝ)) * c ^ 4 := by ring
            _ ≤ (32 * K₀ ^ 2 * (m : ℝ) * (N : ℝ)) * (c ^ 2 * (N : ℝ)) :=
              mul_le_mul_of_nonneg_left hc4 (by positivity)
            _ = 32 * K₀ ^ 2 * (m : ℝ) * c ^ 2 * (N : ℝ) ^ 2 := by ring
        exact (add_le_add h2 h3).trans_eq (by ring)
      calc
        _ ≤ (1 / Real.log N) * (2080 * K₀ ^ 2 * (m : ℝ) * c ^ 2) :=
          hsq_sum.trans (mul_le_mul_of_nonneg_left hsum_tot (by positivity))
        _ ≤ (2080 * K₀ ^ 2 + 40 * K₀ + 1) * (m : ℝ) * c ^ 2 / Real.log N := by
          rw [one_div_mul_eq_div]
          refine div_le_div_of_nonneg_right ?_ hL0.le
          have hex : (0 : ℝ) ≤ (40 * K₀ + 1) * (m : ℝ) * c ^ 2 := by positivity
          linarith only [hex, (by ring : (2080 * K₀ ^ 2 + 40 * K₀ + 1) * (m : ℝ) * c ^ 2 =
            2080 * K₀ ^ 2 * (m : ℝ) * c ^ 2 + (40 * K₀ + 1) * (m : ℝ) * c ^ 2)]
    · have hN1 : N = 1 := by
        by_contra h; exact hL0 (Real.log_pos (by exact_mod_cast (show 2 ≤ N by omega)))
      subst hN1
      have hu0 : Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c 1)
          (normalizedRamanujanHorizonVector m 1) = 0 := by
        ext i; simpa [Real.log_one] using hcoord i
      rw [Nat.cast_one, hu0, norm_zero, zero_pow (by decide), Real.log_one, div_zero]
  · -- Bilinear bound
    intro l hl
    by_cases hL0 : 0 < Real.log (N : ℝ)
    · have hp := abs_inner_of_coord_div_sqrt_log hl _ row_x hcoord
      have hsum_l1 : (∑ n ∈ Icc 1 N, |row_x n| / Real.sqrt n) ≤
          40 * K₀ * Real.sqrt m * c := by
        have hpt : ∀ n ∈ Icc 1 N, |row_x n| / Real.sqrt n ≤
            32 * K₀ * Real.sqrt m * c / N +
              (4 * K₀ * Real.sqrt m * c ^ 2 / N) * (1 / Real.sqrt n) := by
          intro n hn
          have hsn : 0 < Real.sqrt (n : ℝ) :=
            Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hn).1)
          calc
            |row_x n| / Real.sqrt n
                ≤ (32 * K₀ * Real.sqrt m * c * Real.sqrt n / N +
                    4 * K₀ * Real.sqrt m * c ^ 2 / N) / Real.sqrt n :=
                  div_le_div_of_nonneg_right (hrow_abs n hn) hsn.le
            _ = _ := by field_simp [hsn.ne', hN0.ne']
        calc
          _ ≤ ∑ n ∈ Icc 1 N, (32 * K₀ * Real.sqrt m * c / N +
                (4 * K₀ * Real.sqrt m * c ^ 2 / N) * (1 / Real.sqrt n)) := sum_le_sum hpt
          _ = 32 * K₀ * Real.sqrt m * c +
                (4 * K₀ * Real.sqrt m * c ^ 2 / N) * ∑ n ∈ Icc 1 N, 1 / Real.sqrt (n : ℝ) := by
              rw [sum_add_distrib, sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel,
                ← mul_sum]
              congr 1; field_simp [hN0.ne']
          _ ≤ 32 * K₀ * Real.sqrt m * c +
                (4 * K₀ * Real.sqrt m * c ^ 2 / N) * (2 * Real.sqrt N) :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left
                (sum_Icc_one_div_sqrt_le_two_sqrt_nat N) (by positivity))
          _ ≤ 40 * K₀ * Real.sqrt m * c := by
              have hc_sqrt : c ≤ Real.sqrt N := Real.le_sqrt_of_sq_le hc2N
              have hsqN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = N := Real.mul_self_sqrt hN0.le
              have hterm2 : (4 * K₀ * Real.sqrt m * c ^ 2 / N) * (2 * Real.sqrt N) ≤
                  8 * K₀ * Real.sqrt m * c := by
                rw [div_mul_eq_mul_div, div_le_iff₀ hN0]
                have h1 : c * Real.sqrt N ≤ N := by
                  calc c * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N :=
                        mul_le_mul_of_nonneg_right hc_sqrt (Real.sqrt_nonneg _)
                    _ = N := hsqN
                have hm0' : 0 ≤ 8 * K₀ * Real.sqrt m * c := by positivity
                calc
                  4 * K₀ * Real.sqrt m * c ^ 2 * (2 * Real.sqrt N)
                      = (8 * K₀ * Real.sqrt m * c) * (c * Real.sqrt N) := by ring
                  _ ≤ (8 * K₀ * Real.sqrt m * c) * N := mul_le_mul_of_nonneg_left h1 hm0'
              linarith only [hterm2]
      calc
        _ ≤ (Real.sqrt l / Real.log N) * (40 * K₀ * Real.sqrt m * c) :=
          hp.trans (mul_le_mul_of_nonneg_left hsum_l1 (by positivity))
        _ = 40 * K₀ * Real.sqrt ((m : ℝ) * l) * c / Real.log N := by
          rw [Real.sqrt_mul (Nat.cast_nonneg m)]; ring
        _ ≤ (2080 * K₀ ^ 2 + 40 * K₀ + 1) * Real.sqrt ((m : ℝ) * l) * c / Real.log N := by
          refine div_le_div_of_nonneg_right ?_ hL0.le
          have hex : (0 : ℝ) ≤ (2080 * K₀ ^ 2 + 1) * Real.sqrt ((m : ℝ) * l) * c := by positivity
          linarith only [hex, (by ring :
            (2080 * K₀ ^ 2 + 40 * K₀ + 1) * Real.sqrt ((m : ℝ) * l) * c =
              40 * K₀ * Real.sqrt ((m : ℝ) * l) * c +
                (2080 * K₀ ^ 2 + 1) * Real.sqrt ((m : ℝ) * l) * c)]
    · have hN1 : N = 1 := by
        by_contra h; exact hL0 (Real.log_pos (by exact_mod_cast (show 2 ≤ N by omega)))
      subst hN1
      have hu0 : Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c 1)
          (normalizedRamanujanHorizonVector m 1) = 0 := by
        ext i; simpa [Real.log_one] using hcoord i
      rw [Nat.cast_one, hu0, inner_zero_left, abs_zero, Real.log_one, div_zero]

/-! ## Section 3: Channel 8 Dual-Collar Bound and Adjoint Downward-Divisor Bilinear Bound -/

/-- On the top collar `Ioc M N`, the dual seventh-power weight `(n / N)^7` turns the deterministic
`O(m c / √n)` upward shell error into `O(m c^2 / log N)` with zero `log c` and zero Siegel–Walfisz
input. -/
theorem exists_upward_dual_seventh_log_free {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N M m : ℕ} {c : ℝ},
      1 ≤ N → 1 ≤ Real.log (N : ℝ) → 1 ≤ m → 1 ≤ c →
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      2 * linearPrimeStrip c ≤ M →
        topCollarDualSeventhMass M N
          (upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
            shellCorrection φ c m • normalizedRamanujanHorizonVector m N) ≤
          C * (m : ℝ) * (c ^ 2 / Real.log N + c ^ 10 * (Real.log N / N) ^ 2) := by
  obtain ⟨Ca, hCa, ha⟩ := exists_logarithmicUpward_uniform_conductor_harmonic_bound hφ hsupp hM_int
  let d : ℝ := Real.exp 1 + 2
  let C_tot : ℝ := 8 * (Ca * d ^ 6 + 16 * d ^ 2 + 16 * (Real.log 4 + 4) ^ 2 + 1)
  refine ⟨C_tot, by dsimp only [C_tot, d]; positivity, ?_⟩
  intro N M m c hN hlog hm hc hlarge h2BM
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have htot_le : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  let B := linearPrimeStrip c
  have hBc : (B : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc
  have hB1 : (B : ℝ) + 1 ≤ d * c := by dsimp only [d]; nlinarith only [hBc, hc]
  have hBd : (B : ℝ) ≤ d * c := by linarith only [hB1]
  have hc2 : c ≤ c ^ 2 := by nlinarith only [hc]
  have hexp := Real.exp_pos 1
  have hwidth : c / N ≤ 1 := by
    apply (div_le_one hN0).mpr
    have hcoef : 1 ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [hlarge, hc2, h]
  have hcN : c ≤ (N : ℝ) := (div_le_one hN0).mp hwidth
  have h2BN : 2 * B ≤ N := by
    have hcoef : 2 * (Real.exp 1 + 1) ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h1 := mul_le_mul_of_nonneg_left hc2 (show 0 ≤ 2 * (Real.exp 1 + 1) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    have h : 2 * (B : ℝ) ≤ N := by nlinarith only [hBc, h1, h2, hlarge]
    exact_mod_cast h
  have hBN : B ≤ N := by omega
  have hkernel : 2 * ((Real.exp 1 + 3) * c) * B ≤ (N : ℝ) := by
    have hcoef : 2 * (Real.exp 1 + 3) * (Real.exp 1 + 1) ≤
        4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h1 := mul_le_mul_of_nonneg_left hBc
      (show 0 ≤ 2 * ((Real.exp 1 + 3) * c) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [h1, h2, hlarge]
  have hB : ⌈c⌉₊ ≤ B := by
    apply Nat.ceil_le.mpr
    have h := mul_le_mul_of_nonneg_left
      (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)) hc0.le
    have hce : c ≤ c * Real.exp 1 := by simpa only [mul_one] using h
    exact hce.trans (Nat.le_ceil _)
  have hres_eq : upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N =
      (Real.sqrt (m.totient : ℝ))⁻¹ • normalizedUpwardPrimeResidual φ c N m :=
    upwardPrimeVector_ramanujan_residual_eq φ c N hm
  rw [hres_eq, topCollarDualSeventhMass_smul, inv_pow, Real.sq_sqrt htot_pos.le]
  let a : ℕ → ℝ := fun n =>
    (logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) / Real.sqrt n
  let b : ℕ → ℝ := fun n =>
    (linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n
  let r : ℕ → ℝ := fun n =>
    (reciprocalUpwardCoefficient φ c B N m n -
      ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n
  let u_a : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    WithLp.toLp 2 (fun n => a n / Real.sqrt (Real.log N))
  let u_b : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    WithLp.toLp 2 (fun n => b n / Real.sqrt (Real.log N))
  let u_r : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    WithLp.toLp 2 (fun n => r n / Real.sqrt (Real.log N))
  have hsplit3 : normalizedUpwardPrimeResidual φ c N m = (u_a + u_b) + u_r := by
    ext n
    have hn : (n : ℕ) ∈ Icc 1 N := n.2
    have hsqrt : Real.sqrt (n : ℕ) ≠ 0 := (Real.sqrt_pos.mpr
      (by exact_mod_cast (mem_Icc.mp hn).1 : (0 : ℝ) < (n : ℕ))).ne'
    have hu : upwardPrimeRow (atomDilate φ (c / N)) N
        (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
          (∫ u, atomDilate φ (c / N) u ^ 2) =
        logarithmicUpwardCoefficient φ c B N m n / Real.sqrt (n : ℕ) := by
      apply (eq_div_iff hsqrt).mpr
      simpa only [mul_comm] using sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient_small_width
        hsupp hc0 hn hwidth m
    change actualUpwardRowError φ c N m n / Real.sqrt (Real.log N) =
      (a n / Real.sqrt (Real.log N) + b n / Real.sqrt (Real.log N)) + r n / Real.sqrt (Real.log N)
    rw [actualUpwardRowError, hu]
    dsimp only [a, b, r]
    ring
  -- 1. `u_a` via `topCollarDualSeventhMass_le_norm_sq`
  have hua : topCollarDualSeventhMass M N u_a ≤
      Ca * d ^ 6 * (m.totient : ℝ) ^ 2 * c ^ 10 * (Real.log N / N) ^ 2 := by
    have h1 := topCollarDualSeventhMass_le_norm_sq M N u_a
    have hp := pow_le_pow_left₀ (show 0 ≤ (B : ℝ) + 1 by positivity) hB1 6
    have hb := (ha m N hN hlog c hc hwidth B hBN hkernel).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (show 0 ≤ Ca * (m.totient : ℝ) ^ 2 * c ^ 4 by positivity))
        (sq_nonneg (Real.log (N : ℝ) / N)))
    have hua_sq_eq : ‖u_a‖ ^ 2 = (∑ n ∈ Icc 1 N, a n ^ 2) / Real.log N := by
      rw [EuclideanSpace.norm_sq_eq]
      change (∑ n : PrimeHorizonIndex N, ‖a n / Real.sqrt (Real.log N)‖ ^ 2) = _
      simp only [Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hL0.le]
      rw [← sum_div, ← sum_coe_sort (Icc 1 N)]
    exact h1.trans (hua_sq_eq.le.trans (hb.trans_eq (by ring)))
  -- 2. `u_b` directly on `Ioc M N`: since `n > M ≥ 2 * B`, at most one `k` lies in `[N - B, N + B] / n`.
  have hub : topCollarDualSeventhMass M N u_b ≤
      16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / Real.log N := by
    let S_ex : ℕ → Finset ℕ := fun n =>
      (Icc 1 (N + B)).filter (fun k => N ≤ k * n + B ∧ k * n ≤ N + B)
    have hrow_ex : ∀ n ∈ Ioc M N,
        |linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n| ≤
          4 * (B : ℝ) * m.totient * ∑ k ∈ S_ex n, (ArithmeticFunction.vonMangoldt k : ℝ) / k := by
      intro n hn
      have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
      let L_val := 4 * (B : ℝ) * (∫ u, φ u ^ 2) * m.totient
      have hpoint : ∀ k ∈ Icc 1 (N + B),
          |∑ h ∈ Icc 1 B, (linearizedUpwardOffset φ c N m n k h -
              reciprocalUpwardOffset φ c N m n k h)| ≤
            if N ≤ k * n + B ∧ k * n ≤ N + B then L_val else 0 := by
        intro k hk
        have hk1 := (mem_Icc.mp hk).1
        have hT : 1 ≤ k * n := Nat.mul_pos hk1 hn1
        by_cases hex : N ≤ k * n + B ∧ k * n ≤ N + B
        · rw [if_pos hex]
          have h := (abs_sum_le_sum_abs _ (Icc 1 B)).trans
            (sum_le_sum fun h _ => abs_linearizedUpwardOffset_sub_reciprocal_le hφ hsupp c N m n k h)
          rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel] at h
          exact h.trans_eq (by dsimp only [L_val]; ring)
        · rw [if_neg hex]
          have hz : (∑ h ∈ Icc 1 B, (linearizedUpwardOffset φ c N m n k h -
              reciprocalUpwardOffset φ c N m n k h)) = 0 := by
            refine sum_eq_zero fun h hh => ?_
            have hhB := (mem_Icc.mp hh).2
            by_cases hhT : h < k * n
            · have hfar : k * n + B < N ∨ N + B < k * n := by omega
              rcases hfar with hfar | hfar
              · have hp : k * n + h ≤ N := by omega
                have hncut : h < k * n ∧ k * n - h ≤ N := ⟨hhT, by omega⟩
                have hkcut : k * n ≤ N := by omega
                simp only [linearizedUpwardOffset, reciprocalUpwardOffset, if_pos hp, if_pos hncut,
                  if_pos hkcut, ramanujanLagCoefficient_sub_eq_reflected hm hhT.le, sub_self]
              · have hp : ¬ k * n + h ≤ N := by omega
                have hncut : ¬ (h < k * n ∧ k * n - h ≤ N) := by omega
                have hkcut : ¬ k * n ≤ N := by omega
                simp only [linearizedUpwardOffset, reciprocalUpwardOffset, if_neg hp, if_neg hncut,
                  if_neg hkcut, add_zero, sub_self]
            · have hT0 : (0 : ℝ) < (k * n : ℕ) := by exact_mod_cast hT
              have hNc : (1 : ℝ) ≤ (N : ℝ) / c := (one_le_div hc0).mpr hcN
              have hhT' : (1 : ℝ) ≤ (h : ℝ) / (k * n : ℕ) :=
                (one_le_div hT0).mpr (by exact_mod_cast (show k * n ≤ h by omega))
              have hzero := shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
                ((one_le_mul_of_one_le_of_one_le hNc hhT').trans (le_abs_self _))
              simp only [linearizedUpwardOffset, reciprocalUpwardOffset, hzero, mul_zero, sub_self]
          rw [hz, abs_zero]
      unfold linearizedUpwardCoefficient reciprocalUpwardCoefficient
      rw [← mul_sub, ← sum_sub_distrib, abs_mul, abs_of_pos (one_div_pos.mpr hM_int)]
      calc
        1 / (∫ u, φ u ^ 2) * |∑ k ∈ Icc 1 (N + B),
            ((ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, linearizedUpwardOffset φ c N m n k h -
              (ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, reciprocalUpwardOffset φ c N m n k h)| ≤
          1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B),
            |(ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, linearizedUpwardOffset φ c N m n k h -
              (ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, reciprocalUpwardOffset φ c N m n k h| :=
          mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
        _ ≤ 1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B),
            if N ≤ k * n + B ∧ k * n ≤ N + B then
              (ArithmeticFunction.vonMangoldt k : ℝ) / k * L_val else 0 := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun k hk => ?_) (by positivity)
          rw [← mul_sub, ← sum_sub_distrib, abs_mul,
            abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))]
          have hpk := hpoint k hk
          split_ifs at hpk ⊢
          · exact mul_le_mul_of_nonneg_left hpk
              (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
          · simpa only [mul_zero] using mul_le_mul_of_nonneg_left hpk
              (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
        _ = 4 * (B : ℝ) * m.totient * ∑ k ∈ S_ex n, (ArithmeticFunction.vonMangoldt k : ℝ) / k := by
          dsimp only [S_ex, L_val]
          rw [← sum_filter, ← sum_mul]
          field_simp [hM_int.ne']
    have hcard_one : ∀ n ∈ Ioc M N, (S_ex n).card ≤ 1 := by
      intro n hn
      have hn2B : 2 * B < n := lt_of_le_of_lt h2BM (mem_Ioc.mp hn).1
      refine Finset.card_le_one.mpr fun k₁ hk₁ k₂ hk₂ => ?_
      obtain ⟨_, h1lo, h1hi⟩ := mem_filter.mp hk₁
      obtain ⟨_, h2lo, h2hi⟩ := mem_filter.mp hk₂
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hstep : (k₁ + 1) * n ≤ k₂ * n := Nat.mul_le_mul_right n hlt
        nlinarith [hstep, hn2B, h1lo, h2hi]
      · have hstep : (k₂ + 1) * n ≤ k₁ * n := Nat.mul_le_mul_right n hgt
        nlinarith [hstep, hn2B, h2lo, h1hi]
    have hsum_k_le_one : ∀ n ∈ Ioc M N,
        (∑ k ∈ S_ex n, (ArithmeticFunction.vonMangoldt k : ℝ) / k) ≤ 1 := by
      intro n hn
      calc
        (∑ k ∈ S_ex n, (ArithmeticFunction.vonMangoldt k : ℝ) / k)
            ≤ ∑ _k ∈ S_ex n, (1 : ℝ) := by
              refine sum_le_sum fun k hk => ?_
              have hk1 : 1 ≤ k := (mem_Icc.mp (mem_filter.mp hk).1).1
              have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
              rw [div_le_one hk0]
              calc
                (ArithmeticFunction.vonMangoldt k : ℝ) ≤ Real.log k :=
                  ArithmeticFunction.vonMangoldt_le_log
                _ ≤ (k : ℝ) - 1 := Real.log_le_sub_one_of_pos hk0
                _ ≤ k := by linarith
        _ = ((S_ex n).card : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_one]
        _ ≤ 1 := by exact_mod_cast hcard_one n hn
    unfold topCollarDualSeventhMass
    have hpt : ∀ n ∈ Ioc M N,
        ((n : ℝ) / N) ^ 7 * primeHorizonExtension u_b n ^ 2 ≤
          16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N) := by
      intro n hn
      have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
      have hnN : n ≤ N := (mem_Ioc.mp hn).2
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hnNR : (n : ℝ) ≤ N := by exact_mod_cast hnN
      let idx : PrimeHorizonIndex N := ⟨n, mem_Icc.mpr ⟨hn1, hnN⟩⟩
      have hext : primeHorizonExtension u_b n = b n / Real.sqrt (Real.log N) := by
        change primeHorizonExtension u_b idx.1 = _
        exact primeHorizonExtension_coe u_b idx
      rw [hext, div_pow (b n), Real.sq_sqrt hL0.le]
      have hbn : |b n| ≤ 4 * d * (m.totient : ℝ) * c / Real.sqrt n := by
        dsimp only [b]
        rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hn0)]
        refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        calc
          |linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n|
              ≤ 4 * (B : ℝ) * m.totient * 1 :=
                (hrow_ex n hn).trans (mul_le_mul_of_nonneg_left (hsum_k_le_one n hn) (by positivity))
          _ ≤ 4 * (d * c) * m.totient * 1 := by gcongr
          _ = 4 * d * (m.totient : ℝ) * c := by ring
      have hb2 : b n ^ 2 ≤ 16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / n := by
        have hsq := pow_le_pow_left₀ (abs_nonneg _) hbn 2
        rw [sq_abs, div_pow (4 * d * (m.totient : ℝ) * c), Real.sq_sqrt hn0.le] at hsq
        exact hsq.trans_eq (by ring)
      have hw7 : ((n : ℝ) / N) ^ 7 ≤ (n : ℝ) / N := by
        have h01 : (n : ℝ) / N ≤ 1 := (div_le_one hN0).mpr hnNR
        have h6 : ((n : ℝ) / N) ^ 6 ≤ 1 := pow_le_one₀ (by positivity) h01
        calc
          ((n : ℝ) / N) ^ 7 = ((n : ℝ) / N) * ((n : ℝ) / N) ^ 6 := by ring
          _ ≤ ((n : ℝ) / N) * 1 := mul_le_mul_of_nonneg_left h6 (by positivity)
          _ = (n : ℝ) / N := mul_one _
      calc
        ((n : ℝ) / N) ^ 7 * (b n ^ 2 / Real.log N)
            ≤ ((n : ℝ) / N) * ((16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / n) / Real.log N) :=
              mul_le_mul hw7 (div_le_div_of_nonneg_right hb2 hL0.le) (by positivity) (by positivity)
        _ = 16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N) := by
              field_simp [hn0.ne', hN0.ne', hL0.ne']
    calc
      _ ≤ ∑ _n ∈ Ioc M N, 16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N) :=
          sum_le_sum hpt
      _ = ((Ioc M N).card : ℝ) *
            (16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [Nat.card_Ioc]; exact_mod_cast Nat.sub_le N M
      _ = 16 * d ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / Real.log N := by
          field_simp [hN0.ne', hL0.ne']
  -- 3. `u_r` directly on `Ioc M N` via `abs_affineShellCorrection_error_le_linear`
  have hur : topCollarDualSeventhMass M N u_r ≤
      16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / Real.log N := by
    unfold topCollarDualSeventhMass
    have hpt : ∀ n ∈ Ioc M N,
        ((n : ℝ) / N) ^ 7 * primeHorizonExtension u_r n ^ 2 ≤
          16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N) := by
      intro n hn
      have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
      have hnN : n ≤ N := (mem_Ioc.mp hn).2
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hnNR : (n : ℝ) ≤ N := by exact_mod_cast hnN
      have hX1 : 1 ≤ (N : ℝ) / n := (one_le_div hn0).mpr hnNR
      let idx : PrimeHorizonIndex N := ⟨n, mem_Icc.mpr ⟨hn1, hnN⟩⟩
      have hext : primeHorizonExtension u_r n = r n / Real.sqrt (Real.log N) := by
        change primeHorizonExtension u_r idx.1 = _
        exact primeHorizonExtension_coe u_r idx
      rw [hext, div_pow (r n), Real.sq_sqrt hL0.le]
      have hr_eq : r n =
          (shiftedReciprocalUpwardRowError φ c id N m n +
            shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n) / 2 := by
        dsimp only [r, shiftedReciprocalUpwardRowError]
        rw [reciprocalUpwardCoefficient_eq_shifted_corrections hφ hsupp hc0 hB N m n hn1,
          shellCorrectionOfShift_reflected hm]
        change _ = ((affinePrimeShellCorrectionOfShift m n id φ c ((N : ℝ) / n) -
          ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n + _) / 2
        ring
      have hsh1 := abs_affineShellCorrection_error_le_linear hm hφ hsupp hM_int n id hc0 hX1
      have hsh2 := abs_affineShellCorrection_error_le_linear hm hφ hsupp hM_int n
        (reflectedAffineShift m) hc0 hX1
      have hrn : |r n| ≤ 4 * (Real.log 4 + 4) * (m.totient : ℝ) * c / Real.sqrt n := by
        rw [hr_eq]
        dsimp only [shiftedReciprocalUpwardRowError]
        have hs_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
        have h1 : |(affinePrimeShellCorrectionOfShift m n id φ c ((N : ℝ) / n) -
            ramanujanLagCoefficient m n * shellCorrectionOfShift φ c m id) / Real.sqrt n| ≤
            4 * (Real.log 4 + 4) * (m.totient : ℝ) * c / Real.sqrt n := by
          rw [abs_div, abs_of_pos hs_pos]
          exact div_le_div_of_nonneg_right hsh1 hs_pos.le
        have h2 : |(affinePrimeShellCorrectionOfShift m n (reflectedAffineShift m) φ c ((N : ℝ) / n) -
            ramanujanLagCoefficient m n * shellCorrectionOfShift φ c m (reflectedAffineShift m)) /
              Real.sqrt n| ≤
            4 * (Real.log 4 + 4) * (m.totient : ℝ) * c / Real.sqrt n := by
          rw [abs_div, abs_of_pos hs_pos]
          exact div_le_div_of_nonneg_right hsh2 hs_pos.le
        have htri := abs_add_le
          ((affinePrimeShellCorrectionOfShift m n id φ c ((N : ℝ) / n) -
            ramanujanLagCoefficient m n * shellCorrectionOfShift φ c m id) / Real.sqrt n)
          ((affinePrimeShellCorrectionOfShift m n (reflectedAffineShift m) φ c ((N : ℝ) / n) -
            ramanujanLagCoefficient m n * shellCorrectionOfShift φ c m (reflectedAffineShift m)) /
              Real.sqrt n)
        rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
        linarith only [htri, h1, h2]
      have hr2 : r n ^ 2 ≤ 16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / n := by
        have hsq := pow_le_pow_left₀ (abs_nonneg _) hrn 2
        rw [sq_abs, div_pow (4 * (Real.log 4 + 4) * (m.totient : ℝ) * c),
          Real.sq_sqrt hn0.le] at hsq
        exact hsq.trans_eq (by ring)
      have hw7 : ((n : ℝ) / N) ^ 7 ≤ (n : ℝ) / N := by
        have h01 : (n : ℝ) / N ≤ 1 := (div_le_one hN0).mpr hnNR
        have h6 : ((n : ℝ) / N) ^ 6 ≤ 1 := pow_le_one₀ (by positivity) h01
        calc
          ((n : ℝ) / N) ^ 7 = ((n : ℝ) / N) * ((n : ℝ) / N) ^ 6 := by ring
          _ ≤ ((n : ℝ) / N) * 1 := mul_le_mul_of_nonneg_left h6 (by positivity)
          _ = (n : ℝ) / N := mul_one _
      calc
        ((n : ℝ) / N) ^ 7 * (r n ^ 2 / Real.log N)
            ≤ ((n : ℝ) / N) *
                ((16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / n) / Real.log N) :=
              mul_le_mul hw7 (div_le_div_of_nonneg_right hr2 hL0.le) (by positivity) (by positivity)
        _ = 16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N) := by
              field_simp [hn0.ne', hN0.ne', hL0.ne']
    calc
      _ ≤ ∑ _n ∈ Ioc M N,
            16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N) :=
          sum_le_sum hpt
      _ = ((Ioc M N).card : ℝ) *
            (16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) *
            (16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / ((N : ℝ) * Real.log N)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [Nat.card_Ioc]; exact_mod_cast Nat.sub_le N M
      _ = 16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 2 / Real.log N := by
          field_simp [hN0.ne', hL0.ne']
  -- Combine `u_a`, `u_b`, `u_r` and divide by `m.totient`
  have hcomb : topCollarDualSeventhMass M N (normalizedUpwardPrimeResidual φ c N m) ≤
      4 * topCollarDualSeventhMass M N u_a + 4 * topCollarDualSeventhMass M N u_b +
        2 * topCollarDualSeventhMass M N u_r := by
    rw [hsplit3]
    have h1 := topCollarDualSeventhMass_add_le M N (u_a + u_b) u_r
    have h2 := topCollarDualSeventhMass_add_le M N u_a u_b
    linarith only [h1, h2]
  let rate := c ^ 2 / Real.log N + c ^ 10 * (Real.log N / N) ^ 2
  have hr1 : c ^ 2 / Real.log N ≤ rate := le_add_of_nonneg_right (by positivity)
  have hr2 : c ^ 10 * (Real.log N / N) ^ 2 ≤ rate := le_add_of_nonneg_left (by positivity)
  have htot_sum : topCollarDualSeventhMass M N (normalizedUpwardPrimeResidual φ c N m) ≤
      C_tot * (m.totient : ℝ) ^ 2 * rate := by
    have h_a : 4 * topCollarDualSeventhMass M N u_a ≤
        4 * Ca * d ^ 6 * (m.totient : ℝ) ^ 2 * rate := by
      calc
        4 * topCollarDualSeventhMass M N u_a
            ≤ 4 * (Ca * d ^ 6 * (m.totient : ℝ) ^ 2 * (c ^ 10 * (Real.log N / N) ^ 2)) :=
              mul_le_mul_of_nonneg_left (hua.trans_eq (by ring)) (by norm_num)
        _ ≤ 4 * (Ca * d ^ 6 * (m.totient : ℝ) ^ 2 * rate) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hr2 (by dsimp only [d]; positivity)) (by norm_num)
        _ = _ := by ring
    have h_b : 4 * topCollarDualSeventhMass M N u_b ≤
        64 * d ^ 2 * (m.totient : ℝ) ^ 2 * rate := by
      calc
        4 * topCollarDualSeventhMass M N u_b
            ≤ 4 * (16 * d ^ 2 * (m.totient : ℝ) ^ 2 * (c ^ 2 / Real.log N)) :=
              mul_le_mul_of_nonneg_left (hub.trans_eq (by ring)) (by norm_num)
        _ ≤ 4 * (16 * d ^ 2 * (m.totient : ℝ) ^ 2 * rate) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hr1 (by dsimp only [d]; positivity)) (by norm_num)
        _ = _ := by ring
    have h_r : 2 * topCollarDualSeventhMass M N u_r ≤
        32 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * rate := by
      calc
        2 * topCollarDualSeventhMass M N u_r
            ≤ 2 * (16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * (c ^ 2 / Real.log N)) :=
              mul_le_mul_of_nonneg_left (hur.trans_eq (by ring)) (by norm_num)
        _ ≤ 2 * (16 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * rate) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hr1 (by positivity)) (by norm_num)
        _ = _ := by ring
    have hcoef_le : 4 * Ca * d ^ 6 + 64 * d ^ 2 + 32 * (Real.log 4 + 4) ^ 2 ≤ C_tot := by
      dsimp only [C_tot]
      have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
      have hd6 : 0 ≤ Ca * d ^ 6 := mul_nonneg hCa (by positivity)
      have hl4 : 0 ≤ (Real.log 4 + 4) ^ 2 := sq_nonneg _
      linarith only [hd2, hd6, hl4]
    calc
      topCollarDualSeventhMass M N (normalizedUpwardPrimeResidual φ c N m)
          ≤ 4 * topCollarDualSeventhMass M N u_a + 4 * topCollarDualSeventhMass M N u_b +
              2 * topCollarDualSeventhMass M N u_r := hcomb
      _ ≤ 4 * Ca * d ^ 6 * (m.totient : ℝ) ^ 2 * rate +
            64 * d ^ 2 * (m.totient : ℝ) ^ 2 * rate +
            32 * (Real.log 4 + 4) ^ 2 * (m.totient : ℝ) ^ 2 * rate :=
          add_le_add (add_le_add h_a h_b) h_r
      _ = (4 * Ca * d ^ 6 + 64 * d ^ 2 + 32 * (Real.log 4 + 4) ^ 2) *
            ((m.totient : ℝ) ^ 2 * rate) := by ring
      _ ≤ C_tot * ((m.totient : ℝ) ^ 2 * rate) :=
          mul_le_mul_of_nonneg_right hcoef_le (by dsimp only [rate]; positivity)
      _ = C_tot * (m.totient : ℝ) ^ 2 * rate := by ring
  calc
    (m.totient : ℝ)⁻¹ * topCollarDualSeventhMass M N (normalizedUpwardPrimeResidual φ c N m)
        ≤ (m.totient : ℝ)⁻¹ * (C_tot * (m.totient : ℝ) ^ 2 * rate) :=
          mul_le_mul_of_nonneg_left htot_sum (by positivity)
    _ = C_tot * (m.totient : ℝ) * rate := by field_simp [htot_pos.ne']
    _ ≤ C_tot * (m : ℝ) * rate :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left htot_le (by dsimp only [C_tot, d]; positivity))
            (by dsimp only [rate]; positivity)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTopCollarHasADyadicSeventhPowerReserve
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BilinearConductorResidualsAndOneEighthPackets
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SharpenedMidBandAndCrossBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheJetPoleComponentCancelsThePole
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandOverlapAndNonRatioBounds
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.RamanujanAutocorrelationWeights
import GaloisForLFunctions.RHTower.ThetaIntegerCutoffMovingPacket

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

/-! ### Channel 3 Bilinear Residual without Logarithm of Overlap -/

/-- Complete-center bilinear residual bound `O(|α| * m * √l / log N)` across all `m, l ≥ 1`,
combining exact ground-pole harmonic boundary cancellation at `m = 1` with zero-mean periodic
summation by parts at `m ≥ 2`. -/
theorem fullWeilCenter_bilinear_log_free (α : ℝ) {m l N : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hN : 1 ≤ N) (hL0 : 0 < Real.log (N : ℝ)) :
    |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then α else 0) • normalizedRamanujanHorizonVector m N,
      normalizedRamanujanHorizonVector l N⟫| ≤
      5 * |α| * (m : ℝ) * Real.sqrt l / Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hm1 : m = 1
  · subst hm1
    rw [if_pos rfl, Nat.cast_one, mul_one]
    let r₁ := Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
      (normalizedRamanujanHorizonVector 1 N) - α • normalizedRamanujanHorizonVector 1 N
    let B_row : ℕ → ℝ := fun n => (α / N) * Real.sqrt n *
      ((harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 + 3 / (4 * (n : ℝ)))
    have hr1_coord : ∀ n : PrimeHorizonIndex N, r₁ n = B_row n.1 / Real.sqrt (Real.log N) := by
      intro n
      have hn : (n : ℕ) ∈ Icc 1 N := n.2
      have hmode1 : ∀ j : ℕ, ramanujanPoleProfile 1 j = 1 / Real.sqrt j := fun j => by
        rw [ramanujanPoleProfile, normalizedRamanujanMode, ramanujanMode_one,
          Nat.totient_one, Nat.cast_one, Real.sqrt_one, div_one]
      change (Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
          ((Real.sqrt (Real.log N))⁻¹ • ramanujanHorizonVector 1 N)) n -
        α * ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile 1 n) = _
      rw [map_smul]
      change (Real.sqrt (Real.log N))⁻¹ *
          ((Matrix.toEuclideanLin
            (horizonKernelMatrix (fun i j => (α / N) *
              (Real.sqrt i / Real.sqrt j + Real.sqrt j / Real.sqrt i -
                archimedeanCenterKernel i j)) N)
            (horizonProfileVector (ramanujanPoleProfile 1) N)) n) -
        α * ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile 1 n) = _
      rw [horizonKernelMatrix_apply_profile, hmode1 n]
      have hsum_eq : (∑ j ∈ Icc 1 N,
          (α / N) * (Real.sqrt (n : ℕ) / Real.sqrt j + Real.sqrt j / Real.sqrt (n : ℕ) -
            archimedeanCenterKernel n j) * ramanujanPoleProfile 1 j) =
          (α / N) * ∑ j ∈ Icc 1 N,
            ((Real.sqrt (n : ℕ) / Real.sqrt j + Real.sqrt j / Real.sqrt (n : ℕ)) -
              archimedeanCenterKernel n j) / Real.sqrt j := by
        rw [mul_sum]
        refine sum_congr rfl fun j _ => ?_
        rw [hmode1 j]; ring
      rw [hsum_eq, sum_pole_minus_center_div_sqrt hn]
      dsimp only [B_row]
      have hcanc : (α / N) * ((N : ℝ) / Real.sqrt (n : ℕ) + Real.sqrt (n : ℕ) *
          ((harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 +
            3 / (4 * ((n : ℕ) : ℝ)))) - α * (1 / Real.sqrt (n : ℕ)) =
          (α / N) * Real.sqrt (n : ℕ) *
            ((harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 +
              3 / (4 * ((n : ℕ) : ℝ))) := by
        rw [mul_add, div_mul_div_cancel₀ hN0.ne']; ring
      have hfactor : (Real.sqrt (Real.log N))⁻¹ *
          ((α / N) * ((N : ℝ) / Real.sqrt (n : ℕ) + Real.sqrt (n : ℕ) *
            ((harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 +
              3 / (4 * ((n : ℕ) : ℝ))))) -
          α * ((Real.sqrt (Real.log N))⁻¹ * (1 / Real.sqrt (n : ℕ))) =
          (Real.sqrt (Real.log N))⁻¹ *
            ((α / N) * ((N : ℝ) / Real.sqrt (n : ℕ) + Real.sqrt (n : ℕ) *
              ((harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 +
                3 / (4 * ((n : ℕ) : ℝ)))) - α * (1 / Real.sqrt (n : ℕ))) := by ring
      rw [hfactor, hcanc]; ring
    have hp := abs_inner_of_coord_div_sqrt_log hl r₁ B_row hr1_coord
    let b_bdry : ℕ → ℝ := fun n =>
      (harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 + 3 / (4 * (n : ℝ))
    have hb_sq_sum : (∑ n ∈ Icc 1 N, b_bdry n ^ 2) ≤ 6 * (N : ℝ) := by
      have hpt : ∀ n ∈ Icc 1 N, b_bdry n ^ 2 ≤ ((harmonic N : ℝ) - harmonic (N - n)) ^ 2 + 4 := by
        intro n hn
        have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
        let a₀ := (harmonic N : ℝ) - harmonic (N - n)
        let b₀ := (harmonic (N + n) : ℝ) - harmonic N
        let d₀ := 3 / (4 * (n : ℝ))
        have hb0_lo : 0 ≤ b₀ := HTGeometry.harmonic_add_sub_nonneg N n
        have hb0_hi : b₀ ≤ 1 := HTGeometry.harmonic_add_sub_le_one (mem_Icc.mp hn).2
        have hd0_lo : 0 ≤ d₀ := by dsimp only [d₀]; positivity
        have hd0_hi : d₀ ≤ 1 := by
          dsimp only [d₀]; rw [div_le_one (by positivity)]; linarith only [hn1R]
        have hb2 : b₀ ^ 2 ≤ 1 := by nlinarith only [mul_nonneg hb0_lo (sub_nonneg.mpr hb0_hi), hb0_hi]
        have hd2 : d₀ ^ 2 ≤ 1 := by nlinarith only [mul_nonneg hd0_lo (sub_nonneg.mpr hd0_hi), hd0_hi]
        have hcs3 : (a₀ - b₀ + 2 * d₀) ^ 2 ≤ 3 * (a₀ ^ 2 + b₀ ^ 2 + 4 * d₀ ^ 2) := by
          nlinarith only [sq_nonneg (a₀ + b₀), sq_nonneg (a₀ - 2 * d₀), sq_nonneg (b₀ + 2 * d₀)]
        have hid_b : b_bdry n = (a₀ - b₀) / 2 + d₀ := by dsimp only [b_bdry, a₀, b₀, d₀]; ring
        rw [hid_b]
        nlinarith only [hcs3, hb2, hd2, sq_nonneg a₀]
      have hhar_nonneg : 0 ≤ (harmonic N : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        exact sum_nonneg fun _ _ => by positivity
      calc
        (∑ n ∈ Icc 1 N, b_bdry n ^ 2) ≤
            ∑ n ∈ Icc 1 N, (((harmonic N : ℝ) - harmonic (N - n)) ^ 2 + 4) := sum_le_sum hpt
        _ = 2 * (N : ℝ) - harmonic N + 4 * (N : ℝ) := by
          rw [sum_add_distrib, HTGeometry.sum_sq_harmonic_boundary_tails,
            sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          ring
        _ ≤ 6 * (N : ℝ) := by linarith only [hhar_nonneg]
    have hb_l1 : (∑ n ∈ Icc 1 N, |b_bdry n|) ≤ 3 * (N : ℝ) := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N) (fun n => |b_bdry n|) (fun _ => (1 : ℝ))
      simp only [mul_one, sq_abs, one_pow, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
        nsmul_eq_mul, mul_one] at hcs
      have hsq : (∑ n ∈ Icc 1 N, |b_bdry n|) ^ 2 ≤ (3 * (N : ℝ)) ^ 2 := by
        calc
          _ ≤ (∑ n ∈ Icc 1 N, b_bdry n ^ 2) * (N : ℝ) := hcs
          _ ≤ (6 * (N : ℝ)) * (N : ℝ) := mul_le_mul_of_nonneg_right hb_sq_sum hN0.le
          _ ≤ (3 * (N : ℝ)) ^ 2 := by nlinarith only [sq_nonneg (N : ℝ)]
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (sum_nonneg fun _ _ => abs_nonneg _), Real.sqrt_sq (by positivity)] at h
    have hsum_B : (∑ n ∈ Icc 1 N, |B_row n| / Real.sqrt n) ≤ 3 * |α| := by
      have hpt : ∀ n ∈ Icc 1 N, |B_row n| / Real.sqrt n = (|α| / N) * |b_bdry n| := by
        intro n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
        dsimp only [B_row, b_bdry]
        rw [abs_mul, abs_mul, abs_div, abs_of_pos hN0, abs_of_pos hsn]
        field_simp [hsn.ne', hN0.ne']
      rw [sum_congr rfl hpt, ← mul_sum]
      calc
        (|α| / N) * (∑ n ∈ Icc 1 N, |b_bdry n|) ≤ (|α| / N) * (3 * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hb_l1 (by positivity)
        _ = 3 * |α| := by field_simp [hN0.ne']
    calc
      |⟪r₁, normalizedRamanujanHorizonVector l N⟫| ≤
          Real.sqrt l / Real.log N * (3 * |α|) :=
        hp.trans (mul_le_mul_of_nonneg_left hsum_B (by positivity))
      _ ≤ 5 * |α| * Real.sqrt l / Real.log N := by
        have h35 : 3 * |α| ≤ 5 * |α| := by linarith [abs_nonneg α]
        calc
          Real.sqrt l / Real.log N * (3 * |α|) ≤ Real.sqrt l / Real.log N * (5 * |α|) :=
            mul_le_mul_of_nonneg_left h35 (by positivity)
          _ = 5 * |α| * Real.sqrt l / Real.log N := by ring
  · have hm2 : 2 ≤ m := by omega
    rw [if_neg hm1, zero_smul, sub_zero]
    let u := Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (normalizedRamanujanHorizonVector m N)
    let row_u : ℕ → ℝ := fun n => (α / N) * ∑ j ∈ Icc 1 N,
      (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n - archimedeanCenterKernel n j) *
        (normalizedRamanujanMode m j / Real.sqrt j)
    let B : ℕ → ℝ := fun n => 5 * |α| * (m : ℝ) * Real.sqrt n / N
    have hcoord : ∀ n : PrimeHorizonIndex N, u n = row_u n.1 / Real.sqrt (Real.log N) := by
      intro n
      change (Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
        ((Real.sqrt (Real.log N))⁻¹ • ramanujanHorizonVector m N)) n = _
      rw [map_smul]
      change (Real.sqrt (Real.log N))⁻¹ *
        ((Matrix.toEuclideanLin
          (horizonKernelMatrix (fun i j => (α / N) *
            (Real.sqrt i / Real.sqrt j + Real.sqrt j / Real.sqrt i -
              archimedeanCenterKernel i j)) N)
          (horizonProfileVector (ramanujanPoleProfile m) N)) n) = _
      rw [horizonKernelMatrix_apply_profile]
      dsimp only [row_u]
      have hsum : (∑ j ∈ Icc 1 N,
          (α / N) * (Real.sqrt (n : ℕ) / Real.sqrt j + Real.sqrt j / Real.sqrt (n : ℕ) -
            archimedeanCenterKernel n j) * ramanujanPoleProfile m j) =
          (α / N) * ∑ j ∈ Icc 1 N,
            (Real.sqrt (n : ℕ) / Real.sqrt j + Real.sqrt j / Real.sqrt (n : ℕ) -
              archimedeanCenterKernel n j) * (normalizedRamanujanMode m j / Real.sqrt j) := by
        rw [mul_sum]
        refine sum_congr rfl fun j _ => ?_
        unfold ramanujanPoleProfile; ring
      rw [hsum]; ring
    have hrow_le : ∀ n ∈ Icc 1 N, |row_u n| ≤ B n := by
      intro n hn
      have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hsm_le : Real.sqrt (m : ℝ) ≤ m := by
        have hsq : (Real.sqrt (m : ℝ)) ^ 2 ≤ (m : ℝ) ^ 2 := by
          rw [Real.sq_sqrt (by positivity)]; nlinarith only [hm1R]
        have h := Real.sqrt_le_sqrt hsq
        rwa [Real.sqrt_sq (Real.sqrt_nonneg _), Real.sqrt_sq (by positivity)] at h
      dsimp only [row_u]
      rw [abs_mul, abs_div, abs_of_pos hN0]
      have hrow := abs_sum_poleMinusCollar_poleProfile_le hn (Real.sqrt_nonneg (m : ℝ))
        (abs_mode_le_sqrt_conductor hm n)
        (fun a b hab => CompletedArithmeticForms.abs_sum_Ico_normalizedRamanujanMode_le hm2 hab)
      calc
        |α| / N * |∑ j ∈ Icc 1 N,
            (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n -
              archimedeanCenterKernel n j) * (normalizedRamanujanMode m j / Real.sqrt j)|
            ≤ |α| / N * ((4 * (m : ℝ) + Real.sqrt m) * Real.sqrt n) :=
          mul_le_mul_of_nonneg_left hrow (by positivity)
        _ ≤ |α| / N * ((5 * (m : ℝ)) * Real.sqrt n) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by linarith only [hsm_le]) (Real.sqrt_nonneg _))
            (by positivity)
        _ = B n := by dsimp only [B]; ring
    have hp := abs_inner_of_coord_div_sqrt_log hl u row_u hcoord
    have hsumB : (∑ n ∈ Icc 1 N, |row_u n| / Real.sqrt n) ≤ 5 * |α| * (m : ℝ) := by
      have hpt : ∀ n ∈ Icc 1 N, |row_u n| / Real.sqrt n ≤ 5 * |α| * (m : ℝ) / N := by
        intro n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
        calc
          |row_u n| / Real.sqrt n ≤ B n / Real.sqrt n :=
            div_le_div_of_nonneg_right (hrow_le n hn) hsn.le
          _ = 5 * |α| * (m : ℝ) / N := by dsimp only [B]; field_simp [hsn.ne', hN0.ne']
      calc
        (∑ n ∈ Icc 1 N, |row_u n| / Real.sqrt n)
            ≤ ∑ _n ∈ Icc 1 N, (5 * |α| * (m : ℝ) / N) := sum_le_sum hpt
        _ = 5 * |α| * (m : ℝ) := by
          rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
          field_simp [hN0.ne']
    calc
      |⟪u, normalizedRamanujanHorizonVector l N⟫|
          ≤ Real.sqrt l / Real.log N * (5 * |α| * (m : ℝ)) :=
        hp.trans (mul_le_mul_of_nonneg_left hsumB (by positivity))
      _ = 5 * |α| * (m : ℝ) * Real.sqrt l / Real.log N := by ring

/-! ## Section 3b: Upward Prime Bilinear Residual via Near-Gram Mode Polarization -/

/-- Near-Gram bilinear pairing of normalized Ramanujan horizon modes `v_m` and `v_l`. -/
def nearGramModeBilin (φ : ℝ → ℝ) (c : ℝ) (N m l : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
    nearGram φ c N (primeHorizonExtension (normalizedRamanujanHorizonVector l N)) n

private theorem nearRowIndices_symm_mem {c : ℝ} {N n j : ℕ} (hn : n ∈ Icc 1 N) :
    j ∈ nearRowIndices c N n ↔ j ∈ Icc 1 N ∧ n ∈ nearRowIndices c N j := by
  simp only [nearRowIndices, mem_filter]
  constructor
  · rintro ⟨hj, hjn, hlog⟩
    exact ⟨hj, hn, Ne.symm hjn, by rwa [abs_sub_comm]⟩
  · rintro ⟨hj, _, hnj, hlog⟩
    exact ⟨hj, Ne.symm hnj, by rwa [abs_sub_comm]⟩

private theorem nearGram_bilinear_symm (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (f g : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, f n * nearGram φ c N g n) =
      ∑ n ∈ Icc 1 N, g n * nearGram φ c N f n := by
  unfold nearGram
  have hexp : ∀ h₁ h₂ : ℕ → ℝ,
      (∑ n ∈ Icc 1 N, h₁ n * ∑ j ∈ nearRowIndices c N n,
        shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ t, φ t ^ 2) * h₂ j) =
      ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        if j ≠ n ∧ |Real.log (j : ℝ) - Real.log (n : ℝ)| ≤ 2 * c / N then
          h₁ n * h₂ j * (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ t, φ t ^ 2))
        else 0 := by
    intro h₁ h₂
    refine sum_congr rfl fun n _ => ?_
    rw [nearRowIndices, mul_sum, sum_filter]
    refine sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [hexp f g, hexp g f, sum_comm]
  refine sum_congr rfl fun n _ => sum_congr rfl fun j _ => ?_
  have hcond : (n ≠ j ∧ |Real.log (n : ℝ) - Real.log (j : ℝ)| ≤ 2 * c / N) ↔
      (j ≠ n ∧ |Real.log (j : ℝ) - Real.log (n : ℝ)| ≤ 2 * c / N) := by
    rw [ne_comm, abs_sub_comm]
  by_cases hp : j ≠ n ∧ |Real.log (j : ℝ) - Real.log (n : ℝ)| ≤ 2 * c / N
  · rw [if_pos (hcond.mpr hp), if_pos hp, abs_sub_comm]; ring
  · rw [if_neg (fun h => hp (hcond.mp h)), if_neg hp]

private theorem nearGram_quad_eq_leadKernel {φ : ℝ → ℝ} (hM : 0 < ∫ t, φ t ^ 2)
    (c : ℝ) (N : ℕ) (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    (∫ t, φ t ^ 2) *
        (∑ n ∈ Icc 1 N, primeHorizonExtension u n * nearGram φ c N (primeHorizonExtension u) n) =
      ∑ n ∈ Icc 1 N, primeHorizonExtension u n *
        ∑ j ∈ nearRowIndices c N n, midBandLeadKernel φ c N n j * primeHorizonExtension u j := by
  rw [mul_sum]
  refine sum_congr rfl fun n _ => ?_
  unfold nearGram midBandLeadKernel
  rw [mul_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have hM0 : (∫ t, φ t ^ 2) ≠ 0 := hM.ne'
  field_simp [hM0]

/-- Change of variables `u = r / y` identifying `∫_0^1 G(r / y) / y dy = ∫_r^1 G(u) / u du` for
`0 < r ≤ 1`. -/
private theorem integral_recip_shellAutocorr_eq {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∫ y in (0 : ℝ)..1, if y ≤ 0 then 0 else shellAutocorr φ (r / y) / y) =
      ∫ u in r..1, shellAutocorr φ u / u := by
  let f : ℝ → ℝ := fun y => if y ≤ 0 then 0 else shellAutocorr φ (r / y) / y
  have hf_zero : ∀ y ≤ r, f y = 0 := by
    intro y hyr
    dsimp only [f]
    by_cases hy0 : y ≤ 0
    · rw [if_pos hy0]
    · rw [if_neg hy0]
      have hy_pos : 0 < y := lt_of_not_ge hy0
      have h1 : 1 ≤ r / y := (one_le_div hy_pos).mpr hyr
      rw [shellAutocorr_eq_zero_of_one_le hφ hsupp h1, zero_div]
  have hf_cont : ContinuousOn f (Set.Icc 0 1) := by
    intro y hy
    rcases lt_or_ge y r with hyr | hry
    · refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_ (hf_zero y hyr.le)
      have hnhds : Set.Iio r ∈ 𝓝[Set.Icc (0 : ℝ) 1] y :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hyr)
      filter_upwards [self_mem_nhdsWithin, hnhds] with z _ hz2
      exact hf_zero z hz2.le
    · have hy_pos : 0 < y := hr0.trans_le hry
      have hg_at : ContinuousAt (fun z => shellAutocorr φ (r / z) / z) y :=
        ((continuous_shellAutocorr hφ hsupp).continuousAt.comp
          (continuousAt_const.div continuousAt_id hy_pos.ne')).div continuousAt_id hy_pos.ne'
      refine hg_at.continuousWithinAt.congr_of_eventuallyEq ?_ (by dsimp only [f]; rw [if_neg (not_le.mpr hy_pos)])
      have hnhds : Set.Ioi (0 : ℝ) ∈ 𝓝[Set.Icc (0 : ℝ) 1] y :=
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hy_pos)
      filter_upwards [hnhds] with z hz
      dsimp only [f]; rw [if_neg (not_le.mpr hz)]
  have hi1 : IntervalIntegrable f volume 0 r :=
    (hf_cont.mono (by rw [Set.uIcc_of_le hr0.le]; exact Set.Icc_subset_Icc le_rfl hr1)).intervalIntegrable
  have hi2 : IntervalIntegrable f volume r 1 :=
    (hf_cont.mono (by rw [Set.uIcc_of_le hr1]; exact Set.Icc_subset_Icc hr0.le le_rfl)).intervalIntegrable
  change ∫ y in (0 : ℝ)..1, f y = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hz0 : ∫ y in (0 : ℝ)..r, f y = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
    intro y hy
    rw [Set.uIcc_of_le hr0.le] at hy
    exact hf_zero y hy.2
  rw [hz0, zero_add]
  have hf_on_r1 : ∫ y in r..1, f y = ∫ y in r..1, shellAutocorr φ (r / y) / y := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hr1] at hy
    have hy0 : 0 < y := hr0.trans_le hy.1
    dsimp only [f]; rw [if_neg (not_le.mpr hy0)]
  rw [hf_on_r1]
  have hpos : ∀ x ∈ Set.uIcc r 1, 0 < x := fun x hx => by
    rw [Set.uIcc_of_le hr1] at hx; exact hr0.trans_le hx.1
  have hderiv : ∀ x ∈ Set.uIcc r 1, HasDerivAt (fun y => r / y) (-(r / x ^ 2)) x := by
    intro x hx
    have hx0 := (hpos x hx).ne'
    simpa only [div_eq_mul_inv] using
      ((hasDerivAt_inv hx0).const_mul r).congr_deriv (by field_simp [hx0])
  have hcont_d : ContinuousOn (fun x => -(r / x ^ 2)) (Set.uIcc r 1) :=
    (continuousOn_const.div (continuousOn_pow 2) fun x hx => pow_ne_zero 2 (hpos x hx).ne').neg
  have hgcont : ContinuousOn (fun u => shellAutocorr φ u / u) ((fun y => r / y) '' Set.uIcc r 1) :=
    (continuous_shellAutocorr hφ hsupp).continuousOn.div continuousOn_id fun u hu => by
      obtain ⟨x, hx, rfl⟩ := hu
      exact (div_pos hr0 (hpos x hx)).ne'
  have key := intervalIntegral.integral_comp_mul_deriv' hderiv hcont_d hgcont
  have hcongr : (∫ y in r..1, shellAutocorr φ (r / y) / y) =
      -∫ x in r..1, ((fun u => shellAutocorr φ u / u) ∘ fun y => r / y) x * (-(r / x ^ 2)) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx0 := (hpos x hx).ne'
    have hr_ne := hr0.ne'
    simp only [Function.comp_apply]
    field_simp [hx0, hr_ne]
  rw [hcongr, key, intervalIntegral.integral_symm, neg_neg, div_self hr0.ne', div_one]

/-- Riemann-sum approximation of the linearized lag weight sum by the reciprocal shell integral,
with deterministic `O(c^2 / N)` error uniformly over `1 ≤ h ≤ ⌊linearNearRowRadius c⌋₊`. -/
private theorem exists_sum_midBandLinearizedWeight_sub_shellIntegral_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) :
    ∃ C_w : ℝ, 0 ≤ C_w ∧ ∀ {N : ℕ} {c : ℝ},
      1 ≤ c → 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ∀ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
        |(∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
            midBandLinearizedWeight φ c N h n) -
          ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| ≤ C_w * c ^ 2 / N := by
  obtain ⟨K_lip, hG_lip⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  have hG_le : ∀ t, |shellAutocorr φ t| ≤ ∫ t, φ t ^ 2 := abs_shellAutocorr_le hφ hsupp
  have hM_nn : 0 ≤ ∫ t, φ t ^ 2 := integral_nonneg fun t => sq_nonneg (φ t)
  let C_w : ℝ := (K_lip : ℝ) + (∫ t, φ t ^ 2) + 4 * Real.exp 2 * (∫ t, φ t ^ 2) + 1
  refine ⟨C_w, by dsimp only [C_w]; positivity, ?_⟩
  intro N c hc1 hradN h hh
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ 4 * (linearNearRowRadius c + 1) ^ 2 := by
      have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      nlinarith only [h0]
    exact_mod_cast this.trans hradN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hh1, hhB⟩ := mem_Icc.mp hh
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh1
  have hh1R : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  let r := (h : ℝ) / c
  have hr0 : 0 < r := div_pos hh0 hc0
  rcases le_or_gt 1 r with hr1 | hr1
  · -- When `h / c ≥ 1`, both the finite sum and the reciprocal shell integral vanish identically.
    have hint0 : ∫ u in r..1, shellAutocorr φ u / u = 0 :=
      integral_shellAutocorr_div_eq_zero hφ hsupp hr1
    have hsum0 : (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
        midBandLinearizedWeight φ c N h n) = 0 := by
      refine sum_eq_zero fun n hn => ?_
      have hnN : n ≤ N := (mem_Ioc.mp hn).2.trans (Nat.sub_le N h)
      have hn0 : 0 < n := by
        have := (mem_Ioc.mp hn).1; omega
      have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0
      have harg1 : 1 ≤ (N : ℝ) / c * ((h : ℝ) / n) := by
        have hNn : 1 ≤ (N : ℝ) / n := (one_le_div hn0R).mpr (by exact_mod_cast hnN)
        calc
          (1 : ℝ) ≤ r * ((N : ℝ) / n) := one_le_mul_of_one_le_of_one_le hr1 hNn
          _ = (N : ℝ) / c * ((h : ℝ) / n) := by dsimp only [r]; ring
      unfold midBandLinearizedWeight
      rw [shellAutocorr_eq_zero_of_one_le hφ hsupp harg1, mul_zero]
    rw [hsum0, hint0, sub_zero, abs_zero]
    dsimp only [C_w]; positivity
  · -- When `h / c < 1`, extend `Ioc K₀ (N - h)` to `Icc 1 N` and apply Lipschitz Riemann sum.
    let K₀ := ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊
    have hRc_ge : c ≤ linearNearRowRadius c := by
      unfold linearNearRowRadius
      have he2 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
      nlinarith only [hc0, he2]
    have h2h_N : 2 * h ≤ N := by
      have hh_Rc : (h : ℝ) ≤ linearNearRowRadius c :=
        (by exact_mod_cast hhB : (h : ℝ) ≤ ⌊linearNearRowRadius c⌋₊).trans
          (Nat.floor_le (by unfold linearNearRowRadius; positivity))
      have h2R : 2 * linearNearRowRadius c ≤ 4 * (linearNearRowRadius c + 1) ^ 2 := by
        have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
        nlinarith only [h0]
      have hR : 2 * (h : ℝ) ≤ N :=
        (mul_le_mul_of_nonneg_left hh_Rc zero_le_two).trans (h2R.trans hradN)
      exact_mod_cast hR
    have hK0_nh : K₀ ≤ N - h := by
      have h1 : (K₀ : ℝ) ≤ (N : ℝ) / (linearNearRowRadius c + 1) :=
        Nat.floor_le (by unfold linearNearRowRadius; positivity)
      have hT2 : (2 : ℝ) ≤ linearNearRowRadius c + 1 := by linarith only [hc1, hRc_ge]
      have h2 : (N : ℝ) / (linearNearRowRadius c + 1) ≤ (N : ℝ) / 2 :=
        div_le_div_of_nonneg_left hN0.le zero_lt_two hT2
      have h3 : (h : ℝ) ≤ (N : ℝ) / 2 := by
        have : 2 * (h : ℝ) ≤ N := by exact_mod_cast h2h_N
        linarith only [this]
      have h4 : (K₀ : ℝ) ≤ (N - h : ℕ) := by
        rw [Nat.cast_sub (by omega : h ≤ N)]
        linarith only [h1, h2, h3]
      exact_mod_cast h4
    -- Deep indices `1 ≤ n ≤ K₀` have `midBandLinearizedWeight = 0`.
    have hdeep_zero : ∀ n ∈ Icc 1 K₀, midBandLinearizedWeight φ c N h n = 0 := by
      intro n hn
      obtain ⟨hn1, hnK⟩ := mem_Icc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hn_le : (n : ℝ) ≤ (N : ℝ) / (linearNearRowRadius c + 1) :=
        (by exact_mod_cast hnK : (n : ℝ) ≤ K₀).trans
          (Nat.floor_le (by unfold linearNearRowRadius; positivity))
      have hT_gt : c ≤ linearNearRowRadius c + 1 := by linarith only [hRc_ge]
      have hn_Nc : (n : ℝ) ≤ (N : ℝ) * (h : ℝ) / c := by
        calc
          (n : ℝ) ≤ (N : ℝ) / (linearNearRowRadius c + 1) := hn_le
          _ ≤ (N : ℝ) / c := div_le_div_of_nonneg_left hN0.le hc0 hT_gt
          _ ≤ (N : ℝ) * (h : ℝ) / c := by
            rw [div_le_div_iff_of_pos_right hc0]
            exact le_mul_of_one_le_right hN0.le hh1R
      have harg1 : 1 ≤ (N : ℝ) / c * ((h : ℝ) / n) := by
        rw [show (N : ℝ) / c * ((h : ℝ) / n) = ((N : ℝ) * (h : ℝ) / c) / n by ring]
        exact (one_le_div hn0).mpr hn_Nc
      unfold midBandLinearizedWeight
      rw [shellAutocorr_eq_zero_of_one_le hφ hsupp harg1, mul_zero]
    -- Top `h` indices `N - h < n ≤ N` contribute `O(c / N)`.
    have htop_err : |∑ n ∈ Ioc (N - h) N, midBandLinearizedWeight φ c N h n| ≤
        4 * Real.exp 2 * (∫ t, φ t ^ 2) * c ^ 2 / N := by
      have hpt : ∀ n ∈ Ioc (N - h) N,
          |midBandLinearizedWeight φ c N h n| ≤ 2 * (∫ t, φ t ^ 2) / N := by
        intro n hn
        obtain ⟨hn_lo, _⟩ := mem_Ioc.mp hn
        have hn_ge : N ≤ 2 * n := by omega
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hinv : 1 / (n : ℝ) ≤ 2 / (N : ℝ) := by
          rw [div_le_div_iff₀ hn0 hN0]
          have : (N : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hn_ge
          linarith only [this]
        unfold midBandLinearizedWeight
        rw [abs_mul, abs_of_pos (one_div_pos.mpr hn0)]
        exact (mul_le_mul hinv (hG_le _) (abs_nonneg _) (by positivity)).trans_eq (by ring)
      have hh_le : (h : ℝ) ≤ 2 * Real.exp 2 * c ^ 2 := by
        have h1 : (h : ℝ) ≤ linearNearRowRadius c :=
          (by exact_mod_cast hhB : (h : ℝ) ≤ ⌊linearNearRowRadius c⌋₊).trans
            (Nat.floor_le (by unfold linearNearRowRadius; positivity))
        unfold linearNearRowRadius at h1
        have hc2 : c ≤ c ^ 2 := by nlinarith only [hc1]
        nlinarith only [h1, hc2, Real.exp_pos 2]
      calc
        |∑ n ∈ Ioc (N - h) N, midBandLinearizedWeight φ c N h n|
            ≤ ∑ n ∈ Ioc (N - h) N, |midBandLinearizedWeight φ c N h n| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Ioc (N - h) N, (2 * (∫ t, φ t ^ 2) / N) := sum_le_sum hpt
        _ = ((Ioc (N - h) N).card : ℝ) * (2 * (∫ t, φ t ^ 2) / N) := by
          rw [sum_const, nsmul_eq_mul]
        _ ≤ (h : ℝ) * (2 * (∫ t, φ t ^ 2) / N) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [Nat.card_Ioc, Nat.sub_sub_self (by omega : h ≤ N)]
        _ ≤ (2 * Real.exp 2 * c ^ 2) * (2 * (∫ t, φ t ^ 2) / N) :=
          mul_le_mul_of_nonneg_right hh_le (by positivity)
        _ = 4 * Real.exp 2 * (∫ t, φ t ^ 2) * c ^ 2 / N := by ring
    have hsplit_Icc : (∑ n ∈ Icc 1 N, midBandLinearizedWeight φ c N h n) =
        (∑ n ∈ Ioc K₀ (N - h), midBandLinearizedWeight φ c N h n) +
          ∑ n ∈ Ioc (N - h) N, midBandLinearizedWeight φ c N h n := by
      have hu1 : Icc 1 N = Icc 1 (N - h) ∪ Ioc (N - h) N := by
        ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
      have hd1 : Disjoint (Icc 1 (N - h)) (Ioc (N - h) N) :=
        disjoint_left.mpr fun n a b => by
          have := (mem_Icc.mp a).2; have := (mem_Ioc.mp b).1; omega
      have hu2 : Icc 1 (N - h) = Icc 1 K₀ ∪ Ioc K₀ (N - h) := by
        ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
      have hd2 : Disjoint (Icc 1 K₀) (Ioc K₀ (N - h)) :=
        disjoint_left.mpr fun n a b => by
          have := (mem_Icc.mp a).2; have := (mem_Ioc.mp b).1; omega
      rw [hu1, sum_union hd1, hu2, sum_union hd2, sum_eq_zero hdeep_zero, zero_add]
    -- Identify `∑_{n ∈ Icc 1 N} midBandLinearizedWeight` with the Riemann sum of `f` on `[0, 1]`.
    let f : ℝ → ℝ := fun y => if y ≤ 0 then 0 else shellAutocorr φ (r / y) / y
    have hf_zero : ∀ y ≤ r, f y = 0 := by
      intro y hyr
      dsimp only [f]
      by_cases hy0 : y ≤ 0
      · rw [if_pos hy0]
      · rw [if_neg hy0]
        have hy_pos : 0 < y := lt_of_not_ge hy0
        rw [shellAutocorr_eq_zero_of_one_le hφ hsupp ((one_le_div hy_pos).mpr hyr), zero_div]
    have hrc_inv : 1 / c ≤ r := by
      dsimp only [r]; exact div_le_div_of_nonneg_right hh1R hc0.le
    have hr_sq_inv : 1 / r ^ 2 ≤ c ^ 2 := by
      calc
        1 / r ^ 2 ≤ 1 / (1 / c) ^ 2 :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hrc_inv 2)
        _ = c ^ 2 := by field_simp [hc0.ne']
    -- Lipschitz constant of `f` on `[0, 1]`.
    let L_f : ℝ := ((K_lip : ℝ) + ∫ t, φ t ^ 2) * c ^ 2
    have hLf0 : 0 ≤ L_f := by dsimp only [L_f]; positivity
    have hf_pair_above : ∀ {x y : ℝ}, r ≤ x → x ≤ y → |f x - f y| ≤ L_f * (y - x) := by
      intro x y hrx hxy
      have hx0 : 0 < x := hr0.trans_le hrx
      have hy0 : 0 < y := hx0.trans_le hxy
      dsimp only [f]
      rw [if_neg (not_le.mpr hx0), if_neg (not_le.mpr hy0)]
      have hdecomp : shellAutocorr φ (r / x) / x - shellAutocorr φ (r / y) / y =
          (shellAutocorr φ (r / x) - shellAutocorr φ (r / y)) / x +
            shellAutocorr φ (r / y) * ((y - x) / (x * y)) := by
        field_simp [hx0.ne', hy0.ne']; ring
      rw [hdecomp]
      have hglip : |shellAutocorr φ (r / x) - shellAutocorr φ (r / y)| ≤
          (K_lip : ℝ) * (r * (y - x) / (x * y)) := by
        have hd := hG_lip.dist_le_mul (r / x) (r / y)
        rw [Real.dist_eq, Real.dist_eq] at hd
        have hsub_r : r / x - r / y = r * (y - x) / (x * y) := by
          field_simp [hx0.ne', hy0.ne']
        have hnn : 0 ≤ r * (y - x) / (x * y) := by
          have : 0 ≤ y - x := sub_nonneg.mpr hxy; positivity
        rwa [hsub_r, abs_of_nonneg hnn] at hd
      have hden1 : r / (x ^ 2 * y) ≤ c ^ 2 := by
        have hx2y : r ^ 3 ≤ x ^ 2 * y := by
          have hx2 : r ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hr0.le hrx 2
          calc
            r ^ 3 = r ^ 2 * r := by ring
            _ ≤ x ^ 2 * y := mul_le_mul hx2 (hrx.trans hxy) hr0.le (sq_nonneg x)
        calc
          r / (x ^ 2 * y) ≤ r / r ^ 3 := div_le_div_of_nonneg_left hr0.le (by positivity) hx2y
          _ = 1 / r ^ 2 := by field_simp [hr0.ne']
          _ ≤ c ^ 2 := hr_sq_inv
      have hden2 : 1 / (x * y) ≤ c ^ 2 := by
        have hxy_r2 : r ^ 2 ≤ x * y := by
          calc
            r ^ 2 = r * r := sq r
            _ ≤ x * y := mul_le_mul hrx (hrx.trans hxy) hr0.le hx0.le
        exact (one_div_le_one_div_of_le (by positivity) hxy_r2).trans hr_sq_inv
      have ht1 : |(shellAutocorr φ (r / x) - shellAutocorr φ (r / y)) / x| ≤
          (K_lip : ℝ) * c ^ 2 * (y - x) := by
        rw [abs_div, abs_of_pos hx0]
        calc
          |shellAutocorr φ (r / x) - shellAutocorr φ (r / y)| / x
              ≤ ((K_lip : ℝ) * (r * (y - x) / (x * y))) / x :=
            div_le_div_of_nonneg_right hglip hx0.le
          _ = (K_lip : ℝ) * (y - x) * (r / (x ^ 2 * y)) := by
            field_simp [hx0.ne', hy0.ne']
          _ ≤ (K_lip : ℝ) * (y - x) * c ^ 2 :=
            mul_le_mul_of_nonneg_left hden1
              (mul_nonneg (NNReal.coe_nonneg _) (sub_nonneg.mpr hxy))
          _ = (K_lip : ℝ) * c ^ 2 * (y - x) := by ring
      have ht2 : |shellAutocorr φ (r / y) * ((y - x) / (x * y))| ≤
          (∫ t, φ t ^ 2) * c ^ 2 * (y - x) := by
        have hnn : 0 ≤ (y - x) / (x * y) := div_nonneg (sub_nonneg.mpr hxy) (by positivity)
        rw [abs_mul, abs_of_nonneg hnn]
        calc
          |shellAutocorr φ (r / y)| * ((y - x) / (x * y))
              ≤ (∫ t, φ t ^ 2) * ((y - x) / (x * y)) :=
            mul_le_mul_of_nonneg_right (hG_le _) hnn
          _ = (∫ t, φ t ^ 2) * ((y - x) * (1 / (x * y))) := by ring
          _ ≤ (∫ t, φ t ^ 2) * ((y - x) * c ^ 2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hden2 (sub_nonneg.mpr hxy)) hM_nn
          _ = (∫ t, φ t ^ 2) * c ^ 2 * (y - x) := by ring
      calc
        _ ≤ |(shellAutocorr φ (r / x) - shellAutocorr φ (r / y)) / x| +
              |shellAutocorr φ (r / y) * ((y - x) / (x * y))| := abs_add_le _ _
        _ ≤ (K_lip : ℝ) * c ^ 2 * (y - x) + (∫ t, φ t ^ 2) * c ^ 2 * (y - x) :=
          add_le_add ht1 ht2
        _ = L_f * (y - x) := by dsimp only [L_f]; ring
    have hf_lip_le : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        dist (f x) (f y) ≤ L_f * dist x y := by
      have hord : ∀ {x y : ℝ}, x ≤ y → |f x - f y| ≤ L_f * (y - x) := by
        intro x y hxy
        rcases le_or_gt y r with hyr | hry
        · rw [hf_zero x (hxy.trans hyr), hf_zero y hyr, sub_self, abs_zero]
          exact mul_nonneg hLf0 (sub_nonneg.mpr hxy)
        · rcases le_or_gt x r with hxr | hrx
          · rw [hf_zero x hxr, ← hf_zero r le_rfl]
            exact (hf_pair_above le_rfl hry.le).trans
              (mul_le_mul_of_nonneg_left (by linarith only [hxr]) hLf0)
          · exact hf_pair_above hrx.le hxy
      intro x _ y _
      rcases le_total x y with hxy | hyx
      · rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
        exact hord hxy
      · rw [dist_comm (f x), dist_comm x, Real.dist_eq, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hyx), neg_sub]
        exact hord hyx
    let K_nn : NNReal := ⟨L_f, hLf0⟩
    have hf_lip : LipschitzOnWith K_nn f (Set.Icc 0 1) :=
      LipschitzOnWith.of_dist_le_mul fun x hx y hy => hf_lip_le x hx y hy
    have hf_cont : ContinuousOn f (Set.Icc 0 1) := hf_lip.continuousOn
    have hriem := _root_.RHTower.abs_riemannSum_sub_integral_le hf_lip hf_cont N
      (h := 1 / (N : ℝ)) (by positivity) (by rw [mul_one_div_cancel hN0.ne'])
    rw [mul_one_div_cancel hN0.ne', integral_recip_shellAutocorr_eq hφ hsupp hr0 hr1.le] at hriem
    have hsum_eq : (1 / (N : ℝ)) * (∑ i ∈ range N, f (((i : ℝ) + 1) * (1 / (N : ℝ)))) =
        ∑ n ∈ Icc 1 N, midBandLinearizedWeight φ c N h n := by
      rw [mul_sum]
      refine sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
      · intro i hi; exact mem_Icc.mpr ⟨by omega, by have := mem_range.mp hi; omega⟩
      · intro i _ j _ hij; omega
      · intro n hn
        obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
        exact ⟨n - 1, mem_range.mpr (by omega), by omega⟩
      · intro i _
        have hi1 : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) / N := by positivity
        have heq_y : ((i : ℝ) + 1) * (1 / (N : ℝ)) = ((i + 1 : ℕ) : ℝ) / N := by
          push_cast; ring
        rw [heq_y]
        dsimp only [f]
        rw [if_neg (not_le.mpr hi1)]
        unfold midBandLinearizedWeight
        dsimp only [r]
        have hi0 : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hN0.ne', hc0.ne', hi0]
    rw [hsum_eq, hsplit_Icc] at hriem
    have hriem' : |(∑ n ∈ Ioc K₀ (N - h), midBandLinearizedWeight φ c N h n) -
        ∫ u in r..1, shellAutocorr φ u / u| ≤
        (K_nn : ℝ) * N * (1 / (N : ℝ)) ^ 2 +
          |∑ n ∈ Ioc (N - h) N, midBandLinearizedWeight φ c N h n| := by
      set A := ∑ n ∈ Ioc K₀ (N - h), midBandLinearizedWeight φ c N h n
      set B_t := ∑ n ∈ Ioc (N - h) N, midBandLinearizedWeight φ c N h n
      set I := ∫ u in r..1, shellAutocorr φ u / u
      have htri := abs_sub (A + B_t - I) B_t
      have hid : A + B_t - I - B_t = A - I := by ring
      rw [hid] at htri
      linarith only [htri, hriem]
    have hknn : (K_nn : ℝ) * N * (1 / (N : ℝ)) ^ 2 =
        ((K_lip : ℝ) + ∫ t, φ t ^ 2) * c ^ 2 / N := by
      change L_f * N * (1 / (N : ℝ)) ^ 2 = _
      dsimp only [L_f]; field_simp [hN0.ne']
    rw [hknn] at hriem'
    calc
      _ ≤ ((K_lip : ℝ) + ∫ t, φ t ^ 2) * c ^ 2 / N +
            4 * Real.exp 2 * (∫ t, φ t ^ 2) * c ^ 2 / N :=
        hriem'.trans (add_le_add le_rfl htop_err)
      _ ≤ C_w * c ^ 2 / N := by
        dsimp only [C_w]
        have hpos_num : 0 ≤ c ^ 2 / (N : ℝ) := by positivity
        have heq_sum : ((K_lip : ℝ) + ∫ t, φ t ^ 2) * c ^ 2 / N +
            4 * Real.exp 2 * (∫ t, φ t ^ 2) * c ^ 2 / N =
            ((K_lip : ℝ) + (∫ t, φ t ^ 2) + 4 * Real.exp 2 * (∫ t, φ t ^ 2)) * (c ^ 2 / N) := by
          ring
        rw [heq_sum, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith only) hpos_num

/-- **Master `nearGram` mode bilinear approximation.**
On every pair of conductors `m, l ≥ 1` with `R₂ := max 2 (max m l)` satisfying `R₂^2 ≤ N` and
`18 * (1 + log R₂) ≤ log N`, the `nearGram` bilinear form on `(v_m, v_l)` equals
`(if m = l then shellCorrection φ c m / log N else 0)` up to a power-saving `O((m l)^5 * c^5 / N)`
error with zero `1 / log N` or `log c` remainder. -/
theorem exists_nearGram_mode_bilinear_approx {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C_ng : ℝ, 0 ≤ C_ng ∧
      ∀ {m l N : ℕ} {c : ℝ},
        0 < m → 0 < l →
        max 2 (max m l) * max 2 (max m l) ≤ N →
        18 * (1 + Real.log (max 2 (max m l) : ℕ)) ≤ Real.log N →
        1 ≤ c → 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        |nearGramModeBilin φ c N m l -
            (if m = l then shellCorrection φ c m / Real.log N else 0)| ≤
          C_ng * ((m : ℝ) * l) ^ 5 * (c ^ 5 / N) := by
  obtain ⟨C_2, hC2, hlag⟩ := exists_midBand_lag_sub_linearized_le hφ hsupp hM
  obtain ⟨C_4, hC4, hosc⟩ := exists_midBand_osc_sum_le hφ hsupp hM
  obtain ⟨C_w, hCw, hwgt⟩ := exists_sum_midBandLinearizedWeight_sub_shellIntegral_le hφ hsupp
  let C_ng : ℝ := (64 * C_2 + 1024 * C_4 + 4 * Real.exp 2 * C_w) / (∫ u, φ u ^ 2) + 1
  refine ⟨C_ng, by dsimp only [C_ng]; positivity, ?_⟩
  intro m l N c hm hl hR2N hlog18 hc1 hradN
  let R₂ := max 2 (max m l)
  have hR₂2 : 2 ≤ R₂ := le_max_left 2 _
  have hmR₂ : m ∈ Icc 1 R₂ := mem_Icc.mpr ⟨hm, (le_max_left m l).trans (le_max_right 2 _)⟩
  have hlR₂ : l ∈ Icc 1 R₂ := mem_Icc.mpr ⟨hl, (le_max_right m l).trans (le_max_right 2 _)⟩
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N :=
    (by norm_num : 1 ≤ 2 * 2).trans ((Nat.mul_le_mul (le_max_left 2 _) (le_max_left 2 _)).trans hR2N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL1 : 1 ≤ Real.log (N : ℝ) := by
    have hlogR : 0 ≤ Real.log (R₂ : ℝ) := Real.log_natCast_nonneg R₂
    linarith only [hlog18, hlogR]
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hw1 : c / N ≤ 1 := by
    have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
    have hcR : c ≤ linearNearRowRadius c := by
      unfold linearNearRowRadius
      have he2 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
      nlinarith only [hc0, he2]
    have hcN : c ≤ N := by nlinarith only [hcR, h0, hradN]
    exact (div_le_one hN0).mpr hcN
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hl1R : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hml1 : 1 ≤ (m : ℝ) * l := one_le_mul_of_one_le_of_one_le hm1R hl1R
  have hR2_le : (R₂ : ℝ) ≤ 2 * ((m : ℝ) * l) := by
    dsimp only [R₂]
    rw [Nat.cast_max, Nat.cast_max, Nat.cast_ofNat]
    refine max_le (by linarith only [hml1]) (max_le ?_ ?_)
    · nlinarith only [hm1R, hl1R]
    · nlinarith only [hm1R, hl1R]
  have hR2_4 : (R₂ : ℝ) ^ 4 ≤ 16 * ((m : ℝ) * l) ^ 4 := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg R₂) hR2_le 4
    exact h.trans_eq (by ring)
  have hvm_sq : ‖normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ 4 * (m : ℝ) := by
    have h := norm_normalizedRamanujanHorizonVector_le_two_sqrt hm hL1
    have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
    rwa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m), show (2 : ℝ) ^ 2 = 4 by norm_num] at hsq
  have hvl_sq : ‖normalizedRamanujanHorizonVector l N‖ ^ 2 ≤ 4 * (l : ℝ) := by
    have h := norm_normalizedRamanujanHorizonVector_le_two_sqrt hl hL1
    have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
    rwa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg l), show (2 : ℝ) ^ 2 = 4 by norm_num] at hsq
  by_cases hml : m = l
  · -- Diagonal case `m = l`.
    subst hml
    rw [if_pos rfl]
    let a : ℕ → ℝ := fun k => if k = m then 1 else 0
    have hvec_a : (∑ k ∈ Icc 1 R₂, a k • normalizedRamanujanHorizonVector k N) =
        normalizedRamanujanHorizonVector m N := by
      have hpt : ∀ k ∈ Icc 1 R₂, a k • normalizedRamanujanHorizonVector k N =
          if k = m then normalizedRamanujanHorizonVector m N else 0 := by
        intro k _
        dsimp only [a]
        by_cases hkm : k = m
        · subst hkm; simp
        · rw [if_neg hkm, if_neg hkm, zero_smul]
      rw [sum_congr rfl hpt, sum_ite_eq', if_pos hmR₂]
    have hlead := midBand_leadKernel_sum_eq (R₂ := R₂) hφ hsupp hL0 hc0 hw1 hradN a
    rw [hvec_a, ← nearGram_quad_eq_leadKernel hM c N (normalizedRamanujanHorizonVector m N)] at hlead
    change (∫ t, φ t ^ 2) * nearGramModeBilin φ c N m m =
      (Real.log N)⁻¹ * (2 * midBandLagSum φ R₂ N c a) at hlead
    -- Identify `midBandMeanSum` on `a` and compare with `(∫ φ^2 / 2) * shellCorrection φ c m`.
    have hmean_a : midBandMeanSum φ R₂ N c a =
        ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
          (ramanujanLagCoefficient m h / (m.totient : ℝ)) *
            ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
              midBandLinearizedWeight φ c N h n := by
      unfold midBandMeanSum
      refine sum_congr rfl fun h _ => ?_
      have hpt : ∀ k ∈ Icc 1 R₂,
          a k ^ 2 * (ramanujanLagCoefficient k h / (k.totient : ℝ)) *
            (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
              midBandLinearizedWeight φ c N h n) =
          if k = m then
            (ramanujanLagCoefficient m h / (m.totient : ℝ)) *
              ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
                midBandLinearizedWeight φ c N h n
          else 0 := by
        intro k _
        dsimp only [a]
        by_cases hkm : k = m
        · subst hkm; rw [if_pos rfl, if_pos rfl, one_pow, one_mul]
        · rw [if_neg hkm, if_neg hkm, zero_pow (by decide), zero_mul, zero_mul]
      rw [sum_congr rfl hpt, sum_ite_eq', if_pos hmR₂]
    have hceil_le_B : ⌈c⌉₊ - 1 ≤ ⌊linearNearRowRadius c⌋₊ := by
      have hceil_lt : (⌈c⌉₊ : ℝ) < c + 1 := Nat.ceil_lt_add_one hc0.le
      have h2c_Rc : c + 1 ≤ linearNearRowRadius c := by
        unfold linearNearRowRadius
        have he2 : 2 ≤ Real.exp 2 := by
          have := Real.add_one_le_exp (2 : ℝ); linarith
        nlinarith only [hc1, he2]
      have h1 : ((⌈c⌉₊ - 1 : ℕ) : ℝ) ≤ linearNearRowRadius c := by
        rcases Nat.eq_zero_or_pos ⌈c⌉₊ with hz | hp
        · simp [hz]; unfold linearNearRowRadius; positivity
        · rw [Nat.cast_sub hp, Nat.cast_one]; linarith only [hceil_lt, h2c_Rc]
      exact Nat.le_floor h1
    have hshell_eq : (∫ t, φ t ^ 2) * shellCorrection φ c m =
        2 * ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
          (ramanujanLagCoefficient m h / (m.totient : ℝ)) *
            ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u := by
      have htot0 : (m.totient : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr hm).ne'
      have hsub_sum : (∑ h ∈ Ico 1 ⌈c⌉₊, ramanujanLagCoefficient m h *
            ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u) =
          ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, ramanujanLagCoefficient m h *
            ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u := by
        refine sum_subset (fun h hh => ?_) (fun h hh hnot => ?_)
        · obtain ⟨hh1, hhc⟩ := mem_Ico.mp hh
          exact mem_Icc.mpr ⟨hh1, (by omega : h ≤ ⌈c⌉₊ - 1).trans hceil_le_B⟩
        · rw [mem_Ico] at hnot
          have hh1 := (mem_Icc.mp hh).1
          have hch : ⌈c⌉₊ ≤ h := by omega
          have h1 : 1 ≤ (h : ℝ) / c :=
            (one_le_div hc0).mpr ((Nat.le_ceil c).trans (by exact_mod_cast hch))
          rw [integral_shellAutocorr_div_eq_zero hφ hsupp h1, mul_zero]
      unfold shellCorrection
      have hM0 : (∫ t, φ t ^ 2) ≠ 0 := hM.ne'
      rw [hsub_sum, ← mul_assoc, mul_sum, mul_sum]
      refine sum_congr rfl fun h _ => ?_
      field_simp [hM0, htot0]
    have hmean_diff : |2 * midBandMeanSum φ R₂ N c a - (∫ t, φ t ^ 2) * shellCorrection φ c m| ≤
        4 * Real.exp 2 * C_w * c ^ 3 / N := by
      rw [hmean_a, hshell_eq, ← mul_sub, ← sum_sub_distrib, abs_mul, abs_of_pos zero_lt_two]
      have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
      have hpt : ∀ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
          |(ramanujanLagCoefficient m h / (m.totient : ℝ)) *
              (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
                midBandLinearizedWeight φ c N h n) -
            (ramanujanLagCoefficient m h / (m.totient : ℝ)) *
              ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| ≤ C_w * c ^ 2 / N := by
        intro h hh
        rw [← mul_sub, abs_mul]
        have hlag_le : |ramanujanLagCoefficient m h / (m.totient : ℝ)| ≤ 1 := by
          rw [abs_div, abs_of_pos htot_pos, div_le_one htot_pos]
          exact BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m h
        simpa only [one_mul] using
          mul_le_mul hlag_le (hwgt hc1 hradN h hh) (abs_nonneg _) zero_le_one
      have hB_le : (⌊linearNearRowRadius c⌋₊ : ℝ) ≤ 2 * Real.exp 2 * c :=
        (Nat.floor_le (by unfold linearNearRowRadius; positivity)).trans_eq
          (by unfold linearNearRowRadius; ring)
      calc
        2 * |∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, _|
            ≤ 2 * ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, (C_w * c ^ 2 / N) :=
          mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)) zero_le_two
        _ = 2 * ((⌊linearNearRowRadius c⌋₊ : ℝ) * (C_w * c ^ 2 / N)) := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        _ ≤ 2 * ((2 * Real.exp 2 * c) * (C_w * c ^ 2 / N)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB_le (by positivity)) zero_le_two
        _ = 4 * Real.exp 2 * C_w * c ^ 3 / N := by ring
    have hlag_a := hlag hL0 hc1 hradN a
    have hosc_a := hosc hR₂2 hR2N hlog18 hc1 hradN a
    rw [hvec_a] at hlag_a hosc_a
    have hlag_b : |2 * (midBandLagSum φ R₂ N c a - midBandLinearizedSum φ R₂ N c a)| ≤
        8 * C_2 * (m : ℝ) * (c ^ 5 * Real.log N / N) := by
      rw [abs_mul, abs_of_pos zero_lt_two]
      calc
        2 * |midBandLagSum φ R₂ N c a - midBandLinearizedSum φ R₂ N c a|
            ≤ 2 * (C_2 * (c ^ 5 * Real.log N / N) * ‖normalizedRamanujanHorizonVector m N‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hlag_a zero_le_two
        _ ≤ 2 * (C_2 * (c ^ 5 * Real.log N / N) * (4 * (m : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvm_sq (by positivity)) zero_le_two
        _ = 8 * C_2 * (m : ℝ) * (c ^ 5 * Real.log N / N) := by ring
    have hosc_b : |2 * midBandOscSum φ R₂ N c a| ≤
        128 * C_4 * ((m : ℝ) * m) ^ 5 * (c ^ 3 / N) := by
      rw [abs_mul, abs_of_pos zero_lt_two]
      have hm_le_m2 : (m : ℝ) ≤ (m : ℝ) * m := le_mul_of_one_le_right (by positivity) hm1R
      calc
        2 * |midBandOscSum φ R₂ N c a|
            ≤ 2 * (C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N) * (4 * (m : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (hosc_a.trans (mul_le_mul_of_nonneg_left hvm_sq (by positivity))) zero_le_two
        _ = 8 * C_4 * ((R₂ : ℝ) ^ 4 * (m : ℝ)) * (c ^ 3 / N) := by ring
        _ ≤ 8 * C_4 * ((16 * ((m : ℝ) * m) ^ 4) * ((m : ℝ) * m)) * (c ^ 3 / N) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_le_mul hR2_4 hm_le_m2 (by positivity) (by positivity))
              (by positivity)) (by positivity)
        _ = 128 * C_4 * ((m : ℝ) * m) ^ 5 * (c ^ 3 / N) := by ring
    have hid_diag : (∫ t, φ t ^ 2) * Real.log N *
        (nearGramModeBilin φ c N m m - shellCorrection φ c m / Real.log N) =
        2 * (midBandLagSum φ R₂ N c a - midBandLinearizedSum φ R₂ N c a) +
          (2 * midBandMeanSum φ R₂ N c a - (∫ t, φ t ^ 2) * shellCorrection φ c m) +
          2 * midBandOscSum φ R₂ N c a := by
      rw [midBandLinearizedSum_eq_mean_add_osc]
      have hlead' : (∫ t, φ t ^ 2) * Real.log N * nearGramModeBilin φ c N m m =
          2 * midBandLagSum φ R₂ N c a := by
        have := congrArg (fun x => Real.log (N : ℝ) * x) hlead
        dsimp only at this
        rw [← mul_assoc, mul_inv_cancel₀ hL0.ne', one_mul] at this
        linarith only [this, (by ring : Real.log (N : ℝ) * ((∫ t, φ t ^ 2) * nearGramModeBilin φ c N m m) =
          (∫ t, φ t ^ 2) * Real.log N * nearGramModeBilin φ c N m m)]
      have hsc' : (∫ t, φ t ^ 2) * Real.log N * (shellCorrection φ c m / Real.log N) =
          (∫ t, φ t ^ 2) * shellCorrection φ c m := by
        field_simp [hL0.ne']
      rw [mul_sub, hlead', hsc']; ring
    have htot_num : |(∫ t, φ t ^ 2) * Real.log N *
        (nearGramModeBilin φ c N m m - shellCorrection φ c m / Real.log N)| ≤
        (64 * C_2 + 1024 * C_4 + 4 * Real.exp 2 * C_w) *
          ((m : ℝ) * m) ^ 5 * (c ^ 5 * Real.log N / N) := by
      rw [hid_diag]
      have htri := abs_add_three
        (2 * (midBandLagSum φ R₂ N c a - midBandLinearizedSum φ R₂ N c a))
        (2 * midBandMeanSum φ R₂ N c a - (∫ t, φ t ^ 2) * shellCorrection φ c m)
        (2 * midBandOscSum φ R₂ N c a)
      have hc35 : c ^ 3 / N ≤ c ^ 5 * Real.log N / N := by
        apply div_le_div_of_nonneg_right _ hN0.le
        exact (pow_le_pow_right₀ hc1 (by norm_num : 3 ≤ 5)).trans
          (le_mul_of_one_le_right (by positivity) hL1)
      have hm_le5 : (m : ℝ) ≤ ((m : ℝ) * m) ^ 5 := by
        have h1 : (m : ℝ) ≤ (m : ℝ) * m := le_mul_of_one_le_right (by positivity) hm1R
        exact h1.trans (le_self_pow₀ hml1 (by decide))
      have h1 : 8 * C_2 * (m : ℝ) * (c ^ 5 * Real.log N / N) ≤
          64 * C_2 * ((m : ℝ) * m) ^ 5 * (c ^ 5 * Real.log N / N) := by
        have hcoef : 8 * C_2 ≤ 64 * C_2 := by linarith only [hC2]
        exact mul_le_mul_of_nonneg_right (mul_le_mul hcoef hm_le5 (by positivity) (by positivity))
          (by positivity)
      have h2 : 4 * Real.exp 2 * C_w * c ^ 3 / N ≤
          4 * Real.exp 2 * C_w * ((m : ℝ) * m) ^ 5 * (c ^ 5 * Real.log N / N) := by
        have hm5_1 : 1 ≤ ((m : ℝ) * m) ^ 5 := one_le_pow₀ hml1
        calc
          4 * Real.exp 2 * C_w * c ^ 3 / N = 4 * Real.exp 2 * C_w * 1 * (c ^ 3 / N) := by ring
          _ ≤ 4 * Real.exp 2 * C_w * ((m : ℝ) * m) ^ 5 * (c ^ 5 * Real.log N / N) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hm5_1 (by positivity)) hc35
              (by positivity) (by positivity)
      have h3 : 128 * C_4 * ((m : ℝ) * m) ^ 5 * (c ^ 3 / N) ≤
          1024 * C_4 * ((m : ℝ) * m) ^ 5 * (c ^ 5 * Real.log N / N) := by
        have hcoef : 128 * C_4 ≤ 1024 * C_4 := by linarith only [hC4]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hcoef (by positivity)) hc35 (by positivity) (by positivity)
      linarith only [htri, hlag_b, hmean_diff, hosc_b, h1, h2, h3,
        (by ring : 64 * C_2 * ((m : ℝ) * m) ^ 5 * (c ^ 5 * Real.log N / N) +
          4 * Real.exp 2 * C_w * ((m : ℝ) * m) ^ 5 * (c ^ 5 * Real.log N / N) +
          1024 * C_4 * ((m : ℝ) * m) ^ 5 * (c ^ 5 * Real.log N / N) =
          (64 * C_2 + 1024 * C_4 + 4 * Real.exp 2 * C_w) * ((m : ℝ) * m) ^ 5 *
            (c ^ 5 * Real.log N / N))]
    rw [abs_mul, abs_of_pos (mul_pos hM hL0)] at htot_num
    have hdiv := (le_div_iff₀' (mul_pos hM hL0)).mpr htot_num
    refine hdiv.trans ?_
    have hsimp : (64 * C_2 + 1024 * C_4 + 4 * Real.exp 2 * C_w) * ((m : ℝ) * m) ^ 5 *
        (c ^ 5 * Real.log N / N) / ((∫ u, φ u ^ 2) * Real.log N) =
        ((64 * C_2 + 1024 * C_4 + 4 * Real.exp 2 * C_w) / (∫ u, φ u ^ 2)) *
          ((m : ℝ) * m) ^ 5 * (c ^ 5 / N) := by
      field_simp [hM.ne', hL0.ne']
    rw [hsimp]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp only [C_ng]; linarith only) (by positivity))
      (by positivity)
  · -- Off-diagonal case `m ≠ l`: polarization annihilates `midBandMeanSum` identically.
    rw [if_neg hml, sub_zero]
    let a_p : ℕ → ℝ := fun k => (if k = m then 1 else 0) + (if k = l then 1 else 0)
    let a_m : ℕ → ℝ := fun k => (if k = m then 1 else 0) - (if k = l then 1 else 0)
    have hvec_p : (∑ k ∈ Icc 1 R₂, a_p k • normalizedRamanujanHorizonVector k N) =
        normalizedRamanujanHorizonVector m N + normalizedRamanujanHorizonVector l N := by
      dsimp only [a_p]
      simp only [add_smul, sum_add_distrib]
      congr 1
      · have hpt : ∀ k ∈ Icc 1 R₂, (if k = m then (1 : ℝ) else 0) •
            normalizedRamanujanHorizonVector k N =
            if k = m then normalizedRamanujanHorizonVector m N else 0 := by
          intro k _; by_cases hkm : k = m <;> simp [hkm]
        rw [sum_congr rfl hpt, sum_ite_eq', if_pos hmR₂]
      · have hpt : ∀ k ∈ Icc 1 R₂, (if k = l then (1 : ℝ) else 0) •
            normalizedRamanujanHorizonVector k N =
            if k = l then normalizedRamanujanHorizonVector l N else 0 := by
          intro k _; by_cases hkl : k = l <;> simp [hkl]
        rw [sum_congr rfl hpt, sum_ite_eq', if_pos hlR₂]
    have hvec_m : (∑ k ∈ Icc 1 R₂, a_m k • normalizedRamanujanHorizonVector k N) =
        normalizedRamanujanHorizonVector m N - normalizedRamanujanHorizonVector l N := by
      dsimp only [a_m]
      simp only [sub_smul, sum_sub_distrib]
      congr 1
      · have hpt : ∀ k ∈ Icc 1 R₂, (if k = m then (1 : ℝ) else 0) •
            normalizedRamanujanHorizonVector k N =
            if k = m then normalizedRamanujanHorizonVector m N else 0 := by
          intro k _; by_cases hkm : k = m <;> simp [hkm]
        rw [sum_congr rfl hpt, sum_ite_eq', if_pos hmR₂]
      · have hpt : ∀ k ∈ Icc 1 R₂, (if k = l then (1 : ℝ) else 0) •
            normalizedRamanujanHorizonVector k N =
            if k = l then normalizedRamanujanHorizonVector l N else 0 := by
          intro k _; by_cases hkl : k = l <;> simp [hkl]
        rw [sum_congr rfl hpt, sum_ite_eq', if_pos hlR₂]
    have hsq_eq : ∀ k : ℕ, a_p k ^ 2 = a_m k ^ 2 := by
      intro k
      dsimp only [a_p, a_m]
      by_cases hkm : k = m
      · subst hkm; rw [if_pos rfl, if_neg hml]; norm_num
      · by_cases hkl : k = l
        · subst hkl; rw [if_neg (Ne.symm hml), if_pos rfl]; norm_num
        · rw [if_neg hkm, if_neg hkl]; norm_num
    have hmean_eq : midBandMeanSum φ R₂ N c a_p = midBandMeanSum φ R₂ N c a_m := by
      unfold midBandMeanSum
      exact sum_congr rfl fun h _ => sum_congr rfl fun k _ => by rw [hsq_eq k]
    -- Polarization of `nearGram`.
    let v_m := normalizedRamanujanHorizonVector m N
    let v_l := normalizedRamanujanHorizonVector l N
    have hpol : (∑ n ∈ Icc 1 N, primeHorizonExtension (v_m + v_l) n *
          nearGram φ c N (primeHorizonExtension (v_m + v_l)) n) -
        (∑ n ∈ Icc 1 N, primeHorizonExtension (v_m - v_l) n *
          nearGram φ c N (primeHorizonExtension (v_m - v_l)) n) =
        4 * nearGramModeBilin φ c N m l := by
      have hlin_ext : ∀ u v : EuclideanSpace ℝ (PrimeHorizonIndex N), ∀ n ∈ Icc 1 N,
          primeHorizonExtension (u + v) n = primeHorizonExtension u n + primeHorizonExtension v n ∧
          primeHorizonExtension (u - v) n = primeHorizonExtension u n - primeHorizonExtension v n := by
        intro u v n hn
        rw [primeHorizonExtension_coe _ ⟨n, hn⟩, primeHorizonExtension_coe _ ⟨n, hn⟩,
          primeHorizonExtension_coe _ ⟨n, hn⟩, primeHorizonExtension_coe _ ⟨n, hn⟩]
        exact ⟨rfl, rfl⟩
      have hng_add : ∀ u v : EuclideanSpace ℝ (PrimeHorizonIndex N), ∀ n ∈ Icc 1 N,
          nearGram φ c N (primeHorizonExtension (u + v)) n =
            nearGram φ c N (primeHorizonExtension u) n +
              nearGram φ c N (primeHorizonExtension v) n := by
        intro u v n _
        unfold nearGram
        rw [← sum_add_distrib]
        refine sum_congr rfl fun j hj => ?_
        have hjN := (mem_filter.mp hj).1
        rw [(hlin_ext u v j hjN).1]; ring
      have hng_sub : ∀ u v : EuclideanSpace ℝ (PrimeHorizonIndex N), ∀ n ∈ Icc 1 N,
          nearGram φ c N (primeHorizonExtension (u - v)) n =
            nearGram φ c N (primeHorizonExtension u) n -
              nearGram φ c N (primeHorizonExtension v) n := by
        intro u v n _
        unfold nearGram
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun j hj => ?_
        have hjN := (mem_filter.mp hj).1
        rw [(hlin_ext u v j hjN).2]; ring
      have hdiff_pt : ∀ n ∈ Icc 1 N,
          primeHorizonExtension (v_m + v_l) n * nearGram φ c N (primeHorizonExtension (v_m + v_l)) n -
            primeHorizonExtension (v_m - v_l) n * nearGram φ c N (primeHorizonExtension (v_m - v_l)) n =
          2 * (primeHorizonExtension v_m n * nearGram φ c N (primeHorizonExtension v_l) n) +
            2 * (primeHorizonExtension v_l n * nearGram φ c N (primeHorizonExtension v_m) n) := by
        intro n hn
        rw [(hlin_ext v_m v_l n hn).1, (hlin_ext v_m v_l n hn).2,
          hng_add v_m v_l n hn, hng_sub v_m v_l n hn]
        ring
      rw [← sum_sub_distrib, sum_congr rfl hdiff_pt, sum_add_distrib, ← mul_sum, ← mul_sum,
        nearGram_bilinear_symm φ c N (primeHorizonExtension v_l) (primeHorizonExtension v_m)]
      unfold nearGramModeBilin
      dsimp only [v_m, v_l]; ring
    have hlead_p := midBand_leadKernel_sum_eq (R₂ := R₂) hφ hsupp hL0 hc0 hw1 hradN a_p
    have hlead_m := midBand_leadKernel_sum_eq (R₂ := R₂) hφ hsupp hL0 hc0 hw1 hradN a_m
    rw [hvec_p, ← nearGram_quad_eq_leadKernel hM c N (v_m + v_l)] at hlead_p
    rw [hvec_m, ← nearGram_quad_eq_leadKernel hM c N (v_m - v_l)] at hlead_m
    have hid_off : 4 * (∫ t, φ t ^ 2) * Real.log N * nearGramModeBilin φ c N m l =
        2 * (midBandLagSum φ R₂ N c a_p - midBandLinearizedSum φ R₂ N c a_p) -
          2 * (midBandLagSum φ R₂ N c a_m - midBandLinearizedSum φ R₂ N c a_m) +
          2 * midBandOscSum φ R₂ N c a_p - 2 * midBandOscSum φ R₂ N c a_m := by
      have hp_eq : (∫ t, φ t ^ 2) * Real.log N *
          (∑ n ∈ Icc 1 N, primeHorizonExtension (v_m + v_l) n *
            nearGram φ c N (primeHorizonExtension (v_m + v_l)) n) =
          2 * midBandLagSum φ R₂ N c a_p := by
        have := congrArg (fun x => Real.log (N : ℝ) * x) hlead_p
        dsimp only at this
        rw [← mul_assoc (Real.log (N : ℝ)) (Real.log (N : ℝ))⁻¹,
          mul_inv_cancel₀ hL0.ne', one_mul] at this
        linarith only [this, (by ring : Real.log (N : ℝ) * ((∫ t, φ t ^ 2) *
          ∑ n ∈ Icc 1 N, primeHorizonExtension (v_m + v_l) n *
            nearGram φ c N (primeHorizonExtension (v_m + v_l)) n) =
          (∫ t, φ t ^ 2) * Real.log N *
            ∑ n ∈ Icc 1 N, primeHorizonExtension (v_m + v_l) n *
              nearGram φ c N (primeHorizonExtension (v_m + v_l)) n)]
      have hm_eq : (∫ t, φ t ^ 2) * Real.log N *
          (∑ n ∈ Icc 1 N, primeHorizonExtension (v_m - v_l) n *
            nearGram φ c N (primeHorizonExtension (v_m - v_l)) n) =
          2 * midBandLagSum φ R₂ N c a_m := by
        have := congrArg (fun x => Real.log (N : ℝ) * x) hlead_m
        dsimp only at this
        rw [← mul_assoc (Real.log (N : ℝ)) (Real.log (N : ℝ))⁻¹,
          mul_inv_cancel₀ hL0.ne', one_mul] at this
        linarith only [this, (by ring : Real.log (N : ℝ) * ((∫ t, φ t ^ 2) *
          ∑ n ∈ Icc 1 N, primeHorizonExtension (v_m - v_l) n *
            nearGram φ c N (primeHorizonExtension (v_m - v_l)) n) =
          (∫ t, φ t ^ 2) * Real.log N *
            ∑ n ∈ Icc 1 N, primeHorizonExtension (v_m - v_l) n *
              nearGram φ c N (primeHorizonExtension (v_m - v_l)) n)]
      have hsub := congrArg (((∫ t, φ t ^ 2) * Real.log N) * ·) hpol
      change (∫ t, φ t ^ 2) * Real.log N *
          ((∑ n ∈ Icc 1 N, primeHorizonExtension (v_m + v_l) n *
              nearGram φ c N (primeHorizonExtension (v_m + v_l)) n) -
            ∑ n ∈ Icc 1 N, primeHorizonExtension (v_m - v_l) n *
              nearGram φ c N (primeHorizonExtension (v_m - v_l)) n) =
          (∫ t, φ t ^ 2) * Real.log N * (4 * nearGramModeBilin φ c N m l) at hsub
      rw [mul_sub, hp_eq, hm_eq] at hsub
      rw [midBandLinearizedSum_eq_mean_add_osc φ R₂ N c a_p,
        midBandLinearizedSum_eq_mean_add_osc φ R₂ N c a_m, hmean_eq]
      linarith only [hsub, (by ring : (∫ t, φ t ^ 2) * Real.log N * (4 * nearGramModeBilin φ c N m l) =
        4 * (∫ t, φ t ^ 2) * Real.log N * nearGramModeBilin φ c N m l)]
    have hnorm_p : ‖v_m + v_l‖ ^ 2 ≤ 16 * ((m : ℝ) * l) := by
      have htri := norm_add_le v_m v_l
      have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
      have h2 : ‖v_m + v_l‖ ^ 2 ≤ 2 * (‖v_m‖ ^ 2 + ‖v_l‖ ^ 2) := by
        nlinarith only [hsq, sq_nonneg (‖v_m‖ - ‖v_l‖)]
      have hml_sum : (m : ℝ) + l ≤ 2 * ((m : ℝ) * l) := by nlinarith only [hm1R, hl1R]
      nlinarith only [h2, hvm_sq, hvl_sq, hml_sum]
    have hnorm_m : ‖v_m - v_l‖ ^ 2 ≤ 16 * ((m : ℝ) * l) := by
      have htri := norm_sub_le v_m v_l
      have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
      have h2 : ‖v_m - v_l‖ ^ 2 ≤ 2 * (‖v_m‖ ^ 2 + ‖v_l‖ ^ 2) := by
        nlinarith only [hsq, sq_nonneg (‖v_m‖ - ‖v_l‖)]
      have hml_sum : (m : ℝ) + l ≤ 2 * ((m : ℝ) * l) := by nlinarith only [hm1R, hl1R]
      nlinarith only [h2, hvm_sq, hvl_sq, hml_sum]
    have hlag_p := hlag hL0 hc1 hradN a_p
    have hlag_m := hlag hL0 hc1 hradN a_m
    have hosc_p := hosc hR₂2 hR2N hlog18 hc1 hradN a_p
    have hosc_m := hosc hR₂2 hR2N hlog18 hc1 hradN a_m
    rw [hvec_p] at hlag_p hosc_p
    rw [hvec_m] at hlag_m hosc_m
    have hml5 : (m : ℝ) * l ≤ ((m : ℝ) * l) ^ 5 := le_self_pow₀ hml1 (by decide)
    have hc35 : c ^ 3 / N ≤ c ^ 5 * Real.log N / N := by
      apply div_le_div_of_nonneg_right _ hN0.le
      exact (pow_le_pow_right₀ hc1 (by norm_num : 3 ≤ 5)).trans
        (le_mul_of_one_le_right (by positivity) hL1)
    have hb_lp : |midBandLagSum φ R₂ N c a_p - midBandLinearizedSum φ R₂ N c a_p| ≤
        16 * C_2 * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by
      calc
        _ ≤ C_2 * (c ^ 5 * Real.log N / N) * (16 * ((m : ℝ) * l)) :=
          hlag_p.trans (mul_le_mul_of_nonneg_left hnorm_p (by positivity))
        _ = 16 * C_2 * ((m : ℝ) * l) * (c ^ 5 * Real.log N / N) := by ring
        _ ≤ 16 * C_2 * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hml5 (by positivity)) (by positivity)
    have hb_lm : |midBandLagSum φ R₂ N c a_m - midBandLinearizedSum φ R₂ N c a_m| ≤
        16 * C_2 * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by
      calc
        _ ≤ C_2 * (c ^ 5 * Real.log N / N) * (16 * ((m : ℝ) * l)) :=
          hlag_m.trans (mul_le_mul_of_nonneg_left hnorm_m (by positivity))
        _ = 16 * C_2 * ((m : ℝ) * l) * (c ^ 5 * Real.log N / N) := by ring
        _ ≤ 16 * C_2 * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hml5 (by positivity)) (by positivity)
    have hb_op : |midBandOscSum φ R₂ N c a_p| ≤
        256 * C_4 * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by
      calc
        _ ≤ C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N) * (16 * ((m : ℝ) * l)) :=
          hosc_p.trans (mul_le_mul_of_nonneg_left hnorm_p (by positivity))
        _ = 16 * C_4 * ((R₂ : ℝ) ^ 4 * ((m : ℝ) * l)) * (c ^ 3 / N) := by ring
        _ ≤ 16 * C_4 * ((16 * ((m : ℝ) * l) ^ 4) * ((m : ℝ) * l)) * (c ^ 5 * Real.log N / N) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hR2_4 (by positivity)) (by positivity))
            hc35 (by positivity) (by positivity)
        _ = 256 * C_4 * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by ring
    have hb_om : |midBandOscSum φ R₂ N c a_m| ≤
        256 * C_4 * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by
      calc
        _ ≤ C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N) * (16 * ((m : ℝ) * l)) :=
          hosc_m.trans (mul_le_mul_of_nonneg_left hnorm_m (by positivity))
        _ = 16 * C_4 * ((R₂ : ℝ) ^ 4 * ((m : ℝ) * l)) * (c ^ 3 / N) := by ring
        _ ≤ 16 * C_4 * ((16 * ((m : ℝ) * l) ^ 4) * ((m : ℝ) * l)) * (c ^ 5 * Real.log N / N) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hR2_4 (by positivity)) (by positivity))
            hc35 (by positivity) (by positivity)
        _ = 256 * C_4 * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by ring
    have h4_abs : |4 * (∫ t, φ t ^ 2) * Real.log N * nearGramModeBilin φ c N m l| ≤
        4 * (64 * C_2 + 1024 * C_4 + 4 * Real.exp 2 * C_w) *
          ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by
      rw [hid_off]
      set X₁ := midBandLagSum φ R₂ N c a_p - midBandLinearizedSum φ R₂ N c a_p
      set X₂ := midBandLagSum φ R₂ N c a_m - midBandLinearizedSum φ R₂ N c a_m
      set Y₁ := midBandOscSum φ R₂ N c a_p
      set Y₂ := midBandOscSum φ R₂ N c a_m
      have ht1 := abs_sub (2 * X₁ - 2 * X₂ + 2 * Y₁) (2 * Y₂)
      have ht2 := abs_add_le (2 * X₁ - 2 * X₂) (2 * Y₁)
      have ht3 := abs_sub (2 * X₁) (2 * X₂)
      simp only [abs_mul, Nat.abs_ofNat] at ht1 ht2 ht3
      have hcw0 : 0 ≤ 4 * Real.exp 2 * C_w * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by
        positivity
      have hc2_0 : 0 ≤ C_2 * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by positivity
      have hc4_0 : 0 ≤ C_4 * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by positivity
      linarith only [ht1, ht2, ht3, hb_lp, hb_lm, hb_op, hb_om, hcw0, hc2_0, hc4_0,
        (by ring : 4 * (64 * C_2 + 1024 * C_4 + 4 * Real.exp 2 * C_w) *
          ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) =
          64 * (C_2 * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N)) +
          192 * (C_2 * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N)) +
          1024 * (C_4 * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N)) +
          3072 * (C_4 * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N)) +
          4 * (4 * Real.exp 2 * C_w * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N)))]
    rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * (∫ t, φ t ^ 2) * Real.log N)] at h4_abs
    have hdiv := (le_div_iff₀' (by positivity : 0 < 4 * (∫ t, φ t ^ 2) * Real.log N)).mpr h4_abs
    refine hdiv.trans ?_
    have hsimp : 4 * (64 * C_2 + 1024 * C_4 + 4 * Real.exp 2 * C_w) *
        ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) / (4 * (∫ t, φ t ^ 2) * Real.log N) =
        ((64 * C_2 + 1024 * C_4 + 4 * Real.exp 2 * C_w) / (∫ u, φ u ^ 2)) *
          ((m : ℝ) * l) ^ 5 * (c ^ 5 / N) := by
      field_simp [hM.ne', hL0.ne']
    rw [hsimp]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp only [C_ng]; linarith only) (by positivity))
      (by positivity)

private noncomputable def nearShellLogRow (φ : ℝ → ℝ) (c : ℝ) (N l n : ℕ) : ℝ :=
  ∑ j ∈ nearRowIndices c N n,
    shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
      (Real.log N - Real.log j) * normalizedRamanujanMode l j / Real.sqrt j

private noncomputable def nearShellJetRow (φ : ℝ → ℝ) (c : ℝ) (N l n : ℕ) : ℝ :=
  ∑ j ∈ nearRowIndices c N n,
    shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
      ((Real.sqrt (l.totient : ℝ))⁻¹ * ramanujanLogDivisorJet l j) / Real.sqrt j

private lemma nearRowIndices_card_and_pointwise {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} {N n : ℕ}
    (hc0 : 0 < c) (hN0 : (0 : ℝ) < N) (hw1 : c / N ≤ 1) (hn : n ∈ Icc 1 N) :
    ((nearRowIndices c N n).card : ℝ) ≤ 2 * (n : ℝ) * (linearNearRowRadius c / N) ∧
    ∀ j ∈ nearRowIndices c N n,
      1 / Real.sqrt j ≤ Real.exp 1 / Real.sqrt n ∧
      |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)| ≤ 1 ∧
      0 ≤ Real.log N - Real.log j ∧
      Real.log N - Real.log j ≤ 2 + Real.log ((N : ℝ) / n) := by
  have he_gap : Real.exp (2 * c / N) - 1 ≤ linearNearRowRadius c / N := by
    calc
      Real.exp (2 * c / N) - 1 ≤ 2 * c / N * Real.exp (2 * c / N) := exp_sub_one_le_mul_exp
      _ ≤ 2 * c / N * Real.exp 2 :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by
            have h := mul_le_mul_of_nonneg_left hw1 zero_le_two
            simpa only [mul_div_assoc, mul_one] using h)) (by positivity)
      _ = linearNearRowRadius c / N := by unfold linearNearRowRadius; ring
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hR0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
  have hrad0 : 0 ≤ (n : ℝ) * (linearNearRowRadius c / N) := by positivity
  have hcard_n : ((nearRowIndices c N n).card : ℝ) ≤ 2 * (n : ℝ) * (linearNearRowRadius c / N) := by
    have hsub : nearRowIndices c N n ⊆
        (Icc 1 N).filter (fun j => j ≠ n ∧ |(j : ℝ) - n| ≤ (n : ℝ) * (linearNearRowRadius c / N)) := by
      intro j hj
      obtain ⟨hjN, hjn, hlog⟩ := mem_filter.mp hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
      have hdist := (abs_sub_le_of_abs_log_le hj0 hn0 hlog).trans
        (mul_le_mul_of_nonneg_left he_gap hn0.le)
      exact mem_filter.mpr ⟨hjN, hjn, hdist⟩
    exact ((show ((nearRowIndices c N n).card : ℝ) ≤
        (((Icc 1 N).filter (fun j => j ≠ n ∧
          |(j : ℝ) - n| ≤ (n : ℝ) * (linearNearRowRadius c / N))).card : ℝ) by
        exact_mod_cast card_le_card hsub).trans (card_near_le (Icc 1 N) n hrad0)).trans_eq (by ring)
  refine ⟨hcard_n, fun j hj => ?_⟩
  obtain ⟨hjN, _, hlog⟩ := mem_filter.mp hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
  have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj0
  have hlog_nj : Real.log n - Real.log j ≤ 2 := by
    have h1 : Real.log n - Real.log j ≤ |Real.log j - Real.log n| := by
      rw [abs_sub_comm]; exact le_abs_self _
    have h2 : 2 * c / N ≤ 2 := by
      have := mul_le_mul_of_nonneg_left hw1 zero_le_two
      simpa only [mul_div_assoc, mul_one] using this
    exact h1.trans (hlog.trans h2)
  have hnj_exp : (n : ℝ) / j ≤ Real.exp 2 := by
    rw [← Real.exp_log (div_pos hn0 hj0), Real.log_div hn0.ne' hj0.ne']
    exact Real.exp_le_exp.mpr hlog_nj
  have hsqrt_j : 1 / Real.sqrt j ≤ Real.exp 1 / Real.sqrt n := by
    have hsq := Real.sqrt_le_sqrt ((div_le_iff₀ hj0).mp hnj_exp)
    have hexp2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [hexp2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos 1).le] at hsq
    exact (div_le_div_iff₀ hsj hsn).mpr (by linarith only [hsq])
  have hq1 : |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos hM, div_le_one hM]
    exact abs_shellAutocorr_le hφ hsupp _
  have hlog_nn : 0 ≤ Real.log N - Real.log j :=
    sub_nonneg.mpr (Real.log_le_log hj0 (by exact_mod_cast (mem_Icc.mp hjN).2))
  have hlog_ub : Real.log N - Real.log j ≤ 2 + Real.log ((N : ℝ) / n) := by
    rw [Real.log_div hN0.ne' hn0.ne']; linarith only [hlog_nj]
  exact ⟨hsqrt_j, hq1, hlog_nn, hlog_ub⟩

private lemma abs_sum_nearShellLogRow_bilinear_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m l N : ℕ} {c : ℝ}
    (hm : 0 < m) (hl : 0 < l) (hc0 : 0 < c) (hN0 : (0 : ℝ) < N)
    (hL0 : 0 < Real.log (N : ℝ)) (hw1 : c / N ≤ 1) :
    |∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (Real.log N))⁻¹ * nearShellLogRow φ c N l n)| ≤
      16 * Real.exp 3 * (Real.sqrt m * Real.sqrt l) * (c / Real.log N) := by
  have hsL0 : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hL0
  have hR0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
  have hpt : ∀ n ∈ Icc 1 N,
      |primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
          ((Real.sqrt (Real.log N))⁻¹ * nearShellLogRow φ c N l n)| ≤
        (4 * Real.exp 1 * linearNearRowRadius c * Real.sqrt m * Real.sqrt l /
          (Real.sqrt N * Real.log N)) * (1 / Real.sqrt n) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
    obtain ⟨hcard_n, hpt_j⟩ := nearRowIndices_card_and_pointwise hφ hsupp hM hc0 hN0 hw1 hn
    have hlog_sqrt : 2 + Real.log ((N : ℝ) / n) ≤ 2 * Real.sqrt ((N : ℝ) / n) :=
      two_add_log_le_two_sqrt (div_pos hN0 hn0)
    have hrow_le : |nearShellLogRow φ c N l n| ≤
        4 * Real.exp 1 * linearNearRowRadius c * Real.sqrt l / Real.sqrt N := by
      have hj_le : ∀ j ∈ nearRowIndices c N n,
          |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
            (Real.log N - Real.log j) * normalizedRamanujanMode l j / Real.sqrt j| ≤
            2 * Real.exp 1 * Real.sqrt l * Real.sqrt ((N : ℝ) / n) / Real.sqrt n := by
        intro j hj
        obtain ⟨hsj, hq1, hlnn, hlub⟩ := hpt_j j hj
        have hm_l := abs_mode_le_sqrt_conductor hl j
        rw [show shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
              (Real.log N - Real.log j) * normalizedRamanujanMode l j / Real.sqrt j =
            (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
              (Real.log N - Real.log j)) *
              (normalizedRamanujanMode l j * (1 / Real.sqrt j)) by ring,
          abs_mul, abs_mul, abs_of_nonneg hlnn, abs_mul,
          abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (j : ℝ))]
        have h12 : |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)| *
            (Real.log N - Real.log j) ≤ 2 * Real.sqrt ((N : ℝ) / n) := by
          calc
            _ ≤ 1 * (2 + Real.log ((N : ℝ) / n)) :=
              mul_le_mul hq1 hlub hlnn zero_le_one
            _ ≤ 2 * Real.sqrt ((N : ℝ) / n) := by linarith only [hlog_sqrt]
        have h34 : |normalizedRamanujanMode l j| * (1 / Real.sqrt (j : ℝ)) ≤
            Real.sqrt l * (Real.exp 1 / Real.sqrt n) :=
          mul_le_mul hm_l hsj (by positivity) (Real.sqrt_nonneg _)
        exact (mul_le_mul h12 h34 (by positivity) (by positivity)).trans_eq (by ring)
      unfold nearShellLogRow
      calc
        |∑ j ∈ nearRowIndices c N n, _| ≤ ∑ j ∈ nearRowIndices c N n,
            (2 * Real.exp 1 * Real.sqrt l * Real.sqrt ((N : ℝ) / n) / Real.sqrt n) :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum hj_le)
        _ = ((nearRowIndices c N n).card : ℝ) *
              (2 * Real.exp 1 * Real.sqrt l * Real.sqrt ((N : ℝ) / n) / Real.sqrt n) := by
          rw [sum_const, nsmul_eq_mul]
        _ ≤ (2 * (n : ℝ) * (linearNearRowRadius c / N)) *
              (2 * Real.exp 1 * Real.sqrt l * (Real.sqrt N / Real.sqrt n) / Real.sqrt n) := by
          rw [Real.sqrt_div hN0.le]
          exact mul_le_mul_of_nonneg_right hcard_n (by positivity)
        _ = 4 * Real.exp 1 * linearNearRowRadius c * Real.sqrt l / Real.sqrt N := by
          field_simp [hsn.ne', hsN.ne', hN0.ne']
          rw [Real.sq_sqrt hn0.le, Real.sq_sqrt hN0.le]; ring
    have hvm_n : |primeHorizonExtension (normalizedRamanujanHorizonVector m N) n| ≤
        Real.sqrt m / (Real.sqrt n * Real.sqrt (Real.log N)) := by
      rw [primeHorizonExtension_normalizedRamanujan hn]
      unfold ramanujanPoleProfile
      rw [abs_mul, abs_div, abs_of_pos (inv_pos.mpr hsL0), abs_of_pos hsn]
      calc
        (Real.sqrt (Real.log N))⁻¹ * (|normalizedRamanujanMode m n| / Real.sqrt n)
            ≤ (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt m / Real.sqrt n) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (abs_mode_le_sqrt_conductor hm n) hsn.le)
            (by positivity)
        _ = Real.sqrt m / (Real.sqrt n * Real.sqrt (Real.log N)) := by ring
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hsL0)]
    calc
      |primeHorizonExtension (normalizedRamanujanHorizonVector m N) n| *
          ((Real.sqrt (Real.log N))⁻¹ * |nearShellLogRow φ c N l n|)
          ≤ (Real.sqrt m / (Real.sqrt n * Real.sqrt (Real.log N))) *
              ((Real.sqrt (Real.log N))⁻¹ *
                (4 * Real.exp 1 * linearNearRowRadius c * Real.sqrt l / Real.sqrt N)) :=
        mul_le_mul hvm_n (mul_le_mul_of_nonneg_left hrow_le (by positivity))
          (by positivity) (by positivity)
      _ = (4 * Real.exp 1 * linearNearRowRadius c * Real.sqrt m * Real.sqrt l /
            (Real.sqrt N * Real.log N)) * (1 / Real.sqrt n) := by
        field_simp [hsn.ne', hsN.ne', hsL0.ne', hL0.ne']
        rw [Real.sq_sqrt hL0.le]; ring
  have hsum_inv := sum_Icc_one_div_sqrt_le_two_sqrt_nat N
  have hexp3 : Real.exp 1 * Real.exp 2 = Real.exp 3 := by
    rw [← Real.exp_add]; norm_num
  calc
    |∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (Real.log N))⁻¹ * nearShellLogRow φ c N l n)|
        ≤ (4 * Real.exp 1 * linearNearRowRadius c * Real.sqrt m * Real.sqrt l /
            (Real.sqrt N * Real.log N)) * ∑ n ∈ Icc 1 N, 1 / Real.sqrt n := by
      rw [mul_sum]
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)
    _ ≤ (4 * Real.exp 1 * linearNearRowRadius c * Real.sqrt m * Real.sqrt l /
            (Real.sqrt N * Real.log N)) * (2 * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left hsum_inv (by positivity)
    _ = 16 * Real.exp 3 * (Real.sqrt m * Real.sqrt l) * (c / Real.log N) := by
      unfold linearNearRowRadius
      rw [← hexp3]
      have hsN : (Real.sqrt (N : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hN0).ne'
      field_simp [hsN, hL0.ne']; ring

private lemma abs_sum_nearShellJetRow_bilinear_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m l N : ℕ} {c : ℝ}
    (hm : 0 < m) (hl : 0 < l) (hc0 : 0 < c) (hN0 : (0 : ℝ) < N)
    (hL0 : 0 < Real.log (N : ℝ)) (hw1 : c / N ≤ 1) :
    |∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (Real.log N))⁻¹ * nearShellJetRow φ c N l n)| ≤
      16 * Real.exp 3 * (Real.sqrt m * l) * (c / Real.log N) := by
  have hsL0 : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hL0
  have hltot_pos : (0 : ℝ) < l.totient := by exact_mod_cast Nat.totient_pos.mpr hl
  have hsltot_pos : 0 < Real.sqrt (l.totient : ℝ) := Real.sqrt_pos.mpr hltot_pos
  have hR0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
  have hjb : ∀ j : ℕ, |(Real.sqrt (l.totient : ℝ))⁻¹ * ramanujanLogDivisorJet l j| ≤
      4 * (l : ℝ) := by
    intro j
    rw [abs_mul, abs_of_pos (inv_pos.mpr hsltot_pos)]
    have hmangoldt : 0 ≤ ArithmeticFunction.vonMangoldt l := ArithmeticFunction.vonMangoldt_nonneg
    have htri := abs_add_le (ramanujanLogDivisorJet l j - ArithmeticFunction.vonMangoldt l)
      (ArithmeticFunction.vonMangoldt l)
    rw [sub_add_cancel, abs_of_nonneg hmangoldt] at htri
    have henv := abs_ramanujanLogDivisorJet_sub_mean_le hl j
    have htot1 : (1 : ℝ) ≤ l.totient := by exact_mod_cast Nat.totient_pos.mpr hl
    have hvm : ArithmeticFunction.vonMangoldt l ≤ Real.log (l : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log
    have hdiff := mul_le_mul_of_nonneg_left
      (RenormalizedArithmeticPotentialTheory.tameDifferent_le_log hl) (Nat.cast_nonneg l.totient)
    have hj_raw : |ramanujanLogDivisorJet l j| ≤ 2 * (l.totient : ℝ) * (1 + Real.log l) := by
      nlinarith only [htri, henv, htot1, Real.log_natCast_nonneg l, hvm, hdiff]
    have hsl_le : Real.sqrt (l.totient : ℝ) ≤ Real.sqrt l :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le l)
    have hlog_l := one_add_log_le_two_sqrt_pos (by exact_mod_cast hl : (0 : ℝ) < l)
    calc
      (Real.sqrt (l.totient : ℝ))⁻¹ * |ramanujanLogDivisorJet l j|
          ≤ (Real.sqrt (l.totient : ℝ))⁻¹ * (2 * (l.totient : ℝ) * (1 + Real.log l)) :=
        mul_le_mul_of_nonneg_left hj_raw (by positivity)
      _ = 2 * Real.sqrt (l.totient : ℝ) * (1 + Real.log l) := by
        field_simp [hsltot_pos.ne']
        rw [Real.sq_sqrt hltot_pos.le]
      _ ≤ 2 * Real.sqrt l * (2 * Real.sqrt l) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsl_le zero_le_two) hlog_l
          (by linarith [Real.log_natCast_nonneg l]) (by positivity)
      _ = 4 * (l : ℝ) := by
        rw [show 2 * Real.sqrt (l : ℝ) * (2 * Real.sqrt l) =
          4 * (Real.sqrt l * Real.sqrt l) by ring, Real.mul_self_sqrt (by positivity)]
  have hpt : ∀ n ∈ Icc 1 N,
      |primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
          ((Real.sqrt (Real.log N))⁻¹ * nearShellJetRow φ c N l n)| ≤
        8 * Real.exp 1 * linearNearRowRadius c * Real.sqrt m * l / ((N : ℝ) * Real.log N) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    obtain ⟨hcard_n, hpt_j⟩ := nearRowIndices_card_and_pointwise hφ hsupp hM hc0 hN0 hw1 hn
    have hrow_le : |nearShellJetRow φ c N l n| ≤
        8 * Real.exp 1 * linearNearRowRadius c * l * Real.sqrt n / N := by
      have hj_le : ∀ j ∈ nearRowIndices c N n,
          |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
            ((Real.sqrt (l.totient : ℝ))⁻¹ * ramanujanLogDivisorJet l j) / Real.sqrt j| ≤
            4 * Real.exp 1 * l / Real.sqrt n := by
        intro j hj
        obtain ⟨hsj, hq1, -, -⟩ := hpt_j j hj
        rw [show shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
              ((Real.sqrt (l.totient : ℝ))⁻¹ * ramanujanLogDivisorJet l j) / Real.sqrt j =
            (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
              ((Real.sqrt (l.totient : ℝ))⁻¹ * ramanujanLogDivisorJet l j)) *
              (1 / Real.sqrt j) by ring,
          abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (j : ℝ))]
        have h1 : |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)| *
            |(Real.sqrt (l.totient : ℝ))⁻¹ * ramanujanLogDivisorJet l j| ≤ 4 * (l : ℝ) := by
          simpa only [one_mul] using mul_le_mul hq1 (hjb j) (by positivity) zero_le_one
        exact (mul_le_mul h1 hsj (by positivity) (by positivity)).trans_eq (by ring)
      unfold nearShellJetRow
      calc
        |∑ j ∈ nearRowIndices c N n, _|
            ≤ ∑ j ∈ nearRowIndices c N n, (4 * Real.exp 1 * l / Real.sqrt n) :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum hj_le)
        _ = ((nearRowIndices c N n).card : ℝ) * (4 * Real.exp 1 * l / Real.sqrt n) := by
          rw [sum_const, nsmul_eq_mul]
        _ ≤ (2 * (n : ℝ) * (linearNearRowRadius c / N)) * (4 * Real.exp 1 * l / Real.sqrt n) :=
          mul_le_mul_of_nonneg_right hcard_n (by positivity)
        _ = 8 * Real.exp 1 * linearNearRowRadius c * l * Real.sqrt n / N := by
          field_simp [hsn.ne', hN0.ne']
          rw [Real.sq_sqrt hn0.le]; ring
    have hvm_n : |primeHorizonExtension (normalizedRamanujanHorizonVector m N) n| ≤
        Real.sqrt m / (Real.sqrt n * Real.sqrt (Real.log N)) := by
      rw [primeHorizonExtension_normalizedRamanujan hn]
      unfold ramanujanPoleProfile
      rw [abs_mul, abs_div, abs_of_pos (inv_pos.mpr hsL0), abs_of_pos hsn]
      calc
        (Real.sqrt (Real.log N))⁻¹ * (|normalizedRamanujanMode m n| / Real.sqrt n)
            ≤ (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt m / Real.sqrt n) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (abs_mode_le_sqrt_conductor hm n) hsn.le)
            (by positivity)
        _ = Real.sqrt m / (Real.sqrt n * Real.sqrt (Real.log N)) := by ring
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hsL0)]
    calc
      |primeHorizonExtension (normalizedRamanujanHorizonVector m N) n| *
          ((Real.sqrt (Real.log N))⁻¹ * |nearShellJetRow φ c N l n|)
          ≤ (Real.sqrt m / (Real.sqrt n * Real.sqrt (Real.log N))) *
              ((Real.sqrt (Real.log N))⁻¹ *
                (8 * Real.exp 1 * linearNearRowRadius c * l * Real.sqrt n / N)) :=
        mul_le_mul hvm_n (mul_le_mul_of_nonneg_left hrow_le (by positivity))
          (by positivity) (by positivity)
      _ = 8 * Real.exp 1 * linearNearRowRadius c * Real.sqrt m * l / ((N : ℝ) * Real.log N) := by
        field_simp [hsn.ne', hsL0.ne', hL0.ne', hN0.ne']
        rw [Real.sq_sqrt hL0.le]; ring
  have hexp3 : Real.exp 1 * Real.exp 2 = Real.exp 3 := by
    rw [← Real.exp_add]; norm_num
  calc
    |∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (Real.log N))⁻¹ * nearShellJetRow φ c N l n)|
        ≤ ∑ _n ∈ Icc 1 N,
            (8 * Real.exp 1 * linearNearRowRadius c * Real.sqrt m * l /
              ((N : ℝ) * Real.log N)) :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)
    _ = 16 * Real.exp 3 * (Real.sqrt m * l) * (c / Real.log N) := by
      rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel, ← hexp3]
      unfold linearNearRowRadius
      field_simp [hN0.ne', hL0.ne']; ring

private lemma abs_sum_regroupedExterior_bilinear_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m l N : ℕ} {c : ℝ}
    (hm : 0 < m) (hl : 0 < l) (hc1 : 1 ≤ c) (hN1 : 1 ≤ N)
    (hL1 : 1 ≤ Real.log (N : ℝ)) (hradN : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N) :
    |∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
          regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n)| ≤
      10 * (Real.exp 1 + 2) * (Real.exp 1 + 1) * (Real.sqrt m * Real.sqrt l) * (c ^ 2 / N) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hsL0 : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hL0
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hw1 : c / N ≤ 1 := by
    have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
    have hcR : c ≤ linearNearRowRadius c := by
      unfold linearNearRowRadius
      have he2 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
      nlinarith only [hc0, he2]
    exact (div_le_one hN0).mpr (by nlinarith only [hcR, h0, hradN])
  have hltot_pos : (0 : ℝ) < l.totient := by exact_mod_cast Nat.totient_pos.mpr hl
  have hsltot_pos : 0 < Real.sqrt (l.totient : ℝ) := Real.sqrt_pos.mpr hltot_pos
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp hw0
  have hG : 0 < ∫ u, (atomDilate φ (c / N)) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hM
  have hgc : HasCompactSupport (atomDilate φ (c / N)) :=
    HasCompactSupport.intro isCompact_Icc hgsupp
  have hB_le : (linearPrimeStrip c : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc1
  have hcN : c ≤ (N : ℝ) := (div_le_one hN0).mp hw1
  have hcut_ub : (exteriorPrimeCutoff c N : ℝ) ≤ 5 * (N : ℝ) := by
    have h1 : (exteriorPrimeCutoff c N : ℝ) ≤ (N : ℝ) + linearPrimeStrip c := by
      exact_mod_cast (exteriorPrimeCutoff_bounds_small_width hc0 hN1 hw1).2
    have he1 : Real.exp 1 ≤ 3 := by have h := Real.exp_one_lt_d9; linarith
    nlinarith only [h1, hB_le, hcN, he1, hc0]
  have hrow_reg : ∀ n : ℕ, |regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n| ≤
      5 * (l.totient : ℝ) * linearPrimeStrip c * Real.log N / Real.sqrt N := by
    intro n
    have hcard : ((Ioc N (exteriorPrimeCutoff c N)).card : ℝ) ≤ linearPrimeStrip c := by
      have hbound := (exteriorPrimeCutoff_bounds_small_width hc0 hN1 hw1).2
      rw [Nat.card_Ioc]
      exact_mod_cast (show exteriorPrimeCutoff c N - N ≤ linearPrimeStrip c by omega)
    have hterm : ∀ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
        |horizonRamanujanMangoldt l N ℓ / Real.sqrt ℓ *
          (bumpCorr (atomDilate φ (c / N)) (Real.log ℓ - Real.log n) /
            (∫ u, (atomDilate φ (c / N)) u ^ 2))| ≤
          5 * (l.totient : ℝ) * Real.log N / Real.sqrt N := by
      intro ℓ hℓ
      obtain ⟨hNℓ, hℓ_hi⟩ := mem_Ioc.mp hℓ
      have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le N) hNℓ)
      have hsℓ : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ0
      have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
      have hℓ_5N : (ℓ : ℝ) ≤ 5 * (N : ℝ) :=
        (by exact_mod_cast hℓ_hi : (ℓ : ℝ) ≤ exteriorPrimeCutoff c N).trans hcut_ub
      have hlogℓ : Real.log ℓ ≤ 5 * Real.log N := by
        have hl_le := Real.log_le_log hℓ0 hℓ_5N
        rw [Real.log_mul (by norm_num) hN0.ne'] at hl_le
        have hl5 : Real.log 5 ≤ 4 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5); linarith
        linarith only [hl_le, hl5, hL1]
      have hcorr : |bumpCorr (atomDilate φ (c / N)) (Real.log ℓ - Real.log n) /
          (∫ u, (atomDilate φ (c / N)) u ^ 2)| ≤ 1 := by
        rw [abs_div, abs_of_pos hG, div_le_one hG]
        exact abs_bumpCorr_le hg.continuous hgc _
      have hjet : |horizonRamanujanMangoldt l N ℓ / Real.sqrt ℓ| ≤
          5 * (l.totient : ℝ) * Real.log N / Real.sqrt N := by
        rw [abs_div, abs_of_pos hsℓ]
        calc
          |horizonRamanujanMangoldt l N ℓ| / Real.sqrt ℓ ≤
              ((l.totient : ℝ) * Real.log ℓ) / Real.sqrt ℓ :=
            div_le_div_of_nonneg_right (abs_horizonRamanujanMangoldt_le l N ℓ) hsℓ.le
          _ ≤ ((l.totient : ℝ) * (5 * Real.log N)) / Real.sqrt N :=
            (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlogℓ (Nat.cast_nonneg _)) hsℓ.le).trans
              (div_le_div_of_nonneg_left (by positivity) hsN
                (Real.sqrt_le_sqrt (by exact_mod_cast hNℓ.le)))
          _ = 5 * (l.totient : ℝ) * Real.log N / Real.sqrt N := by ring
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul hjet hcorr (abs_nonneg _) (by positivity)
    unfold regroupedExteriorDownwardPrimeRow
    calc
      _ ≤ ∑ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
            (5 * (l.totient : ℝ) * Real.log N / Real.sqrt N) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
      _ ≤ 5 * (l.totient : ℝ) * linearPrimeStrip c * Real.log N / Real.sqrt N := by
        rw [sum_const, nsmul_eq_mul]
        exact (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq (by ring)
  have h2strip_N : 2 * linearPrimeStrip c ≤ N := by
    have he1 : Real.exp 1 ≤ 3 := by have h := Real.exp_one_lt_d9; linarith
    have h1 : 2 * ((Real.exp 1 + 1) * c) ≤ 4 * (linearNearRowRadius c + 1) ^ 2 := by
      unfold linearNearRowRadius
      have he2 : 4 ≤ Real.exp 2 := by
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ); linarith
        have hp : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith only [h2, hp]
      have hce2 : 4 * c ≤ 2 * c * Real.exp 2 := by nlinarith only [hc1, he2]
      nlinarith only [hc1, he1, hce2, sq_nonneg (2 * c * Real.exp 2)]
    have hR : 2 * (linearPrimeStrip c : ℝ) ≤ N :=
      (mul_le_mul_of_nonneg_left hB_le zero_le_two).trans (h1.trans hradN)
    exact_mod_cast hR
  let S := (Icc 1 N).filter (fun n => N - linearPrimeStrip c ≤ n)
  have hrestrict : (∑ n ∈ Icc 1 N,
        primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
          ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
            regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n)) =
      ∑ n ∈ S, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
          regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n) := by
    symm
    refine sum_subset (filter_subset _ _) fun n hn hnS => ?_
    have hout : n < N - linearPrimeStrip c := lt_of_not_ge fun h => hnS (mem_filter.mpr ⟨hn, h⟩)
    rw [regroupedExteriorDownwardPrimeRow_eq_zero_small_width hc0 hn hgsupp hw1 hout l,
      mul_zero, mul_zero]
  rw [hrestrict]
  have hcard_S : (S.card : ℝ) ≤ (Real.exp 1 + 2) * c := by
    have hcontain : S ⊆ Icc (N - linearPrimeStrip c) N := fun n hn =>
      mem_Icc.mpr ⟨(mem_filter.mp hn).2, (mem_Icc.mp (mem_filter.mp hn).1).2⟩
    have hnat : S.card ≤ linearPrimeStrip c + 1 := by
      have h := card_le_card hcontain; rw [Nat.card_Icc] at h; omega
    have hcast : (S.card : ℝ) ≤ (linearPrimeStrip c : ℝ) + 1 := by exact_mod_cast hnat
    linarith only [hcast, hB_le, hc1]
  have hpt_S : ∀ n ∈ S, |primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
          regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n)| ≤
      10 * (Real.exp 1 + 1) * Real.sqrt m * Real.sqrt l * c / N := by
    intro n hnS
    obtain ⟨hn, hn_lo⟩ := mem_filter.mp hnS
    have hn_ge : N ≤ 2 * n := by omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
    have hinv_sn : 1 / Real.sqrt n ≤ 2 / Real.sqrt N := by
      rw [div_le_div_iff₀ hsn hsN, one_mul]
      calc
        Real.sqrt (N : ℝ) ≤ Real.sqrt (4 * (n : ℝ)) :=
          Real.sqrt_le_sqrt (by exact_mod_cast (by omega : N ≤ 4 * n))
        _ = 2 * Real.sqrt n := by
          rw [Real.sqrt_mul (by norm_num),
            show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
    have hvm_n : |primeHorizonExtension (normalizedRamanujanHorizonVector m N) n| ≤
        2 * Real.sqrt m / (Real.sqrt N * Real.sqrt (Real.log N)) := by
      rw [primeHorizonExtension_normalizedRamanujan hn]
      unfold ramanujanPoleProfile
      rw [abs_mul, abs_div, abs_of_pos (inv_pos.mpr hsL0), abs_of_pos hsn]
      calc
        (Real.sqrt (Real.log N))⁻¹ * (|normalizedRamanujanMode m n| / Real.sqrt n)
            ≤ (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt m * (1 / Real.sqrt n)) := by
          rw [← mul_one_div]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (abs_mode_le_sqrt_conductor hm n) (by positivity))
            (by positivity)
        _ ≤ (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt m * (2 / Real.sqrt N)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinv_sn (Real.sqrt_nonneg _)) (by positivity)
        _ = 2 * Real.sqrt m / (Real.sqrt N * Real.sqrt (Real.log N)) := by ring
    have hsl_le : Real.sqrt (l.totient : ℝ) ≤ Real.sqrt l :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le l)
    have hreg_n : |(Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
          regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n| ≤
        5 * (Real.exp 1 + 1) * Real.sqrt l * c * Real.sqrt (Real.log N) / Real.sqrt N := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr (mul_pos hsltot_pos hsL0))]
      calc
        (Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
            |regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n|
            ≤ (Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
                (5 * (l.totient : ℝ) * linearPrimeStrip c * Real.log N / Real.sqrt N) :=
          mul_le_mul_of_nonneg_left (hrow_reg n) (by positivity)
        _ = 5 * Real.sqrt (l.totient : ℝ) * linearPrimeStrip c *
              Real.sqrt (Real.log N) / Real.sqrt N := by
          field_simp [hsltot_pos.ne', hsL0.ne', hsN.ne']
          rw [Real.sq_sqrt hltot_pos.le, Real.sq_sqrt hL0.le]; ring
        _ ≤ 5 * Real.sqrt l * ((Real.exp 1 + 1) * c) *
              Real.sqrt (Real.log N) / Real.sqrt N :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul (mul_le_mul_of_nonneg_left hsl_le (by norm_num)) hB_le
                (Nat.cast_nonneg _) (by positivity)) hsL0.le) hsN.le
        _ = 5 * (Real.exp 1 + 1) * Real.sqrt l * c * Real.sqrt (Real.log N) / Real.sqrt N := by
          ring
    rw [abs_mul]
    calc
      _ ≤ (2 * Real.sqrt m / (Real.sqrt N * Real.sqrt (Real.log N))) *
            (5 * (Real.exp 1 + 1) * Real.sqrt l * c * Real.sqrt (Real.log N) / Real.sqrt N) :=
        mul_le_mul hvm_n hreg_n (abs_nonneg _) (by positivity)
      _ = 10 * (Real.exp 1 + 1) * Real.sqrt m * Real.sqrt l * c / N := by
        field_simp [hsN.ne', hsL0.ne', hN0.ne']
        rw [Real.sq_sqrt hN0.le]; ring
  calc
    |∑ n ∈ S, _| ≤ ∑ _n ∈ S, (10 * (Real.exp 1 + 1) * Real.sqrt m * Real.sqrt l * c / N) :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt_S)
    _ = (S.card : ℝ) * (10 * (Real.exp 1 + 1) * Real.sqrt m * Real.sqrt l * c / N) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ ((Real.exp 1 + 2) * c) *
          (10 * (Real.exp 1 + 1) * Real.sqrt m * Real.sqrt l * c / N) :=
      mul_le_mul_of_nonneg_right hcard_S (by positivity)
    _ = 10 * (Real.exp 1 + 2) * (Real.exp 1 + 1) * (Real.sqrt m * Real.sqrt l) * (c ^ 2 / N) := by
      ring

/-- **Logarithm-free Channel 8 upward bilinear residual bound.**
By adjoint reduction to `downwardPrimeVector`, Mangoldt divisor collapse
`∑_{d | j} Λ(d) c_l(j / d) = c_l(j) log j - ramanujanLogDivisorJet l j`, and
`exists_nearGram_mode_bilinear_approx`, the upward prime bilinear residual is bounded by
`O(m^2 * l^2 * c / log N + (m l)^5 * c^5 log N / N)` with zero `log c` and zero Siegel–Walfisz
input. -/
theorem exists_upward_bilinear_log_free {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C_ub : ℝ, 0 ≤ C_ub ∧
      ∀ {m l N : ℕ} {c : ℝ},
        0 < m → 0 < l →
        max 2 (max m l) * max 2 (max m l) ≤ N →
        18 * (1 + Real.log (max 2 (max m l) : ℕ)) ≤ Real.log N →
        1 ≤ c → 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        |⟪upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
            shellCorrection φ c m • normalizedRamanujanHorizonVector m N,
          normalizedRamanujanHorizonVector l N⟫| ≤
          C_ub * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) +
            ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N)) := by
  obtain ⟨C_ng, hCng, hng⟩ := exists_nearGram_mode_bilinear_approx hφ hsupp hM
  let C_sc := 72 * (Real.log 4 + 4)
  let C_p2 := 16 * Real.exp 3
  let C_p3 := 16 * Real.exp 3
  let C_ext := 10 * (Real.exp 1 + 2) * (Real.exp 1 + 1)
  let C_ub := C_sc + C_p2 + C_p3 + C_ng + C_ext + 1
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨C_ub, by dsimp only [C_ub, C_sc, C_p2, C_p3, C_ext]; positivity, ?_⟩
  intro m l N c hm hl hR2N hlog18 hc1 hradN
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N :=
    (by norm_num : 1 ≤ 2 * 2).trans
      ((Nat.mul_le_mul (le_max_left 2 (max m l)) (le_max_left 2 (max m l))).trans hR2N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL1 : 1 ≤ Real.log (N : ℝ) := by
    have hlogR : 0 ≤ Real.log (max 2 (max m l) : ℕ) := Real.log_natCast_nonneg _
    linarith only [hlog18, hlogR]
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hsL0 : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hL0
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hw1 : c / N ≤ 1 := by
    have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
    have hcR : c ≤ linearNearRowRadius c := by
      unfold linearNearRowRadius
      have he2 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
      nlinarith only [hc0, he2]
    exact (div_le_one hN0).mpr (by nlinarith only [hcR, h0, hradN])
  have hltot_pos : (0 : ℝ) < l.totient := by exact_mod_cast Nat.totient_pos.mpr hl
  have hsltot_pos : 0 < Real.sqrt (l.totient : ℝ) := Real.sqrt_pos.mpr hltot_pos
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hl1R : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hml1 : 1 ≤ (m : ℝ) * l := one_le_mul_of_one_le_of_one_le hm1R hl1R
  -- Step 1: Adjoint transpose to `downwardPrimeVector`.
  have hadj : ⟪upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
        shellCorrection φ c m • normalizedRamanujanHorizonVector m N,
      normalizedRamanujanHorizonVector l N⟫ =
      ⟪normalizedRamanujanHorizonVector m N,
        downwardPrimeVector φ c N (normalizedRamanujanHorizonVector l N)⟫ -
        shellCorrection φ c m *
          ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ := by
    rw [inner_sub_left, real_inner_smul_left,
      upwardPrimeVector_inner_eq_downward hφ hsupp hc0 hN1]
  -- Step 2: Expand `downwardPrimeVector` into interior + exterior rows.
  obtain ⟨-, hgsupp, -⟩ := atomDilate_facts hφ hsupp hw0
  have hdown_coord : ∀ n ∈ Icc 1 N,
      primeHorizonExtension (downwardPrimeVector φ c N (normalizedRamanujanHorizonVector l N)) n =
        (Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
          (interiorDownwardPrimeRow (atomDilate φ (c / N)) N l n +
            regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n) := by
    intro n hn
    rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
    change downwardPrimeRow (atomDilate φ (c / N)) N
        (primeHorizonExtension (normalizedRamanujanHorizonVector l N)) n /
        (∫ u, (atomDilate φ (c / N)) u ^ 2) = _
    have hvl_ext : ∀ j ∈ Icc 1 N,
        primeHorizonExtension (normalizedRamanujanHorizonVector l N) j =
          (Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
            (ramanujanLagCoefficient l j / Real.sqrt j) := by
      intro j hj
      rw [primeHorizonExtension_normalizedRamanujan hj]
      unfold ramanujanPoleProfile
      rw [normalizedRamanujanMode,
        TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hl]
      field_simp [hsltot_pos.ne', hsL0.ne']
    rw [downwardPrimeRow_congr_smul hvl_ext, mul_div_assoc]
    congr 1
    have hsub := downwardRamanujanRow_sub_interior_eq hc0 hn hgsupp l
    linarith only [hsub]
  -- Step 3: Split `interiorDownwardPrimeRow` into `nearGram`, `nearShellLogRow`, `nearShellJetRow`.
  have hint_decomp : ∀ n ∈ Icc 1 N,
      (Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
          interiorDownwardPrimeRow (atomDilate φ (c / N)) N l n =
        Real.log N * nearGram φ c N
            (primeHorizonExtension (normalizedRamanujanHorizonVector l N)) n -
          (Real.sqrt (Real.log N))⁻¹ * nearShellLogRow φ c N l n -
          (Real.sqrt (Real.log N))⁻¹ * nearShellJetRow φ c N l n := by
    intro n hn
    have hprime : interiorDownwardPrimeRow (atomDilate φ (c / N)) N l n =
        ∑ j ∈ nearRowIndices c N n,
          shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
            (∑ d ∈ j.divisors, (ArithmeticFunction.vonMangoldt d : ℝ) *
              ramanujanLagCoefficient l (j / d)) / Real.sqrt j := by
      rw [interiorDownwardPrimeRow_eq_divisors, nearRowIndices, sum_filter]
      refine sum_congr rfl fun j _ => ?_
      by_cases hnear : j ≠ n ∧ |Real.log j - Real.log n| ≤ 2 * c / N
      · rw [if_pos hnear, if_neg hnear.1, normalized_bumpCorr_atomDilate hw0]
      · rw [if_neg hnear]
        by_cases hjeq : j = n
        · rw [if_pos hjeq, zero_div, zero_mul, zero_div]
        · rw [if_neg hjeq]
          have hgap : c / N < |Real.log j - Real.log n| := by
            have hgt : 2 * c / N < |Real.log j - Real.log n| :=
              lt_of_not_ge fun h => hnear ⟨hjeq, h⟩
            linarith only [hgt, hw0, (by ring : 2 * c / N = 2 * (c / N))]
          rw [bumpCorr_eq_zero hgsupp hgap, zero_div, zero_mul, zero_div]
    rw [hprime]
    unfold nearGram nearShellLogRow nearShellJetRow
    rw [mul_sum, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun j hj => ?_
    have hjN := (mem_filter.mp hj).1
    rw [sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet l (mem_Icc.mp hjN).1,
      primeHorizonExtension_normalizedRamanujan hjN]
    unfold ramanujanPoleProfile
    rw [normalizedRamanujanMode,
      TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hl]
    field_simp [hsltot_pos.ne', hsL0.ne']
    ring
  have hinner_down :
      ⟪normalizedRamanujanHorizonVector m N,
        downwardPrimeVector φ c N (normalizedRamanujanHorizonVector l N)⟫ =
      Real.log N * nearGramModeBilin φ c N m l -
        (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
          ((Real.sqrt (Real.log N))⁻¹ * nearShellLogRow φ c N l n)) -
        (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
          ((Real.sqrt (Real.log N))⁻¹ * nearShellJetRow φ c N l n)) +
        (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
          ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
            regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n)) := by
    have hsum_eq : ⟪normalizedRamanujanHorizonVector m N,
        downwardPrimeVector φ c N (normalizedRamanujanHorizonVector l N)⟫ =
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
          primeHorizonExtension
            (downwardPrimeVector φ c N (normalizedRamanujanHorizonVector l N)) n := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change (∑ i : PrimeHorizonIndex N,
        (downwardPrimeVector φ c N (normalizedRamanujanHorizonVector l N)) i *
          (normalizedRamanujanHorizonVector m N) i) = _
      rw [← sum_coe_sort (Icc 1 N)]
      refine sum_congr rfl fun i _ => ?_
      rw [primeHorizonExtension_coe, primeHorizonExtension_coe, mul_comm]
    rw [hsum_eq]
    have hpt : ∀ n ∈ Icc 1 N,
        primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
          primeHorizonExtension
            (downwardPrimeVector φ c N (normalizedRamanujanHorizonVector l N)) n =
          Real.log N * (primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
              nearGram φ c N
                (primeHorizonExtension (normalizedRamanujanHorizonVector l N)) n) -
            primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
              ((Real.sqrt (Real.log N))⁻¹ * nearShellLogRow φ c N l n) -
            primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
              ((Real.sqrt (Real.log N))⁻¹ * nearShellJetRow φ c N l n) +
            primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
              ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
                regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n) := by
      intro n hn
      rw [hdown_coord n hn, mul_add, hint_decomp n hn]
      ring
    rw [sum_congr rfl hpt, sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum]
    rfl
  -- Bound Piece 1: `|Real.log N * nearGramModeBilin - shellCorrection * ⟪v_m, v_l⟫|`.
  have hp1 : |Real.log N * nearGramModeBilin φ c N m l -
        shellCorrection φ c m *
          ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫| ≤
      C_ng * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) +
        C_sc * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) := by
    have hid1 : Real.log N * nearGramModeBilin φ c N m l -
        shellCorrection φ c m *
          ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ =
        Real.log N * (nearGramModeBilin φ c N m l -
            (if m = l then shellCorrection φ c m / Real.log N else 0)) -
          shellCorrection φ c m *
            (⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
              if m = l then 1 else 0) := by
      by_cases hml : m = l
      · subst hml
        rw [if_pos rfl, if_pos rfl, mul_sub, mul_div_cancel₀ _ hL0.ne']; ring
      · rw [if_neg hml, if_neg hml]; ring
    rw [hid1]
    have hng_b : |Real.log N * (nearGramModeBilin φ c N m l -
        (if m = l then shellCorrection φ c m / Real.log N else 0))| ≤
        C_ng * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by
      rw [abs_mul, abs_of_pos hL0]
      calc
        Real.log N * |nearGramModeBilin φ c N m l - _|
            ≤ Real.log N * (C_ng * ((m : ℝ) * l) ^ 5 * (c ^ 5 / N)) :=
          mul_le_mul_of_nonneg_left (hng hm hl hR2N hlog18 hc1 hradN) hL0.le
        _ = C_ng * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by ring
    have hgram_b : |⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
        (if m = l then 1 else 0)| ≤
        36 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 / Real.log N := by
      let am : ℕ → ℝ := fun k => if k = m then 1 else 0
      let al : ℕ → ℝ := fun k => if k = l then 1 else 0
      have hmR : m ∈ Icc 1 (max 2 (max m l)) :=
        mem_Icc.mpr ⟨hm, (le_max_left m l).trans (le_max_right 2 _)⟩
      have hlR : l ∈ Icc 1 (max 2 (max m l)) :=
        mem_Icc.mpr ⟨hl, (le_max_right m l).trans (le_max_right 2 _)⟩
      have hsum_am : (∑ k ∈ Icc 1 (max 2 (max m l)),
          am k • normalizedRamanujanHorizonVector k N) =
          normalizedRamanujanHorizonVector m N := by
        have hpt : ∀ k ∈ Icc 1 (max 2 (max m l)), am k • normalizedRamanujanHorizonVector k N =
            if k = m then normalizedRamanujanHorizonVector m N else 0 := fun k _ => by
          dsimp only [am]; by_cases hkm : k = m <;> simp [hkm]
        rw [sum_congr rfl hpt, sum_ite_eq', if_pos hmR]
      have hsum_al : (∑ k ∈ Icc 1 (max 2 (max m l)),
          al k • normalizedRamanujanHorizonVector k N) =
          normalizedRamanujanHorizonVector l N := by
        have hpt : ∀ k ∈ Icc 1 (max 2 (max m l)), al k • normalizedRamanujanHorizonVector k N =
            if k = l then normalizedRamanujanHorizonVector l N else 0 := fun k _ => by
          dsimp only [al]; by_cases hkl : k = l <;> simp [hkl]
        rw [sum_congr rfl hpt, sum_ite_eq', if_pos hlR]
      have hdot : (∑ k ∈ Icc 1 (max 2 (max m l)), am k * al k) = if m = l then 1 else 0 := by
        have hpt : ∀ k ∈ Icc 1 (max 2 (max m l)),
            am k * al k = if k = m then (if m = l then 1 else 0) else 0 := by
          intro k _
          by_cases hkm : k = m
          · subst hkm; simp [am, al]
          · simp [am, al, hkm]
        rw [sum_congr rfl hpt, sum_ite_eq', if_pos hmR]
      have hsq_am : (∑ k ∈ Icc 1 (max 2 (max m l)), am k ^ 2) = 1 := by
        have hpt : ∀ k ∈ Icc 1 (max 2 (max m l)), am k ^ 2 = if k = m then 1 else 0 := fun k _ => by
          dsimp only [am]; by_cases hkm : k = m <;> simp [hkm]
        rw [sum_congr rfl hpt, sum_ite_eq', if_pos hmR]
      have hsq_al : (∑ k ∈ Icc 1 (max 2 (max m l)), al k ^ 2) = 1 := by
        have hpt : ∀ k ∈ Icc 1 (max 2 (max m l)), al k ^ 2 = if k = l then 1 else 0 := fun k _ => by
          dsimp only [al]; by_cases hkl : k = l <;> simp [hkl]
        rw [sum_congr rfl hpt, sum_ite_eq', if_pos hlR]
      have hg0 := CompletedArithmeticForms.abs_inner_sum_normalizedRamanujanHorizonVector_sub_le
        (le_max_left 2 (max m l)) hR2N am al
      rw [hsum_am, hsum_al, hdot, hsq_am, hsq_al, Real.sqrt_one, mul_one, mul_one] at hg0
      have hR2_le : ((max 2 (max m l) : ℕ) : ℝ) ≤ 2 * ((m : ℝ) * l) := by
        rw [Nat.cast_max, Nat.cast_max, Nat.cast_ofNat]
        exact max_le (by linarith only [hml1]) (max_le (by nlinarith only [hm1R, hl1R])
          (by nlinarith only [hm1R, hl1R]))
      have hlogR2 : 1 + Real.log ((max 2 (max m l) : ℕ) : ℝ) ≤ 4 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 := by
        have hR1 : 1 ≤ max 2 (max m l) := (by decide : 1 ≤ 2).trans (le_max_left 2 _)
        have hR0 : (0 : ℝ) < (max 2 (max m l) : ℕ) := by exact_mod_cast hR1
        have h1 := one_add_log_le_two_sqrt_pos hR0
        have hs : Real.sqrt ((max 2 (max m l) : ℕ) : ℝ) ≤ ((max 2 (max m l) : ℕ) : ℝ) := by
          have h1R : (1 : ℝ) ≤ ((max 2 (max m l) : ℕ) : ℝ) := by exact_mod_cast hR1
          calc
            Real.sqrt ((max 2 (max m l) : ℕ) : ℝ)
                ≤ Real.sqrt (((max 2 (max m l) : ℕ) : ℝ) ^ 2) :=
              Real.sqrt_le_sqrt (by nlinarith only [h1R])
            _ = ((max 2 (max m l) : ℕ) : ℝ) := Real.sqrt_sq hR0.le
        have hml_sq : (m : ℝ) * l ≤ (m : ℝ) ^ 2 * (l : ℝ) ^ 2 := by
          nlinarith only [hml1, hm1R, hl1R]
        linarith only [h1, hs, hR2_le, hml_sq]
      exact hg0.trans ((div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogR2 (by norm_num)) hL0.le).trans_eq (by ring))
    have hsc_b := CompletedArithmeticForms.abs_shellCorrection_le_linear hφ hsupp hM hm hc0
    have hsc_term : |shellCorrection φ c m *
        (⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
          if m = l then 1 else 0)| ≤
        C_sc * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) := by
      rw [abs_mul]
      calc
        |shellCorrection φ c m| * |_ - _|
            ≤ (2 * (Real.log 4 + 4) * c) * (36 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 / Real.log N) :=
          mul_le_mul hsc_b hgram_b (abs_nonneg _) (by positivity)
        _ = C_sc * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) := by
          dsimp only [C_sc]; ring
    exact (abs_sub _ _).trans (add_le_add hng_b hsc_term)
  have hsm_m2 : Real.sqrt (m : ℝ) ≤ (m : ℝ) ^ 2 := by
    calc
      Real.sqrt (m : ℝ) ≤ Real.sqrt (((m : ℝ) ^ 2) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith only [hm1R, sq_nonneg ((m : ℝ) - 1)])
      _ = (m : ℝ) ^ 2 := Real.sqrt_sq (by positivity)
  have hsl_l2 : Real.sqrt (l : ℝ) ≤ (l : ℝ) ^ 2 := by
    calc
      Real.sqrt (l : ℝ) ≤ Real.sqrt (((l : ℝ) ^ 2) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith only [hl1R, sq_nonneg ((l : ℝ) - 1)])
      _ = (l : ℝ) ^ 2 := Real.sqrt_sq (by positivity)
  have hl_l2 : (l : ℝ) ≤ (l : ℝ) ^ 2 := by nlinarith only [hl1R]
  have hp2 : |∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (Real.log N))⁻¹ * nearShellLogRow φ c N l n)| ≤
      C_p2 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) := by
    refine (abs_sum_nearShellLogRow_bilinear_le hφ hsupp hM hm hl hc0 hN0 hL0 hw1).trans ?_
    dsimp only [C_p2]
    have hprod := mul_le_mul hsm_m2 hsl_l2 (Real.sqrt_nonneg _) (by positivity)
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprod (by positivity)) (by positivity)).trans_eq (by ring)
  have hp3 : |∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (Real.log N))⁻¹ * nearShellJetRow φ c N l n)| ≤
      C_p3 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) := by
    refine (abs_sum_nearShellJetRow_bilinear_le hφ hsupp hM hm hl hc0 hN0 hL0 hw1).trans ?_
    dsimp only [C_p3]
    have hprod := mul_le_mul hsm_m2 hl_l2 (Nat.cast_nonneg l) (by positivity)
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprod (by positivity)) (by positivity)).trans_eq (by ring)
  have hp4 : |∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
          regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n)| ≤
      C_ext * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by
    refine (abs_sum_regroupedExterior_bilinear_le hφ hsupp hM hm hl hc1 hN1 hL1 hradN).trans ?_
    dsimp only [C_ext]
    have hsm_ml5 : Real.sqrt (m : ℝ) * Real.sqrt l ≤ ((m : ℝ) * l) ^ 5 := by
      rw [← Real.sqrt_mul (by positivity)]
      have h1 : Real.sqrt ((m : ℝ) * l) ≤ (m : ℝ) * l := by
        calc
          Real.sqrt ((m : ℝ) * l) ≤ Real.sqrt (((m : ℝ) * l) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith only [hml1])
          _ = (m : ℝ) * l := Real.sqrt_sq (by positivity)
      exact h1.trans (le_self_pow₀ hml1 (by decide))
    have hc2_5 : c ^ 2 / N ≤ c ^ 5 * Real.log N / N := by
      apply div_le_div_of_nonneg_right _ hN0.le
      exact (pow_le_pow_right₀ hc1 (by norm_num : 2 ≤ 5)).trans
        (le_mul_of_one_le_right (by positivity) hL1)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsm_ml5 (by positivity))
      hc2_5 (by positivity) (by positivity)
  have hcomb : ⟪upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
        shellCorrection φ c m • normalizedRamanujanHorizonVector m N,
      normalizedRamanujanHorizonVector l N⟫ =
      ((Real.log N * nearGramModeBilin φ c N m l -
          shellCorrection φ c m *
            ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫) -
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
          ((Real.sqrt (Real.log N))⁻¹ * nearShellLogRow φ c N l n)) +
      (-(∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
          ((Real.sqrt (Real.log N))⁻¹ * nearShellJetRow φ c N l n)) +
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
          ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
            regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n)) := by
    rw [hadj, hinner_down]; ring
  have htri1 := abs_add_le
    ((Real.log N * nearGramModeBilin φ c N m l -
        shellCorrection φ c m *
          ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫) -
      ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (Real.log N))⁻¹ * nearShellLogRow φ c N l n))
    (-(∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (Real.log N))⁻¹ * nearShellJetRow φ c N l n)) +
      ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
          regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n))
  have htri2 := abs_sub
    (Real.log N * nearGramModeBilin φ c N m l -
      shellCorrection φ c m *
        ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫)
    (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
      ((Real.sqrt (Real.log N))⁻¹ * nearShellLogRow φ c N l n))
  have htri3 := abs_add_le
    (-(∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (Real.log N))⁻¹ * nearShellJetRow φ c N l n)))
    (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
      ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
        regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n))
  rw [abs_neg] at htri3
  rw [hcomb]
  have hA0 : 0 ≤ (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) := by positivity
  have hB0 : 0 ≤ ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by positivity
  have hsum4 : |((Real.log N * nearGramModeBilin φ c N m l -
        shellCorrection φ c m *
          ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫) -
      ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (Real.log N))⁻¹ * nearShellLogRow φ c N l n)) +
    (-(∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (Real.log N))⁻¹ * nearShellJetRow φ c N l n)) +
      ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n *
        ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
          regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N l n))| ≤
      (C_ng * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) +
        C_sc * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N)) +
      C_p2 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) +
      C_p3 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) +
      C_ext * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by
    linarith only [htri1, htri2, htri3, hp1, hp2, hp3, hp4]
  refine hsum4.trans ?_
  have hlin : (C_ng * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) +
        C_sc * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N)) +
      C_p2 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) +
      C_p3 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) +
      C_ext * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) =
      (C_sc + C_p2 + C_p3) * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N)) +
        (C_ng + C_ext) * (((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N)) := by ring
  rw [hlin]
  dsimp only [C_ub]
  have hC1 : C_sc + C_p2 + C_p3 ≤ C_sc + C_p2 + C_p3 + C_ng + C_ext + 1 := by
    have : 0 ≤ C_ext := by dsimp only [C_ext]; positivity
    linarith only [hCng, this]
  have hC2 : C_ng + C_ext ≤ C_sc + C_p2 + C_p3 + C_ng + C_ext + 1 := by
    have : 0 ≤ C_sc + C_p2 + C_p3 := by dsimp only [C_sc, C_p2, C_p3]; positivity
    linarith only [this]
  exact (add_le_add (mul_le_mul_of_nonneg_right hC1 hA0)
    (mul_le_mul_of_nonneg_right hC2 hB0)).trans_eq (by ring)

/-! ## Section 4: Near-Gamma, Downward-Prime, and Near-Center Cancellation -/

/-- Filtering an integer interval `Ico a b` by an order-convex predicate yields a sub-interval
`Ico L U`. -/
private lemma filter_Ico_eq_Ico_of_ordConvex {P : ℕ → Prop} [DecidablePred P]
    (hconv : ∀ ⦃i j r : ℕ⦄, i ≤ j → j ≤ r → P i → P r → P j) (a b : ℕ) :
    ∃ L U : ℕ, L ≤ U ∧ (Ico a b).filter P = Ico L U := by
  let T := (Ico a b).filter P
  by_cases hT : T.Nonempty
  · have hminmax : T.min' hT ≤ T.max' hT := T.min'_le _ (T.max'_mem hT)
    refine ⟨T.min' hT, T.max' hT + 1, by omega, ?_⟩
    ext j
    simp only [T, mem_filter, mem_Ico]
    constructor
    · intro hj
      have hjT : j ∈ T := mem_filter.mpr ⟨mem_Ico.mpr hj.1, hj.2⟩
      exact ⟨T.min'_le j hjT, Nat.lt_succ_of_le (T.le_max' j hjT)⟩
    · intro ⟨hlo, hhi⟩
      have hhi' : j ≤ T.max' hT := Nat.le_of_lt_succ hhi
      obtain ⟨hminI, hPmin⟩ := mem_filter.mp (T.min'_mem hT)
      obtain ⟨hmaxI, hPmax⟩ := mem_filter.mp (T.max'_mem hT)
      exact ⟨⟨(mem_Ico.mp hminI).1.trans hlo, hhi'.trans_lt (mem_Ico.mp hmaxI).2⟩,
        hconv hlo hhi' hPmin hPmax⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hT
    exact ⟨0, 0, le_rfl, by simp [hT]⟩

/-- Elementary bounded-variation summation by parts on `Ico a b`: if every interval sum of `g`
has magnitude `≤ B`, then `|∑_{j ∈ Ico a b} w(j) g(j)| ≤ B * (|w(b - 1)| + ∑ |w(j) - w(j + 1)|)`. -/
private lemma abs_sum_Ico_mul_le_of_bv {w g : ℕ → ℝ} {B : ℝ}
    (hB0 : 0 ≤ B) {a b : ℕ}
    (hg : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, g j| ≤ B) :
    |∑ j ∈ Ico a b, w j * g j| ≤
      B * ((if a < b then |w (b - 1)| else 0) +
        ∑ j ∈ Ico a (b - 1), |w j - w (j + 1)|) := by
  rcases le_or_gt b a with hba | hab
  · rw [Ico_eq_empty (not_lt.mpr hba), if_neg (not_lt.mpr hba),
      Ico_eq_empty (by omega), sum_empty, sum_empty, abs_zero, add_zero, mul_zero]
  · rw [if_pos hab]
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, b = a + m + 1 := ⟨b - a - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    let G : ℕ → ℝ := fun k => ∑ i ∈ Ico a k, g i
    have hGa : G a = 0 := by simp [G]
    have hG_step : ∀ j : ℕ, a ≤ j → g j = G (j + 1) - G j := fun j haj => by
      dsimp only [G]
      rw [sum_Ico_succ_top haj]
      ring
    have hab_id : ∀ n : ℕ,
        (∑ j ∈ Ico a (a + n + 1), w j * g j) =
          w (a + n) * G (a + n + 1) +
            ∑ j ∈ Ico a (a + n), (w j - w (j + 1)) * G (j + 1) := by
      intro n
      induction n with
      | zero =>
        simp only [add_zero, Finset.Ico_self, sum_empty]
        have h1 : Ico a (a + 1) = {a} := by
          ext j; simp only [mem_Ico, mem_singleton]; omega
        rw [h1, sum_singleton, hG_step a le_rfl, hGa, sub_zero]
      | succ n ih =>
        have htop : a + (n + 1) + 1 = (a + n + 1) + 1 := by omega
        rw [htop, sum_Ico_succ_top (by omega), ih, hG_step (a + n + 1) (by omega),
          show a + (n + 1) = (a + n) + 1 by omega, sum_Ico_succ_top (by omega)]
        ring
    rw [hab_id m]
    have htri : |w (a + m) * G (a + m + 1) +
        ∑ j ∈ Ico a (a + m), (w j - w (j + 1)) * G (j + 1)| ≤
        |w (a + m)| * B + ∑ j ∈ Ico a (a + m), |w j - w (j + 1)| * B := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hg a (a + m + 1) (by omega)) (abs_nonneg _)
      · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (hg a (j + 1) (by have := (mem_Ico.mp hj).1; omega)) (abs_nonneg _)
    exact htri.trans_eq (by rw [← sum_mul]; ring)

/-- Logarithm-free `L^2` and bilinear bounds on the exterior downward boundary piece
`(Real.sqrt m.totient)⁻¹ • normalizedExteriorDownwardVector φ c N m`. -/
private lemma exteriorDownward_log_free_bounds {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C_ext : ℝ, 0 < C_ext ∧
      ∀ {m N : ℕ} {c : ℝ},
        0 < m → 1 ≤ c → 1 ≤ Real.log (N : ℝ) →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedExteriorDownwardVector φ c N m‖ ^ 2 ≤
          C_ext * (m : ℝ) * (c ^ 3 * Real.log N / N) ∧
        ∀ {l : ℕ}, 0 < l →
          |⟪(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedExteriorDownwardVector φ c N m,
              normalizedRamanujanHorizonVector l N⟫| ≤
            C_ext * Real.sqrt ((m : ℝ) * l) * (c ^ 2 / N) := by
  let C_q : ℝ := (Real.exp 1 + 2) * (5 * (Real.exp 1 + 1)) ^ 2
  let C_b : ℝ := 10 * (Real.exp 1 + 2) * (Real.exp 1 + 1)
  refine ⟨C_q + C_b + 1, by dsimp only [C_q, C_b]; positivity, ?_⟩
  intro m N c hm hc1 hL1 hradN
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ 4 * (linearNearRowRadius c + 1) ^ 2 := by
      have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      nlinarith only [h0]
    exact_mod_cast this.trans hradN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hsL0 : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hL0
  have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hstot_pos : 0 < Real.sqrt (m.totient : ℝ) := Real.sqrt_pos.mpr htot_pos
  have htot_le : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hw1 : c / N ≤ 1 := by
    have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
    have hcR : c ≤ linearNearRowRadius c := by
      unfold linearNearRowRadius
      have he2 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
      nlinarith only [hc0, he2]
    exact (div_le_one hN0).mpr (by nlinarith only [hcR, h0, hradN])
  have hcN : c ≤ (N : ℝ) := (div_le_one hN0).mp hw1
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp hw0
  have hgc : HasCompactSupport (atomDilate φ (c / N)) := HasCompactSupport.intro isCompact_Icc hgsupp
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hM
  constructor
  · -- Part 1: `L^2` squared norm bound.
    have hB_le : (linearPrimeStrip c : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc1
    have hcut_ub : (exteriorPrimeCutoff c N : ℝ) ≤ 5 * (N : ℝ) := by
      have h1 : (exteriorPrimeCutoff c N : ℝ) ≤ (N : ℝ) + linearPrimeStrip c := by
        exact_mod_cast (exteriorPrimeCutoff_bounds_small_width hc0 hN1 hw1).2
      have he1 : Real.exp 1 ≤ 3 := by have h := Real.exp_one_lt_d9; linarith
      nlinarith only [h1, hB_le, hcN, he1, hc0]
    have hrow_reg : ∀ n : ℕ, |regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N m n| ≤
        5 * (m.totient : ℝ) * linearPrimeStrip c * Real.log N / Real.sqrt N := by
      intro n
      have hcard : ((Ioc N (exteriorPrimeCutoff c N)).card : ℝ) ≤ linearPrimeStrip c := by
        have hbound := (exteriorPrimeCutoff_bounds_small_width hc0 hN1 hw1).2
        rw [Nat.card_Ioc]
        exact_mod_cast (show exteriorPrimeCutoff c N - N ≤ linearPrimeStrip c by omega)
      have hterm : ∀ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
          |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ *
            (bumpCorr (atomDilate φ (c / N)) (Real.log ℓ - Real.log n) /
              (∫ u, (atomDilate φ (c / N)) u ^ 2))| ≤
            5 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by
        intro ℓ hℓ
        obtain ⟨hNℓ, hℓ_hi⟩ := mem_Ioc.mp hℓ
        have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le N) hNℓ)
        have hsℓ : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ0
        have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
        have hℓ_5N : (ℓ : ℝ) ≤ 5 * (N : ℝ) :=
          (by exact_mod_cast hℓ_hi : (ℓ : ℝ) ≤ exteriorPrimeCutoff c N).trans hcut_ub
        have hlogℓ : Real.log ℓ ≤ 5 * Real.log N := by
          have hl := Real.log_le_log hℓ0 hℓ_5N
          rw [Real.log_mul (by norm_num) hN0.ne'] at hl
          have hl5 : Real.log 5 ≤ 4 := by
            have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5); linarith
          linarith only [hl, hl5, hL1]
        have hcorr : |bumpCorr (atomDilate φ (c / N)) (Real.log ℓ - Real.log n) /
            (∫ u, (atomDilate φ (c / N)) u ^ 2)| ≤ 1 := by
          rw [abs_div, abs_of_pos hG, div_le_one hG]
          exact abs_bumpCorr_le hg.continuous hgc _
        have hjet : |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ| ≤
            5 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by
          rw [abs_div, abs_of_pos hsℓ]
          calc
            |horizonRamanujanMangoldt m N ℓ| / Real.sqrt ℓ ≤
                ((m.totient : ℝ) * Real.log ℓ) / Real.sqrt ℓ :=
              div_le_div_of_nonneg_right (abs_horizonRamanujanMangoldt_le m N ℓ) hsℓ.le
            _ ≤ ((m.totient : ℝ) * (5 * Real.log N)) / Real.sqrt N :=
              (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hlogℓ (Nat.cast_nonneg _)) hsℓ.le).trans
                (div_le_div_of_nonneg_left (by positivity) hsN
                  (Real.sqrt_le_sqrt (by exact_mod_cast hNℓ.le)))
            _ = 5 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by ring
        rw [abs_mul]
        simpa only [mul_one] using mul_le_mul hjet hcorr (abs_nonneg _) (by positivity)
      unfold regroupedExteriorDownwardPrimeRow
      calc
        _ ≤ ∑ _ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
              (5 * (m.totient : ℝ) * Real.log N / Real.sqrt N) :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
        _ ≤ 5 * (m.totient : ℝ) * linearPrimeStrip c * Real.log N / Real.sqrt N := by
          rw [sum_const, nsmul_eq_mul]
          exact (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq (by ring)
    let S := (Icc 1 N).filter (fun n => N - linearPrimeStrip c ≤ n)
    have hrestrict : (∑ n ∈ Icc 1 N, actualExteriorDownwardRow (atomDilate φ (c / N)) N m n ^ 2) =
        ∑ n ∈ S, regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N m n ^ 2 := by
      have heq : (∑ n ∈ Icc 1 N, actualExteriorDownwardRow (atomDilate φ (c / N)) N m n ^ 2) =
          ∑ n ∈ Icc 1 N, regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N m n ^ 2 :=
        sum_congr rfl fun n hn => congrArg (fun t : ℝ => t ^ 2)
          (downwardRamanujanRow_sub_interior_eq hc0 hn hgsupp m)
      rw [heq]
      symm
      refine sum_subset (filter_subset _ _) fun n hn hnS => ?_
      have hout : n < N - linearPrimeStrip c := lt_of_not_ge fun h => hnS (mem_filter.mpr ⟨hn, h⟩)
      rw [regroupedExteriorDownwardPrimeRow_eq_zero_small_width hc0 hn hgsupp hw1 hout m,
        zero_pow (by decide)]
    have hcard_S : (S.card : ℝ) ≤ (Real.exp 1 + 2) * c := by
      have hcontain : S ⊆ Icc (N - linearPrimeStrip c) N := fun n hn =>
        mem_Icc.mpr ⟨(mem_filter.mp hn).2, (mem_Icc.mp (mem_filter.mp hn).1).2⟩
      have hnat : S.card ≤ linearPrimeStrip c + 1 := by
        have h := card_le_card hcontain; rw [Nat.card_Icc] at h; omega
      have hcast : (S.card : ℝ) ≤ (linearPrimeStrip c : ℝ) + 1 := by exact_mod_cast hnat
      linarith only [hcast, hB_le, hc1]
    have hsum_raw : (∑ n ∈ Icc 1 N, actualExteriorDownwardRow (atomDilate φ (c / N)) N m n ^ 2) ≤
        C_q * (m.totient : ℝ) ^ 2 * c ^ 3 * Real.log N ^ 2 / N := by
      rw [hrestrict]
      have hcoef : 5 * (m.totient : ℝ) * linearPrimeStrip c ≤
          5 * (m.totient : ℝ) * ((Real.exp 1 + 1) * c) :=
        mul_le_mul_of_nonneg_left hB_le (by positivity)
      calc
        (∑ n ∈ S, regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N m n ^ 2) ≤
            ∑ _n ∈ S, (5 * (m.totient : ℝ) * linearPrimeStrip c * Real.log N / Real.sqrt N) ^ 2 :=
          sum_le_sum fun n _ => by
            have h := mul_self_le_mul_self (abs_nonneg _) (hrow_reg n)
            rwa [← sq, sq_abs, ← sq] at h
        _ ≤ ((Real.exp 1 + 2) * c) *
              ((5 * (m.totient : ℝ) * ((Real.exp 1 + 1) * c)) ^ 2 * Real.log N ^ 2 / N) := by
          rw [sum_const, nsmul_eq_mul, div_pow, mul_pow, Real.sq_sqrt hN0.le]
          exact mul_le_mul hcard_S
            (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcoef 2) (sq_nonneg _))
              hN0.le) (by positivity) (by positivity)
        _ = C_q * (m.totient : ℝ) ^ 2 * c ^ 3 * Real.log N ^ 2 / N := by dsimp only [C_q]; ring
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt htot_pos.le,
      normalizedExteriorDownwardVector_norm_sq]
    calc
      (m.totient : ℝ)⁻¹ *
          ((∑ n ∈ Icc 1 N, actualExteriorDownwardRow (atomDilate φ (c / N)) N m n ^ 2) / Real.log N)
          ≤ (m.totient : ℝ)⁻¹ *
              ((C_q * (m.totient : ℝ) ^ 2 * c ^ 3 * Real.log N ^ 2 / N) / Real.log N) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum_raw hL0.le) (by positivity)
      _ = C_q * (m.totient : ℝ) * (c ^ 3 * Real.log N / N) := by
        field_simp [htot_pos.ne', hN0.ne', hL0.ne']
      _ ≤ (C_q + C_b + 1) * (m : ℝ) * (c ^ 3 * Real.log N / N) := by
        have hCq1 : C_q * (m.totient : ℝ) ≤ (C_q + C_b + 1) * (m : ℝ) := by
          have : 0 ≤ C_b := by dsimp only [C_b]; positivity
          have : 0 ≤ C_q := by dsimp only [C_q]; positivity
          nlinarith only [htot_le, this, ‹0 ≤ C_b›]
        exact mul_le_mul_of_nonneg_right hCq1 (by positivity)
  · -- Part 2: Bilinear pairing bound via `abs_sum_regroupedExterior_bilinear_le` (swapping `m, l`).
    intro l hl
    have heq_in :
        ⟪(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedExteriorDownwardVector φ c N m,
          normalizedRamanujanHorizonVector l N⟫ =
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          ((Real.sqrt (m.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
            regroupedExteriorDownwardPrimeRow (atomDilate φ (c / N)) c N m n) := by
      rw [real_inner_smul_left, EuclideanSpace.inner_eq_star_dotProduct]
      change (Real.sqrt (m.totient : ℝ))⁻¹ *
        (∑ i : PrimeHorizonIndex N,
          normalizedRamanujanHorizonVector l N i *
            (actualExteriorDownwardRow (atomDilate φ (c / N)) N m i.1 /
              Real.sqrt (Real.log N))) = _
      rw [mul_sum, ← sum_coe_sort (Icc 1 N)]
      refine sum_congr rfl fun n hn => ?_
      rw [primeHorizonExtension_coe, downwardRamanujanRow_sub_interior_eq hc0 hn hgsupp m, mul_inv]
      ring
    rw [heq_in]
    have hb := abs_sum_regroupedExterior_bilinear_le hφ hsupp hM hl hm hc1 hN1 hL1 hradN
    rw [mul_comm (Real.sqrt (l : ℝ)) (Real.sqrt (m : ℝ))] at hb
    rw [Real.sqrt_mul (Nat.cast_nonneg m)]
    calc
      _ ≤ C_b * (Real.sqrt m * Real.sqrt l) * (c ^ 2 / N) := hb
      _ ≤ (C_q + C_b + 1) * (Real.sqrt m * Real.sqrt l) * (c ^ 2 / N) := by
        have hCq0 : 0 ≤ C_q := by dsimp only [C_q]; positivity
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith only [hCq0]) (by positivity)) (by positivity)

/-- Archimedean pair remainder row `(a - log(N/c) q) c̃_m(j) / √j` over `nearRowIndices c N n`. -/
private def nearArchRemRow (φ : ℝ → ℝ) (c : ℝ) (N m n : ℕ) : ℝ :=
  ∑ j ∈ nearRowIndices c N n,
    (atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) -
      Real.log (1 / (c / N)) *
        (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2))) *
      normalizedRamanujanMode m j / Real.sqrt j

/-- Core signed cancellation row combining the `-log c` shell part of `nearGammaDownwardRow` with
the near-center row. -/
private def coreNearRow (φ : ℝ → ℝ) (c : ℝ) (N m n : ℕ) : ℝ :=
  -Real.log c * nearGram φ c N (fun j => normalizedRamanujanMode m j / Real.sqrt j) n +
    ∑ j ∈ nearRowIndices c N n,
      completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
        normalizedRamanujanMode m j / Real.sqrt j

/-- Exact row-by-row decomposition of `(√φ(m))⁻¹ * nearGammaDownwardRow + nearCenterRow` into
three `log c`-free collar rows plus `coreNearRow`. -/
private lemma nearGammaDownward_add_nearCenter_row_eq {φ : ℝ → ℝ}
    {c : ℝ} {N m : ℕ} (hm : 0 < m) (hc0 : 0 < c) (hN0 : (0 : ℝ) < N) (n : ℕ) :
    (Real.sqrt (m.totient : ℝ))⁻¹ * nearGammaDownwardRow φ c N m n +
        (∑ j ∈ nearRowIndices c N n,
          completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
            normalizedRamanujanMode m j / Real.sqrt j) =
      nearArchRemRow φ c N m n + nearShellLogRow φ c N m n +
        nearShellJetRow φ c N m n + coreNearRow φ c N m n := by
  have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hstot_ne : Real.sqrt (m.totient : ℝ) ≠ 0 := (Real.sqrt_pos.mpr htot_pos).ne'
  have hlog_eq : Real.log (1 / (c / N)) = Real.log N - Real.log c := by
    rw [one_div, Real.log_inv, Real.log_div hc0.ne' hN0.ne']; ring
  unfold nearGammaDownwardRow nearArchRemRow nearShellLogRow nearShellJetRow coreNearRow nearGram
  rw [mul_sum, mul_sum]
  have hpt : ∀ j ∈ nearRowIndices c N n,
      (Real.sqrt (m.totient : ℝ))⁻¹ * (nearGammaDownwardCoefficient φ c N m n j / Real.sqrt j) =
        ((atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) -
            Real.log (1 / (c / N)) *
              (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2))) *
            normalizedRamanujanMode m j / Real.sqrt j) +
          (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
            (Real.log N - Real.log j) * normalizedRamanujanMode m j / Real.sqrt j) +
          (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
            ((Real.sqrt (m.totient : ℝ))⁻¹ * ramanujanLogDivisorJet m j) / Real.sqrt j) +
          (-Real.log c *
            ((shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)) *
              (normalizedRamanujanMode m j / Real.sqrt j))) := by
    intro j hj
    have hj1 := (mem_Icc.mp (mem_filter.mp hj).1).1
    rw [nearGammaDownwardCoefficient, sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet m hj1,
      normalizedRamanujanMode,
      TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hm]
    rw [hlog_eq]
    field_simp [hstot_ne]
    ring
  rw [sum_congr rfl hpt, sum_add_distrib, sum_add_distrib, sum_add_distrib]
  ring

/-- Logarithm-free `L^2` and bilinear bounds on the three non-core near-collar rows
`nearArchRemRow`, `nearShellLogRow`, and `nearShellJetRow`. -/
private lemma nonCore_nearRows_log_free_bounds {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C_nc : ℝ, 0 < C_nc ∧
      ∀ {m N : ℕ} {c : ℝ},
        0 < m → 1 ≤ c → 1 ≤ N → 0 < Real.log (N : ℝ) → c / N ≤ 1 / 3 →
        (∑ n ∈ Icc 1 N, (nearArchRemRow φ c N m n + nearShellLogRow φ c N m n +
            nearShellJetRow φ c N m n) ^ 2) / Real.log N ≤
          C_nc * (m : ℝ) ^ 2 * (c ^ 2 / Real.log N) ∧
        ∀ {l : ℕ}, 0 < l →
          |(Real.sqrt (Real.log N))⁻¹ *
              ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
                (nearArchRemRow φ c N m n + nearShellLogRow φ c N m n +
                  nearShellJetRow φ c N m n)| ≤
            C_nc * (m : ℝ) * Real.sqrt l * (c / Real.log N) := by
  obtain ⟨Cp, hCp, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  let C_sq : ℝ := 3 * (16 * Real.exp 6 * Cp ^ 2 + 64 * Real.exp 6 + 256 * Real.exp 6)
  let C_bi : ℝ := 4 * Real.exp 3 * Cp + 32 * Real.exp 3
  refine ⟨C_sq + C_bi + 1, by dsimp only [C_sq, C_bi]; positivity, ?_⟩
  intro m N c hm hc1 hN1 hL0 hw3
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsL0 : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hL0
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hw1 : c / N ≤ 1 := hw3.trans (by norm_num)
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsm_le_m : Real.sqrt (m : ℝ) ≤ m := by
    calc
      Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith only [hm1R])
      _ = m := Real.sqrt_sq (Nat.cast_nonneg m)
  have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hstot_pos : 0 < Real.sqrt (m.totient : ℝ) := Real.sqrt_pos.mpr htot_pos
  -- Pointwise row bounds on `n ∈ Icc 1 N`.
  have hrow_arch : ∀ n ∈ Icc 1 N, |nearArchRemRow φ c N m n| ≤
      2 * Real.exp 1 * Cp * linearNearRowRadius c * Real.sqrt m * Real.sqrt n / N := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    obtain ⟨hcard_n, hpt_n⟩ := nearRowIndices_card_and_pointwise hφ hsupp hM hc0 hN0 hw1 hn
    have hj_le : ∀ j ∈ nearRowIndices c N n,
        |(atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) -
            Real.log (1 / (c / N)) *
              (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2))) *
            normalizedRamanujanMode m j / Real.sqrt j| ≤
          Real.exp 1 * Cp * Real.sqrt m / Real.sqrt n := by
      intro j hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hj).1).1
      have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
        have h := (mem_filter.mp hj).2.2
        simpa only [mul_div_assoc] using h
      have hrem : |atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) -
          Real.log (1 / (c / N)) *
            (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2))| ≤ Cp := by
        simpa only [mul_div_assoc] using hpair (c / N) hw0 hw3 n j hs
      obtain ⟨hinv_sj, _, _, _⟩ := hpt_n j hj
      rw [abs_div, abs_mul, abs_of_pos (Real.sqrt_pos.mpr hj0)]
      calc
        |_| * |normalizedRamanujanMode m j| / Real.sqrt j
            ≤ (Cp * Real.sqrt m) * (1 / Real.sqrt j) := by
          rw [div_eq_mul_one_div]
          exact mul_le_mul (mul_le_mul hrem (abs_mode_le_sqrt_conductor hm j) (abs_nonneg _) hCp)
            le_rfl (by positivity) (by positivity)
        _ ≤ (Cp * Real.sqrt m) * (Real.exp 1 / Real.sqrt n) :=
          mul_le_mul_of_nonneg_left hinv_sj (by positivity)
        _ = Real.exp 1 * Cp * Real.sqrt m / Real.sqrt n := by ring
    unfold nearArchRemRow
    calc
      _ ≤ ((nearRowIndices c N n).card : ℝ) * (Real.exp 1 * Cp * Real.sqrt m / Real.sqrt n) := by
        rw [← nsmul_eq_mul, ← sum_const]
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hj_le)
      _ ≤ (2 * (n : ℝ) * (linearNearRowRadius c / N)) *
            (Real.exp 1 * Cp * Real.sqrt m / Real.sqrt n) :=
        mul_le_mul_of_nonneg_right hcard_n (by positivity)
      _ = 2 * Real.exp 1 * Cp * linearNearRowRadius c * Real.sqrt m * Real.sqrt n / N := by
        field_simp [hsn.ne', hN0.ne']; rw [Real.sq_sqrt hn0.le]; ring
  have hrow_log : ∀ n ∈ Icc 1 N, |nearShellLogRow φ c N m n| ≤
      4 * Real.exp 1 * linearNearRowRadius c * Real.sqrt m / Real.sqrt N := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
    obtain ⟨hcard_n, hpt_n⟩ := nearRowIndices_card_and_pointwise hφ hsupp hM hc0 hN0 hw1 hn
    have hlog_sqrt : 2 + Real.log ((N : ℝ) / n) ≤ 2 * Real.sqrt ((N : ℝ) / n) :=
      two_add_log_le_two_sqrt (div_pos hN0 hn0)
    have hj_le : ∀ j ∈ nearRowIndices c N n,
        |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
            (Real.log N - Real.log j) * normalizedRamanujanMode m j / Real.sqrt j| ≤
          2 * Real.exp 1 * Real.sqrt m * Real.sqrt ((N : ℝ) / n) / Real.sqrt n := by
      intro j hj
      obtain ⟨hinv_sj, hq, hlog_nn, hlog_ub⟩ := hpt_n j hj
      have hm_m := abs_mode_le_sqrt_conductor hm j
      rw [show shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
              (Real.log N - Real.log j) * normalizedRamanujanMode m j / Real.sqrt j =
            (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
              (Real.log N - Real.log j)) *
              (normalizedRamanujanMode m j * (1 / Real.sqrt j)) by ring,
        abs_mul, abs_mul, abs_of_nonneg hlog_nn, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (j : ℝ))]
      have h12 : |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)| *
          (Real.log N - Real.log j) ≤ 2 * Real.sqrt ((N : ℝ) / n) := by
        calc
          _ ≤ 1 * (2 + Real.log ((N : ℝ) / n)) := mul_le_mul hq hlog_ub hlog_nn zero_le_one
          _ ≤ 2 * Real.sqrt ((N : ℝ) / n) := by linarith only [hlog_sqrt]
      have h34 : |normalizedRamanujanMode m j| * (1 / Real.sqrt (j : ℝ)) ≤
          Real.sqrt m * (Real.exp 1 / Real.sqrt n) :=
        mul_le_mul hm_m hinv_sj (by positivity) (Real.sqrt_nonneg _)
      exact (mul_le_mul h12 h34 (by positivity) (by positivity)).trans_eq (by ring)
    unfold nearShellLogRow
    calc
      _ ≤ ((nearRowIndices c N n).card : ℝ) *
            (2 * Real.exp 1 * Real.sqrt m * Real.sqrt ((N : ℝ) / n) / Real.sqrt n) := by
        rw [← nsmul_eq_mul, ← sum_const]
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hj_le)
      _ ≤ (2 * (n : ℝ) * (linearNearRowRadius c / N)) *
            (2 * Real.exp 1 * Real.sqrt m * (Real.sqrt N / Real.sqrt n) / Real.sqrt n) := by
        rw [Real.sqrt_div hN0.le]
        exact mul_le_mul_of_nonneg_right hcard_n (by positivity)
      _ = 4 * Real.exp 1 * linearNearRowRadius c * Real.sqrt m / Real.sqrt N := by
        field_simp [hsn.ne', hsN.ne', hN0.ne']
        rw [Real.sq_sqrt hn0.le, Real.sq_sqrt hN0.le]; ring
  have hrow_jet : ∀ n ∈ Icc 1 N, |nearShellJetRow φ c N m n| ≤
      8 * Real.exp 1 * linearNearRowRadius c * (m : ℝ) * Real.sqrt n / N := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    obtain ⟨hcard_n, hpt_n⟩ := nearRowIndices_card_and_pointwise hφ hsupp hM hc0 hN0 hw1 hn
    have hj_le : ∀ j ∈ nearRowIndices c N n,
        |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
            ((Real.sqrt (m.totient : ℝ))⁻¹ * ramanujanLogDivisorJet m j) / Real.sqrt j| ≤
          4 * Real.exp 1 * (m : ℝ) / Real.sqrt n := by
      intro j hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hj).1).1
      obtain ⟨hinv_sj, hq, _, _⟩ := hpt_n j hj
      have hjb : |(Real.sqrt (m.totient : ℝ))⁻¹ * ramanujanLogDivisorJet m j| ≤ 4 * (m : ℝ) := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hstot_pos)]
        have htri := abs_add_le (ramanujanLogDivisorJet m j - ArithmeticFunction.vonMangoldt m)
          (ArithmeticFunction.vonMangoldt m)
        rw [sub_add_cancel, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] at htri
        have henv := abs_ramanujanLogDivisorJet_sub_mean_le hm j
        have htot1 : (1 : ℝ) ≤ m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
        have hvm : ArithmeticFunction.vonMangoldt m ≤ Real.log (m : ℝ) :=
          ArithmeticFunction.vonMangoldt_le_log
        have hdiff := mul_le_mul_of_nonneg_left
          (RenormalizedArithmeticPotentialTheory.tameDifferent_le_log hm)
          (Nat.cast_nonneg m.totient)
        have hj_raw : |ramanujanLogDivisorJet m j| ≤ 2 * (m.totient : ℝ) * (1 + Real.log m) := by
          nlinarith only [htri, henv, htot1, Real.log_natCast_nonneg m, hvm, hdiff]
        have hsm_le : Real.sqrt (m.totient : ℝ) ≤ Real.sqrt m :=
          Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le m)
        have hlog_m := one_add_log_le_two_sqrt_pos (by exact_mod_cast hm : (0 : ℝ) < m)
        calc
          (Real.sqrt (m.totient : ℝ))⁻¹ * |ramanujanLogDivisorJet m j|
              ≤ (Real.sqrt (m.totient : ℝ))⁻¹ * (2 * (m.totient : ℝ) * (1 + Real.log m)) :=
            mul_le_mul_of_nonneg_left hj_raw (by positivity)
          _ = 2 * Real.sqrt (m.totient : ℝ) * (1 + Real.log m) := by
            field_simp [hstot_pos.ne']; rw [Real.sq_sqrt htot_pos.le]
          _ ≤ 2 * Real.sqrt m * (2 * Real.sqrt m) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hsm_le zero_le_two) hlog_m
              (by linarith [Real.log_natCast_nonneg m]) (by positivity)
          _ = 4 * (m : ℝ) := by
            rw [show 2 * Real.sqrt m * (2 * Real.sqrt m) = 4 * (Real.sqrt m * Real.sqrt m) by ring,
              Real.mul_self_sqrt (Nat.cast_nonneg m)]
      have hrew : shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
          ((Real.sqrt (m.totient : ℝ))⁻¹ * ramanujanLogDivisorJet m j) / Real.sqrt j =
          (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)) *
            ((Real.sqrt (m.totient : ℝ))⁻¹ * ramanujanLogDivisorJet m j) *
            (1 / Real.sqrt j) := by ring
      rw [hrew, abs_mul, abs_mul, abs_of_pos (one_div_pos.mpr (Real.sqrt_pos.mpr hj0))]
      calc
        |_| * |(Real.sqrt (m.totient : ℝ))⁻¹ * ramanujanLogDivisorJet m j| * (1 / Real.sqrt j)
            ≤ (1 * (4 * (m : ℝ))) * (Real.exp 1 / Real.sqrt n) :=
          mul_le_mul (mul_le_mul hq hjb (abs_nonneg _) zero_le_one) hinv_sj
            (by positivity) (by positivity)
        _ = 4 * Real.exp 1 * (m : ℝ) / Real.sqrt n := by ring
    unfold nearShellJetRow
    calc
      _ ≤ ((nearRowIndices c N n).card : ℝ) * (4 * Real.exp 1 * (m : ℝ) / Real.sqrt n) := by
        rw [← nsmul_eq_mul, ← sum_const]
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hj_le)
      _ ≤ (2 * (n : ℝ) * (linearNearRowRadius c / N)) *
            (4 * Real.exp 1 * (m : ℝ) / Real.sqrt n) :=
        mul_le_mul_of_nonneg_right hcard_n (by positivity)
      _ = 8 * Real.exp 1 * linearNearRowRadius c * (m : ℝ) * Real.sqrt n / N := by
        field_simp [hsn.ne', hN0.ne']; rw [Real.sq_sqrt hn0.le]; ring
  constructor
  · -- Part 1: `L^2` squared sum bound.
    have hexp6 : Real.exp 2 * (Real.exp 2) ^ 2 = Real.exp 6 := by
      have : (Real.exp 2) ^ 2 = Real.exp 4 := by rw [sq, ← Real.exp_add]; norm_num
      rw [this, ← Real.exp_add]; norm_num
    have hexp2_sq : (Real.exp 1) ^ 2 = Real.exp 2 := by rw [sq, ← Real.exp_add]; norm_num
    have hpt_sq : ∀ n ∈ Icc 1 N,
        (nearArchRemRow φ c N m n + nearShellLogRow φ c N m n + nearShellJetRow φ c N m n) ^ 2 ≤
          C_sq * (m : ℝ) ^ 2 * c ^ 2 / N := by
      intro n hn
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      have ha1 := hrow_arch n hn
      have hl1 := hrow_log n hn
      have hj1 := hrow_jet n hn
      have ha2 : nearArchRemRow φ c N m n ^ 2 ≤ 16 * Real.exp 6 * Cp ^ 2 * (m : ℝ) ^ 2 * c ^ 2 / N := by
        have hsq := pow_le_pow_left₀ (abs_nonneg _) ha1 2
        rw [sq_abs, div_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow,
          Real.sq_sqrt (Nat.cast_nonneg m), Real.sq_sqrt hn0, hexp2_sq] at hsq
        unfold linearNearRowRadius at hsq
        have h1 : (2 : ℝ) ^ 2 * Real.exp 2 * Cp ^ 2 * (2 * c * Real.exp 2) ^ 2 * m * n / N ^ 2 =
            16 * (Real.exp 2 * (Real.exp 2) ^ 2) * Cp ^ 2 * c ^ 2 * (m * n / N) / N := by ring
        rw [h1, hexp6] at hsq
        have hmn : (m : ℝ) * n / N ≤ (m : ℝ) ^ 2 := by
          have hn1 : (n : ℝ) / N ≤ 1 := (div_le_one hN0).mpr hnN
          calc
            (m : ℝ) * n / N = (m : ℝ) * ((n : ℝ) / N) := by ring
            _ ≤ (m : ℝ) * 1 := mul_le_mul_of_nonneg_left hn1 (Nat.cast_nonneg m)
            _ ≤ (m : ℝ) ^ 2 := by nlinarith only [hm1R]
        exact hsq.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmn (by positivity)) hN0.le)
      have hl2 : nearShellLogRow φ c N m n ^ 2 ≤ 64 * Real.exp 6 * (m : ℝ) ^ 2 * c ^ 2 / N := by
        have hsq := pow_le_pow_left₀ (abs_nonneg _) hl1 2
        rw [sq_abs, div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m),
          Real.sq_sqrt hN0.le, hexp2_sq] at hsq
        unfold linearNearRowRadius at hsq
        have h1 : (4 : ℝ) ^ 2 * Real.exp 2 * (2 * c * Real.exp 2) ^ 2 * m / N =
            64 * (Real.exp 2 * (Real.exp 2) ^ 2) * (m : ℝ) * c ^ 2 / N := by ring
        rw [h1, hexp6] at hsq
        have hm2 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith only [hm1R]
        exact hsq.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm2 (by positivity))
            (sq_nonneg c)) hN0.le)
      have hj2 : nearShellJetRow φ c N m n ^ 2 ≤ 256 * Real.exp 6 * (m : ℝ) ^ 2 * c ^ 2 / N := by
        have hsq := pow_le_pow_left₀ (abs_nonneg _) hj1 2
        rw [sq_abs, div_pow, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hn0, hexp2_sq] at hsq
        unfold linearNearRowRadius at hsq
        have h1 : (8 : ℝ) ^ 2 * Real.exp 2 * (2 * c * Real.exp 2) ^ 2 * (m : ℝ) ^ 2 * n / N ^ 2 =
            256 * (Real.exp 2 * (Real.exp 2) ^ 2) * (m : ℝ) ^ 2 * c ^ 2 * ((n : ℝ) / N) / N := by
          ring
        rw [h1, hexp6] at hsq
        have hn1 : (n : ℝ) / N ≤ 1 := (div_le_one hN0).mpr hnN
        exact hsq.trans ((div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hn1 (by positivity)) hN0.le).trans_eq (by ring))
      have h3sq : (nearArchRemRow φ c N m n + nearShellLogRow φ c N m n +
          nearShellJetRow φ c N m n) ^ 2 ≤
          3 * (nearArchRemRow φ c N m n ^ 2 + nearShellLogRow φ c N m n ^ 2 +
            nearShellJetRow φ c N m n ^ 2) := by
        nlinarith only [sq_nonneg (nearArchRemRow φ c N m n - nearShellLogRow φ c N m n),
          sq_nonneg (nearArchRemRow φ c N m n - nearShellJetRow φ c N m n),
          sq_nonneg (nearShellLogRow φ c N m n - nearShellJetRow φ c N m n)]
      dsimp only [C_sq]
      linarith only [h3sq, ha2, hl2, hj2,
        (by ring : 3 * (16 * Real.exp 6 * Cp ^ 2 * (m : ℝ) ^ 2 * c ^ 2 / N +
            64 * Real.exp 6 * (m : ℝ) ^ 2 * c ^ 2 / N +
            256 * Real.exp 6 * (m : ℝ) ^ 2 * c ^ 2 / N) =
          3 * (16 * Real.exp 6 * Cp ^ 2 + 64 * Real.exp 6 + 256 * Real.exp 6) *
            (m : ℝ) ^ 2 * c ^ 2 / N)]
    calc
      (∑ n ∈ Icc 1 N, (nearArchRemRow φ c N m n + nearShellLogRow φ c N m n +
            nearShellJetRow φ c N m n) ^ 2) / Real.log N
          ≤ (∑ _n ∈ Icc 1 N, (C_sq * (m : ℝ) ^ 2 * c ^ 2 / N)) / Real.log N :=
        div_le_div_of_nonneg_right (sum_le_sum hpt_sq) hL0.le
      _ = C_sq * (m : ℝ) ^ 2 * (c ^ 2 / Real.log N) := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        field_simp [hN0.ne', hL0.ne']
      _ ≤ (C_sq + C_bi + 1) * (m : ℝ) ^ 2 * (c ^ 2 / Real.log N) := by
        have : 0 ≤ C_bi := by dsimp only [C_bi]; positivity
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith only [this]) (sq_nonneg _)) (by positivity)
  · -- Part 2: Bilinear pairing bound against `v_l`.
    intro l hl
    have hexp3 : Real.exp 1 * Real.exp 2 = Real.exp 3 := by rw [← Real.exp_add]; norm_num
    have hbi_arch : |(Real.sqrt (Real.log N))⁻¹ *
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          nearArchRemRow φ c N m n| ≤
        4 * Real.exp 3 * Cp * (Real.sqrt m * Real.sqrt l) * (c / Real.log N) := by
      have hpt : ∀ n ∈ Icc 1 N,
          |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              nearArchRemRow φ c N m n| ≤
            2 * Real.exp 1 * Cp * linearNearRowRadius c * Real.sqrt m * Real.sqrt l /
              (N * Real.sqrt (Real.log N)) := by
        intro n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
        have hvl_n : |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n| ≤
            Real.sqrt l / (Real.sqrt n * Real.sqrt (Real.log N)) := by
          rw [primeHorizonExtension_normalizedRamanujan hn]
          unfold ramanujanPoleProfile
          rw [abs_mul, abs_div, abs_of_pos (inv_pos.mpr hsL0), abs_of_pos hsn]
          exact (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (abs_mode_le_sqrt_conductor hl n) hsn.le)
            (by positivity)).trans_eq (by ring)
        rw [abs_mul]
        calc
          _ ≤ (Real.sqrt l / (Real.sqrt n * Real.sqrt (Real.log N))) *
                (2 * Real.exp 1 * Cp * linearNearRowRadius c * Real.sqrt m * Real.sqrt n / N) :=
            mul_le_mul hvl_n (hrow_arch n hn) (abs_nonneg _) (by positivity)
          _ = 2 * Real.exp 1 * Cp * linearNearRowRadius c * Real.sqrt m * Real.sqrt l /
                (N * Real.sqrt (Real.log N)) := by
            field_simp [hsn.ne', hsL0.ne', hN0.ne']
      rw [abs_mul, abs_of_pos (inv_pos.mpr hsL0)]
      calc
        _ ≤ (Real.sqrt (Real.log N))⁻¹ *
              ∑ _n ∈ Icc 1 N, (2 * Real.exp 1 * Cp * linearNearRowRadius c *
                Real.sqrt m * Real.sqrt l / (N * Real.sqrt (Real.log N))) :=
          mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)) (by positivity)
        _ = 4 * Real.exp 3 * Cp * (Real.sqrt m * Real.sqrt l) * (c / Real.log N) := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          unfold linearNearRowRadius
          rw [← hexp3]
          field_simp [hsL0.ne', hL0.ne', hN0.ne']
          rw [Real.sq_sqrt hL0.le]; ring
    have hbi_log : |(Real.sqrt (Real.log N))⁻¹ *
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          nearShellLogRow φ c N m n| ≤
        16 * Real.exp 3 * (Real.sqrt l * Real.sqrt m) * (c / Real.log N) := by
      have heq : (Real.sqrt (Real.log N))⁻¹ *
          (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            nearShellLogRow φ c N m n) =
          ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            ((Real.sqrt (Real.log N))⁻¹ * nearShellLogRow φ c N m n) := by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
      rw [heq]
      exact abs_sum_nearShellLogRow_bilinear_le hφ hsupp hM hl hm hc0 hN0 hL0 hw1
    have hbi_jet : |(Real.sqrt (Real.log N))⁻¹ *
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          nearShellJetRow φ c N m n| ≤
        16 * Real.exp 3 * (Real.sqrt l * m) * (c / Real.log N) := by
      have heq : (Real.sqrt (Real.log N))⁻¹ *
          (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            nearShellJetRow φ c N m n) =
          ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            ((Real.sqrt (Real.log N))⁻¹ * nearShellJetRow φ c N m n) := by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
      rw [heq]
      exact abs_sum_nearShellJetRow_bilinear_le hφ hsupp hM hl hm hc0 hN0 hL0 hw1
    have hsplit : (Real.sqrt (Real.log N))⁻¹ *
        (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          (nearArchRemRow φ c N m n + nearShellLogRow φ c N m n + nearShellJetRow φ c N m n)) =
        (Real.sqrt (Real.log N))⁻¹ *
          (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            nearArchRemRow φ c N m n) +
        (Real.sqrt (Real.log N))⁻¹ *
          (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            nearShellLogRow φ c N m n) +
        (Real.sqrt (Real.log N))⁻¹ *
          (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            nearShellJetRow φ c N m n) := by
      have hpt : ∀ n ∈ Icc 1 N,
          primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            (nearArchRemRow φ c N m n + nearShellLogRow φ c N m n + nearShellJetRow φ c N m n) =
          primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              nearArchRemRow φ c N m n +
            primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              nearShellLogRow φ c N m n +
            primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              nearShellJetRow φ c N m n := fun _ _ => by ring
      rw [sum_congr rfl hpt, sum_add_distrib, sum_add_distrib, mul_add, mul_add]
    rw [hsplit]
    have htri := abs_add_three
      ((Real.sqrt (Real.log N))⁻¹ *
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          nearArchRemRow φ c N m n)
      ((Real.sqrt (Real.log N))⁻¹ *
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          nearShellLogRow φ c N m n)
      ((Real.sqrt (Real.log N))⁻¹ *
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          nearShellJetRow φ c N m n)
    have hsm_l : Real.sqrt (m : ℝ) * Real.sqrt l ≤ (m : ℝ) * Real.sqrt l :=
      mul_le_mul_of_nonneg_right hsm_le_m (Real.sqrt_nonneg _)
    have hml_arch : 4 * Real.exp 3 * Cp * (Real.sqrt m * Real.sqrt l) * (c / Real.log N) ≤
        4 * Real.exp 3 * Cp * (m : ℝ) * Real.sqrt l * (c / Real.log N) :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsm_l (by positivity))
        (by positivity)).trans_eq (by ring)
    have hml_log : 16 * Real.exp 3 * (Real.sqrt l * Real.sqrt m) * (c / Real.log N) ≤
        16 * Real.exp 3 * (m : ℝ) * Real.sqrt l * (c / Real.log N) := by
      rw [mul_comm (Real.sqrt (l : ℝ)) (Real.sqrt (m : ℝ))]
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsm_l (by positivity))
        (by positivity)).trans_eq (by ring)
    have hml_jet : 16 * Real.exp 3 * (Real.sqrt l * m) * (c / Real.log N) =
        16 * Real.exp 3 * (m : ℝ) * Real.sqrt l * (c / Real.log N) := by ring
    have hsum3 : |(Real.sqrt (Real.log N))⁻¹ *
          (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            nearArchRemRow φ c N m n) +
        (Real.sqrt (Real.log N))⁻¹ *
          (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            nearShellLogRow φ c N m n) +
        (Real.sqrt (Real.log N))⁻¹ *
          (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            nearShellJetRow φ c N m n)| ≤
        C_bi * (m : ℝ) * Real.sqrt l * (c / Real.log N) := by
      dsimp only [C_bi]
      linarith only [htri, hbi_arch, hbi_log, hbi_jet, hml_arch, hml_log, hml_jet,
        (by ring : (4 * Real.exp 3 * Cp + 32 * Real.exp 3) * (m : ℝ) * Real.sqrt l *
            (c / Real.log N) =
          4 * Real.exp 3 * Cp * (m : ℝ) * Real.sqrt l * (c / Real.log N) +
            16 * Real.exp 3 * (m : ℝ) * Real.sqrt l * (c / Real.log N) +
            16 * Real.exp 3 * (m : ℝ) * Real.sqrt l * (c / Real.log N))]
    refine hsum3.trans ?_
    have : 0 ≤ C_sq := by dsimp only [C_sq]; positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [this]) (Nat.cast_nonneg m))
        (Real.sqrt_nonneg _))
      (by positivity)

/-- Two-sided logarithmic bounds on the finite harmonic sum `∑_{k ∈ Icc 1 M} 1 / k` for `M ≥ 1`:
`log M ≤ ∑_{k=1}^M 1 / k ≤ 1 + log M`. -/
private lemma log_le_sum_Icc_one_div_and_le {M : ℕ} (hM : 1 ≤ M) :
    Real.log (M : ℝ) ≤ (∑ k ∈ Icc 1 M, 1 / (k : ℝ)) ∧
      (∑ k ∈ Icc 1 M, 1 / (k : ℝ)) ≤ 1 + Real.log (M : ℝ) := by
  refine ⟨?_, RHTower.sum_Icc_one_div_le hM⟩
  have h1 : Real.log ((M : ℝ) + 1) ≤ ∑ k ∈ Icc 1 M, 1 / (k : ℝ) := by
    clear hM
    induction M with
    | zero => simp
    | succ m ih =>
      rw [sum_Icc_succ_top (by omega)]
      have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hstep : Real.log ((m + 1 : ℕ) + 1 : ℝ) - Real.log ((m : ℝ) + 1) ≤
          1 / ((m + 1 : ℕ) : ℝ) := by
        have hq : (0 : ℝ) < (((m + 1 : ℕ) : ℝ) + 1) / ((m : ℝ) + 1) := by positivity
        have hl := Real.log_le_sub_one_of_pos hq
        rw [Real.log_div (by positivity) hm1.ne'] at hl
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        have hsub : (((m + 1 : ℕ) : ℝ) + 1) / ((m : ℝ) + 1) - 1 = 1 / ((m + 1 : ℕ) : ℝ) := by
          rw [hcast]; field_simp [hm1.ne']; ring
        linarith only [hl, hsub]
      linarith only [ih, hstep]
  exact (Real.log_le_log (by exact_mod_cast hM) (by linarith)).trans h1

/-- Pointwise universal and interior harmonic-collar bounds on
`∑_{j ∈ nearRowIndices c N n} archimedeanCenterKernel n j / √j - log c * √n`.
On interior rows `2 N / c < n` with `n * exp(2 c / N) ≤ N`, the half-collar width `Δ_n ≍ c n / N`
has harmonic sum `log(c n / N) + O(1)`, cancelling `log c` identically and leaving `O(√N)`. -/
private lemma abs_centerPoleCollar_diff_le {c : ℝ} {N n : ℕ}
    (hc1 : 1 ≤ c) (h8c : 8 * c ≤ N) (hn : n ∈ Icc 1 N) :
    |(∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) -
        Real.log c * Real.sqrt n| ≤
      (4 + 2 * Real.exp 2) * (1 + Real.log c) * Real.sqrt n ∧
      (2 * (N : ℝ) / c < n → (n : ℝ) * Real.exp (2 * c / N) ≤ N →
        |(∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) -
            Real.log c * Real.sqrt n| ≤
          2 * (6 + 2 * Real.exp 2) * Real.sqrt N) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < N := by linarith only [hc0, h8c]
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hw1 : c / N ≤ 1 := (div_le_one hN0).mpr (by linarith only [hc0, h8c])
  -- Exact harmonic identity on `nearRowIndices c N n`.
  have hker_eq : (∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) =
      Real.sqrt n * ((1 / 2 : ℝ) *
        ((∑ j ∈ nearRowIndices c N n, 1 / |(n : ℝ) - j|) +
          ∑ j ∈ nearRowIndices c N n, 1 / ((n : ℝ) + j))) := by
    rw [← sum_add_distrib, mul_sum, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    obtain ⟨hjI, hjn, -⟩ := mem_filter.mp hj
    have hj1 := (mem_Icc.mp hjI).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have h := archimedeanCenterKernel_div_sqrt_mul hn1 hj1 (Ne.symm hjn)
    calc
      archimedeanCenterKernel n j / Real.sqrt j =
          Real.sqrt n * (archimedeanCenterKernel n j / (Real.sqrt n * Real.sqrt j)) := by
        field_simp [hsn.ne', (Real.sqrt_pos.mpr hj0).ne']
      _ = _ := by rw [h]
  -- Bound the smooth reciprocal-sum half `∑ 1 / (n + j) ≤ 4 e^2`.
  have hadd_sum : 0 ≤ (∑ j ∈ nearRowIndices c N n, 1 / ((n : ℝ) + j)) ∧
      (∑ j ∈ nearRowIndices c N n, 1 / ((n : ℝ) + j)) ≤ 4 * Real.exp 2 := by
    refine ⟨sum_nonneg fun j _ => by positivity, ?_⟩
    have he_gap : Real.exp (2 * c / N) - 1 ≤ linearNearRowRadius c / N := by
      calc
        Real.exp (2 * c / N) - 1 ≤ 2 * c / N * Real.exp (2 * c / N) := exp_sub_one_le_mul_exp
        _ ≤ 2 * c / N * Real.exp 2 :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by
              have h := mul_le_mul_of_nonneg_left hw1 zero_le_two
              simpa only [mul_div_assoc, mul_one] using h)) (by positivity)
        _ = linearNearRowRadius c / N := by unfold linearNearRowRadius; ring
    let rad_n := (n : ℝ) * (linearNearRowRadius c / N)
    have hrad0 : 0 ≤ rad_n := by dsimp only [rad_n]; unfold linearNearRowRadius; positivity
    have hcard_n : ((nearRowIndices c N n).card : ℝ) ≤ 2 * rad_n := by
      have hsub : nearRowIndices c N n ⊆
          (Icc 1 N).filter (fun j => j ≠ n ∧ |(j : ℝ) - n| ≤ rad_n) := by
        intro j hj
        obtain ⟨hjI, hjn, hlog⟩ := mem_filter.mp hj
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjI).1
        exact mem_filter.mpr ⟨hjI, hjn,
          (abs_sub_le_of_abs_log_le hj0 hn0 hlog).trans (mul_le_mul_of_nonneg_left he_gap hn0.le)⟩
      exact (show ((nearRowIndices c N n).card : ℝ) ≤ _ by exact_mod_cast card_le_card hsub).trans
        (card_near_le (Icc 1 N) n hrad0)
    have hpt : ∀ j ∈ nearRowIndices c N n, 1 / ((n : ℝ) + j) ≤ 1 / (n : ℝ) := fun j _ =>
      one_div_le_one_div_of_le hn0 (le_add_of_nonneg_right (Nat.cast_nonneg j))
    calc
      (∑ j ∈ nearRowIndices c N n, 1 / ((n : ℝ) + j)) ≤
          ((nearRowIndices c N n).card : ℝ) * (1 / (n : ℝ)) := by
        rw [← nsmul_eq_mul, ← sum_const]; exact sum_le_sum hpt
      _ ≤ (2 * rad_n) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_right hcard_n (by positivity)
      _ = 4 * Real.exp 2 * (c / N) := by
        dsimp only [rad_n]; unfold linearNearRowRadius; field_simp [hn0.ne', hN0.ne']; ring
      _ ≤ 4 * Real.exp 2 := by nlinarith only [hw1, Real.exp_pos 2]
  -- Split `nearRowIndices c N n` into lower (`j < n`) and upper (`n < j`) halves.
  let S_lo := (nearRowIndices c N n).filter (· < n)
  let S_hi := (nearRowIndices c N n).filter (n < ·)
  have hsplit_S : nearRowIndices c N n = S_lo ∪ S_hi := by
    ext j; simp only [S_lo, S_hi, mem_union, mem_filter, nearRowIndices]
    constructor
    · rintro ⟨hjI, hjn, hlog⟩
      rcases lt_or_gt_of_ne hjn with h | h
      · exact Or.inl ⟨⟨hjI, hjn, hlog⟩, h⟩
      · exact Or.inr ⟨⟨hjI, hjn, hlog⟩, h⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj_S : Disjoint S_lo S_hi :=
    disjoint_left.mpr fun j h1 h2 => by
      have := (mem_filter.mp h1).2; have := (mem_filter.mp h2).2; omega
  -- Universal upper bound on `∑ 1 / |n - j|` via `K_rad = ⌊linearNearRowRadius c⌋₊`.
  have hdiff_univ : (∑ j ∈ nearRowIndices c N n, 1 / |(n : ℝ) - j|) ≤ 8 + 2 * Real.log c := by
    have hR1 : 1 ≤ linearNearRowRadius c := by
      unfold linearNearRowRadius
      have he2 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
      nlinarith only [hc1, he2]
    let K_rad := ⌊linearNearRowRadius c⌋₊
    have hK1 : 1 ≤ K_rad := Nat.le_floor (by exact_mod_cast hR1)
    have hKR : (K_rad : ℝ) ≤ linearNearRowRadius c := Nat.floor_le (by positivity)
    have hH_K : (∑ k ∈ Icc 1 K_rad, 1 / (k : ℝ)) ≤ 4 + Real.log c := by
      have hb := RHTower.sum_Icc_one_div_le hK1
      have hlogK : Real.log (K_rad : ℝ) ≤ 3 + Real.log c := by
        have hl := Real.log_le_log (by exact_mod_cast hK1) hKR
        unfold linearNearRowRadius at hl
        rw [Real.log_mul (by positivity) (Real.exp_pos 2).ne',
          Real.log_mul two_ne_zero hc0.ne', Real.log_exp] at hl
        have hl2 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos two_pos; linarith
        linarith only [hl, hl2]
      linarith only [hb, hlogK]
    have hdist_le_R : ∀ j ∈ nearRowIndices c N n, |(j : ℝ) - n| ≤ linearNearRowRadius c := by
      intro j hj
      obtain ⟨hjI, _, hlog⟩ := mem_filter.mp hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjI).1
      have he_gap : Real.exp (2 * c / N) - 1 ≤ linearNearRowRadius c / N := by
        calc
          Real.exp (2 * c / N) - 1 ≤ 2 * c / N * Real.exp (2 * c / N) := exp_sub_one_le_mul_exp
          _ ≤ 2 * c / N * Real.exp 2 :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (by
                have h := mul_le_mul_of_nonneg_left hw1 zero_le_two
                simpa only [mul_div_assoc, mul_one] using h)) (by positivity)
          _ = linearNearRowRadius c / N := by unfold linearNearRowRadius; ring
      have hn_le_N : (n : ℝ) ≤ N := by exact_mod_cast hnN
      calc
        |(j : ℝ) - n| ≤ (n : ℝ) * (linearNearRowRadius c / N) :=
          (abs_sub_le_of_abs_log_le hj0 hn0 hlog).trans (mul_le_mul_of_nonneg_left he_gap hn0.le)
        _ = linearNearRowRadius c * ((n : ℝ) / N) := by ring
        _ ≤ linearNearRowRadius c * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one hN0).mpr hn_le_N) (by positivity)
        _ = linearNearRowRadius c := mul_one _
    have hlo_le : (∑ j ∈ S_lo, 1 / |(n : ℝ) - j|) ≤ ∑ k ∈ Icc 1 K_rad, 1 / (k : ℝ) := by
      have himg : (∑ j ∈ S_lo, 1 / |(n : ℝ) - j|) =
          ∑ k ∈ S_lo.image (fun j => n - j), 1 / (k : ℝ) := by
        rw [sum_image]
        · refine sum_congr rfl fun j hj => ?_
          have hjn : j < n := (mem_filter.mp hj).2
          rw [abs_of_pos (sub_pos.mpr (by exact_mod_cast hjn : (j : ℝ) < n)),
            Nat.cast_sub hjn.le]
        · intro i hi j hj hij
          dsimp only at hij
          have := (mem_filter.mp hi).2; have := (mem_filter.mp hj).2; omega
      rw [himg]
      refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
      intro k hk
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
      have hjn : j < n := (mem_filter.mp hj).2
      have hd := hdist_le_R j (mem_filter.mp hj).1
      rw [abs_of_neg (sub_neg.mpr (by exact_mod_cast hjn : (j : ℝ) < n)), neg_sub] at hd
      exact mem_Icc.mpr ⟨by omega, Nat.le_floor (by rw [Nat.cast_sub hjn.le]; exact hd)⟩
    have hhi_le : (∑ j ∈ S_hi, 1 / |(n : ℝ) - j|) ≤ ∑ k ∈ Icc 1 K_rad, 1 / (k : ℝ) := by
      have himg : (∑ j ∈ S_hi, 1 / |(n : ℝ) - j|) =
          ∑ k ∈ S_hi.image (fun j => j - n), 1 / (k : ℝ) := by
        rw [sum_image]
        · refine sum_congr rfl fun j hj => ?_
          have hnj : n < j := (mem_filter.mp hj).2
          rw [abs_of_neg (sub_neg.mpr (by exact_mod_cast hnj : (n : ℝ) < j)), neg_sub,
            Nat.cast_sub hnj.le]
        · intro i hi j hj hij
          dsimp only at hij
          have := (mem_filter.mp hi).2; have := (mem_filter.mp hj).2; omega
      rw [himg]
      refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
      intro k hk
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
      have hnj : n < j := (mem_filter.mp hj).2
      have hd := hdist_le_R j (mem_filter.mp hj).1
      rw [abs_of_pos (sub_pos.mpr (by exact_mod_cast hnj : (n : ℝ) < j))] at hd
      exact mem_Icc.mpr ⟨by omega, Nat.le_floor (by rw [Nat.cast_sub hnj.le]; exact hd)⟩
    rw [hsplit_S, sum_union hdisj_S]
    linarith only [hlo_le, hhi_le, hH_K]
  constructor
  · -- Universal bound across all `n ∈ Icc 1 N`.
    rw [hker_eq, show Real.sqrt n * ((1 / 2 : ℝ) *
        ((∑ j ∈ nearRowIndices c N n, 1 / |(n : ℝ) - j|) +
          ∑ j ∈ nearRowIndices c N n, 1 / ((n : ℝ) + j))) - Real.log c * Real.sqrt n =
      Real.sqrt n * ((1 / 2 : ℝ) *
        ((∑ j ∈ nearRowIndices c N n, 1 / |(n : ℝ) - j|) +
          ∑ j ∈ nearRowIndices c N n, 1 / ((n : ℝ) + j)) - Real.log c) by ring,
      abs_mul, abs_of_pos hsn]
    have hdiff_nn : 0 ≤ ∑ j ∈ nearRowIndices c N n, 1 / |(n : ℝ) - j| :=
      sum_nonneg fun _ _ => by positivity
    have habs_mid : |(1 / 2 : ℝ) *
        ((∑ j ∈ nearRowIndices c N n, 1 / |(n : ℝ) - j|) +
          ∑ j ∈ nearRowIndices c N n, 1 / ((n : ℝ) + j)) - Real.log c| ≤
        (4 + 2 * Real.exp 2) * (1 + Real.log c) := by
      rw [abs_le]
      have hexp0 : 0 ≤ Real.exp 2 := (Real.exp_pos 2).le
      constructor <;> nlinarith only [hdiff_nn, hadd_sum.1, hdiff_univ, hadd_sum.2, hlogc0, hexp0]
    exact (mul_le_mul_of_nonneg_left habs_mid hsn.le).trans_eq (by ring)
  · -- Interior Zone 3 bound: exact cancellation of `Real.log c`.
    intro hn_lo hn_hi
    let w := 2 * c / N
    have hw0 : 0 < w := by dsimp only [w]; positivity
    have hw4 : w ≤ 1 / 4 := by
      dsimp only [w]
      rw [div_le_iff₀ hN0]
      linarith only [h8c]
    have hnw4 : 4 < (n : ℝ) * w := by
      dsimp only [w]
      have h1 : 2 * (N : ℝ) < n * c := (div_lt_iff₀ hc0).mp hn_lo
      rw [show (n : ℝ) * (2 * c / N) = 2 * (n * c) / N by ring, lt_div_iff₀ hN0]
      linarith only [h1]
    -- Upper half `S_hi = Icc (n + 1) U_n` with `c n / N ≤ U_n - n ≤ 6 c n / N`.
    let U_n := ⌊(n : ℝ) * Real.exp w⌋₊
    have hUn_N : U_n ≤ N := Nat.floor_le_of_le hn_hi
    have hexp_ge : 1 + w ≤ Real.exp w := by
      have := Real.add_one_le_exp w; linarith only [this]
    have hn_exp_gt : (n : ℝ) + 4 < (n : ℝ) * Real.exp w := by
      have h1 : (n : ℝ) * (1 + w) ≤ (n : ℝ) * Real.exp w :=
        mul_le_mul_of_nonneg_left hexp_ge hn0.le
      nlinarith only [h1, hnw4]
    have hn_lt_Un : n + 1 ≤ U_n := by
      have h1 : n + 4 ≤ U_n := by
        apply Nat.le_floor
        push_cast
        linarith only [hn_exp_gt]
      omega
    have hShi_eq : S_hi = Icc (n + 1) U_n := by
      ext j
      simp only [S_hi, nearRowIndices, mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨⟨_, _⟩, _, hlog⟩, hnj⟩
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
        have hnjR : (n : ℝ) < j := by exact_mod_cast hnj
        rw [abs_of_pos (sub_pos.mpr (Real.log_lt_log hn0 hnjR)),
          ← Real.log_div hj0.ne' hn0.ne'] at hlog
        have hdiv : (j : ℝ) / n ≤ Real.exp w := by
          rw [← Real.exp_log (div_pos hj0 hn0)]
          exact Real.exp_le_exp.mpr hlog
        have hj_ub : (j : ℝ) ≤ (n : ℝ) * Real.exp w := by
          linarith [(div_le_iff₀ hn0).mp hdiv, mul_comm (Real.exp w) (n : ℝ)]
        exact ⟨by omega, Nat.le_floor hj_ub⟩
      · rintro ⟨hn1j, hjU⟩
        have hnj : n < j := by omega
        have hj1 : 1 ≤ j := by omega
        have hjN : j ≤ N := hjU.trans hUn_N
        have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
        have hnjR : (n : ℝ) < j := by exact_mod_cast hnj
        have hj_le : (j : ℝ) ≤ (n : ℝ) * Real.exp w :=
          (by exact_mod_cast hjU : (j : ℝ) ≤ U_n).trans (Nat.floor_le (by positivity))
        have hlog : |Real.log (j : ℝ) - Real.log n| ≤ w := by
          rw [abs_of_pos (sub_pos.mpr (Real.log_lt_log hn0 hnjR)),
            ← Real.log_div hj0.ne' hn0.ne', ← Real.log_exp w]
          have hj_div : (j : ℝ) / n ≤ Real.exp w :=
            (div_le_iff₀ hn0).mpr (by linarith [hj_le, mul_comm (Real.exp w) (n : ℝ)])
          exact Real.log_le_log (div_pos hj0 hn0) hj_div
        exact ⟨⟨⟨hj1, hjN⟩, by omega, hlog⟩, hnj⟩
    let Δ_hi := U_n - n
    have hΔhi1 : 1 ≤ Δ_hi := by omega
    have hΔhi_bounds : c * (n : ℝ) / N ≤ Δ_hi ∧ (Δ_hi : ℝ) ≤ 6 * (c * (n : ℝ) / N) := by
      have hcast : (Δ_hi : ℝ) = (U_n : ℝ) - n := Nat.cast_sub (by omega : n ≤ U_n)
      rw [hcast]
      constructor
      · have hfl : (n : ℝ) * Real.exp w - 1 < U_n := Nat.sub_one_lt_floor _
        have h1 : (n : ℝ) * (1 + w) ≤ (n : ℝ) * Real.exp w :=
          mul_le_mul_of_nonneg_left hexp_ge hn0.le
        have h2 : (1 / 2 : ℝ) * ((n : ℝ) * w) = c * (n : ℝ) / N := by dsimp only [w]; ring
        linarith only [hfl, h1, hnw4, h2]
      · have hfl : (U_n : ℝ) ≤ (n : ℝ) * Real.exp w := Nat.floor_le (by positivity)
        have hexp_ub : Real.exp w - 1 ≤ 3 * w := by
          have h1 : Real.exp w - 1 ≤ w * Real.exp w := exp_sub_one_le_mul_exp
          have h2 : Real.exp w ≤ 3 :=
            (Real.exp_le_exp.mpr (hw4.trans (by norm_num : (1 / 4 : ℝ) ≤ 1))).trans
              (by have := Real.exp_one_lt_d9; linarith)
          nlinarith only [h1, h2, hw0]
        have h3 : (n : ℝ) * (Real.exp w - 1) ≤ (n : ℝ) * (3 * w) :=
          mul_le_mul_of_nonneg_left hexp_ub hn0.le
        have h4 : (n : ℝ) * (3 * w) = 6 * (c * (n : ℝ) / N) := by dsimp only [w]; ring
        linarith only [hfl, h3, h4]
    have hsum_hi : (∑ j ∈ S_hi, 1 / |(n : ℝ) - j|) = ∑ k ∈ Icc 1 Δ_hi, 1 / (k : ℝ) := by
      rw [hShi_eq]
      refine sum_bij (fun j _ => j - n) ?_ ?_ ?_ ?_
      · intro j hj; obtain ⟨h1, h2⟩ := mem_Icc.mp hj; exact mem_Icc.mpr ⟨by omega, by omega⟩
      · intro i hi j hj hij
        obtain ⟨_, _⟩ := mem_Icc.mp hi; obtain ⟨_, _⟩ := mem_Icc.mp hj; omega
      · intro k hk
        obtain ⟨h1, h2⟩ := mem_Icc.mp hk
        exact ⟨n + k, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro j hj
        have hnj : n ≤ j := by have := (mem_Icc.mp hj).1; omega
        rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hnj)), neg_sub, Nat.cast_sub hnj]
    -- Lower half `S_lo = Icc L_n (n - 1)` with `c n / N ≤ n - L_n ≤ 6 c n / N`.
    let L_n := ⌈(n : ℝ) * Real.exp (-w)⌉₊
    have hLn1 : 1 ≤ L_n := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
    have hexp_neg_ub : Real.exp (-w) ≤ 1 - (4 / 5 : ℝ) * w := by
      have hprod : Real.exp (-w) * (1 + w) ≤ 1 := by
        calc
          Real.exp (-w) * (1 + w) ≤ Real.exp (-w) * Real.exp w :=
            mul_le_mul_of_nonneg_left hexp_ge (Real.exp_pos _).le
          _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have halg : 1 ≤ (1 - (4 / 5 : ℝ) * w) * (1 + w) := by nlinarith only [hw0, hw4]
      have h1w : 0 < 1 + w := by linarith only [hw0]
      nlinarith only [hprod, halg, h1w]
    have hexp_neg_lb : 1 - w ≤ Real.exp (-w) := by
      have := Real.add_one_le_exp (-w); linarith only [this]
    have hLn_lt_n : L_n + 1 ≤ n := by
      have hceil : (L_n : ℝ) < (n : ℝ) * Real.exp (-w) + 1 := Nat.ceil_lt_add_one (by positivity)
      have h1 : (n : ℝ) * Real.exp (-w) ≤ (n : ℝ) * (1 - (4 / 5 : ℝ) * w) :=
        mul_le_mul_of_nonneg_left hexp_neg_ub hn0.le
      have hlt : (L_n : ℝ) + 1 < n := by nlinarith only [hceil, h1, hnw4]
      have hnat : L_n + 1 < n := by exact_mod_cast hlt
      omega
    have hSlo_eq : S_lo = Icc L_n (n - 1) := by
      ext j
      simp only [S_lo, nearRowIndices, mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨⟨hj1, _⟩, _, hlog⟩, hjn⟩
        have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
        have hjnR : (j : ℝ) < n := by exact_mod_cast hjn
        rw [abs_of_neg (sub_neg.mpr (Real.log_lt_log hj0 hjnR)), neg_sub,
          ← Real.log_div hn0.ne' hj0.ne'] at hlog
        have hdiv : (n : ℝ) / j ≤ Real.exp w := by
          rw [← Real.exp_log (div_pos hn0 hj0)]
          exact Real.exp_le_exp.mpr hlog
        have hmul : (n : ℝ) * Real.exp (-w) ≤ j := by
          have h1 : (n : ℝ) ≤ (j : ℝ) * Real.exp w := by
            linarith [(div_le_iff₀ hj0).mp hdiv, mul_comm (Real.exp w) (j : ℝ)]
          have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-w)).le
          rwa [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at h2
        exact ⟨Nat.ceil_le.mpr hmul, by omega⟩
      · rintro ⟨hLj, hjn1⟩
        have hjn : j < n := by omega
        have hj1 : 1 ≤ j := hLn1.trans hLj
        have hjN : j ≤ N := hjn.le.trans hnN
        have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
        have hjnR : (j : ℝ) < n := by exact_mod_cast hjn
        have hj_ge : (n : ℝ) * Real.exp (-w) ≤ j :=
          (Nat.le_ceil _).trans (by exact_mod_cast hLj)
        have hdiv : (n : ℝ) / j ≤ Real.exp w := by
          rw [div_le_iff₀ hj0]
          have h2 := mul_le_mul_of_nonneg_right hj_ge (Real.exp_pos w).le
          rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one,
            mul_comm (j : ℝ)] at h2
        have hlog : |Real.log (j : ℝ) - Real.log n| ≤ w := by
          rw [abs_of_neg (sub_neg.mpr (Real.log_lt_log hj0 hjnR)), neg_sub,
            ← Real.log_div hn0.ne' hj0.ne', ← Real.log_exp w]
          exact Real.log_le_log (div_pos hn0 hj0) hdiv
        exact ⟨⟨⟨hj1, hjN⟩, by omega, hlog⟩, hjn⟩
    let Δ_lo := n - L_n
    have hΔlo1 : 1 ≤ Δ_lo := by omega
    have hΔlo_bounds : c * (n : ℝ) / N ≤ Δ_lo ∧ (Δ_lo : ℝ) ≤ 6 * (c * (n : ℝ) / N) := by
      have hcast : (Δ_lo : ℝ) = (n : ℝ) - L_n := Nat.cast_sub (by omega : L_n ≤ n)
      rw [hcast]
      constructor
      · have hceil : (L_n : ℝ) < (n : ℝ) * Real.exp (-w) + 1 := Nat.ceil_lt_add_one (by positivity)
        have h1 : (n : ℝ) * Real.exp (-w) ≤ (n : ℝ) * (1 - (4 / 5 : ℝ) * w) :=
          mul_le_mul_of_nonneg_left hexp_neg_ub hn0.le
        have h2 : (1 / 2 : ℝ) * ((n : ℝ) * w) = c * (n : ℝ) / N := by dsimp only [w]; ring
        nlinarith only [hceil, h1, hnw4, h2]
      · have hceil : (n : ℝ) * Real.exp (-w) ≤ L_n := Nat.le_ceil _
        have h1 : (n : ℝ) * (1 - w) ≤ (n : ℝ) * Real.exp (-w) :=
          mul_le_mul_of_nonneg_left hexp_neg_lb hn0.le
        have h2 : (n : ℝ) * w = 2 * (c * (n : ℝ) / N) := by dsimp only [w]; ring
        have hcn0 : 0 ≤ c * (n : ℝ) / N := by positivity
        nlinarith only [hceil, h1, h2, hcn0]
    have hsum_lo : (∑ j ∈ S_lo, 1 / |(n : ℝ) - j|) = ∑ k ∈ Icc 1 Δ_lo, 1 / (k : ℝ) := by
      rw [hSlo_eq]
      refine sum_bij (fun j _ => n - j) ?_ ?_ ?_ ?_
      · intro j hj; obtain ⟨h1, h2⟩ := mem_Icc.mp hj; exact mem_Icc.mpr ⟨by omega, by omega⟩
      · intro i hi j hj hij
        obtain ⟨_, _⟩ := mem_Icc.mp hi; obtain ⟨_, _⟩ := mem_Icc.mp hj; omega
      · intro k hk
        obtain ⟨h1, h2⟩ := mem_Icc.mp hk
        exact ⟨n - k, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro j hj
        have hjn : j ≤ n := by have := (mem_Icc.mp hj).2; omega
        rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hjn)), Nat.cast_sub hjn]
    -- Combine harmonic bounds on `Δ_hi` and `Δ_lo` to cancel `Real.log c`.
    obtain ⟨hHhi_lo, hHhi_hi⟩ := log_le_sum_Icc_one_div_and_le hΔhi1
    obtain ⟨hHlo_lo, hHlo_hi⟩ := log_le_sum_Icc_one_div_and_le hΔlo1
    have hcn_pos : 0 < c * (n : ℝ) / N := by positivity
    have hlog6 : Real.log 6 ≤ 5 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6); linarith
    have hhi_log_lo : Real.log c - Real.log ((N : ℝ) / n) ≤ ∑ j ∈ S_hi, 1 / |(n : ℝ) - j| := by
      rw [hsum_hi]
      have hl := Real.log_le_log hcn_pos hΔhi_bounds.1
      have heq : Real.log (c * (n : ℝ) / N) = Real.log c - Real.log ((N : ℝ) / n) := by
        rw [Real.log_div (mul_pos hc0 hn0).ne' hN0.ne', Real.log_mul hc0.ne' hn0.ne',
          Real.log_div hN0.ne' hn0.ne']
        ring
      linarith only [hl, hHhi_lo, heq]
    have hdiv_log : Real.log ((N : ℝ) / n) = Real.log N - Real.log n :=
      Real.log_div hN0.ne' hn0.ne'
    have hhi_log_hi : (∑ j ∈ S_hi, 1 / |(n : ℝ) - j|) ≤
        6 + Real.log c - Real.log ((N : ℝ) / n) := by
      rw [hsum_hi]
      have hl := Real.log_le_log (by exact_mod_cast hΔhi1) hΔhi_bounds.2
      rw [Real.log_mul (by norm_num) hcn_pos.ne',
        Real.log_div (mul_pos hc0 hn0).ne' hN0.ne', Real.log_mul hc0.ne' hn0.ne'] at hl
      linarith only [hl, hHhi_hi, hlog6, hdiv_log]
    have hlo_log_lo : Real.log c - Real.log ((N : ℝ) / n) ≤ ∑ j ∈ S_lo, 1 / |(n : ℝ) - j| := by
      rw [hsum_lo]
      have hl := Real.log_le_log hcn_pos hΔlo_bounds.1
      have heq : Real.log (c * (n : ℝ) / N) = Real.log c - Real.log ((N : ℝ) / n) := by
        rw [Real.log_div (mul_pos hc0 hn0).ne' hN0.ne', Real.log_mul hc0.ne' hn0.ne',
          Real.log_div hN0.ne' hn0.ne']
        ring
      linarith only [hl, hHlo_lo, heq]
    have hlo_log_hi : (∑ j ∈ S_lo, 1 / |(n : ℝ) - j|) ≤
        6 + Real.log c - Real.log ((N : ℝ) / n) := by
      rw [hsum_lo]
      have hl := Real.log_le_log (by exact_mod_cast hΔlo1) hΔlo_bounds.2
      rw [Real.log_mul (by norm_num) hcn_pos.ne',
        Real.log_div (mul_pos hc0 hn0).ne' hN0.ne', Real.log_mul hc0.ne' hn0.ne'] at hl
      linarith only [hl, hHlo_hi, hlog6, hdiv_log]
    have hlog_Nn_nn : 0 ≤ Real.log ((N : ℝ) / n) :=
      Real.log_nonneg ((one_le_div hn0).mpr (by exact_mod_cast hnN))
    have habs_int : |(1 / 2 : ℝ) *
        ((∑ j ∈ nearRowIndices c N n, 1 / |(n : ℝ) - j|) +
          ∑ j ∈ nearRowIndices c N n, 1 / ((n : ℝ) + j)) - Real.log c| ≤
        (6 + 2 * Real.exp 2) * (1 + Real.log ((N : ℝ) / n)) := by
      rw [hsplit_S, sum_union hdisj_S, abs_le]
      have hexp0 : 0 ≤ Real.exp 2 := (Real.exp_pos 2).le
      have hprod_nn : 0 ≤ Real.exp 2 * Real.log ((N : ℝ) / n) := mul_nonneg hexp0 hlog_Nn_nn
      constructor <;>
        linarith only [hlo_log_lo, hlo_log_hi, hhi_log_lo, hhi_log_hi,
          hadd_sum.1, hadd_sum.2, hlog_Nn_nn, hexp0, hprod_nn]
    have hlog_sqrt : 1 + Real.log ((N : ℝ) / n) ≤ 2 * (Real.sqrt N / Real.sqrt n) := by
      rw [← Real.sqrt_div hN0.le]
      exact one_add_log_le_two_sqrt_pos (div_pos hN0 hn0)
    rw [hker_eq, show Real.sqrt n * ((1 / 2 : ℝ) *
        ((∑ j ∈ nearRowIndices c N n, 1 / |(n : ℝ) - j|) +
          ∑ j ∈ nearRowIndices c N n, 1 / ((n : ℝ) + j))) - Real.log c * Real.sqrt n =
      Real.sqrt n * ((1 / 2 : ℝ) *
        ((∑ j ∈ nearRowIndices c N n, 1 / |(n : ℝ) - j|) +
          ∑ j ∈ nearRowIndices c N n, 1 / ((n : ℝ) + j)) - Real.log c) by ring,
      abs_mul, abs_of_pos hsn]
    calc
      Real.sqrt n * |_| ≤ Real.sqrt n * ((6 + 2 * Real.exp 2) * (2 * (Real.sqrt N / Real.sqrt n))) :=
        mul_le_mul_of_nonneg_left
          (habs_int.trans (mul_le_mul_of_nonneg_left hlog_sqrt (by positivity))) hsn.le
      _ = 2 * (6 + 2 * Real.exp 2) * Real.sqrt N := by field_simp [hsn.ne']

/-- Three-zone `L^2` and bilinear bounds on `(completeWeilPoleShift φ c / N)` times the ground-mode
center-collar difference `∑_{j ∈ nearRowIndices c N n} archimedeanCenterKernel n j / √j - log c * √n`. -/
private lemma centerPoleCollar_sum_bounds (φ : ℝ → ℝ) :
    ∃ C_cp : ℝ, 0 < C_cp ∧
      ∀ {N : ℕ} {c : ℝ},
        1 ≤ c → 1 ≤ Real.log (N : ℝ) → 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        (∑ n ∈ Icc 1 N,
            ((completeWeilPoleShift φ c / N) *
              ((∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) -
                Real.log c * Real.sqrt n)) ^ 2) / Real.log N ≤
          C_cp * (c ^ 2 / Real.log N + c ^ 4 / (N * Real.log N)) ∧
        ∀ {l : ℕ}, 0 < l →
          |(Real.sqrt (Real.log N))⁻¹ *
              ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
                ((completeWeilPoleShift φ c / N) *
                  ((∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) -
                    Real.log c * Real.sqrt n))| ≤
            C_cp * Real.sqrt l * (c / Real.log N + c ^ 3 / N) := by
  let S₁ := |completeWeilPoleShift φ 1|
  let C_u := 4 + 2 * Real.exp 2
  let C_i := 2 * (6 + 2 * Real.exp 2)
  let C_sq := 16 * S₁ ^ 2 * C_u ^ 2 + S₁ ^ 2 * C_i ^ 2 + 4 * (2 * Real.exp 2 + 1) * S₁ ^ 2 * C_u ^ 2
  let C_bi := 4 * S₁ * C_u + 2 * S₁ * C_i + 4 * (2 * Real.exp 2 + 1) * S₁ * C_u
  refine ⟨C_sq + C_bi + 1, by dsimp only [C_sq, C_bi, C_u, C_i, S₁]; positivity, ?_⟩
  intro N c hc1 hL1 hradN
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hsL0 : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hL0
  have he2_ge4 : (4 : ℝ) ≤ Real.exp 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have hp : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [h2, hp]
  have h8c : 8 * c ≤ N := by
    unfold linearNearRowRadius at hradN
    have h1 : 8 * c ≤ 2 * c * Real.exp 2 := by nlinarith only [hc0, he2_ge4]
    have h2 : 8 * c ≤ (2 * c * Real.exp 2 + 1) ^ 2 := by nlinarith only [h1, hc1]
    linarith only [h2, hradN]
  have hCu_0 : 0 ≤ C_u := by dsimp only [C_u]; positivity
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith only [hc1, h8c]
    exact_mod_cast this
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hw1 : c / N ≤ 1 := (div_le_one hN0).mpr (by linarith only [hc0, h8c])
  have hshift_eq : completeWeilPoleShift φ c = c * completeWeilPoleShift φ 1 := by
    unfold completeWeilPoleShift; ring
  have hshift_le : |completeWeilPoleShift φ c| ≤ S₁ * c := by
    rw [hshift_eq, abs_mul, abs_of_pos hc0]; dsimp only [S₁]; linarith
  have h1c_le : 1 + Real.log c ≤ 2 * Real.sqrt c := one_add_log_le_two_sqrt_pos hc0
  have h1c_sq : (1 + Real.log c) ^ 2 ≤ 4 * c := by
    have h := pow_le_pow_left₀ (by linarith [Real.log_nonneg hc1]) h1c_le 2
    rwa [mul_pow, Real.sq_sqrt hc0.le, show (2 : ℝ) ^ 2 = 4 by norm_num] at h
  have hsc_le_c : Real.sqrt c ≤ c := by
    calc
      Real.sqrt c ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt (by nlinarith only [hc1])
      _ = c := Real.sqrt_sq hc0.le
  have h1c_c : 1 + Real.log c ≤ 2 * c := h1c_le.trans (by linarith only [hsc_le_c])
  -- Partition `Icc 1 N` into Zone 1 (`n ≤ 2 N / c`), Zone 2 (`n > 2 N / c ∧ N < n exp(2c/N)`),
  -- and Zone 3 (`n > 2 N / c ∧ n exp(2c/N) ≤ N`).
  let Z₁ := (Icc 1 N).filter (fun n : ℕ => (n : ℝ) ≤ 2 * (N : ℝ) / c)
  let Z₂ := (Icc 1 N).filter (fun n : ℕ => 2 * (N : ℝ) / c < n ∧ (N : ℝ) < n * Real.exp (2 * c / N))
  let Z₃ := (Icc 1 N).filter (fun n : ℕ => 2 * (N : ℝ) / c < n ∧ (n : ℝ) * Real.exp (2 * c / N) ≤ N)
  have hZ1_sub : Z₁ ⊆ Icc 1 ⌊2 * (N : ℝ) / c⌋₊ := fun n hn => by
    obtain ⟨hnI, hle⟩ := mem_filter.mp hn
    exact mem_Icc.mpr ⟨(mem_Icc.mp hnI).1, Nat.le_floor hle⟩
  have hZ1_sum_n : (∑ n ∈ Z₁, (n : ℝ)) ≤ 4 * (N : ℝ) ^ 2 / c ^ 2 := by
    let a := ⌊2 * (N : ℝ) / c⌋₊
    have ha_le : (a : ℝ) ≤ 2 * (N : ℝ) / c := Nat.floor_le (by positivity)
    calc
      (∑ n ∈ Z₁, (n : ℝ)) ≤ ∑ n ∈ Icc 1 a, (n : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hZ1_sub fun _ _ _ => Nat.cast_nonneg _
      _ ≤ ∑ _n ∈ Icc 1 a, (a : ℝ) := sum_le_sum fun n hn => by exact_mod_cast (mem_Icc.mp hn).2
      _ = (a : ℝ) ^ 2 := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
      _ ≤ (2 * (N : ℝ) / c) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg a) ha_le 2
      _ = 4 * (N : ℝ) ^ 2 / c ^ 2 := by ring
  have hZ1_card : (Z₁.card : ℝ) ≤ 2 * (N : ℝ) / c := by
    calc
      (Z₁.card : ℝ) ≤ ((Icc 1 ⌊2 * (N : ℝ) / c⌋₊).card : ℝ) := by
        exact_mod_cast card_le_card hZ1_sub
      _ = (⌊2 * (N : ℝ) / c⌋₊ : ℝ) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
      _ ≤ 2 * (N : ℝ) / c := Nat.floor_le (by positivity)
  -- Top strip Zone 2 has `N - ⌊linearNearRowRadius c⌋₊ ≤ n ≤ N`, hence `card ≤ (2 e^2 + 1) c`
  -- and `N ≤ 2 n`.
  have hZ2_sub : Z₂ ⊆ Icc (N - ⌊linearNearRowRadius c⌋₊) N := by
    intro n hn
    obtain ⟨hnI, _, htop⟩ := mem_filter.mp hn
    have hnN := (mem_Icc.mp hnI).2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hnI).1
    have he_gap : Real.exp (2 * c / N) - 1 ≤ linearNearRowRadius c / N := by
      calc
        Real.exp (2 * c / N) - 1 ≤ 2 * c / N * Real.exp (2 * c / N) := exp_sub_one_le_mul_exp
        _ ≤ 2 * c / N * Real.exp 2 :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by
              have h := mul_le_mul_of_nonneg_left hw1 zero_le_two
              simpa only [mul_div_assoc, mul_one] using h)) (by positivity)
        _ = linearNearRowRadius c / N := by unfold linearNearRowRadius; ring
    have hdiff : (N : ℝ) - n < linearNearRowRadius c := by
      have h1 : (N : ℝ) - n < (n : ℝ) * (Real.exp (2 * c / N) - 1) := by linarith only [htop]
      have h2 : (n : ℝ) * (Real.exp (2 * c / N) - 1) ≤ (N : ℝ) * (linearNearRowRadius c / N) :=
        mul_le_mul (by exact_mod_cast hnN) he_gap
          (sub_nonneg.mpr (Real.one_le_exp (by positivity))) hN0.le
      have h3 : (N : ℝ) * (linearNearRowRadius c / N) = linearNearRowRadius c := by
        field_simp [hN0.ne']
      linarith only [h1, h2, h3]
    have hnat : N - n ≤ ⌊linearNearRowRadius c⌋₊ :=
      Nat.le_floor (by rw [Nat.cast_sub hnN]; exact hdiff.le)
    exact mem_Icc.mpr ⟨by omega, hnN⟩
  have hZ2_card : (Z₂.card : ℝ) ≤ (2 * Real.exp 2 + 1) * c := by
    have hnat : Z₂.card ≤ ⌊linearNearRowRadius c⌋₊ + 1 := by
      have h := card_le_card hZ2_sub; rw [Nat.card_Icc] at h; omega
    have hcast : (Z₂.card : ℝ) ≤ (⌊linearNearRowRadius c⌋₊ : ℝ) + 1 := by exact_mod_cast hnat
    have hfl : (⌊linearNearRowRadius c⌋₊ : ℝ) ≤ 2 * c * Real.exp 2 := by
      unfold linearNearRowRadius; exact Nat.floor_le (by positivity)
    nlinarith only [hcast, hfl, hc1]
  have hZ2_half : ∀ n ∈ Z₂, N ≤ 2 * n := by
    intro n hn
    have hlo := (mem_Icc.mp (hZ2_sub hn)).1
    have h2R_N : 2 * ⌊linearNearRowRadius c⌋₊ ≤ N := by
      have hfl : (⌊linearNearRowRadius c⌋₊ : ℝ) ≤ linearNearRowRadius c :=
        Nat.floor_le (by unfold linearNearRowRadius; positivity)
      have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      have hR : 2 * (⌊linearNearRowRadius c⌋₊ : ℝ) ≤ N := by nlinarith only [hfl, h0, hradN]
      exact_mod_cast hR
    omega
  -- Disjoint union `Icc 1 N = Z₁ ∪ (Z₂ ∪ Z₃)`.
  have hpart : ∀ f : ℕ → ℝ, (∑ n ∈ Icc 1 N, f n) =
      (∑ n ∈ Z₁, f n) + (∑ n ∈ Z₂, f n) + (∑ n ∈ Z₃, f n) := by
    intro f
    have hd1 : Disjoint Z₁ (Z₂ ∪ Z₃) := disjoint_left.mpr fun n h1 h23 => by
      have ha := (mem_filter.mp h1).2
      rcases mem_union.mp h23 with h2 | h3
      · linarith [(mem_filter.mp h2).2.1]
      · linarith [(mem_filter.mp h3).2.1]
    have hd2 : Disjoint Z₂ Z₃ := disjoint_left.mpr fun n h2 h3 =>
      lt_irrefl _ ((mem_filter.mp h2).2.2.trans_le (mem_filter.mp h3).2.2)
    have hu : Icc 1 N = Z₁ ∪ (Z₂ ∪ Z₃) := by
      ext n; simp only [Z₁, Z₂, Z₃, mem_union, mem_filter]
      constructor
      · intro hn
        rcases le_or_gt (n : ℝ) (2 * (N : ℝ) / c) with h1 | h1
        · exact Or.inl ⟨hn, h1⟩
        · rcases lt_or_ge (N : ℝ) ((n : ℝ) * Real.exp (2 * c / N)) with h2 | h2
          · exact Or.inr (Or.inl ⟨hn, h1, h2⟩)
          · exact Or.inr (Or.inr ⟨hn, h1, h2⟩)
      · rintro (⟨hn, _⟩ | ⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn
    rw [hu, sum_union hd1, sum_union hd2, add_assoc]
  let D_row : ℕ → ℝ := fun n =>
    (∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) -
      Real.log c * Real.sqrt n
  constructor
  · -- Part 1: `L^2` squared sum across Zones 1, 2, 3.
    have hs1 : (∑ n ∈ Z₁, ((completeWeilPoleShift φ c / N) * D_row n) ^ 2) ≤
        16 * S₁ ^ 2 * C_u ^ 2 * c ^ 2 := by
      have hpt : ∀ n ∈ Z₁, ((completeWeilPoleShift φ c / N) * D_row n) ^ 2 ≤
          (S₁ ^ 2 * C_u ^ 2 * (4 * c ^ 3) / (N : ℝ) ^ 2) * (n : ℝ) := by
        intro n hn
        have hnI := (mem_filter.mp hn).1
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hu : |D_row n| ≤ C_u * (1 + Real.log c) * Real.sqrt n :=
          (abs_centerPoleCollar_diff_le hc1 h8c hnI).1
        have hprod : |(completeWeilPoleShift φ c / N) * D_row n| ≤
            (S₁ * c / N) * (C_u * (1 + Real.log c) * Real.sqrt n) := by
          rw [abs_mul, abs_div, abs_of_pos hN0]
          exact mul_le_mul (div_le_div_of_nonneg_right hshift_le hN0.le) hu
            (abs_nonneg _) (by dsimp only [S₁]; positivity)
        have hsq : ((completeWeilPoleShift φ c / N) * D_row n) ^ 2 ≤
            S₁ ^ 2 * c ^ 2 / (N : ℝ) ^ 2 * (C_u ^ 2 * (1 + Real.log c) ^ 2 * n) := by
          have h := pow_le_pow_left₀ (abs_nonneg _) hprod 2
          rwa [sq_abs, mul_pow (S₁ * c / N), div_pow, mul_pow S₁ c,
            mul_pow (C_u * (1 + Real.log c)), mul_pow C_u, Real.sq_sqrt hn0] at h
        calc
          ((completeWeilPoleShift φ c / N) * D_row n) ^ 2
              ≤ S₁ ^ 2 * c ^ 2 / (N : ℝ) ^ 2 * (C_u ^ 2 * (4 * c) * n) :=
            hsq.trans (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h1c_sq (sq_nonneg C_u)) hn0)
              (by dsimp only [S₁]; positivity))
          _ = (S₁ ^ 2 * C_u ^ 2 * (4 * c ^ 3) / (N : ℝ) ^ 2) * (n : ℝ) := by ring
      calc
        _ ≤ (S₁ ^ 2 * C_u ^ 2 * (4 * c ^ 3) / (N : ℝ) ^ 2) * ∑ n ∈ Z₁, (n : ℝ) := by
          rw [mul_sum]; exact sum_le_sum hpt
        _ ≤ (S₁ ^ 2 * C_u ^ 2 * (4 * c ^ 3) / (N : ℝ) ^ 2) * (4 * (N : ℝ) ^ 2 / c ^ 2) :=
          mul_le_mul_of_nonneg_left hZ1_sum_n (by dsimp only [S₁, C_u]; positivity)
        _ = 16 * S₁ ^ 2 * C_u ^ 2 * c := by field_simp [hN0.ne', hc0.ne']; ring
        _ ≤ 16 * S₁ ^ 2 * C_u ^ 2 * c ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith only [hc1] : c ≤ c ^ 2)
            (by dsimp only [S₁, C_u]; positivity)
    have hs2 : (∑ n ∈ Z₂, ((completeWeilPoleShift φ c / N) * D_row n) ^ 2) ≤
        4 * (2 * Real.exp 2 + 1) * S₁ ^ 2 * C_u ^ 2 * c ^ 4 / N := by
      have hpt : ∀ n ∈ Z₂, ((completeWeilPoleShift φ c / N) * D_row n) ^ 2 ≤
          4 * S₁ ^ 2 * C_u ^ 2 * c ^ 3 / N := by
        intro n hn
        have hnI := (mem_filter.mp hn).1
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hnI).2
        have hu : |D_row n| ≤ C_u * (1 + Real.log c) * Real.sqrt n :=
          (abs_centerPoleCollar_diff_le hc1 h8c hnI).1
        have hprod : |(completeWeilPoleShift φ c / N) * D_row n| ≤
            (S₁ * c / N) * (C_u * (1 + Real.log c) * Real.sqrt N) := by
          rw [abs_mul, abs_div, abs_of_pos hN0]
          have h1c0 : 0 ≤ C_u * (1 + Real.log c) :=
            mul_nonneg hCu_0 (by linarith [Real.log_nonneg hc1])
          exact mul_le_mul (div_le_div_of_nonneg_right hshift_le hN0.le)
            (hu.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnN) h1c0))
            (abs_nonneg _) (by dsimp only [S₁]; positivity)
        have hsq : ((completeWeilPoleShift φ c / N) * D_row n) ^ 2 ≤
            S₁ ^ 2 * c ^ 2 / (N : ℝ) ^ 2 * (C_u ^ 2 * (1 + Real.log c) ^ 2 * N) := by
          have h := pow_le_pow_left₀ (abs_nonneg _) hprod 2
          rwa [sq_abs, mul_pow (S₁ * c / N), div_pow, mul_pow S₁ c,
            mul_pow (C_u * (1 + Real.log c)), mul_pow C_u, Real.sq_sqrt hN0.le] at h
        calc
          ((completeWeilPoleShift φ c / N) * D_row n) ^ 2
              ≤ S₁ ^ 2 * c ^ 2 / (N : ℝ) ^ 2 * (C_u ^ 2 * (4 * c) * N) :=
            hsq.trans (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h1c_sq (sq_nonneg C_u)) hN0.le)
              (by dsimp only [S₁]; positivity))
          _ = 4 * S₁ ^ 2 * C_u ^ 2 * c ^ 3 / N := by field_simp [hN0.ne']; ring
      calc
        _ ≤ (Z₂.card : ℝ) * (4 * S₁ ^ 2 * C_u ^ 2 * c ^ 3 / N) := by
          rw [← nsmul_eq_mul, ← sum_const]; exact sum_le_sum hpt
        _ ≤ ((2 * Real.exp 2 + 1) * c) * (4 * S₁ ^ 2 * C_u ^ 2 * c ^ 3 / N) :=
          mul_le_mul_of_nonneg_right hZ2_card (by dsimp only [S₁, C_u]; positivity)
        _ = 4 * (2 * Real.exp 2 + 1) * S₁ ^ 2 * C_u ^ 2 * c ^ 4 / N := by ring
    have hs3 : (∑ n ∈ Z₃, ((completeWeilPoleShift φ c / N) * D_row n) ^ 2) ≤
        S₁ ^ 2 * C_i ^ 2 * c ^ 2 := by
      have hpt : ∀ n ∈ Z₃, ((completeWeilPoleShift φ c / N) * D_row n) ^ 2 ≤
          S₁ ^ 2 * C_i ^ 2 * c ^ 2 / N := by
        intro n hn
        obtain ⟨hnI, hlo, hhi⟩ := mem_filter.mp hn
        have hi := (abs_centerPoleCollar_diff_le hc1 h8c hnI).2 hlo hhi
        have hprod : |(completeWeilPoleShift φ c / N) * D_row n| ≤
            (S₁ * c / N) * (C_i * Real.sqrt N) := by
          rw [abs_mul, abs_div, abs_of_pos hN0]
          exact mul_le_mul (div_le_div_of_nonneg_right hshift_le hN0.le) hi
            (abs_nonneg _) (by dsimp only [S₁]; positivity)
        have hsq : ((completeWeilPoleShift φ c / N) * D_row n) ^ 2 ≤
            S₁ ^ 2 * c ^ 2 / (N : ℝ) ^ 2 * (C_i ^ 2 * N) := by
          have h := pow_le_pow_left₀ (abs_nonneg _) hprod 2
          rwa [sq_abs, mul_pow (S₁ * c / N), div_pow, mul_pow S₁ c, mul_pow C_i,
            Real.sq_sqrt hN0.le] at h
        exact hsq.trans_eq (by field_simp [hN0.ne']; ring)
      have hcard_Z3 : (Z₃.card : ℝ) ≤ N := by
        have h : Z₃.card ≤ (Icc 1 N).card := card_le_card (filter_subset _ _)
        rw [Nat.card_Icc, Nat.add_sub_cancel] at h
        exact_mod_cast h
      calc
        _ ≤ (Z₃.card : ℝ) * (S₁ ^ 2 * C_i ^ 2 * c ^ 2 / N) := by
          rw [← nsmul_eq_mul, ← sum_const]; exact sum_le_sum hpt
        _ ≤ (N : ℝ) * (S₁ ^ 2 * C_i ^ 2 * c ^ 2 / N) :=
          mul_le_mul_of_nonneg_right hcard_Z3 (by dsimp only [S₁, C_i]; positivity)
        _ = S₁ ^ 2 * C_i ^ 2 * c ^ 2 := by field_simp [hN0.ne']
    rw [hpart]
    have hsum_le : ((∑ n ∈ Z₁, ((completeWeilPoleShift φ c / N) * D_row n) ^ 2) +
          (∑ n ∈ Z₂, ((completeWeilPoleShift φ c / N) * D_row n) ^ 2) +
          (∑ n ∈ Z₃, ((completeWeilPoleShift φ c / N) * D_row n) ^ 2)) / Real.log N ≤
        C_sq * (c ^ 2 / Real.log N + c ^ 4 / (N * Real.log N)) := by
      rw [add_div, add_div]
      have hd1 := div_le_div_of_nonneg_right hs1 hL0.le
      have hd2 : (∑ n ∈ Z₂, ((completeWeilPoleShift φ c / N) * D_row n) ^ 2) / Real.log N ≤
          4 * (2 * Real.exp 2 + 1) * S₁ ^ 2 * C_u ^ 2 * (c ^ 4 / (N * Real.log N)) :=
        (div_le_div_of_nonneg_right hs2 hL0.le).trans_eq (by ring)
      have hd3 := div_le_div_of_nonneg_right hs3 hL0.le
      have hnn1 : 0 ≤ 4 * (2 * Real.exp 2 + 1) * S₁ ^ 2 * C_u ^ 2 * (c ^ 2 / Real.log N) := by
        dsimp only [S₁, C_u]; positivity
      have hnn2 : 0 ≤ (16 * S₁ ^ 2 * C_u ^ 2 + S₁ ^ 2 * C_i ^ 2) * (c ^ 4 / (N * Real.log N)) := by
        dsimp only [S₁, C_u, C_i]; positivity
      dsimp only [C_sq]
      linarith only [hd1, hd2, hd3, hnn1, hnn2,
        (by ring : (16 * S₁ ^ 2 * C_u ^ 2 + S₁ ^ 2 * C_i ^ 2 +
            4 * (2 * Real.exp 2 + 1) * S₁ ^ 2 * C_u ^ 2) *
          (c ^ 2 / Real.log N + c ^ 4 / (N * Real.log N)) =
          16 * S₁ ^ 2 * C_u ^ 2 * c ^ 2 / Real.log N +
            S₁ ^ 2 * C_i ^ 2 * c ^ 2 / Real.log N +
            4 * (2 * Real.exp 2 + 1) * S₁ ^ 2 * C_u ^ 2 * (c ^ 4 / (N * Real.log N)) +
            4 * (2 * Real.exp 2 + 1) * S₁ ^ 2 * C_u ^ 2 * (c ^ 2 / Real.log N) +
            (16 * S₁ ^ 2 * C_u ^ 2 + S₁ ^ 2 * C_i ^ 2) * (c ^ 4 / (N * Real.log N)))]
    refine hsum_le.trans ?_
    have : 0 ≤ C_bi := by dsimp only [C_bi, S₁, C_u, C_i]; positivity
    exact mul_le_mul_of_nonneg_right (by linarith only [this]) (by positivity)
  · -- Part 2: Bilinear pairing bound against `v_l` across Zones 1, 2, 3.
    intro l hl
    have hb1 : |(Real.sqrt (Real.log N))⁻¹ *
        ∑ n ∈ Z₁, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          ((completeWeilPoleShift φ c / N) * D_row n)| ≤
        4 * S₁ * C_u * Real.sqrt l * (c / Real.log N) := by
      have hpt : ∀ n ∈ Z₁,
          |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              ((completeWeilPoleShift φ c / N) * D_row n)| ≤
            2 * S₁ * C_u * Real.sqrt l * c ^ 2 / (N * Real.sqrt (Real.log N)) := by
        intro n hn
        have hnI := (mem_filter.mp hn).1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hnI).1
        have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
        have hu : |D_row n| ≤ C_u * (1 + Real.log c) * Real.sqrt n :=
          (abs_centerPoleCollar_diff_le hc1 h8c hnI).1
        have hvl_n : |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n| ≤
            Real.sqrt l / (Real.sqrt n * Real.sqrt (Real.log N)) := by
          rw [primeHorizonExtension_normalizedRamanujan hnI]
          unfold ramanujanPoleProfile
          rw [abs_mul, abs_div, abs_of_pos (inv_pos.mpr hsL0), abs_of_pos hsn]
          exact (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (abs_mode_le_sqrt_conductor hl n) hsn.le)
            (by positivity)).trans_eq (by ring)
        have hD : |(completeWeilPoleShift φ c / N) * D_row n| ≤
            2 * S₁ * C_u * c ^ 2 * Real.sqrt n / N := by
          rw [abs_mul, abs_div, abs_of_pos hN0]
          calc
            (|completeWeilPoleShift φ c| / N) * |D_row n|
                ≤ (S₁ * c / N) * (C_u * (2 * c) * Real.sqrt n) :=
              mul_le_mul (div_le_div_of_nonneg_right hshift_le hN0.le)
                (hu.trans (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left h1c_c hCu_0) hsn.le))
                (abs_nonneg _) (by dsimp only [S₁]; positivity)
            _ = 2 * S₁ * C_u * c ^ 2 * Real.sqrt n / N := by ring
        rw [abs_mul]
        calc
          _ ≤ (Real.sqrt l / (Real.sqrt n * Real.sqrt (Real.log N))) *
                (2 * S₁ * C_u * c ^ 2 * Real.sqrt n / N) :=
            mul_le_mul hvl_n hD (abs_nonneg _) (by positivity)
          _ = 2 * S₁ * C_u * Real.sqrt l * c ^ 2 / (N * Real.sqrt (Real.log N)) := by
            field_simp [hsn.ne', hsL0.ne', hN0.ne']
      rw [abs_mul, abs_of_pos (inv_pos.mpr hsL0)]
      calc
        _ ≤ (Real.sqrt (Real.log N))⁻¹ *
              ((Z₁.card : ℝ) * (2 * S₁ * C_u * Real.sqrt l * c ^ 2 /
                (N * Real.sqrt (Real.log N)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← nsmul_eq_mul, ← sum_const]
          exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)
        _ ≤ (Real.sqrt (Real.log N))⁻¹ *
              ((2 * (N : ℝ) / c) * (2 * S₁ * C_u * Real.sqrt l * c ^ 2 /
                (N * Real.sqrt (Real.log N)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hZ1_card (by dsimp only [S₁, C_u]; positivity))
            (by positivity)
        _ = 4 * S₁ * C_u * Real.sqrt l * (c / Real.log N) := by
          field_simp [hsL0.ne', hL0.ne', hN0.ne', hc0.ne']
          rw [Real.sq_sqrt hL0.le]; ring
    have hb2 : |(Real.sqrt (Real.log N))⁻¹ *
        ∑ n ∈ Z₂, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          ((completeWeilPoleShift φ c / N) * D_row n)| ≤
        4 * (2 * Real.exp 2 + 1) * S₁ * C_u * Real.sqrt l * (c ^ 3 / N) := by
      have hpt : ∀ n ∈ Z₂,
          |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              ((completeWeilPoleShift φ c / N) * D_row n)| ≤
            4 * S₁ * C_u * Real.sqrt l * c ^ 2 / (N * Real.sqrt (Real.log N)) := by
        intro n hn
        have hnI := (mem_filter.mp hn).1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hnI).1
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hnI).2
        have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
        have hn_half := hZ2_half n hn
        have hinv_sn : 1 / Real.sqrt n ≤ 2 / Real.sqrt N := by
          rw [div_le_div_iff₀ hsn hsN, one_mul]
          calc
            Real.sqrt (N : ℝ) ≤ Real.sqrt (4 * (n : ℝ)) :=
              Real.sqrt_le_sqrt (by exact_mod_cast (by omega : N ≤ 4 * n))
            _ = 2 * Real.sqrt n := by
              rw [Real.sqrt_mul (by norm_num),
                show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
        have hvl_n : |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n| ≤
            2 * Real.sqrt l / (Real.sqrt N * Real.sqrt (Real.log N)) := by
          rw [primeHorizonExtension_normalizedRamanujan hnI]
          unfold ramanujanPoleProfile
          rw [abs_mul, abs_div, abs_of_pos (inv_pos.mpr hsL0), abs_of_pos hsn]
          calc
            (Real.sqrt (Real.log N))⁻¹ * (|normalizedRamanujanMode l n| / Real.sqrt n)
                ≤ (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt l * (2 / Real.sqrt N)) := by
              rw [div_eq_mul_one_div]
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul (abs_mode_le_sqrt_conductor hl n) hinv_sn
                  (by positivity) (Real.sqrt_nonneg _))
                (by positivity)
            _ = 2 * Real.sqrt l / (Real.sqrt N * Real.sqrt (Real.log N)) := by ring
        have hu : |D_row n| ≤ C_u * (1 + Real.log c) * Real.sqrt n :=
          (abs_centerPoleCollar_diff_le hc1 h8c hnI).1
        have hD : |(completeWeilPoleShift φ c / N) * D_row n| ≤
            2 * S₁ * C_u * c ^ 2 * Real.sqrt N / N := by
          rw [abs_mul, abs_div, abs_of_pos hN0]
          calc
            (|completeWeilPoleShift φ c| / N) * |D_row n|
                ≤ (S₁ * c / N) * (C_u * (2 * c) * Real.sqrt N) :=
              mul_le_mul (div_le_div_of_nonneg_right hshift_le hN0.le)
                (hu.trans (mul_le_mul
                  (mul_le_mul_of_nonneg_left h1c_c hCu_0)
                  (Real.sqrt_le_sqrt hnN) (Real.sqrt_nonneg _)
                  (mul_nonneg hCu_0 (by positivity))))
                (abs_nonneg _) (by dsimp only [S₁]; positivity)
            _ = 2 * S₁ * C_u * c ^ 2 * Real.sqrt N / N := by ring
        rw [abs_mul]
        calc
          _ ≤ (2 * Real.sqrt l / (Real.sqrt N * Real.sqrt (Real.log N))) *
                (2 * S₁ * C_u * c ^ 2 * Real.sqrt N / N) :=
            mul_le_mul hvl_n hD (abs_nonneg _) (by positivity)
          _ = 4 * S₁ * C_u * Real.sqrt l * c ^ 2 / (N * Real.sqrt (Real.log N)) := by
            field_simp [hsN.ne', hsL0.ne', hN0.ne']; ring
      rw [abs_mul, abs_of_pos (inv_pos.mpr hsL0)]
      calc
        _ ≤ (Real.sqrt (Real.log N))⁻¹ *
              ((Z₂.card : ℝ) * (4 * S₁ * C_u * Real.sqrt l * c ^ 2 /
                (N * Real.sqrt (Real.log N)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← nsmul_eq_mul, ← sum_const]
          exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)
        _ ≤ (Real.sqrt (Real.log N))⁻¹ *
              (((2 * Real.exp 2 + 1) * c) * (4 * S₁ * C_u * Real.sqrt l * c ^ 2 /
                (N * Real.sqrt (Real.log N)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hZ2_card (by dsimp only [S₁, C_u]; positivity))
            (by positivity)
        _ = 4 * (2 * Real.exp 2 + 1) * S₁ * C_u * Real.sqrt l * (c ^ 3 / (N * Real.log N)) := by
          field_simp [hsL0.ne', hL0.ne', hN0.ne']
          rw [Real.sq_sqrt hL0.le]; ring
        _ ≤ 4 * (2 * Real.exp 2 + 1) * S₁ * C_u * Real.sqrt l * (c ^ 3 / N) := by
          refine mul_le_mul_of_nonneg_left ?_ (by dsimp only [S₁, C_u]; positivity)
          exact div_le_div_of_nonneg_left (by positivity) hN0 (le_mul_of_one_le_right hN0.le hL1)
    have hb3 : |(Real.sqrt (Real.log N))⁻¹ *
        ∑ n ∈ Z₃, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          ((completeWeilPoleShift φ c / N) * D_row n)| ≤
        2 * S₁ * C_i * Real.sqrt l * (c / Real.log N) := by
      have hpt : ∀ n ∈ Z₃,
          |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              ((completeWeilPoleShift φ c / N) * D_row n)| ≤
            (S₁ * C_i * Real.sqrt l * c / (Real.sqrt N * Real.sqrt (Real.log N))) *
              (1 / Real.sqrt n) := by
        intro n hn
        obtain ⟨hnI, hlo, hhi⟩ := mem_filter.mp hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hnI).1
        have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
        have hi := (abs_centerPoleCollar_diff_le hc1 h8c hnI).2 hlo hhi
        have hvl_n : |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n| ≤
            Real.sqrt l / (Real.sqrt n * Real.sqrt (Real.log N)) := by
          rw [primeHorizonExtension_normalizedRamanujan hnI]
          unfold ramanujanPoleProfile
          rw [abs_mul, abs_div, abs_of_pos (inv_pos.mpr hsL0), abs_of_pos hsn]
          exact (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (abs_mode_le_sqrt_conductor hl n) hsn.le)
            (by positivity)).trans_eq (by ring)
        have hD : |(completeWeilPoleShift φ c / N) * D_row n| ≤ S₁ * C_i * c / Real.sqrt N := by
          rw [abs_mul, abs_div, abs_of_pos hN0]
          calc
            (|completeWeilPoleShift φ c| / N) * |D_row n|
                ≤ (S₁ * c / N) * (C_i * Real.sqrt N) :=
              mul_le_mul (div_le_div_of_nonneg_right hshift_le hN0.le) hi
                (abs_nonneg _) (by dsimp only [S₁]; positivity)
            _ = S₁ * C_i * c / Real.sqrt N := by
              field_simp [hsN.ne', hN0.ne']
              rw [Real.sq_sqrt hN0.le]; ring
        rw [abs_mul]
        calc
          _ ≤ (Real.sqrt l / (Real.sqrt n * Real.sqrt (Real.log N))) *
                (S₁ * C_i * c / Real.sqrt N) :=
            mul_le_mul hvl_n hD (abs_nonneg _) (by positivity)
          _ = (S₁ * C_i * Real.sqrt l * c / (Real.sqrt N * Real.sqrt (Real.log N))) *
                (1 / Real.sqrt n) := by ring
      have hsum_inv : (∑ n ∈ Z₃, 1 / Real.sqrt (n : ℝ)) ≤ 2 * Real.sqrt N :=
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity).trans
          (sum_Icc_one_div_sqrt_le_two_sqrt_nat N)
      rw [abs_mul, abs_of_pos (inv_pos.mpr hsL0)]
      calc
        _ ≤ (Real.sqrt (Real.log N))⁻¹ *
              ((S₁ * C_i * Real.sqrt l * c / (Real.sqrt N * Real.sqrt (Real.log N))) *
                ∑ n ∈ Z₃, 1 / Real.sqrt n) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [mul_sum]
          exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)
        _ ≤ (Real.sqrt (Real.log N))⁻¹ *
              ((S₁ * C_i * Real.sqrt l * c / (Real.sqrt N * Real.sqrt (Real.log N))) *
                (2 * Real.sqrt N)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsum_inv (by dsimp only [S₁, C_i]; positivity))
            (by positivity)
        _ = 2 * S₁ * C_i * Real.sqrt l * (c / Real.log N) := by
          field_simp [hsN.ne', hsL0.ne', hL0.ne']
          rw [Real.sq_sqrt hL0.le]; ring
    rw [hpart, mul_add, mul_add]
    have htri := abs_add_three
      ((Real.sqrt (Real.log N))⁻¹ * ∑ n ∈ Z₁,
        primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          ((completeWeilPoleShift φ c / N) * D_row n))
      ((Real.sqrt (Real.log N))⁻¹ * ∑ n ∈ Z₂,
        primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          ((completeWeilPoleShift φ c / N) * D_row n))
      ((Real.sqrt (Real.log N))⁻¹ * ∑ n ∈ Z₃,
        primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          ((completeWeilPoleShift φ c / N) * D_row n))
    have hsum_bi : |(Real.sqrt (Real.log N))⁻¹ * (∑ n ∈ Z₁, _) +
          (Real.sqrt (Real.log N))⁻¹ * (∑ n ∈ Z₂, _) +
          (Real.sqrt (Real.log N))⁻¹ * (∑ n ∈ Z₃, _)| ≤
        C_bi * Real.sqrt l * (c / Real.log N + c ^ 3 / N) := by
      have hnn1 : 0 ≤ 4 * (2 * Real.exp 2 + 1) * S₁ * C_u * Real.sqrt l * (c / Real.log N) := by
        dsimp only [S₁, C_u]; positivity
      have hnn2 : 0 ≤ (4 * S₁ * C_u + 2 * S₁ * C_i) * Real.sqrt l * (c ^ 3 / N) := by
        dsimp only [S₁, C_u, C_i]; positivity
      dsimp only [C_bi]
      linarith only [htri, hb1, hb2, hb3, hnn1, hnn2,
        (by ring : (4 * S₁ * C_u + 2 * S₁ * C_i + 4 * (2 * Real.exp 2 + 1) * S₁ * C_u) *
            Real.sqrt l * (c / Real.log N + c ^ 3 / N) =
          4 * S₁ * C_u * Real.sqrt l * (c / Real.log N) +
            4 * (2 * Real.exp 2 + 1) * S₁ * C_u * Real.sqrt l * (c ^ 3 / N) +
            2 * S₁ * C_i * Real.sqrt l * (c / Real.log N) +
            4 * (2 * Real.exp 2 + 1) * S₁ * C_u * Real.sqrt l * (c / Real.log N) +
            (4 * S₁ * C_u + 2 * S₁ * C_i) * Real.sqrt l * (c ^ 3 / N))]
    refine hsum_bi.trans ?_
    have : 0 ≤ C_sq := by dsimp only [C_sq, S₁, C_u, C_i]; positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [this]) (Real.sqrt_nonneg _))
      (by positivity)

/-- Ground-mode (`m = 1`) logarithm-free `L^2` and bilinear bounds on `coreNearRow φ c N 1`. -/
private lemma coreNearRow_one_log_free_bounds {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C_one : ℝ, 0 < C_one ∧
      ∀ {N : ℕ} {c : ℝ},
        1 ≤ c → 1 ≤ Real.log (N : ℝ) →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N → c ^ 4 ≤ N →
        (∑ n ∈ Icc 1 N, coreNearRow φ c N 1 n ^ 2) / Real.log N ≤
          C_one * (c ^ 2 / Real.log N) ∧
        ∀ {l : ℕ}, 0 < l →
          |(Real.sqrt (Real.log N))⁻¹ *
              ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
                coreNearRow φ c N 1 n| ≤
            C_one * Real.sqrt l * (c / Real.log N + c ^ 3 / N) := by
  obtain ⟨C_d, hCd, hdef_sq⟩ := exists_sum_poleRowDefect_sq_le hφ hsupp hM
  obtain ⟨C_P, hCP, hP_le⟩ := exists_abs_exactPoleCoefficient_le hφ hsupp hM
  obtain ⟨C_cp, hCcp, hcp⟩ := centerPoleCollar_sum_bounds φ
  let C_e := atomPoleMomentErrorConstant φ
  have hCe0 : 0 ≤ C_e := atomPoleMomentErrorConstant_nonneg φ
  let C_sq := 3 * (8 * C_d + 4 * C_e ^ 2 + 2 * C_cp)
  let C_bi := (C_P + 8 * Real.sqrt (C_d + 1)) + 2 * C_e + C_cp
  refine ⟨C_sq + C_bi + 1, by dsimp only [C_sq, C_bi]; positivity, ?_⟩
  intro N c hc1 hL1 hradN hc4N
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hsL0 : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hL0
  have he2_ge4 : (4 : ℝ) ≤ Real.exp 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have hp : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [h2, hp]
  have h8c : 8 * c ≤ N := by
    unfold linearNearRowRadius at hradN
    have h1 : 8 * c ≤ 2 * c * Real.exp 2 := by nlinarith only [hc0, he2_ge4]
    have h2 : 8 * c ≤ (2 * c * Real.exp 2 + 1) ^ 2 := by nlinarith only [h1, hc1]
    linarith only [h2, hradN]
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith only [hc1, h8c]
    exact_mod_cast this
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hw1 : c / N ≤ 1 := (div_le_one hN0).mpr (by linarith only [hc0, h8c])
  have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have h1c_le : 1 + Real.log c ≤ 2 * Real.sqrt c := one_add_log_le_two_sqrt_pos hc0
  have hsc_le_c : Real.sqrt c ≤ c := by
    calc
      Real.sqrt c ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt (by nlinarith only [hc1])
      _ = c := Real.sqrt_sq hc0.le
  have hlogc_le_2sc : Real.log c ≤ 2 * Real.sqrt c := by linarith only [h1c_le]
  have hlogc_le_2c : Real.log c ≤ 2 * c := hlogc_le_2sc.trans (by linarith only [hsc_le_c])
  -- Pointwise decomposition of `coreNearRow φ c N 1 n` into defect, pole-error, and center-collar.
  let D_row : ℕ → ℝ := fun n =>
    (∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j) -
      Real.log c * Real.sqrt n
  have hrow1_eq : ∀ n : ℕ, coreNearRow φ c N 1 n =
      -Real.log c * poleRowDefect φ c N n +
        (-Real.log c * atomPoleErrorCoefficient φ c N * Real.sqrt n) +
        (completeWeilPoleShift φ c / N) * D_row n := by
    intro n
    have hng1 : nearGram φ c N (fun j => normalizedRamanujanMode 1 j / Real.sqrt j) n =
        nearPoleRow φ c N n := by
      unfold nearPoleRow nearGram
      refine sum_congr rfl fun j _ => ?_
      dsimp only
      rw [normalizedRamanujanMode_one, one_div]
    have hnp : nearPoleRow φ c N n =
        poleRowDefect φ c N n +
          (atomPoleErrorCoefficient φ c N + completeWeilPoleShift φ c / N) * Real.sqrt n := by
      unfold poleRowDefect
      rw [exactPoleCoefficient_eq]; ring
    unfold coreNearRow
    rw [hng1, hnp]
    have hc_sum : (∑ j ∈ nearRowIndices c N n,
        completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
          normalizedRamanujanMode 1 j / Real.sqrt j) =
        (completeWeilPoleShift φ c / N) *
          ∑ j ∈ nearRowIndices c N n, archimedeanCenterKernel n j / Real.sqrt j := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [normalizedRamanujanMode_one, mul_one, mul_div_assoc]
    rw [hc_sum]
    dsimp only [D_row]
    ring
  -- Bound `|atomPoleErrorCoefficient φ c N| ≤ C_e * (c / N)^2`.
  have herr_le : |atomPoleErrorCoefficient φ c N| ≤ C_e * (c / N) ^ 2 := by
    have h := abs_dilated_pole_product_sub_le hφ hsupp hM hw0 hw1
    have heq : atomPoleErrorCoefficient φ c N =
        atomExponentialMoment (atomDilate φ (c / N)) (-(1 / 2)) *
          atomExponentialMoment (atomDilate φ (c / N)) (1 / 2) /
            (∫ u, atomDilate φ (c / N) u ^ 2) -
          (c / N) * (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) := by
      simp only [atomPoleErrorCoefficient, completeWeilPoleShift]; ring
    rw [heq]; exact h
  obtain ⟨hcp_sq, hcp_bi⟩ := hcp hc1 hL1 hradN
  constructor
  · -- Part 1: `L^2` squared sum bound.
    have hsq1 : (∑ n ∈ Icc 1 N, (-Real.log c * poleRowDefect φ c N n) ^ 2) / Real.log N ≤
        8 * C_d * (c ^ 2 / Real.log N) := by
      have hfactor : (∑ n ∈ Icc 1 N, (-Real.log c * poleRowDefect φ c N n) ^ 2) =
          Real.log c ^ 2 * ∑ n ∈ Icc 1 N, poleRowDefect φ c N n ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
      have hlog3 : Real.log c ^ 2 * (1 + Real.log c) ≤ 8 * c ^ 2 := by
        have hsq := pow_le_pow_left₀ hlogc0 hlogc_le_2sc 2
        rw [mul_pow, Real.sq_sqrt hc0.le, show (2 : ℝ) ^ 2 = 4 by norm_num] at hsq
        have h1c_2c : 1 + Real.log c ≤ 2 * c := h1c_le.trans (by linarith only [hsc_le_c])
        exact (mul_le_mul hsq h1c_2c (by positivity) (by positivity)).trans_eq (by ring)
      rw [hfactor]
      calc
        (Real.log c ^ 2 * ∑ n ∈ Icc 1 N, poleRowDefect φ c N n ^ 2) / Real.log N
            ≤ (Real.log c ^ 2 * (C_d * (1 + Real.log c))) / Real.log N :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hdef_sq hc1 h8c hc4N) (sq_nonneg _)) hL0.le
        _ = C_d * (Real.log c ^ 2 * (1 + Real.log c)) / Real.log N := by ring
        _ ≤ C_d * (8 * c ^ 2) / Real.log N :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog3 hCd) hL0.le
        _ = 8 * C_d * (c ^ 2 / Real.log N) := by ring
    have hsq2 : (∑ n ∈ Icc 1 N, (-Real.log c * atomPoleErrorCoefficient φ c N * Real.sqrt n) ^ 2) /
        Real.log N ≤ 4 * C_e ^ 2 * (c ^ 2 / Real.log N) := by
      have hpt : ∀ n ∈ Icc 1 N,
          (-Real.log c * atomPoleErrorCoefficient φ c N * Real.sqrt n) ^ 2 ≤
            4 * C_e ^ 2 * c ^ 6 / (N : ℝ) ^ 3 := by
        intro n hn
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
        have hprod : |-Real.log c * atomPoleErrorCoefficient φ c N| ≤ 2 * C_e * c ^ 3 / N ^ 2 := by
          rw [abs_mul, abs_neg, abs_of_nonneg hlogc0]
          exact (mul_le_mul hlogc_le_2c herr_le (abs_nonneg _) (by positivity)).trans_eq
            (by field_simp [hN0.ne'])
        have hsq := pow_le_pow_left₀ (abs_nonneg _) hprod 2
        rw [sq_abs] at hsq
        calc
          (-Real.log c * atomPoleErrorCoefficient φ c N * Real.sqrt n) ^ 2
              = (-Real.log c * atomPoleErrorCoefficient φ c N) ^ 2 * n := by
            rw [mul_pow, Real.sq_sqrt hn0]
          _ ≤ (2 * C_e * c ^ 3 / (N : ℝ) ^ 2) ^ 2 * N :=
            mul_le_mul hsq hnN hn0 (by positivity)
          _ = 4 * C_e ^ 2 * c ^ 6 / (N : ℝ) ^ 3 := by field_simp [hN0.ne']; ring
      have hc6_N2 : c ^ 6 / (N : ℝ) ^ 2 ≤ c ^ 2 := by
        have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
        have hc4_N2 : c ^ 4 ≤ (N : ℝ) ^ 2 := hc4N.trans (by nlinarith only [hN1R])
        rw [div_le_iff₀ (by positivity)]
        calc
          c ^ 6 = c ^ 2 * c ^ 4 := by ring
          _ ≤ c ^ 2 * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hc4_N2 (sq_nonneg c)
      calc
        _ ≤ (∑ _n ∈ Icc 1 N, (4 * C_e ^ 2 * c ^ 6 / (N : ℝ) ^ 3)) / Real.log N :=
          div_le_div_of_nonneg_right (sum_le_sum hpt) hL0.le
        _ = 4 * C_e ^ 2 * (c ^ 6 / (N : ℝ) ^ 2) / Real.log N := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          field_simp [hN0.ne']
        _ ≤ 4 * C_e ^ 2 * c ^ 2 / Real.log N :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc6_N2 (by positivity)) hL0.le
        _ = 4 * C_e ^ 2 * (c ^ 2 / Real.log N) := by ring
    have hsq3 : (∑ n ∈ Icc 1 N, ((completeWeilPoleShift φ c / N) * D_row n) ^ 2) / Real.log N ≤
        2 * C_cp * (c ^ 2 / Real.log N) := by
      have hc2_N : c ^ 2 ≤ N := (pow_le_pow_right₀ hc1 (by norm_num : 2 ≤ 4)).trans hc4N
      have hc4_N : c ^ 4 / (N * Real.log N) ≤ c ^ 2 / Real.log N := by
        rw [div_le_div_iff₀ (by positivity) hL0]
        calc
          c ^ 4 * Real.log N = c ^ 2 * (c ^ 2 * Real.log N) := by ring
          _ ≤ (N : ℝ) * (c ^ 2 * Real.log N) :=
            mul_le_mul_of_nonneg_right hc2_N (by positivity)
          _ = c ^ 2 * (N * Real.log N) := by ring
      exact hcp_sq.trans ((mul_le_mul_of_nonneg_left (add_le_add le_rfl hc4_N) hCcp.le).trans_eq
        (by ring))
    have h3sq : (∑ n ∈ Icc 1 N, coreNearRow φ c N 1 n ^ 2) / Real.log N ≤
        3 * ((∑ n ∈ Icc 1 N, (-Real.log c * poleRowDefect φ c N n) ^ 2) / Real.log N +
          (∑ n ∈ Icc 1 N, (-Real.log c * atomPoleErrorCoefficient φ c N * Real.sqrt n) ^ 2) /
            Real.log N +
          (∑ n ∈ Icc 1 N, ((completeWeilPoleShift φ c / N) * D_row n) ^ 2) / Real.log N) := by
      rw [← add_div, ← add_div, ← mul_div_assoc, ← sum_add_distrib, ← sum_add_distrib, mul_sum]
      refine div_le_div_of_nonneg_right (sum_le_sum fun n _ => ?_) hL0.le
      rw [hrow1_eq n]
      nlinarith only [sq_nonneg (-Real.log c * poleRowDefect φ c N n -
          (-Real.log c * atomPoleErrorCoefficient φ c N * Real.sqrt n)),
        sq_nonneg (-Real.log c * poleRowDefect φ c N n -
          (completeWeilPoleShift φ c / N) * D_row n),
        sq_nonneg (-Real.log c * atomPoleErrorCoefficient φ c N * Real.sqrt n -
          (completeWeilPoleShift φ c / N) * D_row n)]
    have hsum_sq : (∑ n ∈ Icc 1 N, coreNearRow φ c N 1 n ^ 2) / Real.log N ≤
        C_sq * (c ^ 2 / Real.log N) := by
      dsimp only [C_sq]
      linarith only [h3sq, hsq1, hsq2, hsq3,
        (by ring : 3 * (8 * C_d * (c ^ 2 / Real.log N) + 4 * C_e ^ 2 * (c ^ 2 / Real.log N) +
            2 * C_cp * (c ^ 2 / Real.log N)) =
          3 * (8 * C_d + 4 * C_e ^ 2 + 2 * C_cp) * (c ^ 2 / Real.log N))]
    refine hsum_sq.trans ?_
    have : 0 ≤ C_bi := by dsimp only [C_bi]; positivity
    exact mul_le_mul_of_nonneg_right (by linarith only [this]) (by positivity)
  · -- Part 2: Bilinear pairing bound against `v_l`.
    intro l hl
    -- Term 1: `poleRowDefect` split into deep rows (`2 n (c/N) ≤ 1`) and mid/top rows (`2 n (c/N) > 1`).
    have hbi1 : |(Real.sqrt (Real.log N))⁻¹ *
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          (-Real.log c * poleRowDefect φ c N n)| ≤
        (C_P + 8 * Real.sqrt (C_d + 1)) * Real.sqrt l * (c / Real.log N) := by
      let S_deep := (Icc 1 N).filter (fun n : ℕ => 2 * (n : ℝ) * (c / N) ≤ 1)
      let S_mid := (Icc 1 N).filter (fun n : ℕ => 1 < 2 * (n : ℝ) * (c / N))
      have hpart_dm : ∀ f : ℕ → ℝ, (∑ n ∈ Icc 1 N, f n) =
          (∑ n ∈ S_deep, f n) + ∑ n ∈ S_mid, f n := by
        intro f
        have hd : Disjoint S_deep S_mid := disjoint_left.mpr fun n h1 h2 =>
          lt_irrefl _ ((mem_filter.mp h2).2.trans_le (mem_filter.mp h1).2)
        have hu : Icc 1 N = S_deep ∪ S_mid := by
          ext n; simp only [S_deep, S_mid, mem_union, mem_filter]
          exact ⟨fun hn => (le_or_gt (2 * (n : ℝ) * (c / N)) 1).imp (⟨hn, ·⟩) (⟨hn, ·⟩),
            fun h => h.elim (·.1) (·.1)⟩
        rw [hu, sum_union hd]
      have hb_deep : |(Real.sqrt (Real.log N))⁻¹ *
          ∑ n ∈ S_deep, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            (-Real.log c * poleRowDefect φ c N n)| ≤
          C_P * Real.sqrt l * (c / Real.log N) := by
        have hP := hP_le hc0 hN1 hw1
        have hpt : ∀ n ∈ S_deep,
            |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
                (-Real.log c * poleRowDefect φ c N n)| ≤
              Real.log c * C_P * Real.sqrt l * (c / N) / Real.sqrt (Real.log N) := by
          intro n hn
          obtain ⟨hnI, hdeep⟩ := mem_filter.mp hn
          have hn1 := (mem_Icc.mp hnI).1
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
          have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
          have hnp0 := nearPoleRow_eq_zero_of_deep hφ hsupp hc0 hN1 hn1 hdeep
          have hdef_eq : poleRowDefect φ c N n = -exactPoleCoefficient φ c N * Real.sqrt n := by
            unfold poleRowDefect; rw [hnp0]; ring
          have hvl_n : |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n| ≤
              Real.sqrt l / (Real.sqrt n * Real.sqrt (Real.log N)) := by
            rw [primeHorizonExtension_normalizedRamanujan hnI]
            unfold ramanujanPoleProfile
            rw [abs_mul, abs_div, abs_of_pos (inv_pos.mpr hsL0), abs_of_pos hsn]
            exact (mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right (abs_mode_le_sqrt_conductor hl n) hsn.le)
              (by positivity)).trans_eq (by ring)
          rw [hdef_eq, show -Real.log c * (-exactPoleCoefficient φ c N * Real.sqrt n) =
            Real.log c * exactPoleCoefficient φ c N * Real.sqrt n by ring,
            abs_mul, abs_mul, abs_mul, abs_of_nonneg hlogc0, abs_of_pos hsn]
          calc
            |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n| *
                (Real.log c * |exactPoleCoefficient φ c N| * Real.sqrt n)
                ≤ (Real.sqrt l / (Real.sqrt n * Real.sqrt (Real.log N))) *
                    (Real.log c * (C_P * (c / N)) * Real.sqrt n) :=
              mul_le_mul hvl_n
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP hlogc0) hsn.le)
                (by positivity) (by positivity)
            _ = Real.log c * C_P * Real.sqrt l * (c / N) / Real.sqrt (Real.log N) := by
              field_simp [hsn.ne', hsL0.ne']
        have hcard_deep : (S_deep.card : ℝ) ≤ (N : ℝ) / (2 * c) := by
          have hsub : S_deep ⊆ Icc 1 ⌊(N : ℝ) / (2 * c)⌋₊ := fun n hn => by
            obtain ⟨hnI, hdeep⟩ := mem_filter.mp hn
            refine mem_Icc.mpr ⟨(mem_Icc.mp hnI).1, Nat.le_floor ?_⟩
            rw [le_div_iff₀ (by positivity)]
            have h1 : 2 * (n : ℝ) * c ≤ N := by
              rw [show 2 * (n : ℝ) * (c / N) = (2 * (n : ℝ) * c) / N by ring,
                div_le_one hN0] at hdeep
              exact hdeep
            linarith only [h1]
          calc
            (S_deep.card : ℝ) ≤ ((Icc 1 ⌊(N : ℝ) / (2 * c)⌋₊).card : ℝ) := by
              exact_mod_cast card_le_card hsub
            _ = (⌊(N : ℝ) / (2 * c)⌋₊ : ℝ) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
            _ ≤ (N : ℝ) / (2 * c) := Nat.floor_le (by positivity)
        rw [abs_mul, abs_of_pos (inv_pos.mpr hsL0)]
        calc
          _ ≤ (Real.sqrt (Real.log N))⁻¹ *
                ((S_deep.card : ℝ) *
                  (Real.log c * C_P * Real.sqrt l * (c / N) / Real.sqrt (Real.log N))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [← nsmul_eq_mul, ← sum_const]
            exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)
          _ ≤ (Real.sqrt (Real.log N))⁻¹ *
                (((N : ℝ) / (2 * c)) *
                  (Real.log c * C_P * Real.sqrt l * (c / N) / Real.sqrt (Real.log N))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard_deep (by positivity))
              (by positivity)
          _ = (C_P / 2) * Real.sqrt l * (Real.log c / Real.log N) := by
            field_simp [hsL0.ne', hL0.ne', hN0.ne', hc0.ne']
            rw [Real.sq_sqrt hL0.le]; ring
          _ ≤ C_P * Real.sqrt l * (c / Real.log N) := by
            have h1 : (C_P / 2) * Real.log c ≤ C_P * c := by nlinarith only [hCP, hlogc_le_2c]
            calc
              (C_P / 2) * Real.sqrt l * (Real.log c / Real.log N) =
                  ((C_P / 2) * Real.log c) * (Real.sqrt l / Real.log N) := by ring
              _ ≤ (C_P * c) * (Real.sqrt l / Real.log N) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
              _ = C_P * Real.sqrt l * (c / Real.log N) := by ring
      have hb_mid : |(Real.sqrt (Real.log N))⁻¹ *
          ∑ n ∈ S_mid, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            (-Real.log c * poleRowDefect φ c N n)| ≤
          8 * Real.sqrt (C_d + 1) * Real.sqrt l * (c / Real.log N) := by
        have hvl_sq : (∑ n ∈ S_mid,
            primeHorizonExtension (normalizedRamanujanHorizonVector l N) n ^ 2) ≤
            4 * (l : ℝ) * (1 + Real.log c) / Real.log N := by
          have hpt : ∀ n ∈ S_mid,
              primeHorizonExtension (normalizedRamanujanHorizonVector l N) n ^ 2 ≤
                ((l : ℝ) / Real.log N) * (1 / (n : ℝ)) := by
            intro n hn
            have hnI := (mem_filter.mp hn).1
            have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hnI).1
            have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
            have hvl_n : |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n| ≤
                Real.sqrt l / (Real.sqrt n * Real.sqrt (Real.log N)) := by
              rw [primeHorizonExtension_normalizedRamanujan hnI]
              unfold ramanujanPoleProfile
              rw [abs_mul, abs_div, abs_of_pos (inv_pos.mpr hsL0), abs_of_pos hsn]
              exact (mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right (abs_mode_le_sqrt_conductor hl n) hsn.le)
                (by positivity)).trans_eq (by ring)
            have hsq := pow_le_pow_left₀ (abs_nonneg _) hvl_n 2
            rw [sq_abs, div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg l),
              Real.sq_sqrt hn0.le, Real.sq_sqrt hL0.le] at hsq
            exact hsq.trans_eq (by ring)
          have hmid_inv : (∑ n ∈ S_mid, 1 / (n : ℝ)) ≤ 4 * (1 + Real.log c) := by
            have h := sum_mid_rows_inv_le hc1 h8c
            rwa [← sum_filter] at h
          calc
            _ ≤ ((l : ℝ) / Real.log N) * ∑ n ∈ S_mid, 1 / (n : ℝ) := by
              rw [mul_sum]; exact sum_le_sum hpt
            _ ≤ ((l : ℝ) / Real.log N) * (4 * (1 + Real.log c)) :=
              mul_le_mul_of_nonneg_left hmid_inv (by positivity)
            _ = 4 * (l : ℝ) * (1 + Real.log c) / Real.log N := by ring
        have hdef_mid : (∑ n ∈ S_mid, poleRowDefect φ c N n ^ 2) ≤ (C_d + 1) * (1 + Real.log c) := by
          calc
            (∑ n ∈ S_mid, poleRowDefect φ c N n ^ 2) ≤ ∑ n ∈ Icc 1 N, poleRowDefect φ c N n ^ 2 :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
            _ ≤ C_d * (1 + Real.log c) := hdef_sq hc1 h8c hc4N
            _ ≤ (C_d + 1) * (1 + Real.log c) :=
              mul_le_mul_of_nonneg_right (by linarith) (by linarith only [hlogc0])
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq S_mid
          (primeHorizonExtension (normalizedRamanujanHorizonVector l N))
          (poleRowDefect φ c N)
        have hcs_ub : (∑ n ∈ S_mid,
            primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              poleRowDefect φ c N n) ^ 2 ≤
            (2 * Real.sqrt (C_d + 1) * Real.sqrt l * (1 + Real.log c) /
              Real.sqrt (Real.log N)) ^ 2 := by
          calc
            _ ≤ (4 * (l : ℝ) * (1 + Real.log c) / Real.log N) *
                  ((C_d + 1) * (1 + Real.log c)) :=
              hcs.trans (mul_le_mul hvl_sq hdef_mid
                (sum_nonneg fun _ _ => sq_nonneg _) (by positivity))
            _ = (2 * Real.sqrt (C_d + 1) * Real.sqrt l * (1 + Real.log c) /
                  Real.sqrt (Real.log N)) ^ 2 := by
              rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
                Real.sq_sqrt (Nat.cast_nonneg l), Real.sq_sqrt hL0.le]
              ring
        have habs_cs : |∑ n ∈ S_mid,
            primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              poleRowDefect φ c N n| ≤
            2 * Real.sqrt (C_d + 1) * Real.sqrt l * (1 + Real.log c) /
              Real.sqrt (Real.log N) := by
          have h := Real.sqrt_le_sqrt hcs_ub
          rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (by positivity)] at h
        have hrew : (∑ n ∈ S_mid,
            primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              (-Real.log c * poleRowDefect φ c N n)) =
            -Real.log c * ∑ n ∈ S_mid,
              primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
                poleRowDefect φ c N n := by
          rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
        have hlog2_4c : Real.log c * (1 + Real.log c) ≤ 4 * c := by
          calc
            Real.log c * (1 + Real.log c) ≤ (2 * Real.sqrt c) * (2 * Real.sqrt c) :=
              mul_le_mul hlogc_le_2sc h1c_le (by linarith only [hlogc0]) (by positivity)
            _ = 4 * c := by
              rw [show 2 * Real.sqrt c * (2 * Real.sqrt c) = 4 * (Real.sqrt c * Real.sqrt c) by ring,
                Real.mul_self_sqrt hc0.le]
        rw [hrew, abs_mul, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr hsL0), abs_of_nonneg hlogc0]
        calc
          _ ≤ (Real.sqrt (Real.log N))⁻¹ *
                (Real.log c * (2 * Real.sqrt (C_d + 1) * Real.sqrt l * (1 + Real.log c) /
                  Real.sqrt (Real.log N))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habs_cs hlogc0) (by positivity)
          _ = 2 * Real.sqrt (C_d + 1) * Real.sqrt l *
                (Real.log c * (1 + Real.log c)) / Real.log N := by
            field_simp [hsL0.ne', hL0.ne']
            rw [Real.sq_sqrt hL0.le]; ring
          _ ≤ 2 * Real.sqrt (C_d + 1) * Real.sqrt l * (4 * c) / Real.log N :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog2_4c (by positivity)) hL0.le
          _ = 8 * Real.sqrt (C_d + 1) * Real.sqrt l * (c / Real.log N) := by ring
      rw [hpart_dm, mul_add]
      exact (abs_add_le _ _).trans ((add_le_add hb_deep hb_mid).trans_eq (by ring))
    -- Term 2: `atomPoleErrorCoefficient` bilinear bound.
    have hbi2 : |(Real.sqrt (Real.log N))⁻¹ *
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          (-Real.log c * atomPoleErrorCoefficient φ c N * Real.sqrt n)| ≤
        2 * C_e * Real.sqrt l * (c ^ 3 / N) := by
      have hpt : ∀ n ∈ Icc 1 N,
          |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              (-Real.log c * atomPoleErrorCoefficient φ c N * Real.sqrt n)| ≤
            2 * C_e * Real.sqrt l * c ^ 3 / (N ^ 2 * Real.sqrt (Real.log N)) := by
        intro n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
        have hvl_n : |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n| ≤
            Real.sqrt l / (Real.sqrt n * Real.sqrt (Real.log N)) := by
          rw [primeHorizonExtension_normalizedRamanujan hn]
          unfold ramanujanPoleProfile
          rw [abs_mul, abs_div, abs_of_pos (inv_pos.mpr hsL0), abs_of_pos hsn]
          exact (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (abs_mode_le_sqrt_conductor hl n) hsn.le)
            (by positivity)).trans_eq (by ring)
        rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hlogc0, abs_of_pos hsn]
        calc
          _ ≤ (Real.sqrt l / (Real.sqrt n * Real.sqrt (Real.log N))) *
                (2 * c * (C_e * (c / N) ^ 2) * Real.sqrt n) :=
            mul_le_mul hvl_n
              (mul_le_mul_of_nonneg_right (mul_le_mul hlogc_le_2c herr_le (abs_nonneg _)
                (by positivity)) hsn.le)
              (by positivity) (by positivity)
          _ = 2 * C_e * Real.sqrt l * c ^ 3 / (N ^ 2 * Real.sqrt (Real.log N)) := by
            field_simp [hsn.ne', hsL0.ne', hN0.ne']
      rw [abs_mul, abs_of_pos (inv_pos.mpr hsL0)]
      calc
        _ ≤ (Real.sqrt (Real.log N))⁻¹ *
              ∑ _n ∈ Icc 1 N,
                (2 * C_e * Real.sqrt l * c ^ 3 / (N ^ 2 * Real.sqrt (Real.log N))) :=
          mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)) (by positivity)
        _ = 2 * C_e * Real.sqrt l * (c ^ 3 / (N * Real.log N)) := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          field_simp [hsL0.ne', hL0.ne', hN0.ne']
          rw [Real.sq_sqrt hL0.le]; ring
        _ ≤ 2 * C_e * Real.sqrt l * (c ^ 3 / N) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_left (by positivity) hN0 (le_mul_of_one_le_right hN0.le hL1)
    have hbi3 := hcp_bi hl
    have hsplit : (Real.sqrt (Real.log N))⁻¹ *
        (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          coreNearRow φ c N 1 n) =
        (Real.sqrt (Real.log N))⁻¹ *
          (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            (-Real.log c * poleRowDefect φ c N n)) +
        (Real.sqrt (Real.log N))⁻¹ *
          (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            (-Real.log c * atomPoleErrorCoefficient φ c N * Real.sqrt n)) +
        (Real.sqrt (Real.log N))⁻¹ *
          (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            ((completeWeilPoleShift φ c / N) * D_row n)) := by
      have hpt : ∀ n ∈ Icc 1 N,
          primeHorizonExtension (normalizedRamanujanHorizonVector l N) n * coreNearRow φ c N 1 n =
          primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              (-Real.log c * poleRowDefect φ c N n) +
            primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              (-Real.log c * atomPoleErrorCoefficient φ c N * Real.sqrt n) +
            primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              ((completeWeilPoleShift φ c / N) * D_row n) := fun n _ => by
        rw [hrow1_eq n]; ring
      rw [sum_congr rfl hpt, sum_add_distrib, sum_add_distrib, mul_add, mul_add]
    rw [hsplit]
    have htri := abs_add_three
      ((Real.sqrt (Real.log N))⁻¹ *
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          (-Real.log c * poleRowDefect φ c N n))
      ((Real.sqrt (Real.log N))⁻¹ *
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          (-Real.log c * atomPoleErrorCoefficient φ c N * Real.sqrt n))
      ((Real.sqrt (Real.log N))⁻¹ *
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          ((completeWeilPoleShift φ c / N) * D_row n))
    have hsum_bi : |(Real.sqrt (Real.log N))⁻¹ * (∑ n ∈ Icc 1 N, _) +
          (Real.sqrt (Real.log N))⁻¹ * (∑ n ∈ Icc 1 N, _) +
          (Real.sqrt (Real.log N))⁻¹ * (∑ n ∈ Icc 1 N, _)| ≤
        C_bi * Real.sqrt l * (c / Real.log N + c ^ 3 / N) := by
      have hnn1 : 0 ≤ 2 * C_e * Real.sqrt l * (c / Real.log N) := by positivity
      have hnn2 : 0 ≤ (C_P + 8 * Real.sqrt (C_d + 1)) * Real.sqrt l * (c ^ 3 / N) := by positivity
      dsimp only [C_bi]
      linarith only [htri, hbi1, hbi2, hbi3, hnn1, hnn2,
        (by ring : ((C_P + 8 * Real.sqrt (C_d + 1)) + 2 * C_e + C_cp) *
            Real.sqrt l * (c / Real.log N + c ^ 3 / N) =
          (C_P + 8 * Real.sqrt (C_d + 1)) * Real.sqrt l * (c / Real.log N) +
            2 * C_e * Real.sqrt l * (c ^ 3 / N) +
            C_cp * Real.sqrt l * (c / Real.log N + c ^ 3 / N) +
            2 * C_e * Real.sqrt l * (c / Real.log N) +
            (C_P + 8 * Real.sqrt (C_d + 1)) * Real.sqrt l * (c ^ 3 / N))]
    refine hsum_bi.trans ?_
    have : 0 ≤ C_sq := by dsimp only [C_sq]; positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [this]) (Real.sqrt_nonneg _))
      (by positivity)

/-- Non-ground (`2 ≤ m`) logarithm-free `L^2` and bilinear bounds on `coreNearRow φ c N m` via
zero-mean periodic summation by parts on `nearRowIndices c N n`. -/
private lemma coreNearRow_ge_two_log_free_bounds {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C_two : ℝ, 0 < C_two ∧
      ∀ {m N : ℕ} {c : ℝ},
        2 ≤ m → 1 ≤ c → 1 ≤ Real.log (N : ℝ) →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        (∑ n ∈ Icc 1 N, coreNearRow φ c N m n ^ 2) / Real.log N ≤
          C_two * (m : ℝ) ^ 2 * (c ^ 2 / Real.log N) ∧
        ∀ {l : ℕ}, 0 < l →
          |(Real.sqrt (Real.log N))⁻¹ *
              ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
                coreNearRow φ c N m n| ≤
            C_two * (m : ℝ) * Real.sqrt l * (c / Real.log N) := by
  obtain ⟨K_lip, hlip⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  let S₁ := |completeWeilPoleShift φ 1|
  let C_half := 2 * Real.exp 1 + 4 * Real.exp 5 * (K_lip : ℝ) / (∫ u, φ u ^ 2)
  let C_BV := 2 * C_half
  let C_sq := 2 * (512 * C_BV ^ 2 + 9 * S₁ ^ 2)
  let C_bi := 64 * C_BV + 3 * S₁
  refine ⟨C_sq + C_bi + 1, by dsimp only [C_sq, C_bi, C_BV, C_half, S₁]; positivity, ?_⟩
  intro m N c hm2 hc1 hL1 hradN
  have hm : 0 < m := by omega
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hsL0 : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hL0
  have he2_ge4 : (4 : ℝ) ≤ Real.exp 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have hp : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [h2, hp]
  have hR_ge8 : 8 * c ≤ linearNearRowRadius c := by
    unfold linearNearRowRadius; nlinarith only [hc0, he2_ge4]
  have hR1 : 1 ≤ linearNearRowRadius c := by linarith only [hc1, hR_ge8]
  have h8R : 8 * linearNearRowRadius c ≤ N := by
    nlinarith only [sq_nonneg (linearNearRowRadius c), hradN]
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith only [hR1, h8R]
    exact_mod_cast this
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hw1 : c / N ≤ 1 := (div_le_one hN0).mpr (by linarith only [hc0, hR_ge8, h8R])
  have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  -- Log-radius comparison: `1 + Real.log (linearNearRowRadius c) ≤ 4 * (1 + Real.log c)`.
  have hlogR_le : 1 + Real.log (linearNearRowRadius c) ≤ 4 * (1 + Real.log c) := by
    unfold linearNearRowRadius
    rw [show 2 * c * Real.exp 2 = 2 * Real.exp 2 * c by ring,
      Real.log_mul (by positivity) hc0.ne', Real.log_mul zero_lt_two.ne' (Real.exp_pos 2).ne',
      Real.log_exp]
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    linarith only [hl2, hlogc0]
  have hmid_inv : (∑ n ∈ Icc 1 N,
      if 1 < 2 * (n : ℝ) * (linearNearRowRadius c / N) then 1 / (n : ℝ) else 0) ≤
      16 * (1 + Real.log c) :=
    (sum_mid_rows_inv_le hR1 h8R).trans (by linarith only [hlogR_le])
  -- Pointwise bound on the near-center part at `2 ≤ m` via `abs_sum_archimedeanCenterKernel_poleProfile_le`.
  have hcen_pt : ∀ n ∈ Icc 1 N,
      |∑ j ∈ nearRowIndices c N n,
          completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
            normalizedRamanujanMode m j / Real.sqrt j| ≤
        3 * S₁ * c * (m : ℝ) * Real.sqrt n / N := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    let P_n : ℕ → Prop := fun j => 1 ≤ j ∧ |Real.log (j : ℝ) - Real.log n| ≤ 2 * c / N
    have hconv : ∀ ⦃i j r : ℕ⦄, i ≤ j → j ≤ r → P_n i → P_n r → P_n j := by
      intro i j r hij hjr hi hr
      have hj1 : 1 ≤ j := hi.1.trans hij
      have hi0 : (0 : ℝ) < i := by exact_mod_cast hi.1
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.1
      have hli : Real.log (i : ℝ) ≤ Real.log j := Real.log_le_log hi0 (by exact_mod_cast hij)
      have hlr : Real.log (j : ℝ) ≤ Real.log r := Real.log_le_log hj0 (by exact_mod_cast hjr)
      refine ⟨hj1, abs_le.mpr ⟨?_, ?_⟩⟩
      · linarith only [(abs_le.mp hi.2).1, hli]
      · linarith only [(abs_le.mp hr.2).2, hlr]
    let a_n : ℕ → ℝ := fun j => if P_n j then normalizedRamanujanMode m j else 0
    have hsm_le_m : Real.sqrt (m : ℝ) ≤ m := by
      calc
        Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith only [hm1R])
        _ = m := Real.sqrt_sq (Nat.cast_nonneg m)
    have ha_n : |a_n n| ≤ (m : ℝ) := by
      dsimp only [a_n]; split_ifs
      · exact (abs_mode_le_sqrt_conductor hm n).trans hsm_le_m
      · rw [abs_zero]; exact Nat.cast_nonneg m
    have hB_n : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, a_n j| ≤ (m : ℝ) := by
      intro l k hlk
      obtain ⟨L, U, hLU, hfilt⟩ := filter_Ico_eq_Ico_of_ordConvex hconv l k
      have hsf : (∑ j ∈ Ico l k, a_n j) = ∑ j ∈ (Ico l k).filter P_n, normalizedRamanujanMode m j := by
        dsimp only [a_n]; rw [sum_filter]
      rw [hsf, hfilt]
      exact CompletedArithmeticForms.abs_sum_Ico_normalizedRamanujanMode_le hm2 hLU
    have hsum_eq : (∑ j ∈ nearRowIndices c N n,
        completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
          normalizedRamanujanMode m j / Real.sqrt j) =
        (completeWeilPoleShift φ c / N) *
          ∑ j ∈ Icc 1 N, archimedeanCenterKernel n j * (a_n j / Real.sqrt j) := by
      rw [mul_sum, nearRowIndices, sum_filter]
      refine sum_congr rfl fun j hj => ?_
      have hj1 := (mem_Icc.mp hj).1
      by_cases hjn : j = n
      · subst hjn
        rw [if_neg (by simp), archimedeanCenterKernel_self, zero_mul, mul_zero]
      · by_cases hlog : |Real.log (j : ℝ) - Real.log n| ≤ 2 * c / N
        · have hPj : P_n j := ⟨hj1, hlog⟩
          rw [if_pos ⟨hjn, hlog⟩]
          dsimp only [a_n]
          rw [if_pos hPj]; ring
        · have hnPj : ¬ P_n j := fun h => hlog h.2
          rw [if_neg (fun h => hlog h.2)]
          dsimp only [a_n]
          rw [if_neg hnPj, zero_div, mul_zero, mul_zero]
    have hshift : |completeWeilPoleShift φ c| = S₁ * c := by
      have h1 : completeWeilPoleShift φ c = completeWeilPoleShift φ 1 * c := by
        unfold completeWeilPoleShift; ring
      rw [h1, abs_mul, abs_of_pos hc0]
    rw [hsum_eq, abs_mul, abs_div, hshift, abs_of_pos hN0]
    have hker := abs_sum_archimedeanCenterKernel_poleProfile_le hn (Nat.cast_nonneg m) ha_n hB_n
    exact (mul_le_mul_of_nonneg_left hker (by dsimp only [S₁]; positivity)).trans_eq (by ring)
  -- Pointwise BV bound on `nearGram` at `2 ≤ m`, supported on `1 < 2 * n * (linearNearRowRadius c / N)`.
  have hng_pt : ∀ n ∈ Icc 1 N,
      |nearGram φ c N (fun j => normalizedRamanujanMode m j / Real.sqrt j) n| ≤
        if 1 < 2 * (n : ℝ) * (linearNearRowRadius c / N) then
          C_BV * (m : ℝ) / Real.sqrt n else 0 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    obtain ⟨hcard_n, hpt_n⟩ := nearRowIndices_card_and_pointwise hφ hsupp hM hc0 hN0 hw1 hn
    by_cases hact : 1 < 2 * (n : ℝ) * (linearNearRowRadius c / N)
    · rw [if_pos hact]
      let P_n : ℕ → Prop := fun j => 1 ≤ j ∧ |Real.log (j : ℝ) - Real.log n| ≤ 2 * c / N
      have hconv : ∀ ⦃i j r : ℕ⦄, i ≤ j → j ≤ r → P_n i → P_n r → P_n j := by
        intro i j r hij hjr hi hr
        have hj1 : 1 ≤ j := hi.1.trans hij
        have hi0 : (0 : ℝ) < i := by exact_mod_cast hi.1
        have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
        have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.1
        have hli : Real.log (i : ℝ) ≤ Real.log j := Real.log_le_log hi0 (by exact_mod_cast hij)
        have hlr : Real.log (j : ℝ) ≤ Real.log r := Real.log_le_log hj0 (by exact_mod_cast hjr)
        refine ⟨hj1, abs_le.mpr ⟨?_, ?_⟩⟩
        · linarith only [(abs_le.mp hi.2).1, hli]
        · linarith only [(abs_le.mp hr.2).2, hlr]
      let w_n : ℕ → ℝ := fun j =>
        (shellAutocorr φ (|Real.log (j : ℝ) - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)) /
          Real.sqrt j
      -- Sub-interval BV bound on any `Ico a b ⊆ nearRowIndices c N n`.
      have hsub_bv : ∀ a b : ℕ, Ico a b ⊆ nearRowIndices c N n →
          |∑ j ∈ Ico a b, w_n j * normalizedRamanujanMode m j| ≤
            C_half * (m : ℝ) / Real.sqrt n := by
        intro a b hsub
        have hbv := abs_sum_Ico_mul_le_of_bv (w := w_n) (B := (m : ℝ)) (Nat.cast_nonneg m)
          (a := a) (b := b) (fun l k hlk =>
            CompletedArithmeticForms.abs_sum_Ico_normalizedRamanujanMode_le hm2 hlk)
        have hterm1 : (if a < b then |w_n (b - 1)| else 0) ≤ Real.exp 1 / Real.sqrt n := by
          split_ifs with hab
          · have hb_mem : b - 1 ∈ nearRowIndices c N n :=
              hsub (mem_Ico.mpr ⟨by omega, by omega⟩)
            obtain ⟨hsj, hq, _, _⟩ := hpt_n (b - 1) hb_mem
            dsimp only [w_n]
            rw [div_eq_mul_one_div, abs_mul,
              abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt ((b - 1 : ℕ) : ℝ))]
            exact (mul_le_mul hq hsj (by positivity) zero_le_one).trans_eq (one_mul _)
          · positivity
        have hterm2 : (∑ j ∈ Ico a (b - 1), |w_n j - w_n (j + 1)|) ≤
            (Real.exp 1 + 4 * Real.exp 5 * (K_lip : ℝ) / (∫ u, φ u ^ 2)) / Real.sqrt n := by
          rcases le_or_gt (b - 1) a with hba' | hab'
          · rw [Ico_eq_empty (not_lt.mpr hba'), sum_empty]; positivity
          · let q_n : ℕ → ℝ := fun k =>
              shellAutocorr φ (|Real.log (k : ℝ) - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)
            have hstep : ∀ j ∈ Ico a (b - 1),
                |w_n j - w_n (j + 1)| ≤
                  (((K_lip : ℝ) * Real.exp 2 / (∫ u, φ u ^ 2)) * (N / (c * n))) *
                      (Real.exp 1 / Real.sqrt n) +
                    (1 / Real.sqrt j - 1 / Real.sqrt (j + 1 : ℕ)) := by
              intro j hj
              obtain ⟨haj, hjb1⟩ := mem_Ico.mp hj
              have hj_mem : j ∈ nearRowIndices c N n := hsub (mem_Ico.mpr ⟨haj, by omega⟩)
              have hj1_mem : j + 1 ∈ nearRowIndices c N n := hsub (mem_Ico.mpr ⟨by omega, by omega⟩)
              obtain ⟨hsj, _, _, _⟩ := hpt_n j hj_mem
              obtain ⟨_, hq1, _, _⟩ := hpt_n (j + 1) hj1_mem
              have hj1_pos : (0 : ℝ) < j :=
                by exact_mod_cast (mem_Icc.mp (mem_filter.mp hj_mem).1).1
              have hj2_pos : (0 : ℝ) < (j + 1 : ℕ) := by positivity
              have hs_mono : 0 ≤ 1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ) :=
                sub_nonneg.mpr (one_div_le_one_div_of_le (Real.sqrt_pos.mpr hj1_pos)
                  (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ j)))
              have hinv_j : 1 / (j : ℝ) ≤ Real.exp 2 / n := by
                have hsq := pow_le_pow_left₀ (by positivity) hsj 2
                rwa [div_pow, div_pow, one_pow, Real.sq_sqrt hj1_pos.le, Real.sq_sqrt hn0.le,
                  show Real.exp 1 ^ 2 = Real.exp 2 by rw [sq, ← Real.exp_add]; norm_num] at hsq
              have hlog_step : |Real.log ((j + 1 : ℕ) : ℝ) - Real.log j| ≤ 1 / (j : ℝ) := by
                have hpos_q : 0 < ((j + 1 : ℕ) : ℝ) / j := div_pos hj2_pos hj1_pos
                have hge1 : 1 ≤ ((j + 1 : ℕ) : ℝ) / j :=
                  (one_le_div hj1_pos).mpr (by exact_mod_cast Nat.le_succ j)
                rw [← Real.log_div hj2_pos.ne' hj1_pos.ne', abs_of_nonneg (Real.log_nonneg hge1)]
                have hl := Real.log_le_sub_one_of_pos hpos_q
                have hq_eq : ((j + 1 : ℕ) : ℝ) / j - 1 = 1 / (j : ℝ) := by
                  field_simp [hj1_pos.ne']; push_cast; ring
                linarith only [hl, hq_eq]
              have harg_diff : |(|Real.log (j : ℝ) - Real.log n| / (c / N) -
                  |Real.log ((j + 1 : ℕ) : ℝ) - Real.log n| / (c / N))| ≤
                  Real.exp 2 * (N / (c * n)) := by
                rw [← sub_div, abs_div, abs_of_pos hw0]
                have hrev := abs_abs_sub_abs_le_abs_sub
                  (Real.log (j : ℝ) - Real.log n) (Real.log ((j + 1 : ℕ) : ℝ) - Real.log n)
                rw [show (Real.log (j : ℝ) - Real.log n) -
                    (Real.log ((j + 1 : ℕ) : ℝ) - Real.log n) =
                    -(Real.log ((j + 1 : ℕ) : ℝ) - Real.log j) by ring, abs_neg] at hrev
                calc
                  _ ≤ (1 / (j : ℝ)) / (c / N) :=
                    div_le_div_of_nonneg_right (hrev.trans hlog_step) hw0.le
                  _ ≤ (Real.exp 2 / n) / (c / N) :=
                    div_le_div_of_nonneg_right hinv_j hw0.le
                  _ = Real.exp 2 * (N / (c * n)) := by
                    field_simp [hn0.ne', hc0.ne', hN0.ne']
              have hq_diff : |q_n j - q_n (j + 1)| ≤
                  ((K_lip : ℝ) * Real.exp 2 / (∫ u, φ u ^ 2)) * (N / (c * n)) := by
                dsimp only [q_n]
                rw [← sub_div, abs_div, abs_of_pos hM]
                have hd := hlip.dist_le_mul (|Real.log (j : ℝ) - Real.log n| / (c / N))
                  (|Real.log ((j + 1 : ℕ) : ℝ) - Real.log n| / (c / N))
                simp only [Real.dist_eq] at hd
                calc
                  _ ≤ ((K_lip : ℝ) * (Real.exp 2 * (N / (c * n)))) / (∫ u, φ u ^ 2) :=
                    div_le_div_of_nonneg_right
                      (hd.trans (mul_le_mul_of_nonneg_left harg_diff K_lip.coe_nonneg)) hM.le
                  _ = ((K_lip : ℝ) * Real.exp 2 / (∫ u, φ u ^ 2)) * (N / (c * n)) := by ring
              have hw_split : w_n j - w_n (j + 1) =
                  (q_n j - q_n (j + 1)) * (1 / Real.sqrt j) +
                    q_n (j + 1) * (1 / Real.sqrt j - 1 / Real.sqrt (j + 1 : ℕ)) := by
                dsimp only [w_n, q_n]; ring
              rw [hw_split]
              refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
              · rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (j : ℝ))]
                exact mul_le_mul hq_diff hsj (by positivity) (by positivity)
              · rw [abs_mul, abs_of_nonneg hs_mono]
                exact (mul_le_mul_of_nonneg_right hq1 hs_mono).trans_eq (one_mul _)
            have htel : (∑ j ∈ Ico a (b - 1),
                (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ))) ≤
                Real.exp 1 / Real.sqrt n := by
              have htel_eq : ∀ k : ℕ, (∑ j ∈ Ico a (a + k),
                  (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ))) =
                  1 / Real.sqrt (a : ℝ) - 1 / Real.sqrt ((a + k : ℕ) : ℝ) := by
                intro k
                induction k with
                | zero => simp
                | succ k ih =>
                  rw [show a + (k + 1) = (a + k) + 1 by omega, sum_Ico_succ_top (by omega), ih]
                  ring
              obtain ⟨k, hk⟩ : ∃ k : ℕ, b - 1 = a + k := ⟨b - 1 - a, by omega⟩
              rw [hk, htel_eq k]
              have ha_mem : a ∈ nearRowIndices c N n := hsub (mem_Ico.mpr ⟨le_rfl, by omega⟩)
              obtain ⟨hsa, _, _, _⟩ := hpt_n a ha_mem
              linarith only [hsa, (by positivity : 0 ≤ 1 / Real.sqrt ((a + k : ℕ) : ℝ))]
            have hcard_ico : ((Ico a (b - 1)).card : ℝ) ≤ 2 * (n : ℝ) * (linearNearRowRadius c / N) := by
              have hsub' : Ico a (b - 1) ⊆ nearRowIndices c N n :=
                (Ico_subset_Ico_right (Nat.sub_le b 1)).trans hsub
              exact (show ((Ico a (b - 1)).card : ℝ) ≤ ((nearRowIndices c N n).card : ℝ) by
                exact_mod_cast card_le_card hsub').trans hcard_n
            have hexp5 : Real.exp 2 * Real.exp 2 * Real.exp 1 = Real.exp 5 := by
              rw [← Real.exp_add, ← Real.exp_add]; norm_num
            calc
              (∑ j ∈ Ico a (b - 1), |w_n j - w_n (j + 1)|)
                  ≤ ∑ j ∈ Ico a (b - 1),
                      ((((K_lip : ℝ) * Real.exp 2 / (∫ u, φ u ^ 2)) * (N / (c * n))) *
                          (Real.exp 1 / Real.sqrt n) +
                        (1 / Real.sqrt j - 1 / Real.sqrt (j + 1 : ℕ))) := sum_le_sum hstep
              _ = ((Ico a (b - 1)).card : ℝ) *
                    ((((K_lip : ℝ) * Real.exp 2 / (∫ u, φ u ^ 2)) * (N / (c * n))) *
                      (Real.exp 1 / Real.sqrt n)) +
                  ∑ j ∈ Ico a (b - 1), (1 / Real.sqrt j - 1 / Real.sqrt (j + 1 : ℕ)) := by
                rw [sum_add_distrib, sum_const, nsmul_eq_mul]
              _ ≤ (2 * (n : ℝ) * (linearNearRowRadius c / N)) *
                    ((((K_lip : ℝ) * Real.exp 2 / (∫ u, φ u ^ 2)) * (N / (c * n))) *
                      (Real.exp 1 / Real.sqrt n)) +
                  Real.exp 1 / Real.sqrt n :=
                add_le_add (mul_le_mul_of_nonneg_right hcard_ico (by positivity)) htel
              _ = (Real.exp 1 + 4 * Real.exp 5 * (K_lip : ℝ) / (∫ u, φ u ^ 2)) / Real.sqrt n := by
                unfold linearNearRowRadius
                field_simp [hM.ne', hc0.ne', hn0.ne', hN0.ne', hsn.ne']
                rw [show (K_lip : ℝ) * Real.exp 2 * Real.exp 1 * (2 * Real.exp 2) =
                  2 * (K_lip : ℝ) * (Real.exp 2 * Real.exp 2 * Real.exp 1) by ring, hexp5]
                ring
        calc
          |∑ j ∈ Ico a b, w_n j * normalizedRamanujanMode m j|
              ≤ (m : ℝ) * (Real.exp 1 / Real.sqrt n +
                  (Real.exp 1 + 4 * Real.exp 5 * (K_lip : ℝ) / (∫ u, φ u ^ 2)) / Real.sqrt n) :=
            hbv.trans (mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (Nat.cast_nonneg m))
          _ = C_half * (m : ℝ) / Real.sqrt n := by dsimp only [C_half]; ring
      -- Split `nearRowIndices c N n` into `S_lo = (Ico 1 n).filter P_n` and `S_hi = (Ico (n+1) (N+1)).filter P_n`.
      let S_lo := (Ico 1 n).filter P_n
      let S_hi := (Ico (n + 1) (N + 1)).filter P_n
      have hdisj : Disjoint S_lo S_hi :=
        disjoint_left.mpr fun j h1 h2 => by
          have := (mem_Ico.mp (mem_filter.mp h1).1).2
          have := (mem_Ico.mp (mem_filter.mp h2).1).1
          omega
      have hsplit_nr : nearRowIndices c N n = S_lo ∪ S_hi := by
        ext j
        simp only [nearRowIndices, S_lo, S_hi, P_n, mem_union, mem_filter, mem_Icc, mem_Ico]
        constructor
        · rintro ⟨⟨hj1, hjN⟩, hjn, hlog⟩
          rcases lt_or_gt_of_ne hjn with hlt | hgt
          · exact Or.inl ⟨⟨hj1, hlt⟩, hj1, hlog⟩
          · exact Or.inr ⟨⟨by omega, by omega⟩, hj1, hlog⟩
        · rintro (⟨⟨hj1, hlt⟩, _, hlog⟩ | ⟨⟨hgt, hjN⟩, hj1, hlog⟩)
          · exact ⟨⟨hj1, hlt.le.trans (mem_Icc.mp hn).2⟩, by omega, hlog⟩
          · exact ⟨⟨hj1, by omega⟩, by omega, hlog⟩
      obtain ⟨L₁, U₁, _, hlo_eq⟩ := filter_Ico_eq_Ico_of_ordConvex hconv 1 n
      obtain ⟨L₂, U₂, _, hhi_eq⟩ := filter_Ico_eq_Ico_of_ordConvex hconv (n + 1) (N + 1)
      have hsub1 : Ico L₁ U₁ ⊆ nearRowIndices c N n := by
        rw [← hlo_eq, hsplit_nr]; exact subset_union_left
      have hsub2 : Ico L₂ U₂ ⊆ nearRowIndices c N n := by
        rw [← hhi_eq, hsplit_nr]; exact subset_union_right
      have hng_eq : nearGram φ c N (fun j => normalizedRamanujanMode m j / Real.sqrt j) n =
          (∑ j ∈ Ico L₁ U₁, w_n j * normalizedRamanujanMode m j) +
            ∑ j ∈ Ico L₂ U₂, w_n j * normalizedRamanujanMode m j := by
        unfold nearGram
        have hpt_w : ∀ j : ℕ,
            (shellAutocorr φ (|Real.log (j : ℝ) - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)) *
              (normalizedRamanujanMode m j / Real.sqrt j) =
              w_n j * normalizedRamanujanMode m j := fun _ => by dsimp only [w_n]; ring
        simp_rw [hpt_w]
        rw [hsplit_nr, sum_union hdisj, ← hlo_eq, ← hhi_eq]
      rw [hng_eq]
      exact ((abs_add_le _ _).trans (add_le_add (hsub_bv L₁ U₁ hsub1) (hsub_bv L₂ U₂ hsub2))).trans_eq
        (by dsimp only [C_BV]; ring)
    · rw [if_neg hact]
      have hempty : nearRowIndices c N n = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro j hj
        obtain ⟨hjN, hjn, hlog⟩ := mem_filter.mp hj
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
        have he_gap : Real.exp (2 * c / N) - 1 ≤ linearNearRowRadius c / N := by
          calc
            Real.exp (2 * c / N) - 1 ≤ 2 * c / N * Real.exp (2 * c / N) := exp_sub_one_le_mul_exp
            _ ≤ 2 * c / N * Real.exp 2 :=
              mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr (by
                  have h := mul_le_mul_of_nonneg_left hw1 zero_le_two
                  simpa only [mul_div_assoc, mul_one] using h)) (by positivity)
            _ = linearNearRowRadius c / N := by unfold linearNearRowRadius; ring
        have hdist := (abs_sub_le_of_abs_log_le hj0 hn0 hlog).trans
          (mul_le_mul_of_nonneg_left he_gap hn0.le)
        have hge1 : (1 : ℝ) ≤ |(j : ℝ) - n| := by
          rcases lt_or_gt_of_ne hjn with hlt | hgt
          · have h1 : (j : ℝ) + 1 ≤ n := by exact_mod_cast hlt
            rw [abs_of_neg (by linarith only [h1])]; linarith only [h1]
          · have h1 : (n : ℝ) + 1 ≤ j := by exact_mod_cast hgt
            rw [abs_of_pos (by linarith only [h1])]; linarith only [h1]
        have hle_half : 2 * (n : ℝ) * (linearNearRowRadius c / N) ≤ 1 := not_lt.mp hact
        linarith only [hge1, hdist, hle_half]
      unfold nearGram
      rw [hempty, sum_empty, abs_zero]
  have h1c_sq : (1 + Real.log c) ^ 2 ≤ 4 * c := one_add_log_sq_le_four_mul hc1
  have h1c_cube : (1 + Real.log c) ^ 3 ≤ 8 * c ^ 2 := one_add_log_cube_le_eight_sq hc1
  constructor
  · -- Part 1: `L^2` squared sum bound.
    have hsq_A : (∑ n ∈ Icc 1 N,
        (-Real.log c * nearGram φ c N (fun j => normalizedRamanujanMode m j / Real.sqrt j) n) ^ 2) ≤
        512 * C_BV ^ 2 * (m : ℝ) ^ 2 * c ^ 2 := by
      have hpt : ∀ n ∈ Icc 1 N,
          (-Real.log c * nearGram φ c N (fun j => normalizedRamanujanMode m j / Real.sqrt j) n) ^ 2 ≤
            Real.log c ^ 2 * C_BV ^ 2 * (m : ℝ) ^ 2 *
              (if 1 < 2 * (n : ℝ) * (linearNearRowRadius c / N) then 1 / (n : ℝ) else 0) := by
        intro n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have h1 := hng_pt n hn
        rw [show (-Real.log c * nearGram φ c N
              (fun j => normalizedRamanujanMode m j / Real.sqrt j) n) ^ 2 =
            Real.log c ^ 2 * |nearGram φ c N
              (fun j => normalizedRamanujanMode m j / Real.sqrt j) n| ^ 2 by
          rw [sq_abs]; ring]
        have hsq := pow_le_pow_left₀ (abs_nonneg _) h1 2
        refine (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)).trans_eq ?_
        split_ifs
        · rw [div_pow, Real.sq_sqrt hn0.le]; ring
        · simp
      have hlog3 : Real.log c ^ 2 * (16 * (1 + Real.log c)) ≤ 512 * c ^ 2 := by
        have h1 : Real.log c ≤ 1 + Real.log c := by linarith
        have h2 : Real.log c ^ 2 * (1 + Real.log c) ≤ (1 + Real.log c) ^ 3 := by
          have hp := pow_le_pow_left₀ hlogc0 h1 2
          exact (mul_le_mul_of_nonneg_right hp (by linarith)).trans_eq (by ring)
        nlinarith only [h2, h1c_cube]
      calc
        _ ≤ ∑ n ∈ Icc 1 N, Real.log c ^ 2 * C_BV ^ 2 * (m : ℝ) ^ 2 *
              (if 1 < 2 * (n : ℝ) * (linearNearRowRadius c / N) then 1 / (n : ℝ) else 0) :=
          sum_le_sum hpt
        _ = C_BV ^ 2 * (m : ℝ) ^ 2 * (Real.log c ^ 2 *
              ∑ n ∈ Icc 1 N, if 1 < 2 * (n : ℝ) * (linearNearRowRadius c / N) then 1 / (n : ℝ) else 0) := by
          rw [← mul_sum]; ring
        _ ≤ C_BV ^ 2 * (m : ℝ) ^ 2 * (Real.log c ^ 2 * (16 * (1 + Real.log c))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmid_inv (sq_nonneg _)) (by positivity)
        _ ≤ C_BV ^ 2 * (m : ℝ) ^ 2 * (512 * c ^ 2) :=
          mul_le_mul_of_nonneg_left hlog3 (by positivity)
        _ = 512 * C_BV ^ 2 * (m : ℝ) ^ 2 * c ^ 2 := by ring
    have hsq_B : (∑ n ∈ Icc 1 N,
        (∑ j ∈ nearRowIndices c N n,
          completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
            normalizedRamanujanMode m j / Real.sqrt j) ^ 2) ≤
        9 * S₁ ^ 2 * (m : ℝ) ^ 2 * c ^ 2 := by
      have hpt : ∀ n ∈ Icc 1 N,
          (∑ j ∈ nearRowIndices c N n,
            completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
              normalizedRamanujanMode m j / Real.sqrt j) ^ 2 ≤
            9 * S₁ ^ 2 * (m : ℝ) ^ 2 * c ^ 2 / N := by
        intro n hn
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
        have hsq := pow_le_pow_left₀ (abs_nonneg _) (hcen_pt n hn) 2
        rw [sq_abs, div_pow, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at hsq
        have hn1_div : (n : ℝ) / N ≤ 1 := (div_le_one hN0).mpr hnN
        calc
          _ ≤ 3 ^ 2 * S₁ ^ 2 * c ^ 2 * (m : ℝ) ^ 2 * n / N ^ 2 := hsq
          _ = (9 * S₁ ^ 2 * (m : ℝ) ^ 2 * c ^ 2 / N) * ((n : ℝ) / N) := by ring
          _ ≤ (9 * S₁ ^ 2 * (m : ℝ) ^ 2 * c ^ 2 / N) * 1 :=
            mul_le_mul_of_nonneg_left hn1_div (by dsimp only [S₁]; positivity)
          _ = 9 * S₁ ^ 2 * (m : ℝ) ^ 2 * c ^ 2 / N := mul_one _
      calc
        _ ≤ ∑ _n ∈ Icc 1 N, (9 * S₁ ^ 2 * (m : ℝ) ^ 2 * c ^ 2 / N) := sum_le_sum hpt
        _ = 9 * S₁ ^ 2 * (m : ℝ) ^ 2 * c ^ 2 := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          field_simp [hN0.ne']
    have hpt_tot : ∀ n ∈ Icc 1 N, coreNearRow φ c N m n ^ 2 ≤
        2 * (-Real.log c * nearGram φ c N (fun j => normalizedRamanujanMode m j / Real.sqrt j) n) ^ 2 +
          2 * (∑ j ∈ nearRowIndices c N n,
            completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
              normalizedRamanujanMode m j / Real.sqrt j) ^ 2 := fun n _ => by
      unfold coreNearRow
      set A := -Real.log c * nearGram φ c N (fun j => normalizedRamanujanMode m j / Real.sqrt j) n
      set B := ∑ j ∈ nearRowIndices c N n,
        completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
          normalizedRamanujanMode m j / Real.sqrt j
      nlinarith only [sq_nonneg (A - B)]
    calc
      (∑ n ∈ Icc 1 N, coreNearRow φ c N m n ^ 2) / Real.log N
          ≤ (2 * (512 * C_BV ^ 2 * (m : ℝ) ^ 2 * c ^ 2) +
              2 * (9 * S₁ ^ 2 * (m : ℝ) ^ 2 * c ^ 2)) / Real.log N := by
        refine div_le_div_of_nonneg_right ?_ hL0.le
        have hsum := sum_le_sum hpt_tot
        rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
        linarith only [hsum, hsq_A, hsq_B]
      _ = C_sq * (m : ℝ) ^ 2 * (c ^ 2 / Real.log N) := by dsimp only [C_sq]; ring
      _ ≤ (C_sq + C_bi + 1) * (m : ℝ) ^ 2 * (c ^ 2 / Real.log N) := by
        have : 0 ≤ C_bi := by dsimp only [C_bi, C_BV, C_half, S₁]; positivity
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith only [this]) (sq_nonneg _)) (by positivity)
  · -- Part 2: Bilinear pairing bound against `normalizedRamanujanHorizonVector l N`.
    intro l hl
    have hbi_A : |(Real.sqrt (Real.log N))⁻¹ *
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          (-Real.log c * nearGram φ c N (fun j => normalizedRamanujanMode m j / Real.sqrt j) n)| ≤
        64 * C_BV * (m : ℝ) * Real.sqrt l * (c / Real.log N) := by
      have hpt : ∀ n ∈ Icc 1 N,
          |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              (-Real.log c * nearGram φ c N
                (fun j => normalizedRamanujanMode m j / Real.sqrt j) n)| ≤
            (Real.sqrt l / Real.sqrt (Real.log N)) * Real.log c * C_BV * (m : ℝ) *
              (if 1 < 2 * (n : ℝ) * (linearNearRowRadius c / N) then 1 / (n : ℝ) else 0) := by
        intro n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
        have hvl_n : |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n| ≤
            Real.sqrt l / (Real.sqrt n * Real.sqrt (Real.log N)) := by
          rw [primeHorizonExtension_normalizedRamanujan hn]
          unfold ramanujanPoleProfile
          rw [abs_mul, abs_div, abs_of_pos (inv_pos.mpr hsL0), abs_of_pos hsn]
          exact (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (abs_mode_le_sqrt_conductor hl n) hsn.le)
            (by positivity)).trans_eq (by ring)
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hlogc0]
        have h1 := mul_le_mul hvl_n (mul_le_mul_of_nonneg_left (hng_pt n hn) hlogc0)
          (by positivity) (by positivity)
        refine h1.trans_eq ?_
        split_ifs
        · field_simp [hsn.ne', hsL0.ne']; rw [Real.sq_sqrt hn0.le]; ring
        · simp
      have hlog2 : Real.log c * (16 * (1 + Real.log c)) ≤ 64 * c := by
        have h1 : Real.log c * (1 + Real.log c) ≤ (1 + Real.log c) ^ 2 := by
          nlinarith only [hlogc0]
        nlinarith only [h1, h1c_sq]
      rw [abs_mul, abs_of_pos (inv_pos.mpr hsL0)]
      calc
        _ ≤ (Real.sqrt (Real.log N))⁻¹ *
              (((Real.sqrt l / Real.sqrt (Real.log N)) * Real.log c * C_BV * (m : ℝ)) *
                ∑ n ∈ Icc 1 N,
                  if 1 < 2 * (n : ℝ) * (linearNearRowRadius c / N) then 1 / (n : ℝ) else 0) := by
          rw [mul_sum]
          exact mul_le_mul_of_nonneg_left
            ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)) (by positivity)
        _ ≤ (Real.sqrt (Real.log N))⁻¹ *
              (((Real.sqrt l / Real.sqrt (Real.log N)) * Real.log c * C_BV * (m : ℝ)) *
                (16 * (1 + Real.log c))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmid_inv (by dsimp only [C_BV, C_half]; positivity))
            (by positivity)
        _ = C_BV * (m : ℝ) * Real.sqrt l * (Real.log c * (16 * (1 + Real.log c))) / Real.log N := by
          field_simp [hsL0.ne', hL0.ne']; rw [Real.sq_sqrt hL0.le]; ring
        _ ≤ 64 * C_BV * (m : ℝ) * Real.sqrt l * (c / Real.log N) := by
          refine (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog2 (by dsimp only [C_BV, C_half]; positivity))
            hL0.le).trans_eq (by ring)
    have hbi_B : |(Real.sqrt (Real.log N))⁻¹ *
        ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          (∑ j ∈ nearRowIndices c N n,
            completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
              normalizedRamanujanMode m j / Real.sqrt j)| ≤
        3 * S₁ * (m : ℝ) * Real.sqrt l * (c / Real.log N) := by
      have hpt : ∀ n ∈ Icc 1 N,
          |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              (∑ j ∈ nearRowIndices c N n,
                completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
                  normalizedRamanujanMode m j / Real.sqrt j)| ≤
            3 * S₁ * (m : ℝ) * Real.sqrt l * c / (N * Real.sqrt (Real.log N)) := by
        intro n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
        have hvl_n : |primeHorizonExtension (normalizedRamanujanHorizonVector l N) n| ≤
            Real.sqrt l / (Real.sqrt n * Real.sqrt (Real.log N)) := by
          rw [primeHorizonExtension_normalizedRamanujan hn]
          unfold ramanujanPoleProfile
          rw [abs_mul, abs_div, abs_of_pos (inv_pos.mpr hsL0), abs_of_pos hsn]
          exact (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (abs_mode_le_sqrt_conductor hl n) hsn.le)
            (by positivity)).trans_eq (by ring)
        rw [abs_mul]
        calc
          _ ≤ (Real.sqrt l / (Real.sqrt n * Real.sqrt (Real.log N))) *
                (3 * S₁ * c * (m : ℝ) * Real.sqrt n / N) :=
            mul_le_mul hvl_n (hcen_pt n hn) (abs_nonneg _) (by positivity)
          _ = 3 * S₁ * (m : ℝ) * Real.sqrt l * c / (N * Real.sqrt (Real.log N)) := by
            field_simp [hsn.ne', hsL0.ne', hN0.ne']
      rw [abs_mul, abs_of_pos (inv_pos.mpr hsL0)]
      calc
        _ ≤ (Real.sqrt (Real.log N))⁻¹ *
              ∑ _n ∈ Icc 1 N, (3 * S₁ * (m : ℝ) * Real.sqrt l * c / (N * Real.sqrt (Real.log N))) :=
          mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)) (by positivity)
        _ = 3 * S₁ * (m : ℝ) * Real.sqrt l * (c / Real.log N) := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
          field_simp [hsL0.ne', hL0.ne', hN0.ne']
          rw [Real.sq_sqrt hL0.le]; ring
    have hsplit : (Real.sqrt (Real.log N))⁻¹ *
        (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
          coreNearRow φ c N m n) =
        (Real.sqrt (Real.log N))⁻¹ *
          (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            (-Real.log c * nearGram φ c N (fun j => normalizedRamanujanMode m j / Real.sqrt j) n)) +
        (Real.sqrt (Real.log N))⁻¹ *
          (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            (∑ j ∈ nearRowIndices c N n,
              completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
                normalizedRamanujanMode m j / Real.sqrt j)) := by
      have hpt : ∀ n ∈ Icc 1 N,
          primeHorizonExtension (normalizedRamanujanHorizonVector l N) n * coreNearRow φ c N m n =
          primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              (-Real.log c * nearGram φ c N (fun j => normalizedRamanujanMode m j / Real.sqrt j) n) +
            primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              (∑ j ∈ nearRowIndices c N n,
                completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
                  normalizedRamanujanMode m j / Real.sqrt j) := fun _ _ => by
        unfold coreNearRow; ring
      rw [sum_congr rfl hpt, sum_add_distrib, mul_add]
    rw [hsplit]
    have hsum2 : |(Real.sqrt (Real.log N))⁻¹ * (∑ n ∈ Icc 1 N, _) +
          (Real.sqrt (Real.log N))⁻¹ * (∑ n ∈ Icc 1 N, _)| ≤
        C_bi * (m : ℝ) * Real.sqrt l * (c / Real.log N) := by
      have htri := abs_add_le
        ((Real.sqrt (Real.log N))⁻¹ *
          ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            (-Real.log c * nearGram φ c N (fun j => normalizedRamanujanMode m j / Real.sqrt j) n))
        ((Real.sqrt (Real.log N))⁻¹ *
          ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
            (∑ j ∈ nearRowIndices c N n,
              completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
                normalizedRamanujanMode m j / Real.sqrt j))
      dsimp only [C_bi]
      linarith only [htri, hbi_A, hbi_B,
        (by ring : (64 * C_BV + 3 * S₁) * (m : ℝ) * Real.sqrt l * (c / Real.log N) =
          64 * C_BV * (m : ℝ) * Real.sqrt l * (c / Real.log N) +
            3 * S₁ * (m : ℝ) * Real.sqrt l * (c / Real.log N))]
    refine hsum2.trans ?_
    have : 0 ≤ C_sq := by dsimp only [C_sq, C_BV, C_half, S₁]; positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [this]) (Nat.cast_nonneg m))
        (Real.sqrt_nonneg _))
      (by positivity)

/-- **Combined Channels 6 + 7 logarithm-free `L^2` and bilinear bounds.**
Adding `(√φ(m))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m` and `nearCenterVector φ c N m`
cancels the `log c` pole at `m = 1` and eliminates `log c` at `m ≥ 2` by zero-mean summation by
parts. -/
theorem exists_nearGammaDownward_add_nearCenter_log_free {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C_ngc : ℝ, 0 < C_ngc ∧
      ∀ {m N : ℕ} {c : ℝ},
        0 < m → 1 ≤ c → 1 ≤ Real.log (N : ℝ) →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N → c ^ 4 ≤ N →
        ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m +
            nearCenterVector φ c N m‖ ^ 2 ≤
          C_ngc * (m : ℝ) ^ 2 * (c ^ 2 / Real.log N + c ^ 3 * Real.log N / N) ∧
        ∀ {l : ℕ}, 0 < l →
          |⟪(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m +
              nearCenterVector φ c N m,
            normalizedRamanujanHorizonVector l N⟫| ≤
            C_ngc * (m : ℝ) * Real.sqrt l * (c / Real.log N + c ^ 3 / N) := by
  obtain ⟨C_ext, hCext, hext⟩ := exteriorDownward_log_free_bounds hφ hsupp hM
  obtain ⟨C_nc, hCnc, hnc⟩ := nonCore_nearRows_log_free_bounds hφ hsupp hM
  obtain ⟨C_one, hCone, hone⟩ := coreNearRow_one_log_free_bounds hφ hsupp hM
  obtain ⟨C_two, hCtwo, htwo⟩ := coreNearRow_ge_two_log_free_bounds hφ hsupp hM
  let C_core := C_one + C_two
  let C_ngc := 4 * (C_ext + C_nc + C_core) + 1
  refine ⟨C_ngc, by dsimp only [C_ngc, C_core]; positivity, ?_⟩
  intro m N c hm hc1 hL1 hradN hc4N
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hsL0 : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hL0
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have he2_ge4 : (4 : ℝ) ≤ Real.exp 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have hp : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [h2, hp]
  have h8c : 8 * c ≤ N := by
    unfold linearNearRowRadius at hradN
    have h1 : 8 * c ≤ 2 * c * Real.exp 2 := by nlinarith only [hc0, he2_ge4]
    have h2 : 8 * c ≤ (2 * c * Real.exp 2 + 1) ^ 2 := by nlinarith only [h1, hc1]
    linarith only [h2, hradN]
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith only [hc1, h8c]
    exact_mod_cast this
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw3 : c / N ≤ 1 / 3 := (div_le_iff₀ hN0).mpr (by linarith only [hc0, h8c])
  obtain ⟨hext_sq, hext_bi⟩ := hext hm hc1 hL1 hradN
  obtain ⟨hnc_sq, hnc_bi⟩ := hnc hm hc1 hN1 hL0 hw3
  -- Unified `m ≥ 1` bounds on `coreNearRow φ c N m`.
  have hcore : (∑ n ∈ Icc 1 N, coreNearRow φ c N m n ^ 2) / Real.log N ≤
        C_core * (m : ℝ) ^ 2 * (c ^ 2 / Real.log N) ∧
      ∀ {l : ℕ}, 0 < l →
        |(Real.sqrt (Real.log N))⁻¹ *
            ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              coreNearRow φ c N m n| ≤
          C_core * (m : ℝ) * Real.sqrt l * (c / Real.log N + c ^ 3 / N) := by
    by_cases hm1 : m = 1
    · subst hm1
      obtain ⟨h1_sq, h1_bi⟩ := hone hc1 hL1 hradN hc4N
      simp only [Nat.cast_one, one_pow, mul_one]
      refine ⟨h1_sq.trans (mul_le_mul_of_nonneg_right
          (by dsimp only [C_core]; linarith only [hCtwo]) (by positivity)),
        fun {l} hl => (h1_bi hl).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by dsimp only [C_core]; linarith only [hCtwo])
            (Real.sqrt_nonneg _)) (by positivity))⟩
    · have hm2 : 2 ≤ m := by omega
      obtain ⟨h2_sq, h2_bi⟩ := htwo hm2 hc1 hL1 hradN
      refine ⟨h2_sq.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by dsimp only [C_core]; linarith only [hCone])
            (sq_nonneg _)) (by positivity)),
        fun {l} hl => (h2_bi hl).trans ?_⟩
      have hr : c / Real.log N ≤ c / Real.log N + c ^ 3 / N :=
        le_add_of_nonneg_right (by positivity)
      exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by dsimp only [C_core]; linarith only [hCone])
              (Nat.cast_nonneg m)) (Real.sqrt_nonneg _)) (by positivity))
  -- Split `normalizedFullNearGammaDownwardVector = normalizedNearGammaDownwardVector - normalizedExteriorDownwardVector`.
  let u_ext := (Real.sqrt (m.totient : ℝ))⁻¹ • normalizedExteriorDownwardVector φ c N m
  let u_int := (Real.sqrt (m.totient : ℝ))⁻¹ • normalizedNearGammaDownwardVector φ c N m +
    nearCenterVector φ c N m
  have hvec_eq : (Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m +
      nearCenterVector φ c N m = -u_ext + u_int := by
    dsimp only [u_ext, u_int]
    rw [normalizedFullNearGammaDownwardVector_eq_sub hφ hsupp hc0 N m, smul_sub]
    abel
  have hint_coord : ∀ idx : PrimeHorizonIndex N,
      u_int idx =
        (nearArchRemRow φ c N m idx.1 + nearShellLogRow φ c N m idx.1 +
          nearShellJetRow φ c N m idx.1 + coreNearRow φ c N m idx.1) /
          Real.sqrt (Real.log N) := by
    intro idx
    change (Real.sqrt (m.totient : ℝ))⁻¹ * (nearGammaDownwardRow φ c N m idx.1 / Real.sqrt (Real.log N)) +
      (∑ j ∈ nearRowIndices c N idx.1,
        completeWeilPoleShift φ c / N * archimedeanCenterKernel idx.1 j *
          normalizedRamanujanMode m j / Real.sqrt j) / Real.sqrt (Real.log N) = _
    rw [← mul_div_assoc, ← add_div, nearGammaDownward_add_nearCenter_row_eq hm hc0 hN0 idx.1]
  rw [hvec_eq]
  constructor
  · -- Part 1: `L^2` squared norm bound.
    have hu_int_sq : ‖u_int‖ ^ 2 ≤ 2 * (C_nc + C_core) * (m : ℝ) ^ 2 * (c ^ 2 / Real.log N) := by
      have hnorm_eq : ‖u_int‖ ^ 2 =
          (∑ n ∈ Icc 1 N, (nearArchRemRow φ c N m n + nearShellLogRow φ c N m n +
            nearShellJetRow φ c N m n + coreNearRow φ c N m n) ^ 2) / Real.log N := by
        rw [EuclideanSpace.norm_sq_eq, ← sum_coe_sort (Icc 1 N), sum_div]
        refine sum_congr rfl fun idx _ => ?_
        rw [Real.norm_eq_abs, sq_abs, hint_coord idx, div_pow, Real.sq_sqrt hL0.le]
      rw [hnorm_eq]
      have hpt2 : ∀ n ∈ Icc 1 N,
          (nearArchRemRow φ c N m n + nearShellLogRow φ c N m n +
            nearShellJetRow φ c N m n + coreNearRow φ c N m n) ^ 2 ≤
          2 * (nearArchRemRow φ c N m n + nearShellLogRow φ c N m n +
              nearShellJetRow φ c N m n) ^ 2 +
            2 * coreNearRow φ c N m n ^ 2 := fun n _ => by
        set A := nearArchRemRow φ c N m n + nearShellLogRow φ c N m n + nearShellJetRow φ c N m n
        set B := coreNearRow φ c N m n
        nlinarith only [sq_nonneg (A - B)]
      calc
        _ ≤ (2 * (∑ n ∈ Icc 1 N, (nearArchRemRow φ c N m n + nearShellLogRow φ c N m n +
                nearShellJetRow φ c N m n) ^ 2) +
              2 * ∑ n ∈ Icc 1 N, coreNearRow φ c N m n ^ 2) / Real.log N := by
          refine div_le_div_of_nonneg_right ?_ hL0.le
          have hs := sum_le_sum hpt2
          rwa [sum_add_distrib, ← mul_sum, ← mul_sum] at hs
        _ = 2 * ((∑ n ∈ Icc 1 N, (nearArchRemRow φ c N m n + nearShellLogRow φ c N m n +
                nearShellJetRow φ c N m n) ^ 2) / Real.log N) +
              2 * ((∑ n ∈ Icc 1 N, coreNearRow φ c N m n ^ 2) / Real.log N) := by ring
        _ ≤ 2 * (C_nc * (m : ℝ) ^ 2 * (c ^ 2 / Real.log N)) +
              2 * (C_core * (m : ℝ) ^ 2 * (c ^ 2 / Real.log N)) :=
          add_le_add (mul_le_mul_of_nonneg_left hnc_sq zero_le_two)
            (mul_le_mul_of_nonneg_left hcore.1 zero_le_two)
        _ = 2 * (C_nc + C_core) * (m : ℝ) ^ 2 * (c ^ 2 / Real.log N) := by ring
    have hnorm_add : ‖-u_ext + u_int‖ ^ 2 ≤ 2 * ‖u_ext‖ ^ 2 + 2 * ‖u_int‖ ^ 2 := by
      have htri := norm_add_le (-u_ext) u_int
      rw [norm_neg] at htri
      have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
      nlinarith only [hsq, sq_nonneg (‖u_ext‖ - ‖u_int‖)]
    have hext_sq' : ‖u_ext‖ ^ 2 ≤ C_ext * (m : ℝ) ^ 2 * (c ^ 3 * Real.log N / N) := by
      have hm_le_sq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith only [hm1R]
      exact hext_sq.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm_le_sq hCext.le) (by positivity))
    let rate_sq := c ^ 2 / Real.log N + c ^ 3 * Real.log N / N
    have hr1 : c ^ 2 / Real.log N ≤ rate_sq := le_add_of_nonneg_right (by positivity)
    have hr2 : c ^ 3 * Real.log N / N ≤ rate_sq := le_add_of_nonneg_left (by positivity)
    have hb1 : 2 * ‖u_ext‖ ^ 2 ≤ 2 * C_ext * (m : ℝ) ^ 2 * rate_sq := by
      calc
        2 * ‖u_ext‖ ^ 2 ≤ 2 * (C_ext * (m : ℝ) ^ 2 * (c ^ 3 * Real.log N / N)) :=
          mul_le_mul_of_nonneg_left hext_sq' zero_le_two
        _ ≤ 2 * (C_ext * (m : ℝ) ^ 2 * rate_sq) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr2 (by positivity)) zero_le_two
        _ = 2 * C_ext * (m : ℝ) ^ 2 * rate_sq := by ring
    have hb2 : 2 * ‖u_int‖ ^ 2 ≤ 4 * (C_nc + C_core) * (m : ℝ) ^ 2 * rate_sq := by
      calc
        2 * ‖u_int‖ ^ 2 ≤ 2 * (2 * (C_nc + C_core) * (m : ℝ) ^ 2 * (c ^ 2 / Real.log N)) :=
          mul_le_mul_of_nonneg_left hu_int_sq zero_le_two
        _ ≤ 2 * (2 * (C_nc + C_core) * (m : ℝ) ^ 2 * rate_sq) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hr1 (by dsimp only [C_core]; positivity)) zero_le_two
        _ = 4 * (C_nc + C_core) * (m : ℝ) ^ 2 * rate_sq := by ring
    calc
      ‖-u_ext + u_int‖ ^ 2 ≤ 2 * C_ext * (m : ℝ) ^ 2 * rate_sq +
          4 * (C_nc + C_core) * (m : ℝ) ^ 2 * rate_sq :=
        hnorm_add.trans (add_le_add hb1 hb2)
      _ = (2 * C_ext + 4 * (C_nc + C_core)) * (m : ℝ) ^ 2 * rate_sq := by ring
      _ ≤ C_ngc * (m : ℝ) ^ 2 * rate_sq :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by dsimp only [C_ngc]; linarith only [hCext]) (sq_nonneg _))
          (by dsimp only [rate_sq]; positivity)
  · -- Part 2: Bilinear pairing bound against `normalizedRamanujanHorizonVector l N`.
    intro l hl
    have hu_int_bi : |⟪u_int, normalizedRamanujanHorizonVector l N⟫| ≤
        (C_nc + C_core) * (m : ℝ) * Real.sqrt l * (c / Real.log N + c ^ 3 / N) := by
      have hinner_eq : ⟪u_int, normalizedRamanujanHorizonVector l N⟫ =
          (Real.sqrt (Real.log N))⁻¹ *
            (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              (nearArchRemRow φ c N m n + nearShellLogRow φ c N m n +
                nearShellJetRow φ c N m n)) +
          (Real.sqrt (Real.log N))⁻¹ *
            (∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              coreNearRow φ c N m n) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        change (∑ idx : PrimeHorizonIndex N,
          normalizedRamanujanHorizonVector l N idx * u_int idx) = _
        have hsum : (∑ idx : PrimeHorizonIndex N,
            normalizedRamanujanHorizonVector l N idx * u_int idx) =
            ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              ((nearArchRemRow φ c N m n + nearShellLogRow φ c N m n +
                nearShellJetRow φ c N m n + coreNearRow φ c N m n) / Real.sqrt (Real.log N)) := by
          rw [← sum_coe_sort (Icc 1 N)]
          refine sum_congr rfl fun idx _ => ?_
          rw [hint_coord idx, primeHorizonExtension_coe]
        rw [hsum]
        have hpt : ∀ n ∈ Icc 1 N,
            primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
              ((nearArchRemRow φ c N m n + nearShellLogRow φ c N m n +
                nearShellJetRow φ c N m n + coreNearRow φ c N m n) / Real.sqrt (Real.log N)) =
            (Real.sqrt (Real.log N))⁻¹ *
              (primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
                (nearArchRemRow φ c N m n + nearShellLogRow φ c N m n +
                  nearShellJetRow φ c N m n)) +
            (Real.sqrt (Real.log N))⁻¹ *
              (primeHorizonExtension (normalizedRamanujanHorizonVector l N) n *
                coreNearRow φ c N m n) := fun _ _ => by ring
        rw [sum_congr rfl hpt, sum_add_distrib, ← mul_sum, ← mul_sum]
      rw [hinner_eq]
      have h1 : C_nc * (m : ℝ) * Real.sqrt l * (c / Real.log N) ≤
          C_nc * (m : ℝ) * Real.sqrt l * (c / Real.log N + c ^ 3 / N) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
      exact ((abs_add_le _ _).trans (add_le_add ((hnc_bi hl).trans h1) (hcore.2 hl))).trans_eq
        (by ring)
    have hext_bi' : |⟪u_ext, normalizedRamanujanHorizonVector l N⟫| ≤
        C_ext * (m : ℝ) * Real.sqrt l * (c / Real.log N + c ^ 3 / N) := by
      have hsm_le_m : Real.sqrt (m : ℝ) ≤ m := by
        calc
          Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith only [hm1R])
          _ = m := Real.sqrt_sq (Nat.cast_nonneg m)
      have hml : Real.sqrt ((m : ℝ) * l) ≤ (m : ℝ) * Real.sqrt l := by
        rw [Real.sqrt_mul (Nat.cast_nonneg m)]
        exact mul_le_mul_of_nonneg_right hsm_le_m (Real.sqrt_nonneg _)
      have hc23 : c ^ 2 / N ≤ c / Real.log N + c ^ 3 / N :=
        (div_le_div_of_nonneg_right (pow_le_pow_right₀ hc1 (by norm_num : 2 ≤ 3)) hN0.le).trans
          (le_add_of_nonneg_left (by positivity))
      exact (hext_bi hl).trans ((mul_le_mul (mul_le_mul_of_nonneg_left hml hCext.le) hc23
        (by positivity) (by positivity)).trans_eq (by ring))
    rw [inner_add_left, inner_neg_left]
    have htri : |-⟪u_ext, normalizedRamanujanHorizonVector l N⟫ +
        ⟪u_int, normalizedRamanujanHorizonVector l N⟫| ≤
        |⟪u_ext, normalizedRamanujanHorizonVector l N⟫| +
          |⟪u_int, normalizedRamanujanHorizonVector l N⟫| := by
      simpa only [abs_neg] using abs_add_le (-⟪u_ext, normalizedRamanujanHorizonVector l N⟫)
        ⟪u_int, normalizedRamanujanHorizonVector l N⟫
    calc
      _ ≤ (C_ext + C_nc + C_core) * (m : ℝ) * Real.sqrt l * (c / Real.log N + c ^ 3 / N) :=
        (htri.trans (add_le_add hext_bi' hu_int_bi)).trans_eq (by ring)
      _ ≤ C_ngc * (m : ℝ) * Real.sqrt l * (c / Real.log N + c ^ 3 / N) := by
        have h0 : 0 ≤ C_ext + C_nc + C_core := by dsimp only [C_core]; positivity
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by dsimp only [C_ngc]; linarith only [h0])
              (Nat.cast_nonneg m)) (Real.sqrt_nonneg _)) (by positivity)

/-! ## Section 5: Assembled Logarithm-Free Complete-Weil Residuals and Critical-Multiple Budgets -/

private lemma abs_inner_seven_signed_le {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u₁ u₂ u₃ u₄ u₅ u₆₇ u₈ v : E) :
    |⟪-u₁ + u₂ + u₃ - u₄ + u₅ + u₆₇ - u₈, v⟫| ≤
      |⟪u₁, v⟫| + |⟪u₂, v⟫| + |⟪u₃, v⟫| + |⟪u₄, v⟫| +
        |⟪u₅, v⟫| + |⟪u₆₇, v⟫| + |⟪u₈, v⟫| := by
  simp only [inner_add_left, inner_sub_left, inner_neg_left]
  have h1 := abs_sub (-⟪u₁, v⟫ + ⟪u₂, v⟫ + ⟪u₃, v⟫ - ⟪u₄, v⟫ + ⟪u₅, v⟫ + ⟪u₆₇, v⟫) ⟪u₈, v⟫
  have h2 := abs_add_le (-⟪u₁, v⟫ + ⟪u₂, v⟫ + ⟪u₃, v⟫ - ⟪u₄, v⟫ + ⟪u₅, v⟫) ⟪u₆₇, v⟫
  have h3 := abs_add_le (-⟪u₁, v⟫ + ⟪u₂, v⟫ + ⟪u₃, v⟫ - ⟪u₄, v⟫) ⟪u₅, v⟫
  have h4 := abs_sub (-⟪u₁, v⟫ + ⟪u₂, v⟫ + ⟪u₃, v⟫) ⟪u₄, v⟫
  have h5 := abs_add_le (-⟪u₁, v⟫ + ⟪u₂, v⟫) ⟪u₃, v⟫
  have h6 := abs_add_le (-⟪u₁, v⟫) ⟪u₂, v⟫
  rw [abs_neg] at h6
  linarith only [h1, h2, h3, h4, h5, h6]

/-- **Logarithm-free complete-Weil bilinear conductor residual bound.**
Across all `m, l ≥ 1` with `max(2, m, l)^2 ≤ N` and `18 (1 + log max(2, m, l)) ≤ log N`, pairing
the complete Weil residual of mode `m` against mode `l` is bounded by
`O(m^2 * l^2 * c / log N + (m * l)^5 * c^5 * log N / N)` with zero `log c` and zero Siegel–Walfisz
input. -/
theorem exists_completeWeil_bilinear_conductor_residual_log_free {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K_bi : ℝ, 0 < K_bi ∧
      ∀ {m l N : ℕ} {c : ℝ},
        0 < m → 0 < l →
        max 2 (max m l) * max 2 (max m l) ≤ N →
        18 * (1 + Real.log (max 2 (max m l) : ℕ)) ≤ Real.log N →
        1 ≤ c → 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N → c ^ 4 ≤ N →
        |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N,
          normalizedRamanujanHorizonVector l N⟫| ≤
          K_bi * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) +
            ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N)) := by
  obtain ⟨Cp, hCp, hp⟩ := exists_primeResidual_bilinear_log_free
  obtain ⟨Cs, hCs, hs⟩ := exists_selfError_quad_bound hφ hsupp hM
  obtain ⟨Cx, hCx, hx⟩ := exists_separatedCrossError_bounds hφ hsupp hM
  obtain ⟨Cq, hCq, hq⟩ := exists_poleError_quadratic_conductor_bound hφ hsupp hM
  obtain ⟨Cngc, hCngc, hngc⟩ := exists_nearGammaDownward_add_nearCenter_log_free hφ hsupp hM
  obtain ⟨Cub, hCub, hub⟩ := exists_upward_bilinear_log_free hφ hsupp hM
  let S₁ := |completeWeilPoleShift φ 1|
  let K_bi := 2 * Cp + 2 * Real.sqrt Cs + 5 * S₁ + Cx + 2 * Real.sqrt (Cq + 1) + Cngc + Cub + 1
  refine ⟨K_bi, by dsimp only [K_bi, S₁]; positivity, ?_⟩
  intro m l N c hm hl hR2N hlog18 hc1 hradN hc4N
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N :=
    (by norm_num : 1 ≤ 2 * 2).trans
      ((Nat.mul_le_mul (le_max_left 2 (max m l)) (le_max_left 2 (max m l))).trans hR2N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL1 : 1 ≤ Real.log (N : ℝ) := by
    have := Real.log_natCast_nonneg (max 2 (max m l))
    linarith only [hlog18, this]
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hl1R : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hml1 : 1 ≤ (m : ℝ) * l := one_le_mul_of_one_le_of_one_le hm1R hl1R
  have hc2N : c ^ 2 ≤ N := (pow_le_pow_right₀ hc1 (by norm_num : 2 ≤ 4)).trans hc4N
  have hcN : c ≤ N := (by nlinarith only [hc1] : c ≤ c ^ 2).trans hc2N
  have hvl_norm : ‖normalizedRamanujanHorizonVector l N‖ ≤ 2 * Real.sqrt l :=
    norm_normalizedRamanujanHorizonVector_le_two_sqrt hl hL1
  have hsm_le : Real.sqrt (m : ℝ) ≤ m := by
    calc
      Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith only [hm1R])
      _ = m := Real.sqrt_sq (Nat.cast_nonneg m)
  have hsl_le : Real.sqrt (l : ℝ) ≤ l := by
    calc
      Real.sqrt (l : ℝ) ≤ Real.sqrt ((l : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith only [hl1R])
      _ = l := Real.sqrt_sq (Nat.cast_nonneg l)
  have hm_sq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith only [hm1R]
  have hl_sq : (l : ℝ) ≤ (l : ℝ) ^ 2 := by nlinarith only [hl1R]
  have hml_rad : Real.sqrt ((m : ℝ) * l) ≤ (m : ℝ) * Real.sqrt l := by
    rw [Real.sqrt_mul (Nat.cast_nonneg m)]
    exact mul_le_mul_of_nonneg_right hsm_le (Real.sqrt_nonneg _)
  have hml_22 : (m : ℝ) * Real.sqrt l ≤ (m : ℝ) ^ 2 * (l : ℝ) ^ 2 :=
    (mul_le_mul hm_sq (hsl_le.trans hl_sq) (Real.sqrt_nonneg _) (sq_nonneg _))
  have hml_5 : Real.sqrt ((m : ℝ) * l) ≤ ((m : ℝ) * l) ^ 5 :=
    (hml_rad.trans (mul_le_mul_of_nonneg_left hsl_le (Nat.cast_nonneg m))).trans
      (le_self_pow₀ hml1 (by decide))
  let R := (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) + ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N)
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hr1 : (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) ≤ R :=
    le_add_of_nonneg_right (by positivity)
  have hr2 : ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) ≤ R :=
    le_add_of_nonneg_left (by positivity)
  let v_m := normalizedRamanujanHorizonVector m N
  let v_l := normalizedRamanujanHorizonVector l N
  -- 1. Prime residual
  have hb1 : |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) v_m -
      (Real.log N - ramanujanAdjunctionEnergy m) • v_m, v_l⟫| ≤ 2 * Cp * R := by
    have h1m := one_add_log_le_two_sqrt_pos (by exact_mod_cast hm : (0 : ℝ) < m)
    have hnum : Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) ≤ 2 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * c := by
      have h1 : Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) ≤ 2 * ((m : ℝ) * Real.sqrt l) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg m)]
        calc
          (Real.sqrt m * Real.sqrt l) * (1 + Real.log m)
              ≤ (Real.sqrt m * Real.sqrt l) * (2 * Real.sqrt m) :=
            mul_le_mul_of_nonneg_left h1m (by positivity)
          _ = 2 * ((Real.sqrt m * Real.sqrt m) * Real.sqrt l) := by ring
          _ = 2 * ((m : ℝ) * Real.sqrt l) := by rw [Real.mul_self_sqrt (Nat.cast_nonneg m)]
      have h2 : 2 * ((m : ℝ) * Real.sqrt l) ≤ 2 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 := by
        linarith only [hml_22]
      exact (h1.trans h2).trans (le_mul_of_one_le_right (by positivity) hc1)
    calc
      _ ≤ Cp * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N := hp m l N hm hl
      _ ≤ Cp * (2 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * c) / Real.log N := by
        rw [mul_assoc Cp]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hCp.le) hL0.le
      _ = 2 * Cp * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N)) := by ring
      _ ≤ 2 * Cp * R := mul_le_mul_of_nonneg_left hr1 (by positivity)
  -- 2. Self-error
  have hb2 : |⟪completeWeilSelfError φ c N • v_m, v_l⟫| ≤ 2 * Real.sqrt Cs * R := by
    have hsq := hs m hm N hN1 hL1 c hc0 hcN
    have hn : ‖completeWeilSelfError φ c N • v_m‖ ≤ Real.sqrt Cs * Real.sqrt m * c / N := by
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_div (by positivity),
        Real.sqrt_mul (by positivity), Real.sqrt_mul hCs.le, Real.sqrt_sq hc0.le,
        Real.sqrt_sq hN0.le] at h
    calc
      _ ≤ ‖completeWeilSelfError φ c N • v_m‖ * ‖v_l‖ := abs_real_inner_le_norm _ _
      _ ≤ (Real.sqrt Cs * Real.sqrt m * c / N) * (2 * Real.sqrt l) :=
        mul_le_mul hn hvl_norm (norm_nonneg _) (by positivity)
      _ = 2 * Real.sqrt Cs * Real.sqrt ((m : ℝ) * l) * (c / N) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg m)]; ring
      _ ≤ 2 * Real.sqrt Cs * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by
        have hc5 : c ≤ c ^ 5 := by
          have := pow_le_pow_right₀ hc1 (by norm_num : 1 ≤ 5)
          simpa only [pow_one] using this
        have hc15 : c / N ≤ c ^ 5 * Real.log N / N :=
          div_le_div_of_nonneg_right
            (hc5.trans (le_mul_of_one_le_right (by positivity) hL1)) hN0.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left hml_5 (by positivity)) hc15
          (by positivity) (by positivity)
      _ ≤ 2 * Real.sqrt Cs * R :=
        (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hr2 (by positivity))
  -- 3. Full center residual
  have hb3 : |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) v_m -
      (if m = 1 then completeWeilPoleShift φ c else 0) • v_m, v_l⟫| ≤ 5 * S₁ * R := by
    have hcen := fullWeilCenter_bilinear_log_free (completeWeilPoleShift φ c) hm hl hN1 hL0
    have hshift : |completeWeilPoleShift φ c| = S₁ * c := by
      have h1 : completeWeilPoleShift φ c = completeWeilPoleShift φ 1 * c := by
        unfold completeWeilPoleShift; ring
      rw [h1, abs_mul, abs_of_pos hc0]
    calc
      _ ≤ 5 * (S₁ * c) * ((m : ℝ) * Real.sqrt l) / Real.log N := by
        rw [hshift] at hcen; exact hcen.trans_eq (by ring)
      _ ≤ 5 * (S₁ * c) * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2) / Real.log N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hml_22 (by dsimp only [S₁]; positivity)) hL0.le
      _ = 5 * S₁ * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N)) := by ring
      _ ≤ 5 * S₁ * R := mul_le_mul_of_nonneg_left hr1 (by dsimp only [S₁]; positivity)
  -- 4. Separated cross-error
  have hb4 : |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) v_m, v_l⟫| ≤ Cx * R := by
    have h4 := (hx m hm c hc1 N hN1 hc2N).2 l hl
    calc
      _ ≤ Cx * (Real.sqrt ((m : ℝ) * l)) * c / Real.log N := h4
      _ ≤ Cx * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2) * c / Real.log N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hml_rad.trans hml_22) hCx.le) hc0.le) hL0.le
      _ = Cx * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N)) := by ring
      _ ≤ Cx * R := mul_le_mul_of_nonneg_left hr1 hCx.le
  -- 5. Full pole-error
  have hb5 : |⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) v_m, v_l⟫| ≤
      2 * Real.sqrt (Cq + 1) * R := by
    have hsq := (hq m hm c hc1 N hN1 hL1 hcN).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (show Cq ≤ Cq + 1 by linarith) (Nat.cast_nonneg m))
          (by positivity)) (sq_nonneg _))
    have hn : ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) v_m‖ ≤
        Real.sqrt (Cq + 1) * Real.sqrt m * c ^ 5 * (Real.log N / N) := by
      have h := Real.sqrt_le_sqrt hsq
      have hc5 : c ^ 10 = (c ^ 5) ^ 2 := by ring
      rwa [Real.sqrt_sq (norm_nonneg _), hc5, Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at h
    calc
      _ ≤ ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) v_m‖ * ‖v_l‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (Real.sqrt (Cq + 1) * Real.sqrt m * c ^ 5 * (Real.log N / N)) * (2 * Real.sqrt l) :=
        mul_le_mul hn hvl_norm (norm_nonneg _) (by positivity)
      _ = 2 * Real.sqrt (Cq + 1) * Real.sqrt ((m : ℝ) * l) * (c ^ 5 * Real.log N / N) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg m)]; ring
      _ ≤ 2 * Real.sqrt (Cq + 1) * (((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N)) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hml_5 (by positivity))
          (by positivity)
      _ ≤ 2 * Real.sqrt (Cq + 1) * R := mul_le_mul_of_nonneg_left hr2 (by positivity)
  -- 6+7. Combined near-Gamma downward + near-center
  have hb67 : |⟪(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m +
      nearCenterVector φ c N m, v_l⟫| ≤ Cngc * R := by
    have h67 := (hngc hm hc1 hL1 hradN hc4N).2 hl
    have hr67 : (m : ℝ) * Real.sqrt l * (c / Real.log N + c ^ 3 / N) ≤ R := by
      rw [mul_add]
      refine add_le_add (mul_le_mul_of_nonneg_right hml_22 (by positivity)) ?_
      have hc35 : c ^ 3 / N ≤ c ^ 5 * Real.log N / N :=
        div_le_div_of_nonneg_right
          ((pow_le_pow_right₀ hc1 (by norm_num : 3 ≤ 5)).trans
            (le_mul_of_one_le_right (by positivity) hL1)) hN0.le
      have hml_15 : (m : ℝ) * Real.sqrt l ≤ ((m : ℝ) * l) ^ 5 :=
        (mul_le_mul_of_nonneg_left hsl_le (Nat.cast_nonneg m)).trans
          (le_self_pow₀ hml1 (by decide))
      exact mul_le_mul hml_15 hc35 (by positivity) (by positivity)
    have h67' : |⟪(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m +
        nearCenterVector φ c N m, v_l⟫| ≤
        Cngc * ((m : ℝ) * Real.sqrt l * (c / Real.log N + c ^ 3 / N)) :=
      h67.trans_eq (by ring)
    exact h67'.trans (mul_le_mul_of_nonneg_left hr67 hCngc.le)
  -- 8. Upward prime defect
  have hb8 : |⟪upwardPrimeVector φ c N v_m - shellCorrection φ c m • v_m, v_l⟫| ≤ Cub * R :=
    hub hm hl hR2N hlog18 hc1 hradN
  rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM hc0 hN1 hm]
  have h7 := abs_inner_seven_signed_le
    (Matrix.toEuclideanLin (fullPrimeMatrix N) v_m -
      (Real.log N - ramanujanAdjunctionEnergy m) • v_m)
    (completeWeilSelfError φ c N • v_m)
    (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) v_m -
      (if m = 1 then completeWeilPoleShift φ c else 0) • v_m)
    (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) v_m)
    (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) v_m)
    ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m +
      nearCenterVector φ c N m)
    (upwardPrimeVector φ c N v_m - shellCorrection φ c m • v_m)
    v_l
  have hsum := h7.trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add hb1 hb2) hb3) hb4) hb5) hb67) hb8)
  calc
    _ ≤ (2 * Cp + 2 * Real.sqrt Cs + 5 * S₁ + Cx + 2 * Real.sqrt (Cq + 1) + Cngc + Cub) * R :=
      hsum.trans_eq (by ring)
    _ ≤ K_bi * R := mul_le_mul_of_nonneg_right (by dsimp only [K_bi]; linarith only) hR0

/-- **Logarithm-free dual seventh-power top-collar residual bound.**
On any top collar `Ioc M N` with `2 * linearPrimeStrip c ≤ M`, the dual seventh-power collar mass
of the complete Weil residual is bounded by `O(m^2 * (c^2 / log N + c^3 log N / N + c^10 (log N / N)^2))`
with zero `log c` and zero Siegel–Walfisz input. -/
theorem exists_completeWeil_dualSeventh_conductor_residual_log_free {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K_d7 : ℝ, 0 < K_d7 ∧
      ∀ {N M m : ℕ} {c : ℝ},
        0 < m → 1 ≤ c → 1 ≤ Real.log (N : ℝ) →
        4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ N →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N → c ^ 4 ≤ N →
        2 * linearPrimeStrip c ≤ M →
        topCollarDualSeventhMass M N
          (Matrix.toEuclideanLin (completeWeilMatrix φ c N)
              (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N) ≤
          K_d7 * (m : ℝ) ^ 2 *
            (c ^ 2 / Real.log N + c ^ 3 * Real.log N / N + c ^ 10 * (Real.log N / N) ^ 2) := by
  obtain ⟨Cp, hCp, hp⟩ := exists_primeResidual_quad_bound
  obtain ⟨Cs, hCs, hs⟩ := exists_selfError_quad_bound hφ hsupp hM
  obtain ⟨Cx, hCx, hx⟩ := exists_separatedCrossError_bounds hφ hsupp hM
  obtain ⟨Cq, hCq, hq⟩ := exists_poleError_quadratic_conductor_bound hφ hsupp hM
  obtain ⟨Cngc, hCngc, hngc⟩ := exists_nearGammaDownward_add_nearCenter_log_free hφ hsupp hM
  obtain ⟨Cu7, hCu7, hu7⟩ := exists_upward_dual_seventh_log_free hφ hsupp hM
  let S₁ := |completeWeilPoleShift φ 1|
  let K_d7 := 16 * (4 * Cp + Cs + 87 * S₁ ^ 2 + Cx + Cq + Cngc + Cu7 + 1)
  refine ⟨K_d7, by dsimp only [K_d7, S₁]; positivity, ?_⟩
  intro N M m c hm hc1 hL1 hlarge hradN hc4N h2BM
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm_sq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith only [hm1R]
  have hc2N : c ^ 2 ≤ N := (pow_le_pow_right₀ hc1 (by norm_num : 2 ≤ 4)).trans hc4N
  have hcN : c ≤ N := (by nlinarith only [hc1] : c ≤ c ^ 2).trans hc2N
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := hc1.trans hcN
    exact_mod_cast this
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  let R := c ^ 2 / Real.log N + c ^ 3 * Real.log N / N + c ^ 10 * (Real.log N / N) ^ 2
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hr_c2 : c ^ 2 / Real.log N ≤ R := by
    dsimp only [R]
    have : 0 ≤ c ^ 3 * Real.log N / N + c ^ 10 * (Real.log N / N) ^ 2 := by positivity
    linarith only [this]
  have hr_sub : c ^ 10 * (Real.log N / N) ^ 2 ≤ R := le_add_of_nonneg_left (by positivity)
  have hr_ngc : c ^ 2 / Real.log N + c ^ 3 * Real.log N / N ≤ R :=
    le_add_of_nonneg_right (by positivity)
  have hr_u7 : c ^ 2 / Real.log N + c ^ 10 * (Real.log N / N) ^ 2 ≤ R := by
    dsimp only [R]
    have : 0 ≤ c ^ 3 * Real.log N / N := by positivity
    linarith only [this]
  let v_m := normalizedRamanujanHorizonVector m N
  let u₁ := Matrix.toEuclideanLin (fullPrimeMatrix N) v_m -
    (Real.log N - ramanujanAdjunctionEnergy m) • v_m
  let u₂ := completeWeilSelfError φ c N • v_m
  let u₃ := Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) v_m -
    (if m = 1 then completeWeilPoleShift φ c else 0) • v_m
  let u₄ := Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) v_m
  let u₅ := Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) v_m
  let u₆₇ := (Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m +
    nearCenterVector φ c N m
  let u₈ := upwardPrimeVector φ c N v_m - shellCorrection φ c m • v_m
  -- Individual dual-seventh bounds on each channel.
  have hd1 : topCollarDualSeventhMass M N (-u₁) ≤ 4 * Cp * (m : ℝ) ^ 2 * R := by
    rw [topCollarDualSeventhMass_neg]
    have hlog_sq := one_add_log_sq_le_four_mul hm1R
    have h1 : Cp * ((m : ℝ) * (1 + Real.log m) ^ 2) / Real.log N ≤
        4 * Cp * (m : ℝ) ^ 2 * (c ^ 2 / Real.log N) := by
      have hm_c : (m : ℝ) * (1 + Real.log m) ^ 2 ≤ 4 * (m : ℝ) ^ 2 * c ^ 2 := by
        calc
          (m : ℝ) * (1 + Real.log m) ^ 2 ≤ (m : ℝ) * (4 * (m : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog_sq (Nat.cast_nonneg m)
          _ = 4 * (m : ℝ) ^ 2 := by ring
          _ ≤ 4 * (m : ℝ) ^ 2 * c ^ 2 :=
            le_mul_of_one_le_right (by positivity) (one_le_pow₀ hc1)
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm_c hCp.le) hL0.le).trans_eq
        (by ring)
    exact (topCollarDualSeventhMass_le_norm_sq M N u₁).trans
      ((hp m hm N).trans (h1.trans (mul_le_mul_of_nonneg_left hr_c2 (by positivity))))
  have hd2 : topCollarDualSeventhMass M N u₂ ≤ Cs * (m : ℝ) ^ 2 * R := by
    have hc2_10 : c ^ 2 / (N : ℝ) ^ 2 ≤ c ^ 10 * (Real.log N / N) ^ 2 := by
      rw [div_pow, mul_div_assoc']
      refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
      exact (pow_le_pow_right₀ hc1 (by norm_num : 2 ≤ 10)).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1))
    calc
      _ ≤ Cs * (m : ℝ) * c ^ 2 / (N : ℝ) ^ 2 :=
        (topCollarDualSeventhMass_le_norm_sq M N u₂).trans (hs m hm N hN1 hL1 c hc0 hcN)
      _ = Cs * (m : ℝ) * (c ^ 2 / (N : ℝ) ^ 2) := by ring
      _ ≤ Cs * (m : ℝ) ^ 2 * (c ^ 10 * (Real.log N / N) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hm_sq hCs.le) hc2_10 (by positivity) (by positivity)
      _ ≤ Cs * (m : ℝ) ^ 2 * R := mul_le_mul_of_nonneg_left hr_sub (by positivity)
  have hd3 : topCollarDualSeventhMass M N u₃ ≤ 87 * S₁ ^ 2 * (m : ℝ) ^ 2 * R := by
    have hcen := fullWeilCenter_residual_uniform_conductor_bound hm (completeWeilPoleShift φ c) N
    have hshift : (completeWeilPoleShift φ c) ^ 2 = S₁ ^ 2 * c ^ 2 := by
      have h1 : completeWeilPoleShift φ c = completeWeilPoleShift φ 1 * c := by
        unfold completeWeilPoleShift; ring
      rw [h1, mul_pow, ← sq_abs (completeWeilPoleShift φ 1)]
    calc
      _ ≤ 87 * (S₁ ^ 2 * c ^ 2) * (m : ℝ) ^ 2 / Real.log N := by
        rw [hshift] at hcen
        exact (topCollarDualSeventhMass_le_norm_sq M N u₃).trans hcen
      _ = 87 * S₁ ^ 2 * (m : ℝ) ^ 2 * (c ^ 2 / Real.log N) := by ring
      _ ≤ 87 * S₁ ^ 2 * (m : ℝ) ^ 2 * R :=
        mul_le_mul_of_nonneg_left hr_c2 (by dsimp only [S₁]; positivity)
  have hd4 : topCollarDualSeventhMass M N (-u₄) ≤ Cx * (m : ℝ) ^ 2 * R := by
    rw [topCollarDualSeventhMass_neg]
    calc
      _ ≤ Cx * (m : ℝ) * c ^ 2 / Real.log N :=
        (topCollarDualSeventhMass_le_norm_sq M N u₄).trans (hx m hm c hc1 N hN1 hc2N).1
      _ = Cx * (m : ℝ) * (c ^ 2 / Real.log N) := by ring
      _ ≤ Cx * (m : ℝ) ^ 2 * (c ^ 2 / Real.log N) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_sq hCx.le) (by positivity)
      _ ≤ Cx * (m : ℝ) ^ 2 * R := mul_le_mul_of_nonneg_left hr_c2 (by positivity)
  have hd5 : topCollarDualSeventhMass M N u₅ ≤ Cq * (m : ℝ) ^ 2 * R := by
    calc
      _ ≤ Cq * (m : ℝ) * (c ^ 10 * (Real.log N / N) ^ 2) := by
        exact (topCollarDualSeventhMass_le_norm_sq M N u₅).trans
          ((hq m hm c hc1 N hN1 hL1 hcN).trans_eq (by ring))
      _ ≤ Cq * (m : ℝ) ^ 2 * (c ^ 10 * (Real.log N / N) ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_sq hCq) (by positivity)
      _ ≤ Cq * (m : ℝ) ^ 2 * R := mul_le_mul_of_nonneg_left hr_sub (by positivity)
  have hd67 : topCollarDualSeventhMass M N u₆₇ ≤ Cngc * (m : ℝ) ^ 2 * R :=
    (topCollarDualSeventhMass_le_norm_sq M N u₆₇).trans
      ((hngc hm hc1 hL1 hradN hc4N).1.trans
        (mul_le_mul_of_nonneg_left hr_ngc (by positivity)))
  have hd8 : topCollarDualSeventhMass M N (-u₈) ≤ Cu7 * (m : ℝ) ^ 2 * R := by
    rw [topCollarDualSeventhMass_neg]
    exact (hu7 hN1 hL1 hm hc1 hlarge h2BM).trans
      ((mul_le_mul (mul_le_mul_of_nonneg_left hm_sq hCu7.le) hr_u7
        (by positivity) (by positivity)))
  have hres_eq : Matrix.toEuclideanLin (completeWeilMatrix φ c N) v_m -
      completedConductorEnergy φ c m • v_m =
      (-u₁) + u₂ + u₃ + (-u₄) + u₅ + u₆₇ + (-u₈) := by
    rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM hc0 hN1 hm]
    dsimp only [u₁, u₂, u₃, u₄, u₅, u₆₇, u₈]
    abel
  rw [hres_eq]
  have h7 := topCollarDualSeventhMass_seven_le M N (-u₁) u₂ u₃ (-u₄) u₅ u₆₇ (-u₈)
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add hd1 hd2) hd3) hd4) hd5) hd67) hd8
  calc
    _ ≤ 16 * ((4 * Cp + Cs + 87 * S₁ ^ 2 + Cx + Cq + Cngc + Cu7) * (m : ℝ) ^ 2 * R) :=
      h7.trans (mul_le_mul_of_nonneg_left (hsum.trans_eq (by ring)) (by norm_num))
    _ ≤ K_d7 * (m : ℝ) ^ 2 * R := by
      dsimp only [K_d7]
      have : 0 ≤ (m : ℝ) ^ 2 * R := by positivity
      nlinarith only [this]

private lemma one_add_log_le_rpow_256 {L : ℝ} (hL1 : 1 ≤ L) :
    1 + Real.log L ≤ 256 * L ^ (1 / 256 : ℝ) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have ht0 : 0 < L ^ (1 / 256 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hlog : Real.log (L ^ (1 / 256 : ℝ)) = (1 / 256 : ℝ) * Real.log L := Real.log_rpow hL0 _
  have h1 := Real.log_le_sub_one_of_pos ht0
  linarith only [hlog, h1]

private lemma completedConductorEnergy_tilted_ge_low {c : ℝ} {m : ℕ}
    (hc0 : 0 < c) (hm : 0 < m) (hmc : (m : ℝ) ≤ c) :
    tiltedSplineSpectralFloorConstant * ((m : ℝ) / c) ^ 7 ≤
      completedConductorEnergy tiltedUnitSpline c m := by
  have hκ : 0 < tiltedSplineSpectralFloorConstant := tiltedSplineSpectralFloorConstant_pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hfloor := tiltedUnitSpline_completedConductorEnergy_ge_conductor_scale hc0 hm
  have hratio : 1 ≤ (m : ℝ) / m.totient := (one_le_div htot).mpr (by exact_mod_cast Nat.totient_le m)
  have hp : ((m : ℝ) / c) ^ 7 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (div_nonneg hm0.le hc0.le)
      ((div_le_one hc0).mpr hmc) 7
  rw [min_eq_right hp] at hfloor
  have h1 : tiltedSplineSpectralFloorConstant ≤
      (2 * tiltedSplineTailConstant / ∫ u, tiltedUnitSpline u ^ 2) * ((m : ℝ) / m.totient) :=
    le_mul_of_one_le_right hκ.le hratio
  exact (mul_le_mul_of_nonneg_right h1 (by positivity)).trans hfloor

private lemma le_rpow_inv_nat_of_pow_le {a L : ℝ} (ha : 0 ≤ a) {k : ℕ} (hk : 0 < k)
    (h : a ^ k ≤ L) : a ≤ L ^ (1 / (k : ℝ)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    a = (a ^ k) ^ (1 / (k : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha, mul_one_div_cancel hk0.ne', Real.rpow_one]
    _ ≤ L ^ (1 / (k : ℝ)) := Real.rpow_le_rpow (pow_nonneg ha k) h (by positivity)

private lemma rate_vb_critical_le {N : ℕ} {c : ℝ}
    (hc1 : 1 ≤ c) (hL1 : 1 ≤ Real.log (N : ℝ))
    (hc_L8 : c ≤ Real.log (N : ℝ) ^ (1 / 8 : ℝ))
    (hL8N : Real.log (N : ℝ) ^ (8 : ℕ) ≤ N) :
    c * (1 + Real.log c) ^ 2 * Real.log N ^ (1 / (128 : ℕ) : ℝ) / Real.log N +
        c ^ 5 * Real.log N / (N : ℝ) ≤
      65537 * Real.log (N : ℝ) ^ (-55 / 64 : ℝ) := by
  let L := Real.log (N : ℝ)
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hc_le_L : c ≤ L :=
    hc_L8.trans ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L))
  have hN0 : (0 : ℝ) < N := (pow_pos hL0 8).trans_le hL8N
  have hlogc_sq : (1 + Real.log c) ^ 2 ≤ 65536 * L ^ (1 / 128 : ℝ) := by
    have h1 : 1 + Real.log c ≤ 256 * L ^ (1 / 256 : ℝ) :=
      (by linarith [Real.log_le_log hc0 hc_le_L] : 1 + Real.log c ≤ 1 + Real.log L).trans
        (one_add_log_le_rpow_256 hL1)
    calc
      (1 + Real.log c) ^ 2 ≤ (256 * L ^ (1 / 256 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by linarith [Real.log_nonneg hc1]) h1 2
      _ = 65536 * L ^ (1 / 128 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 256 : ℝ)) 2, ← Real.rpow_mul hL0.le]
        norm_num
  have ht1 : c * (1 + Real.log c) ^ 2 * L ^ (1 / (128 : ℕ) : ℝ) / L ≤
      65536 * L ^ (-55 / 64 : ℝ) := by
    have hm1 : c * (1 + Real.log c) ^ 2 ≤ L ^ (1 / 8 : ℝ) * (65536 * L ^ (1 / 128 : ℝ)) :=
      mul_le_mul hc_L8 hlogc_sq (sq_nonneg _) (by positivity)
    rw [show ((128 : ℕ) : ℝ) = 128 by norm_num]
    calc
      c * (1 + Real.log c) ^ 2 * L ^ (1 / 128 : ℝ) / L ≤
          L ^ (1 / 8 : ℝ) * (65536 * L ^ (1 / 128 : ℝ)) * L ^ (1 / 128 : ℝ) / L :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hm1 (by positivity)) hL0.le
      _ = 65536 * (L ^ (1 / 8 : ℝ) * L ^ (1 / 128 : ℝ) * L ^ (1 / 128 : ℝ) * L ^ (-1 : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one L]; ring
      _ = 65536 * L ^ (-55 / 64 : ℝ) := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
  have ht2 : c ^ 5 * L / (N : ℝ) ≤ L ^ (-55 / 64 : ℝ) := by
    have hc5 : c ^ 5 * L * L ≤ N := by
      calc
        c ^ 5 * L * L ≤ L ^ 5 * L * L := by
          gcongr
        _ = L ^ 7 := by ring
        _ ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
        _ ≤ N := hL8N
    have hinv : c ^ 5 * L / (N : ℝ) ≤ L ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one, ← one_div, div_le_div_iff₀ hN0 hL0]
      linarith only [hc5]
    exact hinv.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  linarith only [ht1, ht2]

private lemma rate_q_critical_le {N : ℕ} {c : ℝ}
    (hc1 : 1 ≤ c) (hL1 : 1 ≤ Real.log (N : ℝ))
    (hc_L8 : c ≤ Real.log (N : ℝ) ^ (1 / 8 : ℝ))
    (hL8N : Real.log (N : ℝ) ^ (8 : ℕ) ≤ N) :
    c ^ 2 * (1 + Real.log c) ^ 3 * Real.log N ^ (1 / (128 : ℕ) : ℝ) / Real.log N +
        c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 ≤
      16777217 * Real.log (N : ℝ) ^ (-187 / 256 : ℝ) := by
  let L := Real.log (N : ℝ)
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hc_le_L : c ≤ L :=
    hc_L8.trans ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)).trans_eq (Real.rpow_one L))
  have hN1 : (1 : ℝ) ≤ N := (one_le_pow₀ hL1).trans hL8N
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hc2 : c ^ 2 ≤ L ^ (1 / 4 : ℝ) := by
    calc
      c ^ 2 ≤ (L ^ (1 / 8 : ℝ)) ^ 2 := pow_le_pow_left₀ hc0.le hc_L8 2
      _ = L ^ (1 / 4 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have h1c_nn : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hlogc_cu : (1 + Real.log c) ^ 3 ≤ 16777216 * L ^ (3 / 256 : ℝ) := by
    have h1 : 1 + Real.log c ≤ 256 * L ^ (1 / 256 : ℝ) :=
      (by linarith [Real.log_le_log hc0 hc_le_L] : 1 + Real.log c ≤ 1 + Real.log L).trans
        (one_add_log_le_rpow_256 hL1)
    calc
      (1 + Real.log c) ^ 3 ≤ (256 * L ^ (1 / 256 : ℝ)) ^ 3 :=
        pow_le_pow_left₀ h1c_nn h1 3
      _ = 16777216 * L ^ (3 / 256 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 256 : ℝ)) 3, ← Real.rpow_mul hL0.le]
        norm_num
  have ht1 : c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (128 : ℕ) : ℝ) / L ≤
      16777216 * L ^ (-187 / 256 : ℝ) := by
    have hm1 : c ^ 2 * (1 + Real.log c) ^ 3 ≤ L ^ (1 / 4 : ℝ) * (16777216 * L ^ (3 / 256 : ℝ)) :=
      mul_le_mul hc2 hlogc_cu (pow_nonneg h1c_nn 3) (by positivity)
    rw [show ((128 : ℕ) : ℝ) = 128 by norm_num]
    calc
      c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / 128 : ℝ) / L ≤
          L ^ (1 / 4 : ℝ) * (16777216 * L ^ (3 / 256 : ℝ)) * L ^ (1 / 128 : ℝ) / L :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hm1 (by positivity)) hL0.le
      _ = 16777216 * (L ^ (1 / 4 : ℝ) * L ^ (3 / 256 : ℝ) * L ^ (1 / 128 : ℝ) * L ^ (-1 : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one L]; ring
      _ = 16777216 * L ^ (-187 / 256 : ℝ) := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
  have ht2 : c ^ 10 * (L / N) ^ 2 ≤ L ^ (-187 / 256 : ℝ) := by
    have hc8 : c ^ 8 ≤ L := by
      calc
        c ^ 8 ≤ (L ^ (1 / 8 : ℝ)) ^ 8 := pow_le_pow_left₀ hc0.le hc_L8 8
        _ = L := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    have hc10 : c ^ 10 * L ^ 2 * L ≤ (N : ℝ) ^ 2 := by
      calc
        c ^ 10 * L ^ 2 * L = c ^ 8 * c ^ 2 * L ^ 3 := by ring
        _ ≤ L * L ^ 2 * L ^ 3 := by
          have := pow_le_pow_left₀ hc0.le hc_le_L 2
          gcongr
        _ = L ^ 6 := by ring
        _ ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
        _ ≤ N := hL8N
        _ ≤ (N : ℝ) ^ 2 := le_self_pow₀ hN1 (by decide)
    have hinv : c ^ 10 * (L / N) ^ 2 ≤ L ^ (-1 : ℝ) := by
      rw [div_pow, mul_div_assoc', Real.rpow_neg_one, ← one_div,
        div_le_div_iff₀ (sq_pos_of_pos hN0) hL0]
      linarith only [hc10]
    exact hinv.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  linarith only [ht1, ht2]

/-- **Critical-multiple low-conductor coercivity and dual seventh-power collar budget.**
For every `ε > 0`, there exists `0 < K₁ ≤ 1 / 2` such that eventually in `N` and uniformly across
`1 ≤ c ≤ 2 * K₁ * (log N)^{1/8}`, on `Q₁ = ⌊(log N)^{13/32}⌋₊`:
1. `spectralFloorWeilMatrix c N` retains at least `(1 / 4) * ∑_{m=1}^{Q₁} E_m(c) a_m^2` on `V_{Q₁}`;
2. the full inverse-energy residual sum `∑_{m=1}^{Q₁} ‖r_m‖^2 / E_m(c)` is at most `(log N)^{1/4}`;
3. on any top collar `Ioc M N` with `2 * linearPrimeStrip c ≤ M`, the rescaled dual seventh-power
   collar residual `(c^7 / log N) * ∑_{m=1}^{Q₁} topCollarDualSeventhMass M N r_m / E_m(c)` is at
   most `ε`. -/
theorem exists_critical_multiple_low_packet_and_collar_budget {ε : ℝ} (hε : 0 < ε) :
    ∃ K₁ : ℝ, 0 < K₁ ∧ K₁ ≤ 1 / 2 ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ c : ℝ, 1 ≤ c → c ≤ 2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ) →
          (∀ a : ℕ → ℝ,
            (1 / 4 : ℝ) *
                (∑ m ∈ Icc 1 ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊,
                  completedConductorEnergy tiltedUnitSpline c m * a m ^ 2) ≤
              ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
                  (∑ m ∈ Icc 1 ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊,
                    a m • normalizedRamanujanHorizonVector m N),
                ∑ m ∈ Icc 1 ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊,
                  a m • normalizedRamanujanHorizonVector m N⟫) ∧
          (∑ m ∈ Icc 1 ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊,
            ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
                (normalizedRamanujanHorizonVector m N) -
              completedConductorEnergy tiltedUnitSpline c m •
                normalizedRamanujanHorizonVector m N‖ ^ 2 /
              completedConductorEnergy tiltedUnitSpline c m) ≤
            Real.log (N : ℝ) ^ (1 / 4 : ℝ) ∧
          ∀ M : ℕ, 2 * linearPrimeStrip c ≤ M →
            (c ^ 7 / Real.log N) *
              (∑ m ∈ Icc 1 ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊,
                topCollarDualSeventhMass M N
                  (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
                      (normalizedRamanujanHorizonVector m N) -
                    completedConductorEnergy tiltedUnitSpline c m •
                      normalizedRamanujanHorizonVector m N) /
                  completedConductorEnergy tiltedUnitSpline c m) ≤ ε := by
  let κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  obtain ⟨K_bi, hKbi, hbi_lf⟩ := exists_completeWeil_bilinear_conductor_residual_log_free
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  obtain ⟨K_d7, hKd7, hd7_lf⟩ := exists_completeWeil_dualSeventh_conductor_residual_log_free
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  obtain ⟨K_vb, hKvb, hbi_var⟩ := exists_tiltedUnitSpline_bilinear_conductor_residual_variable_rate
  obtain ⟨K_vq, hKvq, hq_var⟩ := exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate
  obtain ⟨K_inv, hKinv, hinv_sum⟩ := exists_tiltedUnitSpline_quadratic_inv_energy_residual_sum_le
  let K₁ := min (1 / 2) (min (κ ^ 2 / (16384 * K_bi ^ 2 + 1)) (κ * ε / (32 * K_d7 + 1)))
  have hK₁_pos : 0 < K₁ := by dsimp only [K₁]; positivity
  have hK₁_half : K₁ ≤ 1 / 2 := min_le_left _ _
  have hK₁_bi : K₁ ≤ κ ^ 2 / (16384 * K_bi ^ 2 + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hK₁_d7 : K₁ ≤ κ * ε / (32 * K_d7 + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have h2K₁_le1 : 2 * K₁ ≤ 1 := by linarith only [hK₁_half]
  have h2K₁_pow16 : (2 * K₁) ^ 16 ≤ 2 * K₁ := by
    have h15 : (2 * K₁) ^ 15 ≤ 1 := pow_le_one₀ (by positivity) h2K₁_le1
    calc
      (2 * K₁) ^ 16 = (2 * K₁) * (2 * K₁) ^ 15 := by ring
      _ ≤ (2 * K₁) * 1 := mul_le_mul_of_nonneg_left h15 (by positivity)
      _ = 2 * K₁ := mul_one _
  let C_gram := 9 * (2 * (|completeWeilSelfFinitePart tiltedUnitSpline 1| + 5) / κ + 1)
  have hCgram0 : 0 < C_gram := by dsimp only [C_gram]; positivity
  let C_hi_bi := (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 262152
  let C_hi_d7 := (K_vq / κ) * 65536 * 16777217
  let C_Ψ := K_inv * 65537 * 16777217
  let L_thr : ℝ := max 2048
    (max ((262144 * C_gram + 1) ^ 4)
      (max ((128 * C_hi_bi + 1) ^ 64)
        (max ((2 * C_hi_d7 / ε + 1) ^ 32) ((C_Ψ + 1) ^ 16))))
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL_sub_N : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ (8 : ℕ) ≤ N := by
    have hsm := tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).bound zero_lt_one)
    filter_upwards [hsm, eventually_ge_atTop 3] with N hN hN3
    have hN0 : (0 : ℝ) < N := by positivity
    have hL0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    have h1 : Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by
      have habs : |Real.log (N : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by
        simpa only [Function.comp_def, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg hN0.le _), one_mul] using hN
      exact (le_abs_self _).trans habs
    calc
      Real.log (N : ℝ) ^ (8 : ℕ) ≤ ((N : ℝ) ^ (1 / 8 : ℝ)) ^ (8 : ℕ) := pow_le_pow_left₀ hL0 h1 8
      _ = N := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        norm_num
  refine ⟨K₁, hK₁_pos, hK₁_half, ?_⟩
  filter_upwards [hbi_var (13 / 32) (by norm_num) 128 (by norm_num),
    hq_var (13 / 32) (by norm_num) 128 (by norm_num),
    hinv_sum (13 / 32) (by norm_num) 128 (by norm_num),
    hL_sub_N, eventually_ge_atTop 256,
    hloglim.eventually_ge_atTop L_thr] with N hbiN hqN hinvN hL8N hN256 hL_ge
  intro c hc1 hc_up
  let L := Real.log (N : ℝ)
  have hL2048 : 2048 ≤ L := (le_max_left 2048 _).trans hL_ge
  have hL1024 : 1024 ≤ L := by linarith only [hL2048]
  have hL1 : 1 ≤ L := by linarith only [hL2048]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc_L8 : c ≤ L ^ (1 / 8 : ℝ) :=
    hc_up.trans (by
      have := mul_le_mul_of_nonneg_right h2K₁_le1 (Real.rpow_nonneg hL0.le (1 / 8 : ℝ))
      linarith only [this])
  have hc_le_L : c ≤ L :=
    hc_L8.trans ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 8 : ℝ) ≤ 1)).trans_eq
      (Real.rpow_one L))
  have hc7_le : c ^ 7 ≤ L ^ (7 / 8 : ℝ) := by
    calc
      c ^ 7 ≤ (L ^ (1 / 8 : ℝ)) ^ 7 := pow_le_pow_left₀ hc0.le hc_L8 7
      _ = L ^ (7 / 8 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hc8_le : c ^ 8 ≤ L := by
    calc
      c ^ 8 ≤ (L ^ (1 / 8 : ℝ)) ^ 8 := pow_le_pow_left₀ hc0.le hc_L8 8
      _ = L := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hc16_div : c ^ 16 / L ^ 2 ≤ 2 * K₁ := by
    have hp := pow_le_pow_left₀ hc0.le hc_up 16
    have he : (2 * K₁ * L ^ (1 / 8 : ℝ)) ^ 16 = (2 * K₁) ^ 16 * L ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 8 : ℝ)) 16, ← Real.rpow_mul hL0.le]
      norm_num
    exact ((div_le_iff₀ (sq_pos_of_pos hL0)).mpr (hp.trans_eq he)).trans h2K₁_pow16
  let Q₁ := ⌊L ^ (13 / 32 : ℝ)⌋₊
  have hQ₁_le : (Q₁ : ℝ) ≤ L ^ (13 / 32 : ℝ) := Nat.floor_le (by positivity)
  have hQ₁_1 : 1 ≤ Q₁ := Nat.le_floor (by exact_mod_cast Real.one_le_rpow hL1 (by norm_num))
  have hQ₁_ge2 : 2 ≤ Q₁ := by
    apply Nat.le_floor
    have h2 : (1024 : ℝ) ^ (13 / 32 : ℝ) ≤ L ^ (13 / 32 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hL1024 (by norm_num)
    have h1024 : (2 : ℝ) ≤ (1024 : ℝ) ^ (13 / 32 : ℝ) := by
      calc
        (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2 : ℝ) ^ (130 / 32 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = ((2 : ℝ) ^ (10 : ℕ)) ^ (13 / 32 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]; norm_num
        _ = (1024 : ℝ) ^ (13 / 32 : ℝ) := by norm_num
    exact_mod_cast h1024.trans h2
  have hQ₁_le_L : (Q₁ : ℝ) ≤ L :=
    hQ₁_le.trans ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (13 / 32 : ℝ) ≤ 1)).trans_eq
      (Real.rpow_one L))
  have hQ₁_sq : (Q₁ : ℝ) ^ 2 ≤ L ^ (13 / 16 : ℝ) := by
    calc
      (Q₁ : ℝ) ^ 2 ≤ (L ^ (13 / 32 : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ₁_le 2
      _ = L ^ (13 / 16 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hQ₁_sq_78 : (Q₁ : ℝ) ^ 2 ≤ L ^ (7 / 8 : ℝ) :=
    hQ₁_sq.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have hlogL_sq : (1 + Real.log L) ^ 2 ≤ 65536 * L ^ (1 / 128 : ℝ) := by
    calc
      (1 + Real.log L) ^ 2 ≤ (256 * L ^ (1 / 256 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by linarith [Real.log_nonneg hL1]) (one_add_log_le_rpow_256 hL1) 2
      _ = 65536 * L ^ (1 / 128 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 256 : ℝ)) 2, ← Real.rpow_mul hL0.le]; norm_num
  have h1Q_le : 1 + Real.log (Q₁ : ℝ) ≤ 1 + Real.log L := by
    linarith [Real.log_le_log (by exact_mod_cast (by omega : 0 < Q₁)) hQ₁_le_L]
  have hQ_logL_sq : (Q₁ : ℝ) ^ 2 * (1 + Real.log L) ^ 2 ≤ 65536 * L ^ (105 / 128 : ℝ) := by
    calc
      (Q₁ : ℝ) ^ 2 * (1 + Real.log L) ^ 2 ≤ L ^ (13 / 16 : ℝ) * (65536 * L ^ (1 / 128 : ℝ)) :=
        mul_le_mul hQ₁_sq hlogL_sq (sq_nonneg _) (by positivity)
      _ = 65536 * (L ^ (13 / 16 : ℝ) * L ^ (1 / 128 : ℝ)) := by ring
      _ = 65536 * L ^ (105 / 128 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
  have hQ_logQ_sq : (Q₁ : ℝ) ^ 2 * (1 + Real.log Q₁) ^ 2 ≤ 65536 * L ^ (7 / 8 : ℝ) := by
    have h1 : (1 + Real.log Q₁) ^ 2 ≤ (1 + Real.log L) ^ 2 :=
      pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg Q₁]) h1Q_le 2
    exact (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)).trans
      (hQ_logL_sq.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)) (by norm_num)))
  -- Overlap and packet size conditions against `N`.
  have hlarge : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ N := by
    have he1 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have hc2_L : c ^ 2 ≤ L :=
      (pow_le_pow_left₀ hc0.le hc_L8 2).trans
        (((by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num :
          (L ^ (1 / 8 : ℝ)) ^ 2 = L ^ (1 / 4 : ℝ)).le).trans
          ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 4 : ℝ) ≤ 1)).trans_eq
            (Real.rpow_one L)))
    have hL7 : (144 : ℝ) ≤ L ^ 7 := by
      have : (1024 : ℝ) ^ 1 ≤ L ^ 7 :=
        (pow_le_pow_left₀ (by norm_num) hL1024 1).trans (pow_le_pow_right₀ hL1 (by norm_num))
      linarith only [this]
    have h1 : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ 144 * L := by
      have h2 : 4 * (Real.exp 1 + 3) ^ 2 ≤ 144 := by nlinarith only [he1, Real.exp_pos 1]
      exact (mul_le_mul h2 hc2_L (sq_nonneg _) (by norm_num)).trans_eq (by ring)
    have h8 : L * L ^ 7 = L ^ 8 := by ring
    nlinarith only [h1, hL7, h8, hL8N, hL0]
  have hradN : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N := by
    have he2 : Real.exp 2 ≤ 8 := by
      have h1 : Real.exp 1 ≤ 2.8 := by have := Real.exp_one_lt_d9; linarith
      have hp : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith only [h1, hp, Real.exp_pos 1]
    have hR : linearNearRowRadius c + 1 ≤ 17 * c := by
      unfold linearNearRowRadius; nlinarith only [hc1, he2]
    have hc2_L : c ^ 2 ≤ L :=
      (pow_le_pow_left₀ hc0.le hc_L8 2).trans
        (((by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num :
          (L ^ (1 / 8 : ℝ)) ^ 2 = L ^ (1 / 4 : ℝ)).le).trans
          ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 4 : ℝ) ≤ 1)).trans_eq
            (Real.rpow_one L)))
    have h1 : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ 1156 * L := by
      have hsq := pow_le_pow_left₀ (by unfold linearNearRowRadius; positivity) hR 2
      have h2 : 4 * (17 * c) ^ 2 = 1156 * c ^ 2 := by ring
      nlinarith only [hsq, h2, hc2_L]
    have hL7 : (1156 : ℝ) ≤ L ^ 7 := by
      have : (1024 : ℝ) ^ 2 ≤ L ^ 7 :=
        (pow_le_pow_left₀ (by norm_num) hL1024 2).trans (pow_le_pow_right₀ hL1 (by norm_num))
      linarith only [this]
    have h8 : L * L ^ 7 = L ^ 8 := by ring
    nlinarith only [h1, hL7, h8, hL8N, hL0]
  have hc4N : c ^ 4 ≤ N := by
    have hc4_L : c ^ 4 ≤ L :=
      (pow_le_pow_left₀ hc0.le hc_L8 4).trans
        (((by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num :
          (L ^ (1 / 8 : ℝ)) ^ 4 = L ^ (1 / 2 : ℝ)).le).trans
          ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans_eq
            (Real.rpow_one L)))
    exact hc4_L.trans ((pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 8)).trans
      (by simpa only [pow_one] using hL8N))
  have hMQ_eq : max 2 Q₁ = Q₁ := max_eq_right hQ₁_ge2
  have hQ₁_sq_N : max 2 Q₁ * max 2 Q₁ ≤ N := by
    rw [hMQ_eq]
    have h1 : (Q₁ : ℝ) * Q₁ ≤ L ^ 2 := by
      calc
        (Q₁ : ℝ) * Q₁ ≤ L * L := mul_le_mul hQ₁_le_L hQ₁_le_L (Nat.cast_nonneg _) hL0.le
        _ = L ^ 2 := (sq L).symm
    have h2 : L ^ 2 ≤ N := (pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 8)).trans hL8N
    exact_mod_cast h1.trans h2
  have hlog18_Q₁ : 18 * (1 + Real.log (Q₁ : ℝ)) ≤ L := by
    have hsqrt36 : 36 ≤ Real.sqrt L := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 36)]
      exact Real.sqrt_le_sqrt (by linarith only [hL2048])
    have h1 := one_add_log_le_two_sqrt_pos hL0
    have h2 : 36 * Real.sqrt L ≤ Real.sqrt L * Real.sqrt L :=
      mul_le_mul_of_nonneg_right hsqrt36 (Real.sqrt_nonneg L)
    rw [Real.mul_self_sqrt hL0.le] at h2
    linarith only [h1Q_le, h1, h2]
  have hr_vb := rate_vb_critical_le hc1 hL1 hc_L8 hL8N
  have hr_q := rate_q_critical_le hc1 hL1 hc_L8 hL8N
  -- Threshold extractions from `L_thr ≤ L`.
  have hL_gram : 262144 * C_gram + 1 ≤ L ^ (1 / 4 : ℝ) := by
    have h := ((le_max_right 2048 _).trans hL_ge)
    have h1 : (262144 * C_gram + 1) ^ 4 ≤ L := (le_max_left _ _).trans h
    simpa using le_rpow_inv_nat_of_pow_le (by positivity) (by decide : 0 < 4) h1
  have hL_hibi : 128 * C_hi_bi + 1 ≤ L ^ (1 / 64 : ℝ) := by
    have h := (le_max_right _ _).trans ((le_max_right 2048 _).trans hL_ge)
    have h1 : (128 * C_hi_bi + 1) ^ 64 ≤ L := (le_max_left _ _).trans h
    simpa using le_rpow_inv_nat_of_pow_le (by dsimp only [C_hi_bi]; positivity)
      (by decide : 0 < 64) h1
  have hL_hid7 : 2 * C_hi_d7 / ε + 1 ≤ L ^ (1 / 32 : ℝ) := by
    have h := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right 2048 _).trans hL_ge))
    have h1 : (2 * C_hi_d7 / ε + 1) ^ 32 ≤ L := (le_max_left _ _).trans h
    simpa using le_rpow_inv_nat_of_pow_le (by dsimp only [C_hi_d7]; positivity)
      (by decide : 0 < 32) h1
  have hL_Ψ : C_Ψ + 1 ≤ L ^ (1 / 16 : ℝ) := by
    have h1 : (C_Ψ + 1) ^ 16 ≤ L :=
      (le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans ((le_max_right 2048 _).trans hL_ge)))
    simpa using le_rpow_inv_nat_of_pow_le (by dsimp only [C_Ψ]; positivity)
      (by decide : 0 < 16) h1
  -- Part 1a: Polarized Gram factor `≤ 1 / 4`.
  have hgram_small :
      C_gram * (1 + Real.log (max 2 Q₁ : ℕ)) ^ 2 * c ^ 4 / L ≤ 1 / 4 := by
    rw [hMQ_eq]
    have hlog4 : (1 + Real.log (Q₁ : ℝ)) ^ 2 ≤ 65536 * L ^ (1 / 4 : ℝ) := by
      have h1 : (1 + Real.log (Q₁ : ℝ)) ^ 2 ≤ (1 + Real.log L) ^ 2 :=
        pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg Q₁]) h1Q_le 2
      exact h1.trans (hlogL_sq.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)) (by norm_num)))
    have hc4 : c ^ 4 ≤ L ^ (1 / 2 : ℝ) := by
      calc
        c ^ 4 ≤ (L ^ (1 / 8 : ℝ)) ^ 4 := pow_le_pow_left₀ hc0.le hc_L8 4
        _ = L ^ (1 / 2 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    have hprod : (1 + Real.log (Q₁ : ℝ)) ^ 2 * c ^ 4 / L ≤ 65536 / L ^ (1 / 4 : ℝ) := by
      calc
        (1 + Real.log (Q₁ : ℝ)) ^ 2 * c ^ 4 / L ≤
            65536 * L ^ (1 / 4 : ℝ) * L ^ (1 / 2 : ℝ) / L :=
          div_le_div_of_nonneg_right
            (mul_le_mul hlog4 hc4 (by positivity) (by positivity)) hL0.le
        _ = 65536 * (L ^ (1 / 4 : ℝ) * L ^ (1 / 2 : ℝ) * L ^ (-1 : ℝ)) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one L]; ring
        _ = 65536 * L ^ (-1 / 4 : ℝ) := by
          rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
        _ = 65536 / L ^ (1 / 4 : ℝ) := by
          rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by norm_num, Real.rpow_neg hL0.le, div_eq_mul_inv]
    calc
      C_gram * (1 + Real.log (Q₁ : ℝ)) ^ 2 * c ^ 4 / L =
          C_gram * ((1 + Real.log (Q₁ : ℝ)) ^ 2 * c ^ 4 / L) := by ring
      _ ≤ C_gram * (65536 / L ^ (1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hprod hCgram0.le
      _ = 65536 * C_gram / L ^ (1 / 4 : ℝ) := by ring
      _ ≤ 1 / 4 := by
        rw [div_le_iff₀ (by positivity)]
        linarith only [hL_gram]
  -- Part 1b: Bilinear relative double sum `≤ 1 / 64`.
  have hbilin_small :
      (∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁,
        |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy tiltedUnitSpline c m •
              normalizedRamanujanHorizonVector m N,
          normalizedRamanujanHorizonVector l N⟫| ^ 2 /
          (completedConductorEnergy tiltedUnitSpline c m *
            completedConductorEnergy tiltedUnitSpline c l)) ≤ 1 / 64 := by
    let E : ℕ → ℝ := fun m => completedConductorEnergy tiltedUnitSpline c m
    let f : ℕ → ℕ → ℝ := fun m l =>
      |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
          E m • normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector l N⟫| ^ 2 / (E m * E l)
    have hE_nn : ∀ m : ℕ, 0 < m → 0 ≤ E m := fun m hm =>
      completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
        integral_tiltedUnitSpline_sq_pos hc0 hm
    have hf_nn : ∀ m ∈ Icc 1 Q₁, ∀ l ∈ Icc 1 Q₁, 0 ≤ f m l := fun m hm l hl =>
      div_nonneg (sq_nonneg _) (mul_nonneg (hE_nn m (mem_Icc.mp hm).1) (hE_nn l (mem_Icc.mp hl).1))
    -- Low-low block `(m : ℝ) ≤ c ∧ (l : ℝ) ≤ c`.
    have h_low : ∀ m ∈ Icc 1 Q₁, ∀ l ∈ Icc 1 Q₁,
        (if (m : ℝ) ≤ c ∧ (l : ℝ) ≤ c then f m l else 0) ≤
          (4 * K_bi ^ 2 / κ ^ 2) * (c ^ 16 / L ^ 2) *
            ((1 / (m : ℝ) ^ 2) * (1 / (l : ℝ) ^ 2)) := by
      intro m hm l hl
      split_ifs with hmlc
      · obtain ⟨hmc, hlc⟩ := hmlc
        obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
        obtain ⟨hl1, hlQ⟩ := mem_Icc.mp hl
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
        have hl0 : (0 : ℝ) < l := by exact_mod_cast hl1
        have hmax_le : max 2 (max m l) ≤ Q₁ := max_le hQ₁_ge2 (max_le hmQ hlQ)
        have hmax2N : max 2 (max m l) * max 2 (max m l) ≤ N :=
          (Nat.mul_le_mul hmax_le hmax_le).trans (by simpa only [hMQ_eq] using hQ₁_sq_N)
        have hmax_log : 18 * (1 + Real.log (max 2 (max m l) : ℕ)) ≤ L := by
          have hpos : (0 : ℝ) < (max 2 (max m l) : ℕ) := by exact_mod_cast (by omega : 0 < max 2 (max m l))
          have hle : ((max 2 (max m l) : ℕ) : ℝ) ≤ Q₁ := by exact_mod_cast hmax_le
          have := Real.log_le_log hpos hle
          linarith only [this, hlog18_Q₁]
        have hb := hbi_lf hm1 hl1 hmax2N hmax_log hc1 hradN hc4N
        have hsub : ((m : ℝ) * l) ^ 5 * (c ^ 5 * L / N) ≤ (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / L) := by
          have hm3 : (m : ℝ) ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ hm0.le hmc 3
          have hl3 : (l : ℝ) ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ hl0.le hlc 3
          have hc10N : c ^ 10 * L ^ 2 ≤ N := by
            calc
              c ^ 10 * L ^ 2 = c ^ 8 * c ^ 2 * L ^ 2 := by ring
              _ ≤ L * L ^ 2 * L ^ 2 := by
                have := pow_le_pow_left₀ hc0.le hc_le_L 2
                gcongr
              _ = L ^ 5 := by ring
              _ ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
              _ ≤ N := hL8N
          have hc_div : c ^ 11 * L / N ≤ c / L := by
            rw [div_le_div_iff₀ hN0 hL0]
            have := mul_le_mul_of_nonneg_left hc10N hc0.le
            linarith only [show c ^ 11 * L * L = c * (c ^ 10 * L ^ 2) by ring, this]
          calc
            ((m : ℝ) * l) ^ 5 * (c ^ 5 * L / N) =
                (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * ((m : ℝ) ^ 3 * (l : ℝ) ^ 3 * (c ^ 5 * L / N)) := by ring
            _ ≤ (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c ^ 3 * c ^ 3 * (c ^ 5 * L / N)) := by gcongr
            _ = (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c ^ 11 * L / N) := by ring
            _ ≤ (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / L) :=
              mul_le_mul_of_nonneg_left hc_div (by positivity)
        have hb2 : |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) - E m • normalizedRamanujanHorizonVector m N,
            normalizedRamanujanHorizonVector l N⟫| ≤
              2 * K_bi * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / L) :=
          hb.trans (by nlinarith only [hsub, hKbi])
        have hEm := completedConductorEnergy_tilted_ge_low hc0 hm1 hmc
        have hEl := completedConductorEnergy_tilted_ge_low hc0 hl1 hlc
        have hm23 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := pow_le_pow_right₀ (by exact_mod_cast hm1) (by decide)
        have hl23 : (l : ℝ) ^ 2 ≤ (l : ℝ) ^ 3 := pow_le_pow_right₀ (by exact_mod_cast hl1) (by decide)
        calc
          f m l ≤ (2 * K_bi * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / L)) ^ 2 /
              ((κ * ((m : ℝ) / c) ^ 7) * (κ * ((l : ℝ) / c) ^ 7)) := by
            refine (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hb2 2)
              (mul_nonneg (hE_nn m hm1) (hE_nn l hl1))).trans ?_
            exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
              (mul_le_mul hEm hEl (by positivity) (hE_nn m hm1))
          _ = (4 * K_bi ^ 2 / κ ^ 2) * (c ^ 16 / L ^ 2) *
                ((1 / (m : ℝ) ^ 3) * (1 / (l : ℝ) ^ 3)) := by
            field_simp [hκ.ne', hc0.ne', hL0.ne', hm0.ne', hl0.ne']
            ring
          _ ≤ (4 * K_bi ^ 2 / κ ^ 2) * (c ^ 16 / L ^ 2) *
                ((1 / (m : ℝ) ^ 2) * (1 / (l : ℝ) ^ 2)) := by
            gcongr
      · positivity
    have hsum_low :
        (∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁, if (m : ℝ) ≤ c ∧ (l : ℝ) ≤ c then f m l else 0) ≤
          1 / 128 := by
      have hinv := RHTower.Sieve.sum_inv_sq_le_two Q₁
      calc
        _ ≤ ∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁,
              (4 * K_bi ^ 2 / κ ^ 2) * (c ^ 16 / L ^ 2) *
                ((1 / (m : ℝ) ^ 2) * (1 / (l : ℝ) ^ 2)) :=
          sum_le_sum fun m hm => sum_le_sum fun l hl => h_low m hm l hl
        _ = (4 * K_bi ^ 2 / κ ^ 2) * (c ^ 16 / L ^ 2) *
              ((∑ m ∈ Icc 1 Q₁, 1 / (m : ℝ) ^ 2) * (∑ l ∈ Icc 1 Q₁, 1 / (l : ℝ) ^ 2)) := by
          rw [Finset.sum_mul_sum, mul_sum]
          exact sum_congr rfl fun _ _ => by rw [mul_sum]
        _ ≤ (4 * K_bi ^ 2 / κ ^ 2) * (2 * K₁) * (2 * 2) := by
          refine mul_le_mul
            (mul_le_mul_of_nonneg_left hc16_div (by positivity))
            (mul_le_mul hinv hinv (sum_nonneg fun _ _ => by positivity) (by norm_num))
            (mul_nonneg (sum_nonneg fun _ _ => by positivity) (sum_nonneg fun _ _ => by positivity))
            (by positivity)
        _ = (32 * K_bi ^ 2 / κ ^ 2) * K₁ := by ring
        _ ≤ (32 * K_bi ^ 2 / κ ^ 2) * (κ ^ 2 / (16384 * K_bi ^ 2 + 1)) :=
          mul_le_mul_of_nonneg_left hK₁_bi (by positivity)
        _ = 32 * K_bi ^ 2 / (16384 * K_bi ^ 2 + 1) := by field_simp [hκ.ne']
        _ ≤ 1 / 128 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith only [sq_nonneg K_bi]
    -- High-conductor blocks `¬ (m : ℝ) ≤ c` and `¬ (l : ℝ) ≤ c`.
    let r_vb := c * (1 + Real.log c) ^ 2 * L ^ (1 / (128 : ℕ) : ℝ) / L + c ^ 5 * L / (N : ℝ)
    have hr_vb0 : 0 ≤ r_vb := by
      have : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
      dsimp only [r_vb]; positivity
    have hr_vb_sq : r_vb ^ 2 ≤ 65537 ^ 2 * L ^ (-55 / 32 : ℝ) := by
      calc
        r_vb ^ 2 ≤ (65537 * L ^ (-55 / 64 : ℝ)) ^ 2 := pow_le_pow_left₀ hr_vb0 hr_vb 2
        _ = 65537 ^ 2 * L ^ (-55 / 32 : ℝ) := by
          rw [mul_pow, ← Real.rpow_natCast (L ^ (-55 / 64 : ℝ)) 2, ← Real.rpow_mul hL0.le]; norm_num
    have hpt_vb : ∀ m ∈ Icc 1 Q₁, ∀ l ∈ Icc 1 Q₁,
        f m l ≤ (K_vb ^ 2 * r_vb ^ 2) *
          (((m : ℝ) * (1 + Real.log m) ^ 2 / E m) * ((l : ℝ) / E l)) := by
      intro m hm l hl
      obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
      obtain ⟨hl1, hlQ⟩ := mem_Icc.mp hl
      have hb := hbiN m hm1 ((by exact_mod_cast hmQ : (m : ℝ) ≤ Q₁).trans hQ₁_le)
        l hl1 ((by exact_mod_cast hlQ : (l : ℝ) ≤ Q₁).trans hQ₁_le) c hc1 hlarge
      refine (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hb 2)
        (mul_nonneg (hE_nn m hm1) (hE_nn l hl1))).trans_eq ?_
      dsimp only [r_vb]
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have h_hiL : ∀ m ∈ Icc 1 Q₁, ∀ l ∈ Icc 1 Q₁,
        (if ¬ (m : ℝ) ≤ c then f m l else 0) ≤
          (K_vb ^ 2 * r_vb ^ 2) *
            (((Q₁ : ℝ) * (1 + Real.log L) ^ 2 / κ) * ((l : ℝ) / E l)) := by
      intro m hm l hl
      split_ifs with hmc
      · obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
        obtain ⟨hl1, _⟩ := mem_Icc.mp hl
        have hEm : κ ≤ E m :=
          tiltedUnitSpline_completedConductorEnergy_ge_above_overlap hc0 hm1 (le_of_not_ge hmc)
        have hm_num : (m : ℝ) * (1 + Real.log m) ^ 2 ≤ (Q₁ : ℝ) * (1 + Real.log L) ^ 2 := by
          have hmQ' : (m : ℝ) ≤ Q₁ := by exact_mod_cast hmQ
          have hlog : 1 + Real.log (m : ℝ) ≤ 1 + Real.log L := by
            have := Real.log_le_log (by exact_mod_cast hm1 : (0 : ℝ) < m) hmQ'
            linarith only [this, h1Q_le]
          exact mul_le_mul hmQ'
            (pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg m]) hlog 2)
            (sq_nonneg _) (Nat.cast_nonneg _)
        have hdiv : (m : ℝ) * (1 + Real.log m) ^ 2 / E m ≤ (Q₁ : ℝ) * (1 + Real.log L) ^ 2 / κ :=
          (div_le_div_of_nonneg_right hm_num (hE_nn m hm1)).trans
            (div_le_div_of_nonneg_left (by positivity) hκ hEm)
        exact (hpt_vb m hm l hl).trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hdiv (div_nonneg (Nat.cast_nonneg l) (hE_nn l hl1)))
          (by positivity))
      · have hl1 := (mem_Icc.mp hl).1
        exact mul_nonneg (by positivity)
          (mul_nonneg (by positivity) (div_nonneg (Nat.cast_nonneg l) (hE_nn l hl1)))
    have h_hiR : ∀ m ∈ Icc 1 Q₁, ∀ l ∈ Icc 1 Q₁,
        (if ¬ (l : ℝ) ≤ c then f m l else 0) ≤
          (K_vb ^ 2 * r_vb ^ 2) *
            (((m : ℝ) * (1 + Real.log m) ^ 2 / E m) * ((Q₁ : ℝ) / κ)) := by
      intro m hm l hl
      split_ifs with hlc
      · obtain ⟨hm1, _⟩ := mem_Icc.mp hm
        obtain ⟨hl1, hlQ⟩ := mem_Icc.mp hl
        have hEl : κ ≤ E l :=
          tiltedUnitSpline_completedConductorEnergy_ge_above_overlap hc0 hl1 (le_of_not_ge hlc)
        have hdiv : (l : ℝ) / E l ≤ (Q₁ : ℝ) / κ :=
          (div_le_div_of_nonneg_right (by exact_mod_cast hlQ) (hE_nn l hl1)).trans
            (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hκ hEl)
        exact (hpt_vb m hm l hl).trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdiv
            (div_nonneg (by positivity) (hE_nn m hm1))) (by positivity))
      · have hm1 := (mem_Icc.mp hm).1
        exact mul_nonneg (by positivity)
          (mul_nonneg (div_nonneg (by positivity) (hE_nn m hm1)) (by positivity))
    have hsum_hiL :
        (∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁, if ¬ (m : ℝ) ≤ c then f m l else 0) ≤
          (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 196608 / L ^ (1 / 64 : ℝ) := by
      have hsl := sum_conductor_inv_energy_le hc1 Q₁
      have hsl' : (2 * c ^ 7 + (Q₁ : ℝ) ^ 2) / κ ≤ 3 * L ^ (7 / 8 : ℝ) / κ :=
        div_le_div_of_nonneg_right (by linarith only [hc7_le, hQ₁_sq_78]) hκ.le
      calc
        _ ≤ ∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁,
              (K_vb ^ 2 * r_vb ^ 2) *
                (((Q₁ : ℝ) * (1 + Real.log L) ^ 2 / κ) * ((l : ℝ) / E l)) :=
          sum_le_sum fun m hm => sum_le_sum fun l hl => h_hiL m hm l hl
        _ = (K_vb ^ 2 * r_vb ^ 2) *
              (((Q₁ : ℝ) ^ 2 * (1 + Real.log L) ^ 2 / κ) * (∑ l ∈ Icc 1 Q₁, (l : ℝ) / E l)) := by
          rw [Finset.sum_mul_sum, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
        _ ≤ (K_vb ^ 2 * (65537 ^ 2 * L ^ (-55 / 32 : ℝ))) *
              ((65536 * L ^ (105 / 128 : ℝ) / κ) * (3 * L ^ (7 / 8 : ℝ) / κ)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hr_vb_sq (sq_nonneg _))
            (mul_le_mul (div_le_div_of_nonneg_right hQ_logL_sq hκ.le) (hsl.trans hsl')
              (sum_nonneg fun l hl => div_nonneg (Nat.cast_nonneg l) (hE_nn l (mem_Icc.mp hl).1))
              (by positivity))
            (mul_nonneg (by positivity)
              (sum_nonneg fun l hl => div_nonneg (Nat.cast_nonneg l) (hE_nn l (mem_Icc.mp hl).1)))
            (by positivity)
        _ = (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 196608 *
              (L ^ (-55 / 32 : ℝ) * L ^ (105 / 128 : ℝ) * L ^ (7 / 8 : ℝ)) := by ring
        _ = (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 196608 * L ^ (-3 / 128 : ℝ) := by
          rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
        _ ≤ (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 196608 * L ^ (-(1 / 64 : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
            (by positivity)
        _ = (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 196608 / L ^ (1 / 64 : ℝ) := by
          rw [Real.rpow_neg hL0.le, div_eq_mul_inv]
    have hsum_hiR :
        (∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁, if ¬ (l : ℝ) ≤ c then f m l else 0) ≤
          (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 65544 / L ^ (1 / 64 : ℝ) := by
      have hsm := sum_conductor_log_sq_inv_energy_le hc1 Q₁
      have hsm' : (8 * c ^ 7 + (Q₁ : ℝ) ^ 2 * (1 + Real.log Q₁) ^ 2) / κ ≤
          65544 * L ^ (7 / 8 : ℝ) / κ :=
        div_le_div_of_nonneg_right (by linarith only [hc7_le, hQ_logQ_sq]) hκ.le
      calc
        _ ≤ ∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁,
              (K_vb ^ 2 * r_vb ^ 2) *
                (((m : ℝ) * (1 + Real.log m) ^ 2 / E m) * ((Q₁ : ℝ) / κ)) :=
          sum_le_sum fun m hm => sum_le_sum fun l hl => h_hiR m hm l hl
        _ = (K_vb ^ 2 * r_vb ^ 2) *
              ((∑ m ∈ Icc 1 Q₁, (m : ℝ) * (1 + Real.log m) ^ 2 / E m) *
                ((Q₁ : ℝ) ^ 2 / κ)) := by
          rw [Finset.sum_mul_sum, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
        _ ≤ (K_vb ^ 2 * (65537 ^ 2 * L ^ (-55 / 32 : ℝ))) *
              ((65544 * L ^ (7 / 8 : ℝ) / κ) * (L ^ (13 / 16 : ℝ) / κ)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hr_vb_sq (sq_nonneg _))
            (mul_le_mul (hsm.trans hsm') (div_le_div_of_nonneg_right hQ₁_sq hκ.le)
              (by positivity) (by positivity))
            (mul_nonneg (sum_nonneg fun m hm => div_nonneg (by positivity)
              (hE_nn m (mem_Icc.mp hm).1)) (by positivity))
            (by positivity)
        _ = (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 65544 *
              (L ^ (-55 / 32 : ℝ) * L ^ (7 / 8 : ℝ) * L ^ (13 / 16 : ℝ)) := by ring
        _ = (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 65544 * L ^ (-1 / 32 : ℝ) := by
          rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
        _ ≤ (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 65544 * L ^ (-(1 / 64 : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
            (by positivity)
        _ = (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 65544 / L ^ (1 / 64 : ℝ) := by
          rw [Real.rpow_neg hL0.le, div_eq_mul_inv]
    have hsum_hi :
        (∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁, if ¬ (m : ℝ) ≤ c then f m l else 0) +
          (∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁, if ¬ (l : ℝ) ≤ c then f m l else 0) ≤ 1 / 128 := by
      calc
        _ ≤ (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 196608 / L ^ (1 / 64 : ℝ) +
              (K_vb ^ 2 / κ ^ 2) * 65537 ^ 2 * 65544 / L ^ (1 / 64 : ℝ) :=
          add_le_add hsum_hiL hsum_hiR
        _ = C_hi_bi / L ^ (1 / 64 : ℝ) := by dsimp only [C_hi_bi]; ring
        _ ≤ 1 / 128 := by
          rw [div_le_iff₀ (by positivity)]
          linarith only [hL_hibi]
    have hsplit :
        (∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁, f m l) ≤
          (∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁, if (m : ℝ) ≤ c ∧ (l : ℝ) ≤ c then f m l else 0) +
            (∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁, if ¬ (m : ℝ) ≤ c then f m l else 0) +
            (∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁, if ¬ (l : ℝ) ≤ c then f m l else 0) := by
      rw [← sum_add_distrib, ← sum_add_distrib]
      refine sum_le_sum fun m hm => ?_
      rw [← sum_add_distrib, ← sum_add_distrib]
      refine sum_le_sum fun l hl => ?_
      have h0 := hf_nn m hm l hl
      by_cases hmc : (m : ℝ) ≤ c <;> by_cases hlc : (l : ℝ) ≤ c <;> simp [hmc, hlc, h0]
    linarith only [hsplit, hsum_low, hsum_hi]
  refine ⟨fun a => spectralFloorWeilMatrix_subspace_inner_ge_of_bilinear_budget
    hQ₁_1 hQ₁_sq_N hL0 hc1 hgram_small hbilin_small a, ?_, ?_⟩
  -- Part 2: Full inverse-energy residual sum `≤ L ^ (1 / 4 : ℝ)`.
  · have hΨ_raw := hinvN c hc1 hlarge Q₁ hQ₁_le
    have hW : c ^ 7 + (Q₁ : ℝ) ^ 2 * (1 + Real.log Q₁) ^ 2 ≤ 65537 * L ^ (7 / 8 : ℝ) := by
      linarith only [hc7_le, hQ_logQ_sq]
    have hr_q0 : 0 ≤ c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (128 : ℕ) : ℝ) / L +
        c ^ 10 * (L / N) ^ 2 := by
      have : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
      positivity
    calc
      _ ≤ K_inv * (65537 * L ^ (7 / 8 : ℝ)) * (16777217 * L ^ (-187 / 256 : ℝ)) :=
        hΨ_raw.trans (mul_le_mul (mul_le_mul_of_nonneg_left hW hKinv.le) hr_q hr_q0
          (by positivity))
      _ = C_Ψ * (L ^ (7 / 8 : ℝ) * L ^ (-187 / 256 : ℝ)) := by dsimp only [C_Ψ]; ring
      _ = C_Ψ * L ^ (37 / 256 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
      _ ≤ C_Ψ * L ^ (3 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
          (by dsimp only [C_Ψ]; positivity)
      _ ≤ L ^ (1 / 16 : ℝ) * L ^ (3 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hL_Ψ]) (by positivity)
      _ = L ^ (1 / 4 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
  -- Part 3: Dual seventh-power collar budget `≤ ε`.
  · intro M h2BM
    let E : ℕ → ℝ := fun m => completedConductorEnergy tiltedUnitSpline c m
    let d7 : ℕ → ℝ := fun m =>
      topCollarDualSeventhMass M N
        (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          E m • normalizedRamanujanHorizonVector m N) / E m
    have hE_nn : ∀ m : ℕ, 0 < m → 0 ≤ E m := fun m hm =>
      completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
        integral_tiltedUnitSpline_sq_pos hc0 hm
    have hd7_nn : ∀ m ∈ Icc 1 Q₁, 0 ≤ d7 m := fun m hm =>
      div_nonneg (topCollarDualSeventhMass_nonneg _ _ _) (hE_nn m (mem_Icc.mp hm).1)
    have hrate_d7 : c ^ 2 / L + c ^ 3 * L / N + c ^ 10 * (L / N) ^ 2 ≤ 3 * c ^ 2 / L := by
      have ht1 : c ^ 3 * L / N ≤ c ^ 2 / L := by
        rw [div_le_div_iff₀ hN0 hL0]
        have hcLN : c * L ^ 2 ≤ N := by
          calc
            c * L ^ 2 ≤ L * L ^ 2 := mul_le_mul_of_nonneg_right hc_le_L (sq_nonneg _)
            _ = L ^ 3 := by ring
            _ ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
            _ ≤ N := hL8N
        have := mul_le_mul_of_nonneg_left hcLN (sq_nonneg c)
        linarith only [show c ^ 3 * L * L = c ^ 2 * (c * L ^ 2) by ring, this]
      have ht2 : c ^ 10 * (L / N) ^ 2 ≤ c ^ 2 / L := by
        rw [div_pow, mul_div_assoc', div_le_div_iff₀ (sq_pos_of_pos hN0) hL0]
        have hc8N : c ^ 8 * L ^ 3 ≤ (N : ℝ) ^ 2 := by
          calc
            c ^ 8 * L ^ 3 ≤ L * L ^ 3 := mul_le_mul_of_nonneg_right hc8_le (by positivity)
            _ = L ^ 4 := by ring
            _ ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
            _ ≤ N := hL8N
            _ ≤ (N : ℝ) ^ 2 := le_self_pow₀ (by exact_mod_cast hN1) (by decide)
        have := mul_le_mul_of_nonneg_left hc8N (sq_nonneg c)
        linarith only [show c ^ 10 * L ^ 2 * L = c ^ 2 * (c ^ 8 * L ^ 3) by ring, this]
      linarith only [ht1, ht2]
    have hd7_low : ∀ m ∈ Icc 1 Q₁,
        (if (m : ℝ) ≤ c then d7 m else 0) ≤
          (3 * K_d7 / κ) * (c ^ 9 / L) * (1 / (m : ℝ) ^ 2) := by
      intro m hm
      split_ifs with hmc
      · have hm1 := (mem_Icc.mp hm).1
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
        have hb := (hd7_lf hm1 hc1 hL1 hlarge hradN hc4N h2BM).trans
          (mul_le_mul_of_nonneg_left hrate_d7 (by positivity))
        have hEm := completedConductorEnergy_tilted_ge_low hc0 hm1 hmc
        have hm25 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 5 :=
          pow_le_pow_right₀ (by exact_mod_cast hm1) (by norm_num)
        calc
          d7 m ≤ (K_d7 * (m : ℝ) ^ 2 * (3 * c ^ 2 / L)) / (κ * ((m : ℝ) / c) ^ 7) :=
            (div_le_div_of_nonneg_right hb (hE_nn m hm1)).trans
              (div_le_div_of_nonneg_left (by positivity) (by positivity) hEm)
          _ = (3 * K_d7 / κ) * (c ^ 9 / L) * (1 / (m : ℝ) ^ 5) := by
            field_simp [hκ.ne', hc0.ne', hL0.ne', hm0.ne']; ring
          _ ≤ (3 * K_d7 / κ) * (c ^ 9 / L) * (1 / (m : ℝ) ^ 2) := by gcongr
      · positivity
    have hsum_d7_low :
        (c ^ 7 / L) * (∑ m ∈ Icc 1 Q₁, if (m : ℝ) ≤ c then d7 m else 0) ≤ ε / 2 := by
      have hinv := RHTower.Sieve.sum_inv_sq_le_two Q₁
      calc
        _ ≤ (c ^ 7 / L) * (∑ m ∈ Icc 1 Q₁, (3 * K_d7 / κ) * (c ^ 9 / L) * (1 / (m : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun m hm => hd7_low m hm) (by positivity)
        _ = (3 * K_d7 / κ) * (c ^ 16 / L ^ 2) * (∑ m ∈ Icc 1 Q₁, 1 / (m : ℝ) ^ 2) := by
          rw [← mul_sum]; ring
        _ ≤ (3 * K_d7 / κ) * (2 * K₁) * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hc16_div (by positivity)) hinv
            (sum_nonneg fun _ _ => by positivity) (by positivity)
        _ = (12 * K_d7 / κ) * K₁ := by ring
        _ ≤ (12 * K_d7 / κ) * (κ * ε / (32 * K_d7 + 1)) :=
          mul_le_mul_of_nonneg_left hK₁_d7 (by positivity)
        _ = 12 * K_d7 * ε / (32 * K_d7 + 1) := by field_simp [hκ.ne']
        _ ≤ ε / 2 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith only [hKd7, hε]
    let r_q := c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (128 : ℕ) : ℝ) / L + c ^ 10 * (L / N) ^ 2
    have hr_q0 : 0 ≤ r_q := by
      have : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
      dsimp only [r_q]; positivity
    have hd7_hi : ∀ m ∈ Icc 1 Q₁,
        (if ¬ (m : ℝ) ≤ c then d7 m else 0) ≤
          (K_vq / κ) * ((Q₁ : ℝ) * (1 + Real.log L) ^ 2) * r_q := by
      intro m hm
      split_ifs with hmc
      · obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
        have hmQ' : (m : ℝ) ≤ Q₁ := by exact_mod_cast hmQ
        have hEm : κ ≤ E m :=
          tiltedUnitSpline_completedConductorEnergy_ge_above_overlap hc0 hm1 (le_of_not_ge hmc)
        have hq_m := (topCollarDualSeventhMass_le_norm_sq M N _).trans
          (hqN m hm1 (hmQ'.trans hQ₁_le) c hc1 hlarge)
        have hm_num : (m : ℝ) * (1 + Real.log m) ^ 2 ≤ (Q₁ : ℝ) * (1 + Real.log L) ^ 2 := by
          have hlog : 1 + Real.log (m : ℝ) ≤ 1 + Real.log L := by
            have := Real.log_le_log (by exact_mod_cast hm1 : (0 : ℝ) < m) hmQ'
            linarith only [this, h1Q_le]
          exact mul_le_mul hmQ'
            (pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg m]) hlog 2)
            (sq_nonneg _) (Nat.cast_nonneg _)
        calc
          d7 m ≤ (K_vq * ((m : ℝ) * (1 + Real.log m) ^ 2) * r_q) / κ :=
            (div_le_div_of_nonneg_right hq_m (hE_nn m hm1)).trans
              (div_le_div_of_nonneg_left (by positivity) hκ hEm)
          _ ≤ (K_vq * ((Q₁ : ℝ) * (1 + Real.log L) ^ 2) * r_q) / κ :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_num hKvq.le) hr_q0) hκ.le
          _ = (K_vq / κ) * ((Q₁ : ℝ) * (1 + Real.log L) ^ 2) * r_q := by ring
      · positivity
    have hsum_d7_hi :
        (c ^ 7 / L) * (∑ m ∈ Icc 1 Q₁, if ¬ (m : ℝ) ≤ c then d7 m else 0) ≤ ε / 2 := by
      have hc7L : c ^ 7 / L ≤ L ^ (-1 / 8 : ℝ) := by
        calc
          c ^ 7 / L ≤ L ^ (7 / 8 : ℝ) / L := div_le_div_of_nonneg_right hc7_le hL0.le
          _ = L ^ (7 / 8 : ℝ) * L ^ (-1 : ℝ) := by rw [div_eq_mul_inv, ← Real.rpow_neg_one L]
          _ = L ^ (-1 / 8 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
      calc
        _ ≤ (c ^ 7 / L) *
              (∑ _m ∈ Icc 1 Q₁, (K_vq / κ) * ((Q₁ : ℝ) * (1 + Real.log L) ^ 2) * r_q) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun m hm => hd7_hi m hm) (by positivity)
        _ = (K_vq / κ) * (c ^ 7 / L) * ((Q₁ : ℝ) ^ 2 * (1 + Real.log L) ^ 2) * r_q := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
        _ ≤ (K_vq / κ) * L ^ (-1 / 8 : ℝ) *
              (65536 * L ^ (105 / 128 : ℝ)) * (16777217 * L ^ (-187 / 256 : ℝ)) := by
          refine mul_le_mul
            (mul_le_mul (mul_le_mul_of_nonneg_left hc7L (by positivity)) hQ_logL_sq
              (by positivity) (by positivity))
            hr_q hr_q0 (by positivity)
        _ = C_hi_d7 * (L ^ (-1 / 8 : ℝ) * L ^ (105 / 128 : ℝ) * L ^ (-187 / 256 : ℝ)) := by
          dsimp only [C_hi_d7]; ring
        _ = C_hi_d7 * L ^ (-9 / 256 : ℝ) := by
          rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
        _ ≤ C_hi_d7 * L ^ (-(1 / 32 : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
            (by dsimp only [C_hi_d7]; positivity)
        _ = C_hi_d7 / L ^ (1 / 32 : ℝ) := by rw [Real.rpow_neg hL0.le, div_eq_mul_inv]
        _ ≤ ε / 2 := by
          rw [div_le_iff₀ (by positivity)]
          have h := mul_le_mul_of_nonneg_left hL_hid7 hε.le
          have heq : ε * (2 * C_hi_d7 / ε + 1) = 2 * C_hi_d7 + ε := by field_simp [hε.ne']
          linarith only [h, heq, hε]
    have hsplit : (∑ m ∈ Icc 1 Q₁, d7 m) =
        (∑ m ∈ Icc 1 Q₁, if (m : ℝ) ≤ c then d7 m else 0) +
          (∑ m ∈ Icc 1 Q₁, if ¬ (m : ℝ) ≤ c then d7 m else 0) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun m _ => by by_cases hmc : (m : ℝ) ≤ c <;> simp [hmc]
    rw [hsplit, mul_add]
    linarith only [hsum_d7_low, hsum_d7_hi]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

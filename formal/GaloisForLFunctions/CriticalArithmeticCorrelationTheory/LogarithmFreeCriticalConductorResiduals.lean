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
    have hr1_coord : ∀ n : PrimeHorizonIndex N, |r₁ n| ≤ |B_row n| / Real.sqrt (Real.log N) := by
      intro n
      have hn : (n : ℕ) ∈ Icc 1 N := n.2
      have hmode1 : ∀ j : ℕ, ramanujanPoleProfile 1 j = 1 / Real.sqrt j := fun j => by
        rw [ramanujanPoleProfile, normalizedRamanujanMode, ramanujanMode_one,
          Nat.totient_one, Nat.cast_one, Real.sqrt_one, div_one]
      have heq : r₁ n = B_row n / Real.sqrt (Real.log N) := by
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
      rw [heq, abs_div, abs_of_pos (Real.sqrt_pos.mpr hL0)]
    have hp := abs_inner_of_coord_div_sqrt_log hl r₁ (fun n => |B_row n|) (fun _ => abs_nonneg _) hr1_coord
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
    let B : ℕ → ℝ := fun n => 5 * |α| * (m : ℝ) * Real.sqrt n / N
    have hB0 : ∀ n, 0 ≤ B n := fun n => by dsimp only [B]; positivity
    have hcoord : ∀ n : PrimeHorizonIndex N, |u n| ≤ B n / Real.sqrt (Real.log N) := by
      intro n
      have hn : (n : ℕ) ∈ Icc 1 N := n.2
      have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hsm_le : Real.sqrt (m : ℝ) ≤ m := by
        have hsq : (Real.sqrt (m : ℝ)) ^ 2 ≤ (m : ℝ) ^ 2 := by
          rw [Real.sq_sqrt (by positivity)]; nlinarith only [hm1R]
        have h := Real.sqrt_le_sqrt hsq
        rwa [Real.sqrt_sq (Real.sqrt_nonneg _), Real.sqrt_sq (by positivity)] at h
      have heq : u n = ((α / N) * ∑ j ∈ Icc 1 N,
          (Real.sqrt (n : ℕ) / Real.sqrt j + Real.sqrt j / Real.sqrt (n : ℕ) -
            archimedeanCenterKernel n j) *
            (normalizedRamanujanMode m j / Real.sqrt j)) / Real.sqrt (Real.log N) := by
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
      rw [heq, abs_div, abs_of_pos (Real.sqrt_pos.mpr hL0)]
      refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      rw [abs_mul, abs_div, abs_of_pos hN0]
      have hrow := abs_sum_poleMinusCollar_poleProfile_le hn (Real.sqrt_nonneg (m : ℝ))
        (abs_mode_le_sqrt_conductor hm n)
        (fun a b hab => CompletedArithmeticForms.abs_sum_Ico_normalizedRamanujanMode_le hm2 hab)
      calc
        |α| / N * |∑ j ∈ Icc 1 N,
            (Real.sqrt (n : ℕ) / Real.sqrt j + Real.sqrt j / Real.sqrt (n : ℕ) -
              archimedeanCenterKernel n j) * (normalizedRamanujanMode m j / Real.sqrt j)|
            ≤ |α| / N * ((4 * (m : ℝ) + Real.sqrt m) * Real.sqrt (n : ℕ)) :=
          mul_le_mul_of_nonneg_left hrow (by positivity)
        _ ≤ |α| / N * ((5 * (m : ℝ)) * Real.sqrt (n : ℕ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by linarith only [hsm_le]) (Real.sqrt_nonneg _))
            (by positivity)
        _ = B n := by dsimp only [B]; ring
    have hp := abs_inner_of_coord_div_sqrt_log hl u B hB0 hcoord
    have hsumB : (∑ n ∈ Icc 1 N, B n / Real.sqrt n) ≤ 5 * |α| * (m : ℝ) := by
      have hpt : ∀ n ∈ Icc 1 N, B n / Real.sqrt n = 5 * |α| * (m : ℝ) / N := by
        intro n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
        dsimp only [B]; field_simp [hsn.ne', hN0.ne']
      rw [sum_congr rfl hpt, sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
      field_simp [hN0.ne']; exact le_rfl
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
      ((hasDerivAt_inv hx0).const_mul r).congr_deriv (by field_simp [hx0]; ring)
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
      have hR : 2 * (h : ℝ) ≤ N := (by linarith only [hh_Rc]).trans (h2R.trans hradN)
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
      have h := one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hrc_inv 2)
      rwa [div_pow, one_pow, one_div_one_div] at h
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
          field_simp [hx0.ne', hy0.ne']; ring
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
              ≤ (∫ t, φ t ^ 2) * ((y - x) * (1 / (x * y))) := by
            rw [div_eq_mul_one_div]
            exact mul_le_mul_of_nonneg_right (hG_le _) hnn
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
  have hN1 : 1 ≤ N := by
    have : 2 * 2 ≤ R₂ * R₂ := Nat.mul_le_mul hR₂2 hR₂2
    omega
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
    have h := norm_normalizedRamanujanHorizonVector_le_two_sqrt hm N
    have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
    rwa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m), show (2 : ℝ) ^ 2 = 4 by norm_num] at hsq
  have hvl_sq : ‖normalizedRamanujanHorizonVector l N‖ ^ 2 ≤ 4 * (l : ℝ) := by
    have h := norm_normalizedRamanujanHorizonVector_le_two_sqrt hl N
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
    have hlead := midBand_leadKernel_sum_eq hφ hsupp hL0 hc0 hw1 hradN a
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
      rw [hsub_sum, mul_sum]
      have hM0 : (∫ t, φ t ^ 2) ≠ 0 := hM.ne'
      calc
        (∫ t, φ t ^ 2) * (2 / ((∫ t, φ t ^ 2) * m.totient) *
            ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, ramanujanLagCoefficient m h *
              ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u)
            = (2 / (m.totient : ℝ)) *
                ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, ramanujanLagCoefficient m h *
                  ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u := by
              field_simp [hM0, htot0]
        _ = _ := by
              rw [mul_sum, mul_sum]
              exact sum_congr rfl fun h _ => by ring
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
    have hlead_p := midBand_leadKernel_sum_eq hφ hsupp hL0 hc0 hw1 hradN a_p
    have hlead_m := midBand_leadKernel_sum_eq hφ hsupp hL0 hc0 hw1 hradN a_m
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
        rw [← mul_assoc, mul_inv_cancel₀ hL0.ne', one_mul] at this
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
        rw [← mul_assoc, mul_inv_cancel₀ hL0.ne', one_mul] at this
        linarith only [this, (by ring : Real.log (N : ℝ) * ((∫ t, φ t ^ 2) *
          ∑ n ∈ Icc 1 N, primeHorizonExtension (v_m - v_l) n *
            nearGram φ c N (primeHorizonExtension (v_m - v_l)) n) =
          (∫ t, φ t ^ 2) * Real.log N *
            ∑ n ∈ Icc 1 N, primeHorizonExtension (v_m - v_l) n *
              nearGram φ c N (primeHorizonExtension (v_m - v_l)) n)]
      have hsub := congrArg (fun x => (∫ t, φ t ^ 2) * Real.log N * x) hpol
      dsimp only at hsub
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
  let R₂ := max 2 (max m l)
  have hR₂2 : 2 ≤ R₂ := le_max_left 2 _
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N := by
    have : 2 * 2 ≤ R₂ * R₂ := Nat.mul_le_mul hR₂2 hR₂2
    omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL1 : 1 ≤ Real.log (N : ℝ) := by
    have hlogR : 0 ≤ Real.log (R₂ : ℝ) := Real.log_natCast_nonneg R₂
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
  let v_m := normalizedRamanujanHorizonVector m N
  let v_l := normalizedRamanujanHorizonVector l N
  -- Step 1: Adjoint transpose to `downwardPrimeVector`.
  have hadj : ⟪upwardPrimeVector φ c N v_m - shellCorrection φ c m • v_m, v_l⟫ =
      ⟪v_m, downwardPrimeVector φ c N v_l⟫ - shellCorrection φ c m * ⟪v_m, v_l⟫ := by
    rw [inner_sub_left, real_inner_smul_left, upwardPrimeVector_inner_eq_downward]
  -- Step 2: Expand `downwardPrimeVector φ c N v_l` into interior + exterior rows.
  let g := atomDilate φ (c / N)
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp hw0
  have hG : 0 < ∫ u, g u ^ 2 := by
    dsimp only [g]; rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hM
  have hdown_coord : ∀ n ∈ Icc 1 N,
      primeHorizonExtension (downwardPrimeVector φ c N v_l) n =
        (Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
          (interiorDownwardPrimeRow g N l n + regroupedExteriorDownwardPrimeRow g c N l n) := by
    intro n hn
    rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
    change downwardPrimeRow g N (primeHorizonExtension v_l) n / (∫ u, g u ^ 2) = _
    have hvl_ext : ∀ j ∈ Icc 1 N, primeHorizonExtension v_l j =
        (Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
          (ramanujanLagCoefficient l j / Real.sqrt j) := by
      intro j hj
      rw [primeHorizonExtension_normalizedRamanujan hj]
      unfold ramanujanPoleProfile normalizedRamanujanMode ramanujanMode
      rw [ramanujanSum_eq_ramanujanLagCoefficient hl j, Complex.ofReal_re]
      field_simp [hsltot_pos.ne', hsL0.ne']
    rw [downwardPrimeRow_congr_smul hvl_ext, mul_div_assoc]
    congr 1
    have hsub := downwardRamanujanRow_sub_interior_eq hc0 hn hgsupp l
    linarith only [hsub]
  -- Step 3: Split `interiorDownwardPrimeRow` into `nearGram`, `log N - log j`, and `divisorJet`.
  let row_log : ℕ → ℝ := fun n => ∑ j ∈ nearRowIndices c N n,
    shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
      (Real.log N - Real.log j) * normalizedRamanujanMode l j / Real.sqrt j
  let row_jet : ℕ → ℝ := fun n => (Real.sqrt (l.totient : ℝ))⁻¹ * ∑ j ∈ nearRowIndices c N n,
    shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
      ramanujanLogDivisorJet l j / Real.sqrt j
  have hint_decomp : ∀ n ∈ Icc 1 N,
      (Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ * interiorDownwardPrimeRow g N l n =
        Real.log N * nearGram φ c N (primeHorizonExtension v_l) n -
          (Real.sqrt (Real.log N))⁻¹ * row_log n -
          (Real.sqrt (Real.log N))⁻¹ * row_jet n := by
    intro n hn
    have hprime : interiorDownwardPrimeRow g N l n =
        ∑ j ∈ nearRowIndices c N n,
          shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
            (∑ d ∈ j.divisors, (ArithmeticFunction.vonMangoldt d : ℝ) *
              ramanujanLagCoefficient l (j / d)) / Real.sqrt j := by
      dsimp only [g]
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
    unfold nearGram
    dsimp only [row_log, row_jet]
    rw [mul_sum, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun j hj => ?_
    have hjN := (mem_filter.mp hj).1
    rw [sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet l (mem_Icc.mp hjN).1,
      primeHorizonExtension_normalizedRamanujan hjN]
    unfold ramanujanPoleProfile normalizedRamanujanMode ramanujanMode
    rw [ramanujanSum_eq_ramanujanLagCoefficient hl j, Complex.ofReal_re]
    field_simp [hsltot_pos.ne', hsL0.ne']
    ring
  -- Express `⟪v_m, downwardPrimeVector φ c N v_l⟫` as a sum over `Icc 1 N`.
  have hinner_down : ⟪v_m, downwardPrimeVector φ c N v_l⟫ =
      Real.log N * nearGramModeBilin φ c N m l -
        (∑ n ∈ Icc 1 N, primeHorizonExtension v_m n * ((Real.sqrt (Real.log N))⁻¹ * row_log n)) -
        (∑ n ∈ Icc 1 N, primeHorizonExtension v_m n * ((Real.sqrt (Real.log N))⁻¹ * row_jet n)) +
        (∑ n ∈ Icc 1 N, primeHorizonExtension v_m n *
          ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
            regroupedExteriorDownwardPrimeRow g c N l n)) := by
    have hsum_eq : ⟪v_m, downwardPrimeVector φ c N v_l⟫ =
        ∑ n ∈ Icc 1 N, primeHorizonExtension v_m n *
          primeHorizonExtension (downwardPrimeVector φ c N v_l) n := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change (∑ i : PrimeHorizonIndex N, (downwardPrimeVector φ c N v_l) i * v_m i) = _
      rw [← sum_coe_sort (Icc 1 N)]
      refine sum_congr rfl fun i _ => ?_
      rw [primeHorizonExtension_coe, primeHorizonExtension_coe, mul_comm]
    rw [hsum_eq]
    have hpt : ∀ n ∈ Icc 1 N,
        primeHorizonExtension v_m n * primeHorizonExtension (downwardPrimeVector φ c N v_l) n =
          Real.log N * (primeHorizonExtension v_m n * nearGram φ c N (primeHorizonExtension v_l) n) -
            primeHorizonExtension v_m n * ((Real.sqrt (Real.log N))⁻¹ * row_log n) -
            primeHorizonExtension v_m n * ((Real.sqrt (Real.log N))⁻¹ * row_jet n) +
            primeHorizonExtension v_m n *
              ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
                regroupedExteriorDownwardPrimeRow g c N l n) := by
      intro n hn
      rw [hdown_coord n hn, mul_add, hint_decomp n hn]
      ring
    rw [sum_congr rfl hpt, sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum]
    rfl
  -- Bound Piece 1: `|Real.log N * nearGramModeBilin - shellCorrection * ⟪v_m, v_l⟫|`.
  have hp1 : |Real.log N * nearGramModeBilin φ c N m l - shellCorrection φ c m * ⟪v_m, v_l⟫| ≤
      C_ng * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) +
        C_sc * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) := by
    have hid1 : Real.log N * nearGramModeBilin φ c N m l - shellCorrection φ c m * ⟪v_m, v_l⟫ =
        Real.log N * (nearGramModeBilin φ c N m l -
            (if m = l then shellCorrection φ c m / Real.log N else 0)) -
          shellCorrection φ c m * (⟪v_m, v_l⟫ - if m = l then 1 else 0) := by
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
    -- Gram discrepancy `|⟪v_m, v_l⟫ - δ_{m,l}|` via `abs_inner_sum_normalizedRamanujanHorizonVector_sub_le`.
    have hgram_b : |⟪v_m, v_l⟫ - (if m = l then 1 else 0)| ≤
        36 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 / Real.log N := by
      let am : ℕ → ℝ := fun k => if k = m then 1 else 0
      let al : ℕ → ℝ := fun k => if k = l then 1 else 0
      have hmR : m ∈ Icc 1 R₂ := mem_Icc.mpr ⟨hm, (le_max_left m l).trans (le_max_right 2 _)⟩
      have hlR : l ∈ Icc 1 R₂ := mem_Icc.mpr ⟨hl, (le_max_right m l).trans (le_max_right 2 _)⟩
      have hsum_am : (∑ k ∈ Icc 1 R₂, am k • normalizedRamanujanHorizonVector k N) = v_m := by
        have hpt : ∀ k ∈ Icc 1 R₂, am k • normalizedRamanujanHorizonVector k N =
            if k = m then v_m else 0 := fun k _ => by
          dsimp only [am]; by_cases hkm : k = m <;> simp [hkm, v_m]
        rw [sum_congr rfl hpt, sum_ite_eq', if_pos hmR]
      have hsum_al : (∑ k ∈ Icc 1 R₂, al k • normalizedRamanujanHorizonVector k N) = v_l := by
        have hpt : ∀ k ∈ Icc 1 R₂, al k • normalizedRamanujanHorizonVector k N =
            if k = l then v_l else 0 := fun k _ => by
          dsimp only [al]; by_cases hkl : k = l <;> simp [hkl, v_l]
        rw [sum_congr rfl hpt, sum_ite_eq', if_pos hlR]
      have hdot : (∑ k ∈ Icc 1 R₂, am k * al k) = if m = l then 1 else 0 := by
        have hpt : ∀ k ∈ Icc 1 R₂, am k * al k = if k = m then (if m = l then 1 else 0) else 0 := by
          intro k _
          dsimp only [am, al]
          by_cases hkm : k = m
          · subst hkm; rw [if_pos rfl, one_mul]
          · rw [if_neg hkm, zero_mul]
        rw [sum_congr rfl hpt, sum_ite_eq', if_pos hmR]
      have hsq_am : (∑ k ∈ Icc 1 R₂, am k ^ 2) = 1 := by
        have hpt : ∀ k ∈ Icc 1 R₂, am k ^ 2 = if k = m then 1 else 0 := fun k _ => by
          dsimp only [am]; by_cases hkm : k = m <;> simp [hkm]
        rw [sum_congr rfl hpt, sum_ite_eq', if_pos hmR]
      have hsq_al : (∑ k ∈ Icc 1 R₂, al k ^ 2) = 1 := by
        have hpt : ∀ k ∈ Icc 1 R₂, al k ^ 2 = if k = l then 1 else 0 := fun k _ => by
          dsimp only [al]; by_cases hkl : k = l <;> simp [hkl]
        rw [sum_congr rfl hpt, sum_ite_eq', if_pos hlR]
      have hg0 := CompletedArithmeticForms.abs_inner_sum_normalizedRamanujanHorizonVector_sub_le
        hR₂2 hR2N am al
      rw [hsum_am, hsum_al, hdot, hsq_am, hsq_al, Real.sqrt_one, mul_one, mul_one] at hg0
      have hR2_le : (R₂ : ℝ) ≤ 2 * ((m : ℝ) * l) := by
        dsimp only [R₂]
        rw [Nat.cast_max, Nat.cast_max, Nat.cast_ofNat]
        exact max_le (by linarith only [hml1]) (max_le (by nlinarith only [hm1R, hl1R])
          (by nlinarith only [hm1R, hl1R]))
      have hlogR2 : 1 + Real.log (R₂ : ℝ) ≤ 4 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 := by
        have hR0 : (0 : ℝ) < R₂ := by positivity
        have h1 := one_add_log_le_two_sqrt_pos hR0
        have hs : Real.sqrt (R₂ : ℝ) ≤ R₂ := by
          have hsq : (Real.sqrt (R₂ : ℝ)) ^ 2 ≤ (R₂ : ℝ) ^ 2 := by
            rw [Real.sq_sqrt hR0.le]; have : (1 : ℝ) ≤ R₂ := by exact_mod_cast (by omega : 1 ≤ R₂)
            nlinarith only [this]
          have h := Real.sqrt_le_sqrt hsq
          rwa [Real.sqrt_sq (Real.sqrt_nonneg _), Real.sqrt_sq hR0.le] at h
        have hml_sq : (m : ℝ) * l ≤ (m : ℝ) ^ 2 * (l : ℝ) ^ 2 := by
          have : 1 ≤ (m : ℝ) * l := hml1
          nlinarith only [this, hm1R, hl1R]
        linarith only [h1, hs, hR2_le, hml_sq]
      exact hg0.trans ((div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogR2 (by norm_num)) hL0.le).trans_eq (by ring))
    have hsc_b := CompletedArithmeticForms.abs_shellCorrection_le_linear hφ hsupp hM hm hc0
    have hsc_term : |shellCorrection φ c m * (⟪v_m, v_l⟫ - if m = l then 1 else 0)| ≤
        C_sc * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) := by
      rw [abs_mul]
      calc
        |shellCorrection φ c m| * |⟪v_m, v_l⟫ - _|
            ≤ (2 * (Real.log 4 + 4) * c) * (36 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 / Real.log N) :=
          mul_le_mul hsc_b hgram_b (abs_nonneg _) (by positivity)
        _ = C_sc * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) := by
          dsimp only [C_sc]; ring
    exact (abs_sub _ _).trans (add_le_add hng_b hsc_term)
  -- Helper geometry on `nearRowIndices c N n`.
  have he_gap : Real.exp (2 * c / N) - 1 ≤ linearNearRowRadius c / N := by
    calc
      Real.exp (2 * c / N) - 1 ≤ 2 * c / N * Real.exp (2 * c / N) := exp_sub_one_le_mul_exp
      _ ≤ 2 * c / N * Real.exp 2 :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by
            have h := mul_le_mul_of_nonneg_left hw1 zero_le_two
            simpa only [mul_div_assoc, mul_one] using h)) (by positivity)
      _ = linearNearRowRadius c / N := by unfold linearNearRowRadius; ring
  have hnear_card_sqrt : ∀ n ∈ Icc 1 N,
      ((nearRowIndices c N n).card : ℝ) ≤ 2 * (n : ℝ) * (linearNearRowRadius c / N) ∧
      ∀ j ∈ nearRowIndices c N n,
        1 / Real.sqrt j ≤ Real.exp 1 / Real.sqrt n ∧
        |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)| ≤ 1 ∧
        0 ≤ Real.log N - Real.log j ∧
        Real.log N - Real.log j ≤ 2 + Real.log ((N : ℝ) / n) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    let rad_n := (n : ℝ) * (linearNearRowRadius c / N)
    have hrad0 : 0 ≤ rad_n := by dsimp only [rad_n]; unfold linearNearRowRadius; positivity
    have hcard_n : ((nearRowIndices c N n).card : ℝ) ≤ 2 * rad_n := by
      have hsub : nearRowIndices c N n ⊆
          (Icc 1 N).filter (fun j => j ≠ n ∧ |(j : ℝ) - n| ≤ rad_n) := by
        intro j hj
        obtain ⟨hjN, hjn, hlog⟩ := mem_filter.mp hj
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
        have hdist := (abs_sub_le_of_abs_log_le hj0 hn0 hlog).trans
          (mul_le_mul_of_nonneg_left he_gap hn0.le)
        exact mem_filter.mpr ⟨hjN, hjn, hdist⟩
      exact (show ((nearRowIndices c N n).card : ℝ) ≤
          (((Icc 1 N).filter (fun j => j ≠ n ∧ |(j : ℝ) - n| ≤ rad_n)).card : ℝ) by
          exact_mod_cast card_le_card hsub).trans (card_near_le (Icc 1 N) n hrad0)
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
  -- Bound Piece 2 (`row_log`): `2 + log(N/n) ≤ 2 √(N/n)`.
  have hp2 : |∑ n ∈ Icc 1 N, primeHorizonExtension v_m n * ((Real.sqrt (Real.log N))⁻¹ * row_log n)| ≤
      C_p2 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) := by
    have hpt : ∀ n ∈ Icc 1 N,
        |primeHorizonExtension v_m n * ((Real.sqrt (Real.log N))⁻¹ * row_log n)| ≤
          (4 * Real.exp 1 * linearNearRowRadius c * Real.sqrt m * Real.sqrt l /
            (Real.sqrt N * Real.log N)) * (1 / Real.sqrt n) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
      have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
      obtain ⟨hcard_n, hpt_j⟩ := hnear_card_sqrt n hn
      have hlog_sqrt : 2 + Real.log ((N : ℝ) / n) ≤ 2 * Real.sqrt ((N : ℝ) / n) :=
        two_add_log_le_two_sqrt (div_pos hN0 hn0)
      have hrow_le : |row_log n| ≤ 4 * Real.exp 1 * linearNearRowRadius c * Real.sqrt l / Real.sqrt N := by
        have hj_le : ∀ j ∈ nearRowIndices c N n,
            |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
              (Real.log N - Real.log j) * normalizedRamanujanMode l j / Real.sqrt j| ≤
              2 * Real.exp 1 * Real.sqrt l * Real.sqrt ((N : ℝ) / n) / Real.sqrt n := by
          intro j hj
          obtain ⟨hsj, hq1, hlnn, hlub⟩ := hpt_j j hj
          have hm_l := abs_mode_le_sqrt_conductor hl j
          rw [div_eq_mul_one_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg hlnn]
          have h12 : |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)| *
              (Real.log N - Real.log j) ≤ 2 * Real.sqrt ((N : ℝ) / n) := by
            calc
              _ ≤ 1 * (2 + Real.log ((N : ℝ) / n)) :=
                mul_le_mul hq1 hlub hlnn zero_le_one
              _ ≤ 2 * Real.sqrt ((N : ℝ) / n) := by linarith only [hlog_sqrt]
          have h34 : |normalizedRamanujanMode l j| * |1 / Real.sqrt (j : ℝ)| ≤
              Real.sqrt l * (Real.exp 1 / Real.sqrt n) := by
            rw [abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (j : ℝ))]
            exact mul_le_mul hm_l hsj (by positivity) (Real.sqrt_nonneg _)
          exact (mul_le_mul h12 h34 (by positivity) (by positivity)).trans_eq (by ring)
        dsimp only [row_log]
        calc
          |row_log n| ≤ ∑ j ∈ nearRowIndices c N n,
              (2 * Real.exp 1 * Real.sqrt l * Real.sqrt ((N : ℝ) / n) / Real.sqrt n) :=
            (abs_sum_le_sum_abs _ _).trans (sum_le_sum hj_le)
          _ = ((nearRowIndices c N n).card : ℝ) *
                (2 * Real.exp 1 * Real.sqrt l * Real.sqrt ((N : ℝ) / n) / Real.sqrt n) := by
            rw [sum_const, nsmul_eq_mul]
          _ ≤ (2 * (n : ℝ) * (linearNearRowRadius c / N)) *
                (2 * Real.exp 1 * Real.sqrt l * (Real.sqrt N / Real.sqrt n) / Real.sqrt n) := by
            rw [Real.sqrt_div hN0.le]
            exact mul_le_mul_of_nonneg_right hcard_n (by unfold linearNearRowRadius; positivity)
          _ = 4 * Real.exp 1 * linearNearRowRadius c * Real.sqrt l / Real.sqrt N := by
            field_simp [hsn.ne', hsN.ne', hN0.ne']
            rw [Real.sq_sqrt hn0.le, Real.sq_sqrt hN0.le]; ring
      have hvm_n : |primeHorizonExtension v_m n| ≤
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
        |primeHorizonExtension v_m n| * ((Real.sqrt (Real.log N))⁻¹ * |row_log n|)
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
    have hsm_m2 : Real.sqrt (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      have hsq : (Real.sqrt (m : ℝ)) ^ 2 ≤ ((m : ℝ) ^ 2) ^ 2 := by
        rw [Real.sq_sqrt (by positivity)]; nlinarith only [hm1R, sq_nonneg ((m : ℝ) - 1)]
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (Real.sqrt_nonneg _), Real.sqrt_sq (by positivity)] at h
    have hsl_l2 : Real.sqrt (l : ℝ) ≤ (l : ℝ) ^ 2 := by
      have hsq : (Real.sqrt (l : ℝ)) ^ 2 ≤ ((l : ℝ) ^ 2) ^ 2 := by
        rw [Real.sq_sqrt (by positivity)]; nlinarith only [hl1R, sq_nonneg ((l : ℝ) - 1)]
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (Real.sqrt_nonneg _), Real.sqrt_sq (by positivity)] at h
    have hexp3 : Real.exp 1 * Real.exp 2 = Real.exp 3 := by
      rw [← Real.exp_add]; norm_num
    calc
      |∑ n ∈ Icc 1 N, primeHorizonExtension v_m n * ((Real.sqrt (Real.log N))⁻¹ * row_log n)|
          ≤ (4 * Real.exp 1 * linearNearRowRadius c * Real.sqrt m * Real.sqrt l /
              (Real.sqrt N * Real.log N)) * ∑ n ∈ Icc 1 N, 1 / Real.sqrt n := by
        rw [mul_sum]
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)
      _ ≤ (4 * Real.exp 1 * linearNearRowRadius c * Real.sqrt m * Real.sqrt l /
              (Real.sqrt N * Real.log N)) * (2 * Real.sqrt N) :=
        mul_le_mul_of_nonneg_left hsum_inv (by unfold linearNearRowRadius; positivity)
      _ = 16 * (Real.exp 1 * Real.exp 2) * (Real.sqrt m * Real.sqrt l) * (c / Real.log N) := by
        unfold linearNearRowRadius
        have hsN : (Real.sqrt (N : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hN0).ne'
        field_simp [hsN, hL0.ne']; ring
      _ ≤ C_p2 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) := by
        rw [hexp3]; dsimp only [C_p2]
        have hprod := mul_le_mul hsm_m2 hsl_l2 (Real.sqrt_nonneg _) (by positivity)
        exact (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprod (by positivity)) (by positivity)).trans_eq (by ring)
  -- Bound Piece 3 (`row_jet`): `|ramanujanLogDivisorJet l j| ≤ 2 * l.totient * (1 + log l)`.
  have hp3 : |∑ n ∈ Icc 1 N, primeHorizonExtension v_m n * ((Real.sqrt (Real.log N))⁻¹ * row_jet n)| ≤
      C_p3 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) := by
    have hjb : ∀ j : ℕ, (Real.sqrt (l.totient : ℝ))⁻¹ * |ramanujanLogDivisorJet l j| ≤
        4 * (l : ℝ) := by
      intro j
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
          rw [Real.sq_sqrt hltot_pos.le]; ring
        _ ≤ 2 * Real.sqrt l * (2 * Real.sqrt l) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsl_le zero_le_two) hlog_l
            (by linarith [Real.log_natCast_nonneg l]) (by positivity)
        _ = 4 * (l : ℝ) := by
          rw [show 2 * Real.sqrt (l : ℝ) * (2 * Real.sqrt l) =
            4 * (Real.sqrt l * Real.sqrt l) by ring, Real.mul_self_sqrt (by positivity)]
    have hpt : ∀ n ∈ Icc 1 N,
        |primeHorizonExtension v_m n * ((Real.sqrt (Real.log N))⁻¹ * row_jet n)| ≤
          8 * Real.exp 1 * linearNearRowRadius c * Real.sqrt m * l / ((N : ℝ) * Real.log N) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
      obtain ⟨hcard_n, hpt_j⟩ := hnear_card_sqrt n hn
      have hrow_le : |row_jet n| ≤
          8 * Real.exp 1 * linearNearRowRadius c * l * Real.sqrt n / N := by
        have hj_le : ∀ j ∈ nearRowIndices c N n,
            (Real.sqrt (l.totient : ℝ))⁻¹ *
              |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2) *
                ramanujanLogDivisorJet l j / Real.sqrt j| ≤
              4 * Real.exp 1 * l / Real.sqrt n := by
          intro j hj
          obtain ⟨hsj, hq1, -, -⟩ := hpt_j j hj
          rw [div_eq_mul_one_div, abs_mul, abs_mul,
            abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (j : ℝ))]
          have h1 : |shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)| *
              ((Real.sqrt (l.totient : ℝ))⁻¹ * |ramanujanLogDivisorJet l j|) ≤ 4 * (l : ℝ) := by
            simpa only [one_mul] using mul_le_mul hq1 (hjb j) (by positivity) zero_le_one
          calc
            (Real.sqrt (l.totient : ℝ))⁻¹ *
                (|shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)| *
                  |ramanujanLogDivisorJet l j| * (1 / Real.sqrt j))
                = (|shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)| *
                    ((Real.sqrt (l.totient : ℝ))⁻¹ * |ramanujanLogDivisorJet l j|)) *
                    (1 / Real.sqrt j) := by ring
            _ ≤ (4 * (l : ℝ)) * (Real.exp 1 / Real.sqrt n) :=
              mul_le_mul h1 hsj (by positivity) (by positivity)
            _ = 4 * Real.exp 1 * l / Real.sqrt n := by ring
        dsimp only [row_jet]
        rw [abs_mul, abs_of_pos (inv_pos.mpr hsltot_pos)]
        calc
          (Real.sqrt (l.totient : ℝ))⁻¹ * |∑ j ∈ nearRowIndices c N n, _|
              ≤ ∑ j ∈ nearRowIndices c N n, (4 * Real.exp 1 * l / Real.sqrt n) := by
            refine (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)).trans ?_
            rw [mul_sum]
            exact sum_le_sum hj_le
          _ = ((nearRowIndices c N n).card : ℝ) * (4 * Real.exp 1 * l / Real.sqrt n) := by
            rw [sum_const, nsmul_eq_mul]
          _ ≤ (2 * (n : ℝ) * (linearNearRowRadius c / N)) * (4 * Real.exp 1 * l / Real.sqrt n) :=
            mul_le_mul_of_nonneg_right hcard_n (by positivity)
          _ = 8 * Real.exp 1 * linearNearRowRadius c * l * Real.sqrt n / N := by
            field_simp [hsn.ne', hN0.ne']
            rw [Real.sq_sqrt hn0.le]; ring
      have hvm_n : |primeHorizonExtension v_m n| ≤
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
        |primeHorizonExtension v_m n| * ((Real.sqrt (Real.log N))⁻¹ * |row_jet n|)
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
    have hsm_m2 : Real.sqrt (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      have hsq : (Real.sqrt (m : ℝ)) ^ 2 ≤ ((m : ℝ) ^ 2) ^ 2 := by
        rw [Real.sq_sqrt (by positivity)]; nlinarith only [hm1R, sq_nonneg ((m : ℝ) - 1)]
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (Real.sqrt_nonneg _), Real.sqrt_sq (by positivity)] at h
    have hl_l2 : (l : ℝ) ≤ (l : ℝ) ^ 2 := by nlinarith only [hl1R]
    calc
      |∑ n ∈ Icc 1 N, primeHorizonExtension v_m n * ((Real.sqrt (Real.log N))⁻¹ * row_jet n)|
          ≤ ∑ _n ∈ Icc 1 N,
              (8 * Real.exp 1 * linearNearRowRadius c * Real.sqrt m * l /
                ((N : ℝ) * Real.log N)) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt)
      _ = 16 * (Real.exp 1 * Real.exp 2) * (Real.sqrt m * l) * (c / Real.log N) := by
        rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
        unfold linearNearRowRadius
        field_simp [hN0.ne', hL0.ne']; ring
      _ ≤ C_p3 * (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) := by
        rw [hexp3]; dsimp only [C_p3]
        have hprod := mul_le_mul hsm_m2 hl_l2 (Nat.cast_nonneg l) (by positivity)
        exact (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprod (by positivity)) (by positivity)).trans_eq (by ring)
  -- Bound Piece 4 (exterior downward row): `O(√(m l) * c^2 / N)`.
  have hp4 : |∑ n ∈ Icc 1 N, primeHorizonExtension v_m n *
        ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
          regroupedExteriorDownwardPrimeRow g c N l n)| ≤
      C_ext * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by
    have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgsupp
    have hB_le : (linearPrimeStrip c : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc1
    have hcN : c ≤ (N : ℝ) := (div_le_one hN0).mp hw1
    have hcut_ub : (exteriorPrimeCutoff c N : ℝ) ≤ 5 * (N : ℝ) := by
      have h1 : (exteriorPrimeCutoff c N : ℝ) ≤ (N : ℝ) + linearPrimeStrip c := by
        exact_mod_cast (exteriorPrimeCutoff_bounds_small_width hc0 hN1 hw1).2
      have he1 : Real.exp 1 ≤ 3 := by have h := Real.exp_one_lt_d9; linarith
      nlinarith only [h1, hB_le, hcN, he1, hc0]
    have hrow_reg : ∀ n : ℕ, |regroupedExteriorDownwardPrimeRow g c N l n| ≤
        5 * (l.totient : ℝ) * linearPrimeStrip c * Real.log N / Real.sqrt N := by
      intro n
      have hcard : ((Ioc N (exteriorPrimeCutoff c N)).card : ℝ) ≤ linearPrimeStrip c := by
        have hbound := (exteriorPrimeCutoff_bounds_small_width hc0 hN1 hw1).2
        rw [Nat.card_Ioc]
        exact_mod_cast (show exteriorPrimeCutoff c N - N ≤ linearPrimeStrip c by omega)
      have hterm : ∀ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
          |horizonRamanujanMangoldt l N ℓ / Real.sqrt ℓ *
            (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2))| ≤
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
        have hcorr : |bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2)| ≤ 1 := by
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
    -- Only `n ≥ N - linearPrimeStrip c` (`n ≥ N / 2`) are active.
    have h2strip_N : 2 * linearPrimeStrip c ≤ N := by
      have he1 : Real.exp 1 ≤ 3 := by have h := Real.exp_one_lt_d9; linarith
      have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      have h1 : 2 * ((Real.exp 1 + 1) * c) ≤ 4 * (linearNearRowRadius c + 1) ^ 2 := by
        unfold linearNearRowRadius
        have he2 : 4 ≤ Real.exp 2 := by
          have h := Real.exp_one_lt_d9
          have h2 : (2 : ℝ) ≤ Real.exp 1 := by
            have := Real.add_one_le_exp (1 : ℝ); linarith
          have hp : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          nlinarith only [h2, hp]
        nlinarith only [hc1, he1, he2]
      have hR : 2 * (linearPrimeStrip c : ℝ) ≤ N :=
        (by linarith only [hB_le]).trans (h1.trans hradN)
      exact_mod_cast hR
    let S := (Icc 1 N).filter (fun n => N - linearPrimeStrip c ≤ n)
    have hrestrict : (∑ n ∈ Icc 1 N, primeHorizonExtension v_m n *
          ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
            regroupedExteriorDownwardPrimeRow g c N l n)) =
        ∑ n ∈ S, primeHorizonExtension v_m n *
          ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
            regroupedExteriorDownwardPrimeRow g c N l n) := by
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
    have hpt_S : ∀ n ∈ S, |primeHorizonExtension v_m n *
          ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
            regroupedExteriorDownwardPrimeRow g c N l n)| ≤
        10 * (Real.exp 1 + 1) * Real.sqrt m * Real.sqrt l * c / N := by
      intro n hnS
      obtain ⟨hn, hn_lo⟩ := mem_filter.mp hnS
      have hn_ge : N ≤ 2 * n := by omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
      have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
      have hinv_sn : 1 / Real.sqrt n ≤ 2 / Real.sqrt N := by
        rw [div_le_div_iff₀ hsn hsN]
        have hsq : (Real.sqrt (N : ℝ)) ^ 2 ≤ (2 * Real.sqrt n) ^ 2 := by
          rw [Real.sq_sqrt hN0.le, mul_pow, Real.sq_sqrt hn0.le]
          have : (N : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hn_ge
          linarith only [this]
        have h := Real.sqrt_le_sqrt hsq
        rwa [Real.sqrt_sq hsN.le, Real.sqrt_sq (by positivity)] at h
      have hvm_n : |primeHorizonExtension v_m n| ≤
          2 * Real.sqrt m / (Real.sqrt N * Real.sqrt (Real.log N)) := by
        rw [primeHorizonExtension_normalizedRamanujan hn]
        unfold ramanujanPoleProfile
        rw [abs_mul, abs_div, abs_of_pos (inv_pos.mpr hsL0), abs_of_pos hsn]
        calc
          (Real.sqrt (Real.log N))⁻¹ * (|normalizedRamanujanMode m n| / Real.sqrt n)
              ≤ (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt m * (1 / Real.sqrt n)) := by
            rw [ ← mul_one_div]
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
            regroupedExteriorDownwardPrimeRow g c N l n| ≤
          5 * (Real.exp 1 + 1) * Real.sqrt l * c * Real.sqrt (Real.log N) / Real.sqrt N := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr (mul_pos hsltot_pos hsL0))]
        calc
          (Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
              |regroupedExteriorDownwardPrimeRow g c N l n|
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
    have hsm_ml5 : Real.sqrt (m : ℝ) * Real.sqrt l ≤ ((m : ℝ) * l) ^ 5 := by
      rw [← Real.sqrt_mul (by positivity)]
      have h1 : Real.sqrt ((m : ℝ) * l) ≤ (m : ℝ) * l := by
        have hsq : (Real.sqrt ((m : ℝ) * l)) ^ 2 ≤ ((m : ℝ) * l) ^ 2 := by
          rw [Real.sq_sqrt (by positivity)]; nlinarith only [hml1]
        have h := Real.sqrt_le_sqrt hsq
        rwa [Real.sqrt_sq (Real.sqrt_nonneg _), Real.sqrt_sq (by positivity)] at h
      exact h1.trans (le_self_pow₀ hml1 (by decide))
    have hc2_5 : c ^ 2 / N ≤ c ^ 5 * Real.log N / N := by
      apply div_le_div_of_nonneg_right _ hN0.le
      exact (pow_le_pow_right₀ hc1 (by norm_num : 2 ≤ 5)).trans
        (le_mul_of_one_le_right (by positivity) hL1)
    calc
      |∑ n ∈ S, _| ≤ ∑ _n ∈ S, (10 * (Real.exp 1 + 1) * Real.sqrt m * Real.sqrt l * c / N) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hpt_S)
      _ = (S.card : ℝ) * (10 * (Real.exp 1 + 1) * Real.sqrt m * Real.sqrt l * c / N) := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ ((Real.exp 1 + 2) * c) *
            (10 * (Real.exp 1 + 1) * Real.sqrt m * Real.sqrt l * c / N) :=
        mul_le_mul_of_nonneg_right hcard_S (by positivity)
      _ = C_ext * (Real.sqrt m * Real.sqrt l) * (c ^ 2 / N) := by
        dsimp only [C_ext]; ring
      _ ≤ C_ext * ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsm_ml5 (by dsimp only [C_ext]; positivity))
          hc2_5 (by positivity) (by dsimp only [C_ext]; positivity)
  have hcomb : ⟪upwardPrimeVector φ c N v_m - shellCorrection φ c m • v_m, v_l⟫ =
      ((Real.log N * nearGramModeBilin φ c N m l - shellCorrection φ c m * ⟪v_m, v_l⟫) -
        ∑ n ∈ Icc 1 N, primeHorizonExtension v_m n * ((Real.sqrt (Real.log N))⁻¹ * row_log n)) +
      (-(∑ n ∈ Icc 1 N, primeHorizonExtension v_m n * ((Real.sqrt (Real.log N))⁻¹ * row_jet n)) +
        ∑ n ∈ Icc 1 N, primeHorizonExtension v_m n *
          ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
            regroupedExteriorDownwardPrimeRow g c N l n)) := by
    rw [hadj, hinner_down]; ring
  have htri1 := abs_add_le
    ((Real.log N * nearGramModeBilin φ c N m l - shellCorrection φ c m * ⟪v_m, v_l⟫) -
      ∑ n ∈ Icc 1 N, primeHorizonExtension v_m n * ((Real.sqrt (Real.log N))⁻¹ * row_log n))
    (-(∑ n ∈ Icc 1 N, primeHorizonExtension v_m n * ((Real.sqrt (Real.log N))⁻¹ * row_jet n)) +
      ∑ n ∈ Icc 1 N, primeHorizonExtension v_m n *
        ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
          regroupedExteriorDownwardPrimeRow g c N l n))
  have htri2 := abs_sub
    (Real.log N * nearGramModeBilin φ c N m l - shellCorrection φ c m * ⟪v_m, v_l⟫)
    (∑ n ∈ Icc 1 N, primeHorizonExtension v_m n * ((Real.sqrt (Real.log N))⁻¹ * row_log n))
  have htri3 := abs_add_le
    (-(∑ n ∈ Icc 1 N, primeHorizonExtension v_m n * ((Real.sqrt (Real.log N))⁻¹ * row_jet n)))
    (∑ n ∈ Icc 1 N, primeHorizonExtension v_m n *
      ((Real.sqrt (l.totient : ℝ) * Real.sqrt (Real.log N))⁻¹ *
        regroupedExteriorDownwardPrimeRow g c N l n))
  rw [abs_neg] at htri3
  rw [hcomb]
  have hA0 : 0 ≤ (m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c / Real.log N) := by positivity
  have hB0 : 0 ≤ ((m : ℝ) * l) ^ 5 * (c ^ 5 * Real.log N / N) := by positivity
  dsimp only [C_ub]
  nlinarith only [htri1, htri2, htri3, hp1, hp2, hp3, hp4, hA0, hB0]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

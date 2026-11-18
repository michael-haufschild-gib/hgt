import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ConductorSmoothingBeyondTheSplineKnots
import GaloisForLFunctions.CountingHolography.Sections.TheSignedProductOverSquareConductors

/-!
# Conductor-smoothed shell savings and the seventeen-eighteenths prefix criterion

Combining eighth-order single-conductor quotient cancellation with ninth-order
two-variable conductor-mesh smoothing resolves the `7/4` shell question and its
neighbouring subquadratic shells:

1. Pointwise on each conductor, `|powerProductShell (7 / 4) n| ≤ C · (1 + log(2n)) / n`,
   giving `∑_{N < n ≤ M} n² |powerProductShell (7 / 4) n| ≤ C · N² · (1 + log(2N))`.
2. Summing with signs across conductors smooths the B-spline knots by one further
   order, yielding `|∑_{N < n ≤ M} n² · powerProductShell (7 / 4) n| ≤ C · N^(7/4) · (1 + log(2N))`
   for all `N ≤ M ≤ 2N` (hence `O_δ(N^(7/2 - δ))` for every `δ < 7/4`), and more
   generally `O_α(N^(9α - 14) · (1 + log(2N)))` on every shell `⌊n^α⌋ < pv ≤ 2⌊n^α⌋`
   with `3/2 ≤ α < 2`.
3. On individual conductors all products through `⌊n^(15/8)⌋` are paid within six
   logarithms; summing across dyadic conductor octaves pays all products through
   `⌊n^(17/9)⌋ = (n²)^(17/18)` in the signed ACS prefix criterion for zero width,
   the five-sixths zero-free strip, and the Riemann Hypothesis.
-/

noncomputable section
open Finset Filter
open GaloisForLFunctions.CountingHolography.Sections
open GaloisForLFunctions.SquareRootThreshold
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Single-conductor paid product cutoff `⌊n^(15/8)⌋ = (n²)^(15/16)`. -/
def fifteenSixteenthsCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (15 / 8 : ℝ)⌋₊

/-- Capped PVC reading above the fifteen-sixteenths product cutoff. -/
def fifteenSixteenthsConductor (n : ℕ) : ℝ :=
  cappedUpperProductReading (fifteenSixteenthsCut n) n n

/-- Weighted conductor prefix above `⌊n^(15/8)⌋`. -/
def fifteenSixteenthsConductorPrefix (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, (n : ℝ) ^ 2 * fifteenSixteenthsConductor n

/-- Conductor-smoothed paid product cutoff `⌊n^(17/9)⌋ = (n²)^(17/18)`. -/
def seventeenNinthsCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (17 / 9 : ℝ)⌋₊

/-- Capped PVC reading above the seventeen-eighteenths product cutoff. -/
def seventeenNinthsConductor (n : ℕ) : ℝ :=
  cappedUpperProductReading (seventeenNinthsCut n) n n

/-- Weighted conductor prefix above `⌊n^(17/9)⌋`. -/
def seventeenNinthsConductorPrefix (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, (n : ℝ) ^ 2 * seventeenNinthsConductor n

/-- General dyadic product cutoff `⌊n^α⌋` and its capped shell `T_n(⌊n^α⌋, n) - T_n(2⌊n^α⌋, n)`. -/
def powerProductCut (α : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ α⌋₊

def powerProductShell (α : ℝ) (n : ℕ) : ℝ :=
  cappedUpperProductReading (powerProductCut α n) n n -
    cappedUpperProductReading (2 * powerProductCut α n) n n

/-- Explicit unfolding of the `7/4` shell `B_n = T_n(⌊n^(7/4)⌋, n) - T_n(2⌊n^(7/4)⌋, n)`. -/
theorem powerProductShell_sevenFourths_eq (n : ℕ) :
    powerProductShell (7 / 4) n =
      cappedUpperProductReading ⌊(n : ℝ) ^ (7 / 4 : ℝ)⌋₊ n n -
        cappedUpperProductReading (2 * ⌊(n : ℝ) ^ (7 / 4 : ℝ)⌋₊) n n := rfl

private abbrev logFactor (n : ℕ) : ℝ := 1 + Real.log (2 * (n : ℝ))

private theorem logFactor_one_le (n : ℕ) : 1 ≤ logFactor n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [logFactor]
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact le_add_of_nonneg_right (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * n))

private theorem logFactor_mono {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    logFactor n ≤ logFactor N :=
  add_le_add le_rfl (Real.log_le_log (by positivity)
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hnN) (by norm_num)))

private theorem logFactor_pow_subpower {b : ℝ} (hb : 0 < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {n : ℕ}, 0 < n → (logFactor n) ^ 6 ≤ K * (n : ℝ) ^ b := by
  let a := b / 6
  have ha : 0 < a := div_pos hb (by norm_num)
  refine ⟨(1 + 1 / a) ^ 6 * (2 : ℝ) ^ b, by positivity, fun {n} hn => ?_⟩
  let t := 2 * (n : ℝ)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : 1 ≤ t := by dsimp only [t]; linarith only [hn']
  have ht0 := zero_lt_one.trans_le ht
  have hbase : logFactor n ≤ (1 + 1 / a) * t ^ a := by
    have h1 := Real.one_le_rpow ht ha.le
    have h2 := Real.log_le_rpow_div ht0.le ha
    change 1 + Real.log t ≤ _
    exact (add_le_add h1 h2).trans_eq (by ring)
  have he : (t ^ a) ^ 6 = t ^ b := by
    rw [← Real.rpow_natCast _ 6, ← Real.rpow_mul ht0.le]
    congr 1; dsimp only [a]; ring
  refine (pow_le_pow_left₀ (zero_le_one.trans (logFactor_one_le n)) hbase 6).trans_eq ?_
  rw [mul_pow, he, show t ^ b = (2 : ℝ) ^ b * (n : ℝ) ^ b from
    Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)]
  ring

private theorem monotone_powerProductCut {α : ℝ} (hα : 0 ≤ α) : Monotone (powerProductCut α) :=
  fun _ _ hmn => Nat.floor_mono (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hmn) hα)

private theorem power_shell_geometry {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ powerProductCut α n ∧
      16 * (powerProductCut α n : ℝ) < Real.exp (-8) * (n : ℝ) ^ 2 ∧
      productLower 1 (splineHorizon n) ≤ powerProductCut α n := by
  obtain ⟨A, hA, hwin⟩ := successorSquare_window_bound
  have ht1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (2 - α)) atTop atTop :=
    (Real.tendsto_rpow_atTop (by linarith : 0 < 2 - α)).comp tendsto_natCast_atTop_atTop
  have ht2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (α - 1)) atTop atTop :=
    (Real.tendsto_rpow_atTop (by linarith : 0 < α - 1)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    ht1.eventually_ge_atTop (17 * Real.exp 8),
    ht2.eventually_ge_atTop (2 * A + 1)] with n hn hhi hlo
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  let X := (n : ℝ) ^ α
  have hX1 : 1 ≤ X := Real.one_le_rpow hn1 (by linarith)
  have hV_le : (powerProductCut α n : ℝ) ≤ X := Nat.floor_le (zero_le_one.trans hX1)
  refine ⟨(Nat.one_le_floor_iff _).mpr hX1, ?_, ?_⟩
  · have hmul : X * (n : ℝ) ^ (2 - α) = (n : ℝ) ^ 2 := by
      dsimp only [X]; rw [← Real.rpow_add hn0, add_sub_cancel, Real.rpow_two]
    have hgap : 16 < Real.exp (-8) * (n : ℝ) ^ (2 - α) := by
      rw [Real.exp_neg, inv_mul_eq_div, lt_div_iff₀ (Real.exp_pos 8)]
      exact (by nlinarith [Real.exp_pos 8] : 16 * Real.exp 8 < 17 * Real.exp 8).trans_le hhi
    have hh := mul_lt_mul_of_pos_left hgap (zero_lt_one.trans_le hX1)
    rw [mul_left_comm X, hmul] at hh
    nlinarith [hV_le]
  · apply Nat.le_floor
    have hmul : (n : ℝ) ^ (α - 1) * n = X := by
      dsimp only [X]; rw [← Real.rpow_one (n : ℝ), ← Real.rpow_add hn0]; congr 1; ring
    have hroot : Real.sqrt (splineHorizon n) ≤ A * n := by
      have hs := Real.sqrt_le_sqrt (hwin hn)
      rwa [Real.sqrt_sq (mul_nonneg (zero_le_one.trans hA) hn0.le)] at hs
    have hpl : (productLower 1 (splineHorizon n) : ℝ) ≤ 2 * Real.sqrt (splineHorizon n) := by
      refine (Nat.cast_le.mpr (min_le_right _ _)).trans ?_
      push_cast
      exact mul_le_mul_of_nonneg_left (Nat.floor_le (Real.sqrt_nonneg _)) (by norm_num)
    calc (productLower 1 (splineHorizon n) : ℝ)
        ≤ 2 * (A * n) := hpl.trans (mul_le_mul_of_nonneg_left hroot (by norm_num))
      _ ≤ (n : ℝ) ^ (α - 1) * n := by nlinarith [hlo, hn0.le]
      _ = X := hmul

private theorem log_two_mul_cut_le {α : ℝ} (hα : 0 ≤ α) {n : ℕ} (hn : 0 < n)
    (hpos : 1 ≤ powerProductCut α n) :
    1 + Real.log ((2 * powerProductCut α n : ℕ) : ℝ) ≤ (1 + α) * logFactor n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hv0 : (0 : ℝ) < powerProductCut α n := Nat.cast_pos.mpr hpos
  have hfl : (powerProductCut α n : ℝ) ≤ (n : ℝ) ^ α := Nat.floor_le (by positivity)
  have hlog := Real.log_le_log hv0 hfl
  rw [Real.log_rpow hn0] at hlog
  push_cast
  rw [Real.log_mul two_ne_zero hv0.ne', logFactor, Real.log_mul two_ne_zero hn0.ne']
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hln : 0 ≤ Real.log n := Real.log_nonneg hn1
  nlinarith

/-! ### Part 1: Single-conductor eighth-order shell bounds and `7/4` shell decay -/

/-- Pointwise eighth-order bound `O_α(n^(8α - 15) (1 + log(2n)))` for any subquadratic shell `1 < α < 2`. -/
theorem powerProductShell_pointwise_bound {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
      |powerProductShell α n| ≤ C * (n : ℝ) ^ (8 * α - 15) * (1 + Real.log (2 * (n : ℝ))) := by
  obtain ⟨C8, hC8, hshell⟩ := capped_interior_shell_eighth_bound
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (power_shell_geometry hα1 hα2)
  let F := ∑ k ∈ Icc 1 N0, |powerProductShell α k| / ((k : ℝ) ^ (8 * α - 15) * logFactor k)
  have hF0 : 0 ≤ F := sum_nonneg fun k _ => div_nonneg (abs_nonneg _)
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _) (zero_le_one.trans (logFactor_one_le k)))
  let K := F + 2 ^ 8 * C8 * (1 + α)
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ 8 * C8) (by linarith : 0 ≤ 1 + α)]
  refine ⟨K, hK0, fun {n} hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hrpos : 0 < (n : ℝ) ^ (8 * α - 15) * logFactor n :=
    mul_pos (Real.rpow_pos_of_pos hn0 _) (zero_lt_one.trans_le (logFactor_one_le n))
  by_cases hbig : N0 ≤ n
  swap
  · have hle_F : |powerProductShell α n| / ((n : ℝ) ^ (8 * α - 15) * logFactor n) ≤ F :=
      single_le_sum (fun k _ => div_nonneg (abs_nonneg _)
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _) (zero_le_one.trans (logFactor_one_le k))))
        (mem_Icc.mpr ⟨hn, by omega⟩)
    have h1 := (div_le_iff₀ hrpos).mp hle_F
    have hFK : F ≤ K := by
      dsimp only [K]
      linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ 8 * C8) (by linarith : 0 ≤ 1 + α)]
    exact h1.trans ((mul_le_mul_of_nonneg_right hFK hrpos.le).trans_eq (by ring))
  obtain ⟨hv1, hbirth16, hY⟩ := hN0 n hbig
  let V := powerProductCut α n
  have hW1 : 1 ≤ 2 * V := by omega
  have hbirth7 : 7 * ((2 * V : ℕ) : ℝ) < Real.exp (-8) * (n : ℝ) ^ 2 := by
    push_cast; linarith
  have hb := hshell hn hW1 (by omega : V ≤ 2 * V) hbirth7 hY n
  refine hb.trans ?_
  have hfl : (V : ℝ) ≤ (n : ℝ) ^ α := Nat.floor_le (by positivity)
  have hW8 : ((2 * V : ℕ) : ℝ) ^ 8 ≤ 2 ^ 8 * (n : ℝ) ^ (8 * α) := by
    push_cast
    calc (2 * (V : ℝ)) ^ 8 = 2 ^ 8 * (V : ℝ) ^ 8 := by ring
      _ ≤ 2 ^ 8 * ((n : ℝ) ^ α) ^ 8 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg V) hfl 8) (by positivity)
      _ = 2 ^ 8 * (n : ℝ) ^ (8 * α) := by
          rw [← Real.rpow_natCast ((n : ℝ) ^ α) 8, ← Real.rpow_mul hn0.le]; congr 2; ring
  have hlog := log_two_mul_cut_le (by linarith) hn hv1
  have hdiv_eq : (n : ℝ) ^ (8 * α) / (n : ℝ) ^ 15 = (n : ℝ) ^ (8 * α - 15) := by
    rw [← Real.rpow_natCast (n : ℝ) 15, ← Real.rpow_sub hn0]; norm_num
  calc C8 * ((2 * V : ℕ) : ℝ) ^ 8 * (1 + Real.log (2 * V : ℕ)) / (n : ℝ) ^ 15
      ≤ C8 * (2 ^ 8 * (n : ℝ) ^ (8 * α)) * ((1 + α) * logFactor n) / (n : ℝ) ^ 15 := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hW8 hC8) hlog
          (add_nonneg zero_le_one (Real.log_natCast_nonneg _)) (by positivity)
    _ = (2 ^ 8 * C8 * (1 + α)) * ((n : ℝ) ^ (8 * α) / (n : ℝ) ^ 15) * logFactor n := by ring
    _ = (2 ^ 8 * C8 * (1 + α)) * (n : ℝ) ^ (8 * α - 15) * logFactor n := by rw [hdiv_eq]
    _ ≤ K * (n : ℝ) ^ (8 * α - 15) * logFactor n := by
        dsimp only [K]
        nlinarith [mul_nonneg hF0 hrpos.le]

/-- Pointwise decay `|B_n| ≤ C · (1 + log(2n)) / n` on every conductor for the `7/4` shell. -/
theorem sevenFourthsShell_reciprocal_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
      |powerProductShell (7 / 4) n| ≤ C * (1 + Real.log (2 * (n : ℝ))) / (n : ℝ) := by
  obtain ⟨C, hC, h⟩ := powerProductShell_pointwise_bound (α := 7 / 4) (by norm_num) (by norm_num)
  refine ⟨C, hC, fun {n} hn => (h hn).trans_eq ?_⟩
  have hrp : (n : ℝ) ^ (8 * (7 / 4 : ℝ) - 15) = (n : ℝ)⁻¹ := by
    rw [show (8 * (7 / 4 : ℝ) - 15) = -1 by norm_num, Real.rpow_neg_one]
  rw [hrp]; ring

/-- Absolute conductor-octave sum `∑_{N < n ≤ M} n² |B_n| ≤ C · N² · (1 + log(2N))`. -/
theorem sevenFourthsShell_absolute_octave_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N M : ℕ, N ≤ M → M ≤ 2 * N →
      (∑ n ∈ Ioc N M, (n : ℝ) ^ 2 * |powerProductShell (7 / 4) n|) ≤
        C * (N : ℝ) ^ 2 * (1 + Real.log (2 * (N : ℝ))) := by
  obtain ⟨C, hC, h⟩ := sevenFourthsShell_reciprocal_bound
  refine ⟨4 * C, by positivity, fun N M hNM hM2N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hM0 : M = 0 := by omega
    simp [hM0]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hrow : ∀ n ∈ Ioc N M, (n : ℝ) ^ 2 * |powerProductShell (7 / 4) n| ≤
      4 * C * (N : ℝ) * logFactor N := by
    intro n hn
    obtain ⟨hnN, hnM⟩ := mem_Ioc.mp hn
    have hn_pos : 0 < n := hN.trans hnN
    have hn_r : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
    have hn2N : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hnM.trans hM2N
    have hlog : logFactor n ≤ 2 * logFactor N := by
      have hh := Real.log_le_log hn_r hn2N
      rw [Real.log_mul two_ne_zero hN0.ne'] at hh
      simp only [logFactor, Real.log_mul two_ne_zero hn_r.ne', Real.log_mul two_ne_zero hN0.ne']
      linarith [Real.log_nonneg hN1]
    calc (n : ℝ) ^ 2 * |powerProductShell (7 / 4) n|
        ≤ (n : ℝ) ^ 2 * (C * logFactor n / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (h hn_pos) (sq_nonneg _)
      _ = C * (n : ℝ) * logFactor n := by field_simp [hn_r.ne']; ring
      _ ≤ C * (2 * (N : ℝ)) * (2 * logFactor N) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hn2N hC) hlog
            (zero_le_one.trans (logFactor_one_le n)) (by positivity)
      _ = 4 * C * (N : ℝ) * logFactor N := by ring
  calc (∑ n ∈ Ioc N M, (n : ℝ) ^ 2 * |powerProductShell (7 / 4) n|)
      ≤ ∑ _n ∈ Ioc N M, (4 * C * (N : ℝ) * logFactor N) := sum_le_sum hrow
    _ = ((M - N : ℕ) : ℝ) * (4 * C * (N : ℝ) * logFactor N) := by
        rw [sum_const, nsmul_eq_mul, Nat.card_Ioc]
    _ ≤ (N : ℝ) * (4 * C * (N : ℝ) * logFactor N) := by
        refine mul_le_mul_of_nonneg_right (by exact_mod_cast (show M - N ≤ N by omega)) ?_
        have := logFactor_one_le N; positivity
    _ = 4 * C * (N : ℝ) ^ 2 * logFactor N := by ring

/-! ### Part 2: Conductor-smoothed shell savings (`N^(9α - 14)` and `N^(7/4)` on `7/4`) -/

/-- Two-variable conductor-smoothed shell theorem across `3/2 ≤ α < 2`: summing with signs
over `N < n ≤ M ≤ 2N` saves an extra power `N^(2 - α)` beyond the single-conductor knot bound. -/
theorem powerProductShell_conductor_smoothed_bound {α : ℝ} (hα1 : 3 / 2 ≤ α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N M : ℕ, N ≤ M → M ≤ 2 * N →
      |∑ n ∈ Ioc N M, (n : ℝ) ^ 2 * powerProductShell α n| ≤
        C * (N : ℝ) ^ (9 * α - 14) * (1 + Real.log (2 * (N : ℝ))) := by
  obtain ⟨Cs, hCs, hsmooth⟩ := conductor_smoothed_shell_bound
  have hgeom_octave : ∀ᶠ N : ℕ in atTop,
      1 ≤ 2 * powerProductCut α N ∧
      16 * (powerProductCut α (2 * N) : ℝ) < Real.exp (-8) * (N : ℝ) ^ 2 ∧
      ∀ n ∈ Ioc N (2 * N), productLower 1 (splineHorizon n) ≤ powerProductCut α n := by
    obtain ⟨A, hA, hwin⟩ := successorSquare_window_bound
    have ht1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (2 - α)) atTop atTop :=
      (Real.tendsto_rpow_atTop (by linarith : 0 < 2 - α)).comp tendsto_natCast_atTop_atTop
    have ht2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (α - 1)) atTop atTop :=
      (Real.tendsto_rpow_atTop (by linarith : 0 < α - 1)).comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      ht1.eventually_ge_atTop (17 * (2 : ℝ) ^ α * Real.exp 8),
      ht2.eventually_ge_atTop (2 * A + 1)] with N hN hhi hlo
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
    have hcut1 : 1 ≤ powerProductCut α N :=
      (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hN1 (by linarith))
    refine ⟨by omega, ?_, fun n hn => ?_⟩
    · have hfl : (powerProductCut α (2 * N) : ℝ) ≤ ((2 * N : ℕ) : ℝ) ^ α :=
        Nat.floor_le (by positivity)
      have h2N : ((2 * N : ℕ) : ℝ) ^ α = (2 : ℝ) ^ α * (N : ℝ) ^ α := by
        push_cast; exact Real.mul_rpow (by norm_num) hN0.le
      have hmul : (N : ℝ) ^ α * (N : ℝ) ^ (2 - α) = (N : ℝ) ^ 2 := by
        rw [← Real.rpow_add hN0, add_sub_cancel, Real.rpow_two]
      have hgap : 16 * (2 : ℝ) ^ α < Real.exp (-8) * (N : ℝ) ^ (2 - α) := by
        rw [Real.exp_neg, inv_mul_eq_div, lt_div_iff₀ (Real.exp_pos 8)]
        exact (by nlinarith [Real.exp_pos 8, Real.rpow_pos_of_pos two_pos α] :
          16 * (2 : ℝ) ^ α * Real.exp 8 < 17 * (2 : ℝ) ^ α * Real.exp 8).trans_le hhi
      have hh := mul_lt_mul_of_pos_right hgap (Real.rpow_pos_of_pos hN0 α)
      rw [mul_assoc (Real.exp (-8)), mul_comm ((N : ℝ) ^ (2 - α)), hmul] at hh
      rw [h2N] at hfl
      nlinarith [hfl]
    · obtain ⟨hnN, _⟩ := mem_Ioc.mp hn
      have hn0_nat : 0 < n := hN.trans hnN
      have hn1_r : (1 : ℝ) ≤ n := by exact_mod_cast hn0_nat
      have hn0_r : (0 : ℝ) < n := zero_lt_one.trans_le hn1_r
      apply Nat.le_floor
      have hlo_n : 2 * A + 1 ≤ (n : ℝ) ^ (α - 1) :=
        hlo.trans (Real.rpow_le_rpow hN0.le (by exact_mod_cast hnN.le) (by linarith))
      have hmul : (n : ℝ) ^ (α - 1) * n = (n : ℝ) ^ α := by
        rw [← Real.rpow_one (n : ℝ), ← Real.rpow_add hn0_r]; congr 1; ring
      have hroot : Real.sqrt (splineHorizon n) ≤ A * n := by
        have hs := Real.sqrt_le_sqrt (hwin hn0_nat)
        rwa [Real.sqrt_sq (mul_nonneg (zero_le_one.trans hA) hn0_r.le)] at hs
      have hpl : (productLower 1 (splineHorizon n) : ℝ) ≤ 2 * Real.sqrt (splineHorizon n) := by
        refine (Nat.cast_le.mpr (min_le_right _ _)).trans ?_
        push_cast
        exact mul_le_mul_of_nonneg_left (Nat.floor_le (Real.sqrt_nonneg _)) (by norm_num)
      calc (productLower 1 (splineHorizon n) : ℝ)
          ≤ 2 * (A * n) := hpl.trans (mul_le_mul_of_nonneg_left hroot (by norm_num))
        _ ≤ (n : ℝ) ^ (α - 1) * n := by nlinarith [hlo_n, hn0_r.le]
        _ = (n : ℝ) ^ α := hmul
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hgeom_octave
  let F := ∑ k ∈ Icc 1 (2 * N0), (k : ℝ) ^ 2 * |powerProductShell α k|
  have hF0 : 0 ≤ F := sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (abs_nonneg _)
  let A_const := Cs * (2 * (1 + α)) * (3 * (2 : ℝ) ^ (9 * (1 + α)))
  have hA_nonneg : 0 ≤ A_const := by
    dsimp only [A_const]
    have : 0 ≤ 1 + α := by linarith
    positivity
  let K := F + A_const
  refine ⟨K, add_nonneg hF0 hA_nonneg, fun N M hNM hM2N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hM0 : M = 0 := by omega
    rw [hM0, Ioc_self, sum_empty, abs_zero]
    exact mul_nonneg (mul_nonneg (add_nonneg hF0 hA_nonneg) (Real.rpow_nonneg zero_le_zero _))
      (zero_le_one.trans (logFactor_one_le 0))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0_r : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hrge1 : 1 ≤ (N : ℝ) ^ (9 * α - 14) * logFactor N := by
    refine one_le_mul_of_one_le_of_one_le ?_ (logFactor_one_le N)
    exact Real.one_le_rpow hN1 (by linarith)
  by_cases hbig : N0 ≤ N
  swap
  · have hsub : Ioc N M ⊆ Icc 1 (2 * N0) := fun n hn => by
      obtain ⟨h1, h2⟩ := mem_Ioc.mp hn
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    have hfin : |∑ n ∈ Ioc N M, (n : ℝ) ^ 2 * powerProductShell α n| ≤ F := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have heq_abs : ∀ n, |(n : ℝ) ^ 2 * powerProductShell α n| =
          (n : ℝ) ^ 2 * |powerProductShell α n| :=
        fun n => by rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      simp_rw [heq_abs]
      exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => mul_nonneg (sq_nonneg _) (abs_nonneg _)
    calc |∑ n ∈ Ioc N M, (n : ℝ) ^ 2 * powerProductShell α n|
        ≤ F := hfin
      _ ≤ K * ((N : ℝ) ^ (9 * α - 14) * logFactor N) := by
          dsimp only [K]; nlinarith [hrge1]
      _ = K * (N : ℝ) ^ (9 * α - 14) * logFactor N := by ring
  obtain ⟨hw1_N, hbirth16, hY_all⟩ := hN0 N hbig
  let u := powerProductCut α
  let w := fun n : ℕ => 2 * powerProductCut α n
  have hu_mono : Monotone u := monotone_powerProductCut (by linarith)
  have hw_mono : Monotone w := fun _ _ hmn => Nat.mul_le_mul_left 2 (hu_mono hmn)
  have hwM_pos : 1 ≤ w M := hw1_N.trans (hw_mono hNM)
  have hwM_le : w M ≤ w (2 * N) := hw_mono hM2N
  have hbirth8 : 8 * (w M : ℝ) < Real.exp (-8) * (N : ℝ) ^ 2 := by
    have : (w M : ℝ) ≤ 2 * (powerProductCut α (2 * N) : ℝ) := by
      dsimp only [w] at hwM_le ⊢; exact_mod_cast hwM_le
    linarith
  have hmain := hsmooth hu_mono hw_mono hN hNM hM2N hwM_pos hbirth8
    fun n hn => ⟨hY_all n (Ioc_subset_Ioc_right hM2N hn), by dsimp only [u, w]; omega⟩
  refine hmain.trans ?_
  have hwM_bound : (w M : ℝ) ≤ (2 : ℝ) ^ (1 + α) * (N : ℝ) ^ α := by
    have h1 : (w M : ℝ) ≤ 2 * (((2 * N : ℕ) : ℝ) ^ α) := by
      have hfl : (powerProductCut α (2 * N) : ℝ) ≤ ((2 * N : ℕ) : ℝ) ^ α :=
        Nat.floor_le (by positivity)
      have hle' : (w M : ℝ) ≤ 2 * (powerProductCut α (2 * N) : ℝ) := by
        dsimp only [w] at hwM_le ⊢; exact_mod_cast hwM_le
      linarith
    have h2 : 2 * (((2 * N : ℕ) : ℝ) ^ α) = (2 : ℝ) ^ (1 + α) * (N : ℝ) ^ α := by
      push_cast
      rw [Real.mul_rpow (by norm_num) hN0_r.le, Real.rpow_add two_pos, Real.rpow_one]
      ring
    linarith
  have hlogW : 1 + Real.log (w M) ≤ 2 * (1 + α) * logFactor N := by
    have hle1 : 1 + Real.log (w M) ≤ 1 + Real.log (w (2 * N)) :=
      add_le_add le_rfl (Real.log_le_log (by exact_mod_cast hwM_pos) (by exact_mod_cast hwM_le))
    have h2N_pos : 0 < 2 * N := by omega
    have hcut_2N : 1 ≤ powerProductCut α (2 * N) := by
      have : 1 ≤ powerProductCut α N := by omega
      exact this.trans (hu_mono (by omega : N ≤ 2 * N))
    have hle2 := log_two_mul_cut_le (by linarith) h2N_pos hcut_2N
    have hcond_2N : logFactor (2 * N) ≤ 2 * logFactor N := by
      dsimp only [logFactor]
      push_cast
      rw [Real.log_mul two_ne_zero (by positivity), Real.log_mul two_ne_zero hN0_r.ne',
        Real.log_mul two_ne_zero hN0_r.ne']
      linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2), Real.log_nonneg hN1]
    have : 0 ≤ 1 + α := by linarith
    nlinarith
  have hpow_term (m k : ℕ) (hm : m ≤ 9) (hexp : (9 * α - 14) ≥ (m : ℝ) * α - k) :
      (w M : ℝ) ^ m / (N : ℝ) ^ k ≤ (2 : ℝ) ^ (9 * (1 + α)) * (N : ℝ) ^ (9 * α - 14) := by
    have hm_le : (m : ℝ) * (1 + α) ≤ 9 * (1 + α) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hm) (by linarith)
    have h2pow : ((2 : ℝ) ^ (1 + α)) ^ m ≤ (2 : ℝ) ^ (9 * (1 + α)) := by
      rw [← Real.rpow_natCast _ m, ← Real.rpow_mul two_pos.le, mul_comm (1 + α)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hm_le
    have hNpow : ((N : ℝ) ^ α) ^ m / (N : ℝ) ^ k ≤ (N : ℝ) ^ (9 * α - 14) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ α) m, ← Real.rpow_mul hN0_r.le,
        ← Real.rpow_natCast (N : ℝ) k, ← Real.rpow_sub hN0_r, mul_comm α]
      exact Real.rpow_le_rpow_of_exponent_le hN1 hexp
    calc (w M : ℝ) ^ m / (N : ℝ) ^ k
        ≤ ((2 : ℝ) ^ (1 + α) * (N : ℝ) ^ α) ^ m / (N : ℝ) ^ k :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hwM_bound m) (by positivity)
      _ = ((2 : ℝ) ^ (1 + α)) ^ m * (((N : ℝ) ^ α) ^ m / (N : ℝ) ^ k) := by
          rw [mul_pow]; ring
      _ ≤ (2 : ℝ) ^ (9 * (1 + α)) * (N : ℝ) ^ (9 * α - 14) :=
          mul_le_mul h2pow hNpow (by positivity) (by positivity)
  have ht9 := hpow_term 9 14 le_rfl (by push_cast; linarith)
  have ht8 := hpow_term 8 13 (by decide) (by push_cast; linarith)
  have ht5 := hpow_term 5 8 (by decide) (by push_cast; linarith)
  have hsum3 : (w M : ℝ) ^ 9 / (N : ℝ) ^ 14 + (w M : ℝ) ^ 8 / (N : ℝ) ^ 13 +
      (w M : ℝ) ^ 5 / (N : ℝ) ^ 8 ≤ 3 * (2 : ℝ) ^ (9 * (1 + α)) * (N : ℝ) ^ (9 * α - 14) := by
    linarith
  calc Cs * (1 + Real.log (w M)) *
        ((w M : ℝ) ^ 9 / (N : ℝ) ^ 14 + (w M : ℝ) ^ 8 / (N : ℝ) ^ 13 +
          (w M : ℝ) ^ 5 / (N : ℝ) ^ 8)
      ≤ Cs * (2 * (1 + α) * logFactor N) *
          (3 * (2 : ℝ) ^ (9 * (1 + α)) * (N : ℝ) ^ (9 * α - 14)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hlogW hCs) hsum3 (by positivity) ?_
        have := logFactor_one_le N; have : 0 ≤ 1 + α := by linarith; positivity
    _ = A_const * (N : ℝ) ^ (9 * α - 14) * logFactor N := by dsimp only [A_const]; ring
    _ ≤ K * (N : ℝ) ^ (9 * α - 14) * logFactor N := by
        dsimp only [K]
        have hrp_nn : 0 ≤ (N : ℝ) ^ (9 * α - 14) := Real.rpow_nonneg hN0_r.le (9 * α - 14)
        have hlf_nn : 0 ≤ logFactor N := zero_le_one.trans (logFactor_one_le N)
        nlinarith [mul_nonneg hF0 (mul_nonneg hrp_nn hlf_nn)]

/-- Complete conductor-smoothed bound `O(N^(7/4) (1 + log(2N)))` on the `7/4` shell across
every partial or complete conductor octave `N ≤ M ≤ 2N`. -/
theorem sevenFourthsShell_conductor_smoothed_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N M : ℕ, N ≤ M → M ≤ 2 * N →
      |∑ n ∈ Ioc N M, (n : ℝ) ^ 2 * powerProductShell (7 / 4) n| ≤
        C * (N : ℝ) ^ (7 / 4 : ℝ) * (1 + Real.log (2 * (N : ℝ))) := by
  obtain ⟨C, hC, h⟩ := powerProductShell_conductor_smoothed_bound (α := 7 / 4)
    (by norm_num) (by norm_num)
  refine ⟨C, hC, fun N M hNM hM2N => ?_⟩
  have heq : (9 * (7 / 4 : ℝ) - 14) = 7 / 4 := by norm_num
  simpa only [heq] using h N M hNM hM2N

/-- Direct resolution on the complete dyadic octave `N < n ≤ 2N` with `O(N^(7/4) (1 + log(2N)))`. -/
theorem sevenFourthsShell_dyadic_octave_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |∑ n ∈ Ioc N (2 * N), (n : ℝ) ^ 2 * powerProductShell (7 / 4) n| ≤
        C * (N : ℝ) ^ (7 / 4 : ℝ) * (1 + Real.log (2 * (N : ℝ))) := by
  obtain ⟨C, hC, h⟩ := sevenFourthsShell_conductor_smoothed_bound
  exact ⟨C, hC, fun N => h N (2 * N) (Nat.le_mul_of_pos_left N two_pos) le_rfl⟩

/-- Uniform power saving `O_δ(N^(7/2 - δ))` for every `δ < 7/4` across all `N ≤ M ≤ 2N`. -/
theorem sevenFourthsShell_saving_below_seven_fourths {δ : ℝ} (hδ : δ < 7 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N M : ℕ, N ≤ M → M ≤ 2 * N →
      |∑ n ∈ Ioc N M, (n : ℝ) ^ 2 * powerProductShell (7 / 4) n| ≤
        C * (N : ℝ) ^ (7 / 2 - δ) := by
  obtain ⟨C, hC, h⟩ := sevenFourthsShell_conductor_smoothed_bound
  obtain ⟨B, hB, hlog⟩ := logFactor_pow_subpower (show 0 < (7 / 4 : ℝ) - δ by linarith)
  refine ⟨C * B, mul_nonneg hC hB, fun N M hNM hM2N => (h N M hNM hM2N).trans ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [Real.zero_rpow (by linarith : (7 / 4 : ℝ) ≠ 0),
      Real.zero_rpow (by linarith : (7 / 2 - δ) ≠ 0)]
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h1 : logFactor N ≤ B * (N : ℝ) ^ ((7 / 4 : ℝ) - δ) :=
    (le_self_pow₀ (logFactor_one_le N) (by decide : 6 ≠ 0)).trans (hlog hN)
  calc C * (N : ℝ) ^ (7 / 4 : ℝ) * logFactor N
      ≤ C * (N : ℝ) ^ (7 / 4 : ℝ) * (B * (N : ℝ) ^ ((7 / 4 : ℝ) - δ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = C * B * ((N : ℝ) ^ (7 / 4 : ℝ) * (N : ℝ) ^ ((7 / 4 : ℝ) - δ)) := by ring
    _ = C * B * (N : ℝ) ^ (7 / 2 - δ) := by
        rw [← Real.rpow_add hN0]; congr 2; ring

/-- Parameter-free specialization at explicit saving `δ = 13/8 > 0` (`N^(15/8)`). -/
theorem sevenFourthsShell_thirteen_eighths_saving :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N M : ℕ, N ≤ M → M ≤ 2 * N →
      |∑ n ∈ Ioc N M, (n : ℝ) ^ 2 * powerProductShell (7 / 4) n| ≤
        C * (N : ℝ) ^ (7 / 2 - 13 / 8 : ℝ) :=
  sevenFourthsShell_saving_below_seven_fourths (by norm_num)

/-! ### Part 3: The fifteen-sixteenths cutoff and seventeen-eighteenths prefix for RH -/

/-- Every product up to `⌊n^(15/8)⌋` is paid within six logarithms on each conductor. -/
theorem dyadicPrimeContact_fifteenSixteenthsConductor :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
      |dyadicPrimeContact n - fifteenSixteenthsConductor n| ≤
        C * (1 + Real.log (2 * (n : ℝ))) ^ 6 := by
  obtain ⟨A, B, C, hA, hB, hC, h⟩ := dyadicPrimeContact_capped_eighth_product_tail
  obtain ⟨K, hK, hwin⟩ := successorSquare_window_bound
  let J := 3 + 2 * Real.log K
  have hklog := Real.log_nonneg hK
  have hj : 0 ≤ J := by dsimp only [J]; positivity
  refine ⟨A * J ^ 6 + 3 * B + C * J, by positivity, fun {n} hn => ?_⟩
  let L := splineHorizon n
  let U := fifteenSixteenthsCut n
  let H := logFactor n
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK' : 0 < K := zero_lt_one.trans_le hK
  have hH1 : 1 ≤ H := logFactor_one_le n
  have hH0 : 0 ≤ H := zero_le_one.trans hH1
  have hL0 : (0 : ℝ) < L := by
    obtain ⟨_, h1, h2⟩ := successorSquareWindowScale_bounds n
    have hp : (0 : ℝ) < windowEnd ((2 * n + 1) ^ 2 + 1) :=
      (by norm_num : (0 : ℝ) < 9).trans_le (h1.trans h2)
    dsimp only [L, splineHorizon]; push_cast; positivity
  have hlogn : Real.log n ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log hn' (by linarith)
  have hL : 1 + Real.log L ≤ J * H := by
    have hb := Real.log_le_log hL0 (hwin hn)
    rw [Real.log_pow, Real.log_mul hK'.ne' hn'.ne'] at hb
    have hh := le_mul_of_one_le_right hklog hH1
    dsimp only [H, logFactor, J] at hh ⊢
    linarith [hb, hh, hlogn, Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * n)]
  have hU1 : 1 ≤ U := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hn1 (by norm_num))
  have hU_fl : (U : ℝ) ≤ (n : ℝ) ^ (15 / 8 : ℝ) := Nat.floor_le (by positivity)
  have hU_sq : (U : ℝ) ≤ (n : ℝ) ^ 2 :=
    hU_fl.trans ((Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (15 / 8 : ℝ) ≤ 2)).trans_eq
      (Real.rpow_two _))
  have huLog : 1 + Real.log U ≤ 3 * H := by
    have hu := Real.log_le_log (by exact_mod_cast hU1 : (0 : ℝ) < U) hU_sq
    rw [Real.log_pow] at hu; dsimp only [H, logFactor]
    linarith [hu, hlogn, Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * n)]
  have hu8 : (U : ℝ) ^ 8 ≤ (n : ℝ) ^ 15 := by
    calc (U : ℝ) ^ 8 ≤ ((n : ℝ) ^ (15 / 8 : ℝ)) ^ 8 :=
          pow_le_pow_left₀ (Nat.cast_nonneg U) hU_fl 8
      _ = (n : ℝ) ^ 15 := by
          rw [← Real.rpow_natCast _ 8, ← Real.rpow_mul hn'.le, ← Real.rpow_natCast (n : ℝ) 15]
          congr 1; norm_num
  have hfirst := pow_le_pow_left₀ (add_nonneg zero_le_one (Real.log_natCast_nonneg L)) hL 6
  rw [mul_pow] at hfirst
  have hmid : B * (1 + Real.log U) * (U : ℝ) ^ 8 / (n : ℝ) ^ 15 ≤ 3 * B * H := by
    rw [div_le_iff₀ (pow_pos hn' 15)]
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left huLog hB) hu8 (pow_nonneg (Nat.cast_nonneg U) 8)
      (by positivity)
    linarith
  have hlast : C * n * (1 + Real.log L) / (n + 1 : ℕ) ≤ C * J * H := by
    rw [div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos n))]
    have hh := mul_le_mul_of_nonneg_left hL (mul_nonneg hC hn'.le)
    push_cast
    linarith [hh, mul_nonneg (mul_nonneg hC hj) hH0]
  refine (h hn hU1 n).trans ?_
  have hh := le_self_pow₀ hH1 (by decide : 6 ≠ 0)
  change A * (1 + Real.log L) ^ 6 + _ + _ ≤ (A * J ^ 6 + 3 * B + C * J) * H ^ 6
  linarith [mul_le_mul_of_nonneg_left hfirst hA, hmid, hlast,
    mul_le_mul_of_nonneg_left hh (show 0 ≤ 3 * B by positivity),
    mul_le_mul_of_nonneg_left hh (mul_nonneg hC hj)]

/-- Prefix approximation at the single-conductor paid cutoff `⌊n^(15/8)⌋`. -/
theorem squareGeneratorPrefix_fifteenSixteenths_products :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |Real.log (squareGeneratorPrefix N : ℝ) - fifteenSixteenthsConductorPrefix N| ≤
        C * (N : ℝ) ^ 3 * (1 + Real.log (2 * (N : ℝ))) ^ 6 := by
  obtain ⟨A, hA, ha⟩ := successorSquare_contact_error
  obtain ⟨B, hB, hb⟩ := dyadicPrimeContact_error
  obtain ⟨C, hC, hc⟩ := dyadicPrimeContact_fifteenSixteenthsConductor
  let K := A + B + C
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, fun N => ?_⟩
  have hgen_log : Real.log (squareGeneratorPrefix N : ℝ) =
      ∑ n ∈ Icc 1 N, Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n) : ℝ) := by
    rw [show Icc 1 N = Ioc 0 N by ext k; simp only [mem_Icc, mem_Ioc]; omega, squareGeneratorPrefix]
    push_cast
    apply Real.log_prod
    intro n _
    exact ne_of_gt (by exact_mod_cast (show (0 : ℚ) <
      ordinaryPrimeGenerator (n • successorSquareTriple n) from
        prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _))
  rw [hgen_log, fifteenSixteenthsConductorPrefix, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hnrow (n : ℕ) (hn : n ∈ Icc 1 N) :
      |Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n) : ℝ) -
          (n : ℝ) ^ 2 * fifteenSixteenthsConductor n| ≤ K * (N : ℝ) ^ 2 * (logFactor N) ^ 6 := by
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    let P := ordinaryPrimeContact (successorSquareTriple n)
    let D := dyadicPrimeContact n
    have he : Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n) : ℝ) -
        (n : ℝ) ^ 2 * fifteenSixteenthsConductor n =
        (Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n) : ℝ) - (n : ℝ) ^ 2 * P) +
        (n : ℝ) ^ 2 * (P - D) + (n : ℝ) ^ 2 * (D - fifteenSixteenthsConductor n) := by ring
    rw [he]
    refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
    simp only [abs_mul, abs_of_nonneg (sq_nonneg (n : ℝ))]
    have hv := one_le_pow₀ (n := 6) (logFactor_one_le n)
    have hs := mul_le_mul_of_nonneg_left (hb hn1) (sq_nonneg (n : ℝ))
    have ht := mul_le_mul_of_nonneg_left (hc hn1) (sq_nonneg (n : ℝ))
    have hlocal : |Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n) : ℝ) -
          (n : ℝ) ^ 2 * P| + (n : ℝ) ^ 2 * |P - D| +
        (n : ℝ) ^ 2 * |D - fifteenSixteenthsConductor n| ≤ K * (n : ℝ) ^ 2 * (logFactor n) ^ 6 := by
      dsimp only [P, D, K, logFactor] at *
      linarith only [ha hn1 le_rfl, hs, ht,
        le_mul_of_one_le_right (mul_nonneg (add_nonneg hA hB) (sq_nonneg (n : ℝ))) hv]
    exact hlocal.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg n) (Nat.cast_le.mpr hnN) 2) hK)
      (pow_le_pow_left₀ (zero_le_one.trans (logFactor_one_le n)) (logFactor_mono hn1 hnN) 6)
      (by positivity) (by positivity))
  refine (sum_le_sum hnrow).trans_eq ?_
  rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
  ring

private theorem bridge_octave_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N M : ℕ, N ≤ M → M ≤ 2 * N →
      |∑ n ∈ Ioc N M, (n : ℝ) ^ 2 *
          (fifteenSixteenthsConductor n - seventeenNinthsConductor n)| ≤
        C * (N : ℝ) ^ 3 * (1 + Real.log (2 * (N : ℝ))) := by
  obtain ⟨Cs, hCs, hsmooth⟩ := conductor_smoothed_shell_bound
  have hgeom : ∀ᶠ N : ℕ in atTop,
      1 ≤ seventeenNinthsCut N ∧
      8 * (seventeenNinthsCut (2 * N) : ℝ) < Real.exp (-8) * (N : ℝ) ^ 2 ∧
      ∀ n ∈ Ioc N (2 * N),
        productLower 1 (splineHorizon n) ≤ fifteenSixteenthsCut n ∧
          fifteenSixteenthsCut n ≤ seventeenNinthsCut n := by
    obtain ⟨A, hA, hwin⟩ := successorSquare_window_bound
    have ht1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 9 : ℝ)) atTop atTop :=
      (Real.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 9)).comp tendsto_natCast_atTop_atTop
    have ht2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (7 / 8 : ℝ)) atTop atTop :=
      (Real.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 8)).comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      ht1.eventually_ge_atTop (9 * (2 : ℝ) ^ (17 / 9 : ℝ) * Real.exp 8),
      ht2.eventually_ge_atTop (2 * A + 1)] with N hN hhi hlo
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
    refine ⟨(Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hN1 (by norm_num)), ?_, fun n hn => ?_⟩
    · have hfl : (seventeenNinthsCut (2 * N) : ℝ) ≤ ((2 * N : ℕ) : ℝ) ^ (17 / 9 : ℝ) :=
        Nat.floor_le (by positivity)
      have h2N : ((2 * N : ℕ) : ℝ) ^ (17 / 9 : ℝ) = (2 : ℝ) ^ (17 / 9 : ℝ) * (N : ℝ) ^ (17 / 9 : ℝ) := by
        push_cast; exact Real.mul_rpow (by norm_num) hN0.le
      have hmul : (N : ℝ) ^ (17 / 9 : ℝ) * (N : ℝ) ^ (1 / 9 : ℝ) = (N : ℝ) ^ 2 := by
        rw [← Real.rpow_add hN0, show (17 / 9 : ℝ) + 1 / 9 = 2 by norm_num, Real.rpow_two]
      have hgap : 8 * (2 : ℝ) ^ (17 / 9 : ℝ) < Real.exp (-8) * (N : ℝ) ^ (1 / 9 : ℝ) := by
        rw [Real.exp_neg, inv_mul_eq_div, lt_div_iff₀ (Real.exp_pos 8)]
        exact (by nlinarith [Real.exp_pos 8, Real.rpow_pos_of_pos two_pos (17 / 9 : ℝ)] :
          8 * (2 : ℝ) ^ (17 / 9 : ℝ) * Real.exp 8 <
            9 * (2 : ℝ) ^ (17 / 9 : ℝ) * Real.exp 8).trans_le hhi
      have hh := mul_lt_mul_of_pos_right hgap (Real.rpow_pos_of_pos hN0 (17 / 9 : ℝ))
      rw [mul_assoc (Real.exp (-8)), mul_comm ((N : ℝ) ^ (1 / 9 : ℝ)), hmul] at hh
      rw [h2N] at hfl
      nlinarith [hfl]
    · obtain ⟨hnN, _⟩ := mem_Ioc.mp hn
      have hn0_nat : 0 < n := hN.trans hnN
      have hn1_r : (1 : ℝ) ≤ n := by exact_mod_cast hn0_nat
      have hn0_r : (0 : ℝ) < n := zero_lt_one.trans_le hn1_r
      refine ⟨?_, Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hn1_r (by norm_num))⟩
      apply Nat.le_floor
      have hlo_n : 2 * A + 1 ≤ (n : ℝ) ^ (7 / 8 : ℝ) :=
        hlo.trans (Real.rpow_le_rpow hN0.le (by exact_mod_cast hnN.le) (by norm_num))
      have hmul : (n : ℝ) ^ (7 / 8 : ℝ) * n = (n : ℝ) ^ (15 / 8 : ℝ) := by
        rw [← Real.rpow_one (n : ℝ), ← Real.rpow_add hn0_r]; congr 1; norm_num
      have hroot : Real.sqrt (splineHorizon n) ≤ A * n := by
        have hs := Real.sqrt_le_sqrt (hwin hn0_nat)
        rwa [Real.sqrt_sq (mul_nonneg (zero_le_one.trans hA) hn0_r.le)] at hs
      have hpl : (productLower 1 (splineHorizon n) : ℝ) ≤ 2 * Real.sqrt (splineHorizon n) := by
        refine (Nat.cast_le.mpr (min_le_right _ _)).trans ?_
        push_cast
        exact mul_le_mul_of_nonneg_left (Nat.floor_le (Real.sqrt_nonneg _)) (by norm_num)
      calc (productLower 1 (splineHorizon n) : ℝ)
          ≤ 2 * (A * n) := hpl.trans (mul_le_mul_of_nonneg_left hroot (by norm_num))
        _ ≤ (n : ℝ) ^ (7 / 8 : ℝ) * n := by nlinarith [hlo_n, hn0_r.le]
        _ = (n : ℝ) ^ (15 / 8 : ℝ) := hmul
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hgeom
  let diff1 := fun k : ℕ => fifteenSixteenthsConductor k - seventeenNinthsConductor k
  let F := ∑ k ∈ Icc 1 (2 * N0), (k : ℝ) ^ 2 * |diff1 k|
  have hF0 : 0 ≤ F := sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (abs_nonneg _)
  let A_const := Cs * 8 * (3 * (2 : ℝ) ^ 17)
  have hA0 : 0 ≤ A_const := by dsimp only [A_const]; positivity
  refine ⟨F + A_const, add_nonneg hF0 hA0, fun N M hNM hM2N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hM0 : M = 0 := by omega
    simp [hM0]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0_r : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  by_cases hbig : N0 ≤ N
  swap
  · have hsub : Ioc N M ⊆ Icc 1 (2 * N0) := fun n hn => by
      obtain ⟨h1, h2⟩ := mem_Ioc.mp hn; exact mem_Icc.mpr ⟨by omega, by omega⟩
    have hfin : |∑ n ∈ Ioc N M, (n : ℝ) ^ 2 * diff1 n| ≤ F := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have heq_abs : ∀ n, |(n : ℝ) ^ 2 * diff1 n| = (n : ℝ) ^ 2 * |diff1 n| :=
        fun n => by rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      simp_rw [heq_abs]
      exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => mul_nonneg (sq_nonneg _) (abs_nonneg _)
    have hr1 : 1 ≤ (N : ℝ) ^ 3 * logFactor N :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN1) (logFactor_one_le N)
    exact hfin.trans (by nlinarith [hr1, hA0])
  obtain ⟨hw1_N, hbirth8_2N, hgeom_n⟩ := hN0 N hbig
  have hu_mono : Monotone fifteenSixteenthsCut := monotone_powerProductCut (by norm_num)
  have hw_mono : Monotone seventeenNinthsCut := monotone_powerProductCut (by norm_num)
  have hwM1 : 1 ≤ seventeenNinthsCut M := hw1_N.trans (hw_mono hNM)
  have hwM_le : seventeenNinthsCut M ≤ seventeenNinthsCut (2 * N) := hw_mono hM2N
  have hbirth8 : 8 * (seventeenNinthsCut M : ℝ) < Real.exp (-8) * (N : ℝ) ^ 2 := by
    have : (seventeenNinthsCut M : ℝ) ≤ seventeenNinthsCut (2 * N) := by exact_mod_cast hwM_le
    linarith
  have hmain := hsmooth hu_mono hw_mono hN hNM hM2N hwM1 hbirth8
    fun n hn => hgeom_n n (Ioc_subset_Ioc_right hM2N hn)
  refine hmain.trans ?_
  have hwM_bound : (seventeenNinthsCut M : ℝ) ≤ (2 : ℝ) ^ (17 / 9 : ℝ) * (N : ℝ) ^ (17 / 9 : ℝ) := by
    have h1 : (seventeenNinthsCut M : ℝ) ≤ ((2 * N : ℕ) : ℝ) ^ (17 / 9 : ℝ) :=
      (Nat.cast_le.mpr hwM_le).trans (Nat.floor_le (by positivity))
    exact h1.trans_eq (by push_cast; exact Real.mul_rpow (by norm_num) hN0_r.le)
  have hlogW : 1 + Real.log (seventeenNinthsCut M) ≤ 8 * logFactor N := by
    have hw_sq : (seventeenNinthsCut M : ℝ) ≤ (2 * (N : ℝ)) ^ 2 := by
      have hfl : (seventeenNinthsCut M : ℝ) ≤ ((2 * N : ℕ) : ℝ) ^ (17 / 9 : ℝ) :=
        (Nat.cast_le.mpr hwM_le).trans (Nat.floor_le (by positivity))
      have h2N1 : (1 : ℝ) ≤ (2 * N : ℕ) := by push_cast; linarith
      refine hfl.trans ((Real.rpow_le_rpow_of_exponent_le h2N1 (by norm_num : (17 / 9 : ℝ) ≤ 2)).trans_eq ?_)
      push_cast; exact Real.rpow_two _
    have hlog := Real.log_le_log (by exact_mod_cast hwM1) hw_sq
    rw [Real.log_pow] at hlog
    dsimp only [logFactor]
    linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * N)]
  have ht9 : (seventeenNinthsCut M : ℝ) ^ 9 / (N : ℝ) ^ 14 ≤ (2 : ℝ) ^ 17 * (N : ℝ) ^ 3 := by
    calc (seventeenNinthsCut M : ℝ) ^ 9 / (N : ℝ) ^ 14
        ≤ ((2 : ℝ) ^ (17 / 9 : ℝ) * (N : ℝ) ^ (17 / 9 : ℝ)) ^ 9 / (N : ℝ) ^ 14 :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hwM_bound 9) (by positivity)
      _ = ((2 : ℝ) ^ (17 / 9 : ℝ)) ^ 9 * (((N : ℝ) ^ (17 / 9 : ℝ)) ^ 9 / (N : ℝ) ^ 14) := by
          rw [mul_pow]; ring
      _ = (2 : ℝ) ^ 17 * (N : ℝ) ^ 3 := by
          have h2 : ((2 : ℝ) ^ (17 / 9 : ℝ)) ^ 9 = (2 : ℝ) ^ 17 := by
            rw [← Real.rpow_natCast _ 9, ← Real.rpow_mul two_pos.le, ← Real.rpow_natCast 2 17]
            congr 1; norm_num
          have hNp : ((N : ℝ) ^ (17 / 9 : ℝ)) ^ 9 = (N : ℝ) ^ 17 := by
            rw [← Real.rpow_natCast _ 9, ← Real.rpow_mul hN0_r.le, ← Real.rpow_natCast (N : ℝ) 17]
            congr 1; norm_num
          rw [h2, hNp]; field_simp [hN0_r.ne']; ring
  have ht8 : (seventeenNinthsCut M : ℝ) ^ 8 / (N : ℝ) ^ 13 ≤ (2 : ℝ) ^ 17 * (N : ℝ) ^ 3 := by
    have h2 : ((2 : ℝ) ^ (17 / 9 : ℝ)) ^ 8 ≤ (2 : ℝ) ^ 17 := by
      rw [← Real.rpow_natCast _ 8, ← Real.rpow_mul two_pos.le, ← Real.rpow_natCast 2 17]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hNp : ((N : ℝ) ^ (17 / 9 : ℝ)) ^ 8 / (N : ℝ) ^ 13 ≤ (N : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast _ 8, ← Real.rpow_mul hN0_r.le, ← Real.rpow_natCast (N : ℝ) 13,
        ← Real.rpow_sub hN0_r, ← Real.rpow_natCast (N : ℝ) 3]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    calc (seventeenNinthsCut M : ℝ) ^ 8 / (N : ℝ) ^ 13
        ≤ ((2 : ℝ) ^ (17 / 9 : ℝ) * (N : ℝ) ^ (17 / 9 : ℝ)) ^ 8 / (N : ℝ) ^ 13 :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hwM_bound 8) (by positivity)
      _ = ((2 : ℝ) ^ (17 / 9 : ℝ)) ^ 8 * (((N : ℝ) ^ (17 / 9 : ℝ)) ^ 8 / (N : ℝ) ^ 13) := by
          rw [mul_pow]; ring
      _ ≤ (2 : ℝ) ^ 17 * (N : ℝ) ^ 3 := mul_le_mul h2 hNp (by positivity) (by positivity)
  have ht5 : (seventeenNinthsCut M : ℝ) ^ 5 / (N : ℝ) ^ 8 ≤ (2 : ℝ) ^ 17 * (N : ℝ) ^ 3 := by
    have h2 : ((2 : ℝ) ^ (17 / 9 : ℝ)) ^ 5 ≤ (2 : ℝ) ^ 17 := by
      rw [← Real.rpow_natCast _ 5, ← Real.rpow_mul two_pos.le, ← Real.rpow_natCast 2 17]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hNp : ((N : ℝ) ^ (17 / 9 : ℝ)) ^ 5 / (N : ℝ) ^ 8 ≤ (N : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast _ 5, ← Real.rpow_mul hN0_r.le, ← Real.rpow_natCast (N : ℝ) 8,
        ← Real.rpow_sub hN0_r, ← Real.rpow_natCast (N : ℝ) 3]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    calc (seventeenNinthsCut M : ℝ) ^ 5 / (N : ℝ) ^ 8
        ≤ ((2 : ℝ) ^ (17 / 9 : ℝ) * (N : ℝ) ^ (17 / 9 : ℝ)) ^ 5 / (N : ℝ) ^ 8 :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hwM_bound 5) (by positivity)
      _ = ((2 : ℝ) ^ (17 / 9 : ℝ)) ^ 5 * (((N : ℝ) ^ (17 / 9 : ℝ)) ^ 5 / (N : ℝ) ^ 8) := by
          rw [mul_pow]; ring
      _ ≤ (2 : ℝ) ^ 17 * (N : ℝ) ^ 3 := mul_le_mul h2 hNp (by positivity) (by positivity)
  have hsum3 : (seventeenNinthsCut M : ℝ) ^ 9 / (N : ℝ) ^ 14 +
      (seventeenNinthsCut M : ℝ) ^ 8 / (N : ℝ) ^ 13 +
      (seventeenNinthsCut M : ℝ) ^ 5 / (N : ℝ) ^ 8 ≤ 3 * (2 : ℝ) ^ 17 * (N : ℝ) ^ 3 := by
    linarith
  calc Cs * (1 + Real.log (seventeenNinthsCut M)) *
        ((seventeenNinthsCut M : ℝ) ^ 9 / (N : ℝ) ^ 14 +
          (seventeenNinthsCut M : ℝ) ^ 8 / (N : ℝ) ^ 13 +
          (seventeenNinthsCut M : ℝ) ^ 5 / (N : ℝ) ^ 8)
      ≤ Cs * (8 * logFactor N) * (3 * (2 : ℝ) ^ 17 * (N : ℝ) ^ 3) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hlogW hCs) hsum3 (by positivity) ?_
        have := logFactor_one_le N; positivity
    _ = A_const * (N : ℝ) ^ 3 * logFactor N := by dsimp only [A_const]; ring
    _ ≤ (F + A_const) * (N : ℝ) ^ 3 * logFactor N := by
        have hlf_nn : 0 ≤ logFactor N := zero_le_one.trans (logFactor_one_le N)
        nlinarith [mul_nonneg hF0 (mul_nonneg (pow_nonneg hN0_r.le 3) hlf_nn)]

/-- Across every terminal conductor `N`, conductor smoothing bridges the gap from
`⌊n^(15/8)⌋` to `⌊n^(17/9)⌋` at cost `O(N³ (1 + log(2N)))`. -/
theorem fifteenSixteenths_to_seventeenNinths_prefix :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |fifteenSixteenthsConductorPrefix N - seventeenNinthsConductorPrefix N| ≤
        C * (N : ℝ) ^ 3 * (1 + Real.log (2 * (N : ℝ))) := by
  obtain ⟨C0, hC0, hoct⟩ := bridge_octave_bound
  let S := fun n : ℕ => fifteenSixteenthsConductor n - seventeenNinthsConductor n
  let K := |S 1| + 2 * C0
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, fun N => ?_⟩
  have hpref_eq : ∀ M : ℕ,
      fifteenSixteenthsConductorPrefix M - seventeenNinthsConductorPrefix M =
        ∑ n ∈ Icc 1 M, (n : ℝ) ^ 2 * S n := by
    intro M
    unfold fifteenSixteenthsConductorPrefix seventeenNinthsConductorPrefix
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by dsimp only [S]; ring
  rw [hpref_eq N]
  induction N using Nat.strong_induction_on with
  | h N ih =>
    rcases N with _ | _ | m
    · simp
    · simp only [Nat.zero_add, Icc_self, sum_singleton, Nat.cast_one, one_pow, one_mul]
      have h1 : 1 ≤ logFactor 1 := logFactor_one_le 1
      dsimp only [K]
      nlinarith [abs_nonneg (S 1), hC0]
    · set N' := m + 2
      let M0 := (N' + 1) / 2
      have hM0_pos : 1 ≤ M0 := by dsimp only [M0, N']; omega
      have hM0_lt : M0 < N' := by dsimp only [M0, N']; omega
      have hN'_le_2M0 : N' ≤ 2 * M0 := by dsimp only [M0, N']; omega
      have h3M0 : 3 * M0 ≤ 2 * N' := by dsimp only [M0, N']; omega
      have hM0_real : (M0 : ℝ) ≤ (2 / 3 : ℝ) * N' := by
        have : 3 * (M0 : ℝ) ≤ 2 * (N' : ℝ) := by exact_mod_cast h3M0
        linarith
      have hM0_cube : (M0 : ℝ) ^ 3 ≤ (8 / 27 : ℝ) * (N' : ℝ) ^ 3 := by
        calc (M0 : ℝ) ^ 3 ≤ ((2 / 3 : ℝ) * N') ^ 3 :=
              pow_le_pow_left₀ (Nat.cast_nonneg M0) hM0_real 3
          _ = (8 / 27 : ℝ) * (N' : ℝ) ^ 3 := by ring
      have hsplit : (∑ n ∈ Icc 1 N', (n : ℝ) ^ 2 * S n) =
          (∑ n ∈ Icc 1 M0, (n : ℝ) ^ 2 * S n) +
            (∑ n ∈ Ioc M0 N', (n : ℝ) ^ 2 * S n) := by
        have h1 : Icc 1 M0 = Ioc 0 M0 := by ext k; simp only [mem_Icc, mem_Ioc]; omega
        have h2 : Icc 1 N' = Ioc 0 N' := by ext k; simp only [mem_Icc, mem_Ioc]; omega
        rw [h1, h2, sum_Ioc_consecutive _ (Nat.zero_le M0) hM0_lt.le]
      rw [hsplit]
      have hleft := ih M0 hM0_lt
      have hright := hoct M0 N' hM0_lt.le hN'_le_2M0
      have hlog_mono : logFactor M0 ≤ logFactor N' :=
        logFactor_mono hM0_pos hM0_lt.le
      have hcl_pos : 0 ≤ logFactor N' := zero_le_one.trans (logFactor_one_le N')
      have hN'_cube_pos : 0 ≤ (N' : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg N') 3
      calc |(∑ n ∈ Icc 1 M0, (n : ℝ) ^ 2 * S n) + ∑ n ∈ Ioc M0 N', (n : ℝ) ^ 2 * S n|
          ≤ K * (M0 : ℝ) ^ 3 * logFactor M0 + C0 * (M0 : ℝ) ^ 3 * logFactor M0 :=
            (abs_add_le _ _).trans (add_le_add hleft hright)
        _ = (K + C0) * (M0 : ℝ) ^ 3 * logFactor M0 := by ring
        _ ≤ (K + C0) * ((8 / 27 : ℝ) * (N' : ℝ) ^ 3) * logFactor N' := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hM0_cube (add_nonneg hK hC0))
              hlog_mono (zero_le_one.trans (logFactor_one_le M0)) (by positivity)
        _ ≤ K * (N' : ℝ) ^ 3 * logFactor N' := by
            have hKC : (8 / 27 : ℝ) * (K + C0) ≤ K := by
              dsimp only [K]; linarith [abs_nonneg (S 1), hC0]
            calc (K + C0) * ((8 / 27 : ℝ) * (N' : ℝ) ^ 3) * logFactor N'
                = ((8 / 27 : ℝ) * (K + C0)) * ((N' : ℝ) ^ 3 * logFactor N') := by ring
              _ ≤ K * ((N' : ℝ) ^ 3 * logFactor N') :=
                  mul_le_mul_of_nonneg_right hKC (mul_nonneg hN'_cube_pos hcl_pos)
              _ = K * (N' : ℝ) ^ 3 * logFactor N' := by ring

/-- Complete prefix approximation at the seventeen-eighteenths cutoff `⌊n^(17/9)⌋`. -/
theorem squareGeneratorPrefix_seventeenNinths_products :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |Real.log (squareGeneratorPrefix N : ℝ) - seventeenNinthsConductorPrefix N| ≤
        C * (N : ℝ) ^ 3 * (1 + Real.log (2 * (N : ℝ))) ^ 6 := by
  obtain ⟨C1, hC1, h1⟩ := squareGeneratorPrefix_fifteenSixteenths_products
  obtain ⟨C2, hC2, h2⟩ := fifteenSixteenths_to_seventeenNinths_prefix
  refine ⟨C1 + C2, add_nonneg hC1 hC2, fun N => ?_⟩
  have hid : Real.log (squareGeneratorPrefix N : ℝ) - seventeenNinthsConductorPrefix N =
      (Real.log (squareGeneratorPrefix N : ℝ) - fifteenSixteenthsConductorPrefix N) +
        (fifteenSixteenthsConductorPrefix N - seventeenNinthsConductorPrefix N) := by ring
  rw [hid]
  have hlog6 : logFactor N ≤ (logFactor N) ^ 6 :=
    le_self_pow₀ (logFactor_one_le N) (by decide : 6 ≠ 0)
  have h2' : |fifteenSixteenthsConductorPrefix N - seventeenNinthsConductorPrefix N| ≤
      C2 * (N : ℝ) ^ 3 * (logFactor N) ^ 6 :=
    (h2 N).trans (mul_le_mul_of_nonneg_left hlog6
      (mul_nonneg hC2 (pow_nonneg (Nat.cast_nonneg N) 3)))
  exact (abs_add_le _ _).trans ((add_le_add (h1 N) h2').trans_eq (by ring))

/-- Subcritical zero-width equivalence at the seventeen-eighteenths product cutoff. -/
theorem width_iff_seventeenNinthsConductorPrefix {a : ℝ} (ha : 0 < a) (ha' : a < 1 / 2) :
    zetaZeroWidth ≤ a ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |seventeenNinthsConductorPrefix N| ≤ C * (N : ℝ) ^ (3 + 2 * a) := by
  obtain ⟨K, hK, h⟩ := squareGeneratorPrefix_seventeenNinths_products
  obtain ⟨B, hB, hb⟩ := logFactor_pow_subpower (mul_pos two_pos ha)
  have hh (N : ℕ) : |Real.log (squareGeneratorPrefix N : ℝ) - seventeenNinthsConductorPrefix N| ≤
      (K * B) * (N : ℝ) ^ (3 + 2 * a) := by
    refine (h N).trans ?_
    rcases Nat.eq_zero_or_pos N with rfl | hn
    · simp [Real.zero_rpow (by linarith : 3 + 2 * a ≠ 0)]
    · have hn' : (0 : ℝ) < N := Nat.cast_pos.mpr hn
      rw [Real.rpow_add hn', Real.rpow_natCast _ 3]
      exact (mul_le_mul_of_nonneg_left (hb hn) (by positivity : 0 ≤ K * (N : ℝ) ^ 3)).trans_eq (by ring)
  rw [zetaZeroWidth_le_iff_square_generator_prefix ha.le ha']
  constructor <;> rintro ⟨C, hC, hc⟩ <;> refine ⟨C + K * B, by positivity, fun N => ?_⟩
  · have hid : seventeenNinthsConductorPrefix N =
        Real.log (squareGeneratorPrefix N : ℝ) -
          (Real.log (squareGeneratorPrefix N : ℝ) - seventeenNinthsConductorPrefix N) := by ring
    rw [hid]
    exact (abs_sub _ _).trans ((add_le_add (hc N) (hh N)).trans_eq (by ring))
  · have hid : Real.log (squareGeneratorPrefix N : ℝ) =
        seventeenNinthsConductorPrefix N +
          (Real.log (squareGeneratorPrefix N : ℝ) - seventeenNinthsConductorPrefix N) := by ring
    rw [hid]
    exact (abs_add_le _ _).trans ((add_le_add (hc N) (hh N)).trans_eq (by ring))

/-- Five-sixths zero-free strip equivalence at the seventeen-eighteenths product cutoff. -/
theorem five_sixths_iff_seventeenNinthsConductorPrefix :
    _root_.RHTower.zetaZeroAbscissa ≤ 5 / 6 ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |seventeenNinthsConductorPrefix N| ≤ C * (N : ℝ) ^ (11 / 3 : ℝ) := by
  have h := (zetaZeroWidth_le_iff_zetaZeroAbscissa_le (by norm_num : (0 : ℝ) ≤ 1 / 3)).symm.trans
    (width_iff_seventeenNinthsConductorPrefix (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num))
  simpa only [show 1 / 2 + (1 / 3 : ℝ) = 5 / 6 by norm_num,
    show 3 + 2 * (1 / 3 : ℝ) = 11 / 3 by norm_num] using h

/-- Exact Riemann Hypothesis equivalence for the signed prefix above `⌊n^(17/9)⌋`. -/
theorem riemannHypothesis_iff_seventeenNinthsConductorPrefix :
    RiemannHypothesis ↔ ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |seventeenNinthsConductorPrefix N| ≤ C * (N : ℝ) ^ (3 + η) := by
  rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  constructor
  · intro hw η hη
    let a := min (η / 2) (1 / 4)
    have ha : 0 < a := lt_min (by positivity) (by norm_num)
    have ha' : a < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
    obtain ⟨C, hC, h⟩ := (width_iff_seventeenNinthsConductorPrefix ha ha').mp (hw ▸ ha.le)
    refine ⟨C, hC, fun N => (h N).trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
    rcases Nat.eq_zero_or_pos N with rfl | hn
    · simp [Real.zero_rpow (by linarith : 3 + 2 * a ≠ 0),
        Real.zero_rpow (by linarith : 3 + η ≠ 0)]
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
        (by linarith [min_le_left (η / 2) (1 / 4 : ℝ)] : 3 + 2 * a ≤ 3 + η)
  · intro h
    apply le_antisymm _ zetaZeroWidth_nonneg
    by_contra! hw
    have ha : 0 < zetaZeroWidth / 2 := half_pos hw
    have ha' : zetaZeroWidth / 2 < 1 / 2 := by linarith [zetaZeroWidth_le_half]
    have hs := (width_iff_seventeenNinthsConductorPrefix ha ha').mpr (h _ (mul_pos two_pos ha))
    linarith

/-- Every surviving pair `(p, v)` in `seventeenNinthsConductor n` has product above
`⌊n^(17/9)⌋`, prime factor above `⌊n^(17/9)⌋ / n`, and outer quotient at most `k / (⌊n^(17/9)⌋ + 1)`. -/
theorem seventeenNinths_surviving_ranges {n k p v : ℕ} (hp : 0 < p)
    (hv : v ∈ Ioc (max (productLower 1 k) (seventeenNinthsCut n) / p) (min (k / p) n)) :
    seventeenNinthsCut n < p * v ∧ seventeenNinthsCut n / n < p ∧
      k / p / v ≤ k / (seventeenNinthsCut n + 1) :=
  capped_upper_ranges hp hv

#print axioms sevenFourthsShell_reciprocal_bound
#print axioms sevenFourthsShell_absolute_octave_bound
#print axioms powerProductShell_conductor_smoothed_bound
#print axioms sevenFourthsShell_conductor_smoothed_bound
#print axioms sevenFourthsShell_dyadic_octave_bound
#print axioms sevenFourthsShell_saving_below_seven_fourths
#print axioms sevenFourthsShell_thirteen_eighths_saving
#print axioms dyadicPrimeContact_fifteenSixteenthsConductor
#print axioms squareGeneratorPrefix_seventeenNinths_products
#print axioms width_iff_seventeenNinthsConductorPrefix
#print axioms five_sixths_iff_seventeenNinthsConductorPrefix
#print axioms riemannHypothesis_iff_seventeenNinthsConductorPrefix
#print axioms seventeenNinths_surviving_ranges
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

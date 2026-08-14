import GaloisForLFunctions.RHTower.Sieve.InghamRightEdgeMeanSquare
import GaloisForLFunctions.RHTower.Sieve.DirichletTruncationError

open Complex MeasureTheory Set Finset ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

/-- Fixed right edge retaining enough room below Route T's `7/10` target. -/
noncomputable def inghamPowerSavingRightEdge : ℝ := 181 / 180

/-- Divisor-bound constant at the fixed exponent `1/360`. -/
noncomputable def inghamPowerSavingDivisorConstant : ℝ :=
  Classical.choose
    (_root_.RHTower.card_divisors_le_const_mul_rpow
      (show (0 : ℝ) < 1 / 360 by norm_num))

theorem inghamPowerSavingDivisorConstant_pos :
    0 < inghamPowerSavingDivisorConstant :=
  (Classical.choose_spec
    (_root_.RHTower.card_divisors_le_const_mul_rpow
      (show (0 : ℝ) < 1 / 360 by norm_num))).1

theorem card_divisors_le_inghamPowerSavingDivisorConstant
    (n : ℕ) (hn : 1 ≤ n) :
    (n.divisors.card : ℝ) ≤
      inghamPowerSavingDivisorConstant * (n : ℝ) ^ (1 / 360 : ℝ) :=
  (Classical.choose_spec
    (_root_.RHTower.card_divisors_le_const_mul_rpow
      (show (0 : ℝ) < 1 / 360 by norm_num))).2 n hn

noncomputable def inghamRightEdgeSquareMass (X n : ℕ) : ℝ :=
  ‖complexCoeff (moebiusZetaDefect X) n *
      (((n : ℝ) ^ (-inghamPowerSavingRightEdge) : ℝ) : ℂ)‖ ^ 2

private theorem inghamRightEdgeSquareMass_nonneg (X n : ℕ) :
    0 ≤ inghamRightEdgeSquareMass X n := by
  exact sq_nonneg _

private theorem inghamRightEdgeSquareMass_zero_of_le
    {X n : ℕ} (hn : n ≤ X) :
    inghamRightEdgeSquareMass X n = 0 := by
  have hz : moebiusZetaDefect X n = 0 :=
    (moebiusZetaDefect_vanishesBelow X) n (by omega)
  simp [inghamRightEdgeSquareMass, hz, complexCoeff]

private theorem inghamRightEdgeSquareMass_le
    {X n : ℕ} (hX : 1 ≤ X) (hn : 1 ≤ n) :
    inghamRightEdgeSquareMass X n ≤
      inghamPowerSavingDivisorConstant ^ 2 *
        (n : ℝ) ^ (-(361 / 180 : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcoeff := norm_complexCoeff_moebiusZetaDefect_le_card_divisors hX n
  have hdiv := card_divisors_le_inghamPowerSavingDivisorConstant n hn
  have hC0 : 0 ≤ inghamPowerSavingDivisorConstant :=
    inghamPowerSavingDivisorConstant_pos.le
  have hpow0 : 0 ≤ (n : ℝ) ^ (1 / 360 : ℝ) := Real.rpow_nonneg hnR.le _
  have hcoeff' : ‖complexCoeff (moebiusZetaDefect X) n‖ ≤
      inghamPowerSavingDivisorConstant * (n : ℝ) ^ (1 / 360 : ℝ) :=
    hcoeff.trans hdiv
  unfold inghamRightEdgeSquareMass inghamPowerSavingRightEdge
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hnR.le _), mul_pow]
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hcoeff' 2
  have hpowSmall : ((n : ℝ) ^ (1 / 360 : ℝ)) ^ (2 : ℕ) =
      (n : ℝ) ^ (1 / 180 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    norm_num
  have hpowRight : ((n : ℝ) ^ (-(181 / 180 : ℝ))) ^ (2 : ℕ) =
      (n : ℝ) ^ (-(181 / 90 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    norm_num
  calc
    ‖complexCoeff (moebiusZetaDefect X) n‖ ^ 2 *
          ((n : ℝ) ^ (-(181 / 180 : ℝ))) ^ 2
        ≤ (inghamPowerSavingDivisorConstant *
            (n : ℝ) ^ (1 / 360 : ℝ)) ^ 2 *
          ((n : ℝ) ^ (-(181 / 180 : ℝ))) ^ 2 :=
      mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
    _ = inghamPowerSavingDivisorConstant ^ 2 *
        (n : ℝ) ^ (-(361 / 180 : ℝ)) := by
      rw [mul_pow, hpowSmall, hpowRight]
      calc
        inghamPowerSavingDivisorConstant ^ 2 * (n : ℝ) ^ (1 / 180 : ℝ) *
              (n : ℝ) ^ (-(181 / 90 : ℝ)) =
            inghamPowerSavingDivisorConstant ^ 2 *
              ((n : ℝ) ^ (1 / 180 : ℝ) *
                (n : ℝ) ^ (-(181 / 90 : ℝ))) := by ring
        _ = inghamPowerSavingDivisorConstant ^ 2 *
            (n : ℝ) ^ (-(361 / 180 : ℝ)) := by
          rw [← Real.rpow_add hnR]
          congr 2
          norm_num

private theorem inghamRightEdgeWeightedSquareMass_le
    {X n : ℕ} (hX : 1 ≤ X) (hn : 1 ≤ n) :
    (n : ℝ) * inghamRightEdgeSquareMass X n ≤
      inghamPowerSavingDivisorConstant ^ 2 *
        (n : ℝ) ^ (-(181 / 180 : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := inghamRightEdgeSquareMass_le hX hn
  calc
    (n : ℝ) * inghamRightEdgeSquareMass X n ≤
        (n : ℝ) * (inghamPowerSavingDivisorConstant ^ 2 *
          (n : ℝ) ^ (-(361 / 180 : ℝ))) :=
      mul_le_mul_of_nonneg_left h hnR.le
    _ = inghamPowerSavingDivisorConstant ^ 2 *
        (n : ℝ) ^ (-(181 / 180 : ℝ)) := by
      calc
        (n : ℝ) * (inghamPowerSavingDivisorConstant ^ 2 *
              (n : ℝ) ^ (-(361 / 180 : ℝ))) =
            inghamPowerSavingDivisorConstant ^ 2 *
              ((n : ℝ) * (n : ℝ) ^ (-(361 / 180 : ℝ))) := by ring
        _ = inghamPowerSavingDivisorConstant ^ 2 *
              ((n : ℝ) ^ (1 : ℝ) *
                (n : ℝ) ^ (-(361 / 180 : ℝ))) := by rw [Real.rpow_one]
        _ = inghamPowerSavingDivisorConstant ^ 2 *
            (n : ℝ) ^ (-(181 / 180 : ℝ)) := by
          rw [← Real.rpow_add hnR]
          congr 2
          norm_num

private theorem tsum_inghamRightEdgeSquareMass_eq_shift
    {X : ℕ} (hX : 1 ≤ X) :
    ∑' n : ℕ, inghamRightEdgeSquareMass X n =
      ∑' k : ℕ, inghamRightEdgeSquareMass X (k + X + 1) := by
  have hs := summable_normSq_complexCoeff_moebiusZetaDefect_damped hX
    (show 1 < inghamPowerSavingRightEdge by norm_num [inghamPowerSavingRightEdge])
  have hs' : Summable (inghamRightEdgeSquareMass X) := by
    show Summable (fun n : ℕ =>
      ‖complexCoeff (moebiusZetaDefect X) n *
        (((n : ℝ) ^ (-inghamPowerSavingRightEdge) : ℝ) : ℂ)‖ ^ 2)
    exact hs
  have hsplit := hs'.sum_add_tsum_nat_add (X + 1)
  have hzero : ∑ n ∈ Finset.range (X + 1), inghamRightEdgeSquareMass X n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact inghamRightEdgeSquareMass_zero_of_le (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hn))
  rw [hzero, zero_add] at hsplit
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit.symm

private theorem tsum_inghamRightEdgeWeightedSquareMass_eq_shift
    {X : ℕ} (hX : 1 ≤ X) :
    ∑' n : ℕ, (n : ℝ) * inghamRightEdgeSquareMass X n =
      ∑' k : ℕ, ((k + X + 1 : ℕ) : ℝ) *
        inghamRightEdgeSquareMass X (k + X + 1) := by
  have hs := summable_weighted_normSq_complexCoeff_moebiusZetaDefect_damped hX
    (show 1 < inghamPowerSavingRightEdge by norm_num [inghamPowerSavingRightEdge])
  have hs' : Summable (fun n : ℕ => (n : ℝ) * inghamRightEdgeSquareMass X n) := by
    simpa [inghamRightEdgeSquareMass] using hs
  have hsplit := hs'.sum_add_tsum_nat_add (X + 1)
  have hzero : ∑ n ∈ Finset.range (X + 1),
      (n : ℝ) * inghamRightEdgeSquareMass X n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [inghamRightEdgeSquareMass_zero_of_le
      (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hn)), mul_zero]
  rw [hzero, zero_add] at hsplit
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit.symm

theorem tsum_inghamRightEdgeSquareMass_le
    {X : ℕ} (hX : 1 ≤ X) :
    ∑' n : ℕ, inghamRightEdgeSquareMass X n ≤
      inghamPowerSavingDivisorConstant ^ 2 *
        (X : ℝ) ^ (-(181 / 180 : ℝ)) / (181 / 180 : ℝ) := by
  rw [tsum_inghamRightEdgeSquareMass_eq_shift hX]
  have hterm : ∀ k : ℕ,
      inghamRightEdgeSquareMass X (k + X + 1) ≤
        inghamPowerSavingDivisorConstant ^ 2 *
          (((k + X + 1 : ℕ) : ℝ) ^ (-(361 / 180 : ℝ))) := by
    intro k
    exact inghamRightEdgeSquareMass_le hX (by omega)
  have hsum : Summable (fun k : ℕ =>
      inghamPowerSavingDivisorConstant ^ 2 *
        (((k + X + 1 : ℕ) : ℝ) ^ (-(361 / 180 : ℝ)))) :=
    ((summable_nat_add_iff (X + 1)).2
      (summable_nat_rpow_neg (show 1 < (361 / 180 : ℝ) by norm_num))).mul_left _
  have hbase := summable_normSq_complexCoeff_moebiusZetaDefect_damped hX
    (show 1 < inghamPowerSavingRightEdge by norm_num [inghamPowerSavingRightEdge])
  have hinj : Function.Injective (fun k : ℕ => k + X + 1) := by
    intro a b hab
    exact Nat.add_right_cancel (Nat.add_right_cancel hab)
  have hsmall : Summable (fun k : ℕ => inghamRightEdgeSquareMass X (k + X + 1)) := by
    apply (hbase.comp_injective hinj).congr
    intro k
    rfl
  refine (Summable.tsum_le_tsum hterm hsmall hsum).trans ?_
  · calc
      (∑' i : ℕ, inghamPowerSavingDivisorConstant ^ 2 *
          (((i + X + 1 : ℕ) : ℝ) ^ (-(361 / 180 : ℝ)))) =
          inghamPowerSavingDivisorConstant ^ 2 *
            ∑' i : ℕ, (((i + X + 1 : ℕ) : ℝ) ^ (-(361 / 180 : ℝ))) := tsum_mul_left
      _ ≤ inghamPowerSavingDivisorConstant ^ 2 *
          ((X : ℝ) ^ (-(181 / 180 : ℝ)) / (181 / 180 : ℝ)) :=
        mul_le_mul_of_nonneg_left (by
          have htail := tsum_tail_rpow_neg_le
            (show 1 < (361 / 180 : ℝ) by norm_num) hX
          norm_num at htail
          simpa only [Nat.cast_add, Nat.cast_one] using htail) (sq_nonneg _)
      _ = inghamPowerSavingDivisorConstant ^ 2 *
          (X : ℝ) ^ (-(181 / 180 : ℝ)) / (181 / 180 : ℝ) := by ring

theorem tsum_inghamRightEdgeWeightedSquareMass_le
    {X : ℕ} (hX : 1 ≤ X) :
    ∑' n : ℕ, (n : ℝ) * inghamRightEdgeSquareMass X n ≤
      inghamPowerSavingDivisorConstant ^ 2 *
        (X : ℝ) ^ (-(1 / 180 : ℝ)) / (1 / 180 : ℝ) := by
  rw [tsum_inghamRightEdgeWeightedSquareMass_eq_shift hX]
  have hterm : ∀ k : ℕ,
      ((k + X + 1 : ℕ) : ℝ) * inghamRightEdgeSquareMass X (k + X + 1) ≤
        inghamPowerSavingDivisorConstant ^ 2 *
          (((k + X + 1 : ℕ) : ℝ) ^ (-(181 / 180 : ℝ))) := by
    intro k
    exact inghamRightEdgeWeightedSquareMass_le hX (by omega)
  have hsum : Summable (fun k : ℕ =>
      inghamPowerSavingDivisorConstant ^ 2 *
        (((k + X + 1 : ℕ) : ℝ) ^ (-(181 / 180 : ℝ)))) :=
    ((summable_nat_add_iff (X + 1)).2
      (summable_nat_rpow_neg (show 1 < (181 / 180 : ℝ) by norm_num))).mul_left _
  have hbase := summable_weighted_normSq_complexCoeff_moebiusZetaDefect_damped hX
    (show 1 < inghamPowerSavingRightEdge by norm_num [inghamPowerSavingRightEdge])
  have hinj : Function.Injective (fun k : ℕ => k + X + 1) := by
    intro a b hab
    exact Nat.add_right_cancel (Nat.add_right_cancel hab)
  have hsmall : Summable (fun k : ℕ =>
      ((k + X + 1 : ℕ) : ℝ) * inghamRightEdgeSquareMass X (k + X + 1)) := by
    apply (hbase.comp_injective hinj).congr
    intro k
    rfl
  refine (Summable.tsum_le_tsum hterm hsmall hsum).trans ?_
  · calc
      (∑' i : ℕ, inghamPowerSavingDivisorConstant ^ 2 *
          (((i + X + 1 : ℕ) : ℝ) ^ (-(181 / 180 : ℝ)))) =
          inghamPowerSavingDivisorConstant ^ 2 *
            ∑' i : ℕ, (((i + X + 1 : ℕ) : ℝ) ^ (-(181 / 180 : ℝ))) := tsum_mul_left
      _ ≤ inghamPowerSavingDivisorConstant ^ 2 *
          ((X : ℝ) ^ (-(1 / 180 : ℝ)) / (1 / 180 : ℝ)) :=
        mul_le_mul_of_nonneg_left (by
          have htail := tsum_tail_rpow_neg_le
            (show 1 < (181 / 180 : ℝ) by norm_num) hX
          norm_num at htail
          simpa only [Nat.cast_add, Nat.cast_one] using htail) (sq_nonneg _)
      _ = inghamPowerSavingDivisorConstant ^ 2 *
          (X : ℝ) ^ (-(1 / 180 : ℝ)) / (1 / 180 : ℝ) := by ring

/-- Constant in the fixed-right-edge power-saving mean square. -/
noncomputable def inghamPowerSavingRightEdgeMeanSquareConstant : ℝ :=
  5 * Real.pi * Real.exp 1 *
      (inghamPowerSavingDivisorConstant ^ 2 / (1 / 180 : ℝ)) +
    (5 * Real.pi / 2) *
      (inghamPowerSavingDivisorConstant ^ 2 / (181 / 180 : ℝ))

theorem inghamPowerSavingRightEdgeMeanSquareConstant_pos :
    0 < inghamPowerSavingRightEdgeMeanSquareConstant := by
  unfold inghamPowerSavingRightEdgeMeanSquareConstant
  have hC := inghamPowerSavingDivisorConstant_pos
  positivity

/-- **Power-saving right-edge mean square.** Exact coefficient vanishing through `X`, rather than
mere cutoff-uniform summability, saves `X^(-1/180)` on the fixed line `181/180`. This is the
right-edge input that coefficient-three Gabriel interpolation actually needs. -/
theorem integral_Icc_normSq_inghamMollifiedError_powerSavingRightEdge_le
    {X : ℕ} (hX : 1 ≤ X) :
    (∫ t in Set.Icc (-(X : ℝ)) (X : ℝ),
      ‖riemannZeta (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) *
          inghamMollifier X
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) - 1‖ ^ 2) ≤
      inghamPowerSavingRightEdgeMeanSquareConstant *
        (X : ℝ) ^ (-(1 / 180 : ℝ)) := by
  let a : ℕ → ℂ := complexCoeff (moebiusZetaDefect X)
  have hbeta : 1 < inghamPowerSavingRightEdge := by
    norm_num [inghamPowerSavingRightEdge]
  have habs := summable_norm_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hplain := summable_normSq_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hweighted :=
    summable_weighted_normSq_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hbase := integral_Icc_normSq_LSeries_le_general_affine_infinite
    (a := a) (complexCoeff_moebiusZetaDefect_zero X)
    inghamPowerSavingRightEdge habs hplain hweighted hXR
  have hsource (t : ℝ) :
      ‖LSeries a
          (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I)‖ =
        ‖riemannZeta
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) *
          inghamMollifier X
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) - 1‖ := by
    have hs : 1 <
        ((((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I)).re := by
      simpa using hbeta
    rw [show a = complexCoeff (moebiusZetaDefect X) by rfl,
      LSeries_complexCoeff_moebiusZetaDefect_eq X hs]
    rw [show 1 - inghamMollifier X
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) *
          riemannZeta
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) =
        -(riemannZeta
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) *
          inghamMollifier X
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) - 1) by ring,
      norm_neg]
  have hW : (∑' n : ℕ, (n : ℝ) *
      ‖a n * (((n : ℝ) ^ (-inghamPowerSavingRightEdge) : ℝ) : ℂ)‖ ^ 2) ≤
      inghamPowerSavingDivisorConstant ^ 2 *
        (X : ℝ) ^ (-(1 / 180 : ℝ)) / (1 / 180 : ℝ) := by
    simpa [a, inghamRightEdgeSquareMass] using
      tsum_inghamRightEdgeWeightedSquareMass_le hX
  have hP : (∑' n : ℕ,
      ‖a n * (((n : ℝ) ^ (-inghamPowerSavingRightEdge) : ℝ) : ℂ)‖ ^ 2) ≤
      inghamPowerSavingDivisorConstant ^ 2 *
        (X : ℝ) ^ (-(181 / 180 : ℝ)) / (181 / 180 : ℝ) := by
    simpa [a, inghamRightEdgeSquareMass] using
      tsum_inghamRightEdgeSquareMass_le hX
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hW0 : 0 ≤ inghamPowerSavingDivisorConstant ^ 2 *
      (X : ℝ) ^ (-(1 / 180 : ℝ)) / (1 / 180 : ℝ) := by positivity
  have hP0 : 0 ≤ inghamPowerSavingDivisorConstant ^ 2 *
      (X : ℝ) ^ (-(181 / 180 : ℝ)) / (181 / 180 : ℝ) := by positivity
  calc
    (∫ t in Set.Icc (-(X : ℝ)) (X : ℝ),
      ‖riemannZeta (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) *
          inghamMollifier X
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I) - 1‖ ^ 2) =
        ∫ t in Set.Icc (-(X : ℝ)) (X : ℝ),
          ‖LSeries a
            (((inghamPowerSavingRightEdge : ℝ) : ℂ) + (t : ℝ) * I)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hsource]
    _ ≤ 5 * Real.pi * Real.exp 1 *
          (∑' n : ℕ, (n : ℝ) *
            ‖a n * (((n : ℝ) ^ (-inghamPowerSavingRightEdge) : ℝ) : ℂ)‖ ^ 2) +
        (5 * Real.pi / 2) *
          (∑' n : ℕ,
            ‖a n * (((n : ℝ) ^ (-inghamPowerSavingRightEdge) : ℝ) : ℂ)‖ ^ 2) *
              (X : ℝ) := hbase
    _ ≤ 5 * Real.pi * Real.exp 1 *
          (inghamPowerSavingDivisorConstant ^ 2 *
            (X : ℝ) ^ (-(1 / 180 : ℝ)) / (1 / 180 : ℝ)) +
        (5 * Real.pi / 2) *
          (inghamPowerSavingDivisorConstant ^ 2 *
            (X : ℝ) ^ (-(181 / 180 : ℝ)) / (181 / 180 : ℝ)) *
              (X : ℝ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hW (by positivity))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hP (by positivity)) hX0.le)
    _ = inghamPowerSavingRightEdgeMeanSquareConstant *
        (X : ℝ) ^ (-(1 / 180 : ℝ)) := by
      have hpow : (X : ℝ) ^ (-(181 / 180 : ℝ)) * (X : ℝ) =
          (X : ℝ) ^ (-(1 / 180 : ℝ)) := by
        calc
          (X : ℝ) ^ (-(181 / 180 : ℝ)) * (X : ℝ) =
              (X : ℝ) ^ (-(181 / 180 : ℝ)) * (X : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = (X : ℝ) ^ (-(181 / 180 : ℝ) + (1 : ℝ)) := by
            rw [Real.rpow_add hX0]
          _ = (X : ℝ) ^ (-(1 / 180 : ℝ)) := by
            congr 1
            norm_num
      have hfirst : inghamPowerSavingDivisorConstant ^ 2 *
            (X : ℝ) ^ (-(1 / 180 : ℝ)) / (1 / 180 : ℝ) =
          (inghamPowerSavingDivisorConstant ^ 2 / (1 / 180 : ℝ)) *
            (X : ℝ) ^ (-(1 / 180 : ℝ)) := by ring
      have hright : inghamPowerSavingDivisorConstant ^ 2 *
            (X : ℝ) ^ (-(181 / 180 : ℝ)) / (181 / 180 : ℝ) * (X : ℝ) =
          (inghamPowerSavingDivisorConstant ^ 2 / (181 / 180 : ℝ)) *
            (X : ℝ) ^ (-(1 / 180 : ℝ)) := by
        calc
          inghamPowerSavingDivisorConstant ^ 2 *
                (X : ℝ) ^ (-(181 / 180 : ℝ)) / (181 / 180 : ℝ) * (X : ℝ) =
              (inghamPowerSavingDivisorConstant ^ 2 / (181 / 180 : ℝ)) *
                ((X : ℝ) ^ (-(181 / 180 : ℝ)) * (X : ℝ)) := by ring
          _ = (inghamPowerSavingDivisorConstant ^ 2 / (181 / 180 : ℝ)) *
              (X : ℝ) ^ (-(1 / 180 : ℝ)) := by rw [hpow]
      unfold inghamPowerSavingRightEdgeMeanSquareConstant
      calc
        5 * Real.pi * Real.exp 1 *
              (inghamPowerSavingDivisorConstant ^ 2 *
                (X : ℝ) ^ (-(1 / 180 : ℝ)) / (1 / 180 : ℝ)) +
            (5 * Real.pi / 2) *
              (inghamPowerSavingDivisorConstant ^ 2 *
                (X : ℝ) ^ (-(181 / 180 : ℝ)) / (181 / 180 : ℝ)) * (X : ℝ) =
            5 * Real.pi * Real.exp 1 *
              ((inghamPowerSavingDivisorConstant ^ 2 / (1 / 180 : ℝ)) *
                (X : ℝ) ^ (-(1 / 180 : ℝ))) +
            (5 * Real.pi / 2) *
              ((inghamPowerSavingDivisorConstant ^ 2 *
                (X : ℝ) ^ (-(181 / 180 : ℝ)) / (181 / 180 : ℝ)) * (X : ℝ)) := by
          rw [hfirst]
          ring
        _ = 5 * Real.pi * Real.exp 1 *
              ((inghamPowerSavingDivisorConstant ^ 2 / (1 / 180 : ℝ)) *
                (X : ℝ) ^ (-(1 / 180 : ℝ))) +
            (5 * Real.pi / 2) *
              ((inghamPowerSavingDivisorConstant ^ 2 / (181 / 180 : ℝ)) *
                (X : ℝ) ^ (-(1 / 180 : ℝ))) := by rw [hright]
        _ = (5 * Real.pi * Real.exp 1 *
                (inghamPowerSavingDivisorConstant ^ 2 / (1 / 180 : ℝ)) +
              5 * Real.pi / 2 *
                (inghamPowerSavingDivisorConstant ^ 2 / (181 / 180 : ℝ))) *
              (X : ℝ) ^ (-(1 / 180 : ℝ)) := by ring

end

end RHTower.Sieve

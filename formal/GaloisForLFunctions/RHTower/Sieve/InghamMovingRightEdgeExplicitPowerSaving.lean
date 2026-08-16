import GaloisForLFunctions.RHTower.Sieve.InghamMovingRightEdgePowerSaving
import GaloisForLFunctions.RHTower.Sieve.InghamDivisorSquareNearPole

open Complex MeasureTheory Set Finset ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

private noncomputable def inghamMovingRightExplicitSquareMass
    (delta : ℝ) (X n : ℕ) : ℝ :=
  ‖complexCoeff (moebiusZetaDefect X) n *
      (((n : ℝ) ^ (-(1 + delta)) : ℝ) : ℂ)‖ ^ 2

private theorem inghamMovingRightExplicitSquareMass_zero_of_le
    {delta : ℝ} {X n : ℕ} (hn : n ≤ X) :
    inghamMovingRightExplicitSquareMass delta X n = 0 := by
  have hz : moebiusZetaDefect X n = 0 :=
    (moebiusZetaDefect_vanishesBelow X) n (by omega)
  simp [inghamMovingRightExplicitSquareMass, hz, complexCoeff]

private theorem inghamMovingRightExplicitSquareMass_le
    {delta : ℝ} {X n : ℕ} (hX : 1 ≤ X) (hn : 1 ≤ n) :
    inghamMovingRightExplicitSquareMass delta X n ≤
      (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(2 + 2 * delta)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcoeff := norm_complexCoeff_moebiusZetaDefect_le_card_divisors hX n
  unfold inghamMovingRightExplicitSquareMass
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hnR.le _), mul_pow]
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hcoeff 2
  have hpowRight : ((n : ℝ) ^ (-(1 + delta))) ^ (2 : ℕ) =
      (n : ℝ) ^ (-2 * (1 + delta)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    congr 1
    ring
  calc
    ‖complexCoeff (moebiusZetaDefect X) n‖ ^ 2 *
          ((n : ℝ) ^ (-(1 + delta))) ^ 2
        ≤ (n.divisors.card : ℝ) ^ 2 *
          ((n : ℝ) ^ (-(1 + delta))) ^ 2 :=
      mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
    _ = (n.divisors.card : ℝ) ^ 2 *
        (n : ℝ) ^ (-(2 + 2 * delta)) := by
      rw [hpowRight]
      congr 2
      ring

private theorem inghamMovingRightExplicitWeightedSquareMass_le
    {delta : ℝ} {X n : ℕ} (hX : 1 ≤ X) (hn : 1 ≤ n) :
    (n : ℝ) * inghamMovingRightExplicitSquareMass delta X n ≤
      (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + 2 * delta)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := inghamMovingRightExplicitSquareMass_le (delta := delta) hX hn
  calc
    (n : ℝ) * inghamMovingRightExplicitSquareMass delta X n ≤
        (n : ℝ) * ((n.divisors.card : ℝ) ^ 2 *
          (n : ℝ) ^ (-(2 + 2 * delta))) :=
      mul_le_mul_of_nonneg_left h hnR.le
    _ = (n.divisors.card : ℝ) ^ 2 *
        (n : ℝ) ^ (-(1 + 2 * delta)) := by
      calc
        (n : ℝ) * ((n.divisors.card : ℝ) ^ 2 *
            (n : ℝ) ^ (-(2 + 2 * delta))) =
          (n.divisors.card : ℝ) ^ 2 *
            ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(2 + 2 * delta))) := by
              rw [Real.rpow_one]
              ring
        _ = _ := by
          rw [← Real.rpow_add hnR]
          congr 2
          ring

private theorem tsum_inghamMovingRightExplicitWeighted_eq_shift
    {delta : ℝ} (hdelta : 0 < delta) {X : ℕ} (hX : 1 ≤ X) :
    ∑' n : ℕ, (n : ℝ) * inghamMovingRightExplicitSquareMass delta X n =
      ∑' k : ℕ, ((k + X + 1 : ℕ) : ℝ) *
        inghamMovingRightExplicitSquareMass delta X (k + X + 1) := by
  have hbeta : 1 < 1 + delta := by linarith
  have hs := summable_weighted_normSq_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hs' : Summable (fun n : ℕ =>
      (n : ℝ) * inghamMovingRightExplicitSquareMass delta X n) := by
    simpa only [inghamMovingRightExplicitSquareMass] using hs
  have hsplit := hs'.sum_add_tsum_nat_add (X + 1)
  have hzero : ∑ n ∈ Finset.range (X + 1),
      (n : ℝ) * inghamMovingRightExplicitSquareMass delta X n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [inghamMovingRightExplicitSquareMass_zero_of_le
      (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hn)), mul_zero]
  rw [hzero, zero_add] at hsplit
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit.symm

private theorem tsum_inghamMovingRightExplicit_eq_shift
    {delta : ℝ} (hdelta : 0 < delta) {X : ℕ} (hX : 1 ≤ X) :
    ∑' n : ℕ, inghamMovingRightExplicitSquareMass delta X n =
      ∑' k : ℕ, inghamMovingRightExplicitSquareMass delta X (k + X + 1) := by
  have hbeta : 1 < 1 + delta := by linarith
  have hs := summable_normSq_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hs' : Summable (inghamMovingRightExplicitSquareMass delta X) := by
    change Summable fun n : ℕ =>
      ‖complexCoeff (moebiusZetaDefect X) n *
        (((n : ℝ) ^ (-(1 + delta)) : ℝ) : ℂ)‖ ^ 2
    exact hs
  have hsplit := hs'.sum_add_tsum_nat_add (X + 1)
  have hzero : ∑ n ∈ Finset.range (X + 1),
      inghamMovingRightExplicitSquareMass delta X n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact inghamMovingRightExplicitSquareMass_zero_of_le
      (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hn))
  rw [hzero, zero_add] at hsplit
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit.symm

theorem tsum_inghamMovingRightExplicitWeightedSquareMass_le_explicit
    {delta : ℝ} (hdelta : 0 < delta) {X : ℕ} (hX : 1 ≤ X) :
    ∑' n : ℕ, (n : ℝ) * inghamMovingRightExplicitSquareMass delta X n ≤
      (X : ℝ) ^ (-delta) * (1 + 1 / delta) ^ 4 := by
  rw [tsum_inghamMovingRightExplicitWeighted_eq_shift hdelta hX]
  let base : ℕ → ℝ := fun n =>
    (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + delta))
  let shift : ℕ → ℕ := fun k => k + X + 1
  have hinj : Function.Injective shift := by
    intro a b hab
    dsimp only [shift] at hab
    omega
  have hbase : Summable base := by
    simpa only [base] using
      summable_divisorSquare_mul_rpow_neg (by linarith : 1 < 1 + delta)
  have hbaseShift : Summable (fun k => base (shift k)) := hbase.comp_injective hinj
  have hactual : Summable (fun k : ℕ => ((shift k : ℕ) : ℝ) *
      inghamMovingRightExplicitSquareMass delta X (shift k)) := by
    have hbeta : 1 < 1 + delta := by linarith
    have hs := summable_weighted_normSq_complexCoeff_moebiusZetaDefect_damped hX hbeta
    have hs' : Summable (fun n : ℕ =>
        (n : ℝ) * inghamMovingRightExplicitSquareMass delta X n) := by
      simpa only [inghamMovingRightExplicitSquareMass] using hs
    exact hs'.comp_injective hinj
  have hterm : ∀ k : ℕ,
      ((shift k : ℕ) : ℝ) * inghamMovingRightExplicitSquareMass delta X (shift k) ≤
        (X : ℝ) ^ (-delta) * base (shift k) := by
    intro k
    have hn : 1 ≤ shift k := by dsimp only [shift]; omega
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    have hXn : (X : ℝ) ≤ (shift k : ℕ) := by
      exact_mod_cast (show X ≤ shift k by dsimp only [shift]; omega)
    have hpow : ((shift k : ℕ) : ℝ) ^ (-delta) ≤ (X : ℝ) ^ (-delta) :=
      Real.rpow_le_rpow_of_nonpos hXR hXn (by linarith)
    calc
      ((shift k : ℕ) : ℝ) * inghamMovingRightExplicitSquareMass delta X (shift k) ≤
          ((shift k).divisors.card : ℝ) ^ 2 *
            ((shift k : ℕ) : ℝ) ^ (-(1 + 2 * delta)) :=
        inghamMovingRightExplicitWeightedSquareMass_le hX hn
      _ = ((shift k : ℕ) : ℝ) ^ (-delta) * base (shift k) := by
        dsimp only [base]
        have hp : ((shift k : ℕ) : ℝ) ^ (-(1 + 2 * delta)) =
            ((shift k : ℕ) : ℝ) ^ (-delta) *
              ((shift k : ℕ) : ℝ) ^ (-(1 + delta)) := by
          rw [← Real.rpow_add (by positivity : (0 : ℝ) < (shift k : ℕ))]
          congr 1
          ring
        rw [hp]
        ring
      _ ≤ (X : ℝ) ^ (-delta) * base (shift k) :=
        mul_le_mul_of_nonneg_right hpow (by dsimp only [base]; positivity)
  have hmajor : Summable (fun k => (X : ℝ) ^ (-delta) * base (shift k)) :=
    hbaseShift.mul_left _
  have hshiftle : (∑' k, base (shift k)) ≤ ∑' n, base n := by
    exact Summable.tsum_le_tsum_of_inj shift hinj
      (fun n _ => by dsimp only [base]; positivity)
      (fun k => le_rfl) hbaseShift hbase
  have hnear := tsum_divisorSquare_rpow_le_near_one
    (by linarith : 1 < 1 + delta)
  calc
    (∑' k : ℕ, ((shift k : ℕ) : ℝ) *
        inghamMovingRightExplicitSquareMass delta X (shift k)) ≤
        ∑' k : ℕ, (X : ℝ) ^ (-delta) * base (shift k) :=
      hactual.tsum_le_tsum hterm hmajor
    _ = (X : ℝ) ^ (-delta) * ∑' k, base (shift k) := by
      rw [hbaseShift.tsum_mul_left]
    _ ≤ (X : ℝ) ^ (-delta) * ∑' n, base n :=
      mul_le_mul_of_nonneg_left hshiftle (Real.rpow_nonneg (Nat.cast_nonneg X) _)
    _ ≤ (X : ℝ) ^ (-delta) * (1 + 1 / delta) ^ 4 := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg X) _)
      simpa only [base, add_sub_cancel_left] using hnear

theorem tsum_inghamMovingRightExplicitSquareMass_le_explicit
    {delta : ℝ} (hdelta : 0 < delta) {X : ℕ} (hX : 1 ≤ X) :
    ∑' n : ℕ, inghamMovingRightExplicitSquareMass delta X n ≤
      (X : ℝ) ^ (-(1 + delta)) * (1 + 1 / delta) ^ 4 := by
  rw [tsum_inghamMovingRightExplicit_eq_shift hdelta hX]
  let base : ℕ → ℝ := fun n =>
    (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + delta))
  let shift : ℕ → ℕ := fun k => k + X + 1
  have hinj : Function.Injective shift := by
    intro a b hab
    dsimp only [shift] at hab
    omega
  have hbase : Summable base := by
    simpa only [base] using
      summable_divisorSquare_mul_rpow_neg (by linarith : 1 < 1 + delta)
  have hbaseShift : Summable (fun k => base (shift k)) := hbase.comp_injective hinj
  have hactual : Summable (fun k : ℕ =>
      inghamMovingRightExplicitSquareMass delta X (shift k)) := by
    have hbeta : 1 < 1 + delta := by linarith
    have hs := summable_normSq_complexCoeff_moebiusZetaDefect_damped hX hbeta
    have hs' : Summable (inghamMovingRightExplicitSquareMass delta X) := by
      change Summable fun n : ℕ =>
        ‖complexCoeff (moebiusZetaDefect X) n *
          (((n : ℝ) ^ (-(1 + delta)) : ℝ) : ℂ)‖ ^ 2
      exact hs
    exact hs'.comp_injective hinj
  have hterm : ∀ k : ℕ,
      inghamMovingRightExplicitSquareMass delta X (shift k) ≤
        (X : ℝ) ^ (-(1 + delta)) * base (shift k) := by
    intro k
    have hn : 1 ≤ shift k := by dsimp only [shift]; omega
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    have hXn : (X : ℝ) ≤ (shift k : ℕ) := by
      exact_mod_cast (show X ≤ shift k by dsimp only [shift]; omega)
    have hpow : ((shift k : ℕ) : ℝ) ^ (-(1 + delta)) ≤
        (X : ℝ) ^ (-(1 + delta)) :=
      Real.rpow_le_rpow_of_nonpos hXR hXn (by linarith)
    calc
      inghamMovingRightExplicitSquareMass delta X (shift k) ≤
          ((shift k).divisors.card : ℝ) ^ 2 *
            ((shift k : ℕ) : ℝ) ^ (-(2 + 2 * delta)) :=
        inghamMovingRightExplicitSquareMass_le hX hn
      _ = ((shift k : ℕ) : ℝ) ^ (-(1 + delta)) * base (shift k) := by
        dsimp only [base]
        have hp : ((shift k : ℕ) : ℝ) ^ (-(2 + 2 * delta)) =
            ((shift k : ℕ) : ℝ) ^ (-(1 + delta)) *
              ((shift k : ℕ) : ℝ) ^ (-(1 + delta)) := by
          rw [← Real.rpow_add (by positivity : (0 : ℝ) < (shift k : ℕ))]
          congr 1
          ring
        rw [hp]
        ring
      _ ≤ (X : ℝ) ^ (-(1 + delta)) * base (shift k) :=
        mul_le_mul_of_nonneg_right hpow (by dsimp only [base]; positivity)
  have hmajor : Summable (fun k =>
      (X : ℝ) ^ (-(1 + delta)) * base (shift k)) := hbaseShift.mul_left _
  have hshiftle : (∑' k, base (shift k)) ≤ ∑' n, base n := by
    exact Summable.tsum_le_tsum_of_inj shift hinj
      (fun n _ => by dsimp only [base]; positivity)
      (fun k => le_rfl) hbaseShift hbase
  have hnear := tsum_divisorSquare_rpow_le_near_one
    (by linarith : 1 < 1 + delta)
  calc
    (∑' k : ℕ, inghamMovingRightExplicitSquareMass delta X (shift k)) ≤
        ∑' k : ℕ, (X : ℝ) ^ (-(1 + delta)) * base (shift k) :=
      hactual.tsum_le_tsum hterm hmajor
    _ = (X : ℝ) ^ (-(1 + delta)) * ∑' k, base (shift k) := by
      rw [hbaseShift.tsum_mul_left]
    _ ≤ (X : ℝ) ^ (-(1 + delta)) * ∑' n, base n :=
      mul_le_mul_of_nonneg_left hshiftle (Real.rpow_nonneg (Nat.cast_nonneg X) _)
    _ ≤ (X : ℝ) ^ (-(1 + delta)) * (1 + 1 / delta) ^ 4 := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg X) _)
      simpa only [base, add_sub_cancel_left] using hnear

theorem integral_Icc_normSq_inghamMollifiedError_movingRightEdge_symmetric_le_explicit
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ {X N : ℕ}, 1 ≤ X → 1 ≤ N →
      (∫ t in Set.Icc (-(N : ℝ)) (N : ℝ),
        ‖riemannZeta ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I) *
            inghamMollifier X ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I) - 1‖ ^ 2) ≤
        5 * Real.pi * Real.exp 1 *
            ((X : ℝ) ^ (-delta) * (1 + 1 / delta) ^ 4) +
          (5 * Real.pi / 2) *
            ((X : ℝ) ^ (-(1 + delta)) * (1 + 1 / delta) ^ 4) * (N : ℝ) := by
  intro X N hX hN
  let a : ℕ → ℂ := complexCoeff (moebiusZetaDefect X)
  have hbeta : 1 < 1 + delta := by linarith
  have habs := summable_norm_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hplain := summable_normSq_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hweighted := summable_weighted_normSq_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hbase := integral_Icc_normSq_LSeries_le_general_affine_infinite
    (a := a) (complexCoeff_moebiusZetaDefect_zero X) (1 + delta)
    habs hplain hweighted hNR
  have hsource (t : ℝ) :
      ‖LSeries a ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I)‖ =
        ‖riemannZeta ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I) *
          inghamMollifier X ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I) - 1‖ := by
    have hs : 1 < (((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I)).re := by
      simpa using hbeta
    rw [show a = complexCoeff (moebiusZetaDefect X) by rfl,
      LSeries_complexCoeff_moebiusZetaDefect_eq X hs]
    rw [show 1 - inghamMollifier X ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I) *
          riemannZeta ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I) =
        -(riemannZeta ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I) *
          inghamMollifier X ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I) - 1) by ring,
      norm_neg]
  have hW : (∑' n : ℕ, (n : ℝ) *
      ‖a n * (((n : ℝ) ^ (-(1 + delta)) : ℝ) : ℂ)‖ ^ 2) ≤
      (X : ℝ) ^ (-delta) * (1 + 1 / delta) ^ 4 := by
    simpa only [a, inghamMovingRightExplicitSquareMass] using
      tsum_inghamMovingRightExplicitWeightedSquareMass_le_explicit hdelta hX
  have hP : (∑' n : ℕ,
      ‖a n * (((n : ℝ) ^ (-(1 + delta)) : ℝ) : ℂ)‖ ^ 2) ≤
      (X : ℝ) ^ (-(1 + delta)) * (1 + 1 / delta) ^ 4 := by
    simpa only [a, inghamMovingRightExplicitSquareMass] using
      tsum_inghamMovingRightExplicitSquareMass_le_explicit hdelta hX
  calc
    (∫ t in Set.Icc (-(N : ℝ)) (N : ℝ),
      ‖riemannZeta ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I) *
          inghamMollifier X ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I) - 1‖ ^ 2) =
        ∫ t in Set.Icc (-(N : ℝ)) (N : ℝ),
          ‖LSeries a ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hsource]
    _ ≤ 5 * Real.pi * Real.exp 1 *
          (∑' n : ℕ, (n : ℝ) *
            ‖a n * (((n : ℝ) ^ (-(1 + delta)) : ℝ) : ℂ)‖ ^ 2) +
        (5 * Real.pi / 2) *
          (∑' n : ℕ,
            ‖a n * (((n : ℝ) ^ (-(1 + delta)) : ℝ) : ℂ)‖ ^ 2) * (N : ℝ) := hbase
    _ ≤ 5 * Real.pi * Real.exp 1 *
          ((X : ℝ) ^ (-delta) * (1 + 1 / delta) ^ 4) +
        (5 * Real.pi / 2) *
          ((X : ℝ) ^ (-(1 + delta)) * (1 + 1 / delta) ^ 4) * (N : ℝ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hW (by positivity))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hP (by positivity)) (by positivity))

theorem integral_Icc_normSq_inghamMollifiedError_movingRightEdge_le_explicit
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ {X : ℕ}, 1 ≤ X →
      (∫ t in Set.Icc (-(X : ℝ)) (X : ℝ),
        ‖riemannZeta ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I) *
            inghamMollifier X ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I) - 1‖ ^ 2) ≤
        (5 * Real.pi * Real.exp 1 + 5 * Real.pi / 2) *
          (1 + 1 / delta) ^ 4 * (X : ℝ) ^ (-delta) := by
  intro X hX
  have hmain :=
    integral_Icc_normSq_inghamMollifiedError_movingRightEdge_symmetric_le_explicit
      hdelta (X := X) (N := X) hX hX
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hpow : (X : ℝ) ^ (-(1 + delta)) * (X : ℝ) =
      (X : ℝ) ^ (-delta) := by
    calc
      (X : ℝ) ^ (-(1 + delta)) * (X : ℝ) =
          (X : ℝ) ^ (-(1 + delta)) * (X : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (X : ℝ) ^ (-(1 + delta) + 1) := by rw [Real.rpow_add hX0]
      _ = (X : ℝ) ^ (-delta) := by congr 1; ring
  calc
    _ ≤ 5 * Real.pi * Real.exp 1 *
          ((X : ℝ) ^ (-delta) * (1 + 1 / delta) ^ 4) +
        (5 * Real.pi / 2) *
          ((X : ℝ) ^ (-(1 + delta)) * (1 + 1 / delta) ^ 4) * (X : ℝ) := hmain
    _ = (5 * Real.pi * Real.exp 1 + 5 * Real.pi / 2) *
          (1 + 1 / delta) ^ 4 * (X : ℝ) ^ (-delta) := by
      rw [show (5 * Real.pi / 2) *
            ((X : ℝ) ^ (-(1 + delta)) * (1 + 1 / delta) ^ 4) * (X : ℝ) =
          (5 * Real.pi / 2) * (1 + 1 / delta) ^ 4 *
            ((X : ℝ) ^ (-(1 + delta)) * (X : ℝ)) by ring, hpow]
      ring

end

end RHTower.Sieve


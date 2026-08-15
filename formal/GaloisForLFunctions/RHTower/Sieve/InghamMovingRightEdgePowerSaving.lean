import GaloisForLFunctions.RHTower.Sieve.InghamRightEdgePowerSaving

open Complex MeasureTheory Set Finset ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

private noncomputable def inghamMovingRightSquareMass
    (delta : ℝ) (X n : ℕ) : ℝ :=
  ‖complexCoeff (moebiusZetaDefect X) n *
      (((n : ℝ) ^ (-(1 + delta)) : ℝ) : ℂ)‖ ^ 2

private theorem inghamMovingRightSquareMass_zero_of_le
    {delta : ℝ} {X n : ℕ} (hn : n ≤ X) :
    inghamMovingRightSquareMass delta X n = 0 := by
  have hz : moebiusZetaDefect X n = 0 :=
    (moebiusZetaDefect_vanishesBelow X) n (by omega)
  simp [inghamMovingRightSquareMass, hz, complexCoeff]

private theorem inghamMovingRightSquareMass_le
    {delta C : ℝ}
    (hdiv : ∀ n : ℕ, 1 ≤ n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (delta / 2))
    {X n : ℕ} (hX : 1 ≤ X) (hn : 1 ≤ n) :
    inghamMovingRightSquareMass delta X n ≤
      C ^ 2 * (n : ℝ) ^ (-(2 + delta)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcoeff := norm_complexCoeff_moebiusZetaDefect_le_card_divisors hX n
  have hcoeff' : ‖complexCoeff (moebiusZetaDefect X) n‖ ≤
      C * (n : ℝ) ^ (delta / 2) := hcoeff.trans (hdiv n hn)
  unfold inghamMovingRightSquareMass
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hnR.le _), mul_pow]
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hcoeff' 2
  have hpowSmall : ((n : ℝ) ^ (delta / 2)) ^ (2 : ℕ) =
      (n : ℝ) ^ delta := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    congr 1
    ring
  have hpowRight : ((n : ℝ) ^ (-(1 + delta))) ^ (2 : ℕ) =
      (n : ℝ) ^ (-2 * (1 + delta)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    congr 1
    ring
  calc
    ‖complexCoeff (moebiusZetaDefect X) n‖ ^ 2 *
          ((n : ℝ) ^ (-(1 + delta))) ^ 2
        ≤ (C * (n : ℝ) ^ (delta / 2)) ^ 2 *
          ((n : ℝ) ^ (-(1 + delta))) ^ 2 :=
      mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
    _ = C ^ 2 * (n : ℝ) ^ (-(2 + delta)) := by
      rw [mul_pow, hpowSmall, hpowRight]
      calc
        C ^ 2 * (n : ℝ) ^ delta * (n : ℝ) ^ (-2 * (1 + delta)) =
            C ^ 2 * ((n : ℝ) ^ delta * (n : ℝ) ^ (-2 * (1 + delta))) := by ring
        _ = C ^ 2 * (n : ℝ) ^ (-(2 + delta)) := by
          rw [← Real.rpow_add hnR]
          congr 2
          ring

private theorem inghamMovingRightWeightedSquareMass_le
    {delta C : ℝ}
    (hdiv : ∀ n : ℕ, 1 ≤ n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (delta / 2))
    {X n : ℕ} (hX : 1 ≤ X) (hn : 1 ≤ n) :
    (n : ℝ) * inghamMovingRightSquareMass delta X n ≤
      C ^ 2 * (n : ℝ) ^ (-(1 + delta)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := inghamMovingRightSquareMass_le hdiv hX hn
  calc
    (n : ℝ) * inghamMovingRightSquareMass delta X n ≤
        (n : ℝ) * (C ^ 2 * (n : ℝ) ^ (-(2 + delta))) :=
      mul_le_mul_of_nonneg_left h hnR.le
    _ = C ^ 2 * (n : ℝ) ^ (-(1 + delta)) := by
      calc
        (n : ℝ) * (C ^ 2 * (n : ℝ) ^ (-(2 + delta))) =
            C ^ 2 * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(2 + delta))) := by
          rw [Real.rpow_one]
          ring
        _ = C ^ 2 * (n : ℝ) ^ (-(1 + delta)) := by
          rw [← Real.rpow_add hnR]
          congr 2
          ring

private theorem tsum_inghamMovingRightSquareMass_eq_shift
    {delta : ℝ} (hdelta : 0 < delta) {X : ℕ} (hX : 1 ≤ X) :
    ∑' n : ℕ, inghamMovingRightSquareMass delta X n =
      ∑' k : ℕ, inghamMovingRightSquareMass delta X (k + X + 1) := by
  have hbeta : 1 < 1 + delta := by linarith
  have hs := summable_normSq_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hs' : Summable (inghamMovingRightSquareMass delta X) := by
    change Summable (fun n : ℕ =>
      ‖complexCoeff (moebiusZetaDefect X) n *
        (((n : ℝ) ^ (-(1 + delta)) : ℝ) : ℂ)‖ ^ 2)
    exact hs
  have hsplit := hs'.sum_add_tsum_nat_add (X + 1)
  have hzero : ∑ n ∈ Finset.range (X + 1), inghamMovingRightSquareMass delta X n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact inghamMovingRightSquareMass_zero_of_le
      (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hn))
  rw [hzero, zero_add] at hsplit
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit.symm

private theorem tsum_inghamMovingRightWeightedSquareMass_eq_shift
    {delta : ℝ} (hdelta : 0 < delta) {X : ℕ} (hX : 1 ≤ X) :
    ∑' n : ℕ, (n : ℝ) * inghamMovingRightSquareMass delta X n =
      ∑' k : ℕ, ((k + X + 1 : ℕ) : ℝ) *
        inghamMovingRightSquareMass delta X (k + X + 1) := by
  have hbeta : 1 < 1 + delta := by linarith
  have hs := summable_weighted_normSq_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hs' : Summable (fun n : ℕ =>
      (n : ℝ) * inghamMovingRightSquareMass delta X n) := by
    simpa only [inghamMovingRightSquareMass] using hs
  have hsplit := hs'.sum_add_tsum_nat_add (X + 1)
  have hzero : ∑ n ∈ Finset.range (X + 1),
      (n : ℝ) * inghamMovingRightSquareMass delta X n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [inghamMovingRightSquareMass_zero_of_le
      (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hn)), mul_zero]
  rw [hzero, zero_add] at hsplit
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit.symm

private theorem tsum_inghamMovingRightSquareMass_le
    {delta C : ℝ} (hdelta : 0 < delta)
    (hdiv : ∀ n : ℕ, 1 ≤ n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (delta / 2))
    {X : ℕ} (hX : 1 ≤ X) :
    ∑' n : ℕ, inghamMovingRightSquareMass delta X n ≤
      C ^ 2 * (X : ℝ) ^ (-(1 + delta)) / (1 + delta) := by
  rw [tsum_inghamMovingRightSquareMass_eq_shift hdelta hX]
  have hterm : ∀ k : ℕ,
      inghamMovingRightSquareMass delta X (k + X + 1) ≤
        C ^ 2 * (((k + X + 1 : ℕ) : ℝ) ^ (-(2 + delta))) := by
    intro k
    exact inghamMovingRightSquareMass_le hdiv hX (by omega)
  have hp : 1 < 2 + delta := by linarith
  have hsum : Summable (fun k : ℕ =>
      C ^ 2 * (((k + X + 1 : ℕ) : ℝ) ^ (-(2 + delta)))) :=
    ((summable_nat_add_iff (X + 1)).2 (summable_nat_rpow_neg hp)).mul_left _
  have hbeta : 1 < 1 + delta := by linarith
  have hbase := summable_normSq_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hinj : Function.Injective (fun k : ℕ => k + X + 1) := by
    intro a b hab
    exact Nat.add_right_cancel (Nat.add_right_cancel hab)
  have hsmall : Summable (fun k : ℕ =>
      inghamMovingRightSquareMass delta X (k + X + 1)) := by
    apply (hbase.comp_injective hinj).congr
    intro k
    rfl
  refine (Summable.tsum_le_tsum hterm hsmall hsum).trans ?_
  calc
    (∑' i : ℕ, C ^ 2 * (((i + X + 1 : ℕ) : ℝ) ^ (-(2 + delta)))) =
        C ^ 2 * ∑' i : ℕ, (((i + X + 1 : ℕ) : ℝ) ^ (-(2 + delta))) :=
      tsum_mul_left
    _ ≤ C ^ 2 * ((X : ℝ) ^ (-(1 + delta)) / (1 + delta)) :=
      mul_le_mul_of_nonneg_left (by
        have htail := tsum_tail_rpow_neg_le hp hX
        have hexp : 1 - (2 + delta) = -(1 + delta) := by ring
        have hden : (2 + delta) - 1 = 1 + delta := by ring
        rw [hexp, hden] at htail
        simpa only [Nat.cast_add, Nat.cast_one] using htail) (sq_nonneg _)
    _ = C ^ 2 * (X : ℝ) ^ (-(1 + delta)) / (1 + delta) := by ring

private theorem tsum_inghamMovingRightWeightedSquareMass_le
    {delta C : ℝ} (hdelta : 0 < delta)
    (hdiv : ∀ n : ℕ, 1 ≤ n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (delta / 2))
    {X : ℕ} (hX : 1 ≤ X) :
    ∑' n : ℕ, (n : ℝ) * inghamMovingRightSquareMass delta X n ≤
      C ^ 2 * (X : ℝ) ^ (-delta) / delta := by
  rw [tsum_inghamMovingRightWeightedSquareMass_eq_shift hdelta hX]
  have hterm : ∀ k : ℕ,
      ((k + X + 1 : ℕ) : ℝ) * inghamMovingRightSquareMass delta X (k + X + 1) ≤
        C ^ 2 * (((k + X + 1 : ℕ) : ℝ) ^ (-(1 + delta))) := by
    intro k
    exact inghamMovingRightWeightedSquareMass_le hdiv hX (by omega)
  have hp : 1 < 1 + delta := by linarith
  have hsum : Summable (fun k : ℕ =>
      C ^ 2 * (((k + X + 1 : ℕ) : ℝ) ^ (-(1 + delta)))) :=
    ((summable_nat_add_iff (X + 1)).2 (summable_nat_rpow_neg hp)).mul_left _
  have hbase := summable_weighted_normSq_complexCoeff_moebiusZetaDefect_damped hX hp
  have hinj : Function.Injective (fun k : ℕ => k + X + 1) := by
    intro a b hab
    exact Nat.add_right_cancel (Nat.add_right_cancel hab)
  have hsmall : Summable (fun k : ℕ =>
      ((k + X + 1 : ℕ) : ℝ) * inghamMovingRightSquareMass delta X (k + X + 1)) := by
    apply (hbase.comp_injective hinj).congr
    intro k
    rfl
  refine (Summable.tsum_le_tsum hterm hsmall hsum).trans ?_
  calc
    (∑' i : ℕ, C ^ 2 * (((i + X + 1 : ℕ) : ℝ) ^ (-(1 + delta)))) =
        C ^ 2 * ∑' i : ℕ, (((i + X + 1 : ℕ) : ℝ) ^ (-(1 + delta))) :=
      tsum_mul_left
    _ ≤ C ^ 2 * ((X : ℝ) ^ (-delta) / delta) :=
      mul_le_mul_of_nonneg_left (by
        have htail := tsum_tail_rpow_neg_le hp hX
        have hexp : 1 - (1 + delta) = -delta := by ring
        have hden : (1 + delta) - 1 = delta := by ring
        rw [hexp, hden] at htail
        simpa only [Nat.cast_add, Nat.cast_one] using htail) (sq_nonneg _)
    _ = C ^ 2 * (X : ℝ) ^ (-delta) / delta := by ring

/-- Affine moving-right-edge mean square.  Coefficient vanishing through `X` gives the weighted
mass saving `X^{-delta}` and the plain-mass saving `X^{-1-delta}` uniformly in the height `N`. -/
theorem exists_integral_Icc_normSq_inghamMollifiedError_movingRightEdge_symmetric_le
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ {X N : ℕ}, 1 ≤ X → 1 ≤ N →
      (∫ t in Set.Icc (-(N : ℝ)) (N : ℝ),
        ‖riemannZeta ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I) *
            inghamMollifier X ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I) - 1‖ ^ 2) ≤
        A * (X : ℝ) ^ (-delta) +
          B * (X : ℝ) ^ (-(1 + delta)) * (N : ℝ) := by
  obtain ⟨C, hC, hdiv⟩ := _root_.RHTower.card_divisors_le_const_mul_rpow
    (show 0 < delta / 2 by linarith)
  let A : ℝ := 5 * Real.pi * Real.exp 1 * (C ^ 2 / delta)
  let B : ℝ := (5 * Real.pi / 2) * (C ^ 2 / (1 + delta))
  have hA : 0 < A := by dsimp only [A]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨A, B, hA, hB, ?_⟩
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
      C ^ 2 * (X : ℝ) ^ (-delta) / delta := by
    simpa only [a, inghamMovingRightSquareMass] using
      tsum_inghamMovingRightWeightedSquareMass_le hdelta hdiv hX
  have hP : (∑' n : ℕ,
      ‖a n * (((n : ℝ) ^ (-(1 + delta)) : ℝ) : ℂ)‖ ^ 2) ≤
      C ^ 2 * (X : ℝ) ^ (-(1 + delta)) / (1 + delta) := by
    simpa only [a, inghamMovingRightSquareMass] using
      tsum_inghamMovingRightSquareMass_le hdelta hdiv hX
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
          (C ^ 2 * (X : ℝ) ^ (-delta) / delta) +
        (5 * Real.pi / 2) *
          (C ^ 2 * (X : ℝ) ^ (-(1 + delta)) / (1 + delta)) * (N : ℝ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hW (by positivity))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hP (by positivity)) (by positivity))
    _ = A * (X : ℝ) ^ (-delta) +
          B * (X : ℝ) ^ (-(1 + delta)) * (N : ℝ) := by
      dsimp only [A, B]
      ring

/-- Every moving right edge `1 + delta` has an `X^{-delta}` mean-square saving.  The constant may
depend on `delta`, which is exactly the quantifier structure needed for a zero-density exponent
function. -/
theorem exists_integral_Icc_normSq_inghamMollifiedError_movingRightEdge_le
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ K : ℝ, 0 < K ∧ ∀ {X : ℕ}, 1 ≤ X →
      (∫ t in Set.Icc (-(X : ℝ)) (X : ℝ),
        ‖riemannZeta ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I) *
            inghamMollifier X ((((1 + delta : ℝ) : ℂ)) + (t : ℝ) * I) - 1‖ ^ 2) ≤
        K * (X : ℝ) ^ (-delta) := by
  obtain ⟨A, B, hA, hB, hmean⟩ :=
    exists_integral_Icc_normSq_inghamMollifiedError_movingRightEdge_symmetric_le hdelta
  let K : ℝ := A + B
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro X hX
  have hmain := hmean hX hX
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
    _ ≤ A * (X : ℝ) ^ (-delta) +
        B * (X : ℝ) ^ (-(1 + delta)) * (X : ℝ) := hmain
    _ = K * (X : ℝ) ^ (-delta) := by
      dsimp only [K]
      rw [show B * (X : ℝ) ^ (-(1 + delta)) * (X : ℝ) =
          B * ((X : ℝ) ^ (-(1 + delta)) * (X : ℝ)) by ring, hpow]
      ring

end


end RHTower.Sieve

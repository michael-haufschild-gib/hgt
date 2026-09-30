import GaloisForLFunctions.RHTower.LiEvenCrossEulerThirdMassRemainder
import GaloisForLFunctions.RHTower.LiEvenCrossEulerFirstNegativeOrder

/-!
# The positive third source term delays the first negative Euler order

The complete later tail has a cubic bound on the same scale that makes the
third source term quadratic. This proves strict positivity at every natural
order at or below the exact two-term crossover, including integer ties.
-/

namespace RHTower

noncomputable section

/-- A cubic bound for the complete tail after the positive third source term. -/
theorem abs_liEvenCrossEulerThirdMassTail_le_cubic_scale
    {v : ℝ} (hv : 0 ≤ v) (k : ℕ)
    (hq : (3 : ℝ) ^ k * v / 150 ≤ 1 / 8) :
    |liEvenCrossEulerThirdMassTail v k| ≤
      32 * xiShiftAbsoluteMass 0 * ((3 : ℝ) ^ k * v / 150) ^ 3 := by
  have hp : (2 : ℝ) ^ k * v / 150 ≤ 1 / 8 := by
    apply le_trans ?_ hq
    gcongr
    norm_num
  have hpow : ((4 : ℝ) ^ k) ^ 2 ≤ ((3 : ℝ) ^ k) ^ 3 := by
    have hfour : ((4 : ℝ) ^ k) ^ 2 = (16 : ℝ) ^ k := by
      rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
      norm_num
    have hthree : ((3 : ℝ) ^ k) ^ 3 = (27 : ℝ) ^ k := by
      rw [← pow_mul, Nat.mul_comm k 3, pow_mul]
      norm_num
    rw [hfour, hthree]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hA := xiShiftAbsoluteMass_nonneg 0
  calc
    |liEvenCrossEulerThirdMassTail v k| ≤
        32 * xiShiftAbsoluteMass 0 * ((4 : ℝ) ^ k * v) ^ 2 * v / 150 ^ 3 :=
      abs_liEvenCrossEulerThirdMassTail_le hv k hp
    _ = (32 * xiShiftAbsoluteMass 0 / 150 ^ 3) * ((4 : ℝ) ^ k) ^ 2 * v ^ 3 := by ring
    _ ≤ (32 * xiShiftAbsoluteMass 0 / 150 ^ 3) * ((3 : ℝ) ^ k) ^ 3 * v ^ 3 := by gcongr
    _ = 32 * xiShiftAbsoluteMass 0 * ((3 : ℝ) ^ k * v / 150) ^ 3 := by ring

/-- Literal source positivity holds uniformly at every order below the two-term center. -/
theorem liEvenCrossFirstCurrentEvenEulerJet_eventually_pos_le_crossover :
    ∀ᶠ v : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ k : ℕ,
      (k : ℝ) ≤ liEvenCrossEulerCrossoverCenter v →
        0 < liEvenCrossFirstCurrentEvenEulerJet v k := by
  let A : ℝ := xiShiftAbsoluteMass 0
  let M : ℝ := normalizedPrimeArchMoment 2
  let C : ℝ := liEvenCrossEulerCrossoverOffset
  let η : ℝ := min (1 / 8) (9 * 150 ^ 2 * M / (32 * A))
  have hA : 0 < A := xiShiftAbsoluteMass_pos 0
  have hM : 0 < M := normalizedPrimeArchMoment_pos_of_le_eleven 2 (by omega)
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ := liEvenCrossEulerSmallMassHalfExponent_pos
  have hs : Filter.Tendsto
      (fun v : ℝ => (3 : ℝ) ^ C / 150 * v ^ liEvenCrossEulerSmallMassHalfExponent)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hp : Filter.Tendsto (fun v : ℝ => v ^ liEvenCrossEulerSmallMassHalfExponent)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa [Real.zero_rpow hδ.ne'] using
        ((Real.continuousAt_rpow_const 0 liEvenCrossEulerSmallMassHalfExponent
          (Or.inr hδ.le)).tendsto.mono_left nhdsWithin_le_nhds)
    simpa using tendsto_const_nhds.mul hp
  have hquarter : ∀ᶠ v : ℝ in nhdsWithin 0 (Set.Ioi 0), v < 1 / 4 :=
    (show ∀ᶠ v : ℝ in nhds 0, v < 1 / 4 from
      Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hquarter, hs.eventually (Iio_mem_nhds hη)]
    with v hv hquarter hsmall
  change 0 < v at hv
  intro k hk
  let q : ℝ := (3 : ℝ) ^ k * v / 150
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hwindow : (k : ℝ) ≤ -Real.log v / Real.log 4 + C := hk
  have hqη : q < η :=
    (liEvenCrossEulerTailScale_log_window_le hv C k hwindow).trans_lt hsmall
  have hq8 : q ≤ 1 / 8 := hqη.le.trans (min_le_left _ _)
  have hcoeff : 32 * A * q < 9 * 150 ^ 2 * M := by
    have h := hqη.trans_le (min_le_right _ _)
    have hh := (lt_div_iff₀ (by positivity : 0 < 32 * A)).1 h
    nlinarith
  have htail : |liEvenCrossEulerThirdMassTail v k| < 9 * 150 ^ 2 * M * q ^ 2 := by
    calc
      _ ≤ 32 * A * q ^ 3 := abs_liEvenCrossEulerThirdMassTail_le_cubic_scale hv.le k hq8
      _ = (32 * A * q) * q ^ 2 := by ring
      _ < (9 * 150 ^ 2 * M) * q ^ 2 :=
        mul_lt_mul_of_pos_right hcoeff (sq_pos_of_pos hq0)
  have hthird : (9 : ℝ) ^ (k + 1) * M * v ^ 2 = 9 * 150 ^ 2 * M * q ^ 2 := by
    have hpow : (9 : ℝ) ^ k = ((3 : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
      norm_num
    dsimp [q]
    rw [pow_succ, hpow]
    ring
  have hleading : (4 : ℝ) ^ (k + 1) * normalizedPrimeArchMoment 1 * v ≤
      normalizedPrimeArchMoment 0 := by
    have h1 := normalizedPrimeArchMoment_pos_of_le_eleven 1 (by omega)
    have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hk
    rw [Real.rpow_natCast] at hpow
    calc
      _ = (4 : ℝ) ^ k * (4 * normalizedPrimeArchMoment 1 * v) := by rw [pow_succ]; ring
      _ ≤ (4 : ℝ) ^ liEvenCrossEulerCrossoverCenter v *
          (4 * normalizedPrimeArchMoment 1 * v) := by gcongr
      _ = normalizedPrimeArchMoment 0 := liEvenCrossEulerCrossoverCenter_rpow_balance hv
  have hnormalized : 0 < liEvenCrossFirstCurrentEvenEulerJet v k / (2 * v) := by
    rw [liEvenCrossFirstCurrentEvenEulerJet_div_two_mul_mass_eq_three_terms hv hquarter.le]
    have hlow := (abs_lt.mp htail).1
    dsimp [M] at hthird
    rw [hthird]
    linarith
  have hden : 0 < 2 * v := by positivity
  simpa only [div_mul_cancel₀ _ hden.ne'] using mul_pos hnormalized hden

end

end RHTower

import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheReceiverIsTheChainOrbitOfTheReciprocal

/-!
# The first column of the chain is the receiver

Is the centred damping chain `C_η` bounded in the receiver norm `ℓ²`?  By
`TheReceiverIsTheChainOrbitOfTheReciprocal` a positive answer at `η` admits `η`.  This module
shows that the very first test of the question is already the receiver itself.

The first column of the chain — its value on the first state — is
(`centeredOperator_firstState_apply_eq`)

`(C_η e₁)(m − 1) = D_η(m)/m + ρ 2^{−η} (m mod 2)/(2m)`,   `D_η(m) = P_η(m) − 2^{−η} P_η(⌊m/2⌋)`,

the **dyadic difference** of the centred prefix `P_η` plus a term of size `1/m`.  The dyadic
difference loses nothing in the receiver norm: `D_η(m)/m` is square summable iff `P_η(m)/m` is
(`summable_dyadicDifference_iff`).  One direction is the two-to-one count of `⌊m/2⌋`
(`summable_floor_half_le`); the other inverts the difference by the geometric series
`P(m) = Σ_j 2^{−jη} D(⌊m/2^j⌋)` with a weighted Cauchy–Schwarz inequality.

Hence (`admits_iff_summable_firstColumn`): **the first column of `C_η` lies in `ℓ²` iff `η` is
admitted.**  An `ℓ²` bound for the centred chain is a uniform version, over its columns, of
admission statements for dilated sources; its first instance is RH-strength at cofinally small
damping (`riemannHypothesis_iff_firstColumn_summable`).
-/

open Finset Filter Topology
open scoped ZeroAtInfty
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### The first column -/

/-- The first state as a `c₀` vector. -/
def firstState : C₀(ℕ, ℝ) :=
  c0OfTendsto (fun n => if n = 0 then 1 else 0) (by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [show n ≠ 0 by omega])

theorem centeredOperator_firstState_apply {η : ℝ} (hη : 0 < η) (n : ℕ) :
    arithmeticDampingCenteredOperator hη firstState n =
      arithmeticDampingTransition η (n + 1) 1 - arithmeticDampingEntrance η 1 := by
  rw [arithmeticDampingCenteredOperator_apply]
  have : (fun k => arithmeticDampingCenteredRow η n k * firstState k) =
      fun k => if k = 0 then arithmeticDampingCenteredRow η n 0 else 0 := by
    funext k
    by_cases hk : k = 0
    · subst hk; simp [firstState]
    · simp [firstState, hk]
  rw [this, tsum_ite_eq]
  simp [arithmeticDampingCenteredRow]

/-- The dyadic difference of the centred prefix. -/
def dyadicDifference (η : ℝ) (m : ℕ) : ℝ :=
  RHTower.pmPowerDampedCenteredDivisorPrefix η m -
    (2 : ℝ) ^ (-η) * RHTower.pmPowerDampedCenteredDivisorPrefix η (m / 2)

theorem centeredPrefix_zero (η : ℝ) : RHTower.pmPowerDampedCenteredDivisorPrefix η 0 = 0 := by
  simp [RHTower.pmPowerDampedCenteredDivisorPrefix]

theorem dyadicDifference_zero (η : ℝ) : dyadicDifference η 0 = 0 := by
  simp [dyadicDifference]

/-- **The first column is the dyadic difference of the source**, up to a term of size `1/m`. -/
theorem centeredOperator_firstState_apply_eq {η : ℝ} (hη : 0 < η) (n : ℕ) :
    arithmeticDampingCenteredOperator hη firstState n =
      dyadicDifference η (n + 1) / ((n : ℝ) + 1) +
        (RHTower.pmPowerDampedDivisorDensity η).re * (2 : ℝ) ^ (-η) *
          (((n + 1) % 2 : ℕ) : ℝ) / (2 * ((n : ℝ) + 1)) := by
  rw [centeredOperator_firstState_apply]
  set ρ := (RHTower.pmPowerDampedDivisorDensity η).re
  set m := n + 1 with hm
  have hpre : ∀ k : ℕ, arithmeticDampingPrefix η k =
      RHTower.pmPowerDampedCenteredDivisorPrefix η k + ρ * k := by
    intro k
    rw [RHTower.pmPowerDampedCenteredDivisorPrefix_eq]
    unfold arithmeticDampingPrefix
    ring
  have htr : arithmeticDampingTransition η m 1 =
      (arithmeticDampingPrefix η m - (2 : ℝ) ^ (-η) * arithmeticDampingPrefix η (m / 2)) / m := by
    unfold arithmeticDampingTransition
    simp only [Nat.cast_one, Real.one_rpow, one_mul, Nat.div_one]
    norm_num
    ring
  have hen : arithmeticDampingEntrance η 1 = ρ * (1 - (2 : ℝ) ^ (-1 - η)) := by
    unfold arithmeticDampingEntrance
    simp only [Nat.cast_one, Real.one_rpow, mul_one]
    norm_num
    exact Or.inl rfl
  have hhalf : ((m / 2 : ℕ) : ℝ) = ((m : ℝ) - ((m % 2 : ℕ) : ℝ)) / 2 := by
    have := Nat.div_add_mod m 2
    have h : (2 : ℝ) * ((m / 2 : ℕ) : ℝ) + ((m % 2 : ℕ) : ℝ) = m := by exact_mod_cast this
    linarith
  have h2 : (2 : ℝ) ^ (-1 - η) = (2 : ℝ) ^ (-η) / 2 := by
    rw [show (-1 - η) = -η + (-1) by ring, Real.rpow_add (by norm_num), Real.rpow_neg_one]
    ring
  rw [htr, hen, hpre, hpre, hhalf, h2]
  unfold dyadicDifference
  have hmpos : (0 : ℝ) < m := by positivity
  have hmc : (m : ℝ) = (n : ℝ) + 1 := by rw [hm]; push_cast; ring
  rw [← hmc]
  field_simp
  ring

/-! ### The dyadic difference loses nothing in the receiver norm -/

/-- Summing a nonnegative profile at `⌊m/2⌋` against `1/m²` costs at most half its own sum. -/
theorem sum_range_floor_half_le (h : ℕ → ℝ) (hh : ∀ k, 0 ≤ h k) (hh0 : h 0 = 0) (K : ℕ) :
    ∑ m ∈ range (2 * K), h (m / 2) / (m : ℝ) ^ 2 ≤ (1 / 2) * ∑ k ∈ range K, h k / (k : ℝ) ^ 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have e1 : (2 * K) / 2 = K := by omega
    have e2 : (2 * K + 1) / 2 = K := by omega
    rw [e1, e2]
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp [hh0]
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have hb : h K / ((2 * K : ℕ) : ℝ) ^ 2 + h K / ((2 * K + 1 : ℕ) : ℝ) ^ 2 ≤
        (1 / 2) * (h K / (K : ℝ) ^ 2) := by
      have hk := hh K
      push_cast
      have h1 : h K / (2 * (K : ℝ)) ^ 2 = (1 / 4) * (h K / (K : ℝ) ^ 2) := by
        field_simp; ring
      have h2 : h K / (2 * (K : ℝ) + 1) ^ 2 ≤ (1 / 4) * (h K / (K : ℝ) ^ 2) := by
        rw [div_le_iff₀ (by positivity)]
        have : (1 / 4) * (h K / (K : ℝ) ^ 2) * (2 * (K : ℝ) + 1) ^ 2 =
            h K * ((2 * K + 1) ^ 2 / (4 * K ^ 2)) := by field_simp
        rw [this]
        have hr : (1 : ℝ) ≤ (2 * K + 1) ^ 2 / (4 * K ^ 2) := by
          rw [le_div_iff₀ (by positivity)]; nlinarith
        nlinarith
      linarith
    linarith

theorem summable_floor_half_le {h : ℕ → ℝ} (hh : ∀ k, 0 ≤ h k) (hh0 : h 0 = 0)
    (hs : Summable fun k => h k / (k : ℝ) ^ 2) :
    Summable (fun m => h (m / 2) / (m : ℝ) ^ 2) ∧
      ∑' m, h (m / 2) / (m : ℝ) ^ 2 ≤ (1 / 2) * ∑' k, h k / (k : ℝ) ^ 2 := by
  have hnn : ∀ m, 0 ≤ h (m / 2) / (m : ℝ) ^ 2 := fun m => div_nonneg (hh _) (sq_nonneg _)
  have hknn : ∀ k, 0 ≤ h k / (k : ℝ) ^ 2 := fun k => div_nonneg (hh _) (sq_nonneg _)
  have hpart : ∀ N, ∑ m ∈ range N, h (m / 2) / (m : ℝ) ^ 2 ≤ (1 / 2) * ∑' k, h k / (k : ℝ) ^ 2 := by
    intro N
    calc ∑ m ∈ range N, h (m / 2) / (m : ℝ) ^ 2 ≤ ∑ m ∈ range (2 * N), h (m / 2) / (m : ℝ) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun m _ _ => hnn m
      _ ≤ (1 / 2) * ∑ k ∈ range N, h k / (k : ℝ) ^ 2 := sum_range_floor_half_le h hh hh0 N
      _ ≤ _ := mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ fun k _ => hknn k) (by norm_num)
  exact ⟨summable_of_sum_range_le hnn hpart, Real.tsum_le_of_sum_range_le hnn hpart⟩

/-- Iterated halving: `Σ_m h(⌊m/2^j⌋)/m² ≤ 2^{−j} Σ_k h(k)/k²`. -/
theorem summable_floor_pow_le {h : ℕ → ℝ} (hh : ∀ k, 0 ≤ h k) (hh0 : h 0 = 0)
    (hs : Summable fun k => h k / (k : ℝ) ^ 2) (j : ℕ) :
    Summable (fun m => h (m / 2 ^ j) / (m : ℝ) ^ 2) ∧
      ∑' m, h (m / 2 ^ j) / (m : ℝ) ^ 2 ≤ (1 / 2) ^ j * ∑' k, h k / (k : ℝ) ^ 2 := by
  induction j with
  | zero => simpa using hs
  | succ j ih =>
    have hh' : ∀ k, 0 ≤ h (k / 2 ^ j) := fun k => hh _
    have hh0' : h (0 / 2 ^ j) = 0 := by simpa using hh0
    obtain ⟨hs2, hle2⟩ := summable_floor_half_le hh' hh0' ih.1
    have e : ∀ m : ℕ, m / 2 / 2 ^ j = m / 2 ^ (j + 1) := by
      intro m; rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
    simp only [e] at hs2 hle2
    refine ⟨hs2, hle2.trans ?_⟩
    rw [pow_succ, mul_comm ((1 / 2 : ℝ) ^ j), mul_assoc]
    exact mul_le_mul_of_nonneg_left ih.2 (by norm_num)

/-- The square of a profile at `m` against `1/m²`. -/
private def sqProfile (u : ℕ → ℝ) (m : ℕ) : ℝ := u m ^ 2 / (m : ℝ) ^ 2

private theorem summable_sq_add {a b : ℕ → ℝ} (ha : Summable fun m => a m ^ 2)
    (hb : Summable fun m => b m ^ 2) : Summable fun m => (a m + b m) ^ 2 :=
  Summable.of_nonneg_of_le (fun m => sq_nonneg _)
    (fun m => by nlinarith [sq_nonneg (a m - b m)]) ((ha.add hb).mul_left 2)

/-- `P(m) = Σ_{j<J} 2^{−jη} D(⌊m/2^j⌋)` once `2^J > m`. -/
theorem centeredPrefix_eq_sum_dyadicDifference (η : ℝ) (m J : ℕ) (hJ : m < 2 ^ J) :
    RHTower.pmPowerDampedCenteredDivisorPrefix η m =
      ∑ j ∈ range J, ((2 : ℝ) ^ (-η)) ^ j * dyadicDifference η (m / 2 ^ j) := by
  have htel : ∀ J : ℕ, RHTower.pmPowerDampedCenteredDivisorPrefix η m -
      ((2 : ℝ) ^ (-η)) ^ J * RHTower.pmPowerDampedCenteredDivisorPrefix η (m / 2 ^ J) =
      ∑ j ∈ range J, ((2 : ℝ) ^ (-η)) ^ j * dyadicDifference η (m / 2 ^ j) := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [Finset.sum_range_succ, ← ih]
      unfold dyadicDifference
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
      ring
  have := htel J
  rw [Nat.div_eq_of_lt hJ, centeredPrefix_zero, mul_zero, sub_zero] at this
  exact this

/-- Partial geometric sums are below the full sum. -/
private theorem geom_partial_le {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) (T : ℕ) :
    ∑ j ∈ range T, lam ^ j ≤ 1 / (1 - lam) := by
  rw [geom_sum_eq hl1.ne T]
  have h1 : 0 < 1 - lam := by linarith
  have hlT : 0 ≤ lam ^ T := by positivity
  rw [show (lam ^ T - 1) / (lam - 1) = (1 - lam ^ T) / (1 - lam) by
    rw [← neg_div_neg_eq]; ring_nf]
  exact div_le_div_of_nonneg_right (by linarith) h1.le

/-- **The dyadic difference loses nothing**: `D(m)/m ∈ ℓ²` iff `P(m)/m ∈ ℓ²`. -/
theorem summable_dyadicDifference_iff {η : ℝ} (hη : 0 < η) :
    (Summable fun m : ℕ => dyadicDifference η m ^ 2 / (m : ℝ) ^ 2) ↔
      Summable fun m : ℕ => RHTower.pmPowerDampedCenteredDivisorPrefix η m ^ 2 / (m : ℝ) ^ 2 := by
  set P := RHTower.pmPowerDampedCenteredDivisorPrefix η with hP
  set q : ℝ := (2 : ℝ) ^ (-η) with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  constructor
  · intro hD
    -- `P² ≤ (Σ_j λ^j) Σ_j λ^{−j} q^{2j} D(⌊m/2^j⌋)²` with `λ = q · 2^{−1/2}`
    set lam : ℝ := q * (2 : ℝ) ^ (-(1 / 2 : ℝ)) with hlam
    have hl0 : 0 < lam := by positivity
    have hl1 : lam < 1 := by
      have : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
      nlinarith
    have hratio : q ^ 2 / lam * (1 / 2) = lam := by
      have h22 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) * (2 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
        rw [← Real.rpow_add (by norm_num)]; norm_num
      rw [hlam]
      field_simp
      nlinarith [h22]
    set SD := ∑' k, dyadicDifference η k ^ 2 / (k : ℝ) ^ 2 with hSD
    have hDnn : ∀ k, 0 ≤ dyadicDifference η k ^ 2 := fun k => sq_nonneg _
    have hD0 : dyadicDifference η 0 ^ 2 = 0 := by rw [dyadicDifference_zero]; norm_num
    have hfloor := fun j => summable_floor_pow_le (h := fun k => dyadicDifference η k ^ 2)
      hDnn hD0 hD j
    have hpart : ∀ T : ℕ, ∑ m ∈ range T, P m ^ 2 / (m : ℝ) ^ 2 ≤
        (1 / (1 - lam)) * (1 / (1 - lam)) * SD := by
      intro T
      -- each `P(m)`, `m < T`, is a sum over `j < T`
      have hJ : ∀ m ∈ range T, m < 2 ^ T := fun m hm =>
        lt_of_lt_of_le (mem_range.mp hm) (Nat.lt_two_pow_self).le
      have hcs : ∀ m ∈ range T, P m ^ 2 ≤ (1 / (1 - lam)) *
          ∑ j ∈ range T, (q ^ 2 / lam) ^ j * dyadicDifference η (m / 2 ^ j) ^ 2 := by
        intro m hm
        rw [hP, centeredPrefix_eq_sum_dyadicDifference η m T (hJ m hm)]
        have h1 := sum_mul_sq_le_sq_mul_sq (range T) (fun j => Real.sqrt (lam ^ j))
          (fun j => q ^ j * dyadicDifference η (m / 2 ^ j) / Real.sqrt (lam ^ j))
        have hsq : ∀ j, Real.sqrt (lam ^ j) ^ 2 = lam ^ j := fun j => Real.sq_sqrt (by positivity)
        have hne : ∀ j, Real.sqrt (lam ^ j) ≠ 0 := fun j => (Real.sqrt_pos.mpr (by positivity)).ne'
        have e1 : ∑ j ∈ range T, Real.sqrt (lam ^ j) *
            (q ^ j * dyadicDifference η (m / 2 ^ j) / Real.sqrt (lam ^ j)) =
            ∑ j ∈ range T, q ^ j * dyadicDifference η (m / 2 ^ j) :=
          sum_congr rfl fun j _ => by field_simp
        have e2 : ∀ j, (q ^ j * dyadicDifference η (m / 2 ^ j) / Real.sqrt (lam ^ j)) ^ 2 =
            (q ^ 2 / lam) ^ j * dyadicDifference η (m / 2 ^ j) ^ 2 := by
          intro j
          have hqj : (q ^ 2 / lam) ^ j = (q ^ j) ^ 2 / lam ^ j := by
            rw [div_pow, ← pow_mul, ← pow_mul, mul_comm 2 j]
          rw [div_pow, hsq, hqj, mul_pow]
          ring
        rw [e1] at h1
        simp only [hsq, e2] at h1
        have hgeo : ∑ j ∈ range T, lam ^ j ≤ 1 / (1 - lam) := geom_partial_le hl0 hl1 T
        have hnn : 0 ≤ ∑ j ∈ range T, (q ^ 2 / lam) ^ j * dyadicDifference η (m / 2 ^ j) ^ 2 :=
          sum_nonneg fun j _ => by positivity
        calc (∑ j ∈ range T, q ^ j * dyadicDifference η (m / 2 ^ j)) ^ 2 ≤ _ := h1
          _ ≤ _ := mul_le_mul_of_nonneg_right hgeo hnn
      calc ∑ m ∈ range T, P m ^ 2 / (m : ℝ) ^ 2
          ≤ ∑ m ∈ range T, (1 / (1 - lam)) *
              ∑ j ∈ range T, (q ^ 2 / lam) ^ j * dyadicDifference η (m / 2 ^ j) ^ 2 / (m : ℝ) ^ 2 := by
            refine sum_le_sum fun m hm => ?_
            rw [← sum_div, ← mul_div_assoc]
            exact div_le_div_of_nonneg_right (hcs m hm) (sq_nonneg _)
        _ = (1 / (1 - lam)) * ∑ j ∈ range T, (q ^ 2 / lam) ^ j *
              ∑ m ∈ range T, dyadicDifference η (m / 2 ^ j) ^ 2 / (m : ℝ) ^ 2 := by
            rw [← mul_sum, sum_comm]
            congr 1
            refine sum_congr rfl fun j _ => ?_
            rw [mul_sum]
            exact sum_congr rfl fun m _ => by ring
        _ ≤ (1 / (1 - lam)) * ∑ j ∈ range T, (q ^ 2 / lam) ^ j * ((1 / 2) ^ j * SD) := by
            refine mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => ?_) (by
              have : 0 < 1 - lam := by linarith
              positivity)
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact ((hfloor j).1.sum_le_tsum _ fun m _ => by positivity).trans (hfloor j).2
        _ = (1 / (1 - lam)) * ((∑ j ∈ range T, lam ^ j) * SD) := by
            congr 1
            rw [sum_mul]
            refine sum_congr rfl fun j _ => ?_
            rw [← mul_assoc, ← mul_pow, hratio]
        _ ≤ (1 / (1 - lam)) * ((1 / (1 - lam)) * SD) := by
            have hSD0 : 0 ≤ SD := tsum_nonneg fun k => by positivity
            have hg : ∑ j ∈ range T, lam ^ j ≤ 1 / (1 - lam) := geom_partial_le hl0 hl1 T
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg hSD0) (by
              have : 0 < 1 - lam := by linarith
              positivity)
        _ = _ := by ring
    exact summable_of_sum_range_le (fun m => by positivity) hpart
  · intro hPs
    have hPnn : ∀ k, 0 ≤ P k ^ 2 := fun k => sq_nonneg _
    have hP0 : P 0 ^ 2 = 0 := by rw [hP, centeredPrefix_zero]; norm_num
    obtain ⟨hhalf, -⟩ := summable_floor_half_le (h := fun k => P k ^ 2) hPnn hP0 hPs
    have h2 : Summable fun m : ℕ => (q * P (m / 2)) ^ 2 / (m : ℝ) ^ 2 :=
      (hhalf.mul_left (q ^ 2)).congr fun m => by ring
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      ((hPs.add h2).mul_left 2)
    unfold dyadicDifference
    rw [← hP, ← hq]
    have : (P m - q * P (m / 2)) ^ 2 ≤ 2 * (P m ^ 2 + (q * P (m / 2)) ^ 2) := by
      nlinarith [sq_nonneg (P m + q * P (m / 2))]
    calc (P m - q * P (m / 2)) ^ 2 / (m : ℝ) ^ 2 ≤ 2 * (P m ^ 2 + (q * P (m / 2)) ^ 2) / (m : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right this (sq_nonneg _)
      _ = _ := by ring

/-- `P(m+1)/(m+1) ∈ ℓ²` is the same as `P(m)/m ∈ ℓ²`. -/
private theorem summable_shift_iff (u : ℕ → ℝ) :
    (Summable fun n : ℕ => (u (n + 1) / ((n : ℝ) + 1)) ^ 2) ↔
      Summable fun m : ℕ => u m ^ 2 / (m : ℝ) ^ 2 := by
  rw [← summable_nat_add_iff 1 (f := fun m : ℕ => u m ^ 2 / (m : ℝ) ^ 2)]
  constructor <;> intro h <;> refine h.congr fun n => ?_ <;> push_cast <;> rw [div_pow]

/-- **The first column of the centred chain is in `ℓ²` iff the damping is admitted.** -/
theorem admits_iff_summable_firstColumn {η : ℝ} (hη : 0 < η) :
    Admits dampedMobiusEnergy η ↔
      Summable fun n => arithmeticDampingCenteredOperator hη firstState n ^ 2 := by
  set P := RHTower.pmPowerDampedCenteredDivisorPrefix η
  set ρ := (RHTower.pmPowerDampedDivisorDensity η).re
  -- the `1/m` correction is square summable
  set e : ℕ → ℝ := fun n => ρ * (2 : ℝ) ^ (-η) * (((n + 1) % 2 : ℕ) : ℝ) / (2 * ((n : ℝ) + 1))
    with he
  have hes : Summable fun n => e n ^ 2 := by
    have hmaj : Summable fun n : ℕ => (ρ * (2 : ℝ) ^ (-η)) ^ 2 * (1 / ((n : ℝ) + 1)) ^ 2 := by
      have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      exact (h.congr fun n => by push_cast; rw [one_div_pow]).mul_left _
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hmaj
    have hmod : (((n + 1) % 2 : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    have hmod0 : (0 : ℝ) ≤ (((n + 1) % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hr : (((n + 1) % 2 : ℕ) : ℝ) / (2 * ((n : ℝ) + 1)) ≤ 1 / ((n : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity) hpos]
      nlinarith
    have hr0 : 0 ≤ (((n + 1) % 2 : ℕ) : ℝ) / (2 * ((n : ℝ) + 1)) := by positivity
    have he' : e n = ρ * (2 : ℝ) ^ (-η) * ((((n + 1) % 2 : ℕ) : ℝ) / (2 * ((n : ℝ) + 1))) := by
      simp only [he]
      ring
    rw [he', mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr 2) (sq_nonneg _)
  have hcol : ∀ n, arithmeticDampingCenteredOperator hη firstState n =
      dyadicDifference η (n + 1) / ((n : ℝ) + 1) + e n := fun n => by
    rw [centeredOperator_firstState_apply_eq]
  have hD : (Summable fun n => arithmeticDampingCenteredOperator hη firstState n ^ 2) ↔
      Summable fun n : ℕ => (dyadicDifference η (n + 1) / ((n : ℝ) + 1)) ^ 2 := by
    simp only [hcol]
    constructor
    · intro h
      have h2 := summable_sq_add h (hes.congr fun n => (neg_sq (e n)).symm)
      refine h2.congr fun n => ?_
      ring
    · intro h
      exact summable_sq_add h hes
  rw [admits_iff_summable_orbit hη, hD]
  have horbit : (fun m => arithmeticDampingCenteredOperator hη reciprocalObservable m ^ 2) =
      fun n : ℕ => (P (n + 1) / ((n : ℝ) + 1)) ^ 2 := by
    funext n
    rw [centeredOperator_reciprocal_apply]
  rw [horbit, summable_shift_iff P, summable_shift_iff (dyadicDifference η)]
  exact (summable_dyadicDifference_iff hη).symm

/-- The Riemann hypothesis is the first column of the centred chain entering `ℓ²` at arbitrarily
small dampings. -/
theorem riemannHypothesis_iff_firstColumn_summable :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, ∃ hε : 0 < ε, ε < δ ∧
      Summable fun n => arithmeticDampingCenteredOperator hε firstState n ^ 2 := by
  rw [riemannHypothesis_iff_cofinallyAdmits]
  constructor
  · intro h δ hδ
    obtain ⟨ε, hε, hεδ, ha⟩ := h δ hδ
    exact ⟨ε, hε, hεδ, (admits_iff_summable_firstColumn hε).mp ha⟩
  · intro h δ hδ
    obtain ⟨ε, hε, hεδ, hs⟩ := h δ hδ
    exact ⟨ε, hε, hεδ, (admits_iff_summable_firstColumn hε).mpr hs⟩

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence

import GaloisForLFunctions.HTGeometry.AlternatingHarmonicPair
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def sharpHarmonicError (m : ℕ) : ℝ :=
  Real.log 2 - ((harmonic (2 * m) : ℚ) : ℝ) + ((harmonic m : ℚ) : ℝ)

def reciprocalTelescope (c k : ℕ) : ℝ :=
  1 / (k + c : ℝ) - 1 / (k + c + 1 : ℝ)

lemma sum_range_reciprocalTelescope (c N : ℕ) :
    ∑ k ∈ Finset.range N, reciprocalTelescope c k =
      1 / (c : ℝ) - 1 / (N + c : ℝ) := by
  induction N with
  | zero => simp [reciprocalTelescope]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      unfold reciprocalTelescope
      push_cast
      ring

lemma hasSum_reciprocalTelescope (c : ℕ) (hc : 0 < c) :
    HasSum (reciprocalTelescope c) (1 / (c : ℝ)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hzero : Tendsto (fun N : ℕ => 1 / (N + c : ℝ)) atTop (nhds 0) := by
      have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat c)
      change Tendsto (fun N : ℕ => 1 / ((N + c : ℕ) : ℝ)) atTop (nhds 0) at h
      simpa only [Nat.cast_add] using h
    simpa only [sum_range_reciprocalTelescope c, sub_zero] using
      (tendsto_const_nhds.sub hzero)
  · intro k
    unfold reciprocalTelescope
    have hkc : 0 < (k + c : ℝ) := by positivity
    have hle : (k + c : ℝ) ≤ k + c + 1 := by norm_num
    linarith [one_div_le_one_div_of_le hkc hle]

lemma sharpHarmonicError_eq_tsum_tail (m : ℕ) :
    sharpHarmonicError m =
      ∑' k : ℕ, GaloisForLFunctions.HTGeometry.alternatingHarmonicPair (k + m) := by
  have hsplit :=
    GaloisForLFunctions.HTGeometry.summable_alternatingHarmonicPair.sum_add_tsum_nat_add m
  rw [GaloisForLFunctions.HTGeometry.tsum_alternatingHarmonicPair] at hsplit
  rw [GaloisForLFunctions.HTGeometry.sum_alternatingHarmonicPair_eq] at hsplit
  unfold sharpHarmonicError
  linarith

lemma lower_telescope_le_alternatingHarmonicPair_tail (m k : ℕ) (hm : 0 < m) :
    (1 / 4 : ℝ) * reciprocalTelescope (m + 1) k ≤
      GaloisForLFunctions.HTGeometry.alternatingHarmonicPair (k + m) := by
  rw [GaloisForLFunctions.HTGeometry.alternatingHarmonicPair_eq]
  unfold reciprocalTelescope
  push_cast
  have hj : 0 < (k : ℝ) + m := by positivity
  field_simp
  ring
  nlinarith

lemma alternatingHarmonicPair_tail_le_upper_telescope (m k : ℕ) (hm : 0 < m) :
    GaloisForLFunctions.HTGeometry.alternatingHarmonicPair (k + m) ≤
      (1 / 4 : ℝ) * reciprocalTelescope m k := by
  rw [GaloisForLFunctions.HTGeometry.alternatingHarmonicPair_eq]
  unfold reciprocalTelescope
  push_cast
  have hj : 0 < (k : ℝ) + m := by positivity
  field_simp
  nlinarith

/-- Strong sharp sandwich; its lower bound improves the paper card's `1/(8m)`. -/
theorem sharpHarmonicError_bounds (m : ℕ) (hm : 0 < m) :
    1 / (4 * (m + 1 : ℝ)) ≤ sharpHarmonicError m ∧
      sharpHarmonicError m ≤ 1 / (4 * (m : ℝ)) := by
  have hpair : Summable (fun k : ℕ =>
      GaloisForLFunctions.HTGeometry.alternatingHarmonicPair (k + m)) :=
    (summable_nat_add_iff m).mpr
      GaloisForLFunctions.HTGeometry.summable_alternatingHarmonicPair
  have hLower : HasSum (fun k : ℕ =>
      (1 / 4 : ℝ) * reciprocalTelescope (m + 1) k)
      ((1 / 4 : ℝ) * (1 / ((m + 1 : ℕ) : ℝ))) :=
    (hasSum_reciprocalTelescope (m + 1) (by omega)).mul_left (1 / 4 : ℝ)
  have hUpper : HasSum (fun k : ℕ =>
      (1 / 4 : ℝ) * reciprocalTelescope m k)
      ((1 / 4 : ℝ) * (1 / (m : ℝ))) :=
    (hasSum_reciprocalTelescope m hm).mul_left (1 / 4 : ℝ)
  constructor
  · rw [sharpHarmonicError_eq_tsum_tail]
    have hle := hLower.summable.tsum_le_tsum
      (fun k => lower_telescope_le_alternatingHarmonicPair_tail m k hm) hpair
    rw [hLower.tsum_eq] at hle
    have heq : 1 / (4 * (m + 1 : ℝ)) =
        (1 / 4 : ℝ) * (1 / ((m + 1 : ℕ) : ℝ)) := by
      push_cast
      field_simp
    rw [heq]
    exact hle
  · rw [sharpHarmonicError_eq_tsum_tail]
    have hle := hpair.tsum_le_tsum
      (fun k => alternatingHarmonicPair_tail_le_upper_telescope m k hm) hUpper.summable
    rw [hUpper.tsum_eq] at hle
    have heq : 1 / (4 * (m : ℝ)) = (1 / 4 : ℝ) * (1 / (m : ℝ)) := by
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp
    rw [heq]
    exact hle

theorem sharpHarmonicError_pos (m : ℕ) (hm : 0 < m) :
    0 < sharpHarmonicError m :=
  lt_of_lt_of_le (by positivity) (sharpHarmonicError_bounds m hm).1

theorem sharpHarmonicError_lt_odd_reciprocal (m : ℕ) (hm : 0 < m) :
    sharpHarmonicError m < 1 / (2 * m + 1 : ℝ) := by
  refine lt_of_le_of_lt (sharpHarmonicError_bounds m hm).2 ?_
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [one_div_lt_one_div (by positivity) (by positivity)]
  linarith

theorem tendsto_nat_mul_sharpHarmonicError :
    Tendsto (fun m : ℕ => (m : ℝ) * sharpHarmonicError m) atTop (nhds (1 / 4)) := by
  have hlower : Tendsto (fun m : ℕ =>
      (1 / 4 : ℝ) * ((m : ℝ) / (m + 1))) atTop (nhds (1 / 4)) := by
    simpa using (tendsto_const_nhds.mul
      (tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hmpos : 0 < m := by omega
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    calc
      (1 / 4 : ℝ) * ((m : ℝ) / (m + 1)) =
          (m : ℝ) * (1 / (4 * (m + 1 : ℝ))) := by field_simp
      _ ≤ (m : ℝ) * sharpHarmonicError m :=
        mul_le_mul_of_nonneg_left (sharpHarmonicError_bounds m hmpos).1 hmR.le
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hmpos : 0 < m := by omega
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    calc
      (m : ℝ) * sharpHarmonicError m ≤
          (m : ℝ) * (1 / (4 * (m : ℝ))) :=
        mul_le_mul_of_nonneg_left (sharpHarmonicError_bounds m hmpos).2 hmR.le
      _ = 1 / 4 := by field_simp

def sharpOddError (m : ℕ) : ℝ :=
  1 / (2 * m + 1 : ℝ) - sharpHarmonicError m

theorem sharpOddError_pos (m : ℕ) (hm : 0 < m) : 0 < sharpOddError m := by
  unfold sharpOddError
  linarith [sharpHarmonicError_lt_odd_reciprocal m hm]

theorem tendsto_nat_mul_odd_reciprocal :
    Tendsto (fun m : ℕ => (m : ℝ) * (1 / (2 * m + 1 : ℝ))) atTop
      (nhds (1 / 2)) := by
  have h := tendsto_add_mul_div_add_mul_atTop_nhds (0 : ℝ) 1 1 (by norm_num : (2 : ℝ) ≠ 0)
  convert h using 1
  · funext m
    field_simp
    ring

theorem tendsto_nat_mul_sharpOddError :
    Tendsto (fun m : ℕ => (m : ℝ) * sharpOddError m) atTop (nhds (1 / 4)) := by
  have h := tendsto_nat_mul_odd_reciprocal.sub tendsto_nat_mul_sharpHarmonicError
  convert h using 1
  · funext m
    unfold sharpOddError
    ring
  · ring

def sharpCriticalEnergy (m : ℕ) : ℝ :=
  (2 * m + 1 / 2 : ℝ) * sharpHarmonicError m ^ (2 : ℕ) +
    (2 * m + 3 / 2 : ℝ) * sharpOddError m ^ (2 : ℕ)

theorem tendsto_nat_mul_evenCriticalEnergy :
    Tendsto (fun m : ℕ =>
      (m : ℝ) * (2 * m + 1 / 2 : ℝ) * sharpHarmonicError m ^ (2 : ℕ))
      atTop (nhds (1 / 8)) := by
  have hcoeff := tendsto_add_mul_div_add_mul_atTop_nhds
    (1 / 2 : ℝ) 0 2 (by norm_num : (1 : ℝ) ≠ 0)
  have hprod := hcoeff.mul (tendsto_nat_mul_sharpHarmonicError.pow 2)
  have hprod' : Tendsto (fun m : ℕ =>
      ((1 / 2 : ℝ) + 2 * m) / (m : ℝ) *
        ((m : ℝ) * sharpHarmonicError m) ^ (2 : ℕ)) atTop (nhds (1 / 8)) := by
    have hval : (2 : ℝ) * (1 / 4) ^ (2 : ℕ) = 1 / 8 := by norm_num
    simpa only [zero_add, one_mul, div_one, hval] using hprod
  apply hprod'.congr'
  filter_upwards [eventually_ne_atTop 0] with m hm
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp
  ring

theorem tendsto_nat_mul_oddCriticalEnergy :
    Tendsto (fun m : ℕ =>
      (m : ℝ) * (2 * m + 3 / 2 : ℝ) * sharpOddError m ^ (2 : ℕ))
      atTop (nhds (1 / 8)) := by
  have hcoeff := tendsto_add_mul_div_add_mul_atTop_nhds
    (3 / 2 : ℝ) 0 2 (by norm_num : (1 : ℝ) ≠ 0)
  have hprod := hcoeff.mul (tendsto_nat_mul_sharpOddError.pow 2)
  have hprod' : Tendsto (fun m : ℕ =>
      ((3 / 2 : ℝ) + 2 * m) / (m : ℝ) *
        ((m : ℝ) * sharpOddError m) ^ (2 : ℕ)) atTop (nhds (1 / 8)) := by
    have hval : (2 : ℝ) * (1 / 4) ^ (2 : ℕ) = 1 / 8 := by norm_num
    simpa only [zero_add, one_mul, div_one, hval] using hprod
  apply hprod'.congr'
  filter_upwards [eventually_ne_atTop 0] with m hm
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp
  ring

theorem tendsto_nat_mul_sharpCriticalEnergy :
    Tendsto (fun m : ℕ => (m : ℝ) * sharpCriticalEnergy m) atTop (nhds (1 / 4)) := by
  have h := tendsto_nat_mul_evenCriticalEnergy.add tendsto_nat_mul_oddCriticalEnergy
  convert h using 1
  · funext m
    unfold sharpCriticalEnergy
    ring
  · ring

theorem sharpCriticalEnergy_error_bound (m : ℕ) (hm : 0 < m) :
    |sharpCriticalEnergy m - 1 / (4 * (m : ℝ))| ≤ 17 / (m : ℝ) ^ (2 : ℕ) := by
  let d := sharpHarmonicError m
  let o := sharpOddError m
  let q : ℝ := 1 / (4 * (m : ℝ))
  let r : ℝ := 1 / (m : ℝ) ^ (2 : ℕ)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hd0 : 0 ≤ d := (sharpHarmonicError_pos m hm).le
  have ho0 : 0 ≤ o := (sharpOddError_pos m hm).le
  have hdq : d ≤ q := by
    exact (sharpHarmonicError_bounds m hm).2
  have hdlower : 1 / (4 * (m + 1 : ℝ)) ≤ d :=
    (sharpHarmonicError_bounds m hm).1
  have hdiff : q - 1 / (4 * (m + 1 : ℝ)) ≤ r := by
    dsimp [q, r]
    field_simp
    nlinarith
  have hdErr : |d - q| ≤ r := by
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith
  have hoFormula : o = 1 / (2 * m + 1 : ℝ) - d := by rfl
  have hoLower : 1 / (2 * m + 1 : ℝ) - q ≤ o := by linarith
  have hoUpper : o ≤ 1 / (2 * m + 1 : ℝ) - 1 / (4 * (m + 1 : ℝ)) := by
    linarith
  have hoErr : |o - q| ≤ r := by
    rw [abs_le]
    constructor
    · have haux : q - r ≤ 1 / (2 * m + 1 : ℝ) - q := by
        dsimp [q, r]
        field_simp
        nlinarith
      linarith
    · have haux : 1 / (2 * m + 1 : ℝ) - 1 / (4 * (m + 1 : ℝ)) ≤ q + r := by
        dsimp [q, r]
        field_simp
        nlinarith
      linarith
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq_le : q ≤ 1 / (m : ℝ) := by
    dsimp [q]
    have hm4 : (0 : ℝ) < 4 * m := by positivity
    rw [one_div_le_one_div hm4 hmR]
    nlinarith
  have hd_le : d ≤ 1 / (m : ℝ) := hdq.trans hq_le
  have ho_le : o ≤ 1 / (m : ℝ) := by
    rw [hoFormula]
    have hrec : 1 / (2 * m + 1 : ℝ) ≤ 1 / (m : ℝ) := by
      rw [one_div_le_one_div (by positivity) hmR]
      nlinarith
    linarith
  have hdSq : |d ^ (2 : ℕ) - q ^ (2 : ℕ)| ≤ 2 / (m : ℝ) ^ (3 : ℕ) := by
    rw [show d ^ (2 : ℕ) - q ^ (2 : ℕ) = (d - q) * (d + q) by ring, abs_mul]
    have hsum : |d + q| ≤ 2 / (m : ℝ) := by
      rw [abs_of_nonneg (add_nonneg hd0 hq0)]
      calc
        d + q ≤ 1 / (m : ℝ) + 1 / (m : ℝ) := add_le_add hd_le hq_le
        _ = 2 / (m : ℝ) := by ring
    calc
      |d - q| * |d + q| ≤ r * (2 / (m : ℝ)) :=
        mul_le_mul hdErr hsum (abs_nonneg _) (by positivity)
      _ = 2 / (m : ℝ) ^ (3 : ℕ) := by dsimp [r]; field_simp
  have hoSq : |o ^ (2 : ℕ) - q ^ (2 : ℕ)| ≤ 2 / (m : ℝ) ^ (3 : ℕ) := by
    rw [show o ^ (2 : ℕ) - q ^ (2 : ℕ) = (o - q) * (o + q) by ring, abs_mul]
    have hsum : |o + q| ≤ 2 / (m : ℝ) := by
      rw [abs_of_nonneg (add_nonneg ho0 hq0)]
      calc
        o + q ≤ 1 / (m : ℝ) + 1 / (m : ℝ) := add_le_add ho_le hq_le
        _ = 2 / (m : ℝ) := by ring
    calc
      |o - q| * |o + q| ≤ r * (2 / (m : ℝ)) :=
        mul_le_mul hoErr hsum (abs_nonneg _) (by positivity)
      _ = 2 / (m : ℝ) ^ (3 : ℕ) := by dsimp [r]; field_simp
  let w₁ : ℝ := 2 * m + 1 / 2
  let w₂ : ℝ := 2 * m + 3 / 2
  have hw₁0 : 0 ≤ w₁ := by dsimp [w₁]; positivity
  have hw₂0 : 0 ≤ w₂ := by dsimp [w₂]; positivity
  have hw₁ : w₁ ≤ 4 * (m : ℝ) := by
    dsimp [w₁]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hw₂ : w₂ ≤ 4 * (m : ℝ) := by
    dsimp [w₂]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hdev : |w₁ * (d ^ (2 : ℕ) - q ^ (2 : ℕ)) + w₂ * (o ^ (2 : ℕ) - q ^ (2 : ℕ))| ≤
      16 / (m : ℝ) ^ (2 : ℕ) := by
    calc
      |w₁ * (d ^ (2 : ℕ) - q ^ (2 : ℕ)) + w₂ * (o ^ (2 : ℕ) - q ^ (2 : ℕ))| ≤
          |w₁ * (d ^ (2 : ℕ) - q ^ (2 : ℕ))| + |w₂ * (o ^ (2 : ℕ) - q ^ (2 : ℕ))| :=
            abs_add_le _ _
      _ =
          w₁ * |d ^ (2 : ℕ) - q ^ (2 : ℕ)| + w₂ * |o ^ (2 : ℕ) - q ^ (2 : ℕ)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hw₁0, abs_of_nonneg hw₂0]
      _ ≤ (4 * (m : ℝ)) * (2 / (m : ℝ) ^ (3 : ℕ)) +
          (4 * (m : ℝ)) * (2 / (m : ℝ) ^ (3 : ℕ)) := by
            gcongr
      _ = 16 / (m : ℝ) ^ (2 : ℕ) := by field_simp; ring
  have hbase : (w₁ + w₂) * q ^ (2 : ℕ) =
      1 / (4 * (m : ℝ)) + 1 / (8 * (m : ℝ) ^ (2 : ℕ)) := by
    dsimp [w₁, w₂, q]
    field_simp
    ring
  have hdecomp : sharpCriticalEnergy m - 1 / (4 * (m : ℝ)) =
      (w₁ * (d ^ (2 : ℕ) - q ^ (2 : ℕ)) + w₂ * (o ^ (2 : ℕ) - q ^ (2 : ℕ))) +
        1 / (8 * (m : ℝ) ^ (2 : ℕ)) := by
    unfold sharpCriticalEnergy
    change w₁ * d ^ (2 : ℕ) + w₂ * o ^ (2 : ℕ) - 1 / (4 * (m : ℝ)) =
      (w₁ * (d ^ (2 : ℕ) - q ^ (2 : ℕ)) + w₂ * (o ^ (2 : ℕ) - q ^ (2 : ℕ))) +
        1 / (8 * (m : ℝ) ^ (2 : ℕ))
    calc
      w₁ * d ^ (2 : ℕ) + w₂ * o ^ (2 : ℕ) - 1 / (4 * (m : ℝ)) =
          w₁ * (d ^ (2 : ℕ) - q ^ (2 : ℕ)) + w₂ * (o ^ (2 : ℕ) - q ^ (2 : ℕ)) +
            ((w₁ + w₂) * q ^ (2 : ℕ) - 1 / (4 * (m : ℝ))) := by ring
      _ = w₁ * (d ^ (2 : ℕ) - q ^ (2 : ℕ)) + w₂ * (o ^ (2 : ℕ) - q ^ (2 : ℕ)) +
            1 / (8 * (m : ℝ) ^ (2 : ℕ)) := by rw [hbase]; ring
  rw [hdecomp]
  calc
    |w₁ * (d ^ (2 : ℕ) - q ^ (2 : ℕ)) + w₂ * (o ^ (2 : ℕ) - q ^ (2 : ℕ)) +
        1 / (8 * (m : ℝ) ^ (2 : ℕ))| ≤
      |w₁ * (d ^ (2 : ℕ) - q ^ (2 : ℕ)) + w₂ * (o ^ (2 : ℕ) - q ^ (2 : ℕ))| +
        |1 / (8 * (m : ℝ) ^ (2 : ℕ))| := abs_add_le _ _
    _ ≤ 16 / (m : ℝ) ^ (2 : ℕ) + 1 / (8 * (m : ℝ) ^ (2 : ℕ)) := by
      gcongr
      rw [abs_of_nonneg (by positivity)]
    _ ≤ 17 / (m : ℝ) ^ (2 : ℕ) := by
      field_simp
      nlinarith

/-- The deviation from the exact critical harmonic main term is absolutely summable. -/
theorem summable_sharpCriticalEnergy_error :
    Summable (fun n : ℕ =>
      sharpCriticalEnergy (n + 1) - 1 / (4 * (n + 1 : ℝ))) := by
  have hsquare : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => 17 / (n + 1 : ℝ) ^ (2 : ℕ)) := by
    have h := ((summable_nat_add_iff 1).mpr hsquare).mul_left (17 : ℝ)
    simpa [Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using h
  apply Summable.of_norm_bounded hshift
  intro n
  rw [Real.norm_eq_abs]
  simpa only [Nat.cast_add, Nat.cast_one] using
    sharpCriticalEnergy_error_bound (n + 1) (by omega)

def sharpCriticalPartialEnergy (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.range M, sharpCriticalEnergy (n + 1)

lemma sum_range_shifted_reciprocal (M : ℕ) :
    ∑ n ∈ Finset.range M, (1 / (n + 1 : ℝ)) = ((harmonic M : ℚ) : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih, harmonic_succ]
      norm_num

theorem tendsto_harmonic_div_log :
    Tendsto (fun M : ℕ => ((harmonic M : ℚ) : ℝ) / Real.log (M : ℝ))
      atTop (nhds 1) := by
  have hlog : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herror : Tendsto (fun M : ℕ =>
      (((harmonic M : ℚ) : ℝ) - Real.log (M : ℝ)) / Real.log (M : ℝ))
      atTop (nhds 0) := Real.tendsto_harmonic_sub_log.div_atTop hlog
  have heq : (fun M : ℕ => ((harmonic M : ℚ) : ℝ) / Real.log (M : ℝ)) =ᶠ[atTop]
      (fun M : ℕ => 1 +
        ((((harmonic M : ℚ) : ℝ) - Real.log (M : ℝ)) / Real.log (M : ℝ))) := by
    filter_upwards [eventually_ge_atTop 2] with M hM
    have hM1 : (1 : ℝ) < M := by exact_mod_cast hM
    have hlogM : Real.log (M : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hM1)
    field_simp
    ring
  simpa only [add_zero] using (herror.const_add 1).congr' heq.symm

/-- Exact discrete logarithmic flux law: critical block energy has coefficient `1/4`. -/
theorem tendsto_sharpCriticalPartialEnergy_div_log :
    Tendsto (fun M : ℕ => sharpCriticalPartialEnergy M / Real.log (M : ℝ))
      atTop (nhds (1 / 4)) := by
  let err : ℕ → ℝ := fun n =>
    sharpCriticalEnergy (n + 1) - 1 / (4 * (n + 1 : ℝ))
  have herr : Summable err := summable_sharpCriticalEnergy_error
  have hpartial : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, err n)
      atTop (nhds (∑' n : ℕ, err n)) := herr.hasSum.tendsto_sum_nat
  have hlog : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hvanish : Tendsto (fun M : ℕ =>
      (∑ n ∈ Finset.range M, err n) / Real.log (M : ℝ)) atTop (nhds 0) :=
    hpartial.div_atTop hlog
  have hmain := tendsto_harmonic_div_log.const_mul (1 / 4 : ℝ)
  have hsum := hmain.add hvanish
  convert hsum using 1
  · funext M
    unfold sharpCriticalPartialEnergy err
    have hnum : (∑ n ∈ Finset.range M, sharpCriticalEnergy (n + 1)) =
        (1 / 4 : ℝ) * ((harmonic M : ℚ) : ℝ) +
          ∑ n ∈ Finset.range M,
            (sharpCriticalEnergy (n + 1) - 1 / (4 * (n + 1 : ℝ))) := by
      calc
        (∑ n ∈ Finset.range M, sharpCriticalEnergy (n + 1)) =
            ∑ n ∈ Finset.range M,
              ((1 / 4 : ℝ) * (1 / (n + 1 : ℝ)) +
                (sharpCriticalEnergy (n + 1) - 1 / (4 * (n + 1 : ℝ)))) := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnpos : (0 : ℝ) < n + 1 := by positivity
          field_simp
          ring
        _ = (1 / 4 : ℝ) * (∑ n ∈ Finset.range M, (1 / (n + 1 : ℝ))) +
              ∑ n ∈ Finset.range M,
                (sharpCriticalEnergy (n + 1) - 1 / (4 * (n + 1 : ℝ))) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = _ := by rw [sum_range_shifted_reciprocal]
    rw [hnum]
    ring
  · ring

/-- Exact sharp co-Poisson step function, with endpoint values fixed arbitrarily on a null set. -/
def sharpCoPoissonP (t : ℝ) : ℝ :=
  if t < 1 then -Real.log 2
  else if t < 2 then 1 - Real.log 2
  else
    let m := ⌊t / 2⌋₊
    if t < 2 * (m : ℝ) + 1 then -sharpHarmonicError m else sharpOddError m

theorem measurable_sharpCoPoissonP : Measurable sharpCoPoissonP := by
  have hm : Measurable (fun t : ℝ => ⌊t / 2⌋₊) :=
    (measurable_id.div_const (2 : ℝ)).nat_floor
  have hd : Measurable (fun t : ℝ => sharpHarmonicError ⌊t / 2⌋₊) :=
    (measurable_of_countable sharpHarmonicError).comp hm
  have ho : Measurable (fun t : ℝ => sharpOddError ⌊t / 2⌋₊) :=
    (measurable_of_countable sharpOddError).comp hm
  have hw : Measurable (fun t : ℝ => (2 * (⌊t / 2⌋₊ : ℝ) + 1)) :=
    ((measurable_of_countable fun m : ℕ => (2 * (m : ℝ) + 1 : ℝ)).comp hm)
  unfold sharpCoPoissonP
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      (Measurable.ite (measurableSet_lt measurable_id hw) hd.neg ho))

lemma natFloor_half_eq_on_even_cell (m : ℕ) {t : ℝ}
    (ht0 : (2 * m : ℝ) < t) (ht1 : t < 2 * m + 1) : ⌊t / 2⌋₊ = m := by
  have ht : 0 ≤ t / 2 := by
    have hm0 : (0 : ℝ) ≤ 2 * m := by positivity
    have htpos : 0 < t := lt_of_le_of_lt hm0 ht0
    exact div_nonneg htpos.le (by norm_num)
  rw [Nat.floor_eq_iff ht]
  constructor <;> linarith

lemma natFloor_half_eq_on_odd_cell (m : ℕ) {t : ℝ}
    (ht0 : (2 * m + 1 : ℝ) < t) (ht1 : t < 2 * m + 2) : ⌊t / 2⌋₊ = m := by
  have ht : 0 ≤ t / 2 := by
    have htpos : 0 < t := by
      have : (0 : ℝ) ≤ 2 * m := by positivity
      linarith
    exact div_nonneg htpos.le (by norm_num)
  rw [Nat.floor_eq_iff ht]
  constructor <;> linarith

/-- Exact even-cell evaluation of Burnol's sharp source, away from endpoints. -/
theorem sharpCoPoissonP_even_cell (m : ℕ) (hm : 0 < m) {t : ℝ}
    (ht0 : (2 * m : ℝ) < t) (ht1 : t < 2 * m + 1) :
    sharpCoPoissonP t = -sharpHarmonicError m := by
  have ht2 : ¬t < 2 := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : (2 : ℝ) ≤ 2 * m := by linarith
    linarith
  have ht1' : ¬t < 1 := by linarith
  rw [sharpCoPoissonP, if_neg ht1', if_neg ht2,
    natFloor_half_eq_on_even_cell m ht0 ht1, if_pos ht1]

/-- Exact odd-cell evaluation of Burnol's sharp source, away from endpoints. -/
theorem sharpCoPoissonP_odd_cell (m : ℕ) (hm : 0 < m) {t : ℝ}
    (ht0 : (2 * m + 1 : ℝ) < t) (ht1 : t < 2 * m + 2) :
    sharpCoPoissonP t = sharpOddError m := by
  have ht2 : ¬t < 2 := by
    have : (2 : ℝ) ≤ 2 * m + 1 := by
      have hm1 : 1 ≤ m := hm
      exact_mod_cast (show 2 ≤ 2 * m + 1 by omega)
    linarith
  have ht1' : ¬t < 1 := by linarith
  rw [sharpCoPoissonP, if_neg ht1', if_neg ht2,
    natFloor_half_eq_on_odd_cell m ht0 ht1, if_neg (by linarith)]

lemma intervalIntegral_id_exact (a b : ℝ) :
    ∫ t in a..b, t = (b ^ (2 : ℕ) - a ^ (2 : ℕ)) / 2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => x * x / 2) (f' := fun x : ℝ => x)
    (a := a) (b := b) (fun x hx => by
      have hx' := ((hasDerivAt_id' x).mul (hasDerivAt_id' x)).div_const 2
      norm_num at hx'
      exact hx')
    (continuous_id.intervalIntegrable a b)
  convert h using 1
  all_goals ring

theorem integral_even_cell_criticalEnergy (m : ℕ) (hm : 0 < m) :
    ∫ t in (2 * m : ℝ)..(2 * m + 1 : ℝ), t * sharpCoPoissonP t ^ (2 : ℕ) =
      (2 * m + 1 / 2 : ℝ) * sharpHarmonicError m ^ (2 : ℕ) := by
  rw [intervalIntegral.integral_congr_ae (g := fun t : ℝ =>
      t * sharpHarmonicError m ^ (2 : ℕ)) (by
    filter_upwards [MeasureTheory.volume.ae_ne (2 * m + 1 : ℝ)] with t ht hmem
    rw [Set.uIoc_of_le (by linarith), Set.mem_Ioc] at hmem
    have ht0 : (2 * m : ℝ) < t := hmem.1
    have ht1 : t < 2 * m + 1 := lt_of_le_of_ne hmem.2 ht
    rw [sharpCoPoissonP_even_cell m hm ht0 ht1]
    ring)]
  rw [intervalIntegral.integral_mul_const]
  rw [intervalIntegral_id_exact]
  ring

theorem integral_odd_cell_criticalEnergy (m : ℕ) (hm : 0 < m) :
    ∫ t in (2 * m + 1 : ℝ)..(2 * m + 2 : ℝ), t * sharpCoPoissonP t ^ (2 : ℕ) =
      (2 * m + 3 / 2 : ℝ) * sharpOddError m ^ (2 : ℕ) := by
  rw [intervalIntegral.integral_congr_ae (g := fun t : ℝ =>
      t * sharpOddError m ^ (2 : ℕ)) (by
    filter_upwards [MeasureTheory.volume.ae_ne (2 * m + 2 : ℝ)] with t ht hmem
    rw [Set.uIoc_of_le (by linarith), Set.mem_Ioc] at hmem
    have ht0 : (2 * m + 1 : ℝ) < t := hmem.1
    have ht1 : t < 2 * m + 2 := lt_of_le_of_ne hmem.2 ht
    rw [sharpCoPoissonP_odd_cell m hm ht0 ht1])]
  rw [intervalIntegral.integral_mul_const]
  rw [intervalIntegral_id_exact]
  ring

lemma intervalIntegrable_even_cell_criticalEnergy (m : ℕ) (hm : 0 < m) :
    IntervalIntegrable (fun t : ℝ => t * sharpCoPoissonP t ^ (2 : ℕ)) MeasureTheory.volume
      (2 * m : ℝ) (2 * m + 1 : ℝ) := by
  have hcont : Continuous (fun t : ℝ => t * sharpHarmonicError m ^ (2 : ℕ)) :=
    continuous_id.mul continuous_const
  apply (hcont.intervalIntegrable _ _).congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc,
    (MeasureTheory.volume.ae_ne (2 * m + 1 : ℝ)).filter_mono
      MeasureTheory.ae_restrict_le] with t hmem ht
  rw [Set.uIoc_of_le (by linarith), Set.mem_Ioc] at hmem
  have ht0 : (2 * m : ℝ) < t := hmem.1
  have ht1 : t < 2 * m + 1 := lt_of_le_of_ne hmem.2 ht
  rw [sharpCoPoissonP_even_cell m hm ht0 ht1]
  ring

lemma intervalIntegrable_odd_cell_criticalEnergy (m : ℕ) (hm : 0 < m) :
    IntervalIntegrable (fun t : ℝ => t * sharpCoPoissonP t ^ (2 : ℕ)) MeasureTheory.volume
      (2 * m + 1 : ℝ) (2 * m + 2 : ℝ) := by
  have hcont : Continuous (fun t : ℝ => t * sharpOddError m ^ (2 : ℕ)) :=
    continuous_id.mul continuous_const
  apply (hcont.intervalIntegrable _ _).congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc,
    (MeasureTheory.volume.ae_ne (2 * m + 2 : ℝ)).filter_mono
      MeasureTheory.ae_restrict_le] with t hmem ht
  rw [Set.uIoc_of_le (by linarith), Set.mem_Ioc] at hmem
  have ht0 : (2 * m + 1 : ℝ) < t := hmem.1
  have ht1 : t < 2 * m + 2 := lt_of_le_of_ne hmem.2 ht
  rw [sharpCoPoissonP_odd_cell m hm ht0 ht1]

theorem integral_two_cell_criticalEnergy (m : ℕ) (hm : 0 < m) :
    ∫ t in (2 * m : ℝ)..(2 * m + 2 : ℝ), t * sharpCoPoissonP t ^ (2 : ℕ) =
      sharpCriticalEnergy m := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_even_cell_criticalEnergy m hm)
    (intervalIntegrable_odd_cell_criticalEnergy m hm)]
  rw [integral_even_cell_criticalEnergy m hm, integral_odd_cell_criticalEnergy m hm]
  unfold sharpCriticalEnergy
  ring

lemma intervalIntegrable_two_cell_criticalEnergy (m : ℕ) (hm : 0 < m) :
    IntervalIntegrable (fun t : ℝ => t * sharpCoPoissonP t ^ (2 : ℕ)) MeasureTheory.volume
      (2 * m : ℝ) (2 * m + 2 : ℝ) :=
  (intervalIntegrable_even_cell_criticalEnergy m hm).trans
    (intervalIntegrable_odd_cell_criticalEnergy m hm)

lemma intervalIntegrable_sharpCriticalFlux_cutoff (M : ℕ) :
    IntervalIntegrable (fun t : ℝ => t * sharpCoPoissonP t ^ (2 : ℕ)) MeasureTheory.volume
      2 (2 * (M + 1) : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
      have hblock := intervalIntegrable_two_cell_criticalEnergy (M + 1) (by omega)
      have hblock' : IntervalIntegrable
          (fun t : ℝ => t * sharpCoPoissonP t ^ (2 : ℕ)) MeasureTheory.volume
          (2 * ((M + 1) : ℝ)) (2 * (((M + 1) + 1) : ℝ)) := by
        convert hblock using 1 <;> push_cast <;> ring
      convert ih.trans hblock' using 1
      push_cast
      ring

/-- Exact identification of physical weighted flux with discrete critical block energy. -/
theorem integral_sharpCriticalFlux_cutoff_eq (M : ℕ) :
    ∫ t in (2 : ℝ)..(2 * (M + 1) : ℝ), t * sharpCoPoissonP t ^ (2 : ℕ) =
      sharpCriticalPartialEnergy M := by
  induction M with
  | zero => simp [sharpCriticalPartialEnergy]
  | succ M ih =>
      have hleft := intervalIntegrable_sharpCriticalFlux_cutoff M
      have hblock := intervalIntegrable_two_cell_criticalEnergy (M + 1) (by omega)
      have hblock' : IntervalIntegrable
          (fun t : ℝ => t * sharpCoPoissonP t ^ (2 : ℕ)) MeasureTheory.volume
          (2 * ((M + 1) : ℝ)) (2 * (((M + 1) + 1) : ℝ)) := by
        convert hblock using 1 <;> push_cast <;> ring
      have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hblock'
      have hblockEq :
          (∫ t in (2 * ((M : ℝ) + 1) : ℝ)..(2 * ((M : ℝ) + 1 + 1) : ℝ),
            t * sharpCoPoissonP t ^ (2 : ℕ)) = sharpCriticalEnergy (M + 1) := by
        convert integral_two_cell_criticalEnergy (M + 1) (by omega) using 1
        push_cast
        ring
      calc
        _ =
            ∫ t in (2 : ℝ)..(2 * ((M : ℝ) + 1 + 1) : ℝ),
              t * sharpCoPoissonP t ^ (2 : ℕ) := by
                congr 2
                push_cast
                ring
        _ = (∫ t in (2 : ℝ)..(2 * ((M : ℝ) + 1) : ℝ),
              t * sharpCoPoissonP t ^ (2 : ℕ)) +
            ∫ t in (2 * ((M : ℝ) + 1) : ℝ)..(2 * ((M : ℝ) + 1 + 1) : ℝ),
              t * sharpCoPoissonP t ^ (2 : ℕ) := hadd.symm
        _ = sharpCriticalPartialEnergy M + sharpCriticalEnergy (M + 1) := by
          rw [ih, hblockEq]
        _ = sharpCriticalPartialEnergy (M + 1) := by
          unfold sharpCriticalPartialEnergy
          rw [Finset.sum_range_succ]

lemma tendsto_log_sharpCutoff_atTop :
    Tendsto (fun M : ℕ => Real.log (2 * ((M : ℝ) + 1))) atTop atTop := by
  have hadd : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  exact Real.tendsto_log_atTop.comp (hadd.const_mul_atTop (by norm_num : (0 : ℝ) < 2))

lemma tendsto_log_nat_div_log_sharpCutoff :
    Tendsto (fun M : ℕ => Real.log (M : ℝ) / Real.log (2 * ((M : ℝ) + 1)))
      atTop (nhds 1) := by
  have hdiff : Tendsto (fun M : ℕ =>
      Real.log (2 * ((M : ℝ) + 1)) - Real.log (M : ℝ)) atTop
      (nhds (Real.log 2)) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log 2) atTop
      (nhds (Real.log 2))).add Real.tendsto_log_nat_add_one_sub_log
    convert h using 1
    · funext M
      rw [Real.log_mul (by norm_num) (by positivity)]
      ring
    · simp
  have hvanish := hdiff.div_atTop tendsto_log_sharpCutoff_atTop
  have hlimit : Tendsto (fun M : ℕ => 1 -
      (Real.log (2 * ((M : ℝ) + 1)) - Real.log (M : ℝ)) /
        Real.log (2 * ((M : ℝ) + 1))) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hvanish)
  apply hlimit.congr'
  filter_upwards with M
  have hlog : Real.log (2 * ((M : ℝ) + 1)) ≠ 0 := by
    apply ne_of_gt (Real.log_pos ?_)
    have hM0 : (0 : ℝ) ≤ M := by positivity
    linarith
  field_simp
  ring

theorem tendsto_sharpCriticalPartialEnergy_div_log_cutoff :
    Tendsto (fun M : ℕ =>
      sharpCriticalPartialEnergy M / Real.log (2 * ((M : ℝ) + 1))) atTop
      (nhds (1 / 4)) := by
  have h : Tendsto (fun M : ℕ =>
      (sharpCriticalPartialEnergy M / Real.log (M : ℝ)) *
        (Real.log (M : ℝ) / Real.log (2 * ((M : ℝ) + 1)))) atTop
      (nhds (1 / 4)) := by
    convert tendsto_sharpCriticalPartialEnergy_div_log.mul
      tendsto_log_nat_div_log_sharpCutoff using 1
    ring
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with M hM
  have hlogM : Real.log (M : ℝ) ≠ 0 := by
    apply ne_of_gt (Real.log_pos ?_)
    exact_mod_cast hM
  field_simp

/-- Physical weighted flux through exact dyadic-block cutoffs has coefficient `1/4`. -/
theorem tendsto_integral_sharpCriticalFlux_cutoff_div_log :
    Tendsto (fun M : ℕ =>
      (∫ t in (2 : ℝ)..(2 * (M + 1) : ℝ), t * sharpCoPoissonP t ^ (2 : ℕ)) /
        Real.log (2 * ((M : ℝ) + 1))) atTop (nhds (1 / 4)) := by
  simpa only [integral_sharpCriticalFlux_cutoff_eq] using
    tendsto_sharpCriticalPartialEnergy_div_log_cutoff

end
end RHTower

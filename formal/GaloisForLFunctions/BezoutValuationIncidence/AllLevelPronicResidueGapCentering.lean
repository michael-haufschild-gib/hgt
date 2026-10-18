import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic

/-!
# All-level pronic centering of residue gaps

On every quotient cell `[k*p,(k+1)*p)`, the difference between residues modulo
`p` and `p+h` has at most one jump. Its conditional pronic mean lies in
`[-h,0]`, even after the pre-overlap restriction `k*h ≤ p` fails. The next
larger-modulus jump determines both this mean and the exact centered variance.

For arbitrary positive moduli `p_i = P + offset_i`, the signed packet of these
local means has energy at most `(sum h_i)/P * sum a_i^2*h_i` at every horizon.
Consequently, the full residue packet reduces to its locally centered packet
with an explicit uniform cost. No bound for the latter packet is assumed or
proved here; its mixed-level covariance remains the dispersion obligation.
-/

open Finset
open scoped BigOperators
namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- Conditional pronic mean of a literal residue difference on one quotient cell. -/
def residueGapCellPronicMean (p h k : ℕ) : ℝ :=
  (k : ℝ) * ((k : ℝ) + 1) * p *
    ∑ n ∈ Ico (k * p) ((k + 1) * p),
      (((n % p : ℕ) : ℝ) - ((n % (p + h) : ℕ) : ℝ)) /
        ((n : ℝ) * ((n : ℝ) + 1))

private theorem reciprocal_cell_mass {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Ico a b, 1 / ((n : ℝ) * ((n : ℝ) + 1))) = 1 / (a : ℝ) - 1 / b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ico_succ_top hab, ih]
    have hb : (b : ℝ) ≠ 0 := by have : 0 < b := ha.trans_le hab; positivity
    have haR : (a : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

private theorem quotient_mod_cast {p n k : ℕ} (hl : k * p ≤ n) (hu : n < (k + 1) * p) :
    ((n % p : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) * p := by
  have hd : n / p = k := Nat.div_eq_of_lt_le hl hu
  have he := Nat.mod_add_div n p
  rw [hd] at he
  have heR : ((n % p : ℕ) : ℝ) + (p : ℝ) * k = n := by exact_mod_cast he
  nlinarith

private theorem all_level_cell_sum (p k : ℕ+) (h : ℕ) (f : ℝ → ℝ) :
    let q := (p : ℕ) + h
    let j := (k : ℕ) * (p : ℕ) / q
    let s := (j + 1) * q
    let t := min s (((k : ℕ) + 1) * (p : ℕ))
    (∑ n ∈ Ico ((k : ℕ) * (p : ℕ)) (((k : ℕ) + 1) * (p : ℕ)),
      f (((n % (p : ℕ) : ℕ) : ℝ) - ((n % q : ℕ) : ℝ)) /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      f ((j : ℝ) * q - (k : ℝ) * p) * (1 / ((k : ℝ) * p) - 1 / (t : ℝ)) +
      f (((j : ℝ) + 1) * q - (k : ℝ) * p) *
        (1 / (t : ℝ) - 1 / (((k : ℝ) + 1) * p)) := by
  let q := (p : ℕ) + h
  let j := (k : ℕ) * (p : ℕ) / q
  let s := (j + 1) * q
  let a := (k : ℕ) * (p : ℕ)
  let b := ((k : ℕ) + 1) * (p : ℕ)
  let t := min s b
  change (∑ n ∈ Ico a b,
      f (((n % (p : ℕ) : ℕ) : ℝ) - ((n % q : ℕ) : ℝ)) /
        ((n : ℝ) * ((n : ℝ) + 1))) =
    f ((j : ℝ) * q - (k : ℝ) * p) * (1 / ((k : ℝ) * p) - 1 / (t : ℝ)) +
      f (((j : ℝ) + 1) * q - (k : ℝ) * p) *
        (1 / (t : ℝ) - 1 / (((k : ℝ) + 1) * p))
  have hq : 0 < q := by dsimp only [q]; positivity
  have ha : 0 < a := by dsimp only [a]; positivity
  have hab : a ≤ b := by dsimp only [a, b]; nlinarith
  have hjas : j * q ≤ a := Nat.div_mul_le_self a q
  have has : a < s := by simpa only [s, j, a, Nat.mul_comm] using Nat.lt_mul_div_succ a hq
  have hsb : b ≤ (j + 1 + 1) * q := by
    have hpq : (p : ℕ) ≤ q := by dsimp only [q]; omega
    dsimp only [a, b, s] at *
    nlinarith
  have hat : a ≤ t := le_min has.le hab
  have htb : t ≤ b := min_le_right _ _
  let g (n : ℕ) := f (((n % (p : ℕ) : ℕ) : ℝ) - ((n % q : ℕ) : ℝ)) /
    ((n : ℝ) * ((n : ℝ) + 1))
  have hfirst (n : ℕ) (hn : n ∈ Ico a t) :
      g n = f ((j : ℝ) * q - (k : ℝ) * p) * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    have hnlo := (mem_Ico.mp hn).1
    have hnhi := (mem_Ico.mp hn).2
    have hnp : n < ((k : ℕ) + 1) * (p : ℕ) := hnhi.trans_le htb
    have hnq : n < (j + 1) * q := hnhi.trans_le (min_le_left _ _)
    dsimp only [g]
    rw [quotient_mod_cast hnlo hnp, quotient_mod_cast (hjas.trans hnlo) hnq]
    rw [mul_one_div]
    congr 2; ring
  have hsecond (n : ℕ) (hn : n ∈ Ico t b) :
      g n = f (((j : ℝ) + 1) * q - (k : ℝ) * p) *
        (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    have hnlo := (mem_Ico.mp hn).1
    have hnhi := (mem_Ico.mp hn).2
    have hst : s = t := by
      have : t < b := hnlo.trans_lt hnhi
      dsimp only [t] at *
      omega
    have hnp : a ≤ n := hat.trans hnlo
    have hnq : (j + 1) * q ≤ n := by simpa only [s, ← hst] using hnlo
    dsimp only [g]
    rw [quotient_mod_cast hnp hnhi, quotient_mod_cast hnq (hnhi.trans_le hsb)]
    push_cast
    rw [mul_one_div]
    congr 2; ring
  change (∑ n ∈ Ico a b, g n) = _
  rw [← sum_Ico_consecutive g hat htb]
  rw [sum_congr rfl (fun n hn => hfirst n hn),
    sum_congr rfl (fun n hn => hsecond n hn)]
  rw [← mul_sum, ← mul_sum, reciprocal_cell_mass ha hat,
    reciprocal_cell_mass (ha.trans_le hat) htb]
  simp only [a, b, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

private theorem all_level_cell_mean_formula (p k : ℕ+) (h : ℕ) :
    let q := (p : ℕ) + h
    let j := (k : ℕ) * (p : ℕ) / q
    let s := (j + 1) * q
    residueGapCellPronicMean p h k =
      if s < ((k : ℕ) + 1) * (p : ℕ) then
        -((k : ℝ) - j) * ((s : ℝ) - (k : ℝ) * p) / ((j : ℝ) + 1)
      else (j : ℝ) * q - (k : ℝ) * p := by
  let q := (p : ℕ) + h
  let j := (k : ℕ) * (p : ℕ) / q
  let s := (j + 1) * q
  change residueGapCellPronicMean p h k =
    if s < ((k : ℕ) + 1) * (p : ℕ) then
      -((k : ℝ) - j) * ((s : ℝ) - (k : ℝ) * p) / ((j : ℝ) + 1)
    else (j : ℝ) * q - (k : ℝ) * p
  have hs := all_level_cell_sum p k h id
  simp only [id_eq] at hs
  change (∑ n ∈ Ico ((k : ℕ) * (p : ℕ)) (((k : ℕ) + 1) * (p : ℕ)),
      (((n % (p : ℕ) : ℕ) : ℝ) - ((n % q : ℕ) : ℝ)) /
        ((n : ℝ) * ((n : ℝ) + 1))) =
    ((j : ℝ) * q - (k : ℝ) * p) *
        (1 / ((k : ℝ) * p) - 1 / ((min s (((k : ℕ) + 1) * (p : ℕ)) : ℕ) : ℝ)) +
      (((j : ℝ) + 1) * q - (k : ℝ) * p) *
        (1 / ((min s (((k : ℕ) + 1) * (p : ℕ)) : ℕ) : ℝ) -
          1 / (((k : ℝ) + 1) * p)) at hs
  unfold residueGapCellPronicMean
  rw [hs]
  change _ = if s < ((k : ℕ) + 1) * (p : ℕ) then _ else _
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hq0 : (q : ℝ) ≠ 0 := by dsimp only [q]; positivity
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  by_cases hh : s < ((k : ℕ) + 1) * (p : ℕ)
  · rw [if_pos hh, min_eq_left hh.le]
    dsimp only [s]
    push_cast
    field_simp
    ring
  · rw [if_neg hh, min_eq_right (not_lt.mp hh)]
    push_cast
    field_simp
    ring

/-- At every quotient level, including after overlap, the local mean remains gap-sized. -/
theorem residueGapCellPronicMean_bounds (p : ℕ+) (h k : ℕ) :
    -(h : ℝ) ≤ residueGapCellPronicMean p h k ∧ residueGapCellPronicMean p h k ≤ 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [residueGapCellPronicMean, Nat.cast_zero, zero_mul]
    exact ⟨neg_nonpos.mpr (Nat.cast_nonneg _), le_rfl⟩
  · let q := (p : ℕ) + h
    let j := k * (p : ℕ) / q
    let s := (j + 1) * q
    have hq : 0 < q := by dsimp only [q]; positivity
    have hlow : j * q ≤ k * (p : ℕ) := Nat.div_mul_le_self (k * (p : ℕ)) q
    have hhigh : k * (p : ℕ) < s := by
      simpa only [s, j, Nat.mul_comm] using Nat.lt_mul_div_succ (k * (p : ℕ)) hq
    have hlowR : (j : ℝ) * q ≤ (k : ℝ) * p := by exact_mod_cast hlow
    have hhighR : (k : ℝ) * p < (s : ℝ) := by exact_mod_cast hhigh
    have he : (s : ℝ) = ((j : ℝ) + 1) * ((p : ℝ) + h) := by
      simp only [s, q, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hm := all_level_cell_mean_formula p ⟨k, hk⟩ h
    change residueGapCellPronicMean p h k = if s < (k + 1) * (p : ℕ) then
      -((k : ℝ) - j) * ((s : ℝ) - (k : ℝ) * p) / ((j : ℝ) + 1)
      else (j : ℝ) * q - (k : ℝ) * p at hm
    rw [hm]
    by_cases hs : s < (k + 1) * (p : ℕ)
    · rw [if_pos hs]
      have hsR : (s : ℝ) < ((k : ℝ) + 1) * p := by exact_mod_cast hs
      have hjk : j + 1 ≤ k := by
        have hpq : (p : ℕ) ≤ q := by dsimp only [q]; omega
        have hmul := Nat.mul_le_mul_left (j + 1) hpq
        have hp := p.pos
        dsimp only [s] at hs
        nlinarith
      have hjkR : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
      have hD : 0 ≤ (s : ℝ) - (k : ℝ) * p := by linarith
      have hrem : 0 ≤ (p : ℝ) - ((s : ℝ) - (k : ℝ) * p) := by linarith
      have hprod := mul_nonneg (show 0 ≤ (k : ℝ) - ((j : ℝ) + 1) by linarith) hrem
      constructor
      · apply (le_div_iff₀ (by positivity : 0 < (j : ℝ) + 1)).mpr
        nlinarith
      · exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) hD) (by positivity)
    · rw [if_neg hs]
      have hsR : ((k : ℝ) + 1) * p ≤ (s : ℝ) := by exact_mod_cast (not_lt.mp hs)
      have hqR : (q : ℝ) = (p : ℝ) + h := by simp only [q, Nat.cast_add]
      constructor <;> nlinarith

/-- Exact conditional mean in terms of the next jump of the larger modulus. -/
theorem residueGapCellPronicMean_eq (p k : ℕ+) (h : ℕ) :
    let q := (p : ℕ) + h
    let j := (k : ℕ) * (p : ℕ) / q
    let s := (j + 1) * q
    residueGapCellPronicMean p h k =
      if s < ((k : ℕ) + 1) * (p : ℕ) then
        -((k : ℝ) - j) * ((s : ℝ) - (k : ℝ) * p) / ((j : ℝ) + 1)
      else (j : ℝ) * q - (k : ℝ) * p :=
  all_level_cell_mean_formula p k h

/-- Centering every quotient cell gives zero mean and an exact jump-spacing variance. -/
theorem residueGapCellPronicMoments (p k : ℕ+) (h : ℕ) :
    let q := (p : ℕ) + h
    let j := (k : ℕ) * (p : ℕ) / q
    let s := (j + 1) * q
    (∑ n ∈ Ico ((k : ℕ) * (p : ℕ)) (((k : ℕ) + 1) * (p : ℕ)),
      (((n % (p : ℕ) : ℕ) : ℝ) - ((n % q : ℕ) : ℝ) - residueGapCellPronicMean p h k) /
        ((n : ℝ) * ((n : ℝ) + 1))) = 0 ∧
    (∑ n ∈ Ico ((k : ℕ) * (p : ℕ)) (((k : ℕ) + 1) * (p : ℕ)),
      (((n % (p : ℕ) : ℕ) : ℝ) - ((n % q : ℕ) : ℝ) - residueGapCellPronicMean p h k) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      if s < ((k : ℕ) + 1) * (p : ℕ) then
        ((s : ℝ) - (k : ℝ) * p) * (((k : ℝ) + 1) * p - s) /
          (((j : ℝ) + 1) ^ 2 * p)
      else 0 := by
  let q := (p : ℕ) + h
  let j := (k : ℕ) * (p : ℕ) / q
  let s := (j + 1) * q
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hq0 : (q : ℝ) ≠ 0 := by dsimp only [q]; positivity
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have hmass : (∑ n ∈ Ico ((k : ℕ) * (p : ℕ)) (((k : ℕ) + 1) * (p : ℕ)),
      1 / ((n : ℝ) * ((n : ℝ) + 1))) = 1 / ((k : ℝ) * ((k : ℝ) + 1) * p) := by
    rw [reciprocal_cell_mass (by positivity) (by nlinarith : (k : ℕ) * p ≤ ((k : ℕ) + 1) * p)]
    push_cast
    field_simp
    ring
  constructor
  · calc
      _ = (∑ n ∈ Ico ((k : ℕ) * (p : ℕ)) (((k : ℕ) + 1) * (p : ℕ)),
          (((n % (p : ℕ) : ℕ) : ℝ) - ((n % q : ℕ) : ℝ)) / ((n : ℝ) * ((n : ℝ) + 1))) -
          residueGapCellPronicMean p h k *
            (∑ n ∈ Ico ((k : ℕ) * (p : ℕ)) (((k : ℕ) + 1) * (p : ℕ)),
              1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        simp_rw [sub_div]
        rw [sum_sub_distrib, mul_sum]
        congr 1
        apply sum_congr rfl
        intro n _
        ring
      _ = 0 := by
        rw [hmass]
        unfold residueGapCellPronicMean
        field_simp
        ring
  · rw [all_level_cell_sum p k h (fun x => (x - residueGapCellPronicMean p h k) ^ 2)]
    change (((j : ℝ) * q - (k : ℝ) * p) - residueGapCellPronicMean p h k) ^ 2 *
        (1 / ((k : ℝ) * p) - 1 / ((min s (((k : ℕ) + 1) * (p : ℕ)) : ℕ) : ℝ)) +
      ((((j : ℝ) + 1) * q - (k : ℝ) * p) - residueGapCellPronicMean p h k) ^ 2 *
        (1 / ((min s (((k : ℕ) + 1) * (p : ℕ)) : ℕ) : ℝ) -
          1 / (((k : ℝ) + 1) * p)) =
      if s < ((k : ℕ) + 1) * (p : ℕ) then
        ((s : ℝ) - (k : ℝ) * p) * (((k : ℝ) + 1) * p - s) /
          (((j : ℝ) + 1) ^ 2 * p)
      else 0
    have hm := all_level_cell_mean_formula p k h
    change residueGapCellPronicMean p h k = if s < ((k : ℕ) + 1) * (p : ℕ) then
      -((k : ℝ) - j) * ((s : ℝ) - (k : ℝ) * p) / ((j : ℝ) + 1)
      else (j : ℝ) * q - (k : ℝ) * p at hm
    rw [hm]
    by_cases hh : s < ((k : ℕ) + 1) * (p : ℕ)
    · simp only [if_pos hh, min_eq_left hh.le]
      dsimp only [s]
      push_cast
      field_simp
      ring
    · simp only [if_neg hh, min_eq_right (not_lt.mp hh)]
      push_cast
      field_simp
      ring

private theorem gap_weighted_cauchy (m : ℕ) (a : ℕ → ℝ) (h : ℕ → ℕ) :
    (∑ i ∈ range m, a i * (h i : ℝ)) ^ 2 ≤
      (∑ i ∈ range m, (h i : ℝ)) * ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ) := by
  have hs (i : ℕ) : (Real.sqrt (h i : ℝ)) ^ 2 = (h i : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have he (i : ℕ) : Real.sqrt (h i : ℝ) * (a i * Real.sqrt (h i : ℝ)) = a i * (h i : ℝ) := by
    calc
      _ = a i * (Real.sqrt (h i : ℝ)) ^ 2 := by ring
      _ = _ := by rw [hs]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (range m)
    (fun i => Real.sqrt (h i : ℝ)) (fun i => a i * Real.sqrt (h i : ℝ))
  simpa only [he, mul_pow, hs] using hc

/-- The collective local-mean part has a uniform energy bound at every horizon. -/
theorem residueGapCellPronicMean_collective_energy_le (P : ℕ+) (m T : ℕ)
    (offset h : ℕ → ℕ) (a : ℕ → ℝ) :
    (∑ n ∈ range T,
      (∑ i ∈ range m, a i * residueGapCellPronicMean ((P : ℕ) + offset i) (h i)
        (n / ((P : ℕ) + offset i))) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
      (((∑ i ∈ range m, h i : ℕ) : ℝ) / P) *
        ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ) := by
  let F (n : ℕ) := ∑ i ∈ range m, a i *
    residueGapCellPronicMean ((P : ℕ) + offset i) (h i) (n / ((P : ℕ) + offset i))
  let H := ∑ i ∈ range m, h i
  let A := ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ)
  let B := ∑ i ∈ range m, |a i| * (h i : ℝ)
  have hA : 0 ≤ A := sum_nonneg fun _ _ => by positivity
  have hB : 0 ≤ B := sum_nonneg fun _ _ => by positivity
  have hbound (n : ℕ) : (F n) ^ 2 ≤ (H : ℝ) * A := by
    have hm (i : ℕ) :
        |residueGapCellPronicMean ((P : ℕ) + offset i) (h i) (n / ((P : ℕ) + offset i))| ≤ (h i : ℝ) := by
      have hp : 0 < (P : ℕ) + offset i := by have := P.pos; omega
      have hb := residueGapCellPronicMean_bounds ⟨(P : ℕ) + offset i, hp⟩ (h i)
        (n / ((P : ℕ) + offset i))
      exact abs_le.mpr ⟨hb.1, hb.2.trans (Nat.cast_nonneg _)⟩
    have htri : |F n| ≤ B := by
      calc
        _ ≤ ∑ i ∈ range m,
            |a i * residueGapCellPronicMean ((P : ℕ) + offset i) (h i) (n / ((P : ℕ) + offset i))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ B := by
          apply sum_le_sum
          intro i _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hm i) (abs_nonneg _)
    have hp := mul_nonneg (sub_nonneg.mpr htri) (add_nonneg hB (abs_nonneg (F n)))
    have hc := gap_weighted_cauchy m (fun i => |a i|) h
    simp only [sq_abs, ← Nat.cast_sum] at hc
    change B ^ 2 ≤ (H : ℝ) * A at hc
    nlinarith [sq_abs (F n)]
  have hzero (n : ℕ) (hn : n < (P : ℕ)) : F n = 0 := by
    apply sum_eq_zero
    intro i _
    rw [Nat.div_eq_of_lt (by omega : n < (P : ℕ) + offset i)]
    simp only [residueGapCellPronicMean, Nat.cast_zero, zero_mul, mul_zero]
  change (∑ n ∈ range T, (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ (H : ℝ) / P * A
  by_cases hT : T < (P : ℕ)
  · have hz : (∑ n ∈ range T, (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) = 0 := by
      apply sum_eq_zero
      intro n hn
      rw [hzero n ((mem_range.mp hn).trans hT)]
      simp
    rw [hz]
    positivity
  · have hPT : (P : ℕ) ≤ T := by omega
    have hz : (∑ n ∈ range (P : ℕ), (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) = 0 := by
      apply sum_eq_zero
      intro n hn
      rw [hzero n (mem_range.mp hn)]
      simp
    rw [← sum_range_add_sum_Ico (fun n => (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) hPT,
      hz, zero_add]
    calc
      _ ≤ ∑ n ∈ Ico (P : ℕ) T,
          ((H : ℝ) * A) * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        apply sum_le_sum
        intro n _
        simpa only [mul_one_div] using
          div_le_div_of_nonneg_right (hbound n) (by positivity)
      _ = ((H : ℝ) * A) * (1 / (P : ℝ) - 1 / T) := by
        rw [← mul_sum, reciprocal_cell_mass P.pos hPT]
      _ ≤ ((H : ℝ) * A) * (1 / (P : ℝ)) :=
        mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (mul_nonneg (Nat.cast_nonneg _) hA)
      _ = _ := by ring

/-- The full literal packet reduces to its locally centered cells with a uniform mean-part cost. -/
theorem residueGapPacket_energy_le_centered_add_mean_budget (P : ℕ+) (m T : ℕ)
    (offset h : ℕ → ℕ) (a : ℕ → ℝ) :
    (∑ n ∈ range T,
      (∑ i ∈ range m, a i *
        (((n % ((P : ℕ) + offset i) : ℕ) : ℝ) -
          ((n % ((P : ℕ) + offset i + h i) : ℕ) : ℝ))) ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1))) ≤
      2 * (∑ n ∈ range T,
        (∑ i ∈ range m, a i *
          (((n % ((P : ℕ) + offset i) : ℕ) : ℝ) -
            ((n % ((P : ℕ) + offset i + h i) : ℕ) : ℝ) -
            residueGapCellPronicMean ((P : ℕ) + offset i) (h i) (n / ((P : ℕ) + offset i)))) ^ 2 /
              ((n : ℝ) * ((n : ℝ) + 1))) +
      2 * (((∑ i ∈ range m, h i : ℕ) : ℝ) / P) *
        ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ) := by
  let R (n : ℕ) := ∑ i ∈ range m, a i *
    (((n % ((P : ℕ) + offset i) : ℕ) : ℝ) -
      ((n % ((P : ℕ) + offset i + h i) : ℕ) : ℝ))
  let M (n : ℕ) := ∑ i ∈ range m, a i *
    residueGapCellPronicMean ((P : ℕ) + offset i) (h i) (n / ((P : ℕ) + offset i))
  let W (n : ℕ) := ∑ i ∈ range m, a i *
    (((n % ((P : ℕ) + offset i) : ℕ) : ℝ) -
      ((n % ((P : ℕ) + offset i + h i) : ℕ) : ℝ) -
        residueGapCellPronicMean ((P : ℕ) + offset i) (h i) (n / ((P : ℕ) + offset i)))
  have hsplit (n : ℕ) : R n = W n + M n := by
    dsimp only [W, R, M]
    simp only [mul_sub, sum_sub_distrib]
    ring
  have htriangle : (∑ n ∈ range T, (R n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
      2 * (∑ n ∈ range T, (W n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) +
      2 * (∑ n ∈ range T, (M n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
    calc
      _ ≤ ∑ n ∈ range T, (2 * (W n) ^ 2 + 2 * (M n) ^ 2) /
          ((n : ℝ) * ((n : ℝ) + 1)) := by
        apply sum_le_sum
        intro n _
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [hsplit]
        nlinarith [sq_nonneg (W n - M n)]
      _ = _ := by
        simp_rw [add_div, mul_div_assoc]
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hm := residueGapCellPronicMean_collective_energy_le P m T offset h a
  change (∑ n ∈ range T, (M n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ _ at hm
  change (∑ n ∈ range T, (R n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
    2 * (∑ n ∈ range T, (W n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) + _
  linarith

end
end GaloisForLFunctions.BezoutValuationIncidence

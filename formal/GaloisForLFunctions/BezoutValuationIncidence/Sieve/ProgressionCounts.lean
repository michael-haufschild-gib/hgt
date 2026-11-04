import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Unit discrepancies for residue-class interval counts

The count in any integer interval differs from its residue-class density
by less than one. Coprime progression and divisibility conditions combine
into one residue class, so the same discrepancy applies to sieve remainders.
-/

namespace GaloisForLFunctions.BezoutValuationIncidence

open Finset

/-- A residue-class interval count has discrepancy strictly less than one. -/
theorem abs_card_residue_Ioc_sub_lt_one {A B r v : ℕ}
    (hr : 0 < r) (hAB : A ≤ B) :
    |((#{n ∈ Ioc A B | n ≡ v [MOD r]} : ℕ) : ℝ) -
      ((B : ℝ) - A) / r| < 1 := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hABQ : (A : ℚ) ≤ B := by exact_mod_cast hAB
  have hm := Int.floor_mono
    (div_le_div_of_nonneg_right (sub_le_sub_right hABQ (v : ℚ)) hrQ.le)
  have hc := Nat.Ioc_filter_modEq_card A B hr v
  rw [max_eq_left (sub_nonneg.mpr hm)] at hc
  have hcQ : ((#{n ∈ Ioc A B | n ≡ v [MOD r]} : ℕ) : ℚ) =
      (⌊((B : ℚ) - v) / r⌋ : ℚ) - (⌊((A : ℚ) - v) / r⌋ : ℚ) := by
    exact_mod_cast hc
  have he : ((B : ℚ) - A) / r = ((B : ℚ) - v) / r - ((A : ℚ) - v) / r := by ring
  have hb1 := Int.floor_le (((B : ℚ) - v) / r)
  have hb2 := Int.lt_floor_add_one (((B : ℚ) - v) / r)
  have ha1 := Int.floor_le (((A : ℚ) - v) / r)
  have ha2 := Int.lt_floor_add_one (((A : ℚ) - v) / r)
  have hRat : |((#{n ∈ Ioc A B | n ≡ v [MOD r]} : ℕ) : ℚ) -
      ((B : ℚ) - A) / r| < 1 := by
    rw [hcQ, he, abs_lt]
    constructor <;> linarith only [ha1, ha2, hb1, hb2]
  have hReal : ((|((#{n ∈ Ioc A B | n ≡ v [MOD r]} : ℕ) : ℚ) -
      ((B : ℚ) - A) / r| : ℚ) : ℝ) < ((1 : ℚ) : ℝ) := Rat.cast_lt.mpr hRat
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_one] using hReal

/-- Two residue conditions with coprime moduli form one residue class. -/
theorem exists_coprime_residue_intersection {p d a b : ℕ} (hpd : p.Coprime d) :
    ∃ v : ℕ, ∀ n : ℕ, (n ≡ a [MOD p] ∧ n ≡ b [MOD d]) ↔ n ≡ v [MOD p * d] := by
  let v := Nat.chineseRemainder hpd a b
  refine ⟨v, fun n => ?_⟩
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hpd]
  constructor
  · rintro ⟨hp, hd⟩
    exact ⟨hp.trans v.property.1.symm, hd.trans v.property.2.symm⟩
  · rintro ⟨hp, hd⟩
    exact ⟨hp.trans v.property.1, hd.trans v.property.2⟩

/-- Coprime progression and divisibility conditions form one residue class. -/
theorem exists_progression_divisibility_residue {p d a : ℕ} (hpd : p.Coprime d) :
    ∃ v : ℕ, ∀ n : ℕ, (n ≡ a [MOD p] ∧ d ∣ n) ↔ n ≡ v [MOD p * d] := by
  simpa only [Nat.modEq_zero_iff_dvd] using
    (exists_coprime_residue_intersection (a := a) (b := 0) hpd)

/-- An intersection of coprime residue classes has unit counting discrepancy. -/
theorem abs_card_coprime_residues_Ioc_sub_lt_one {A B p d a b : ℕ}
    (hAB : A ≤ B) (hp : 0 < p) (hd : 0 < d) (hpd : p.Coprime d) :
    |((#{n ∈ Ioc A B | n ≡ a [MOD p] ∧ n ≡ b [MOD d]} : ℕ) : ℝ) -
      ((B : ℝ) - A) / ((p : ℝ) * d)| < 1 := by
  obtain ⟨v, hv⟩ := exists_coprime_residue_intersection (a := a) (b := b) hpd
  have hset : {n ∈ Ioc A B | n ≡ a [MOD p] ∧ n ≡ b [MOD d]} =
      {n ∈ Ioc A B | n ≡ v [MOD p * d]} := filter_congr fun n _ => hv n
  rw [hset]
  simpa only [Nat.cast_mul] using
    abs_card_residue_Ioc_sub_lt_one (v := v) (Nat.mul_pos hp hd) hAB

/-- Sieve multiples in a coprime progression have unit counting discrepancy. -/
theorem abs_card_progression_dvd_Ioc_sub_lt_one {A B p d a : ℕ}
    (hAB : A ≤ B) (hp : 0 < p) (hd : 0 < d) (hpd : p.Coprime d) :
    |((#{n ∈ Ioc A B | n ≡ a [MOD p] ∧ d ∣ n} : ℕ) : ℝ) -
      ((B : ℝ) - A) / ((p : ℝ) * d)| < 1 := by
  simpa only [Nat.modEq_zero_iff_dvd] using
    (abs_card_coprime_residues_Ioc_sub_lt_one (a := a) (b := 0) hAB hp hd hpd)

#print axioms abs_card_residue_Ioc_sub_lt_one
#print axioms abs_card_progression_dvd_Ioc_sub_lt_one

end GaloisForLFunctions.BezoutValuationIncidence

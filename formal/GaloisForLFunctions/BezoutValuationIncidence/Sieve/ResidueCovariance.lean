import GaloisForLFunctions.BezoutValuationIncidence.Sieve.ProgressionCounts
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field

/-!
# Exact period means and bounded residue covariance errors

Coprime centered residues have zero joint period mean. Equal moduli retain
the collision density minus the product of the marginal densities. Unit
interval-count discrepancies bound both errors independently of interval length.
-/

noncomputable section
set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.BezoutValuationIncidence


/-- Indicator of a residue class. -/
def residueIndicator (p a n : ℕ) : ℝ := if n ≡ a [MOD p] then 1 else 0
/-- Residue indicator with its complete-period mean removed. -/
def centeredResidue (p a n : ℕ) : ℝ := residueIndicator p a n - 1 / (p : ℝ)

theorem sum_residue (S : Finset ℕ) (p a : ℕ) :
    (∑ n ∈ S, residueIndicator p a n) = ((#{n ∈ S | n ≡ a [MOD p]} : ℕ) : ℝ) :=
  (natCast_card_filter (fun n => n ≡ a [MOD p]) S).symm

theorem sum_residue_product (S : Finset ℕ) (p q a b : ℕ) :
    (∑ n ∈ S, residueIndicator p a n * residueIndicator q b n) =
      ((#{n ∈ S | n ≡ a [MOD p] ∧ n ≡ b [MOD q]} : ℕ) : ℝ) := by
  have he (n : ℕ) : residueIndicator p a n * residueIndicator q b n =
      if n ≡ a [MOD p] ∧ n ≡ b [MOD q] then (1 : ℝ) else 0 := by
    by_cases hp : n ≡ a [MOD p] <;> by_cases hq : n ≡ b [MOD q] <;>
      simp only [residueIndicator, hp, hq, and_self, and_false, false_and,
        if_true, if_false, mul_zero, mul_one]
  rw [sum_congr rfl (fun n _ => he n)]
  exact (natCast_card_filter _ _).symm

theorem centered_product_sum (S : Finset ℕ) (p q a b : ℕ) :
    (∑ n ∈ S, centeredResidue p a n * centeredResidue q b n) =
      ((#{n ∈ S | n ≡ a [MOD p] ∧ n ≡ b [MOD q]} : ℕ) : ℝ) -
        ((#{n ∈ S | n ≡ a [MOD p]} : ℕ) : ℝ) / q -
        ((#{n ∈ S | n ≡ b [MOD q]} : ℕ) : ℝ) / p +
        (S.card : ℝ) / ((p : ℝ) * q) := by
  have he (n : ℕ) : centeredResidue p a n * centeredResidue q b n =
      residueIndicator p a n * residueIndicator q b n -
        residueIndicator p a n / q - residueIndicator q b n / p +
        1 / ((p : ℝ) * q) := by unfold centeredResidue; ring
  rw [sum_congr rfl (fun n _ => he n), sum_add_distrib, sum_sub_distrib,
    sum_sub_distrib, ← sum_div, ← sum_div, sum_residue_product,
    sum_residue, sum_residue, sum_const, nsmul_eq_mul]
  ring

/-- Coprime centered residues have uniformly bounded interval covariance. -/
theorem coprime_residue_covariance {A B p q a b : ℕ} (hAB : A ≤ B) (hp : 0 < p) (hq : 0 < q)
    (hpq : p.Coprime q) :
    |∑ n ∈ Ioc A B, centeredResidue p a n * centeredResidue q b n| ≤
      1 + 1 / (p : ℝ) + 1 / (q : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let L := (B : ℝ) - A
  let Cp : ℝ := (#{n ∈ Ioc A B | n ≡ a [MOD p]} : ℕ)
  let Cq : ℝ := (#{n ∈ Ioc A B | n ≡ b [MOD q]} : ℕ)
  let Cpq : ℝ := (#{n ∈ Ioc A B | n ≡ a [MOD p] ∧ n ≡ b [MOD q]} : ℕ)
  have h1 : |Cpq - L / ((p : ℝ) * q)| ≤ 1 :=
    (abs_card_coprime_residues_Ioc_sub_lt_one hAB hp hq hpq).le
  have h2 : |(Cp - L / p) / q| ≤ 1 / (q : ℝ) := by
    rw [abs_div, abs_of_pos hqR]
    exact div_le_div_of_nonneg_right (abs_card_residue_Ioc_sub_lt_one hp hAB).le hqR.le
  have h3 : |(Cq - L / q) / p| ≤ 1 / (p : ℝ) := by
    rw [abs_div, abs_of_pos hpR]
    exact div_le_div_of_nonneg_right (abs_card_residue_Ioc_sub_lt_one hq hAB).le hpR.le
  have hcard : ((Ioc A B).card : ℝ) = L := by
    rw [Nat.card_Ioc, Nat.cast_sub hAB]
  have he : (∑ n ∈ Ioc A B, centeredResidue p a n * centeredResidue q b n) =
      (Cpq - L / ((p : ℝ) * q)) - (Cp - L / p) / q - (Cq - L / q) / p := by
    rw [centered_product_sum, hcard]
    change Cpq - Cp / q - Cq / p + L / ((p : ℝ) * q) = _
    ring
  rw [he]
  calc
    _ ≤ |(Cpq - L / ((p : ℝ) * q)) - (Cp - L / p) / q| + |(Cq - L / q) / p| :=
      abs_sub _ _
    _ ≤ (|Cpq - L / ((p : ℝ) * q)| + |(Cp - L / p) / q|) + |(Cq - L / q) / p| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ (1 + 1 / (q : ℝ)) + 1 / (p : ℝ) := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

theorem sum_same_residue_product (S : Finset ℕ) (p a b : ℕ) :
    (∑ n ∈ S, residueIndicator p a n * residueIndicator p b n) =
      if a ≡ b [MOD p] then ((#{n ∈ S | n ≡ a [MOD p]} : ℕ) : ℝ) else 0 := by
  by_cases hab : a ≡ b [MOD p]
  · rw [if_pos hab]
    have he (n : ℕ) : residueIndicator p a n * residueIndicator p b n =
        residueIndicator p a n := by
      by_cases hna : n ≡ a [MOD p]
      · have hnb := hna.trans hab
        simp only [residueIndicator, hna, hnb, if_true, mul_one]
      · simp only [residueIndicator, hna, if_false, zero_mul]
    rw [sum_congr rfl (fun n _ => he n), sum_residue]
  · rw [if_neg hab]
    apply sum_eq_zero
    intro n _
    by_cases hna : n ≡ a [MOD p]
    · have hnb : ¬n ≡ b [MOD p] := fun hnb => hab (hna.symm.trans hnb)
      simp only [residueIndicator, hna, hnb, if_true, if_false, mul_zero]
    · simp only [residueIndicator, hna, if_false, zero_mul]

/-- Equal moduli retain precisely the residue-collision covariance, up to endpoint error. -/
theorem same_residue_covariance {A B p a b : ℕ} (hAB : A ≤ B) (hp : 0 < p) :
    |(∑ n ∈ Ioc A B, centeredResidue p a n * centeredResidue p b n) -
      ((B : ℝ) - A) * ((if a ≡ b [MOD p] then 1 / (p : ℝ) else 0) -
        1 / (p : ℝ) ^ 2)| ≤ 1 + 2 / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  let L := (B : ℝ) - A
  let Ca : ℝ := (#{n ∈ Ioc A B | n ≡ a [MOD p]} : ℕ)
  let Cb : ℝ := (#{n ∈ Ioc A B | n ≡ b [MOD p]} : ℕ)
  let Cab : ℝ := if a ≡ b [MOD p] then Ca else 0
  let delta : ℝ := if a ≡ b [MOD p] then 1 / (p : ℝ) else 0
  have h1 : |Cab - L * delta| ≤ 1 := by
    by_cases hab : a ≡ b [MOD p]
    · simpa only [Cab, delta, hab, if_true, mul_one_div] using
        (abs_card_residue_Ioc_sub_lt_one (v := a) hp hAB).le
    · simp only [Cab, delta, hab, if_false, mul_zero, sub_self, abs_zero, zero_le_one]
  have h2 : |(Ca - L / p) / p| ≤ 1 / (p : ℝ) := by
    rw [abs_div, abs_of_pos hpR]
    exact div_le_div_of_nonneg_right
      (abs_card_residue_Ioc_sub_lt_one (v := a) hp hAB).le hpR.le
  have h3 : |(Cb - L / p) / p| ≤ 1 / (p : ℝ) := by
    rw [abs_div, abs_of_pos hpR]
    exact div_le_div_of_nonneg_right
      (abs_card_residue_Ioc_sub_lt_one (v := b) hp hAB).le hpR.le
  have hcard : ((Ioc A B).card : ℝ) = L := by
    rw [Nat.card_Ioc, Nat.cast_sub hAB]
  have hprod : ((#{n ∈ Ioc A B | n ≡ a [MOD p] ∧ n ≡ b [MOD p]} : ℕ) : ℝ) = Cab := by
    rw [← sum_residue_product, sum_same_residue_product]
  have he : (∑ n ∈ Ioc A B, centeredResidue p a n * centeredResidue p b n) -
      L * (delta - 1 / (p : ℝ) ^ 2) =
      (Cab - L * delta) - (Ca - L / p) / p - (Cb - L / p) / p := by
    rw [centered_product_sum, hcard, hprod]
    change Cab - Ca / p - Cb / p + L / ((p : ℝ) * p) - _ = _
    ring
  change |(∑ n ∈ Ioc A B, centeredResidue p a n * centeredResidue p b n) -
    L * (delta - 1 / (p : ℝ) ^ 2)| ≤ _
  rw [he]
  calc
    _ ≤ |(Cab - L * delta) - (Ca - L / p) / p| + |(Cb - L / p) / p| := abs_sub _ _
    _ ≤ (|Cab - L * delta| + |(Ca - L / p) / p|) + |(Cb - L / p) / p| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ (1 + 1 / (p : ℝ)) + 1 / (p : ℝ) := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

#print axioms coprime_residue_covariance
#print axioms same_residue_covariance

end GaloisForLFunctions.BezoutValuationIncidence

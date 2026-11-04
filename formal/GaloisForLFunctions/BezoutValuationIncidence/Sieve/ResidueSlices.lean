import GaloisForLFunctions.BezoutValuationIncidence.Sieve.ResidueCovariance

/-!
# Prime covariance on a fixed coprime residue slice

Chinese remaindering retains the exact covariance density. The four finite
count discrepancies remain bounded independently of the moduli.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace GaloisForLFunctions.BezoutValuationIncidence

private theorem abs_four_terms (a b c d : ℝ) :
    |a - b - c + d| ≤ |a| + |b| + |c| + |d| := by
  refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)

private theorem residue_intersection_indicator {M p r a v : ℕ}
    (hv : ∀ n : ℕ, (n ≡ r [MOD M] ∧ n ≡ a [MOD p]) ↔ n ≡ v [MOD M * p]) (n : ℕ) :
    residueIndicator M r n * residueIndicator p a n = residueIndicator (M * p) v n := by
  unfold residueIndicator
  simp only [← hv n]
  by_cases hM : n ≡ r [MOD M] <;> by_cases hp : n ≡ a [MOD p] <;>
    simp only [hM, hp, and_self, and_false, false_and, if_true, if_false, mul_zero, mul_one]

/-- Fixing a coprime residue slice still leaves only four unit count errors. -/
theorem coprime_covariance_residue_slice {A B M p q r a b : ℕ}
    (hAB : A ≤ B) (hM : 0 < M) (hp : 0 < p) (hq : 0 < q)
    (hMp : M.Coprime p) (hMq : M.Coprime q) (hpq : p.Coprime q) :
    |∑ n ∈ Ioc A B, residueIndicator M r n * centeredResidue p a n * centeredResidue q b n| ≤
      (1 + 1 / (p : ℝ)) * (1 + 1 / (q : ℝ)) := by
  obtain ⟨v, hv⟩ := exists_coprime_residue_intersection (a := r) (b := a) hMp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  let L : ℝ := (B : ℝ) - A
  let C0 : ℝ := (#{n ∈ Ioc A B | n ≡ r [MOD M]} : ℕ)
  let Cp : ℝ := (#{n ∈ Ioc A B | n ≡ v [MOD M * p]} : ℕ)
  let Cq : ℝ := (#{n ∈ Ioc A B | n ≡ r [MOD M] ∧ n ≡ b [MOD q]} : ℕ)
  let Cpq : ℝ := (#{n ∈ Ioc A B | n ≡ v [MOD M * p] ∧ n ≡ b [MOD q]} : ℕ)
  have hterm (n : ℕ) :
      residueIndicator M r n * centeredResidue p a n * centeredResidue q b n =
        residueIndicator (M * p) v n * residueIndicator q b n -
          residueIndicator (M * p) v n / q -
            (residueIndicator M r n * residueIndicator q b n) / p +
              residueIndicator M r n / ((p : ℝ) * q) := by
    rw [← residue_intersection_indicator hv n]
    unfold centeredResidue
    ring
  have hsum : (∑ n ∈ Ioc A B,
      residueIndicator M r n * centeredResidue p a n * centeredResidue q b n) =
        Cpq - Cp / q - Cq / p + C0 / ((p : ℝ) * q) := by
    rw [sum_congr rfl (fun n _ => hterm n), sum_add_distrib, sum_sub_distrib,
      sum_sub_distrib, ← sum_div, ← sum_div, ← sum_div,
      sum_residue_product, sum_residue, sum_residue_product, sum_residue]
  have h1 : |Cpq - L / (((M : ℝ) * p) * q)| ≤ 1 := by
    simpa only [Nat.cast_mul] using
      (abs_card_coprime_residues_Ioc_sub_lt_one (a := v) (b := b) hAB
        (Nat.mul_pos hM hp) hq (hMq.mul_left hpq)).le
  have h2 : |(Cp - L / ((M : ℝ) * p)) / q| ≤ 1 / (q : ℝ) := by
    rw [abs_div, show |(q : ℝ)| = (q : ℝ) from abs_of_pos hq0]
    apply div_le_div_of_nonneg_right _ hq0.le
    simpa only [Nat.cast_mul] using
      (abs_card_residue_Ioc_sub_lt_one (v := v) (Nat.mul_pos hM hp) hAB).le
  have h3 : |(Cq - L / ((M : ℝ) * q)) / p| ≤ 1 / (p : ℝ) := by
    rw [abs_div, show |(p : ℝ)| = (p : ℝ) from abs_of_pos hp0]
    exact div_le_div_of_nonneg_right
      (abs_card_coprime_residues_Ioc_sub_lt_one (a := r) (b := b) hAB hM hq hMq).le hp0.le
  have h4 : |(C0 - L / M) / ((p : ℝ) * q)| ≤ 1 / ((p : ℝ) * q) := by
    rw [abs_div, show |(p : ℝ) * q| = (p : ℝ) * q from abs_of_pos (mul_pos hp0 hq0)]
    exact div_le_div_of_nonneg_right (abs_card_residue_Ioc_sub_lt_one (v := r) hM hAB).le
      (mul_pos hp0 hq0).le
  have he : Cpq - Cp / q - Cq / p + C0 / ((p : ℝ) * q) =
      (Cpq - L / (((M : ℝ) * p) * q)) - (Cp - L / ((M : ℝ) * p)) / q -
        (Cq - L / ((M : ℝ) * q)) / p + (C0 - L / M) / ((p : ℝ) * q) := by ring
  rw [hsum, he]
  refine (abs_four_terms _ _ _ _).trans ?_
  exact (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans_eq (by ring)

#print axioms coprime_covariance_residue_slice

private theorem same_residue_indicator_product (p a b n : ℕ) :
    residueIndicator p a n * residueIndicator p b n =
      if a ≡ b [MOD p] then residueIndicator p a n else 0 := by
  by_cases hab : a ≡ b [MOD p]
  · rw [if_pos hab]
    by_cases hna : n ≡ a [MOD p]
    · simp only [residueIndicator, hna, hna.trans hab, if_true, mul_one]
    · simp only [residueIndicator, hna, if_false, zero_mul]
  · rw [if_neg hab]
    by_cases hna : n ≡ a [MOD p]
    · have hnb : ¬n ≡ b [MOD p] := fun hnb => hab (hna.symm.trans hnb)
      simp only [residueIndicator, hna, hnb, if_true, if_false, mul_zero]
    · simp only [residueIndicator, hna, if_false, zero_mul]

/-- An equal-prime collision has the same covariance density in each coprime residue slice. -/
theorem same_covariance_residue_slice {A B M p r a b : ℕ}
    (hAB : A ≤ B) (hM : 0 < M) (hp : 0 < p) (hMp : M.Coprime p) :
    |(∑ n ∈ Ioc A B, residueIndicator M r n * centeredResidue p a n * centeredResidue p b n) -
      (((B : ℝ) - A) / M) *
        ((if a ≡ b [MOD p] then 1 / (p : ℝ) else 0) - 1 / (p : ℝ) ^ 2)| ≤
      (1 + 1 / (p : ℝ)) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  let L : ℝ := (B : ℝ) - A
  let C0 : ℝ := (#{n ∈ Ioc A B | n ≡ r [MOD M]} : ℕ)
  let Ca : ℝ := (#{n ∈ Ioc A B | n ≡ r [MOD M] ∧ n ≡ a [MOD p]} : ℕ)
  let Cb : ℝ := (#{n ∈ Ioc A B | n ≡ r [MOD M] ∧ n ≡ b [MOD p]} : ℕ)
  let Cab : ℝ := if a ≡ b [MOD p] then Ca else 0
  let delta : ℝ := if a ≡ b [MOD p] then 1 / (p : ℝ) else 0
  have hterm (n : ℕ) :
      residueIndicator M r n * centeredResidue p a n * centeredResidue p b n =
        (if a ≡ b [MOD p] then residueIndicator M r n * residueIndicator p a n else 0) -
          (residueIndicator M r n * residueIndicator p a n) / p -
            (residueIndicator M r n * residueIndicator p b n) / p +
              residueIndicator M r n / (p : ℝ) ^ 2 := by
    calc
      _ = residueIndicator M r n * (residueIndicator p a n * residueIndicator p b n) -
          (residueIndicator M r n * residueIndicator p a n) / p -
            (residueIndicator M r n * residueIndicator p b n) / p +
              residueIndicator M r n / (p : ℝ) ^ 2 := by unfold centeredResidue; ring
      _ = _ := by
        rw [same_residue_indicator_product]
        split_ifs <;> ring
  have hfirst : (∑ n ∈ Ioc A B,
      if a ≡ b [MOD p] then residueIndicator M r n * residueIndicator p a n else 0) = Cab := by
    by_cases hab : a ≡ b [MOD p]
    · simp only [if_pos hab, Cab, Ca, sum_residue_product]
    · simp only [if_neg hab, Cab, sum_const_zero]
  have hsum : (∑ n ∈ Ioc A B,
      residueIndicator M r n * centeredResidue p a n * centeredResidue p b n) =
        Cab - Ca / p - Cb / p + C0 / (p : ℝ) ^ 2 := by
    rw [sum_congr rfl (fun n _ => hterm n), sum_add_distrib, sum_sub_distrib,
      sum_sub_distrib, hfirst, ← sum_div, ← sum_div, ← sum_div,
      sum_residue_product, sum_residue_product, sum_residue]
  have h1 : |Cab - (L / M) * delta| ≤ 1 := by
    by_cases hab : a ≡ b [MOD p]
    · simp only [Cab, delta, if_pos hab]
      rw [show (L / M) * (1 / (p : ℝ)) = L / ((M : ℝ) * p) by ring]
      exact (abs_card_coprime_residues_Ioc_sub_lt_one (a := r) (b := a) hAB hM hp hMp).le
    · simp only [Cab, delta, if_neg hab, mul_zero, sub_self, abs_zero, zero_le_one]
  have h2 : |(Ca - L / ((M : ℝ) * p)) / p| ≤ 1 / (p : ℝ) := by
    rw [abs_div, show |(p : ℝ)| = (p : ℝ) from abs_of_pos hp0]
    exact div_le_div_of_nonneg_right
      (abs_card_coprime_residues_Ioc_sub_lt_one (a := r) (b := a) hAB hM hp hMp).le hp0.le
  have h3 : |(Cb - L / ((M : ℝ) * p)) / p| ≤ 1 / (p : ℝ) := by
    rw [abs_div, show |(p : ℝ)| = (p : ℝ) from abs_of_pos hp0]
    exact div_le_div_of_nonneg_right
      (abs_card_coprime_residues_Ioc_sub_lt_one (a := r) (b := b) hAB hM hp hMp).le hp0.le
  have h4 : |(C0 - L / M) / (p : ℝ) ^ 2| ≤ 1 / (p : ℝ) ^ 2 := by
    rw [abs_div, abs_of_nonneg (sq_nonneg (p : ℝ))]
    exact div_le_div_of_nonneg_right (abs_card_residue_Ioc_sub_lt_one (v := r) hM hAB).le
      (sq_nonneg (p : ℝ))
  have he : Cab - Ca / p - Cb / p + C0 / (p : ℝ) ^ 2 - (L / M) * (delta - 1 / (p : ℝ) ^ 2) =
      (Cab - (L / M) * delta) - (Ca - L / ((M : ℝ) * p)) / p -
        (Cb - L / ((M : ℝ) * p)) / p + (C0 - L / M) / (p : ℝ) ^ 2 := by ring
  change |(∑ n ∈ Ioc A B, residueIndicator M r n * centeredResidue p a n * centeredResidue p b n) -
    (L / M) * (delta - 1 / (p : ℝ) ^ 2)| ≤ _
  rw [hsum, he]
  refine (abs_four_terms _ _ _ _).trans ?_
  exact (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans_eq (by ring)

#print axioms same_covariance_residue_slice

end GaloisForLFunctions.BezoutValuationIncidence

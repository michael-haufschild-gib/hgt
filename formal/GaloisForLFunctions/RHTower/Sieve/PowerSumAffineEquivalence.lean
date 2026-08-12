import GaloisForLFunctions.RHTower.Sieve.VinogradovModularMoment

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

theorem sum_affine_pow_eq_of_powerSums_eq
    {b k : ℕ} (p r : ℕ) (u v : Fin b → ℕ)
    (hpower : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i : Fin b, u i ^ j = ∑ i : Fin b, v i ^ j) :
    ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i : Fin b, (p * u i + r) ^ j =
        ∑ i : Fin b, (p * v i + r) ^ j := by
  intro j hjpos hjk
  simp_rw [add_pow]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have hmle : m ≤ j := by simpa using hm
  by_cases hm0 : m = 0
  · subst m
    simp
  · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have h := hpower m hmpos (hmle.trans hjk)
    calc
      (∑ i : Fin b, (p * u i) ^ m * r ^ (j - m) * j.choose m) =
          p ^ m * (r ^ (j - m) * j.choose m) * ∑ i : Fin b, u i ^ m := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_pow]
        ring
      _ = p ^ m * (r ^ (j - m) * j.choose m) * ∑ i : Fin b, v i ^ m := by rw [h]
      _ = ∑ i : Fin b, (p * v i) ^ m * r ^ (j - m) * j.choose m := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_pow]
        ring

theorem powerSums_eq_of_sum_affine_pow_eq
    {b k : ℕ} {p : ℕ} (hp : p ≠ 0) (r : ℕ) (u v : Fin b → ℕ)
    (haffine : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i : Fin b, (p * u i + r) ^ j =
        ∑ i : Fin b, (p * v i + r) ^ j) :
    ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i : Fin b, u i ^ j = ∑ i : Fin b, v i ^ j := by
  intro j hjpos hjk
  induction j using Nat.strong_induction_on with
  | h j ih =>
      have hfull := haffine j hjpos hjk
      simp_rw [add_pow] at hfull
      conv at hfull =>
        lhs
        rw [Finset.sum_comm]
      conv at hfull =>
        rhs
        rw [Finset.sum_comm]
      have hlower :
          (∑ m ∈ Finset.range j,
              ∑ i : Fin b, (p * u i) ^ m * r ^ (j - m) * j.choose m) =
            ∑ m ∈ Finset.range j,
              ∑ i : Fin b, (p * v i) ^ m * r ^ (j - m) * j.choose m := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmj : m < j := Finset.mem_range.mp hm
        by_cases hm0 : m = 0
        · subst m
          simp
        · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
          have hmom := ih m hmj hmpos (hmj.le.trans hjk)
          calc
            (∑ i : Fin b, (p * u i) ^ m * r ^ (j - m) * j.choose m) =
                p ^ m * (r ^ (j - m) * j.choose m) * ∑ i : Fin b, u i ^ m := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [mul_pow]
              ring
            _ = p ^ m * (r ^ (j - m) * j.choose m) * ∑ i : Fin b, v i ^ m := by
              rw [hmom]
            _ = ∑ i : Fin b, (p * v i) ^ m * r ^ (j - m) * j.choose m := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [mul_pow]
              ring
      have hsplitU := Finset.sum_range_succ
        (f := fun m => ∑ i : Fin b,
          (p * u i) ^ m * r ^ (j - m) * j.choose m) j
      have hsplitV := Finset.sum_range_succ
        (f := fun m => ∑ i : Fin b,
          (p * v i) ^ m * r ^ (j - m) * j.choose m) j
      have htop :
          (∑ i : Fin b, (p * u i) ^ j * r ^ (j - j) * j.choose j) =
            ∑ i : Fin b, (p * v i) ^ j * r ^ (j - j) * j.choose j := by
        have hfull' :
            (∑ m ∈ Finset.range (j + 1), ∑ i : Fin b,
              (p * u i) ^ m * r ^ (j - m) * j.choose m) =
            ∑ m ∈ Finset.range (j + 1), ∑ i : Fin b,
              (p * v i) ^ m * r ^ (j - m) * j.choose m := by
          simpa using hfull
        have hsplitU' :
            (∑ m ∈ Finset.range (j + 1), ∑ i : Fin b,
              (p * u i) ^ m * r ^ (j - m) * j.choose m) =
              (∑ m ∈ Finset.range j, ∑ i : Fin b,
                (p * u i) ^ m * r ^ (j - m) * j.choose m) +
                ∑ i : Fin b, (p * u i) ^ j * r ^ (j - j) * j.choose j := by
          simpa using hsplitU
        have hsplitV' :
            (∑ m ∈ Finset.range (j + 1), ∑ i : Fin b,
              (p * v i) ^ m * r ^ (j - m) * j.choose m) =
              (∑ m ∈ Finset.range j, ∑ i : Fin b,
                (p * v i) ^ m * r ^ (j - m) * j.choose m) +
                ∑ i : Fin b, (p * v i) ^ j * r ^ (j - j) * j.choose j := by
          simpa using hsplitV
        rw [hsplitU', hsplitV'] at hfull'
        rw [hlower] at hfull'
        exact Nat.add_left_cancel hfull'
      simp only [Nat.sub_self, pow_zero, Nat.choose_self, mul_one] at htop
      have htop' : p ^ j * (∑ i : Fin b, u i ^ j) =
          p ^ j * ∑ i : Fin b, v i ^ j := by
        calc
          p ^ j * (∑ i : Fin b, u i ^ j) =
              ∑ i : Fin b, (p * u i) ^ j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [mul_pow]
          _ = ∑ i : Fin b, (p * v i) ^ j := htop
          _ = p ^ j * ∑ i : Fin b, v i ^ j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [mul_pow]
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hp) j) htop'

theorem affine_powerSums_eq_iff
    {b k : ℕ} {p : ℕ} (hp : p ≠ 0) (r : ℕ) (u v : Fin b → ℕ) :
    (∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i : Fin b, (p * u i + r) ^ j =
        ∑ i : Fin b, (p * v i + r) ^ j) ↔
    ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i : Fin b, u i ^ j = ∑ i : Fin b, v i ^ j :=
  ⟨powerSums_eq_of_sum_affine_pow_eq hp r u v,
    sum_affine_pow_eq_of_powerSums_eq p r u v⟩

end

end RHTower.Sieve


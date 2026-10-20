import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimePowerIncidenceDominance
import GaloisForLFunctions.ArithmeticIncidencePositivity.LatticeCrossingClassification
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeAtomVersusPoleClassification

/-!
# The total crossing kernel on lattice pairs

The crossing pair `(−log a, log b)` of two integers `a, b ≥ 2` carries two sources of negative
conductance, the archimedean density `ω(log ab)` and, when `ab` is a prime power, the atom
`Λ(ab)/√(ab)`; against them stands the polar weight `2 sinh(log a / 2) sinh(log b / 2)`. The
**total lattice crossing kernel** is `k_arch(−log a, log b) + Λ(ab)/√(ab)`; the pair has negative
conductance in an odd gauge iff this kernel is positive.

**Law.** For `a, b ≥ 2` the total kernel is positive exactly on the four unordered pairs
`{2,2}, {2,3}, {2,4}, {3,3}`. The archimedean kernel alone is positive on `{2,2}` and `{2,3}`; the
prime atom flips the sign of exactly two further pairs, `{2, 4}` (`ab = 8`, atom `log 2 / √8`) and
`{3, 3}` (`ab = 9`, atom `log 3 / 3`). In closed form the condition is
`(a−1)(b−1)(N²−1) < 2N² + 2Λ(N)(N²−1)`, `N = ab`; for `N = p^k` outside these pairs the three
regimes are `p = 2` with `(a−1)(b−1) ≥ 7`, `N ≥ 16`; `p = 3` with `(a−1)(b−1) ≥ 16`, `N ≥ 27`; and
`p ≥ 5` with `(a−1)(b−1) ≥ (p−1)²`, `N ≥ 25`.
-/

open RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- The total crossing kernel of the lattice pair `(−log a, log b)`: archimedean kernel plus the
product atom. -/
def totalLatticeCrossingKernel (a b : ℕ) : ℝ :=
  archPairKernel (-Real.log a) (Real.log b) + productAtom a b

/-! ### Closed form on a tower pair -/

/-- For `a = p^i`, `b = p^j`, `i, j ≥ 1`, `N = ab`:
`k_total = (2N² − (a−1)(b−1)(N²−1) + 2(N²−1) log p) / (2(N²−1)√N)`. -/
theorem totalLatticeCrossingKernel_pow_pow_eq {p i j : ℕ} (hp : p.Prime) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    totalLatticeCrossingKernel (p ^ i) (p ^ j) =
      (2 * (((p ^ i : ℕ) : ℝ) * ((p ^ j : ℕ) : ℝ)) ^ 2
          - (((p ^ i : ℕ) : ℝ) - 1) * (((p ^ j : ℕ) : ℝ) - 1) *
            ((((p ^ i : ℕ) : ℝ) * ((p ^ j : ℕ) : ℝ)) ^ 2 - 1)
          + 2 * ((((p ^ i : ℕ) : ℝ) * ((p ^ j : ℕ) : ℝ)) ^ 2 - 1) * Real.log p) /
        (2 * ((((p ^ i : ℕ) : ℝ) * ((p ^ j : ℕ) : ℝ)) ^ 2 - 1) *
          Real.sqrt (((p ^ i : ℕ) : ℝ) * ((p ^ j : ℕ) : ℝ))) := by
  unfold totalLatticeCrossingKernel
  have hp2 := hp.two_le
  have hA2 : (2 : ℝ) ≤ ((p ^ i : ℕ) : ℝ) := by
    exact_mod_cast le_trans hp2 (Nat.le_self_pow (by omega) p)
  have hB2 : (2 : ℝ) ≤ ((p ^ j : ℕ) : ℝ) := by
    exact_mod_cast le_trans hp2 (Nat.le_self_pow (by omega) p)
  set A : ℝ := ((p ^ i : ℕ) : ℝ) with hA_def
  set B : ℝ := ((p ^ j : ℕ) : ℝ) with hB_def
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hab : 1 < A * B := by nlinarith
  rw [archPairKernel_neg_log_log hA0 hB0 hab, productAtom_pow_pow hp (by omega)]
  have hcast : ((p ^ (i + j) : ℕ) : ℝ) = A * B := by rw [hA_def, hB_def]; push_cast; ring
  rw [hcast]
  have hN2 : 0 < (A * B) ^ 2 - 1 := by nlinarith
  have hne : (2 * ((A * B) ^ 2 - 1)) ≠ 0 := by positivity
  rw [mul_right_comm 2 (Real.sqrt (A * B)) ((A * B) ^ 2 - 1),
    ← mul_div_mul_left (Real.log p) (Real.sqrt (A * B)) hne, ← add_div]

/-- The denominator of the closed form is positive. -/
theorem tower_denominator_pos {A B : ℝ} (hA : 2 ≤ A) (hB : 2 ≤ B) :
    0 < 2 * ((A * B) ^ 2 - 1) * Real.sqrt (A * B) := by
  have hab : 1 < A * B := by nlinarith
  have h1 : 0 < (A * B) ^ 2 - 1 := by nlinarith
  have h2 : 0 < Real.sqrt (A * B) := Real.sqrt_pos.mpr (by linarith)
  positivity

/-! ### The coefficient inequality -/

/-- If `N ≥ m > 1`, `L ≤ c` and `2 + 2/(m² − 1) + 2c ≤ C`, then
`2N² + 2(N² − 1)L ≤ C(N² − 1)`. -/
theorem lattice_atom_inequality_aux {C L N m c : ℝ} (hm : 1 < m) (hN : m ≤ N) (hL : L ≤ c)
    (hC : 2 + 2 / (m ^ 2 - 1) + 2 * c ≤ C) :
    2 * N ^ 2 + 2 * (N ^ 2 - 1) * L ≤ C * (N ^ 2 - 1) := by
  have hm2 : 0 < m ^ 2 - 1 := by nlinarith
  have hN2 : m ^ 2 - 1 ≤ N ^ 2 - 1 := by nlinarith
  have hpos : 0 < N ^ 2 - 1 := lt_of_lt_of_le hm2 hN2
  have h2 : 2 ≤ 2 / (m ^ 2 - 1) * (N ^ 2 - 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm2]; nlinarith
  have hLc : 2 * (N ^ 2 - 1) * L ≤ 2 * (N ^ 2 - 1) * c := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hC hpos.le]

/-- Regime `p = 2`: `(A−1)(B−1) ≥ 7` and `AB ≥ 16`. -/
theorem atom_inequality_two {A B : ℝ} (hC : 7 ≤ (A - 1) * (B - 1)) (hN : 16 ≤ A * B) :
    2 * (A * B) ^ 2 + 2 * ((A * B) ^ 2 - 1) * Real.log 2 ≤
      (A - 1) * (B - 1) * ((A * B) ^ 2 - 1) :=
  lattice_atom_inequality_aux (by norm_num : (1 : ℝ) < 16) hN Real.log_two_lt_d9.le
    (by norm_num; linarith [hC])

/-- Regime `p = 3`: `(A−1)(B−1) ≥ 16` and `AB ≥ 27`. -/
theorem atom_inequality_three {A B : ℝ} (hC : 16 ≤ (A - 1) * (B - 1)) (hN : 27 ≤ A * B) :
    2 * (A * B) ^ 2 + 2 * ((A * B) ^ 2 - 1) * Real.log 3 ≤
      (A - 1) * (B - 1) * ((A * B) ^ 2 - 1) :=
  lattice_atom_inequality_aux (by norm_num : (1 : ℝ) < 27) hN
    (Real.log_le_sub_one_of_pos (by norm_num) : Real.log 3 ≤ 3 - 1) (by norm_num; linarith [hC])

/-- Regime `p ≥ 5`: `(A−1)(B−1) ≥ (p−1)²` and `AB ≥ 25`, with `log p ≤ p − 1`. -/
theorem atom_inequality_ge_five {A B p : ℝ} (hp : 5 ≤ p) (hC : (p - 1) ^ 2 ≤ (A - 1) * (B - 1))
    (hN : 25 ≤ A * B) :
    2 * (A * B) ^ 2 + 2 * ((A * B) ^ 2 - 1) * Real.log p ≤
      (A - 1) * (B - 1) * ((A * B) ^ 2 - 1) := by
  have hL : Real.log p ≤ p - 1 := Real.log_le_sub_one_of_pos (by linarith)
  refine lattice_atom_inequality_aux (by norm_num : (1 : ℝ) < 25) hN hL ?_
  norm_num
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ p - 1) (by linarith : (0 : ℝ) ≤ p - 3)]

/-! ### From the inequality to the kernel -/

/-- On a tower pair `(p^i, p^j)`, `i, j ≥ 1`, the coefficient inequality forces the total kernel
to be nonpositive. -/
theorem totalLatticeCrossingKernel_nonpos_of {p i j : ℕ} (hp : p.Prime) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (h : 2 * (((p ^ i : ℕ) : ℝ) * ((p ^ j : ℕ) : ℝ)) ^ 2
        + 2 * ((((p ^ i : ℕ) : ℝ) * ((p ^ j : ℕ) : ℝ)) ^ 2 - 1) * Real.log p
        ≤ (((p ^ i : ℕ) : ℝ) - 1) * (((p ^ j : ℕ) : ℝ) - 1) *
          ((((p ^ i : ℕ) : ℝ) * ((p ^ j : ℕ) : ℝ)) ^ 2 - 1)) :
    totalLatticeCrossingKernel (p ^ i) (p ^ j) ≤ 0 := by
  rw [totalLatticeCrossingKernel_pow_pow_eq hp hi hj]
  have hp2 := hp.two_le
  have hA2 : (2 : ℝ) ≤ ((p ^ i : ℕ) : ℝ) := by
    exact_mod_cast le_trans hp2 (Nat.le_self_pow (by omega) p)
  have hB2 : (2 : ℝ) ≤ ((p ^ j : ℕ) : ℝ) := by
    exact_mod_cast le_trans hp2 (Nat.le_self_pow (by omega) p)
  apply div_nonpos_of_nonpos_of_nonneg _ (tower_denominator_pos hA2 hB2).le
  linarith

/-! ### The three regimes on towers -/

/-- The coefficient inequality holds on every tower pair outside `{2,2}, {2,4}, {3,3}`. -/
theorem lattice_atom_inequality {p i j : ℕ} (hp : p.Prime) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hex : ¬ ((p ^ i = 2 ∧ p ^ j = 2) ∨ (p ^ i = 2 ∧ p ^ j = 4) ∨ (p ^ i = 4 ∧ p ^ j = 2) ∨
      (p ^ i = 3 ∧ p ^ j = 3))) :
    2 * (((p ^ i : ℕ) : ℝ) * ((p ^ j : ℕ) : ℝ)) ^ 2
        + 2 * ((((p ^ i : ℕ) : ℝ) * ((p ^ j : ℕ) : ℝ)) ^ 2 - 1) * Real.log p
      ≤ (((p ^ i : ℕ) : ℝ) - 1) * (((p ^ j : ℕ) : ℝ) - 1) *
          ((((p ^ i : ℕ) : ℝ) * ((p ^ j : ℕ) : ℝ)) ^ 2 - 1) := by
  have hp2 := hp.two_le
  rcases Nat.lt_or_ge p 5 with hp5 | hp5
  · interval_cases p
    · -- powers of `2`
      simp only [Nat.cast_ofNat]
      apply atom_inequality_two
      all_goals
        have hi' : i = 1 ∨ i = 2 ∨ 3 ≤ i := by omega
        have hj' : j = 1 ∨ j = 2 ∨ 3 ≤ j := by omega
        rcases hi' with rfl | rfl | hi3
        · -- `a = 2`: `b ≥ 8`
          have hj3 : 3 ≤ j := by
            rcases hj' with rfl | rfl | h
            · exact absurd (Or.inl ⟨rfl, rfl⟩) hex
            · exact absurd (Or.inr (Or.inl ⟨rfl, rfl⟩)) hex
            · exact h
          have h8 : (8 : ℕ) ≤ 2 ^ j := by
            calc (8 : ℕ) = 2 ^ 3 := by norm_num
              _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj3
          have h8r : (8 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast h8
          have hA : ((2 ^ 1 : ℕ) : ℝ) = 2 := by norm_num
          rw [hA]
          nlinarith
        · -- `a = 4`: `b ≥ 4`
          have hj2 : 2 ≤ j := by
            rcases hj' with rfl | rfl | h
            · exact absurd (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hex
            · exact le_refl 2
            · omega
          have h4 : (4 : ℕ) ≤ 2 ^ j := by
            calc (4 : ℕ) = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
          have h4r : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast h4
          have hA : ((2 ^ 2 : ℕ) : ℝ) = 4 := by norm_num
          rw [hA]
          nlinarith
        · -- `a ≥ 8`, `b ≥ 2`
          have h8 : (8 : ℕ) ≤ 2 ^ i := by
            calc (8 : ℕ) = 2 ^ 3 := by norm_num
              _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi3
          have h2 : (2 : ℕ) ≤ 2 ^ j := by
            calc (2 : ℕ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
          have h8r : (8 : ℝ) ≤ ((2 ^ i : ℕ) : ℝ) := by exact_mod_cast h8
          have h2r : (2 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast h2
          nlinarith
    · -- powers of `3`
      simp only [Nat.cast_ofNat]
      apply atom_inequality_three
      all_goals
        have hi' : i = 1 ∨ 2 ≤ i := by omega
        rcases hi' with rfl | hi2
        · -- `a = 3`: `b ≥ 9`
          have hj2 : 2 ≤ j := by
            rcases Nat.lt_or_ge j 2 with h | h
            · obtain rfl : j = 1 := by omega
              exact absurd (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) hex
            · exact h
          have h9 : (9 : ℕ) ≤ 3 ^ j := by
            calc (9 : ℕ) = 3 ^ 2 := by norm_num
              _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
          have h9r : (9 : ℝ) ≤ ((3 ^ j : ℕ) : ℝ) := by exact_mod_cast h9
          have hA : ((3 ^ 1 : ℕ) : ℝ) = 3 := by norm_num
          rw [hA]
          nlinarith
        · -- `a ≥ 9`, `b ≥ 3`
          have h9 : (9 : ℕ) ≤ 3 ^ i := by
            calc (9 : ℕ) = 3 ^ 2 := by norm_num
              _ ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hi2
          have h3 : (3 : ℕ) ≤ 3 ^ j := by
            calc (3 : ℕ) = 3 ^ 1 := by norm_num
              _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
          have h9r : (9 : ℝ) ≤ ((3 ^ i : ℕ) : ℝ) := by exact_mod_cast h9
          have h3r : (3 : ℝ) ≤ ((3 ^ j : ℕ) : ℝ) := by exact_mod_cast h3
          nlinarith
    · -- `4` is not prime
      norm_num at hp
  · -- `p ≥ 5`
    have hpA : ((p : ℕ) : ℝ) ≤ ((p ^ i : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_self_pow (by omega) p
    have hpB : ((p : ℕ) : ℝ) ≤ ((p ^ j : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_self_pow (by omega) p
    have hp5' : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    apply atom_inequality_ge_five hp5'
    · nlinarith
    · nlinarith

/-! ### The two pairs the atom flips -/

/-- `{2, 4}`: `k_arch < 0` but the atom `log 2 / √8` wins, `126 log 2 > 61`. -/
theorem totalLatticeCrossingKernel_two_four_pos : 0 < totalLatticeCrossingKernel 2 4 := by
  have h := totalLatticeCrossingKernel_pow_pow_eq (p := 2) (i := 1) (j := 2) Nat.prime_two
    (le_refl 1) (by norm_num)
  norm_num at h
  rw [h]
  have hl2 := Real.log_two_gt_d9
  have h8 : 0 < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  apply div_pos _ (by positivity)
  linarith

/-- `{3, 3}`: `k_arch < 0` but the atom `log 3 / 3` wins, `160 log 3 > 158`. -/
theorem totalLatticeCrossingKernel_three_three_pos : 0 < totalLatticeCrossingKernel 3 3 := by
  have h := totalLatticeCrossingKernel_pow_pow_eq (p := 3) (i := 1) (j := 1) Nat.prime_three
    (le_refl 1) (le_refl 1)
  norm_num at h
  rw [h]
  have hl3 := log_add_one_sub_div_le_log (m := 2) (p := 3) (by norm_num) (by norm_num)
  have hl2 := Real.log_two_gt_d9
  have h9 : 0 < Real.sqrt 9 := Real.sqrt_pos.mpr (by norm_num)
  apply div_pos _ (by positivity)
  linarith

/-! ### The law -/

/-- **Total lattice crossing law.** For `a, b ≥ 2` the total crossing kernel of `(−log a, log b)`
is positive exactly on the four unordered pairs `{2,2}, {2,3}, {2,4}, {3,3}`. -/
theorem totalLatticeCrossingKernel_pos_iff {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    0 < totalLatticeCrossingKernel a b ↔
      (a = 2 ∧ b = 2) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨ (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) ∨
        (a = 3 ∧ b = 3) := by
  constructor
  · intro h
    by_contra hnot
    have hk : archPairKernel (-Real.log a) (Real.log b) ≤ 0 := by
      rw [← not_lt, archPairKernel_neg_log_log_pos_iff_of_two_le ha hb]
      rintro (h' | h' | h') <;> exact hnot (by tauto)
    by_cases hpp : IsPrimePow (a * b)
    · obtain ⟨p, i, j, hp, rfl, rfl, -⟩ := exists_prime_pow_of_isPrimePow_mul hpp
      have hi : 1 ≤ i := by
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · subst h0; simp at ha
        · exact h0
      have hj : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0; simp at hb
        · exact h0
      have hex : ¬ ((p ^ i = 2 ∧ p ^ j = 2) ∨ (p ^ i = 2 ∧ p ^ j = 4) ∨ (p ^ i = 4 ∧ p ^ j = 2) ∨
          (p ^ i = 3 ∧ p ^ j = 3)) := by
        rintro (h' | h' | h' | h') <;> exact hnot (by tauto)
      have hle := totalLatticeCrossingKernel_nonpos_of hp hi hj (lattice_atom_inequality hp hi hj hex)
      linarith
    · unfold totalLatticeCrossingKernel at h
      rw [productAtom_eq_zero_of_not_isPrimePow hpp] at h
      linarith
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have := (archPairKernel_neg_log_log_pos_iff_of_two_le (a := 2) (b := 2) (by norm_num)
        (by norm_num)).mpr (by norm_num)
      unfold totalLatticeCrossingKernel
      linarith [productAtom_nonneg 2 2]
    · have := (archPairKernel_neg_log_log_pos_iff_of_two_le (a := 2) (b := 3) (by norm_num)
        (by norm_num)).mpr (by norm_num)
      unfold totalLatticeCrossingKernel
      linarith [productAtom_nonneg 2 3]
    · have := (archPairKernel_neg_log_log_pos_iff_of_two_le (a := 3) (b := 2) (by norm_num)
        (by norm_num)).mpr (by norm_num)
      unfold totalLatticeCrossingKernel
      linarith [productAtom_nonneg 3 2]
    · exact totalLatticeCrossingKernel_two_four_pos
    · have h := totalLatticeCrossingKernel_two_four_pos
      unfold totalLatticeCrossingKernel at h ⊢
      rw [← archPairKernel_neg_neg, neg_neg] at h
      rw [show productAtom 4 2 = productAtom 2 4 by unfold productAtom; rw [mul_comm]]
      push_cast at h ⊢
      linarith
    · exact totalLatticeCrossingKernel_three_three_pos

/-- The atom flips exactly the two lattice signs `{2,4}` and `{3,3}`: the total kernel is positive
iff the archimedean kernel is positive or the pair is one of these two. -/
theorem totalLatticeCrossingKernel_pos_iff_archPairKernel_pos_or {a b : ℕ} (ha : 2 ≤ a)
    (hb : 2 ≤ b) :
    0 < totalLatticeCrossingKernel a b ↔
      0 < archPairKernel (-Real.log a) (Real.log b) ∨
        (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) ∨ (a = 3 ∧ b = 3) := by
  rw [totalLatticeCrossingKernel_pos_iff ha hb, archPairKernel_neg_log_log_pos_iff_of_two_le ha hb]
  tauto

end GaloisForLFunctions.ArithmeticIncidencePositivity

import Mathlib

/-!
# The Euclidean cone signatures

A parabolic (zero-curvature) orbifold structure on the sphere is a finite list of cone orders
`ν ≥ 2` together with a number `c` of cusps satisfying

`c + ∑ (1 - 1/ν) = 2`.

There are exactly six solutions: `(∞, ∞)`, `(2, 2, ∞)`, `(2, 2, 2, 2)`, `(2, 3, 6)`, `(2, 4, 4)`
and `(3, 3, 3)`.

The proof is elementary: each cone contributes at least `1/2` and less than `1`, which bounds the
number of cones by `4 - 2c`, and the remaining short cases are finite arithmetic.  The only
substantive step is the classification of the triples with `1/a + 1/b + 1/c = 1`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The Euclidean cone triples.**  The only weakly increasing triples of integers at least `2`
with reciprocal sum `1` are `(2,3,6)`, `(2,4,4)` and `(3,3,3)`. -/
theorem euclidean_cone_triple {a b c : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (heq : (1 : ℚ) / a + 1 / b + 1 / c = 1) :
    (a = 2 ∧ b = 3 ∧ c = 6) ∨ (a = 2 ∧ b = 4 ∧ c = 4) ∨ (a = 3 ∧ b = 3 ∧ c = 3) := by
  have hb : 2 ≤ b := le_trans ha hab
  have hc : 2 ≤ c := le_trans hb hbc
  have ha0 : (0 : ℚ) < (a : ℚ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) ha
  have hb0 : (0 : ℚ) < (b : ℚ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hb
  have hc0 : (0 : ℚ) < (c : ℚ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hc
  have hab' : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast hab
  have hbc' : (b : ℚ) ≤ (c : ℚ) := by exact_mod_cast hbc
  have h1 : (1 : ℚ) / (b : ℚ) ≤ 1 / (a : ℚ) := one_div_le_one_div_of_le ha0 hab'
  have h2 : (1 : ℚ) / (c : ℚ) ≤ 1 / (b : ℚ) := one_div_le_one_div_of_le hb0 hbc'
  have hpc : (0 : ℚ) < 1 / (c : ℚ) := by positivity
  have hpb : (0 : ℚ) < 1 / (b : ℚ) := by positivity
  have hale : a ≤ 3 := by
    by_contra hcon
    push_neg at hcon
    have h4 : (4 : ℚ) ≤ (a : ℚ) := by exact_mod_cast hcon
    have hle : (1 : ℚ) / (a : ℚ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) h4
    linarith
  interval_cases a
  · -- `a = 2`
    have hble : b ≤ 4 := by
      by_contra hcon
      push_neg at hcon
      have h5 : (5 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hcon
      have hle : (1 : ℚ) / (b : ℚ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) h5
      have hlec : (1 : ℚ) / (c : ℚ) ≤ 1 / 5 := le_trans h2 hle
      rw [show ((2 : ℕ) : ℚ) = 2 from by norm_num] at heq
      linarith
    have hbge : 3 ≤ b := by
      by_contra hcon
      push_neg at hcon
      have hb2 : b = 2 := by omega
      subst hb2
      rw [show ((2 : ℕ) : ℚ) = 2 from by norm_num] at heq
      have : (1 : ℚ) / (c : ℚ) = 0 := by linarith
      simp only [div_eq_zero_iff, one_ne_zero, false_or] at this
      exact absurd this (ne_of_gt hc0)
    interval_cases b
    · -- `b = 3`
      left
      refine ⟨rfl, rfl, ?_⟩
      have hcq : (c : ℚ) = 6 := by
        rw [show ((2 : ℕ) : ℚ) = 2 from by norm_num,
          show ((3 : ℕ) : ℚ) = 3 from by norm_num] at heq
        have h : (1 : ℚ) / (c : ℚ) = 1 / 6 := by linarith
        field_simp at h
        linarith
      exact_mod_cast hcq
    · -- `b = 4`
      right; left
      refine ⟨rfl, rfl, ?_⟩
      have hcq : (c : ℚ) = 4 := by
        rw [show ((2 : ℕ) : ℚ) = 2 from by norm_num,
          show ((4 : ℕ) : ℚ) = 4 from by norm_num] at heq
        have h : (1 : ℚ) / (c : ℚ) = 1 / 4 := by linarith
        field_simp at h
        linarith
      exact_mod_cast hcq
  · -- `a = 3`
    have hble : b ≤ 3 := by
      by_contra hcon
      push_neg at hcon
      have h4 : (4 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hcon
      have hle : (1 : ℚ) / (b : ℚ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) h4
      have hlec : (1 : ℚ) / (c : ℚ) ≤ 1 / 4 := le_trans h2 hle
      rw [show ((3 : ℕ) : ℚ) = 3 from by norm_num] at heq
      linarith
    have hb3 : b = 3 := le_antisymm hble hab
    subst hb3
    right; right
    refine ⟨rfl, rfl, ?_⟩
    have hcq : (c : ℚ) = 3 := by
      rw [show ((3 : ℕ) : ℚ) = 3 from by norm_num] at heq
      have h : (1 : ℚ) / (c : ℚ) = 1 / 3 := by linarith
      field_simp at h
      linarith
    exact_mod_cast hcq


/-- The cone-defect sum in terms of the reciprocal sum. -/
theorem sum_one_sub_inv (l : List ℕ) :
    (l.map (fun ν : ℕ => 1 - 1 / (ν : ℚ))).sum
      = (l.length : ℚ) - (l.map (fun ν : ℕ => 1 / (ν : ℚ))).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      push_cast
      ring

/-- Each cone contributes a reciprocal at most one half. -/
theorem inv_le_half_of_two_le {ν : ℕ} (h : 2 ≤ ν) : (1 : ℚ) / (ν : ℚ) ≤ 1 / 2 := by
  have h2 : (2 : ℚ) ≤ (ν : ℚ) := by exact_mod_cast h
  exact one_div_le_one_div_of_le (by norm_num) h2

theorem inv_pos_of_two_le {ν : ℕ} (h : 2 ≤ ν) : (0 : ℚ) < 1 / (ν : ℚ) := by
  have h2 : (0 : ℚ) < (ν : ℚ) := by
    have : (2 : ℚ) ≤ (ν : ℚ) := by exact_mod_cast h
    linarith
  positivity

theorem sum_inv_le_half_length {l : List ℕ} (h2 : ∀ ν ∈ l, 2 ≤ ν) :
    (l.map (fun ν : ℕ => 1 / (ν : ℚ))).sum ≤ (l.length : ℚ) / 2 := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha := inv_le_half_of_two_le (h2 a (List.mem_cons_self ..))
      have ht := ih (fun ν hν => h2 ν (List.mem_cons_of_mem a hν))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      linarith

theorem sum_inv_pos {l : List ℕ} (h2 : ∀ ν ∈ l, 2 ≤ ν) (hne : l ≠ []) :
    (0 : ℚ) < (l.map (fun ν : ℕ => 1 / (ν : ℚ))).sum := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a t ih =>
      have ha := inv_pos_of_two_le (h2 a (List.mem_cons_self ..))
      rcases eq_or_ne t [] with rfl | hte
      · simpa using ha
      · have ht := ih (fun ν hν => h2 ν (List.mem_cons_of_mem a hν)) hte
        simp only [List.map_cons, List.sum_cons]
        linarith

/-- Two cones with reciprocal sum one are both of order two. -/
theorem cone_pair_eq_two {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (heq : (1 : ℚ) / a + 1 / b = 1) : a = 2 ∧ b = 2 := by
  have ha' := inv_le_half_of_two_le ha
  have hb' := inv_le_half_of_two_le hb
  have haq : (1 : ℚ) / a = 1 / 2 := by linarith
  have hbq : (1 : ℚ) / b = 1 / 2 := by linarith
  have ha0 : (0 : ℚ) < (a : ℚ) := by
    have : (2 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
    linarith
  have hb0 : (0 : ℚ) < (b : ℚ) := by
    have : (2 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
    linarith
  field_simp at haq hbq
  constructor
  · exact_mod_cast haq.symm
  · exact_mod_cast hbq.symm

/-- Four cones with reciprocal sum two are all of order two. -/
theorem cone_quad_eq_two {a b c d : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (heq : (1 : ℚ) / a + 1 / b + 1 / c + 1 / d = 2) :
    a = 2 ∧ b = 2 ∧ c = 2 ∧ d = 2 := by
  have ha' := inv_le_half_of_two_le ha
  have hb' := inv_le_half_of_two_le hb
  have hc' := inv_le_half_of_two_le hc
  have hd' := inv_le_half_of_two_le hd
  have haq : (1 : ℚ) / a = 1 / 2 := by linarith
  have hbq : (1 : ℚ) / b = 1 / 2 := by linarith
  have hcq : (1 : ℚ) / c = 1 / 2 := by linarith
  have hdq : (1 : ℚ) / d = 1 / 2 := by linarith
  have ha0 : (0 : ℚ) < (a : ℚ) := by
    have : (2 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
    linarith
  have hb0 : (0 : ℚ) < (b : ℚ) := by
    have : (2 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
    linarith
  have hc0 : (0 : ℚ) < (c : ℚ) := by
    have : (2 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc
    linarith
  have hd0 : (0 : ℚ) < (d : ℚ) := by
    have : (2 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
    linarith
  field_simp at haq hbq hcq hdq
  exact ⟨by exact_mod_cast haq.symm, by exact_mod_cast hbq.symm,
    by exact_mod_cast hcq.symm, by exact_mod_cast hdq.symm⟩

/-- **The Euclidean signature classification.**  A parabolic orbifold structure on the sphere,
recorded by its number `c` of cusps and its weakly increasing list of cone orders, is one of the
six Euclidean signatures. -/
theorem parabolic_signature_classification (c : ℕ) (l : List ℕ)
    (hsorted : l.Pairwise (· ≤ ·)) (h2 : ∀ ν ∈ l, 2 ≤ ν)
    (heq : (c : ℚ) + (l.map (fun ν : ℕ => 1 - 1 / (ν : ℚ))).sum = 2) :
    (c = 2 ∧ l = []) ∨ (c = 1 ∧ l = [2, 2]) ∨ (c = 0 ∧ l = [2, 2, 2, 2]) ∨
      (c = 0 ∧ l = [2, 3, 6]) ∨ (c = 0 ∧ l = [2, 4, 4]) ∨ (c = 0 ∧ l = [3, 3, 3]) := by
  classical
  have hSval : (l.map (fun ν : ℕ => 1 / (ν : ℚ))).sum = (c : ℚ) + (l.length : ℚ) - 2 := by
    rw [sum_one_sub_inv l] at heq
    linarith
  have hSle : (l.map (fun ν : ℕ => 1 / (ν : ℚ))).sum ≤ (l.length : ℚ) / 2 :=
    sum_inv_le_half_length h2
  have hnle : (l.length : ℚ) ≤ 4 - 2 * (c : ℚ) := by rw [hSval] at hSle; linarith
  rcases eq_or_ne l [] with hnil | hne
  · subst hnil
    left
    refine ⟨?_, rfl⟩
    simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero] at hSval
    have hc2 : (c : ℚ) = 2 := by linarith
    exact_mod_cast hc2
  have hSpos : 0 < (l.map (fun ν : ℕ => 1 / (ν : ℚ))).sum := sum_inv_pos h2 hne
  have hcle : c ≤ 2 := by
    by_contra hcon
    have h3 : (3 : ℚ) ≤ (c : ℚ) := by exact_mod_cast (by omega : 3 ≤ c)
    have hn0 : (0 : ℚ) ≤ (l.length : ℚ) := by positivity
    linarith
  interval_cases c
  · -- no cusps: the length is three or four
    have hnb : l.length ≤ 4 := by
      have : (l.length : ℚ) ≤ 4 := by simpa using hnle
      exact_mod_cast this
    have hn3 : 3 ≤ l.length := by
      by_contra hcon
      have hlt : (l.length : ℚ) ≤ 2 := by exact_mod_cast (by omega : l.length ≤ 2)
      simp only [Nat.cast_zero, zero_add] at hSval
      linarith
    interval_cases hlen : l.length
    · -- three cones
      obtain ⟨a, b, d, rfl⟩ := List.length_eq_three.mp hlen
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, true_and] at hsorted
      have hab : a ≤ b := hsorted.1.1
      have hbd : b ≤ d := hsorted.2.1
      have ha : 2 ≤ a := h2 a (by simp)
      have hsum : (1 : ℚ) / a + 1 / b + 1 / d = 1 := by
        simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero,
          List.length_cons, List.length_nil, Nat.cast_zero, Nat.cast_ofNat] at hSval
        push_cast at hSval
        linarith
      rcases euclidean_cone_triple ha hab hbd hsum with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by rw [h.1, h.2.1, h.2.2]⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by rw [h.1, h.2.1, h.2.2]⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by rw [h.1, h.2.1, h.2.2]⟩))))
    · -- four cones
      obtain ⟨a, b, d, e, rfl⟩ : ∃ a b d e, l = [a, b, d, e] := by
        match l, hlen with
        | [a, b, d, e], _ => exact ⟨a, b, d, e, rfl⟩
      have ha : 2 ≤ a := h2 a (by simp)
      have hb : 2 ≤ b := h2 b (by simp)
      have hd : 2 ≤ d := h2 d (by simp)
      have he : 2 ≤ e := h2 e (by simp)
      have hsum : (1 : ℚ) / a + 1 / b + 1 / d + 1 / e = 2 := by
        simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero,
          List.length_cons, List.length_nil, Nat.cast_zero, Nat.cast_ofNat] at hSval
        push_cast at hSval
        linarith
      obtain ⟨h1, h2', h3, h4⟩ := cone_quad_eq_two ha hb hd he hsum
      exact Or.inr (Or.inr (Or.inl ⟨rfl, by rw [h1, h2', h3, h4]⟩))
  · -- one cusp: the length is two
    have hnb : l.length ≤ 2 := by
      have : (l.length : ℚ) ≤ 2 := by push_cast at hnle; linarith
      exact_mod_cast this
    have hn2 : 2 ≤ l.length := by
      by_contra hcon
      have hlt : (l.length : ℚ) ≤ 1 := by exact_mod_cast (by omega : l.length ≤ 1)
      push_cast at hSval
      linarith
    have hlen : l.length = 2 := le_antisymm hnb hn2
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
    have ha : 2 ≤ a := h2 a (by simp)
    have hb : 2 ≤ b := h2 b (by simp)
    have hsum : (1 : ℚ) / a + 1 / b = 1 := by
      simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero,
        List.length_cons, List.length_nil] at hSval
      push_cast at hSval
      linarith
    obtain ⟨h1, h3⟩ := cone_pair_eq_two ha hb hsum
    exact Or.inr (Or.inl ⟨rfl, by rw [h1, h3]⟩)
  · -- two cusps: no cones, contradicting nonemptiness
    exfalso
    have hnb : l.length ≤ 0 := by
      have : (l.length : ℚ) ≤ 0 := by push_cast at hnle; linarith
      exact_mod_cast this
    exact hne (List.length_eq_zero_iff.mp (by omega))

end GaloisForLFunctions.HTGeometry

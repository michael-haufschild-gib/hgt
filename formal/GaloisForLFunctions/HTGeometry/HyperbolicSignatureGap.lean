import GaloisForLFunctions.HTGeometry.EuclideanConeSignature
import GaloisForLFunctions.HTGeometry.HurwitzTriangleSumBound

/-!
# The Hurwitz gap for sphere signatures

A hyperbolic orbifold structure on the sphere — `c` cusps and cone orders `ν ≥ 2` with

`A = c + ∑ (1 - 1/ν) > 2`

— satisfies `A - 2 ≥ 1/42`, with the extremal signature `(2,3,7)`.

Only the three-cone case is delicate, and the corpus already owns it
(`hurwitz_triple_sum_le`).  Every other case is a counting bound: each cone contributes at least
`1/2` and each cusp exactly `1`, so five cones, or four cones one of which has order at least
three, already overshoot `2` by more than `1/42`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Each cone contributes at least one half to the orbifold defect. -/
theorem half_le_cone_defect {ν : ℕ} (h : 2 ≤ ν) : (1 : ℚ) / 2 ≤ 1 - 1 / (ν : ℚ) := by
  have h2 : (2 : ℚ) ≤ (ν : ℚ) := by exact_mod_cast h
  have h0 : (0 : ℚ) < (ν : ℚ) := by linarith
  have : (1 : ℚ) / (ν : ℚ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
  linarith

/-- A cone of order at least three contributes at least two thirds. -/
theorem two_thirds_le_cone_defect {ν : ℕ} (h : 3 ≤ ν) : (2 : ℚ) / 3 ≤ 1 - 1 / (ν : ℚ) := by
  have h3 : (3 : ℚ) ≤ (ν : ℚ) := by exact_mod_cast h
  have h0 : (0 : ℚ) < (ν : ℚ) := by linarith
  have : (1 : ℚ) / (ν : ℚ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3
  linarith

/-- Each cone contributes less than one. -/
theorem cone_defect_lt_one {ν : ℕ} (h : 2 ≤ ν) : 1 - 1 / (ν : ℚ) < 1 := by
  have h2 : (2 : ℚ) ≤ (ν : ℚ) := by exact_mod_cast h
  have h0 : (0 : ℚ) < (ν : ℚ) := by linarith
  have : (0 : ℚ) < 1 / (ν : ℚ) := by positivity
  linarith

/-- The total cone defect is at least half the number of cones. -/
theorem half_length_le_sum_defect {l : List ℕ} (h2 : ∀ ν ∈ l, 2 ≤ ν) :
    (l.length : ℚ) / 2 ≤ (l.map (fun ν : ℕ => 1 - 1 / (ν : ℚ))).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha := half_le_cone_defect (h2 a (List.mem_cons_self ..))
      have ht := ih (fun ν hν => h2 ν (List.mem_cons_of_mem a hν))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      linarith

/-- The total cone defect is less than the number of cones. -/
theorem sum_defect_lt_length {l : List ℕ} (h2 : ∀ ν ∈ l, 2 ≤ ν) :
    (l.map (fun ν : ℕ => 1 - 1 / (ν : ℚ))).sum ≤ (l.length : ℚ) := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha := (cone_defect_lt_one (h2 a (List.mem_cons_self ..))).le
      have ht := ih (fun ν hν => h2 ν (List.mem_cons_of_mem a hν))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      linarith

/-- **The Hurwitz gap.**  A hyperbolic sphere signature overshoots the parabolic value by at least
`1/42`. -/
theorem hyperbolic_signature_gap (c : ℕ) (l : List ℕ)
    (hsorted : l.Pairwise (· ≤ ·)) (h2 : ∀ ν ∈ l, 2 ≤ ν)
    (hhyp : 2 < (c : ℚ) + (l.map (fun ν : ℕ => 1 - 1 / (ν : ℚ))).sum) :
    2 + 1 / 42 ≤ (c : ℚ) + (l.map (fun ν : ℕ => 1 - 1 / (ν : ℚ))).sum := by
  classical
  set S : ℚ := (l.map (fun ν : ℕ => 1 - 1 / (ν : ℚ))).sum with hS
  have hSlow : (l.length : ℚ) / 2 ≤ S := half_length_le_sum_defect h2
  have hShigh : S ≤ (l.length : ℚ) := sum_defect_lt_length h2
  have hS0 : 0 ≤ S := le_trans (by positivity) hSlow
  -- many cusps or many cones overshoot immediately
  rcases le_or_gt 3 c with hc3 | hc3
  · have : (3 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc3
    linarith
  interval_cases c
  · -- no cusps
    rcases le_or_gt 5 l.length with hl5 | hl5
    · have : (5 : ℚ) ≤ (l.length : ℚ) := by exact_mod_cast hl5
      push_cast
      linarith
    · interval_cases hlen : l.length
      · simp only [List.length_eq_zero_iff] at hlen
        subst hlen
        simp only [hS, List.map_nil, List.sum_nil] at hhyp
        norm_num at hhyp
      · have : S ≤ 1 := by
          simpa using hShigh
        push_cast at hhyp
        linarith
      · have : S ≤ 2 := by
          simpa using hShigh
        push_cast at hhyp
        linarith
      · -- three cones: the corpus's Hurwitz bound
        obtain ⟨a, b, d, rfl⟩ := List.length_eq_three.mp hlen
        have ha : 2 ≤ a := h2 a (by simp)
        have hb : 2 ≤ b := h2 b (by simp)
        have hd : 2 ≤ d := h2 d (by simp)
        have hrecip : (1 : ℚ) / a + 1 / b + 1 / d < 1 := by
          simp only [hS, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
            add_zero] at hhyp
          push_cast at hhyp
          linarith
        have hbound := hurwitz_triple_sum_le_symm (by omega : 1 ≤ a) (by omega : 1 ≤ b)
          (by omega : 1 ≤ d) hrecip
        simp only [hS, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero]
        push_cast
        linarith
      · -- four cones: one of them has order at least three
        obtain ⟨a, b, d, e, rfl⟩ : ∃ a b d e, l = [a, b, d, e] := by
          match l, hlen with
          | [a, b, d, e], _ => exact ⟨a, b, d, e, rfl⟩
        have ha := h2 a (by simp)
        have hb := h2 b (by simp)
        have hd := h2 d (by simp)
        have he := h2 e (by simp)
        by_cases hall : a = 2 ∧ b = 2 ∧ d = 2 ∧ e = 2
        · exfalso
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hall
          simp only [hS, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
            add_zero] at hhyp
          norm_num at hhyp
        · have hone : 3 ≤ a ∨ 3 ≤ b ∨ 3 ≤ d ∨ 3 ≤ e := by
            by_contra hcon
            exact hall ⟨by omega, by omega, by omega, by omega⟩
          have hda := half_le_cone_defect ha
          have hdb := half_le_cone_defect hb
          have hdd := half_le_cone_defect hd
          have hde := half_le_cone_defect he
          simp only [hS, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero]
          push_cast
          rcases hone with h | h | h | h
          · have := two_thirds_le_cone_defect h; linarith
          · have := two_thirds_le_cone_defect h; linarith
          · have := two_thirds_le_cone_defect h; linarith
          · have := two_thirds_le_cone_defect h; linarith
  · -- one cusp
    rcases le_or_gt 3 l.length with hl3 | hl3
    · have : (3 : ℚ) ≤ (l.length : ℚ) := by exact_mod_cast hl3
      push_cast
      linarith
    · interval_cases hlen : l.length
      · simp only [List.length_eq_zero_iff] at hlen
        subst hlen
        simp only [hS, List.map_nil, List.sum_nil] at hhyp
        norm_num at hhyp
      · have : S ≤ 1 := by
          simpa using hShigh
        push_cast at hhyp
        linarith
      · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
        have ha := h2 a (by simp)
        have hb := h2 b (by simp)
        by_cases hall : a = 2 ∧ b = 2
        · exfalso
          obtain ⟨rfl, rfl⟩ := hall
          simp only [hS, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
            add_zero] at hhyp
          norm_num at hhyp
        · have hone : 3 ≤ a ∨ 3 ≤ b := by
            by_contra hcon
            exact hall ⟨by omega, by omega⟩
          have hda := half_le_cone_defect ha
          have hdb := half_le_cone_defect hb
          simp only [hS, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero]
          push_cast
          rcases hone with h | h
          · have := two_thirds_le_cone_defect h; linarith
          · have := two_thirds_le_cone_defect h; linarith
  · -- two cusps
    rcases Nat.eq_zero_or_pos l.length with hlen | hlen
    · exfalso
      simp only [List.length_eq_zero_iff] at hlen
      subst hlen
      simp only [hS, List.map_nil, List.sum_nil] at hhyp
      norm_num at hhyp
    · have h1 : (1 : ℚ) ≤ (l.length : ℚ) := by exact_mod_cast hlen
      push_cast
      linarith


/-- **The degree bound from the Hurwitz gap.**  A hyperbolic late signature with a fixed earlier
singularity budget `s` bounds the prefix degree by `42 (s - 2)`. -/
theorem degree_le_of_hyperbolic_defect {D : ℕ} {A B : ℚ}
    (hA : 2 + 1 / 42 ≤ A) (hbound : (D : ℚ) * (A - 2) + 2 ≤ B) :
    (D : ℚ) ≤ 42 * (B - 2) := by
  have hD : (0 : ℚ) ≤ (D : ℚ) := by positivity
  have h1 : (D : ℚ) * (1 / 42) ≤ (D : ℚ) * (A - 2) := by
    have : (1 : ℚ) / 42 ≤ A - 2 := by linarith
    exact mul_le_mul_of_nonneg_left this hD
  linarith

end GaloisForLFunctions.HTGeometry

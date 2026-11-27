import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-! Multiplicativity under invertible squares and two-sided polynomial growth
determine the dimensions of the powers of a principal polarization. -/

namespace GlobalTheory.FinrankGrowthBounds

open Filter Topology

private theorem le_of_pow_le_mul_pow {a b C : ℕ} (hb : 1 ≤ b) (h : ∀ k : ℕ, a ^ k ≤ C * b ^ k) : a ≤ b := by
  by_contra hab
  push Not at hab
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 : (1 : ℝ) < a / b := by rw [one_lt_div hb']; exact_mod_cast hab
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop (C : ℝ)).exists
  rw [div_pow, lt_div_iff₀ (pow_pos hb' k)] at hk
  have := h k
  have h2 : ((a : ℝ)) ^ k ≤ C * b ^ k := by exact_mod_cast this
  linarith

private theorem le_of_frequently {a b g : ℕ} (h : ∀ M : ℕ, ∃ n, M ≤ n ∧ a * n ^ g ≤ b * (n + 8) ^ g) :
    a ≤ b := by
  by_contra hab
  push Not at hab
  have ht : Tendsto (fun n : ℕ => (b : ℝ) * (1 + 8 / (n : ℝ)) ^ g) atTop (𝓝 ((b : ℝ) * (1 + 0) ^ g)) :=
    ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat 8)).pow g).const_mul _
  have hlt : (b : ℝ) * (1 + 0) ^ g < a := by simpa using hab
  obtain ⟨M, hM⟩ := eventually_atTop.1 (ht.eventually_lt_const hlt)
  obtain ⟨n, hn, hle⟩ := h (M + 1)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h1 := hM n (by omega)
  have h2 : (1 + 8 / (n : ℝ)) = (n + 8) / n := by field_simp
  rw [h2, div_pow, ← mul_div_assoc, div_lt_iff₀ (pow_pos hn0 g)] at h1
  have h3 : (a : ℝ) * n ^ g ≤ b * (n + 8) ^ g := by exact_mod_cast hle
  linarith

private theorem eq_pow_of_growth_every_index (h : ℕ → ℕ) (g : ℕ) (G : ℕ → Prop) (hG : ∀ m, G m ∨ G (m + 1))
    (hG0 : ¬ G 0) (h1 : h 1 = 1)
    (hmono : Monotone h) (hrel : ∀ n j, G n → 1 ≤ j → h (n ^ 2 * j) = h (n ^ 2) * h j)
    (N c C : ℕ) (hN : 1 ≤ N)
    (hgr : ∀ t, 1 ≤ t → t ^ g ≤ c * h (N * t) ∧ h (N * t) ≤ C * t ^ g) (j : ℕ) (hj : 1 ≤ j) :
    h j = j ^ g := by
  have hpos : ∀ n, G n → 1 ≤ n := fun n hn => Nat.pos_of_ne_zero fun e => hG0 (e ▸ hn)
  have hit : ∀ n, G n → ∀ i, 1 ≤ i → ∀ k, h ((n ^ 2) ^ k * i) = h (n ^ 2) ^ k * h i := by
    intro n hn i hi k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hpos n hn
      rw [pow_succ' (n ^ 2), Nat.mul_assoc, hrel n _ hn (Nat.mul_pos (by positivity) hi), ih]
      ring
  have hsq : ∀ n, G n → h (n ^ 2) = (n ^ 2) ^ g := by
    intro n hn
    have hn1 := hpos n hn
    apply le_antisymm
    · refine le_of_pow_le_mul_pow (C := C) (Nat.pos_of_ne_zero (by positivity)) fun k => ?_
      have e := hit n hn 1 le_rfl k
      rw [h1, Nat.mul_one, Nat.mul_one] at e
      rw [← e, ← pow_mul (n ^ 2) g k, mul_comm g k, pow_mul]
      refine le_trans (hmono (Nat.le_mul_of_pos_left _ hN)) (hgr _ (Nat.pos_of_ne_zero (by positivity))).2
    · have hd : 1 ≤ h (n ^ 2) := h1 ▸ hmono (Nat.pos_of_ne_zero (by positivity))
      refine le_of_pow_le_mul_pow (C := c * h N) hd fun k => ?_
      have e := hit n hn N hN k
      have := (hgr ((n ^ 2) ^ k) (Nat.pos_of_ne_zero (by positivity))).1
      rw [mul_comm N, e] at this
      rw [← pow_mul (n ^ 2) g k, mul_comm g k, pow_mul]
      calc _ ≤ _ := this
        _ = _ := by ring
  have hbig : ∀ M, ∃ n, M ≤ n ∧ G n := fun M => (hG M).elim (fun x => ⟨M, le_rfl, x⟩)
    fun x => ⟨M + 1, by omega, x⟩
  apply le_antisymm
  · refine le_of_frequently (g := g) fun M => ?_
    obtain ⟨n, hMn, hn⟩ := hbig M
    have hn1 := hpos n hn
    refine ⟨n, hMn, ?_⟩
    set m := Nat.sqrt (n ^ 2 * j) with hm
    have l1 : m * m ≤ n ^ 2 * j := Nat.sqrt_le _
    have l2 : n ^ 2 * j < (m + 1) * (m + 1) := Nat.lt_succ_sqrt _
    obtain ⟨m', a1, a2, hm'⟩ : ∃ m', m + 1 ≤ m' ∧ m' ≤ m + 2 ∧ G m' :=
      (hG (m + 1)).elim (fun x => ⟨_, le_rfl, by omega, x⟩) fun x => ⟨_, by omega, le_rfl, x⟩
    have hnj : 1 ≤ n * j := Nat.mul_pos hn1 hj
    have l3 : m ≤ n * j := by
      by_contra hc
      push Not at hc
      have : n ^ 2 * j ≤ (n * j) * (n * j) := by nlinarith [Nat.mul_le_mul_left (n ^ 2 * j) hj]
      nlinarith
    have l4 : m' ^ 2 ≤ n * (j * (n + 8)) := by nlinarith
    have l5 : h (n ^ 2 * j) ≤ h (m' ^ 2) := hmono (by nlinarith)
    rw [hrel n j hn hj, hsq n hn, hsq m' hm'] at l5
    have l6 := l5.trans (Nat.pow_le_pow_left l4 g)
    rw [pow_two, mul_pow, mul_pow, mul_pow, Nat.mul_assoc] at l6
    rw [mul_comm]
    exact Nat.le_of_mul_le_mul_left l6 (by positivity)
  · refine le_of_frequently (g := g) fun M => ?_
    obtain ⟨n, hMn, hn⟩ := hbig (M + 2)
    have hn1 := hpos n hn
    set m := Nat.sqrt (n ^ 2 * j) with hm
    have l1 : m * m ≤ n ^ 2 * j := Nat.sqrt_le _
    have l2 : n ^ 2 * j < (m + 1) * (m + 1) := Nat.lt_succ_sqrt _
    have l3 : n ≤ m := by
      by_contra hc
      push Not at hc
      nlinarith [Nat.mul_le_mul_left (n ^ 2) hj]
    obtain ⟨m', a1, a2, hm'⟩ : ∃ m', m' ≤ m ∧ m ≤ m' + 1 ∧ G m' :=
      (hG (m - 1)).elim (fun x => ⟨_, by omega, by omega, x⟩) fun x => ⟨_, by omega, by omega, x⟩
    have hm1 := hpos m' hm'
    refine ⟨m', by omega, ?_⟩
    have l4 : n ^ 2 * j ≤ m' * (m' + 8) := by nlinarith
    have l5 : h (m' ^ 2) ≤ h (n ^ 2 * j) := hmono (by nlinarith)
    rw [hrel n j hn hj, hsq n hn, hsq m' hm'] at l5
    have l6 := Nat.pow_le_pow_left l4 g
    rw [mul_pow, mul_pow] at l6
    rw [pow_two m', mul_pow] at l5
    have l7 : (n ^ 2) ^ g * (j ^ g * m' ^ g) ≤ (n ^ 2) ^ g * (h j * (m' + 8) ^ g) :=
      calc _ = ((n ^ 2) ^ g * j ^ g) * m' ^ g := by ring
        _ ≤ (m' ^ g * (m' + 8) ^ g) * m' ^ g := Nat.mul_le_mul_right _ l6
        _ = (m' ^ g * m' ^ g) * (m' + 8) ^ g := by ring
        _ ≤ ((n ^ 2) ^ g * h j) * (m' + 8) ^ g := Nat.mul_le_mul_right _ l5
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left l7 (by positivity)

/-- Monotonicity fills the gaps between admissible squares. Growth along
sufficiently large multiples suffices, since the multiple can be increased. -/
theorem eq_pow_of_growth (h : ℕ → ℕ) (d : ℕ) (G : ℕ → Prop)
    (hG : ∀ m, G m ∨ G (m + 1)) (hG0 : ¬ G 0) (h₁ : h 1 = 1)
    (hmono : Monotone h) (hrel : ∀ n j, G n → 1 ≤ j → h (n ^ 2 * j) = h (n ^ 2) * h j)
    (N b c C : ℕ) (hN : 1 ≤ N)
    (hgr : ∀ t : ℕ, b ≤ t → 1 ≤ t → t ^ d ≤ c * h (N * t) ∧ h (N * t) ≤ C * t ^ d)
    (j : ℕ) (hj : 1 ≤ j) : h j = j ^ d := by
  let B := max b 1
  have hB : 1 ≤ B := le_max_right _ _
  refine eq_pow_of_growth_every_index h d G hG hG0 h₁ hmono hrel (N * B) c (C * B ^ d)
    (Nat.mul_pos hN hB) (fun t ht => ?_) j hj
  have hBt : B ≤ B * t := Nat.le_mul_of_pos_right B ht
  have htB : t ≤ B * t := Nat.le_mul_of_pos_left t hB
  obtain ⟨hl, hu⟩ := hgr (B * t) ((le_max_left b 1).trans hBt) (ht.trans htB)
  constructor
  · exact (Nat.pow_le_pow_left htB d).trans (by simpa only [Nat.mul_assoc] using hl)
  · simpa only [Nat.mul_assoc, mul_pow] using hu

end GlobalTheory.FinrankGrowthBounds

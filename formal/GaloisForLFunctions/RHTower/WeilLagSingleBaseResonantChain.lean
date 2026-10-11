import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Dist

/-!
# A resonant chain whose single-base lag samples are eventually negative

A single-base lag sequence samples `Φ(u) = Σ_ρ w_ρ e^{u(ρ − ½)}` on the lattice `u = m log b`. A
bounded sample sequence excludes every attained top real part, and Pringsheim's theorem forces any
remaining obstruction to be a chain of real parts increasing to a supremum that is not attained, with
ordinates approaching the lattice `(2π/log b)ℤ`. This file shows that such a chain does evade the
lattice samples, for weights with positive real part.

**Theorem** (`chainSum_neg`). With rates `σ_n = 1 − 2^{−(n+1)}` (increasing to `1`, not attained),
weights `e^{−40(n+1)}` and phases `φ_n = π/(120·2ⁿ) → 0`,

`Σ_n e^{−40(n+1)} e^{mσ_n} cos(mφ_n) < 0` for every real `m ≥ 80`.

**Mechanism (Newton polygon).** The term `n` dominates on the window `[80·2ⁿ, 160·2ⁿ]`, where its phase
lies in `[2π/3, 4π/3]` and its cosine is at most `−½`. Its neighbours are comparable only at the window
ends, where their own cosines are nonpositive. Every other term is smaller by `e^{−5}2^{1−d}`, `d` the
index distance.

For a base `b > 1`, `σ_n/log b` and `φ_n/log b` are the real parts and ordinates of the chain: the
samples `Φ(m log b)` of this configuration are negative for `m ≥ 80`, hence bounded above.
-/

open Real Finset Filter Topology

noncomputable section

namespace RHTower

/-- The exponent `−40(n+1) + m(1 − 2^{−(n+1)})`. -/
def resonantChainExponent (m : ℝ) (n : ℕ) : ℝ := -(40 * ((n : ℝ) + 1)) + m * (1 - 1 / 2 ^ (n + 1))

/-- The phase `π/(120·2ⁿ)`. -/
def resonantChainPhase (n : ℕ) : ℝ := Real.pi / (120 * 2 ^ n)

/-- The `n`-th term `e^{−40(n+1)} e^{m(1 − 2^{−(n+1)})} cos(mφ_n)`. -/
def resonantChainTerm (m : ℝ) (n : ℕ) : ℝ := Real.exp (resonantChainExponent m n) * Real.cos (m * resonantChainPhase n)

/-- The chain sum. -/
def resonantChainSum (m : ℝ) : ℝ := ∑' n, resonantChainTerm m n

/-! ## Elementary bounds -/

theorem exp_neg_five_lt : Real.exp (-5) < 1 / 8 := by
  have h1 : (5 : ℝ) / 2 + 1 ≤ Real.exp (5 / 2) := Real.add_one_le_exp _
  have h2 : Real.exp 5 = Real.exp (5 / 2) ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : 8 < Real.exp 5 := by rw [h2]; nlinarith
  rw [Real.exp_neg, one_div]
  exact inv_strictAnti₀ (by norm_num) h3

theorem exp_neg_le_half_pow (k : ℕ) : Real.exp (-(k : ℝ)) ≤ (1 / 2) ^ k := by
  have h : Real.exp (-1) ≤ 1 / 2 := by
    have := Real.add_one_le_exp 1
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith)
  rw [show -(k : ℝ) = k * (-1) by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le h k

theorem two_mul_le_two_pow (i : ℕ) : 2 * i ≤ 2 ^ i := by
  induction i with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; norm_num
    · rw [pow_succ]; omega

theorem chainExponent_sub (m : ℝ) (j n : ℕ) :
    resonantChainExponent m j - resonantChainExponent m n =
      40 * ((n : ℝ) - j) + m * (1 / 2 ^ (n + 1) - 1 / 2 ^ (j + 1)) := by
  unfold resonantChainExponent; ring

theorem cos_le_neg_half_of_mem {x : ℝ} (h1 : 2 * Real.pi / 3 ≤ x) (h2 : x ≤ 4 * Real.pi / 3) :
    Real.cos x ≤ -(1 / 2) := by
  have hπ := Real.pi_pos
  have e : Real.cos x = -Real.cos (x - Real.pi) := by
    rw [Real.cos_sub_pi]; ring
  have hle : Real.cos (Real.pi / 3) ≤ Real.cos (x - Real.pi) := by
    rw [← Real.cos_abs (x - Real.pi)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith)
      (by rw [abs_le]; constructor <;> linarith)
  rw [Real.cos_pi_div_three] at hle
  linarith

/-- A term whose exponent lies `5 + (d − 1)` below the dominant one is at most
`2e^{−5}(½)^d` times the dominant exponential. -/
theorem chainTerm_le_of_exponent {m : ℝ} {j n : ℕ} (hd : 1 ≤ Nat.dist j n)
    (h : Real.cos (m * resonantChainPhase j) ≤ 0 ∨
      resonantChainExponent m j - resonantChainExponent m n ≤ -5 - ((Nat.dist j n : ℝ) - 1)) :
    resonantChainTerm m j ≤ 2 * Real.exp (-5) * (1 / 2) ^ Nat.dist j n * Real.exp (resonantChainExponent m n) := by
  have hR : 0 ≤ 2 * Real.exp (-5) * (1 / 2) ^ Nat.dist j n * Real.exp (resonantChainExponent m n) := by
    positivity
  rcases h with h | h
  · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le h) hR
  · unfold resonantChainTerm
    have hcos := Real.cos_le_one (m * resonantChainPhase j)
    have h1 : Real.exp (resonantChainExponent m j) * Real.cos (m * resonantChainPhase j) ≤
        Real.exp (resonantChainExponent m j) := by
      nlinarith [Real.exp_pos (resonantChainExponent m j)]
    refine le_trans h1 ?_
    have h2 : Real.exp (resonantChainExponent m j) ≤
        Real.exp (-5 - ((Nat.dist j n : ℝ) - 1)) * Real.exp (resonantChainExponent m n) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    refine le_trans h2 ?_
    obtain ⟨k, hk⟩ : ∃ k, Nat.dist j n = k + 1 := ⟨Nat.dist j n - 1, by omega⟩
    rw [hk]
    have h3 : Real.exp (-5 - (((k + 1 : ℕ) : ℝ) - 1)) = Real.exp (-5) * Real.exp (-(k : ℝ)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [h3]
    have h4 := exp_neg_le_half_pow k
    have h5 : (2 : ℝ) * (1 / 2) ^ (k + 1) = (1 / 2) ^ k := by rw [pow_succ]; ring
    have hE := Real.exp_pos (resonantChainExponent m n)
    have h5' := Real.exp_pos (-5)
    calc Real.exp (-5) * Real.exp (-(k : ℝ)) * Real.exp (resonantChainExponent m n)
        ≤ Real.exp (-5) * (1 / 2) ^ k * Real.exp (resonantChainExponent m n) := by gcongr
      _ = 2 * Real.exp (-5) * (1 / 2) ^ (k + 1) * Real.exp (resonantChainExponent m n) := by
          rw [← h5]; ring

/-! ## The window of the `n`-th term -/

theorem phase_mul_eq (m : ℝ) (n : ℕ) : m * resonantChainPhase n = m / (120 * 2 ^ n) * Real.pi := by
  unfold resonantChainPhase; field_simp

/-- **The dominant term.** On `[80·2ⁿ, 160·2ⁿ]` the `n`-th term is at most `−½e^{E_n}`. -/
theorem chainTerm_self_le {m : ℝ} {n : ℕ} (h1 : 80 * 2 ^ n ≤ m) (h2 : m ≤ 160 * 2 ^ n) :
    resonantChainTerm m n ≤ -(1 / 2) * Real.exp (resonantChainExponent m n) := by
  have hπ := Real.pi_pos
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hc : Real.cos (m * resonantChainPhase n) ≤ -(1 / 2) := by
    rw [phase_mul_eq]
    apply cos_le_neg_half_of_mem
    · have : (2 : ℝ) / 3 ≤ m / (120 * 2 ^ n) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      nlinarith
    · have : m / (120 * 2 ^ n) ≤ (4 : ℝ) / 3 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      nlinarith
  unfold resonantChainTerm
  have := Real.exp_pos (resonantChainExponent m n)
  nlinarith

/-- **Every other term is small.** On `[80·2ⁿ, 160·2ⁿ]`, every `j ≠ n` has
`term_j ≤ 2e^{−5}(½)^{|j−n|}e^{E_n}`. -/
theorem chainTerm_le_of_ne {m : ℝ} {j n : ℕ} (h1 : 80 * 2 ^ n ≤ m) (h2 : m ≤ 160 * 2 ^ n)
    (hjn : j ≠ n) :
    resonantChainTerm m j ≤ 2 * Real.exp (-5) * (1 / 2) ^ Nat.dist j n * Real.exp (resonantChainExponent m n) := by
  have hπ := Real.pi_pos
  have hd : 1 ≤ Nat.dist j n := by
    rcases lt_or_gt_of_ne hjn with h | h
    · rw [Nat.dist_eq_sub_of_le h.le]; omega
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h.le]; omega
  apply chainTerm_le_of_exponent hd
  rw [chainExponent_sub]
  rcases (show n = j + 1 ∨ j = n + 1 ∨ (∃ i, n = j + 2 + i) ∨ (∃ i, j = n + 2 + i) by
    rcases lt_or_gt_of_ne hjn with h | h
    · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
      · left; omega
      · right; right; left; exact ⟨n - (j + 2), by omega⟩
    · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
      · right; left; omega
      · right; right; right; exact ⟨j - (n + 2), by omega⟩) with h | h | ⟨i, h⟩ | ⟨i, h⟩
  · -- the left neighbour: `n = j + 1`
    subst h
    have hdist : Nat.dist j (j + 1) = 1 := by rw [Nat.dist_eq_sub_of_le (by omega)]; omega
    rw [hdist]
    set X : ℝ := 2 ^ j with hX
    have hX0 : 0 < X := by positivity
    have e1 : (2 : ℝ) ^ (j + 1) = 2 * X := by rw [pow_succ, hX]; ring
    have e2 : (2 : ℝ) ^ (j + 1 + 1) = 4 * X := by rw [pow_succ, pow_succ, hX]; ring
    rw [e1] at h1 h2
    by_cases hx : m * resonantChainPhase j ≤ 3 * Real.pi / 2
    · left
      apply Real.cos_nonpos_of_pi_div_two_le_of_le _ (by linarith)
      rw [phase_mul_eq]
      have : (1 : ℝ) / 2 ≤ m / (120 * X) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      nlinarith
    · right
      push Not at hx
      rw [phase_mul_eq] at hx
      have hm : 180 * X < m := by
        have : (3 : ℝ) / 2 < m / (120 * X) := by
          by_contra hc; push Not at hc; nlinarith
        rw [lt_div_iff₀ (by positivity)] at this; linarith
      rw [e2, e1]
      have e : m * (1 / (4 * X) - 1 / (2 * X)) = -(m / (4 * X)) := by field_simp; ring
      rw [e]
      have : (45 : ℝ) < m / (4 * X) := by rw [lt_div_iff₀ (by positivity)]; linarith
      push_cast
      linarith
  · -- the right neighbour: `j = n + 1`
    subst h
    have hdist : Nat.dist (n + 1) n = 1 := by
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega)]; omega
    rw [hdist]
    set X : ℝ := 2 ^ n with hX
    have hX0 : 0 < X := by positivity
    have e1 : (2 : ℝ) ^ (n + 1) = 2 * X := by rw [pow_succ, hX]; ring
    have e2 : (2 : ℝ) ^ (n + 1 + 1) = 4 * X := by rw [pow_succ, pow_succ, hX]; ring
    by_cases hx : Real.pi / 2 ≤ m * resonantChainPhase (n + 1)
    · left
      apply Real.cos_nonpos_of_pi_div_two_le_of_le hx
      rw [phase_mul_eq, e1]
      have : m / (120 * (2 * X)) ≤ (2 : ℝ) / 3 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      nlinarith
    · right
      push Not at hx
      rw [phase_mul_eq, e1] at hx
      have hm : m < 120 * X := by
        have : m / (120 * (2 * X)) < (1 : ℝ) / 2 := by
          by_contra hc; push Not at hc; nlinarith
        rw [div_lt_iff₀ (by positivity)] at this; linarith
      rw [e2, e1]
      have e : m * (1 / (2 * X) - 1 / (4 * X)) = m / (4 * X) := by field_simp; ring
      rw [e]
      have : m / (4 * X) < 30 := by rw [div_lt_iff₀ (by positivity)]; linarith
      push_cast
      linarith
  · -- `n ≥ j + 2`
    subst h
    right
    have hdist : Nat.dist j (j + 2 + i) = i + 2 := by
      rw [Nat.dist_eq_sub_of_le (by omega)]; omega
    rw [hdist]
    set X : ℝ := 2 ^ (j + 1) with hX
    set Y : ℝ := 2 ^ (i + 2) with hY
    have hX0 : 0 < X := by positivity
    have hY0 : (0 : ℝ) < Y := by positivity
    have hYge : 2 * ((i : ℝ) + 2) ≤ Y := by
      have := two_mul_le_two_pow (i + 2); rw [hY]; exact_mod_cast this
    have e1 : (2 : ℝ) ^ (j + 2 + i + 1) = X * Y := by rw [hX, hY, ← pow_add]; ring_nf
    have e0 : (2 : ℝ) ^ (j + 2 + i) * 2 = X * Y := by rw [← pow_succ, e1]
    have hm : 40 * (X * Y) ≤ m := by rw [← e0]; linarith
    rw [e1]
    have e : m * (1 / (X * Y) - 1 / X) = -(m / (X * Y) * (Y - 1)) := by field_simp; ring
    rw [e]
    have h40 : (40 : ℝ) ≤ m / (X * Y) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hY1 : (0 : ℝ) ≤ Y - 1 := by linarith
    push_cast
    nlinarith
  · -- `j ≥ n + 2`
    subst h
    right
    have hdist : Nat.dist (n + 2 + i) n = i + 2 := by
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega)]; omega
    rw [hdist]
    set X : ℝ := 2 ^ (n + 1) with hX
    set Y : ℝ := 2 ^ (i + 2) with hY
    have hX0 : 0 < X := by positivity
    have hY0 : (0 : ℝ) < Y := by positivity
    have hY4 : (4 : ℝ) ≤ Y := by
      rw [hY]
      have : (2 : ℝ) ^ 2 ≤ 2 ^ (i + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at this ⊢; linarith
    have e1 : (2 : ℝ) ^ (n + 2 + i + 1) = X * Y := by rw [hX, hY, ← pow_add]; ring_nf
    have e0 : (2 : ℝ) ^ n * 2 = X := by rw [hX, pow_succ]
    have hm : m ≤ 80 * X := by rw [← e0]; linarith
    rw [e1]
    have e : m * (1 / X - 1 / (X * Y)) = m / X * (1 - 1 / Y) := by field_simp
    rw [e]
    have hmX : m / X ≤ 80 := by rw [div_le_iff₀ hX0]; linarith
    have hmX0 : 0 ≤ m / X := div_nonneg (by linarith [mul_pos (by norm_num : (0:ℝ) < 80) (pow_pos (by norm_num : (0:ℝ) < 2) n)]) hX0.le
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have hY : Y = 4 := by rw [hY]; norm_num
      rw [hY]
      push_cast
      nlinarith
    · have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hipos
      have h1Y : 0 ≤ 1 - 1 / Y := by
        rw [sub_nonneg, div_le_one (by linarith)]; linarith
      have h1Y' : 1 - 1 / Y ≤ 1 := by
        have : 0 ≤ 1 / Y := by positivity
        linarith
      have : m / X * (1 - 1 / Y) ≤ 80 := by nlinarith
      push_cast
      nlinarith

/-! ## Summation -/

theorem summable_half_pow_dist (n : ℕ) : Summable fun j : ℕ => (1 / 2 : ℝ) ^ Nat.dist j n := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left
      ((2 : ℝ) ^ n))
  rcases le_or_gt n j with h | h
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]
    have e : (2 : ℝ) ^ n * (1 / 2) ^ j = (1 / 2) ^ (j - n) := by
      rw [show j = j - n + n by omega, pow_add, one_div_pow (n := n)]
      field_simp
      simp
    rw [e]
  · have h1 : (1 / 2 : ℝ) ^ Nat.dist j n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h2 : (1 : ℝ) ≤ 2 ^ n * (1 / 2) ^ j := by
      rw [show n = n - j + j by omega, pow_add, mul_assoc, ← mul_pow]
      norm_num
      exact one_le_pow₀ (by norm_num)
    linarith

theorem tsum_half_pow_dist_le (n : ℕ) : ∑' j : ℕ, (1 / 2 : ℝ) ^ Nat.dist j n ≤ 3 := by
  have hs := summable_half_pow_dist n
  rw [← hs.sum_add_tsum_nat_add n]
  have h1 : ∑ j ∈ range n, (1 / 2 : ℝ) ^ Nat.dist j n ≤ 1 := by
    have e : ∑ j ∈ range n, (1 / 2 : ℝ) ^ Nat.dist j n = ∑ j ∈ range n, (1 / 2 : ℝ) ^ (j + 1) := by
      rw [← Finset.sum_range_reflect (fun j => (1 / 2 : ℝ) ^ (j + 1)) n]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      rw [Nat.dist_eq_sub_of_le hj'.le]
      congr 1
      omega
    rw [e]
    have hg := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have h2 : ∑ j ∈ range n, (1 / 2 : ℝ) ^ (j + 1) = (1 / 2) * ∑ j ∈ range n, (1 / 2 : ℝ) ^ j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
    rw [h2]
    have h3 := hg.sum_le_tsum (range n) (fun j _ => by positivity)
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h3
    norm_num at h3 ⊢
    linarith
  have h2 : ∑' i : ℕ, (1 / 2 : ℝ) ^ Nat.dist (i + n) n = 2 := by
    have e : ∀ i : ℕ, Nat.dist (i + n) n = i := fun i => by
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega)]; omega
    simp_rw [e]
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  linarith

theorem summable_chainTerm {m : ℝ} (hm : 0 ≤ m) : Summable (resonantChainTerm m) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (Real.exp_pos (-40)).le
      ((Real.exp_lt_exp.mpr (by norm_num : (-40 : ℝ) < 0)).trans_eq Real.exp_zero)).mul_left (Real.exp (m - 40))) fun j => ?_
  unfold resonantChainTerm
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hc := Real.abs_cos_le_one (m * resonantChainPhase j)
  have h1 : Real.exp (resonantChainExponent m j) ≤ Real.exp (m - 40) * Real.exp (-40) ^ j := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold resonantChainExponent
    have : (0 : ℝ) ≤ m * (1 / 2 ^ (j + 1)) := by positivity
    nlinarith
  calc Real.exp (resonantChainExponent m j) * |Real.cos (m * resonantChainPhase j)| ≤ Real.exp (resonantChainExponent m j) := by
        nlinarith [Real.exp_pos (resonantChainExponent m j), abs_nonneg (Real.cos (m * resonantChainPhase j))]
    _ ≤ _ := h1

/-- **The chain sum is negative on every window.** -/
theorem chainSum_neg_of_window {m : ℝ} {n : ℕ} (h1 : 80 * 2 ^ n ≤ m) (h2 : m ≤ 160 * 2 ^ n) :
    resonantChainSum m < 0 := by
  classical
  have hm0 : 0 ≤ m := le_trans (by positivity) h1
  set A := Real.exp (resonantChainExponent m n) with hA
  have hA0 : 0 < A := Real.exp_pos _
  set u : ℕ → ℝ := fun j => 2 * Real.exp (-5) * (1 / 2) ^ Nat.dist j n * A -
    (if j = n then (1 / 2 + 2 * Real.exp (-5)) * A else 0) with hu
  have hle : ∀ j, resonantChainTerm m j ≤ u j := by
    intro j
    by_cases hj : j = n
    · subst hj
      simp only [hu, if_true, Nat.dist_self, pow_zero, mul_one]
      have := chainTerm_self_le h1 h2
      linarith
    · simp only [hu, if_neg hj, sub_zero]
      exact chainTerm_le_of_ne h1 h2 hj
  have hs1 : Summable fun j => 2 * Real.exp (-5) * (1 / 2) ^ Nat.dist j n * A := by
    have := (summable_half_pow_dist n).mul_left (2 * Real.exp (-5))
    exact this.mul_right A
  have hs2 : Summable fun j : ℕ => if j = n then (1 / 2 + 2 * Real.exp (-5)) * A else 0 :=
    summable_of_ne_finset_zero (s := {n}) fun j hj => by
      simp only [Finset.mem_singleton] at hj; simp [hj]
  have hsu : Summable u := hs1.sub hs2
  have hsum := (summable_chainTerm hm0).tsum_le_tsum hle hsu
  have hval : ∑' j, u j = 2 * Real.exp (-5) * A * ∑' j : ℕ, (1 / 2 : ℝ) ^ Nat.dist j n -
      (1 / 2 + 2 * Real.exp (-5)) * A := by
    rw [hu, hs1.tsum_sub hs2, tsum_ite_eq]
    congr 1
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    ring
  have hd := tsum_half_pow_dist_le n
  have he := exp_neg_five_lt
  have he0 := Real.exp_pos (-5)
  unfold resonantChainSum
  have : ∑' j, u j < 0 := by
    rw [hval]
    have h3 : 2 * Real.exp (-5) * A * ∑' j : ℕ, (1 / 2 : ℝ) ^ Nat.dist j n ≤
        2 * Real.exp (-5) * A * 3 :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    nlinarith
  linarith

/-- **The resonant chain evades the lattice.** `Σ_n e^{−40(n+1)}e^{m(1−2^{−(n+1)})}cos(mπ/(120·2ⁿ)) < 0`
for every real `m ≥ 80`. -/
theorem chainSum_neg {m : ℝ} (hm : 80 ≤ m) : resonantChainSum m < 0 := by
  classical
  have hex : ∃ n : ℕ, m ≤ 160 * 2 ^ n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt m (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]⟩
  set n := Nat.find hex with hn
  have h2 : m ≤ 160 * 2 ^ n := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · exact chainSum_neg_of_window (n := n) (by rw [h0]; simpa using hm) h2
  · obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hmin := Nat.find_min hex (m := k) (by omega)
    push Not at hmin
    refine chainSum_neg_of_window (n := n) ?_ h2
    rw [hk, pow_succ]
    linarith

/-- The chain data: rates `1 − 2^{−(n+1)}` increase strictly to `1` without reaching it, the phases
tend to `0`, and the weights `e^{−40(n+1)}` are summable. -/
theorem chain_data :
    StrictMono (fun n : ℕ => 1 - 1 / (2 : ℝ) ^ (n + 1)) ∧
      (∀ n : ℕ, 1 - 1 / (2 : ℝ) ^ (n + 1) < 1) ∧
      Tendsto (fun n : ℕ => 1 - 1 / (2 : ℝ) ^ (n + 1)) atTop (𝓝 1) ∧
      Tendsto resonantChainPhase atTop (𝓝 0) ∧
      Summable (fun n : ℕ => Real.exp (-(40 * ((n : ℝ) + 1)))) := by
  refine ⟨fun a b hab => ?_, fun n => ?_, ?_, ?_, ?_⟩
  · have : (2 : ℝ) ^ (a + 1) < 2 ^ (b + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
    have h0 : (0 : ℝ) < 2 ^ (a + 1) := by positivity
    simp only
    have : 1 / (2 : ℝ) ^ (b + 1) < 1 / 2 ^ (a + 1) := one_div_lt_one_div_of_lt h0 this
    linarith
  · have : (0 : ℝ) < 1 / 2 ^ (n + 1) := by positivity
    linarith
  · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).comp (tendsto_add_atTop_nat 1)
    have h' : Tendsto (fun n : ℕ => 1 - (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub h
    rw [sub_zero] at h'
    refine h'.congr fun n => ?_
    rw [one_div_pow]
  · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (Real.pi / 120)
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    unfold resonantChainPhase
    rw [one_div_pow]
    field_simp
  · have h := (summable_geometric_of_lt_one (Real.exp_pos (-40)).le
      ((Real.exp_lt_exp.mpr (by norm_num : (-40 : ℝ) < 0)).trans_eq Real.exp_zero)).mul_left (Real.exp (-40))
    refine h.congr fun n => ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring

end RHTower

end

import Mathlib

/-!
# The window ladder

A window of length `L` leaves the remainder chain at scale `L`, so a construction that starts with a
long window cannot pass directly to windows of length `x^θ`: the state would be measured in the wrong
scale.  The ladder halves the window length at each step until it reaches `x^θ`, and each halving
costs only a bounded factor in the state constant.
-/

noncomputable section

open Filter

namespace RHTower.Sieve

/-- Base and length of the `k`-th window of the ladder. -/
def ladder (θ C x₀ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (x₀, C * x₀)
  | (k + 1) =>
      let s := ladder θ C x₀ k
      (s.1 + s.2, max ((s.1 + s.2) ^ θ) (s.2 / 2))

/-- The base point of the `k`-th window. -/
def ladderBase (θ C x₀ : ℝ) (k : ℕ) : ℝ := (ladder θ C x₀ k).1

/-- The length of the `k`-th window. -/
def ladderLen (θ C x₀ : ℝ) (k : ℕ) : ℝ := (ladder θ C x₀ k).2

theorem ladderBase_zero (θ C x₀ : ℝ) : ladderBase θ C x₀ 0 = x₀ := rfl

theorem ladderLen_zero (θ C x₀ : ℝ) : ladderLen θ C x₀ 0 = C * x₀ := rfl

theorem ladderBase_succ (θ C x₀ : ℝ) (k : ℕ) :
    ladderBase θ C x₀ (k + 1) = ladderBase θ C x₀ k + ladderLen θ C x₀ k := rfl

theorem ladderLen_succ (θ C x₀ : ℝ) (k : ℕ) :
    ladderLen θ C x₀ (k + 1)
      = max ((ladderBase θ C x₀ (k + 1)) ^ θ) (ladderLen θ C x₀ k / 2) := rfl

theorem ladderLen_pos (θ : ℝ) {C x₀ : ℝ} (hC : 0 < C) (hx₀ : 0 < x₀) (k : ℕ) :
    0 < ladderLen θ C x₀ k := by
  induction k with
  | zero =>
      rw [ladderLen_zero]
      positivity
  | succ k ih =>
      rw [ladderLen_succ]
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _)

theorem ladderBase_pos (θ : ℝ) {C x₀ : ℝ} (hC : 0 < C) (hx₀ : 0 < x₀) (k : ℕ) :
    0 < ladderBase θ C x₀ k := by
  induction k with
  | zero =>
      rw [ladderBase_zero]
      exact hx₀
  | succ k ih =>
      rw [ladderBase_succ]
      have := ladderLen_pos θ hC hx₀ k
      linarith

theorem ladderBase_le_succ (θ : ℝ) {C x₀ : ℝ} (hC : 0 < C) (hx₀ : 0 < x₀) (k : ℕ) :
    ladderBase θ C x₀ k ≤ ladderBase θ C x₀ (k + 1) := by
  rw [ladderBase_succ]
  have := ladderLen_pos θ hC hx₀ k
  linarith

theorem ladderBase_mono (θ : ℝ) {C x₀ : ℝ} (hC : 0 < C) (hx₀ : 0 < x₀) :
    Monotone (ladderBase θ C x₀) :=
  monotone_nat_of_le_succ (ladderBase_le_succ θ hC hx₀)

theorem ladderBase_ge (θ : ℝ) {C x₀ : ℝ} (hC : 0 < C) (hx₀ : 0 < x₀) (k : ℕ) :
    x₀ ≤ ladderBase θ C x₀ k := by
  have := ladderBase_mono θ hC hx₀ (Nat.zero_le k)
  rwa [ladderBase_zero] at this

/-- Lengths halve at worst. -/
theorem ladderLen_le_two_mul (θ C x₀ : ℝ) (k : ℕ) :
    ladderLen θ C x₀ k ≤ 2 * ladderLen θ C x₀ (k + 1) := by
  have h := le_max_right ((ladderBase θ C x₀ (k + 1)) ^ θ) (ladderLen θ C x₀ k / 2)
  rw [ladderLen_succ]
  linarith

/-- From the first rung on, the window is at least the `θ`-power of its base. -/
theorem rpow_le_ladderLen (θ C x₀ : ℝ) (k : ℕ) :
    (ladderBase θ C x₀ (k + 1)) ^ θ ≤ ladderLen θ C x₀ (k + 1) := by
  rw [ladderLen_succ]
  exact le_max_left _ _

theorem ladderLen_le {θ : ℝ} (hθ : 0 ≤ θ) {C x₀ : ℝ} (hC : 0 < C) (hx₀ : 0 < x₀) (k : ℕ) :
    ladderLen θ C x₀ k ≤ max ((ladderBase θ C x₀ k) ^ θ) (C * x₀ / 2 ^ k) := by
  induction k with
  | zero =>
      rw [ladderLen_zero, ladderBase_zero]
      simp
  | succ k ih =>
      rw [ladderLen_succ]
      refine max_le (le_max_left _ _) ?_
      refine le_trans (by linarith [ih] : ladderLen θ C x₀ k / 2
        ≤ max ((ladderBase θ C x₀ k) ^ θ) (C * x₀ / 2 ^ k) / 2) ?_
      rcases le_total ((ladderBase θ C x₀ k) ^ θ) (C * x₀ / 2 ^ k) with h | h
      · rw [max_eq_right h]
        refine le_trans (le_of_eq ?_) (le_max_right _ _)
        rw [pow_succ]
        ring
      · rw [max_eq_left h]
        refine le_trans ?_ (le_max_left _ _)
        have hmono : (ladderBase θ C x₀ k) ^ θ ≤ (ladderBase θ C x₀ (k + 1)) ^ θ :=
          Real.rpow_le_rpow (le_of_lt (ladderBase_pos θ hC hx₀ k))
            (ladderBase_le_succ θ hC hx₀ k) hθ
        have hpos : (0:ℝ) < (ladderBase θ C x₀ k) ^ θ :=
          Real.rpow_pos_of_pos (ladderBase_pos θ hC hx₀ k) θ
        linarith
  
theorem ladderBase_lower_linear {θ : ℝ} (hθ : 0 ≤ θ) {C x₀ : ℝ} (hC : 0 < C) (hx₀ : 0 < x₀)
    (k : ℕ) :
    x₀ + (k : ℝ) * min (C * x₀) (x₀ ^ θ) ≤ ladderBase θ C x₀ k := by
  induction k with
  | zero =>
      rw [ladderBase_zero]
      simp
  | succ k ih =>
      rw [ladderBase_succ]
      have hstep : min (C * x₀) (x₀ ^ θ) ≤ ladderLen θ C x₀ k := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [ladderLen_zero]
          exact min_le_left _ _
        · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          refine le_trans (min_le_right _ _) (le_trans ?_ (rpow_le_ladderLen θ C x₀ k'))
          exact Real.rpow_le_rpow (le_of_lt hx₀) (ladderBase_ge θ hC hx₀ (k' + 1)) hθ
      push_cast
      linarith

theorem ladderBase_tendsto {θ : ℝ} (hθ : 0 ≤ θ) {C x₀ : ℝ} (hC : 0 < C) (hx₀ : 0 < x₀) :
    Tendsto (ladderBase θ C x₀) atTop atTop := by
  have hmin : 0 < min (C * x₀) (x₀ ^ θ) := by
    refine lt_min (by positivity) (Real.rpow_pos_of_pos hx₀ θ)
  have hlin : Tendsto (fun k : ℕ => x₀ + (k : ℝ) * min (C * x₀) (x₀ ^ θ)) atTop atTop := by
    refine tendsto_atTop_add_const_left _ x₀ ?_
    exact tendsto_natCast_atTop_atTop.atTop_mul_const hmin
  exact tendsto_atTop_mono (fun k => ladderBase_lower_linear hθ hC hx₀ k) hlin

/-- Eventually the ladder has reached the short windows. -/
theorem eventually_ladderLen_eq {θ : ℝ} (hθ : 0 ≤ θ) {C x₀ : ℝ} (hC : 0 < C) (hx₀ : 0 < x₀) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ladderLen θ C x₀ k = (ladderBase θ C x₀ k) ^ θ := by
  have hx₀θ : (0:ℝ) < x₀ ^ θ := Real.rpow_pos_of_pos hx₀ θ
  have htend : Tendsto (fun k : ℕ => C * x₀ / 2 ^ k) atTop (nhds 0) := by
    have h2 : Tendsto (fun k : ℕ => (2:ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have h3 := (h2.inv_tendsto_atTop).const_mul (C * x₀)
    simpa [div_eq_mul_inv] using h3
  obtain ⟨N₀, hN₀⟩ := (htend.eventually (eventually_le_nhds hx₀θ)).exists_forall_of_atTop
  refine ⟨N₀ + 1, fun k hk => ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hbase : x₀ ^ θ ≤ (ladderBase θ C x₀ (k' + 1)) ^ θ :=
    Real.rpow_le_rpow (le_of_lt hx₀) (ladderBase_ge θ hC hx₀ (k' + 1)) hθ
  have hsmall : C * x₀ / 2 ^ (k' + 1) ≤ x₀ ^ θ := hN₀ (k' + 1) (by omega)
  refine le_antisymm ?_ (rpow_le_ladderLen θ C x₀ k')
  refine le_trans (ladderLen_le hθ hC hx₀ (k' + 1)) ?_
  exact max_le (le_refl _) (le_trans hsmall hbase)

/-- Every window is at least the `θ`-power of its base. -/
theorem rpow_le_ladderLen' {θ : ℝ} (hθ1 : θ ≤ 1) {C x₀ : ℝ} (hC : 1 ≤ C)
    (hx₀ : 1 ≤ x₀) (k : ℕ) :
    (ladderBase θ C x₀ k) ^ θ ≤ ladderLen θ C x₀ k := by
  have hC0 : (0:ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hx₀0 : (0:ℝ) < x₀ := lt_of_lt_of_le zero_lt_one hx₀
  cases k with
  | zero =>
      rw [ladderBase_zero, ladderLen_zero]
      have h1 : x₀ ^ θ ≤ x₀ ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx₀ hθ1
      rw [Real.rpow_one] at h1
      nlinarith [h1, hx₀0]
  | succ k => exact rpow_le_ladderLen θ C x₀ k

/-- Every window is at most `C` times its base. -/
theorem ladderLen_le_mul {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {C x₀ : ℝ} (hC : 1 ≤ C)
    (hx₀ : 1 ≤ x₀) (k : ℕ) :
    ladderLen θ C x₀ k ≤ C * ladderBase θ C x₀ k := by
  have hC0 : (0:ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hx₀0 : (0:ℝ) < x₀ := lt_of_lt_of_le zero_lt_one hx₀
  have hbase1 : (1:ℝ) ≤ ladderBase θ C x₀ k := le_trans hx₀ (ladderBase_ge θ hC0 hx₀0 k)
  have hbase0 : (0:ℝ) < ladderBase θ C x₀ k := lt_of_lt_of_le zero_lt_one hbase1
  refine le_trans (ladderLen_le hθ0 hC0 hx₀0 k) (max_le ?_ ?_)
  · have h1 : (ladderBase θ C x₀ k) ^ θ ≤ (ladderBase θ C x₀ k) ^ (1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase1 hθ1
    rw [Real.rpow_one] at h1
    nlinarith [h1, hbase0]
  · have h2 : C * x₀ / 2 ^ k ≤ C * x₀ := by
      have hpow : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_pos hC0 hx₀0).le (sub_nonneg.2 hpow)]
    have h3 : x₀ ≤ ladderBase θ C x₀ k := ladderBase_ge θ hC0 hx₀0 k
    nlinarith [h2, h3, hC0]

/-- After the first window the length never exceeds the base. -/
theorem ladderLen_le_base {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {C x₀ : ℝ} (hC : 1 ≤ C)
    (hx₀ : 1 ≤ x₀) (k : ℕ) :
    ladderLen θ C x₀ (k + 1) ≤ ladderBase θ C x₀ (k + 1) := by
  have hC0 : (0:ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hx₀0 : (0:ℝ) < x₀ := lt_of_lt_of_le zero_lt_one hx₀
  have hbase1 : (1:ℝ) ≤ ladderBase θ C x₀ (k + 1) :=
    le_trans hx₀ (ladderBase_ge θ hC0 hx₀0 (k + 1))
  have hbase0 : (0:ℝ) < ladderBase θ C x₀ (k + 1) := lt_of_lt_of_le zero_lt_one hbase1
  refine le_trans (ladderLen_le hθ0 hC0 hx₀0 (k + 1)) (max_le ?_ ?_)
  · have h1 : (ladderBase θ C x₀ (k + 1)) ^ θ ≤ (ladderBase θ C x₀ (k + 1)) ^ (1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase1 hθ1
    rwa [Real.rpow_one] at h1
  · have hstep : C * x₀ ≤ ladderBase θ C x₀ 1 := by
      rw [ladderBase_succ, ladderBase_zero, ladderLen_zero]
      linarith
    have hmono : ladderBase θ C x₀ 1 ≤ ladderBase θ C x₀ (k + 1) :=
      ladderBase_mono θ hC0 hx₀0 (by omega)
    have hpow : (1:ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
    have hdiv : C * x₀ / 2 ^ (k + 1) ≤ C * x₀ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_pos hC0 hx₀0).le (sub_nonneg.2 hpow)]
    linarith

theorem ladderBase_ge_index {θ : ℝ} (hθ0 : 0 ≤ θ) {C x₀ : ℝ} (hC : 1 ≤ C) (hx₀ : 1 ≤ x₀)
    (k : ℕ) : (k : ℝ) ≤ ladderBase θ C x₀ k := by
  have hC0 : (0:ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hx₀0 : (0:ℝ) < x₀ := lt_of_lt_of_le zero_lt_one hx₀
  have hmin : (1:ℝ) ≤ min (C * x₀) (x₀ ^ θ) := by
    refine le_min ?_ ?_
    · nlinarith [hC, hx₀]
    · exact Real.one_le_rpow hx₀ hθ0
  have hlow := ladderBase_lower_linear hθ0 hC0 hx₀0 k
  have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [hlow, hmin, hx₀, hk]

end RHTower.Sieve

end

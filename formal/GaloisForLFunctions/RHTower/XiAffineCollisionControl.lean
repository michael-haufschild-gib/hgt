import GaloisForLFunctions.RHTower.RHLadderTheory

/-!
# Affine collision control for the strict-right Xi source

The evaluated theta-cusp Hawking angular source at a strict-right Xi zero `ρ` vanishes exactly
when one of the three affine values `xi (5ρ/2 - 1)`, `xi (ρ/2)`, `xi (3ρ/2)` vanishes.  This file
controls two of those three factors from the zero-free half-plane `Re s ≥ 1` and the isolation of
Xi zeros, with no arithmetic input beyond `xi`.

* `xi (3ρ/2) ≠ 0` for `Re ρ ≥ 2/3`, and for `Re ρ < 2/3` any `3ρ/2`-collision partner is itself a
  strict-right zero whose own `3/2`-partner is zero-free.
* `xi (5ρ/2 - 1) ≠ 0` for `Re ρ ≥ 4/5`.
* Half-collisions descend: the orbit `ρ ↦ 1 - ρ/2` converges to the real point `2/3`, where zeros
  are isolated, so from every strict-right zero one reaches a strict-right zero `ρ'` with
  `xi (ρ'/2) ≠ 0` in finitely many steps.

The `5ρ/2 - 1` factor below `Re ρ = 4/5` is not controlled here.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

private theorem re_three_half (ρ : ℂ) : (3 * ρ / 2).re = 3 * ρ.re / 2 := by
  simp [Complex.div_ofNat_re, Complex.mul_re]

private theorem re_five_half_sub_one (ρ : ℂ) : (5 * ρ / 2 - 1).re = 5 * ρ.re / 2 - 1 := by
  simp [Complex.div_ofNat_re, Complex.mul_re]

private theorem re_half (ρ : ℂ) : (ρ / 2).re = ρ.re / 2 := by
  simp [Complex.div_ofNat_re]

/-- The `3ρ/2` factor is zero-free once `Re ρ ≥ 2/3`. -/
theorem xi_three_half_ne_zero_of_re {ρ : ℂ} (h : 2 / 3 ≤ ρ.re) : xi (3 * ρ / 2) ≠ 0 := by
  apply xi_ne_zero_of_one_le_re
  rw [re_three_half]
  linarith

/-- The `5ρ/2 - 1` factor is zero-free once `Re ρ ≥ 4/5`. -/
theorem xi_five_half_sub_one_ne_zero_of_re {ρ : ℂ} (h : 4 / 5 ≤ ρ.re) :
    xi (5 * ρ / 2 - 1) ≠ 0 := by
  apply xi_ne_zero_of_one_le_re
  rw [re_five_half_sub_one]
  linarith

/-- A `3ρ/2` collision at a strict-right point forces `Re ρ < 2/3`, and the partner `3ρ/2` is
then a strict-right point below the line `Re = 1` whose own `3/2`-partner is zero-free. -/
theorem xi_three_half_collision_partner {ρ : ℂ} (h1 : 1 / 2 < ρ.re) (hc : xi (3 * ρ / 2) = 0) :
    ρ.re < 2 / 3 ∧ 3 / 4 < (3 * ρ / 2).re ∧ (3 * ρ / 2).re < 1 ∧
      xi (3 * (3 * ρ / 2) / 2) ≠ 0 := by
  have hlt : ρ.re < 2 / 3 := by
    by_contra hge
    exact xi_three_half_ne_zero_of_re (le_of_not_gt hge) hc
  refine ⟨hlt, ?_, ?_, ?_⟩
  · rw [re_three_half]; linarith
  · by_contra hge
    exact xi_ne_zero_of_one_le_re (le_of_not_gt hge) hc
  · apply xi_ne_zero_of_one_le_re
    rw [re_three_half, re_three_half]
    linarith

/-- The half-descent orbit `ρ ↦ 1 - ρ/2`. -/
def xiHalfDescent (ρ : ℂ) : ℕ → ℂ
  | 0 => ρ
  | n + 1 => 1 - xiHalfDescent ρ n / 2

theorem xiHalfDescent_zero (ρ : ℂ) : xiHalfDescent ρ 0 = ρ := rfl

theorem xiHalfDescent_succ (ρ : ℂ) (n : ℕ) :
    xiHalfDescent ρ (n + 1) = 1 - xiHalfDescent ρ n / 2 := rfl

theorem xiHalfDescent_eq (ρ : ℂ) (n : ℕ) :
    xiHalfDescent ρ n = 2 / 3 + (-1 / 2 : ℂ) ^ n * (ρ - 2 / 3) := by
  induction n with
  | zero => simp [xiHalfDescent]
  | succ n ih =>
    rw [xiHalfDescent_succ, ih, pow_succ]
    ring

private theorem neg_half_eq_ofReal : (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) := by
  push_cast
  ring

private theorem neg_half_pow_re (n : ℕ) : ((-1 / 2 : ℂ) ^ n).re = (-1 / 2 : ℝ) ^ n := by
  rw [neg_half_eq_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re]

private theorem neg_half_pow_im (n : ℕ) : ((-1 / 2 : ℂ) ^ n).im = 0 := by
  rw [neg_half_eq_ofReal, ← Complex.ofReal_pow, Complex.ofReal_im]

private theorem two_thirds_re : ((2 / 3 : ℂ)).re = 2 / 3 := by simp

private theorem two_thirds_im : ((2 / 3 : ℂ)).im = 0 := by simp

theorem xiHalfDescent_re (ρ : ℂ) (n : ℕ) :
    (xiHalfDescent ρ n).re = 2 / 3 + (-1 / 2 : ℝ) ^ n * (ρ.re - 2 / 3) := by
  rw [xiHalfDescent_eq, Complex.add_re, Complex.mul_re, neg_half_pow_re, neg_half_pow_im,
    Complex.sub_re, two_thirds_re]
  ring

theorem xiHalfDescent_im (ρ : ℂ) (n : ℕ) :
    (xiHalfDescent ρ n).im = (-1 / 2 : ℝ) ^ n * ρ.im := by
  rw [xiHalfDescent_eq, Complex.add_im, Complex.mul_im, neg_half_pow_re, neg_half_pow_im,
    Complex.sub_im, two_thirds_im]
  ring

theorem xiHalfDescent_tendsto (ρ : ℂ) :
    Tendsto (xiHalfDescent ρ) atTop (𝓝 (2 / 3 : ℂ)) := by
  have hn : ‖(-1 / 2 : ℂ)‖ < 1 := by
    rw [norm_div, norm_neg, norm_one]
    simp
    norm_num
  have h : Tendsto (fun n : ℕ => (-1 / 2 : ℂ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn
  have h2 := (h.mul_const (ρ - 2 / 3)).const_add (2 / 3 : ℂ)
  simp only [zero_mul, add_zero] at h2
  refine h2.congr (fun n => ?_)
  rw [xiHalfDescent_eq]

theorem xiHalfDescent_ne_two_thirds {ρ : ℂ} (hi : ρ.im ≠ 0) (n : ℕ) :
    xiHalfDescent ρ n ≠ 2 / 3 := by
  intro h
  have him := xiHalfDescent_im ρ n
  rw [h] at him
  have hp : (-1 / 2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  rw [two_thirds_im] at him
  exact mul_ne_zero hp hi him.symm

/-- Zeros of `xi` propagate along the orbit as long as every half-value vanishes. -/
theorem xi_xiHalfDescent_eq_zero {ρ : ℂ} (hρ : xi ρ = 0) (n : ℕ)
    (h : ∀ m < n, xi (xiHalfDescent ρ m / 2) = 0) : xi (xiHalfDescent ρ n) = 0 := by
  induction n with
  | zero => simpa [xiHalfDescent] using hρ
  | succ n ih =>
    rw [xiHalfDescent_succ, xi_one_sub]
    exact h n (Nat.lt_succ_self n)

/-- Some half-value along the orbit is nonzero: the orbit accumulates at `2/3`, where the zeros of
`xi` are isolated. -/
theorem exists_xiHalfDescent_half_ne_zero {ρ : ℂ} (hρ : xi ρ = 0) (hi : ρ.im ≠ 0) :
    ∃ n, xi (xiHalfDescent ρ n / 2) ≠ 0 := by
  by_contra hcon
  have hcon' : ∀ n, xi (xiHalfDescent ρ n / 2) = 0 :=
    fun n => not_not.mp (fun h => hcon ⟨n, h⟩)
  have hall : ∀ n, xi (xiHalfDescent ρ n) = 0 :=
    fun n => xi_xiHalfDescent_eq_zero hρ n (fun m _ => hcon' m)
  have ha : AnalyticAt ℂ xi (2 / 3) := xi_analyticOnNhd_univ _ (mem_univ _)
  rcases ha.eventually_eq_zero_or_eventually_ne_zero with hz | hnz
  · have h0 := xi_analyticOnNhd_univ.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ (2 / 3 : ℂ)) hz (mem_univ (0 : ℂ))
    simp [xi_zero] at h0
  · have ht : Tendsto (xiHalfDescent ρ) atTop (𝓝[≠] (2 / 3 : ℂ)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨xiHalfDescent_tendsto ρ, Eventually.of_forall (xiHalfDescent_ne_two_thirds hi)⟩
    obtain ⟨n, hn⟩ := (ht.eventually hnz).exists
    exact hn (hall n)

private theorem abs_neg_half_pow_le (n : ℕ) (hn : 1 ≤ n) : |(-1 / 2 : ℝ) ^ n| ≤ 1 / 2 := by
  rw [abs_pow, abs_div, abs_neg, abs_one, abs_two]
  calc (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    _ = 1 / 2 := pow_one _

/-- From every strict-right nonreal zero of `xi`, the half-descent reaches a strict-right nonreal
zero whose half-value is nonzero. -/
theorem exists_xi_zero_half_ne_zero {ρ : ℂ} (hρ : xi ρ = 0) (h1 : 1 / 2 < ρ.re)
    (h2 : ρ.re < 1) (hi : ρ.im ≠ 0) :
    ∃ ρ' : ℂ, xi ρ' = 0 ∧ 1 / 2 < ρ'.re ∧ ρ'.re < 1 ∧ ρ'.im ≠ 0 ∧ xi (ρ' / 2) ≠ 0 := by
  classical
  have hex := exists_xiHalfDescent_half_ne_zero hρ hi
  refine ⟨xiHalfDescent ρ (Nat.find hex), ?_, ?_, ?_, ?_, Nat.find_spec hex⟩
  · exact xi_xiHalfDescent_eq_zero hρ _ (fun m hm => not_not.mp (Nat.find_min hex hm))
  · rw [xiHalfDescent_re]
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, pow_zero]; linarith
    · have hb := abs_neg_half_pow_le _ hpos
      have hs : |ρ.re - 2 / 3| < 1 / 3 := by rw [abs_lt]; constructor <;> linarith
      have := abs_mul ((-1 / 2 : ℝ) ^ (Nat.find hex)) (ρ.re - 2 / 3)
      have hlt : |(-1 / 2 : ℝ) ^ (Nat.find hex) * (ρ.re - 2 / 3)| < 1 / 6 := by
        rw [this]
        calc |(-1 / 2 : ℝ) ^ (Nat.find hex)| * |ρ.re - 2 / 3| ≤ 1 / 2 * |ρ.re - 2 / 3| :=
              mul_le_mul_of_nonneg_right hb (abs_nonneg _)
          _ < 1 / 2 * (1 / 3) := by
              exact mul_lt_mul_of_pos_left hs (by norm_num)
          _ = 1 / 6 := by norm_num
      rw [abs_lt] at hlt
      linarith [hlt.1]
  · rw [xiHalfDescent_re]
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, pow_zero]; linarith
    · have hb := abs_neg_half_pow_le _ hpos
      have hs : |ρ.re - 2 / 3| < 1 / 3 := by rw [abs_lt]; constructor <;> linarith
      have := abs_mul ((-1 / 2 : ℝ) ^ (Nat.find hex)) (ρ.re - 2 / 3)
      have hlt : |(-1 / 2 : ℝ) ^ (Nat.find hex) * (ρ.re - 2 / 3)| < 1 / 6 := by
        rw [this]
        calc |(-1 / 2 : ℝ) ^ (Nat.find hex)| * |ρ.re - 2 / 3| ≤ 1 / 2 * |ρ.re - 2 / 3| :=
              mul_le_mul_of_nonneg_right hb (abs_nonneg _)
          _ < 1 / 2 * (1 / 3) := by
              exact mul_lt_mul_of_pos_left hs (by norm_num)
          _ = 1 / 6 := by norm_num
      rw [abs_lt] at hlt
      linarith [hlt.2]
  · rw [xiHalfDescent_im]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hi

/-- Any nonreal zero of `xi` in the open strip has a strict-right representative. -/
theorem exists_strict_right_representative {ρ : ℂ} (hρ : xi ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hh : ρ.re ≠ 1 / 2) (hi : ρ.im ≠ 0) :
    ∃ ρ' : ℂ, xi ρ' = 0 ∧ 1 / 2 < ρ'.re ∧ ρ'.re < 1 ∧ ρ'.im ≠ 0 := by
  rcases lt_or_gt_of_ne hh with hlt | hgt
  · refine ⟨1 - ρ, by rw [xi_one_sub, hρ], ?_, ?_, ?_⟩
    · simp only [Complex.sub_re, Complex.one_re]; linarith
    · simp only [Complex.sub_re, Complex.one_re]; linarith
    · simp only [Complex.sub_im, Complex.one_im, zero_sub, ne_eq, neg_eq_zero]; exact hi
  · exact ⟨ρ, hρ, hgt, h1, hi⟩

end

end RHTower

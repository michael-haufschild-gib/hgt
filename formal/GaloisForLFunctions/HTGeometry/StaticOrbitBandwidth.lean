import GaloisForLFunctions.HTGeometry.SpectralPhaseBandwidth

/-!
# The bandwidth of a static orbit

Along `U(t) = exp(-itH)` the adjacent phase increment across the gap `δⱼ` is `t δⱼ`, so the
nearest-neighbour ratios of the bandwidth formula are `dist(t δⱼ, 2πℤ)/δⱼ`.  Every one of them is at
most `|t|`, and the one belonging to the smallest gap equals `|t|` as long as `|t| δ_min ≤ π`, so
below that time the bandwidth is exactly `|t|`.

Since the `D-1` gaps sum to the spectral width, one of them is at most the average, which turns the
condition `|t| δ_min ≤ π` into the dimension-linear clock horizon `|t| ≤ π(D-1)/W` with no
anti-concentration input.  At an exact projective recurrence all adjacent increments vanish and the
bandwidth collapses to zero.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## The circular distance below `π` -/

/-- **Below `π` the circular distance is the ordinary one.** -/
theorem circDist_eq_abs_of_le_pi {a b : ℝ} (h : |a - b| ≤ Real.pi) : circDist a b = |a - b| := by
  refine le_antisymm (circDist_le_abs_sub a b) ?_
  obtain ⟨k, hk⟩ := exists_int_circDist a b
  rcases eq_or_ne k 0 with hk0 | hk0
  · rw [hk, hk0]
    simp
  · have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hone : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs (by exact hk0)
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast this
        _ = |(k : ℝ)| := by push_cast [Int.cast_abs]; rfl
    have hbig : 2 * Real.pi ≤ |2 * Real.pi * (k : ℝ)| := by
      rw [abs_mul, abs_of_pos two_pi_pos]
      nlinarith [hone, two_pi_pos]
    have hlow : |2 * Real.pi * (k : ℝ)| - |a - b| ≤ |a - b + 2 * Real.pi * (k : ℝ)| := by
      have := abs_sub_abs_le_abs_sub (2 * Real.pi * (k : ℝ)) (-(a - b))
      simp only [abs_neg] at this
      calc |2 * Real.pi * (k : ℝ)| - |a - b| ≤ |2 * Real.pi * (k : ℝ) - -(a - b)| := this
        _ = |a - b + 2 * Real.pi * (k : ℝ)| := by rw [sub_neg_eq_add, add_comm]
    rw [hk]
    linarith [hbig, hlow, h]

/-! ## The orbit ratios -/

/-- Every orbit ratio is at most `|t|`. -/
theorem circDist_orbit_le (t : ℝ) {E : ℕ → ℝ} (hmono : ∀ j, E j ≤ E (j + 1)) (j : ℕ) :
    circDist (t * E (j + 1)) (t * E j) ≤ |t| * (E (j + 1) - E j) := by
  have hnn : 0 ≤ E (j + 1) - E j := by linarith [hmono j]
  calc circDist (t * E (j + 1)) (t * E j) ≤ |t * E (j + 1) - t * E j| :=
        circDist_le_abs_sub _ _
    _ = |t| * (E (j + 1) - E j) := by
        rw [show t * E (j + 1) - t * E j = t * (E (j + 1) - E j) from by ring, abs_mul,
          abs_of_nonneg hnn]

/-- **`(11)`: at the smallest gap the ratio is exactly `|t|`, below the horizon.** -/
theorem circDist_orbit_ratio_eq (t : ℝ) {E : ℕ → ℝ} {j : ℕ} (hgap : E j < E (j + 1))
    (hsmall : |t| * (E (j + 1) - E j) ≤ Real.pi) :
    circDist (t * E (j + 1)) (t * E j) / (E (j + 1) - E j) = |t| := by
  have hpos : 0 < E (j + 1) - E j := by linarith
  have hrw : t * E (j + 1) - t * E j = t * (E (j + 1) - E j) := by ring
  have habs : |t * E (j + 1) - t * E j| = |t| * (E (j + 1) - E j) := by
    rw [hrw, abs_mul, abs_of_pos hpos]
  have heq : circDist (t * E (j + 1)) (t * E j) = |t| * (E (j + 1) - E j) := by
    rw [circDist_eq_abs_of_le_pi (by rw [habs]; exact hsmall), habs]
  rw [heq]
  field_simp

/-! ## The pigeonhole horizon -/

/-- **`(12)`: the smallest gap is at most the average gap.** -/
theorem minGap_mul_le_width {E : ℕ → ℝ} {m : ℝ} (n : ℕ)
    (hm : ∀ j, j < n → m ≤ E (j + 1) - E j) : (n : ℝ) * m ≤ E n - E 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev : (n : ℝ) * m ≤ E n - E 0 := ih fun j hj => hm j (Nat.lt_succ_of_lt hj)
    have hlast : m ≤ E (n + 1) - E n := hm n (Nat.lt_succ_self n)
    push_cast
    linarith

/-- A strictly dominated gap family strictly dominates the width. -/
theorem lt_width_of_forall_lt {E : ℕ → ℝ} {m : ℝ} :
    ∀ n : ℕ, 0 < n → (∀ j, j < n → m < E (j + 1) - E j) → (n : ℝ) * m < E n - E 0 := by
  intro n
  induction n with
  | zero => intro h _; exact absurd h (lt_irrefl 0)
  | succ n ih =>
    intro _ hm
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have h0 := hm 0 (by norm_num)
      simpa using h0
    · have hprev := ih hnpos fun j hj => hm j (Nat.lt_succ_of_lt hj)
      have hlast := hm n (Nat.lt_succ_self n)
      push_cast
      linarith

/-- **`(13)`: the dimension-linear clock horizon.**  One of the `n` gaps is at most the average, so
the exact-growth regime is reached with no anti-concentration input. -/
theorem exists_gap_le_average {E : ℕ → ℝ} {n : ℕ} (hn : 0 < n) :
    ∃ j < n, ((n : ℝ)) * (E (j + 1) - E j) ≤ E n - E 0 := by
  by_contra hcon
  push Not at hcon
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : ∀ j, j < n → (E n - E 0) / (n : ℝ) < E (j + 1) - E j := by
    intro j hj
    rw [div_lt_iff₀ hnpos]
    nlinarith [hcon j hj]
  have h := lt_width_of_forall_lt (E := E) n hn hm
  have heq : (n : ℝ) * ((E n - E 0) / (n : ℝ)) = E n - E 0 := by
    field_simp
  rw [heq] at h
  exact lt_irrefl _ h

/-! ## Recurrence collapses the bandwidth -/

/-- **`(14)`: an exact projective recurrence has zero bandwidth.** -/
theorem exists_phaseLift_zero {θ E : ℕ → ℝ} {n : ℕ} (hmono : ∀ j, E j ≤ E (j + 1))
    (hzero : ∀ j, circDist (θ (j + 1)) (θ j) = 0) :
    ∃ p : ℝ → ℝ, (∀ x y, |p x - p y| ≤ 0 * |x - y|) ∧ IsPhaseLift θ E n p := by
  refine exists_phaseLift_of_step le_rfl hmono fun j => ?_
  rw [hzero j, zero_mul]

/-- A constant phase assignment has all adjacent circular distances zero, so an exact recurrence
`U(T) = λI` collapses the bandwidth. -/
theorem circDist_const_zero {θ : ℝ} : circDist θ θ = 0 := by
  have h := circDist_le_abs_sub θ θ
  have hnn := circDist_nonneg θ θ
  simp only [sub_self, abs_zero] at h
  linarith

end GaloisForLFunctions.HTGeometry

import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.MultiplicityQuantization

/-!
# Exact two-prime noise floor

For fixed counts the optimal real exponent balances the excess probability on
one prime against the deficit on the other. On a closed interval, projection of
this balance point gives the optimum. Only 36 count pairs can improve on their
neighbors in the closed critical strip.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Set

/-- Total probability for D equal-modulus branches at shell n. -/
def probeMass (n : ℕ+) (D : ℕ) (σ : ℝ) : ℝ := D / ((n : ℕ) : ℝ) ^ (2 * σ)

theorem probeMass_eq_heat (s : ℂ) (n : ℕ+) (D : ℕ) :
    probeMass n D s.re = D * ‖heat s n‖ ^ 2 := by
  rw [probeMass, norm_heat, sq, ← Real.exp_add, div_eq_mul_inv,
    Real.rpow_def_of_pos (by exact_mod_cast n.pos), ← Real.exp_neg]
  congr 2
  unfold energy
  ring

theorem probeMass_strictAnti {n : ℕ+} (hn : 1 < (n : ℕ)) {D : ℕ} (hD : 0 < D) :
    StrictAnti (probeMass n D) := by
  intro x y hxy
  apply div_lt_div_of_pos_left (Nat.cast_pos.mpr hD) (Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _)
  exact (Real.strictMono_rpow_of_base_gt_one (by exact_mod_cast hn : 1 < ((n : ℕ) : ℝ))) (by linarith)

theorem continuous_probeMass (n : ℕ+) (D : ℕ) : Continuous (probeMass n D) := by
  unfold probeMass
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  apply continuous_const.div
  · fun_prop (disch := exact hn.ne')
  · exact fun x => (Real.rpow_pos_of_pos hn _).ne'

def probeError (a b : ℕ) (σ : ℝ) : ℝ :=
  max |probeMass 2 a σ - 1| |probeMass 3 b σ - 1|

/-- Positive counts that can be nearest to the target counts in the closed strip. -/
abbrev ProbeCounts := Fin 4 × Fin 9

def countError (c : ProbeCounts) := probeError (c.1.val + 1) (c.2.val + 1)

private def total (c : ProbeCounts) (x : ℝ) :=
  probeMass 2 (c.1.val + 1) x + probeMass 3 (c.2.val + 1) x

private theorem strictAnti_total (c : ProbeCounts) : StrictAnti (total c) :=
  (probeMass_strictAnti (n := 2) (by norm_num) (Nat.succ_pos _)).add
    (probeMass_strictAnti (n := 3) (by norm_num) (Nat.succ_pos _))

private theorem exists_balance (c : ProbeCounts) : ∃ x ∈ Icc (0 : ℝ) 1, total c x = 2 := by
  apply intermediate_value_Icc' zero_le_one
    ((continuous_probeMass 2 _).add (continuous_probeMass 3 _)).continuousOn
  have ha' : c.1.val + 1 ≤ 4 := c.1.isLt
  have hb' : c.2.val + 1 ≤ 9 := c.2.isLt
  constructor
  · change probeMass 2 _ 1 + probeMass 3 _ 1 ≤ 2
    norm_num [probeMass, Real.rpow_two]
    linarith [show (c.1.val : ℝ) + 1 ≤ 4 by exact_mod_cast ha',
      show (c.2.val : ℝ) + 1 ≤ 9 by exact_mod_cast hb']
  · change 2 ≤ probeMass 2 _ 0 + probeMass 3 _ 0
    simp only [probeMass, mul_zero, Real.rpow_zero, div_one, Nat.cast_add, Nat.cast_one]
    linarith [Nat.cast_nonneg (α := ℝ) c.1.val, Nat.cast_nonneg (α := ℝ) c.2.val]

/-- At the balance point the two signed deviations sum to zero. -/
def probeBalance (c : ProbeCounts) : ℝ := (exists_balance c).choose

theorem probeBalance_mem (c : ProbeCounts) : probeBalance c ∈ Icc (0 : ℝ) 1 :=
  (exists_balance c).choose_spec.1

theorem probeBalance_iff (c : ProbeCounts) (x : ℝ) :
    probeMass 2 (c.1.val + 1) x + probeMass 3 (c.2.val + 1) x = 2 ↔ x = probeBalance c := by
  have h := (exists_balance c).choose_spec.2
  exact ⟨fun hx => (strictAnti_total c).injective (hx.trans h.symm), fun hx => hx ▸ h⟩

private theorem high_error {u v : ℝ} (h : 2 ≤ u + v) :
    max |u - 1| |v - 1| = max u v - 1 := by
  have aux {a b : ℝ} (hab : a ≤ b) (hs : 2 ≤ a + b) :
      max |a - 1| |b - 1| = b - 1 := by
    rw [abs_of_nonneg (show 0 ≤ b - 1 by linarith)]
    exact max_eq_right (abs_le.mpr ⟨by linarith, by linarith⟩)
  rcases le_total u v with huv | hvu
  · rw [max_eq_right huv, aux huv h]
  · rw [max_comm |u - 1|, max_eq_left hvu, aux hvu (by linarith)]

private theorem low_error {u v : ℝ} (h : u + v ≤ 2) :
    max |u - 1| |v - 1| = 1 - min u v := by
  have h' := high_error (u := 2-u) (v := 2-v) (by linarith)
  rw [show 2-u-1 = -(u-1) by ring, show 2-v-1 = -(v-1) by ring, abs_neg, abs_neg] at h'
  rw [h']
  rcases le_total u v with huv | hvu
  · rw [min_eq_left huv, max_eq_left (by linarith : 2-v ≤ 2-u)]
    ring
  · rw [min_eq_right hvu, max_eq_right (by linarith : 2-u ≤ 2-v)]
    ring

/-- To the left of balance the larger excess decreases strictly. -/
theorem countError_left (c : ProbeCounts) : StrictAntiOn (countError c) (Iic (probeBalance c)) := by
  have form (x : ℝ) (hx : x ≤ probeBalance c) :
      countError c x = max (probeMass 2 (c.1.val+1) x) (probeMass 3 (c.2.val+1) x) - 1 := by
    apply high_error
    exact (probeBalance_iff c _).2 rfl ▸ (strictAnti_total c).antitone hx
  intro x hx y hy hxy
  rw [form x hx, form y hy]
  exact sub_lt_sub_right (max_lt_max
    (probeMass_strictAnti (n := 2) (by norm_num) (Nat.succ_pos _) hxy)
    (probeMass_strictAnti (n := 3) (by norm_num) (Nat.succ_pos _) hxy)) 1

/-- To the right of balance the larger deficit increases strictly. -/
theorem countError_right (c : ProbeCounts) : StrictMonoOn (countError c) (Ici (probeBalance c)) := by
  have form (x : ℝ) (hx : probeBalance c ≤ x) :
      countError c x = 1 - min (probeMass 2 (c.1.val+1) x) (probeMass 3 (c.2.val+1) x) := by
    apply low_error
    exact (probeBalance_iff c _).2 rfl ▸ (strictAnti_total c).antitone hx
  intro x hx y hy hxy
  rw [form x hx, form y hy]
  exact sub_lt_sub_left (min_lt_min
    (probeMass_strictAnti (n := 2) (by norm_num) (Nat.succ_pos _) hxy)
    (probeMass_strictAnti (n := 3) (by norm_num) (Nat.succ_pos _) hxy)) 1

def intervalBalance (l u : ℝ) (c : ProbeCounts) := max l (min u (probeBalance c))

theorem intervalBalance_mem {l u : ℝ} (h : l ≤ u) (c : ProbeCounts) :
    intervalBalance l u c ∈ Icc l u :=
  ⟨le_max_left .., max_le h (min_le_left ..)⟩

theorem intervalBalance_min {l u x : ℝ} (hx : x ∈ Icc l u) (c : ProbeCounts) :
    countError c (intervalBalance l u c) ≤ countError c x := by
  unfold intervalBalance
  rcases le_total (probeBalance c) l with hl | hl
  · rw [max_eq_left ((min_le_right ..).trans hl)]
    exact (countError_right c).monotoneOn hl (hl.trans hx.1) hx.1
  rcases le_total u (probeBalance c) with hu | hu
  · rw [min_eq_left hu, max_eq_right (hx.1.trans hx.2)]
    exact (countError_left c).antitoneOn (hx.2.trans hu) hu hx.2
  rw [min_eq_right hu, max_eq_right hl]
  rcases le_total x (probeBalance c) with h | h
  · exact (countError_left c).antitoneOn h (show probeBalance c ≤ probeBalance c from le_rfl) h
  · exact (countError_right c).monotoneOn (show probeBalance c ≤ probeBalance c from le_rfl) h h

/-- Clipping an outcome count to the range of possible target counts reduces its defect. -/
private theorem clip_count {N : ℕ} (hN : 0 < N) {v : ℝ} (hv : 1 ≤ v) (hvN : v ≤ N)
    (D : ℕ) : ∃ k : Fin N, |((k.val + 1 : ℕ) : ℝ) / v - 1| ≤ |(D : ℝ) / v - 1| := by
  have hc : ∃ k : Fin N, |((k.val + 1 : ℕ) : ℝ) - v| ≤ |(D : ℝ) - v| := by
    by_cases hz : D = 0
    · subst D
      refine ⟨⟨0, hN⟩, ?_⟩
      simp only [zero_add, Nat.cast_one, Nat.cast_zero, zero_sub, abs_neg]
      rw [abs_of_nonpos (sub_nonpos.mpr hv), abs_of_nonneg (by linarith : 0 ≤ v)]
      linarith
    by_cases hd : D ≤ N
    · refine ⟨⟨D - 1, by omega⟩, ?_⟩
      simp only [show D - 1 + 1 = D by omega, le_refl]
    · refine ⟨⟨N - 1, by omega⟩, ?_⟩
      have hND : (N : ℝ) ≤ D := by exact_mod_cast (by omega : N ≤ D)
      rw [show N - 1 + 1 = N by omega, abs_of_nonneg (sub_nonneg.mpr hvN),
        abs_of_nonneg (sub_nonneg.mpr (hvN.trans hND))]
      linarith
  obtain ⟨k, hk⟩ := hc
  refine ⟨k, ?_⟩
  have hpos : 0 < v := by linarith
  rw [div_sub_one hpos.ne', div_sub_one hpos.ne', abs_div, abs_div]
  exact div_le_div_of_nonneg_right hk (abs_nonneg _)

private theorem strip_power_bounds {p : ℝ} (hp : 1 < p) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    1 ≤ p ^ (2*x) ∧ p ^ (2*x) ≤ p^2 := by
  have inc := (Real.strictMono_rpow_of_base_gt_one hp).monotone
  constructor
  · simpa only [Real.rpow_zero] using inc (show (0 : ℝ) ≤ 2*x by linarith [hx.1])
  · simpa only [Real.rpow_two] using inc (show 2*x ≤ (2 : ℝ) by linarith [hx.2])

theorem countError_dominates (a b : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ c : ProbeCounts, countError c x ≤ probeError a b x := by
  obtain ⟨h₂, H₂⟩ := strip_power_bounds (by norm_num : (1 : ℝ) < 2) hx
  obtain ⟨h₃, H₃⟩ := strip_power_bounds (by norm_num : (1 : ℝ) < 3) hx
  obtain ⟨i, hi⟩ := clip_count (N := 4) (by norm_num) h₂ (by norm_num at H₂ ⊢; exact H₂) a
  obtain ⟨j, hj⟩ := clip_count (N := 9) (by norm_num) h₃ (by norm_num at H₃ ⊢; exact H₃) b
  exact ⟨(i,j), max_le_max hi hj⟩

/-- All observable maximum probability defects with exponent in the given interval. -/
def observedErrors (l u : ℝ) : Set ℝ :=
  {e | ∃ a b : ℕ, ∃ x ∈ Icc l u, e = probeError a b x}

/-- Exact optimal defect from 36 projected balance points. -/
def intervalFloor (l u : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun c : ProbeCounts => countError c (intervalBalance l u c))

theorem intervalFloor_isLeast {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u ≤ 1) :
    IsLeast (observedErrors l u) (intervalFloor l u) := by
  classical
  let F (c : ProbeCounts) := countError c (intervalBalance l u c)
  constructor
  · obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty F
    exact ⟨_, _, _, intervalBalance_mem hlu c, hc⟩
  · rintro e ⟨a, b, x, hx, rfl⟩
    obtain ⟨c, hc⟩ := countError_dominates a b ⟨hl.trans hx.1, hx.2.trans hu⟩
    exact (Finset.inf'_le F (Finset.mem_univ c)).trans ((intervalBalance_min hx c).trans hc)

private theorem exact_exponent {x : ℝ} (h₀ : 0 < x) (h₁ : x < 1) {a b : ℕ}
    (he : probeError a b x = 0) : x = 1/2 := by
  have fit (n : ℕ+) (D : ℕ) (h : |probeMass n D x - 1| ≤ 0) : conserves (x : ℂ) n D := by
    have hm := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
    exact (probeMass_eq_heat (x : ℂ) n D).symm.trans hm
  apply (binary_ternary_resolution_iff ⟨(x : ℂ), h₀, h₁⟩).1
  exact ⟨⟨a, fit 2 a ((le_max_left ..).trans he.le)⟩, ⟨b, fit 3 b ((le_max_right ..).trans he.le)⟩⟩

theorem intervalFloor_pos {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < 1)
    (hh : (1/2 : ℝ) ∉ Icc l u) : 0 < intervalFloor l u := by
  obtain ⟨a, b, x, hx, he⟩ := (intervalFloor_isLeast hl.le hlu hu.le).1
  rw [he]
  apply lt_of_le_of_ne ((abs_nonneg _).trans (le_max_left ..))
  intro hz
  exact hh (exact_exponent (hl.trans_le hx.1) (hx.2.trans_lt hu) hz.symm ▸ hx)

/-- Smallest possible error at separation at least δ from all three exact exponents. -/
def separatedFloor (δ : ℝ) :=
  min (intervalFloor δ (1/2-δ)) (intervalFloor (1/2+δ) (1-δ))

theorem separatedFloor_isLeast {δ : ℝ} (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1/4) :
    IsLeast (observedErrors δ (1/2-δ) ∪ observedErrors (1/2+δ) (1-δ)) (separatedFloor δ) := by
  have hL := intervalFloor_isLeast (l := δ) (u := 1/2-δ) h₀ (by linarith) (by linarith)
  have hR := intervalFloor_isLeast (l := 1/2+δ) (u := 1-δ) (by linarith) (by linarith) (by linarith)
  exact hL.union hR

theorem separatedFloor_pos {δ : ℝ} (h₀ : 0 < δ) (h₁ : δ ≤ 1/4) : 0 < separatedFloor δ := by
  apply lt_min
  · apply intervalFloor_pos h₀ (by linarith) (by linarith)
    intro h
    linarith [h.2]
  · apply intervalFloor_pos (by linarith) (by linarith) (by linarith)
    intro h
    linarith [h.1]

#print axioms probeMass_eq_heat
#print axioms probeBalance_iff
#print axioms countError_left
#print axioms countError_right
#print axioms intervalFloor_isLeast
#print axioms separatedFloor_isLeast
#print axioms separatedFloor_pos

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

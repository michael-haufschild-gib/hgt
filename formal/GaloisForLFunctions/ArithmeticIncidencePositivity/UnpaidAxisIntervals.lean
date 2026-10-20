import GaloisForLFunctions.ArithmeticIncidencePositivity.CollarSandwichLaw
import GaloisForLFunctions.ArithmeticIncidencePositivity.TotalAntiDiagonalClassification

/-!
# The unpaid axis intervals of an anti-diagonal

Fix a level `E ≥ 0` of negative conductance on the anti-diagonal of sum `s`. The **unpaid set**
is the set of `a ∈ (0, s)` where the polar weight `P_s(a) = sinh(a/2) sinh((s − a)/2)` is below `E`.
Since `P_s` increases on `[0, s/2]` and is symmetric, the unpaid set is two axis intervals as soon as
the quarter point is paid, `E ≤ P_s(s/4)`, and the two bounds `a sinh(s/2 − a) ≤ 2P_s(a) ≤ a sinh(s/2)`
sandwich its ends:

    (0, ℓ) ∪ (s − ℓ, s) ⊆ unpaid set ⊆ (0, L) ∪ (s − L, s),
    ℓ = 2E/sinh(s/2),   L = 2E/sinh(s/2 − min(s/4, 2E/sinh(s/4))).

For the anti-diagonal of `n` and its full level `E_n = ω(log n) + Λ(n)/√n` the inner end is
`ℓ_n = 4(n²/(n² − 1) + Λ(n))/(n − 1)`, of exact order `4(1 + Λ(n))/n`, and the quarter point is paid
for every `n ≥ 41`. So for `n ≥ 41` the pole pays the whole negative conductance of the anti-diagonal
of `n` except on two axis intervals of length between `ℓ_n` and `ℓ_n · sinh(s/2)/sinh(s/2 − min(…))`.
-/

open RHTower Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### Monotonicity of the polar weight -/

/-- The polar weight increases from the axis to the midpoint. -/
theorem crossingPolarWeight_mono {s a b : ℝ} (hab : a ≤ b) (hb : b ≤ s / 2) :
    crossingPolarWeight s a ≤ crossingPolarWeight s b := by
  rw [crossingPolarWeight_eq, crossingPolarWeight_eq]
  have h : Real.cosh (s / 2 - b) ≤ Real.cosh (s / 2 - a) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  linarith

/-! ### The unpaid set of a level -/

/-- The unpaid set of the level `E` on the anti-diagonal of sum `s`. -/
def unpaidSet (s E : ℝ) : Set ℝ := {a | 0 < a ∧ a < s ∧ crossingPolarWeight s a < E}

theorem sub_mem_unpaidSet_iff {s E a : ℝ} : s - a ∈ unpaidSet s E ↔ a ∈ unpaidSet s E := by
  simp only [unpaidSet, mem_setOf_eq, crossingPolarWeight_symm]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨by linarith, by linarith, h3⟩

/-- The inner end `ℓ = 2E/sinh(s/2)`. -/
def unpaidInnerEnd (s E : ℝ) : ℝ := 2 * E / Real.sinh (s / 2)

/-- The crude end `2E/sinh(s/4)`. -/
def unpaidCrudeEnd (s E : ℝ) : ℝ := 2 * E / Real.sinh (s / 4)

/-- The outer end `L = 2E/sinh(s/2 − min(s/4, 2E/sinh(s/4)))`. -/
def unpaidOuterEnd (s E : ℝ) : ℝ :=
  2 * E / Real.sinh (s / 2 - min (s / 4) (unpaidCrudeEnd s E))

theorem mem_unpaidSet_of_lt_innerEnd {s E a : ℝ} (hs : 0 < s) (ha : 0 < a) (has : a < s)
    (hl : a < unpaidInnerEnd s E) : a ∈ unpaidSet s E := by
  refine ⟨ha, has, ?_⟩
  have hsh : 0 < Real.sinh (s / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have h := two_mul_crossingPolarWeight_le hs.le ha.le
  unfold unpaidInnerEnd at hl
  rw [lt_div_iff₀ hsh] at hl
  linarith

/-- **Inner inclusion.** -/
theorem innerEnds_subset_unpaidSet {s E : ℝ} (hs : 0 < s) :
    Ioo 0 (min (unpaidInnerEnd s E) s) ∪ Ioo (s - min (unpaidInnerEnd s E) s) s ⊆
      unpaidSet s E := by
  intro a ha
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mem_unpaidSet_of_lt_innerEnd hs h1 (lt_of_lt_of_le h2 (min_le_right _ _))
      (lt_of_lt_of_le h2 (min_le_left _ _))
  · rw [← sub_mem_unpaidSet_iff]
    have hm : s - a < min (unpaidInnerEnd s E) s := by linarith
    exact mem_unpaidSet_of_lt_innerEnd hs (by linarith) (lt_of_lt_of_le hm (min_le_right _ _))
      (lt_of_lt_of_le hm (min_le_left _ _))

/-- Below the midpoint, an unpaid point lies below the quarter point once the quarter point is
paid. -/
theorem lt_quarter_of_mem_unpaidSet {s E a : ℝ} (hq : E ≤ crossingPolarWeight s (s / 4))
    (ha : a ∈ unpaidSet s E) (hhalf : a ≤ s / 2) : a < s / 4 := by
  obtain ⟨ha0, _, hP⟩ := ha
  by_contra h
  rw [not_lt] at h
  have := crossingPolarWeight_mono h hhalf
  linarith

theorem lt_outerEnd_of_mem_unpaidSet {s E a : ℝ}
    (hq : E ≤ crossingPolarWeight s (s / 4)) (ha : a ∈ unpaidSet s E) (hhalf : a ≤ s / 2) :
    a < unpaidOuterEnd s E := by
  have hq4 := lt_quarter_of_mem_unpaidSet hq ha hhalf
  obtain ⟨ha0, _, hP⟩ := ha
  have hsinh4 : 0 < Real.sinh (s / 4) := Real.sinh_pos_iff.mpr (by linarith)
  have h1 := le_two_mul_crossingPolarWeight ha0.le hhalf
  have h2 : Real.sinh (s / 4) ≤ Real.sinh (s / 2 - a) := Real.sinh_le_sinh.mpr (by linarith)
  have hcrude : a < unpaidCrudeEnd s E := by
    unfold unpaidCrudeEnd
    rw [lt_div_iff₀ hsinh4]
    nlinarith [mul_le_mul_of_nonneg_left h2 ha0.le]
  have hm : a < min (s / 4) (unpaidCrudeEnd s E) := lt_min hq4 hcrude
  have hsm : 0 < Real.sinh (s / 2 - min (s / 4) (unpaidCrudeEnd s E)) :=
    Real.sinh_pos_iff.mpr (by linarith [min_le_left (s / 4) (unpaidCrudeEnd s E)])
  have h3 : Real.sinh (s / 2 - min (s / 4) (unpaidCrudeEnd s E)) ≤ Real.sinh (s / 2 - a) :=
    Real.sinh_le_sinh.mpr (by linarith)
  unfold unpaidOuterEnd
  rw [lt_div_iff₀ hsm]
  nlinarith [mul_le_mul_of_nonneg_left h3 ha0.le]

/-- **Outer inclusion.** Once the quarter point is paid, the unpaid set lies within the outer end
of the two axes. -/
theorem unpaidSet_subset_outer {s E : ℝ} (hq : E ≤ crossingPolarWeight s (s / 4)) :
    unpaidSet s E ⊆ Ioo 0 (unpaidOuterEnd s E) ∪ Ioo (s - unpaidOuterEnd s E) s := by
  intro a ha
  rcases le_or_gt a (s / 2) with hhalf | hhalf
  · exact Or.inl ⟨ha.1, lt_outerEnd_of_mem_unpaidSet hq ha hhalf⟩
  · have ha' : s - a ∈ unpaidSet s E := sub_mem_unpaidSet_iff.mpr ha
    have := lt_outerEnd_of_mem_unpaidSet hq ha' (by linarith)
    exact Or.inr ⟨by linarith, ha.2.1⟩

/-- The two ends differ by the factor `sinh(s/2)/sinh(s/2 − min(s/4, 2E/sinh(s/4)))`. -/
theorem unpaidOuterEnd_eq {s E : ℝ} (hs : 0 < s) :
    unpaidOuterEnd s E = unpaidInnerEnd s E *
      (Real.sinh (s / 2) / Real.sinh (s / 2 - min (s / 4) (unpaidCrudeEnd s E))) := by
  unfold unpaidOuterEnd unpaidInnerEnd
  have hsh : Real.sinh (s / 2) ≠ 0 := (Real.sinh_pos_iff.mpr (by linarith)).ne'
  rw [div_mul_div_comm, mul_comm (2 * E) (Real.sinh (s / 2)), mul_div_mul_left _ _ hsh]

/-! ### The full level of the anti-diagonal of `n` -/

/-- The negative conductance level of the anti-diagonal of `n`: `ω(log n) + Λ(n)/√n`. -/
def antiDiagonalLevel (n : ℕ) : ℝ := archLevyDensity (Real.log n) + vonMangoldtAtom n

/-- The unpaid set of the full level is the set of points of positive total kernel. -/
theorem mem_unpaidSet_level_iff (n : ℕ) (a : ℝ) :
    a ∈ unpaidSet (Real.log n) (antiDiagonalLevel n) ↔
      0 < a ∧ a < Real.log n ∧ 0 < totalAntiDiagonalKernel n a := by
  simp only [unpaidSet, mem_setOf_eq, antiDiagonalLevel, totalAntiDiagonalKernel, sub_pos]

/-- `sinh(log n / 2) = (n − 1)/(2√n)`. -/
theorem sinh_half_log_nat {n : ℕ} (hn : 1 ≤ n) :
    Real.sinh (Real.log n / 2) = ((n : ℝ) - 1) / (2 * Real.sqrt n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  rw [show Real.log n / 2 = Real.log (Real.sqrt n) by rw [Real.log_sqrt hn0.le], Real.sinh_eq,
    Real.exp_neg, Real.exp_log hs, div_eq_div_iff two_ne_zero (by positivity)]
  have e : (Real.sqrt n)⁻¹ * Real.sqrt n = 1 := inv_mul_cancel₀ hs.ne'
  have e2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  linear_combination 2 * e2 - 2 * e

/-- The inner end of the full level: `ℓ_n = 4(n²/(n² − 1) + Λ(n))/(n − 1)`. -/
theorem unpaidInnerEnd_level_eq {n : ℕ} (hn : 2 ≤ n) :
    unpaidInnerEnd (Real.log n) (antiDiagonalLevel n) =
      4 * ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) + ArithmeticFunction.vonMangoldt n) / ((n : ℝ) - 1) := by
  unfold unpaidInnerEnd antiDiagonalLevel vonMangoldtAtom
  rw [if_pos hn, archLevyDensity_log_nat hn, sinh_half_log_nat (by omega)]
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hne : (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `4/(n − 1) ≤ ℓ_n`. -/
theorem four_div_le_unpaidInnerEnd_level {n : ℕ} (hn : 2 ≤ n) :
    4 / ((n : ℝ) - 1) ≤ unpaidInnerEnd (Real.log n) (antiDiagonalLevel n) := by
  rw [unpaidInnerEnd_level_eq hn]
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) := by
    rw [le_div_iff₀ hn2]; linarith
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  apply div_le_div_of_nonneg_right _ (by linarith)
  linarith

/-- `ℓ_n ≤ 4(1 + 1/(n² − 1) + log n)/(n − 1)`. -/
theorem unpaidInnerEnd_level_le {n : ℕ} (hn : 2 ≤ n) :
    unpaidInnerEnd (Real.log n) (antiDiagonalLevel n) ≤
      4 * (1 + 1 / ((n : ℝ) ^ 2 - 1) + Real.log n) / ((n : ℝ) - 1) := by
  rw [unpaidInnerEnd_level_eq hn]
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  have h1 : (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) = 1 + 1 / ((n : ℝ) ^ 2 - 1) := by
    field_simp
    ring
  have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  apply div_le_div_of_nonneg_right _ (by linarith)
  linarith

/-! ### The quarter point is paid from `41` on -/

/-- The polynomial inequality behind the quarter condition: for `t ≥ 0` and `r = 2.53 + t`,
`4.003 r + 8(r² − 1) ≤ r⁵ − r⁴ − r² + r`. -/
theorem quarter_poly_aux {t : ℝ} (ht : 0 ≤ t) :
    4.003 * (2.53 + t) + 8 * ((2.53 + t) ^ 2 - 1) ≤
      (2.53 + t) ^ 5 - (2.53 + t) ^ 4 - (2.53 + t) ^ 2 + (2.53 + t) := by
  nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5, ht]

/-- **Quarter condition.** For `n ≥ 41` the pole pays the full level at the quarter point. -/
theorem antiDiagonalLevel_le_quarter {n : ℕ} (hn : 41 ≤ n) :
    antiDiagonalLevel n ≤ crossingPolarWeight (Real.log n) (Real.log n / 4) := by
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn41 : (41 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = Real.sqrt (Real.sqrt n) := ⟨_, rfl⟩
  have hr : 0 < r := hr_def ▸ Real.sqrt_pos.mpr hs
  have hr2 : r ^ 2 = Real.sqrt n := by rw [hr_def]; exact Real.sq_sqrt hs.le
  have hr4 : r ^ 4 = n := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr2, Real.sq_sqrt hn0.le]
  have hr253 : (2.53 : ℝ) ≤ r := by
    by_contra hlt
    rw [not_le] at hlt
    have h4 : r ^ 4 < (2.53 : ℝ) ^ 4 := pow_lt_pow_left₀ hlt hr.le (by norm_num)
    rw [hr4] at h4
    norm_num at h4
    linarith
  have hr1 : 1 < r := by linarith
  have hlog : Real.log n = 4 * Real.log r := by
    rw [← hr4, Real.log_pow]; push_cast; ring
  have hsinh : Real.log r ≤ (r - r⁻¹) / 2 := by
    have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg hr1.le)
    rwa [Real.sinh_eq, Real.exp_neg, Real.exp_log hr] at h
  -- the quarter value in terms of `r`
  have hP : crossingPolarWeight (Real.log n) (Real.log n / 4) =
      ((r ^ 2 + (r ^ 2)⁻¹) / 2 - (r + r⁻¹) / 2) / 2 := by
    rw [crossingPolarWeight_eq, show Real.log n / 2 - Real.log n / 4 = Real.log n / 4 by ring,
      hlog, show 4 * Real.log r / 2 = Real.log (r ^ 2) by rw [Real.log_pow]; push_cast; ring,
      show 4 * Real.log r / 4 = Real.log r by ring, cosh_log (by positivity), cosh_log hr]
  -- the level in terms of `r`
  have hF : (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) ≤ 1 + 1 / 1680 := by
    have hpos : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
    rw [div_le_iff₀ hpos]; nlinarith
  have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  unfold antiDiagonalLevel vonMangoldtAtom
  rw [if_pos hn2, archLevyDensity_log_nat hn2, hP]
  rw [show (n : ℝ) ^ 2 / (((n : ℝ) ^ 2 - 1) * Real.sqrt n) =
      ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) / Real.sqrt n by rw [div_div], ← add_div, ← hr2,
    div_le_iff₀ (by positivity)]
  have hR : ((r ^ 2 + (r ^ 2)⁻¹) / 2 - (r + r⁻¹) / 2) / 2 * r ^ 2 =
      (r ^ 4 + 1 - r ^ 3 - r) / 4 := by
    field_simp
    ring
  rw [hR]
  have key := quarter_poly_aux (t := r - 2.53) (by linarith)
  rw [show (2.53 : ℝ) + (r - 2.53) = r by ring] at key
  have key' : 4.003 + 8 * (r - r⁻¹) ≤ r ^ 4 + 1 - r ^ 3 - r := by
    have e : r ^ 4 + 1 - r ^ 3 - r - (4.003 + 8 * (r - r⁻¹)) =
        (r ^ 5 - r ^ 4 - r ^ 2 + r - (4.003 * r + 8 * (r ^ 2 - 1))) / r := by
      field_simp
      ring
    have : 0 ≤ (r ^ 5 - r ^ 4 - r ^ 2 + r - (4.003 * r + 8 * (r ^ 2 - 1))) / r :=
      div_nonneg (by linarith) hr.le
    linarith
  linarith

/-! ### The unpaid axis intervals of the anti-diagonal of `n` -/

/-- **Inner inclusion for `n`.** Both axis intervals of length `min(ℓ_n, log n)` are unpaid. -/
theorem innerEnds_subset_unpaid_level {n : ℕ} (hn : 2 ≤ n) :
    Ioo 0 (min (unpaidInnerEnd (Real.log n) (antiDiagonalLevel n)) (Real.log n)) ∪
      Ioo (Real.log n - min (unpaidInnerEnd (Real.log n) (antiDiagonalLevel n)) (Real.log n))
        (Real.log n) ⊆ unpaidSet (Real.log n) (antiDiagonalLevel n) :=
  innerEnds_subset_unpaidSet (Real.log_pos (by exact_mod_cast (by omega : 1 < n)))

/-- **Outer inclusion for `n ≥ 41`.** The pole pays the whole negative conductance of the
anti-diagonal of `n` outside two axis intervals of length `L_n`. -/
theorem unpaid_level_subset_outer {n : ℕ} (hn : 41 ≤ n) :
    unpaidSet (Real.log n) (antiDiagonalLevel n) ⊆
      Ioo 0 (unpaidOuterEnd (Real.log n) (antiDiagonalLevel n)) ∪
        Ioo (Real.log n - unpaidOuterEnd (Real.log n) (antiDiagonalLevel n)) (Real.log n) :=
  unpaidSet_subset_outer (antiDiagonalLevel_le_quarter hn)

/-- Kernel form of the outer inclusion: for `n ≥ 41`, a point of the anti-diagonal with positive
total kernel lies within `L_n` of an axis. -/
theorem totalAntiDiagonalKernel_pos_imp_near_axis {n : ℕ} (hn : 41 ≤ n) {a : ℝ} (ha : 0 < a)
    (has : a < Real.log n) (hk : 0 < totalAntiDiagonalKernel n a) :
    a < unpaidOuterEnd (Real.log n) (antiDiagonalLevel n) ∨
      Real.log n - unpaidOuterEnd (Real.log n) (antiDiagonalLevel n) < a := by
  have hmem : a ∈ unpaidSet (Real.log n) (antiDiagonalLevel n) :=
    (mem_unpaidSet_level_iff n a).mpr ⟨ha, has, hk⟩
  rcases unpaid_level_subset_outer hn hmem with h | h
  · exact Or.inl h.2
  · exact Or.inr h.1

end GaloisForLFunctions.ArithmeticIncidencePositivity

import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeAtomVersusPoleClassification

/-!
# The collar of an anti-diagonal: two-sided law

On the anti-diagonal of sum `s`, parametrized by `(−a, s − a)`, the collar is the set of `a ∈ (0, s)`
with `P_s(a) < ω(s)`, where `P_s(a) = 2 sinh(a/2) sinh((s − a)/2) = cosh(s/2) − cosh(s/2 − a)` is
the polar weight. Two elementary bounds on the polar weight,

    a · sinh(s/2 − a) ≤ P_s(a) ≤ a · sinh(s/2)      (0 ≤ a ≤ s/2),

sandwich the collar between two explicit pairs of end intervals: for `s ≥ 4 log 2`,

    (0, ℓ(s)) ∪ (s − ℓ(s), s) ⊆ collar ⊆ (0, L(s)) ∪ (s − L(s), s),

with the **inner end** `ℓ(s) = ω(s)/sinh(s/2) = 2e^{−s}/((1 − e^{−2s})(1 − e^{−s}))`, which lies in
`[2e^{−s}, (256/239) · 2e^{−s}]`, and the **outer end** `L(s) = ℓ(s) · sinh(s/2)/sinh(s/2 − 3e^{−3s/4})`.
The collar has exact order `2e^{−s}` at each axis, and the unpaid archimedean mass of the
anti-diagonal is at most `2 ω(s) L(s)`, of order `4 e^{−3s/2}`.
-/

open RHTower Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### Two bounds on the polar weight -/

/-- `2 sinh t sinh(u − t) = sinh(2t) sinh u − (cosh(2t) − 1) cosh u`. -/
theorem two_sinh_mul_sinh_sub (t u : ℝ) :
    2 * Real.sinh t * Real.sinh (u - t) =
      Real.sinh (2 * t) * Real.sinh u - (Real.cosh (2 * t) - 1) * Real.cosh u := by
  rw [Real.sinh_sub, Real.sinh_two_mul, Real.cosh_two_mul, Real.cosh_sq]
  ring

/-- `sinh a − a ≤ cosh a − 1`: the convexity defect of `sinh` is below that of `cosh`. -/
theorem sinh_sub_self_le_cosh_sub_one (a : ℝ) : Real.sinh a - a ≤ Real.cosh a - 1 := by
  have h := Real.add_one_le_exp (-a)
  rw [← Real.cosh_sub_sinh] at h
  linarith

/-- Upper bound: `P_s(a) ≤ a sinh(s/2)` for `a, s ≥ 0`. -/
theorem crossingPolarWeight_le {s a : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) :
    crossingPolarWeight s a ≤ a * Real.sinh (s / 2) := by
  have e : crossingPolarWeight s a =
      Real.sinh a * Real.sinh (s / 2) - (Real.cosh a - 1) * Real.cosh (s / 2) := by
    unfold crossingPolarWeight
    have h := two_sinh_mul_sinh_sub (a / 2) (s / 2)
    rw [show 2 * (a / 2) = a by ring, show s / 2 - a / 2 = (s - a) / 2 by ring] at h
    exact h
  rw [e]
  have h1 : 0 ≤ Real.sinh (s / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
  have h2 : Real.sinh (s / 2) ≤ Real.cosh (s / 2) := (Real.sinh_lt_cosh (s / 2)).le
  have h3 : 0 ≤ Real.sinh a - a := by linarith [Real.self_le_sinh_iff.mpr ha]
  have h4 := sinh_sub_self_le_cosh_sub_one a
  nlinarith [mul_le_mul h2 h4 h3 (by linarith [Real.one_le_cosh (s / 2)])]

/-- Lower bound: `a sinh(s/2 − a) ≤ P_s(a)` for `0 ≤ a ≤ s/2`. -/
theorem le_crossingPolarWeight {s a : ℝ} (ha : 0 ≤ a) (has : a ≤ s / 2) :
    a * Real.sinh (s / 2 - a) ≤ crossingPolarWeight s a := by
  unfold crossingPolarWeight
  have h1 : a / 2 ≤ Real.sinh (a / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  have h2 : Real.sinh (s / 2 - a) ≤ Real.sinh ((s - a) / 2) :=
    Real.sinh_le_sinh.mpr (by linarith)
  have h3 : 0 ≤ Real.sinh (s / 2 - a) := Real.sinh_nonneg_iff.mpr (by linarith)
  have := mul_le_mul h1 h2 h3 (by linarith)
  linarith

/-! ### The two ends -/

/-- The inner collar end `ℓ(s) = ω(s)/sinh(s/2)`. -/
def collarInnerEnd (s : ℝ) : ℝ := archLevyDensity s / Real.sinh (s / 2)

/-- The outer collar end `L(s) = ω(s)/sinh(s/2 − 3e^{−3s/4})`. -/
def collarOuterEnd (s : ℝ) : ℝ :=
  archLevyDensity s / Real.sinh (s / 2 - 3 * Real.exp (-(3 * s) / 4))

theorem pos_of_four_log_two_le {s : ℝ} (hs : 4 * Real.log 2 ≤ s) : 0 < s := by
  linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- Closed form of the inner end: `ℓ(s) = 2e^{−s}/((1 − e^{−2s})(1 − e^{−s}))`. -/
theorem collarInnerEnd_eq {s : ℝ} (hs : 0 < s) :
    collarInnerEnd s = 2 * Real.exp (-s) / ((1 - Real.exp (-2 * s)) * (1 - Real.exp (-s))) := by
  unfold collarInnerEnd archLevyDensity
  set q := Real.exp (-s / 2) with hq_def
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hq_def, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have e1 : Real.exp (-s) = q ^ 2 := by
    rw [hq_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Real.exp (-2 * s) = q ^ 4 := by
    rw [hq_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e3 : Real.exp (s / 2) = q⁻¹ := by
    rw [hq_def, ← Real.exp_neg]; congr 1; ring
  have e4 : Real.exp (-(s / 2)) = q := by
    rw [hq_def]; congr 1; ring
  rw [Real.sinh_eq, e1, e2, e3, e4]
  have hq2 : q ^ 2 < 1 := by nlinarith
  have hq4 : q ^ 4 < 1 := by nlinarith [pow_pos hq 2]
  have h2 : (1 : ℝ) - q ^ 2 ≠ 0 := by linarith
  have h4 : (1 : ℝ) - q ^ 4 ≠ 0 := by linarith
  have e5 : q⁻¹ - q = (1 - q ^ 2) / q := by
    rw [eq_div_iff hq.ne', sub_mul, inv_mul_cancel₀ hq.ne']; ring
  have h5 : q⁻¹ - q ≠ 0 := by rw [e5]; exact div_ne_zero h2 hq.ne'
  rw [e5]
  field_simp

/-- `2e^{−s} ≤ ℓ(s)`. -/
theorem two_exp_neg_le_collarInnerEnd {s : ℝ} (hs : 0 < s) :
    2 * Real.exp (-s) ≤ collarInnerEnd s := by
  rw [collarInnerEnd_eq hs]
  have h1 : Real.exp (-2 * s) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h2 : Real.exp (-s) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hp1 : 0 < Real.exp (-2 * s) := Real.exp_pos _
  have hp2 : 0 < Real.exp (-s) := Real.exp_pos _
  have hden : 0 < (1 - Real.exp (-2 * s)) * (1 - Real.exp (-s)) :=
    mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2)
  have hle : (1 - Real.exp (-2 * s)) * (1 - Real.exp (-s)) ≤ 1 := by nlinarith
  rw [le_div_iff₀ hden]
  calc 2 * Real.exp (-s) * ((1 - Real.exp (-2 * s)) * (1 - Real.exp (-s)))
      ≤ 2 * Real.exp (-s) * 1 := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 2 * Real.exp (-s) := mul_one _

/-- `ℓ(s) ≤ (256/239) · 2e^{−s}` for `s ≥ 4 log 2`. -/
theorem collarInnerEnd_le {s : ℝ} (hs : 4 * Real.log 2 ≤ s) :
    collarInnerEnd s ≤ 256 / 239 * (2 * Real.exp (-s)) := by
  have hs0 := pos_of_four_log_two_le hs
  rw [collarInnerEnd_eq hs0]
  have hh := exp_neg_half_le_of_four_log_two_le hs
  have hq : 0 < Real.exp (-s / 2) := Real.exp_pos _
  have e1 : Real.exp (-s) = Real.exp (-s / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Real.exp (-2 * s) = Real.exp (-s / 2) ^ 4 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hA : Real.exp (-2 * s) ≤ 1 / 256 := by
    rw [e2]
    calc Real.exp (-s / 2) ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ hq.le hh 4
      _ = 1 / 256 := by norm_num
  have hB : Real.exp (-s) ≤ 1 / 16 := by
    rw [e1]
    calc Real.exp (-s / 2) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := pow_le_pow_left₀ hq.le hh 2
      _ = 1 / 16 := by norm_num
  have hp1 : 0 < Real.exp (-2 * s) := Real.exp_pos _
  have hp2 : 0 < Real.exp (-s) := Real.exp_pos _
  have hden : 239 / 256 ≤ (1 - Real.exp (-2 * s)) * (1 - Real.exp (-s)) := by
    nlinarith [mul_pos hp1 hp2]
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hden (by positivity : (0 : ℝ) ≤ 256 / 239 * (2 * Real.exp (-s)))]

/-- `3 e^{−3s/4} ≤ 3/8` for `s ≥ 4 log 2`. -/
theorem three_exp_le_three_eighths {s : ℝ} (hs : 4 * Real.log 2 ≤ s) :
    3 * Real.exp (-(3 * s) / 4) ≤ 3 / 8 := by
  have h : Real.exp (-(3 * s) / 4) ≤ 1 / 8 := by
    have h8 : -(3 * s) / 4 ≤ -Real.log 8 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; linarith
    calc Real.exp (-(3 * s) / 4) ≤ Real.exp (-Real.log 8) := Real.exp_le_exp.mpr h8
      _ = 1 / 8 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  linarith

theorem sinh_half_sub_pos {s : ℝ} (hs : 4 * Real.log 2 ≤ s) :
    0 < Real.sinh (s / 2 - 3 * Real.exp (-(3 * s) / 4)) := by
  have h := three_exp_le_three_eighths hs
  have := Real.log_two_gt_d9
  exact Real.sinh_pos_iff.mpr (by linarith)

/-- The two ends differ by the factor `sinh(s/2)/sinh(s/2 − 3e^{−3s/4})`. -/
theorem collarOuterEnd_eq {s : ℝ} (hs : 4 * Real.log 2 ≤ s) :
    collarOuterEnd s =
      collarInnerEnd s * (Real.sinh (s / 2) / Real.sinh (s / 2 - 3 * Real.exp (-(3 * s) / 4))) := by
  unfold collarOuterEnd collarInnerEnd
  have hsh : Real.sinh (s / 2) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (by linarith [pos_of_four_log_two_le hs])).ne'
  rw [div_mul_div_comm, mul_comm (archLevyDensity s) (Real.sinh (s / 2)),
    mul_div_mul_left _ _ hsh]

theorem collarOuterEnd_nonneg {s : ℝ} (hs : 4 * Real.log 2 ≤ s) : 0 ≤ collarOuterEnd s :=
  div_nonneg (archLevyDensity_pos (pos_of_four_log_two_le hs)).le (sinh_half_sub_pos hs).le

/-! ### The sandwich -/

/-- The collar is symmetric under `a ↦ s − a`. -/
theorem sub_mem_antiDiagonalCollar_iff {s a : ℝ} (hs : 0 < s) :
    s - a ∈ antiDiagonalCollar s ↔ a ∈ antiDiagonalCollar s := by
  rw [antiDiagonalCollar_eq hs]
  simp only [mem_inter_iff, mem_Ioo, mem_setOf_eq, crossingPolarWeight_symm]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h3⟩

/-- **Inner inclusion.** Every `a ∈ (0, s)` below the inner end lies in the collar. -/
theorem mem_antiDiagonalCollar_of_lt_innerEnd {s a : ℝ} (hs : 0 < s) (ha : 0 < a) (has : a < s)
    (hl : a < collarInnerEnd s) : a ∈ antiDiagonalCollar s := by
  refine ⟨ha, has, ?_⟩
  rw [archPairKernel_antiDiagonal_eq hs, sub_pos]
  have hsh : 0 < Real.sinh (s / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have h := crossingPolarWeight_le hs.le ha.le
  unfold collarInnerEnd at hl
  rw [lt_div_iff₀ hsh] at hl
  linarith

/-- **Inner inclusion, both ends.** -/
theorem innerEnds_subset_antiDiagonalCollar {s : ℝ} (hs : 0 < s) :
    Ioo 0 (min (collarInnerEnd s) s) ∪ Ioo (s - min (collarInnerEnd s) s) s ⊆
      antiDiagonalCollar s := by
  intro a ha
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mem_antiDiagonalCollar_of_lt_innerEnd hs h1 (lt_of_lt_of_le h2 (min_le_right _ _))
      (lt_of_lt_of_le h2 (min_le_left _ _))
  · rw [← sub_mem_antiDiagonalCollar_iff hs]
    have hm : s - a < min (collarInnerEnd s) s := by linarith
    exact mem_antiDiagonalCollar_of_lt_innerEnd hs (by linarith)
      (lt_of_lt_of_le hm (min_le_right _ _)) (lt_of_lt_of_le hm (min_le_left _ _))

/-- **Outer inclusion.** For `s ≥ 4 log 2` the collar lies within the outer end of the two axes. -/
theorem antiDiagonalCollar_subset_outer {s : ℝ} (hs : 4 * Real.log 2 ≤ s) :
    antiDiagonalCollar s ⊆ Ioo 0 (collarOuterEnd s) ∪ Ioo (s - collarOuterEnd s) s := by
  have hs0 := pos_of_four_log_two_le hs
  have hδ := three_exp_le_three_eighths hs
  have hl2 := Real.log_two_gt_d9
  have hsh := sinh_half_sub_pos hs
  have key : ∀ a ∈ antiDiagonalCollar s,
      a < 3 * Real.exp (-(3 * s) / 4) → a < collarOuterEnd s := by
    intro a ha hδa
    obtain ⟨ha0, _, hk⟩ := ha
    rw [archPairKernel_antiDiagonal_eq hs0, sub_pos] at hk
    have h1 := le_crossingPolarWeight ha0.le (by linarith : a ≤ s / 2)
    have h2 : Real.sinh (s / 2 - 3 * Real.exp (-(3 * s) / 4)) ≤ Real.sinh (s / 2 - a) :=
      Real.sinh_le_sinh.mpr (by linarith)
    unfold collarOuterEnd
    rw [lt_div_iff₀ hsh]
    nlinarith [mul_le_mul_of_nonneg_left h2 ha0.le]
  intro a ha
  rcases antiDiagonalCollar_subset hs ha with h | h
  · exact Or.inl ⟨h.1, key a ha h.2⟩
  · have ha' : s - a ∈ antiDiagonalCollar s := (sub_mem_antiDiagonalCollar_iff hs0).mpr ha
    have := key (s - a) ha' (by linarith [h.1])
    exact Or.inr ⟨by linarith, h.2⟩

/-- **Collar measure, sharp order.** For `s ≥ 4 log 2` the collar has length at most `2 L(s)`. -/
theorem volume_antiDiagonalCollar_le_outer {s : ℝ} (hs : 4 * Real.log 2 ≤ s) :
    volume (antiDiagonalCollar s) ≤ ENNReal.ofReal (2 * collarOuterEnd s) := by
  have hL := collarOuterEnd_nonneg hs
  calc volume (antiDiagonalCollar s)
      ≤ volume (Ioo 0 (collarOuterEnd s) ∪ Ioo (s - collarOuterEnd s) s) :=
        measure_mono (antiDiagonalCollar_subset_outer hs)
    _ ≤ volume (Ioo 0 (collarOuterEnd s)) + volume (Ioo (s - collarOuterEnd s) s) :=
        measure_union_le _ _
    _ = ENNReal.ofReal (collarOuterEnd s - 0) + ENNReal.ofReal (s - (s - collarOuterEnd s)) := by
        rw [Real.volume_Ioo, Real.volume_Ioo]
    _ = ENNReal.ofReal (2 * collarOuterEnd s) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        ring

/-- **Unpaid archimedean mass, sharp order.** At most `ω(s) · 2L(s)`, of order `4e^{−3s/2}`. -/
theorem lintegral_antiDiagonalCollar_le_outer {s : ℝ} (hs : 4 * Real.log 2 ≤ s) :
    ∫⁻ a in antiDiagonalCollar s, ENNReal.ofReal (archPairKernel (-a) (s - a)) ≤
      ENNReal.ofReal (archLevyDensity s) * ENNReal.ofReal (2 * collarOuterEnd s) := by
  have hs0 := pos_of_four_log_two_le hs
  calc ∫⁻ a in antiDiagonalCollar s, ENNReal.ofReal (archPairKernel (-a) (s - a))
      ≤ ∫⁻ _ in antiDiagonalCollar s, ENNReal.ofReal (archLevyDensity s) := by
        refine setLIntegral_mono' (measurableSet_antiDiagonalCollar hs0) fun a ha => ?_
        obtain ⟨h1, h2, _⟩ := ha
        exact ENNReal.ofReal_le_ofReal (archPairKernel_antiDiagonal_le hs0 h1.le h2.le)
    _ = ENNReal.ofReal (archLevyDensity s) * volume (antiDiagonalCollar s) :=
        setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (archLevyDensity s) * ENNReal.ofReal (2 * collarOuterEnd s) :=
        mul_le_mul' le_rfl (volume_antiDiagonalCollar_le_outer hs)

end GaloisForLFunctions.ArithmeticIncidencePositivity
